use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    Function, GlobalVariableRef, Immediate, InstId, Type, Value, ValueId,
    global_variable::GvInitializer,
    inst::{control_flow, data, downcast},
    module::ModuleCtx,
    types::CompoundType,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ConstPathStep {
    Field(usize),
    IndexConst(usize),
    IndexValue(ValueId),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ConstPath {
    pub(crate) global: GlobalVariableRef,
    pub(crate) ty: Type,
    pub(crate) steps: Vec<ConstPathStep>,
}

#[derive(Debug, Default)]
pub(crate) struct ConstPathAnalysis {
    paths: FxHashMap<ValueId, Option<ConstPath>>,
}

impl ConstPathAnalysis {
    pub(crate) fn path(&self, value: ValueId) -> Option<&ConstPath> {
        self.paths.get(&value).and_then(Option::as_ref)
    }

    fn compute(func: &Function, constref_value_tys: &FxHashMap<ValueId, Type>) -> Self {
        let mut analysis = Self::default();
        let mut visiting = FxHashSet::default();
        for &value in constref_value_tys.keys() {
            analysis.compute_value_path(func, value, constref_value_tys, &mut visiting);
        }
        analysis
    }

    fn compute_value_path(
        &mut self,
        func: &Function,
        value: ValueId,
        constref_value_tys: &FxHashMap<ValueId, Type>,
        visiting: &mut FxHashSet<ValueId>,
    ) -> Option<ConstPath> {
        if let Some(path) = self.paths.get(&value) {
            return path.clone();
        }
        if !constref_value_tys.contains_key(&value) || !visiting.insert(value) {
            return None;
        }

        let path = match func.dfg.value(value) {
            Value::Inst { inst, .. } => {
                self.compute_inst_path(func, *inst, constref_value_tys, visiting)
            }
            Value::Arg { .. }
            | Value::Immediate { .. }
            | Value::Global { .. }
            | Value::Undef { .. } => None,
        };

        visiting.remove(&value);
        self.paths.insert(value, path.clone());
        path
    }

    fn compute_inst_path(
        &mut self,
        func: &Function,
        inst: InstId,
        constref_value_tys: &FxHashMap<ValueId, Type>,
        visiting: &mut FxHashSet<ValueId>,
    ) -> Option<ConstPath> {
        let inst_data = func.dfg.inst(inst);
        if let Some(const_ref) = downcast::<&data::ConstRef>(func.inst_set(), inst_data) {
            let global = const_ref.global().gv();
            let ty = func.ctx().with_gv_store(|store| store.ty(global));
            return Some(ConstPath {
                global,
                ty,
                steps: Vec::new(),
            });
        }
        if let Some(proj) = downcast::<&data::ConstProj>(func.inst_set(), inst_data) {
            let (&base, rest) = proj.values().split_first()?;
            return self.compute_subref_path(func, base, rest, constref_value_tys, visiting);
        }
        if let Some(index) = downcast::<&data::ConstIndex>(func.inst_set(), inst_data) {
            return self.compute_subref_path(
                func,
                *index.object(),
                &[*index.index()],
                constref_value_tys,
                visiting,
            );
        }
        if let Some(phi) = downcast::<&control_flow::Phi>(func.inst_set(), inst_data) {
            return self.compute_phi_path(func, phi, constref_value_tys, visiting);
        }
        None
    }

    fn compute_subref_path(
        &mut self,
        func: &Function,
        base: ValueId,
        indices: &[ValueId],
        constref_value_tys: &FxHashMap<ValueId, Type>,
        visiting: &mut FxHashSet<ValueId>,
    ) -> Option<ConstPath> {
        let mut path = self.compute_value_path(func, base, constref_value_tys, visiting)?;
        let (ty, steps) = const_path_steps(func, path.ty, indices)?;
        path.ty = ty;
        path.steps.extend(steps);
        Some(path)
    }

    fn compute_phi_path(
        &mut self,
        func: &Function,
        phi: &control_flow::Phi,
        constref_value_tys: &FxHashMap<ValueId, Type>,
        visiting: &mut FxHashSet<ValueId>,
    ) -> Option<ConstPath> {
        let mut candidate = None;
        for &(arg, _) in phi.args() {
            let path = self.compute_value_path(func, arg, constref_value_tys, visiting)?;
            match candidate {
                Some(ref existing) if *existing != path => return None,
                Some(_) => {}
                None => candidate = Some(path),
            }
        }
        candidate
    }
}

pub(crate) fn analyze_const_paths(
    func: &Function,
    constref_value_tys: &FxHashMap<ValueId, Type>,
) -> ConstPathAnalysis {
    ConstPathAnalysis::compute(func, constref_value_tys)
}

pub(crate) fn collect_constref_value_tys(func: &Function) -> FxHashMap<ValueId, Type> {
    func.dfg
        .value_ids()
        .filter_map(|value| {
            let ty = func.dfg.value_ty(value);
            match ty.resolve_compound(func.ctx()) {
                Some(CompoundType::ConstRef(elem)) => Some((value, elem)),
                _ => None,
            }
        })
        .collect()
}

pub(crate) fn const_path_steps(
    func: &Function,
    base_ty: Type,
    indices: &[ValueId],
) -> Option<(Type, Vec<ConstPathStep>)> {
    let mut current_ty = base_ty;
    let mut steps = Vec::with_capacity(indices.len());
    for &idx_value in indices {
        let (next_ty, step) = const_child_path_step(func, current_ty, idx_value)?;
        current_ty = next_ty;
        steps.push(step);
    }
    Some((current_ty, steps))
}

pub(crate) fn eval_const_value_immediate(
    module: &ModuleCtx,
    const_paths: &ConstPathAnalysis,
    value: ValueId,
    resolve_index: impl Fn(ValueId) -> Option<Immediate>,
) -> Option<Immediate> {
    let path = const_paths.path(value)?;
    eval_const_path_immediate(module, path, resolve_index)
}

pub(crate) fn eval_const_path_immediate(
    module: &ModuleCtx,
    path: &ConstPath,
    resolve_index: impl Fn(ValueId) -> Option<Immediate>,
) -> Option<Immediate> {
    let (ty, init) = eval_const_path_subtree(module, path, resolve_index)?;
    match init {
        GvInitializer::Immediate(imm) if imm.ty() == ty => Some(imm),
        _ => None,
    }
}

pub(crate) fn dynamic_index_values(path: &ConstPath) -> impl Iterator<Item = ValueId> + '_ {
    path.steps.iter().filter_map(|step| match step {
        ConstPathStep::IndexValue(value) => Some(*value),
        ConstPathStep::Field(_) | ConstPathStep::IndexConst(_) => None,
    })
}

pub(crate) fn eval_const_path_subtree(
    module: &ModuleCtx,
    path: &ConstPath,
    resolve_index: impl Fn(ValueId) -> Option<Immediate>,
) -> Option<(Type, GvInitializer)> {
    module.with_gv_store(|store| {
        let ty = store.ty(path.global);
        let init = store.init_data(path.global)?;
        eval_initializer_subtree(module, ty, init, &path.steps, &resolve_index)
    })
}

fn const_child_path_step(
    func: &Function,
    current_ty: Type,
    idx_value: ValueId,
) -> Option<(Type, ConstPathStep)> {
    let idx_imm = func
        .dfg
        .value_imm(idx_value)
        .filter(|imm| !imm.is_negative())
        .map(Immediate::as_usize);
    match current_ty.resolve_compound(func.ctx())? {
        CompoundType::Array { elem, len } => {
            let step = match idx_imm {
                Some(idx) if idx < len => ConstPathStep::IndexConst(idx),
                Some(_) => return None,
                None => ConstPathStep::IndexValue(idx_value),
            };
            Some((elem, step))
        }
        CompoundType::Struct(s) => {
            if s.packed {
                return None;
            }
            let idx = idx_imm?;
            Some((*s.fields.get(idx)?, ConstPathStep::Field(idx)))
        }
        CompoundType::Ptr(_)
        | CompoundType::ObjRef(_)
        | CompoundType::ConstRef(_)
        | CompoundType::Enum(_)
        | CompoundType::Func { .. } => None,
    }
}

fn eval_initializer_subtree<R>(
    module: &ModuleCtx,
    ty: Type,
    init: &GvInitializer,
    steps: &[ConstPathStep],
    resolve_index: &R,
) -> Option<(Type, GvInitializer)>
where
    R: Fn(ValueId) -> Option<Immediate>,
{
    let Some((step, rest)) = steps.split_first() else {
        return Some((ty, init.clone()));
    };
    match (ty.resolve_compound(module)?, init, step) {
        (
            CompoundType::Array { elem, len },
            GvInitializer::Array(items),
            ConstPathStep::IndexConst(idx),
        ) => {
            (*idx < len).then_some(())?;
            eval_initializer_subtree(module, elem, items.get(*idx)?, rest, resolve_index)
        }
        (
            CompoundType::Array { elem, len },
            GvInitializer::Array(items),
            ConstPathStep::IndexValue(value),
        ) => {
            let idx = resolve_index(*value)
                .filter(|imm| !imm.is_negative())
                .map(Immediate::as_usize)?;
            (idx < len).then_some(())?;
            eval_initializer_subtree(module, elem, items.get(idx)?, rest, resolve_index)
        }
        (CompoundType::Struct(s), GvInitializer::Struct(fields), ConstPathStep::Field(idx)) => {
            if s.packed {
                return None;
            }
            eval_initializer_subtree(
                module,
                *s.fields.get(*idx)?,
                fields.get(*idx)?,
                rest,
                resolve_index,
            )
        }
        _ => None,
    }
}
