use cranelift_entity::SecondaryMap;
use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::SmallVec;
use sonatina_ir::{
    Function, InstId, InstSetExt, Type, ValueId,
    inst::evm::inst_set::EvmInstKind,
    isa::{Isa, evm::Evm},
    module::{FuncRef, ModuleCtx},
    types::{CompoundType, CompoundTypeRef},
};

use super::ptr_escape::PtrEscapeSummary;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum PtrBase {
    Arg(u32),
    Alloca(InstId),
    Malloc(InstId),
}

impl PtrBase {
    fn key(self) -> (u8, u32) {
        match self {
            PtrBase::Arg(i) => (0, i),
            PtrBase::Alloca(inst) => (1, inst.as_u32()),
            PtrBase::Malloc(inst) => (2, inst.as_u32()),
        }
    }
}

/// Pointer provenance facts for an SSA value or modeled memory cell.
///
/// Exact `bases` may coexist with unknown flags. For example, a call result can
/// be either a caller-local alloca or an unknown non-arg pointer; preserving the
/// exact alloca base lets later escape analysis report the local escape.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct Provenance {
    bases: SmallVec<[PtrBase; 4]>,
    /// Arg attribution retained after exact arg bases are collapsed.
    unknown_arg_indices: SmallVec<[u32; 4]>,
    /// The value may also be a non-arg pointer whose exact base is unknown.
    unknown_non_arg: bool,
}

impl Provenance {
    pub(crate) fn has_no_known_bases(&self) -> bool {
        self.bases.is_empty()
    }

    pub(crate) fn is_unknown_ptr(&self) -> bool {
        self.unknown_non_arg || !self.unknown_arg_indices.is_empty()
    }

    fn insert_arg_index(indices: &mut SmallVec<[u32; 4]>, idx: u32) -> bool {
        if indices.contains(&idx) {
            return false;
        }
        indices.push(idx);
        indices.sort_unstable();
        indices.dedup();
        true
    }

    fn add_unknown_arg_index(&mut self, idx: u32) -> bool {
        Self::insert_arg_index(&mut self.unknown_arg_indices, idx)
    }

    fn collapse_arg_bases_to_unknown_arg_indices(&mut self) -> bool {
        let arg_indices: SmallVec<[u32; 4]> = self
            .bases
            .iter()
            .filter_map(|base| match base {
                PtrBase::Arg(idx) => Some(*idx),
                _ => None,
            })
            .collect();
        let mut changed = false;
        for idx in arg_indices {
            changed |= self.add_unknown_arg_index(idx);
        }

        let old_len = self.bases.len();
        self.bases.retain(|base| !matches!(base, PtrBase::Arg(_)));
        changed || self.bases.len() != old_len
    }

    fn mark_unknown_non_arg(&mut self) -> bool {
        let mut changed = !self.unknown_non_arg;
        self.unknown_non_arg = true;
        changed |= self.collapse_arg_bases_to_unknown_arg_indices();
        changed
    }

    fn poison_to_unknown_non_arg_preserving_arg_attribution(&mut self) -> bool {
        let mut changed = self.mark_unknown_non_arg();
        // Memory clobbering intentionally loses exact bases. Plain union does not.
        if !self.bases.is_empty() {
            self.bases.clear();
            changed = true;
        }
        changed
    }

    pub(crate) fn union_with(&mut self, other: &Self) -> bool {
        let mut changed = false;
        let mut bases_changed = false;

        for base in other.bases.iter().copied() {
            match base {
                PtrBase::Arg(idx) if self.unknown_non_arg => {
                    changed |= self.add_unknown_arg_index(idx);
                }
                _ => {
                    if !self.bases.contains(&base) {
                        self.bases.push(base);
                        bases_changed = true;
                    }
                }
            }
        }

        if bases_changed {
            self.bases.sort_unstable_by_key(|b| b.key());
            self.bases.dedup();
            changed = true;
        }

        for idx in other.unknown_arg_indices.iter().copied() {
            changed |= self.add_unknown_arg_index(idx);
        }
        if other.unknown_non_arg {
            changed |= self.mark_unknown_non_arg();
        }
        changed
    }

    pub(crate) fn has_any_arg(&self) -> bool {
        self.bases.iter().any(|b| matches!(b, PtrBase::Arg(_)))
            || !self.unknown_arg_indices.is_empty()
    }

    pub(crate) fn arg_indices(&self) -> impl Iterator<Item = u32> + '_ {
        self.bases
            .iter()
            .filter_map(|b| match b {
                PtrBase::Arg(i) => Some(*i),
                PtrBase::Alloca(_) | PtrBase::Malloc(_) => None,
            })
            .chain(self.unknown_arg_indices.iter().copied())
    }

    pub(crate) fn is_local_addr(&self) -> bool {
        !self.is_unknown_ptr()
            && !self.has_no_known_bases()
            && self.bases.iter().all(|b| matches!(b, PtrBase::Alloca(_)))
    }

    pub(crate) fn may_be_nonlocal_nonarg(&self) -> bool {
        self.unknown_non_arg
            || self.bases.iter().any(|b| matches!(b, PtrBase::Malloc(_)))
            || (self.has_no_known_bases() && self.unknown_arg_indices.is_empty())
    }

    pub(crate) fn may_be_nonlocal_nonarg_without_malloc(&self) -> bool {
        self.unknown_non_arg || (self.has_no_known_bases() && self.unknown_arg_indices.is_empty())
    }

    pub(crate) fn alloca_insts(&self) -> impl Iterator<Item = InstId> + '_ {
        self.bases.iter().filter_map(|b| match b {
            PtrBase::Alloca(inst) => Some(*inst),
            PtrBase::Arg(_) => None,
            PtrBase::Malloc(_) => None,
        })
    }

    pub(crate) fn malloc_insts(&self) -> impl Iterator<Item = InstId> + '_ {
        self.bases.iter().filter_map(|b| match b {
            PtrBase::Malloc(inst) => Some(*inst),
            PtrBase::Arg(_) | PtrBase::Alloca(_) => None,
        })
    }
}

fn store_local_mem(
    mem: &mut FxHashMap<InstId, Provenance>,
    addr_prov: &Provenance,
    val_prov: &Provenance,
) -> bool {
    if !addr_prov.is_local_addr() {
        return false;
    }

    let mut changed = false;
    for base in addr_prov.alloca_insts() {
        changed |= mem.entry(base).or_default().union_with(val_prov);
    }
    changed
}

fn load_local_mem(mem: &FxHashMap<InstId, Provenance>, addr_prov: &Provenance) -> Provenance {
    let mut out = Provenance::default();
    if addr_prov.is_local_addr() {
        for base in addr_prov.alloca_insts() {
            if let Some(stored) = mem.get(&base) {
                let _ = out.union_with(stored);
            }
        }
    }
    out
}

fn poison_local_mem(mem: &mut FxHashMap<InstId, Provenance>, addr_prov: &Provenance) -> bool {
    if !addr_prov.is_local_addr() {
        return false;
    }

    let mut changed = false;
    for base in addr_prov.alloca_insts() {
        changed |= mem
            .entry(base)
            .or_default()
            .poison_to_unknown_non_arg_preserving_arg_attribution();
    }
    changed
}

fn store_arg_mem(mem: &mut [Provenance], addr_prov: &Provenance, val_prov: &Provenance) -> bool {
    let mut changed = false;
    for arg_idx in addr_prov.arg_indices() {
        if let Some(slot) = mem.get_mut(arg_idx as usize) {
            changed |= slot.union_with(val_prov);
        }
    }
    changed
}

fn poison_arg_mem(mem: &mut [Provenance], addr_prov: &Provenance) -> bool {
    let mut changed = false;
    for arg_idx in addr_prov.arg_indices() {
        if let Some(slot) = mem.get_mut(arg_idx as usize) {
            changed |= slot.poison_to_unknown_non_arg_preserving_arg_attribution();
        }
    }
    changed
}

fn unmodeled_write_addr(data: &EvmInstKind) -> Option<ValueId> {
    match data {
        EvmInstKind::EvmMstore8(mstore8) => Some(*mstore8.addr()),
        EvmInstKind::EvmMcopy(mcopy) => Some(*mcopy.dest()),
        EvmInstKind::EvmCalldataCopy(copy) => Some(*copy.dst_addr()),
        EvmInstKind::EvmCodeCopy(copy) => Some(*copy.dst_addr()),
        EvmInstKind::EvmExtCodeCopy(copy) => Some(*copy.dst_addr()),
        EvmInstKind::EvmReturnDataCopy(copy) => Some(*copy.dst_addr()),
        EvmInstKind::EvmCall(call) => Some(*call.ret_addr()),
        EvmInstKind::EvmCallCode(call) => Some(*call.ret_addr()),
        EvmInstKind::EvmDelegateCall(call) => Some(*call.ret_addr()),
        EvmInstKind::EvmStaticCall(call) => Some(*call.ret_addr()),
        _ => None,
    }
}

fn call_result_provenance(
    function: &Function,
    module: &ModuleCtx,
    call_args: &[ValueId],
    summary: &PtrEscapeSummary,
    prov: &SecondaryMap<ValueId, Provenance>,
    ret_idx: usize,
    def: ValueId,
) -> Provenance {
    let mut next = Provenance::default();
    for &idx in summary.returned_arg_indices(ret_idx) {
        if let Some(&arg) = call_args.get(idx as usize) {
            let _ = next.union_with(&prov[arg]);
        }
    }
    let def_ty = function.dfg.value_ty(def);
    if summary.return_may_be_non_arg_pointer(ret_idx)
        && type_can_carry_pointer_provenance(module, def_ty)
    {
        let _ = next.mark_unknown_non_arg();
    } else if def_ty.is_pointer(module) && next.has_no_known_bases() && !next.is_unknown_ptr() {
        // Pointer-typed calls with incomplete summaries still produce pointer values.
        let _ = next.mark_unknown_non_arg();
    }
    next
}

pub(crate) fn type_can_carry_pointer_provenance(module: &ModuleCtx, ty: Type) -> bool {
    // TODO: This is dual-use encoded-pointer carrier logic, not provenance-specific.
    // Move it to a shared EVM helper with a clearer name and cache recursive type queries.
    let mut seen = FxHashSet::default();
    type_can_carry_pointer_provenance_inner(module, ty, &mut seen)
}

fn type_can_carry_pointer_provenance_inner(
    module: &ModuleCtx,
    ty: Type,
    seen: &mut FxHashSet<CompoundTypeRef>,
) -> bool {
    match ty {
        Type::I256 => true,
        Type::I1 | Type::I8 | Type::I16 | Type::I32 | Type::I64 | Type::I128 | Type::Unit => false,
        Type::EnumTag(_) => false,
        Type::Compound(compound) => {
            if !seen.insert(compound) {
                return false;
            }

            match module.with_ty_store(|store| store.resolve_compound(compound).clone()) {
                CompoundType::Ptr(_) | CompoundType::ObjRef(_) | CompoundType::ConstRef(_) => true,
                CompoundType::Array { elem, .. } => {
                    type_can_carry_pointer_provenance_inner(module, elem, seen)
                }
                CompoundType::Struct(data) => data
                    .fields
                    .iter()
                    .any(|&field| type_can_carry_pointer_provenance_inner(module, field, seen)),
                CompoundType::Enum(data) => data.variants.iter().any(|variant| {
                    variant
                        .fields
                        .iter()
                        .any(|&field| type_can_carry_pointer_provenance_inner(module, field, seen))
                }),
                CompoundType::Func { .. } => false,
            }
        }
    }
}

pub(crate) struct ProvenanceInfo {
    pub(crate) value: SecondaryMap<ValueId, Provenance>,
    pub(crate) local_mem: FxHashMap<InstId, Provenance>,
    /// Tracks what the callee stores to arg-backed memory addresses.
    /// Initialized empty (bottom); only callee-initiated stores are recorded.
    /// Used by mcopy handling to determine the provenance of bytes being copied
    /// from arg-addressed memory.
    pub(crate) arg_mem: Vec<Provenance>,
}

pub(crate) fn compute_provenance(
    function: &Function,
    module: &ModuleCtx,
    isa: &Evm,
    callee_summary: impl Fn(FuncRef) -> PtrEscapeSummary,
) -> ProvenanceInfo {
    let mut prov: SecondaryMap<ValueId, Provenance> = SecondaryMap::new();
    for value in function.dfg.value_ids() {
        let _ = &mut prov[value];
    }

    for (idx, &arg) in function.arg_values.iter().enumerate() {
        if function.dfg.value_ty(arg).is_pointer(module) {
            prov[arg].bases.push(PtrBase::Arg(idx as u32));
        }
    }

    for block in function.layout.iter_block() {
        for inst in function.layout.iter_inst(block) {
            let data = isa.inst_set().resolve_inst(function.dfg.inst(inst));
            let [def] = function.dfg.inst_results(inst) else {
                continue;
            };
            match data {
                EvmInstKind::Alloca(_) => prov[*def].bases.push(PtrBase::Alloca(inst)),
                EvmInstKind::EvmMalloc(_) => prov[*def].bases.push(PtrBase::Malloc(inst)),
                _ => {}
            }
        }
    }

    let mut mem: FxHashMap<InstId, Provenance> = FxHashMap::default();
    let mut arg_mem: Vec<Provenance> = vec![Provenance::default(); function.arg_values.len()];

    let mut changed = true;
    while changed {
        changed = false;

        for block in function.layout.iter_block() {
            for inst in function.layout.iter_inst(block) {
                let data = isa.inst_set().resolve_inst(function.dfg.inst(inst));

                if let EvmInstKind::Mstore(mstore) = &data {
                    let addr = &prov[*mstore.addr()];
                    let val = &prov[*mstore.value()];
                    changed |= store_local_mem(&mut mem, addr, val);
                    changed |= store_arg_mem(&mut arg_mem, addr, val);
                }

                if let Some(dst) = unmodeled_write_addr(&data) {
                    changed |= poison_local_mem(&mut mem, &prov[dst]);
                    changed |= poison_arg_mem(&mut arg_mem, &prov[dst]);
                }

                if let EvmInstKind::Call(call) = &data {
                    let summary = callee_summary(*call.callee());
                    let args = call.args();
                    summary.for_each_store_effect(args, |src_idx, dst_actual| {
                        if let Some(&src_actual) = args.get(src_idx) {
                            let src_prov = prov[src_actual].clone();
                            let dst_addr = &prov[dst_actual];
                            changed |= store_local_mem(&mut mem, dst_addr, &src_prov);
                            changed |= store_arg_mem(&mut arg_mem, dst_addr, &src_prov);
                        }
                    });
                    for (ret_idx, &def) in function.dfg.inst_results(inst).iter().enumerate() {
                        let next = call_result_provenance(
                            function, module, args, &summary, &prov, ret_idx, def,
                        );
                        let cur = &mut prov[def];
                        if *cur != next {
                            *cur = next;
                            changed = true;
                        }
                    }
                    continue;
                }

                let [def] = function.dfg.inst_results(inst) else {
                    continue;
                };

                let mut next = Provenance::default();

                match data {
                    EvmInstKind::Alloca(_) => next.bases.push(PtrBase::Alloca(inst)),
                    EvmInstKind::EvmMalloc(_) => next.bases.push(PtrBase::Malloc(inst)),
                    EvmInstKind::Mload(mload) => {
                        let _ = next.union_with(&load_local_mem(&mem, &prov[*mload.addr()]));
                    }
                    EvmInstKind::Phi(phi) => {
                        for (val, _) in phi.args().iter() {
                            let _ = next.union_with(&prov[*val]);
                        }
                    }
                    EvmInstKind::Gep(gep) => {
                        let Some(&base) = gep.values().first() else {
                            continue;
                        };
                        let _ = next.union_with(&prov[base]);
                    }
                    EvmInstKind::Bitcast(bc) => {
                        let _ = next.union_with(&prov[*bc.from()]);
                    }
                    EvmInstKind::IntToPtr(i2p) => {
                        let from = *i2p.from();
                        let from_prov = &prov[from];
                        let _ = next.union_with(from_prov);
                        if from_prov.has_no_known_bases() && !from_prov.is_unknown_ptr() {
                            let _ = next.mark_unknown_non_arg();
                        }
                    }
                    EvmInstKind::PtrToInt(p2i) => {
                        let _ = next.union_with(&prov[*p2i.from()]);
                    }
                    EvmInstKind::InsertValue(iv) => {
                        let _ = next.union_with(&prov[*iv.dest()]);
                        let _ = next.union_with(&prov[*iv.value()]);
                    }
                    EvmInstKind::ExtractValue(ev) => {
                        let _ = next.union_with(&prov[*ev.dest()]);
                    }
                    EvmInstKind::Add(_)
                    | EvmInstKind::Sub(_)
                    | EvmInstKind::Mul(_)
                    | EvmInstKind::And(_)
                    | EvmInstKind::Or(_)
                    | EvmInstKind::Xor(_)
                    | EvmInstKind::Shl(_)
                    | EvmInstKind::Shr(_)
                    | EvmInstKind::Sar(_)
                    | EvmInstKind::Not(_)
                    | EvmInstKind::Sext(_)
                    | EvmInstKind::Zext(_)
                    | EvmInstKind::Trunc(_)
                    | EvmInstKind::EvmSdiv(_)
                    | EvmInstKind::EvmUdiv(_)
                    | EvmInstKind::EvmUmod(_)
                    | EvmInstKind::EvmSmod(_)
                    | EvmInstKind::EvmAddMod(_)
                    | EvmInstKind::EvmMulMod(_)
                    | EvmInstKind::EvmExp(_)
                    | EvmInstKind::EvmSignExtend(_)
                    | EvmInstKind::EvmByte(_)
                    | EvmInstKind::EvmClz(_) => {
                        function.dfg.inst(inst).for_each_value(&mut |v| {
                            let _ = next.union_with(&prov[v]);
                        });
                    }
                    _ => {}
                }

                let cur = &mut prov[*def];
                if *cur != next {
                    *cur = next;
                    changed = true;
                }
            }
        }
    }

    ProvenanceInfo {
        value: prov,
        local_mem: mem,
        arg_mem,
    }
}

pub(crate) fn compute_value_provenance(
    function: &Function,
    module: &ModuleCtx,
    isa: &Evm,
    callee_summary: impl Fn(FuncRef) -> PtrEscapeSummary,
) -> SecondaryMap<ValueId, Provenance> {
    compute_provenance(function, module, isa, callee_summary).value
}

#[cfg(test)]
mod tests {
    use super::{super::ptr_escape::compute_ptr_escape_summaries, *};
    use sonatina_parser::parse_module;
    use sonatina_triple::{Architecture, EvmVersion, OperatingSystem, TargetTriple, Vendor};

    fn ret_provenance(src: &str, func_name: &str) -> Provenance {
        let parsed = parse_module(src).expect("module parses");
        let funcs = parsed.module.funcs();
        let func_ref = parsed
            .module
            .funcs()
            .into_iter()
            .find(|&f| parsed.module.ctx.func_sig(f, |sig| sig.name() == func_name))
            .expect("function exists");

        let isa = Evm::new(TargetTriple {
            architecture: Architecture::Evm,
            vendor: Vendor::Ethereum,
            operating_system: OperatingSystem::Evm(EvmVersion::Osaka),
        });

        let summaries = compute_ptr_escape_summaries(&parsed.module, &funcs, &isa);

        parsed.module.func_store.view(func_ref, |function| {
            let prov = compute_value_provenance(function, &parsed.module.ctx, &isa, |callee| {
                PtrEscapeSummary::get_or_conservative(&summaries, &parsed.module.ctx, callee)
            });

            for block in function.layout.iter_block() {
                for inst in function.layout.iter_inst(block) {
                    let data = isa.inst_set().resolve_inst(function.dfg.inst(inst));
                    if let EvmInstKind::Return(_) = data
                        && let Some(ret_val) = function
                            .dfg
                            .return_args(inst)
                            .and_then(|args| args.first().copied())
                    {
                        return prov[ret_val].clone();
                    }
                }
            }

            panic!("no return value in function");
        })
    }

    #[test]
    fn union_preserves_exact_bases_when_unknown_non_arg_is_present() {
        let alloca = InstId(1);
        let malloc = InstId(2);
        let mut lhs = Provenance {
            bases: SmallVec::from_vec(vec![PtrBase::Alloca(alloca), PtrBase::Arg(0)]),
            unknown_arg_indices: SmallVec::new(),
            unknown_non_arg: false,
        };
        let rhs = Provenance {
            bases: SmallVec::from_vec(vec![PtrBase::Malloc(malloc), PtrBase::Arg(1)]),
            unknown_arg_indices: SmallVec::from_vec(vec![2]),
            unknown_non_arg: true,
        };

        assert!(lhs.mark_unknown_non_arg());
        assert!(lhs.union_with(&rhs));

        assert!(lhs.is_unknown_ptr());
        assert_eq!(lhs.alloca_insts().collect::<Vec<_>>(), vec![alloca]);
        assert_eq!(lhs.malloc_insts().collect::<Vec<_>>(), vec![malloc]);
        assert_eq!(lhs.arg_indices().collect::<Vec<_>>(), vec![0, 1, 2]);
    }

    #[test]
    fn int_to_ptr_from_integer_is_unknown_non_arg() {
        let ret_prov = ret_provenance(
            r#"
target = "evm-ethereum-osaka"

func public %f() -> *i8 {
block0:
    v0.*i8 = int_to_ptr 0.i32 *i8;
    return v0;
}
"#,
            "f",
        );

        assert!(ret_prov.is_unknown_ptr());
        assert_eq!(
            ret_prov.arg_indices().collect::<Vec<_>>(),
            Vec::<u32>::new()
        );
    }

    #[test]
    fn ptr_to_int_int_to_ptr_roundtrip_keeps_arg_attribution() {
        let ret_prov = ret_provenance(
            r#"
target = "evm-ethereum-osaka"

func public %f(v0.*i8) -> *i8 {
block0:
    v1.i256 = ptr_to_int v0 i256;
    v2.i256 = add v1 32.i256;
    v3.*i8 = int_to_ptr v2 *i8;
    return v3;
}
"#,
            "f",
        );

        assert!(!ret_prov.is_unknown_ptr());
        assert_eq!(ret_prov.arg_indices().collect::<Vec<_>>(), vec![0]);
    }

    #[test]
    fn local_mem_poison_preserves_arg_attribution() {
        let ret_prov = ret_provenance(
            r#"
target = "evm-ethereum-osaka"

func public %f(v0.*i8) -> *i8 {
block0:
    v1.*i256 = alloca i256;
    mstore v1 v0 *i8;
    v2.i256 = ptr_to_int v1 i256;
    evm_mstore8 v2 1.i8;
    v3.*i8 = mload v1 *i8;
    return v3;
}
"#,
            "f",
        );

        assert!(ret_prov.is_unknown_ptr());
        assert_eq!(ret_prov.arg_indices().collect::<Vec<_>>(), vec![0]);
    }

    #[test]
    fn mixed_unknown_call_result_preserves_alloca_through_carrier() {
        let ret_prov = ret_provenance(
            r#"
target = "evm-ethereum-osaka"

func public %maybe_arg(v0.*i8, v1.i1) -> *i8 {
block0:
    br v1 block1 block2;

block1:
    return v0;

block2:
    v2.*i8 = int_to_ptr 0.i32 *i8;
    return v2;
}

func public %caller(v0.i1) -> *i8 {
block0:
    v1.*i8 = alloca i8;
    v2.*i8 = call %maybe_arg v1 v0;
    v3.i256 = ptr_to_int v2 i256;
    v4.i256 = add v3 0.i256;
    v5.*i8 = int_to_ptr v4 *i8;
    return v5;
}
"#,
            "caller",
        );

        assert!(ret_prov.is_unknown_ptr(), "{ret_prov:?}");
        assert_eq!(ret_prov.alloca_insts().count(), 1, "{ret_prov:?}");
    }

    #[test]
    fn call_result_preserves_i256_encoded_malloc_returned_in_aggregate() {
        let ret_prov = ret_provenance(
            r#"
target = "evm-ethereum-osaka"

type @Bytes = {i256, i256};

func public %from_ptr(v0.i256, v1.i256) -> @Bytes {
block0:
    v2.@Bytes = insert_value undef.@Bytes 0.i256 v0;
    v3.@Bytes = insert_value v2 1.i256 v1;
    return v3;
}

func public %caller() -> @Bytes {
block0:
    v0.*i8 = evm_malloc 32.i256;
    v1.i256 = ptr_to_int v0 i256;
    v2.@Bytes = call %from_ptr v1 32.i256;
    return v2;
}
"#,
            "caller",
        );

        assert!(!ret_prov.is_unknown_ptr(), "{ret_prov:?}");
        assert_eq!(ret_prov.malloc_insts().count(), 1, "{ret_prov:?}");
    }

    #[test]
    fn multi_result_call_preserves_i256_encoded_malloc_return() {
        let ret_prov = ret_provenance(
            r#"
target = "evm-ethereum-osaka"

func public %from_ptr(v0.i256, v1.i256) -> (i256, i256) {
block0:
    return (v0, v1);
}

func public %caller() -> i256 {
block0:
    v0.*i8 = evm_malloc 32.i256;
    v1.i256 = ptr_to_int v0 i256;
    (v2.i256, v3.i256) = call %from_ptr v1 32.i256;
    return v2;
}
"#,
            "caller",
        );

        assert!(!ret_prov.is_unknown_ptr(), "{ret_prov:?}");
        assert_eq!(ret_prov.malloc_insts().count(), 1, "{ret_prov:?}");
    }

    #[test]
    fn multi_result_call_does_not_taint_unrelated_i256_result() {
        let ret_prov = ret_provenance(
            r#"
target = "evm-ethereum-osaka"

func public %mk() -> (i256, i256) {
block0:
    v0.*i8 = evm_malloc 32.i256;
    v1.i256 = ptr_to_int v0 i256;
    return (7.i256, v1);
}

func public %caller() -> i256 {
block0:
    (v0.i256, v1.i256) = call %mk;
    return v0;
}
"#,
            "caller",
        );

        assert!(!ret_prov.is_unknown_ptr(), "{ret_prov:?}");
        assert_eq!(ret_prov.malloc_insts().count(), 0, "{ret_prov:?}");
    }

    #[test]
    fn scalar_i256_arg_forwarding_does_not_create_pointer_provenance() {
        let ret_prov = ret_provenance(
            r#"
target = "evm-ethereum-osaka"

func public %id(v0.i256) -> i256 {
block0:
    return v0;
}

func public %caller(v0.i256) -> i256 {
block0:
    v1.i256 = call %id v0;
    return v1;
}
"#,
            "caller",
        );

        assert!(!ret_prov.is_unknown_ptr(), "{ret_prov:?}");
        assert_eq!(
            ret_prov.arg_indices().collect::<Vec<_>>(),
            Vec::<u32>::new()
        );
        assert_eq!(ret_prov.malloc_insts().count(), 0, "{ret_prov:?}");
    }

    #[test]
    fn call_result_marks_i256_encoded_non_arg_pointer_return_unknown() {
        let ret_prov = ret_provenance(
            r#"
target = "evm-ethereum-osaka"

func public %mk() -> i256 {
block0:
    v0.*i8 = evm_malloc 32.i256;
    v1.i256 = ptr_to_int v0 i256;
    return v1;
}

func public %caller() -> i256 {
block0:
    v0.i256 = call %mk;
    return v0;
}
"#,
            "caller",
        );

        assert!(ret_prov.is_unknown_ptr(), "{ret_prov:?}");
        assert_eq!(
            ret_prov.arg_indices().collect::<Vec<_>>(),
            Vec::<u32>::new()
        );
    }
}
