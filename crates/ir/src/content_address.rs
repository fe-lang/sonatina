use std::collections::{BTreeMap, BTreeSet};

use crate::{BlockId, DebugTagPayload, Function, InstId, Value};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum ShapeDimension {
    Structure,
    OpcodeKind,
    TypeSensitive,
    ConstantsSensitive,
    DebugOriginSensitive,
    DebugOriginElided,
    LayoutSensitive,
    LayoutElided,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShapeHashPolicy {
    dimensions: BTreeSet<ShapeDimension>,
}

impl ShapeHashPolicy {
    pub fn new(dimensions: impl IntoIterator<Item = ShapeDimension>) -> Self {
        Self {
            dimensions: dimensions.into_iter().collect(),
        }
    }

    pub fn structure() -> Self {
        Self::new([ShapeDimension::Structure, ShapeDimension::LayoutElided])
    }

    pub fn contains(&self, dimension: ShapeDimension) -> bool {
        self.dimensions.contains(&dimension)
    }

    pub fn dimensions(&self) -> &BTreeSet<ShapeDimension> {
        &self.dimensions
    }

    fn layout_sensitive(&self) -> bool {
        self.contains(ShapeDimension::LayoutSensitive)
            && !self.contains(ShapeDimension::LayoutElided)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FunctionShapeHashes {
    pub function_hash: String,
    pub block_hashes: BTreeMap<BlockId, String>,
    pub instruction_hashes: BTreeMap<InstId, String>,
    pub scc_hashes: Vec<ShapeSccHash>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShapeSccHash {
    pub blocks: Vec<BlockId>,
    pub hash: String,
}

pub fn hash_function_shape(func: &Function, policy: &ShapeHashPolicy) -> FunctionShapeHashes {
    let instruction_hashes = hash_instructions(func, policy);
    let block_hashes = hash_blocks(func, policy, &instruction_hashes);
    let sccs = cfg_sccs(func);
    let scc_hashes = hash_sccs(func, policy, &block_hashes, &sccs);
    let function_hash = if policy.layout_sensitive() {
        hash_layout_sensitive_function(func, policy, &block_hashes)
    } else {
        hash_layout_elided_function(func, policy, &scc_hashes)
    };

    FunctionShapeHashes {
        function_hash,
        block_hashes,
        instruction_hashes,
        scc_hashes,
    }
}

fn hash_instructions(func: &Function, policy: &ShapeHashPolicy) -> BTreeMap<InstId, String> {
    func.dfg
        .inst_ids()
        .map(|inst| (inst, hash_instruction(func, inst, policy)))
        .collect()
}

fn hash_instruction(func: &Function, inst: InstId, policy: &ShapeHashPolicy) -> String {
    let data = func.dfg.inst(inst);
    let mut fields = Vec::new();
    fields.push(format!("policy:{:?}", policy.dimensions()));
    fields.push(format!("arity:{:?}", data.arity()));
    fields.push(format!("terminator:{}", data.is_terminator()));
    fields.push(format!("results:{}", func.dfg.inst_results(inst).len()));

    let operands = data.collect_values();
    fields.push(format!("operands:{}", operands.len()));
    for value in &operands {
        fields.push(format!("operand_kind:{:?}", value_kind(func, *value)));
    }

    if policy.contains(ShapeDimension::OpcodeKind) {
        fields.push(format!("opcode:{}", data.as_text()));
        fields.push(format!("class:{:?}", data.kind()));
    }

    if policy.contains(ShapeDimension::TypeSensitive) {
        for value in &operands {
            fields.push(format!("operand_ty:{:?}", func.dfg.value_ty(*value)));
        }
        for value in func.dfg.inst_results(inst) {
            fields.push(format!("result_ty:{:?}", func.dfg.value_ty(*value)));
        }
    }

    if policy.contains(ShapeDimension::ConstantsSensitive) {
        for value in &operands {
            if let Value::Immediate { imm, .. } = func.dfg.value(*value) {
                fields.push(format!("imm:{imm:?}"));
            }
        }
    }

    if policy.contains(ShapeDimension::DebugOriginSensitive) {
        fields.extend(debug_fields(func, inst));
    } else if policy.contains(ShapeDimension::DebugOriginElided) {
        fields.push("debug:elided".to_string());
    }

    digest("sonatina.inst.v1", fields)
}

fn hash_blocks(
    func: &Function,
    policy: &ShapeHashPolicy,
    instruction_hashes: &BTreeMap<InstId, String>,
) -> BTreeMap<BlockId, String> {
    func.layout
        .iter_block()
        .map(|block| {
            let mut fields = Vec::new();
            let insts: Vec<_> = func.layout.iter_inst(block).collect();
            fields.push(format!("inst_count:{}", insts.len()));
            for inst in insts {
                fields.push(format!("inst:{}", instruction_hashes[&inst]));
            }
            for edge in block_edges(func, block) {
                if policy.layout_sensitive() {
                    fields.push(format!("edge:{}:{}", edge.ordinal, edge.to.as_u32()));
                } else {
                    fields.push(format!("edge:{}", edge.ordinal));
                }
            }
            (block, digest("sonatina.block.v1", fields))
        })
        .collect()
}

fn hash_layout_sensitive_function(
    func: &Function,
    policy: &ShapeHashPolicy,
    block_hashes: &BTreeMap<BlockId, String>,
) -> String {
    let mut fields = Vec::new();
    fields.push(format!("policy:{:?}", policy.dimensions()));
    for (ordinal, block) in func.layout.iter_block().enumerate() {
        fields.push(format!("block:{ordinal}:{}", block_hashes[&block]));
        for edge in block_edges(func, block) {
            fields.push(format!(
                "edge:{ordinal}:{}:{}",
                edge.ordinal,
                edge.to.as_u32()
            ));
        }
    }
    digest("sonatina.function.layout-sensitive.v1", fields)
}

fn hash_layout_elided_function(
    func: &Function,
    policy: &ShapeHashPolicy,
    scc_hashes: &[ShapeSccHash],
) -> String {
    let component_index = component_index(scc_hashes);
    let mut fields = Vec::new();
    fields.push(format!("policy:{:?}", policy.dimensions()));

    let mut component_hashes: Vec<_> = scc_hashes.iter().map(|scc| scc.hash.clone()).collect();
    component_hashes.sort();
    for hash in component_hashes {
        fields.push(format!("component:{hash}"));
    }

    let mut inter_edges = Vec::new();
    for block in func.layout.iter_block() {
        let Some(&from_component) = component_index.get(&block) else {
            continue;
        };
        for edge in block_edges(func, block) {
            let Some(&to_component) = component_index.get(&edge.to) else {
                continue;
            };
            if from_component != to_component {
                inter_edges.push(format!(
                    "{}:{}:{}",
                    scc_hashes[from_component].hash, edge.ordinal, scc_hashes[to_component].hash
                ));
            }
        }
    }
    inter_edges.sort();
    fields.extend(inter_edges.into_iter().map(|edge| format!("edge:{edge}")));

    digest("sonatina.function.layout-elided.v1", fields)
}

fn hash_sccs(
    func: &Function,
    policy: &ShapeHashPolicy,
    block_hashes: &BTreeMap<BlockId, String>,
    sccs: &[Vec<BlockId>],
) -> Vec<ShapeSccHash> {
    let component_index = sccs
        .iter()
        .enumerate()
        .flat_map(|(idx, blocks)| blocks.iter().copied().map(move |block| (block, idx)))
        .collect::<BTreeMap<_, _>>();

    let mut hashes = Vec::new();
    for blocks in sccs {
        let mut sorted_blocks = blocks.clone();
        sorted_blocks.sort_by(|lhs, rhs| {
            block_hashes[lhs]
                .cmp(&block_hashes[rhs])
                .then_with(|| lhs.cmp(rhs))
        });

        let mut fields = Vec::new();
        fields.push(format!("policy:{:?}", policy.dimensions()));
        for block in &sorted_blocks {
            fields.push(format!("block:{}", block_hashes[block]));
        }

        let mut internal_edges = Vec::new();
        for &block in blocks {
            for edge in block_edges(func, block) {
                if component_index.get(&edge.to) == component_index.get(&block) {
                    internal_edges.push(format!(
                        "{}:{}:{}",
                        block_hashes[&block], edge.ordinal, block_hashes[&edge.to]
                    ));
                }
            }
        }
        internal_edges.sort();
        fields.extend(
            internal_edges
                .into_iter()
                .map(|edge| format!("edge:{edge}")),
        );

        hashes.push(ShapeSccHash {
            blocks: sorted_blocks,
            hash: digest("sonatina.scc.v1", fields),
        });
    }

    hashes.sort_by(|lhs, rhs| {
        lhs.hash
            .cmp(&rhs.hash)
            .then_with(|| lhs.blocks.cmp(&rhs.blocks))
    });
    hashes
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ValueKind {
    Arg,
    Inst,
    Immediate,
    Global,
    Undef,
}

fn value_kind(func: &Function, value: crate::ValueId) -> ValueKind {
    match func.dfg.value(value) {
        Value::Arg { .. } => ValueKind::Arg,
        Value::Inst { .. } => ValueKind::Inst,
        Value::Immediate { .. } => ValueKind::Immediate,
        Value::Global { .. } => ValueKind::Global,
        Value::Undef { .. } => ValueKind::Undef,
    }
}

fn debug_fields(func: &Function, inst: InstId) -> Vec<String> {
    let mut fields = Vec::new();
    if let Some(loc) = func
        .inst_debug_loc(inst)
        .and_then(|loc| func.debug.debug_loc(loc))
    {
        fields.push(format!("debug_confidence:{:?}", loc.confidence));
        if let Some(origin) = loc
            .primary_origin
            .and_then(|id| func.debug.frontend_origin(id))
        {
            fields.push(format!("debug_origin_kind:{:?}", origin.kind));
            fields.push(format!(
                "debug_origin_key:{}",
                origin.external_key.as_deref().unwrap_or("")
            ));
            fields.push(format!(
                "debug_origin_label:{}",
                origin.display_label.as_deref().unwrap_or("")
            ));
        }
    }

    for tag in func
        .inst_debug_tags(inst)
        .iter()
        .filter_map(|&tag| func.debug.debug_tag(tag))
    {
        fields.push(format!("debug_tag:{:?}", tag.kind));
        if let Some(origin) = tag.origin.and_then(|id| func.debug.frontend_origin(id)) {
            fields.push(format!(
                "debug_tag_origin:{}",
                origin.external_key.as_deref().unwrap_or("")
            ));
        }
        fields.push(format!(
            "debug_tag_payload:{}",
            debug_payload_text(&tag.payload)
        ));
    }

    fields
}

fn debug_payload_text(payload: &DebugTagPayload) -> String {
    match payload {
        DebugTagPayload::Empty => String::new(),
        DebugTagPayload::Text(text) => text.clone(),
        DebugTagPayload::KeyValue { key, value } => format!("{key}={value}"),
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ShapeCfgEdge {
    to: BlockId,
    ordinal: usize,
}

fn block_edges(func: &Function, block: BlockId) -> Vec<ShapeCfgEdge> {
    let Some(Some(term)) = func.layout.try_last_inst_of(block) else {
        return Vec::new();
    };
    let Some(branch) = func.dfg.branch_info(term) else {
        return Vec::new();
    };
    branch
        .dests()
        .into_iter()
        .enumerate()
        .map(|(ordinal, to)| ShapeCfgEdge { to, ordinal })
        .collect()
}

fn cfg_sccs(func: &Function) -> Vec<Vec<BlockId>> {
    let blocks: Vec<_> = func.layout.iter_block().collect();
    let block_set: BTreeSet<_> = blocks.iter().copied().collect();
    let mut state = TarjanState::default();
    for block in blocks {
        if !state.indices.contains_key(&block) {
            strong_connect(func, &block_set, block, &mut state);
        }
    }
    state.components
}

#[derive(Default)]
struct TarjanState {
    next_index: usize,
    stack: Vec<BlockId>,
    on_stack: BTreeSet<BlockId>,
    indices: BTreeMap<BlockId, usize>,
    lowlinks: BTreeMap<BlockId, usize>,
    components: Vec<Vec<BlockId>>,
}

fn strong_connect(
    func: &Function,
    block_set: &BTreeSet<BlockId>,
    block: BlockId,
    state: &mut TarjanState,
) {
    let index = state.next_index;
    state.next_index += 1;
    state.indices.insert(block, index);
    state.lowlinks.insert(block, index);
    state.stack.push(block);
    state.on_stack.insert(block);

    for edge in block_edges(func, block) {
        if !block_set.contains(&edge.to) {
            continue;
        }
        if !state.indices.contains_key(&edge.to) {
            strong_connect(func, block_set, edge.to, state);
            let low = state.lowlinks[&block].min(state.lowlinks[&edge.to]);
            state.lowlinks.insert(block, low);
        } else if state.on_stack.contains(&edge.to) {
            let low = state.lowlinks[&block].min(state.indices[&edge.to]);
            state.lowlinks.insert(block, low);
        }
    }

    if state.lowlinks[&block] == state.indices[&block] {
        let mut component = Vec::new();
        loop {
            let member = state
                .stack
                .pop()
                .expect("tarjan stack should contain current component");
            state.on_stack.remove(&member);
            component.push(member);
            if member == block {
                break;
            }
        }
        component.sort();
        state.components.push(component);
    }
}

fn component_index(scc_hashes: &[ShapeSccHash]) -> BTreeMap<BlockId, usize> {
    scc_hashes
        .iter()
        .enumerate()
        .flat_map(|(idx, scc)| scc.blocks.iter().copied().map(move |block| (block, idx)))
        .collect()
}

fn digest(domain: &str, fields: Vec<String>) -> String {
    let mut hasher = blake3::Hasher::new();
    write_field(&mut hasher, domain);
    for field in fields {
        write_field(&mut hasher, &field);
    }
    hasher.finalize().to_hex().to_string()
}

fn write_field(hasher: &mut blake3::Hasher, field: &str) {
    hasher.update(&(field.len() as u64).to_le_bytes());
    hasher.update(field.as_bytes());
}

#[cfg(test)]
mod tests {
    use sonatina_triple::{Architecture, EvmVersion, OperatingSystem, TargetTriple, Vendor};

    use crate::{
        DebugConfidence, DebugLoc, FrontendOriginKind, FrontendOriginRecord, Linkage, Module,
        Signature, Type,
        builder::ModuleBuilder,
        func_cursor::InstInserter,
        inst::{
            arith::Add,
            control_flow::{Br, Jump, Return},
        },
        isa::{Isa, evm::Evm},
        module::ModuleCtx,
    };

    use super::{ShapeDimension, ShapeHashPolicy, hash_function_shape};

    #[test]
    fn constants_dimension_changes_constants_without_changing_structure() {
        let a = single_add_function(2, None);
        let b = single_add_function(3, None);
        let structure = ShapeHashPolicy::new([
            ShapeDimension::Structure,
            ShapeDimension::OpcodeKind,
            ShapeDimension::LayoutElided,
        ]);
        let constants = ShapeHashPolicy::new([
            ShapeDimension::Structure,
            ShapeDimension::OpcodeKind,
            ShapeDimension::ConstantsSensitive,
            ShapeDimension::LayoutElided,
        ]);

        assert_eq!(function_hash(&a, &structure), function_hash(&b, &structure));
        assert_ne!(function_hash(&a, &constants), function_hash(&b, &constants));
    }

    #[test]
    fn debug_sensitive_hash_changes_when_debug_origin_changes() {
        let a = single_add_function(2, Some("origin-a"));
        let b = single_add_function(2, Some("origin-b"));
        let debug_sensitive = ShapeHashPolicy::new([
            ShapeDimension::Structure,
            ShapeDimension::OpcodeKind,
            ShapeDimension::DebugOriginSensitive,
            ShapeDimension::LayoutElided,
        ]);
        let debug_elided = ShapeHashPolicy::new([
            ShapeDimension::Structure,
            ShapeDimension::OpcodeKind,
            ShapeDimension::DebugOriginElided,
            ShapeDimension::LayoutElided,
        ]);

        assert_ne!(
            function_hash(&a, &debug_sensitive),
            function_hash(&b, &debug_sensitive)
        );
        assert_eq!(
            function_hash(&a, &debug_elided),
            function_hash(&b, &debug_elided)
        );
    }

    #[test]
    fn layout_elided_hash_is_stable_across_block_insertion_order() {
        let a = branch_function(false);
        let b = branch_function(true);
        let elided = ShapeHashPolicy::new([
            ShapeDimension::Structure,
            ShapeDimension::OpcodeKind,
            ShapeDimension::LayoutElided,
        ]);
        let sensitive = ShapeHashPolicy::new([
            ShapeDimension::Structure,
            ShapeDimension::OpcodeKind,
            ShapeDimension::LayoutSensitive,
        ]);

        assert_eq!(function_hash(&a, &elided), function_hash(&b, &elided));
        assert_ne!(function_hash(&a, &sensitive), function_hash(&b, &sensitive));
    }

    #[test]
    fn cyclic_cfg_hashes_through_scc_condensation() {
        let module = loop_function();
        let policy = ShapeHashPolicy::new([
            ShapeDimension::Structure,
            ShapeDimension::OpcodeKind,
            ShapeDimension::LayoutElided,
        ]);
        let hashes = module.func_store.view(module.funcs()[0], |func| {
            let first = hash_function_shape(func, &policy);
            let second = hash_function_shape(func, &policy);
            assert_eq!(first.function_hash, second.function_hash);
            first
        });

        assert!(hashes.scc_hashes.iter().any(|scc| scc.blocks.len() > 1));
    }

    fn function_hash(module: &Module, policy: &ShapeHashPolicy) -> String {
        module.func_store.view(module.funcs()[0], |func| {
            hash_function_shape(func, policy).function_hash
        })
    }

    fn test_module_builder() -> (Evm, ModuleBuilder) {
        let triple = TargetTriple::new(
            Architecture::Evm,
            Vendor::Ethereum,
            OperatingSystem::Evm(EvmVersion::London),
        );
        let evm = Evm::new(triple);
        let ctx = ModuleCtx::new(&evm);
        (evm, ModuleBuilder::new(ctx))
    }

    fn single_add_function(rhs_value: i32, debug_key: Option<&str>) -> Module {
        let (_evm, mb) = test_module_builder();
        let func_ref = mb
            .declare_function(Signature::new_single(
                "add",
                Linkage::Public,
                &[],
                Type::I32,
            ))
            .unwrap();
        let mut builder = mb.func_builder::<InstInserter>(func_ref);
        let block = builder.append_block();
        builder.switch_to_block(block);
        let lhs = builder.make_imm_value(1i32);
        let rhs = builder.make_imm_value(rhs_value);
        let has_add = builder.inst_set().has_add().unwrap();
        let value = builder.insert_inst(Add::new(has_add, lhs, rhs), Type::I32);
        let inst = builder.func.dfg.value_inst(value).unwrap();
        if let Some(debug_key) = debug_key {
            let origin = builder
                .func
                .debug
                .add_frontend_origin(FrontendOriginRecord {
                    external_key: Some(debug_key.to_string()),
                    source_span: None,
                    display_label: None,
                    kind: FrontendOriginKind::SourceExpr,
                });
            let loc = builder.func.debug.add_debug_loc(DebugLoc {
                primary_origin: Some(origin),
                source_span: None,
                confidence: DebugConfidence::Exact,
            });
            builder.func.set_inst_debug_loc(inst, loc);
        }
        builder.insert_return(value);
        builder.seal_all();
        builder.finish();
        mb.build()
    }

    fn branch_function(reordered_layout: bool) -> Module {
        let (evm, mb) = test_module_builder();
        let is = evm.inst_set();
        let func_ref = mb
            .declare_function(Signature::new_single(
                "branch",
                Linkage::Public,
                &[Type::I1],
                Type::I32,
            ))
            .unwrap();
        let mut builder = mb.func_builder::<InstInserter>(func_ref);
        let entry = builder.append_block();
        let first = builder.append_block();
        let second = builder.append_block();
        let (body, exit) = if reordered_layout {
            (second, first)
        } else {
            (first, second)
        };
        let cond = builder.args()[0];

        builder.switch_to_block(entry);
        builder.insert_inst_no_result(Br::new(is, cond, body, exit));

        builder.switch_to_block(body);
        let value = builder.make_imm_value(7i32);
        builder.insert_inst_no_result(Jump::new(is, exit));

        builder.switch_to_block(exit);
        builder.insert_return(value);
        builder.seal_all();
        builder.finish();
        mb.build()
    }

    fn loop_function() -> Module {
        let (evm, mb) = test_module_builder();
        let is = evm.inst_set();
        let func_ref = mb
            .declare_function(Signature::new_single(
                "loop",
                Linkage::Public,
                &[Type::I1],
                Type::I32,
            ))
            .unwrap();
        let mut builder = mb.func_builder::<InstInserter>(func_ref);
        let entry = builder.append_block();
        let header = builder.append_block();
        let body = builder.append_block();
        let exit = builder.append_block();
        let cond = builder.args()[0];

        builder.switch_to_block(entry);
        builder.insert_inst_no_result(Jump::new(is, header));

        builder.switch_to_block(header);
        builder.insert_inst_no_result(Br::new(is, cond, body, exit));

        builder.switch_to_block(body);
        builder.insert_inst_no_result(Jump::new(is, header));

        builder.switch_to_block(exit);
        let value = builder.make_imm_value(0i32);
        builder.insert_inst_no_result(Return::new_single(is, value));
        builder.seal_all();
        builder.finish();
        mb.build()
    }
}
