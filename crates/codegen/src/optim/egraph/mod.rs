mod elaborate;
mod pass;

pub use elaborate::{EggTerm, Elaborator};
pub use pass::run_egraph_pass;

use std::fmt::Write;

use cranelift_entity::SecondaryMap;
use egglog::EGraph;
use rustc_hash::FxHashSet;
use sonatina_ir::{
    BlockId, Function, InstDowncast, InstId, Type, U256, Value, ValueId,
    cfg::ControlFlowGraph,
    inst::{SideEffect, arith::*, cast::*, cmp::*, control_flow::Phi, data::*, evm::*, logic::*},
    module::FuncAttrs,
};

const TYPES: &str = include_str!("types.egg");
const EXPRS: &str = include_str!("expr.egg");
const RULES: &str = include_str!("rules.egg");
const MEMORY: &str = include_str!("memory.egg");

/// Run egglog optimization on the given program.
pub fn run_egglog(program: &str) -> egglog::EGraph {
    let full_program = format!("{}\n{}\n{}\n{}\n{}", TYPES, EXPRS, RULES, MEMORY, program);
    let mut egraph = EGraph::default();
    egraph.parse_and_run_program(None, &full_program).unwrap();
    egraph
}

pub fn func_to_egglog(func: &Function) -> String {
    let mut out = String::new();
    let mut body = String::new();
    let mut mem_state_counter: u32 = 0;
    let predeclared_values = collect_forward_decl_values(func);

    // Compute CFG for predecessor information
    let mut cfg = ControlFlowGraph::new();
    cfg.compute(func);

    // Track exit memory state per block
    let mut block_exit_mem: SecondaryMap<BlockId, u32> = SecondaryMap::new();
    let mut memphis: Vec<(u32, usize)> = Vec::new();
    let mut pending_memphi_preds: Vec<(u32, usize, BlockId)> = Vec::new();
    let mut processed: FxHashSet<BlockId> = FxHashSet::default();

    // Define function arguments
    for (idx, &arg_val) in func.arg_values.iter().enumerate() {
        let ty = func.dfg.value_ty(arg_val);
        writeln!(
            &mut out,
            "(let {} (Arg {} {}))",
            value_name(arg_val),
            idx,
            type_to_egglog(ty)
        )
        .unwrap();
    }

    // Predeclare values that may be referenced before their defining instruction is emitted.
    for block in func.layout.iter_block() {
        for inst_id in func.layout.iter_inst(block) {
            if let Some(result) = func.dfg.inst_result(inst_id)
                && predeclared_values.contains(&result)
            {
                writeln!(&mut out, "{}", side_effect_result_to_egglog(func, result)).unwrap();
            }
        }
    }

    // Process blocks in RPO (reverse post-order) for proper dataflow
    let rpo: Vec<BlockId> = cfg
        .post_order()
        .collect::<Vec<_>>()
        .into_iter()
        .rev()
        .collect();

    for block in rpo {
        writeln!(&mut body, "; block{}", block.as_u32()).unwrap();

        // Determine entry memory state for this block
        let preds: Vec<BlockId> = cfg.preds_of(block).copied().collect();
        let entry_mem_id = if preds.is_empty() {
            // Entry block: use initial memory state 0
            0
        } else if preds.len() == 1 && processed.contains(&preds[0]) {
            // Single predecessor: use its exit memory state.
            block_exit_mem[preds[0]]
        } else {
            // Multiple predecessors or a backedge: create a MemPhi.
            mem_state_counter += 1;
            let memphi_id = mem_state_counter;
            memphis.push((memphi_id, preds.len()));
            for (pred_idx, pred_block) in preds.into_iter().enumerate() {
                pending_memphi_preds.push((memphi_id, pred_idx, pred_block));
            }
            memphi_id
        };

        let mut current_mem = format!("mem{}", entry_mem_id);

        // Process instructions in this block
        for inst_id in func.layout.iter_inst(block) {
            if let Some((s, new_mem)) = inst_to_egglog_with_mem(
                func,
                inst_id,
                &current_mem,
                &mut mem_state_counter,
                &predeclared_values,
            ) {
                writeln!(&mut body, "{}", s).unwrap();
                if let Some(m) = new_mem {
                    current_mem = m;
                }
            }
        }

        // Record exit memory state for this block
        let exit_mem_id: u32 = current_mem
            .strip_prefix("mem")
            .and_then(|s| s.parse().ok())
            .unwrap_or(0);
        block_exit_mem[block] = exit_mem_id;
        processed.insert(block);
    }

    for (memphi_id, num_preds) in memphis {
        writeln!(&mut out, "(is-memphi {})", memphi_id).unwrap();
        writeln!(
            &mut out,
            "(set (memphi-num-preds {}) {})",
            memphi_id, num_preds
        )
        .unwrap();
    }

    for (memphi_id, pred_idx, pred_block) in pending_memphi_preds {
        if !processed.contains(&pred_block) {
            continue;
        }

        let pred_mem = block_exit_mem[pred_block];
        writeln!(
            &mut out,
            "(set (memphi-pred {} {}) {})",
            memphi_id, pred_idx, pred_mem
        )
        .unwrap();
    }

    out.push_str(&body);
    out
}

fn inst_to_egglog(
    func: &Function,
    inst_id: InstId,
    predeclared_values: &FxHashSet<ValueId>,
) -> Option<String> {
    let inst = func.dfg.inst(inst_id);
    let is = func.inst_set();
    let result = func.dfg.inst_result(inst_id);

    macro_rules! try_binary {
        ($inst_ty:ty, $op:literal) => {
            if let Some(i) = <&$inst_ty>::downcast(is, inst) {
                let result = result?;
                return Some(bind_result_expr(
                    result,
                    format!(
                        "({} {} {})",
                        $op,
                        value_to_egglog(func, *i.lhs()),
                        value_to_egglog(func, *i.rhs())
                    ),
                    predeclared_values,
                ));
            }
        };
    }

    macro_rules! try_unary {
        ($inst_ty:ty, $op:literal) => {
            if let Some(i) = <&$inst_ty>::downcast(is, inst) {
                let result = result?;
                return Some(bind_result_expr(
                    result,
                    format!("({} {})", $op, value_to_egglog(func, *i.arg())),
                    predeclared_values,
                ));
            }
        };
    }

    macro_rules! try_cast {
        ($inst_ty:ty, $op:literal) => {
            if let Some(i) = <&$inst_ty>::downcast(is, inst) {
                let result = result?;
                return Some(bind_result_expr(
                    result,
                    format!(
                        "({} {} {})",
                        $op,
                        value_to_egglog(func, *i.from()),
                        type_to_egglog(*i.ty())
                    ),
                    predeclared_values,
                ));
            }
        };
    }

    macro_rules! try_ternary {
        ($inst_ty:ty, $op:literal, $a:ident, $b:ident, $c:ident) => {
            if let Some(i) = <&$inst_ty>::downcast(is, inst) {
                let result = result?;
                return Some(bind_result_expr(
                    result,
                    format!(
                        "({} {} {} {})",
                        $op,
                        value_to_egglog(func, *i.$a()),
                        value_to_egglog(func, *i.$b()),
                        value_to_egglog(func, *i.$c())
                    ),
                    predeclared_values,
                ));
            }
        };
    }

    // Arithmetic
    try_binary!(Add, "Add");
    try_binary!(Sub, "Sub");
    try_binary!(Mul, "Mul");
    try_binary!(Udiv, "Udiv");
    try_binary!(Sdiv, "Sdiv");
    try_binary!(Umod, "Umod");
    try_binary!(Smod, "Smod");
    try_unary!(Neg, "Neg");

    // EVM-specific arithmetic (map to generic egraph nodes)
    try_binary!(EvmUdiv, "Udiv");
    try_binary!(EvmSdiv, "Sdiv");
    try_binary!(EvmUmod, "Umod");
    try_binary!(EvmSmod, "Smod");
    try_ternary!(EvmAddMod, "EvmAddMod", lhs, rhs, modulus);
    try_ternary!(EvmMulMod, "EvmMulMod", lhs, rhs, modulus);

    if let Some(i) = <&EvmExp>::downcast(is, inst) {
        let result = result?;
        return Some(bind_result_expr(
            result,
            format!(
                "(EvmExp {} {})",
                value_to_egglog(func, *i.base()),
                value_to_egglog(func, *i.exponent())
            ),
            predeclared_values,
        ));
    }

    if let Some(i) = <&EvmByte>::downcast(is, inst) {
        let result = result?;
        return Some(bind_result_expr(
            result,
            format!(
                "(EvmByte {} {})",
                value_to_egglog(func, *i.pos()),
                value_to_egglog(func, *i.value())
            ),
            predeclared_values,
        ));
    }

    if let Some(i) = <&EvmClz>::downcast(is, inst) {
        let result = result?;
        return Some(bind_result_expr(
            result,
            format!("(EvmClz {})", value_to_egglog(func, *i.word())),
            predeclared_values,
        ));
    }

    // Shifts have different field names (bits, value)
    if let Some(i) = <&Shl>::downcast(is, inst) {
        let result = result?;
        return Some(bind_result_expr(
            result,
            format!(
                "(Shl {} {})",
                value_to_egglog(func, *i.bits()),
                value_to_egglog(func, *i.value())
            ),
            predeclared_values,
        ));
    }
    if let Some(i) = <&Shr>::downcast(is, inst) {
        let result = result?;
        return Some(bind_result_expr(
            result,
            format!(
                "(Shr {} {})",
                value_to_egglog(func, *i.bits()),
                value_to_egglog(func, *i.value())
            ),
            predeclared_values,
        ));
    }
    if let Some(i) = <&Sar>::downcast(is, inst) {
        let result = result?;
        return Some(bind_result_expr(
            result,
            format!(
                "(Sar {} {})",
                value_to_egglog(func, *i.bits()),
                value_to_egglog(func, *i.value())
            ),
            predeclared_values,
        ));
    }

    // Logic
    try_binary!(And, "And");
    try_binary!(Or, "Or");
    try_binary!(Xor, "Xor");
    try_unary!(Not, "Not");

    // Comparisons
    try_binary!(Lt, "Lt");
    try_binary!(Gt, "Gt");
    try_binary!(Le, "Le");
    try_binary!(Ge, "Ge");
    try_binary!(Slt, "Slt");
    try_binary!(Sgt, "Sgt");
    try_binary!(Sle, "Sle");
    try_binary!(Sge, "Sge");
    try_binary!(Eq, "Eq");
    try_binary!(Ne, "Ne");

    if let Some(i) = <&IsZero>::downcast(is, inst) {
        let result = result?;
        return Some(bind_result_expr(
            result,
            format!("(IsZero {})", value_to_egglog(func, *i.lhs())),
            predeclared_values,
        ));
    }

    // Casts
    try_cast!(Sext, "Sext");
    try_cast!(Zext, "Zext");
    try_cast!(Trunc, "Trunc");
    try_cast!(Bitcast, "Bitcast");

    if let Some(phi) = <&Phi>::downcast(is, inst) {
        let result = result?;
        return Some(phi_to_egglog(func, result, phi, predeclared_values));
    }

    // Alloca - creates a unique stack allocation
    if <&Alloca>::downcast(is, inst).is_some() {
        let result = result?;
        let ty = func.dfg.value_ty(result);
        return Some(bind_result_expr(
            result,
            format!("(AllocaResult {} {})", result.as_u32(), type_to_egglog(ty)),
            predeclared_values,
        ));
    }

    // Gep - get element pointer (address computation)
    if let Some(gep) = <&Gep>::downcast(is, inst) {
        let result = result?;
        let values = gep.values();
        if !values.is_empty() {
            // Build nested GEP expression: GepBase -> GepOffset -> GepOffset -> ...
            let mut gep_expr = format!("(GepBase {})", value_to_egglog(func, values[0]));
            for (i, &idx) in values[1..].iter().enumerate() {
                gep_expr = format!(
                    "(GepOffset {} {} {})",
                    gep_expr,
                    value_to_egglog(func, idx),
                    i
                );
            }

            return Some(bind_result_expr(result, gep_expr, predeclared_values));
        }
    }

    let result = result?;
    if predeclared_values.contains(&result) {
        None
    } else {
        Some(side_effect_result_to_egglog(func, result))
    }
}

fn phi_to_egglog(
    func: &Function,
    result: ValueId,
    phi: &Phi,
    predeclared_values: &FxHashSet<ValueId>,
) -> String {
    let mut out = bind_result_expr(
        result,
        format!(
            "(PhiResult {} {})",
            result.as_u32(),
            type_to_egglog(func.dfg.value_ty(result))
        ),
        predeclared_values,
    );
    write!(
        &mut out,
        "\n(set (phi-num-preds {}) {})",
        result.as_u32(),
        phi.args().len()
    )
    .unwrap();

    for (idx, (incoming, _pred)) in phi.args().iter().enumerate() {
        write!(
            &mut out,
            "\n(set (phi-val {} {}) {})",
            result.as_u32(),
            idx,
            value_to_egglog(func, *incoming)
        )
        .unwrap();
    }

    out
}

fn side_effect_result_to_egglog(func: &Function, result: ValueId) -> String {
    format!(
        "(let {} (SideEffectResult {} {}))",
        value_name(result),
        result.as_u32(),
        type_to_egglog(func.dfg.value_ty(result))
    )
}

/// Convert instruction to egglog with memory state tracking.
/// Returns (egglog_string, new_memory_state_name) if instruction can be converted.
fn inst_to_egglog_with_mem(
    func: &Function,
    inst_id: InstId,
    current_mem: &str,
    mem_counter: &mut u32,
    predeclared_values: &FxHashSet<ValueId>,
) -> Option<(String, Option<String>)> {
    let inst = func.dfg.inst(inst_id);
    let is = func.inst_set();
    let result = func.dfg.inst_result(inst_id);

    // Mload - load from memory, creates a LoadResult with unique ID
    // Also sets the load-addr function for this load
    if let Some(load) = <&Mload>::downcast(is, inst) {
        let result = result?;
        let ty = func.dfg.value_ty(result);
        let addr = value_to_egglog(func, *load.addr());
        let load_id = result.as_u32();
        // Parse current_mem to get mem_id (e.g., "mem0" -> 0, "mem1" -> 1)
        let mem_id: u32 = current_mem
            .strip_prefix("mem")
            .and_then(|s| s.parse().ok())
            .unwrap_or(0);
        let egglog = format!(
            "{}\n(set (load-addr {}) {})",
            bind_result_expr(
                result,
                format!("(LoadResult {} {} {})", load_id, mem_id, type_to_egglog(ty)),
                predeclared_values,
            ),
            load_id,
            addr
        );
        return Some((egglog, None));
    }

    // Mstore - store to memory, creates new memory state
    // Sets store-prev, store-addr, store-val, store-ty functions
    if let Some(store) = <&Mstore>::downcast(is, inst) {
        *mem_counter += 1;
        let new_mem_id = *mem_counter;
        let new_mem = format!("mem{}", new_mem_id);
        let addr = value_to_egglog(func, *store.addr());
        let value = value_to_egglog(func, *store.value());
        let ty = func.dfg.value_ty(*store.value());
        // Parse current_mem to get prev_mem_id
        let prev_mem_id: u32 = current_mem
            .strip_prefix("mem")
            .and_then(|s| s.parse().ok())
            .unwrap_or(0);
        let egglog = format!(
            "(set (store-prev {}) {})\n(set (store-addr {}) {})\n(set (store-val {}) {})\n(set (store-ty {}) {})",
            new_mem_id,
            prev_mem_id,
            new_mem_id,
            addr,
            new_mem_id,
            value,
            new_mem_id,
            type_to_egglog(ty)
        );
        return Some((egglog, Some(new_mem)));
    }

    let new_mem = if inst_writes_memory(func, inst_id) {
        *mem_counter += 1;
        Some(format!("mem{}", *mem_counter))
    } else {
        None
    };

    // Fall back to non-memory instruction conversion.
    // Some write-barrier instructions (e.g. no-result calls) have no egglog term.
    if let Some(stmt) = inst_to_egglog(func, inst_id, predeclared_values) {
        return Some((stmt, new_mem));
    }

    new_mem.map(|mem| {
        (
            format!("; memory-barrier inst{}", inst_id.as_u32()),
            Some(mem),
        )
    })
}

fn inst_writes_memory(func: &Function, inst_id: InstId) -> bool {
    if let Some(call) = func.dfg.call_info(inst_id) {
        return func
            .ctx()
            .func_attrs(call.callee())
            .contains(FuncAttrs::MEM_WRITE);
    }

    matches!(func.dfg.inst(inst_id).side_effect(), SideEffect::Write)
}

fn bind_result_expr(
    result: ValueId,
    expr: String,
    predeclared_values: &FxHashSet<ValueId>,
) -> String {
    if predeclared_values.contains(&result) {
        format!("(union {} {})", value_name(result), expr)
    } else {
        format!("(let {} {})", value_name(result), expr)
    }
}

fn collect_forward_decl_values(func: &Function) -> FxHashSet<ValueId> {
    let mut values = FxHashSet::default();
    let is = func.inst_set();

    for block in func.layout.iter_block() {
        for inst_id in func.layout.iter_inst(block) {
            if let Some(phi) = <&Phi>::downcast(is, func.dfg.inst(inst_id)) {
                if let Some(result) = func.dfg.inst_result(inst_id) {
                    values.insert(result);
                }

                for (incoming, _pred) in phi.args() {
                    if matches!(func.dfg.value(*incoming), Value::Inst { .. }) {
                        values.insert(*incoming);
                    }
                }
            }
        }
    }

    values
}

fn value_name(v: ValueId) -> String {
    format!("v{}", v.as_u32())
}

fn value_to_egglog(func: &Function, v: ValueId) -> String {
    match func.dfg.value(v) {
        Value::Immediate { imm, ty } => {
            let mut bits = imm.as_i256().to_u256();
            let bit_width: usize = match ty {
                Type::I1 => 1,
                Type::I8 => 8,
                Type::I16 => 16,
                Type::I32 => 32,
                Type::I64 => 64,
                Type::I128 => 128,
                Type::I256 => 256,
                _ => unreachable!("immediates are always integers"),
            };
            if bit_width < 256 {
                let mask = (U256::one() << bit_width) - U256::one();
                bits &= mask;
            }
            format!("(Const {bits:#x} {})", type_to_egglog(*ty))
        }
        Value::Global { gv, ty } => {
            format!("(Global {} {})", gv.as_u32(), type_to_egglog(*ty))
        }
        Value::Undef { ty } => {
            format!("(Undef {})", type_to_egglog(*ty))
        }
        _ => value_name(v),
    }
}

fn type_to_egglog(ty: Type) -> String {
    match ty {
        Type::I1 => "(I1)".to_string(),
        Type::I8 => "(I8)".to_string(),
        Type::I16 => "(I16)".to_string(),
        Type::I32 => "(I32)".to_string(),
        Type::I64 => "(I64)".to_string(),
        Type::I128 => "(I128)".to_string(),
        Type::I256 => "(I256)".to_string(),
        Type::Unit => "(UnitTy)".to_string(),
        Type::Compound(ty) => format!("(CompoundRef {})", ty.as_u32()),
    }
}

#[cfg(test)]
mod tests {
    use smallvec::smallvec;
    use sonatina_ir::{
        InstSetBase, Linkage, Signature,
        builder::test_util::{test_func_builder, test_module_builder},
        inst::{
            arith::Add,
            control_flow::{Br, Call, Jump, Phi, Return},
            data::{Mload, Mstore},
        },
        isa::Isa,
    };

    use super::*;

    fn call_load_mem_id(attrs: FuncAttrs) -> u32 {
        let mb = test_module_builder();
        let callee_sig = Signature::new("callee", Linkage::Public, &[], Type::Unit);
        let callee = mb.declare_function(callee_sig).unwrap();
        mb.ctx.set_func_attrs(callee, attrs);

        let ptr_ty = mb.ptr_type(Type::I32);
        let (evm, mut builder) = test_func_builder(&mb, &[ptr_ty], Type::Unit);
        let is = evm.inst_set();
        let block = builder.append_block();
        builder.switch_to_block(block);

        let addr = builder.func.arg_values[0];
        let v10 = builder.make_imm_value(10i32);
        builder.insert_inst_no_result_with(|| Mstore::new(is, addr, v10, Type::I32));
        builder.insert_inst_no_result_with(|| {
            Call::new(
                is.has_call().expect("target ISA must support `call`"),
                callee,
                smallvec![],
            )
        });
        builder.insert_inst_with(|| Mload::new(is, addr, Type::I32), Type::I32);
        builder.insert_inst_no_result_with(|| Return::new(is, None));
        builder.seal_all();

        let program = func_to_egglog(&builder.func);
        let mem_ids: Vec<u32> = program
            .lines()
            .filter_map(|line| {
                let (_, rest) = line.split_once("(LoadResult ")?;
                let mut fields = rest.split_whitespace();
                let _load_id = fields.next()?;
                fields.next()?.parse().ok()
            })
            .collect();

        assert_eq!(mem_ids.len(), 1, "expected one load in:\n{program}");
        mem_ids[0]
    }

    #[test]
    fn test_basic() {
        assert_eq!(type_to_egglog(Type::I32), "(I32)");
    }

    #[test]
    fn test_mem_write_call_advances_memory() {
        let mem_id = call_load_mem_id(FuncAttrs::MEM_WRITE | FuncAttrs::WILLRETURN);
        assert_eq!(mem_id, 2);
    }

    #[test]
    fn test_pure_call_does_not_advance_memory() {
        let mem_id = call_load_mem_id(FuncAttrs::WILLRETURN);
        assert_eq!(mem_id, 1);
    }

    #[test]
    fn test_noreturn_mem_write_call_still_advances_memory() {
        let mem_id = call_load_mem_id(FuncAttrs::MEM_WRITE | FuncAttrs::NORETURN);
        assert_eq!(mem_id, 2);
    }

    #[test]
    fn test_forward_phi_is_fully_modeled() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[Type::I32, Type::I1], Type::I32);
        let is = evm.inst_set();

        let b0 = builder.append_block();
        let b1 = builder.append_block();
        let b2 = builder.append_block();
        let b3 = builder.append_block();

        let seed = builder.func.arg_values[0];
        let cond = builder.func.arg_values[1];

        builder.switch_to_block(b0);
        builder.insert_inst_no_result_with(|| Jump::new(is, b1));

        builder.switch_to_block(b1);
        let loop_phi = builder.insert_inst_with(|| Phi::new(is, vec![(seed, b0)]), Type::I32);
        builder.insert_inst_no_result_with(|| Br::new(is, cond, b2, b3));

        builder.switch_to_block(b2);
        let zero = builder.make_imm_value(0i32);
        let backedge = builder.insert_inst_with(|| Add::new(is, seed, zero), Type::I32);
        builder.insert_inst_no_result_with(|| Jump::new(is, b1));

        builder.switch_to_block(b3);
        builder.insert_inst_no_result_with(|| Return::new(is, Some(loop_phi)));
        builder.append_phi_arg(loop_phi, backedge, b2);
        builder.seal_all();

        let program = func_to_egglog(&builder.func);
        let phi_id = loop_phi.as_u32();
        let backedge_id = backedge.as_u32();
        assert!(program.contains(&format!("(union v{phi_id} (PhiResult {phi_id} (I32)))")));
        assert!(program.contains(&format!("(set (phi-num-preds {phi_id}) 2)")));
        assert!(program.contains(&format!("(set (phi-val {phi_id} 1) v{backedge_id})")));
    }
}
