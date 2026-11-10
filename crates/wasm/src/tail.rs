//! Tail calls in the encoded module.
//!
//! WAFFLE has no `return_call`. The translator ends a tail call's block with
//! a return of the call's results, which WAFFLE encodes as the call, moves of
//! the results through locals, and `return`. This pass makes that sequence a
//! `return_call` in the functions the translator names.

use rustc_hash::{FxHashMap, FxHashSet};
use waffle::wasmparser::{BinaryReader, BinaryReaderError, FunctionBody, Operator, Result};

use super::WasmError;

/// The functions that make tail calls, with the callees of those calls, by
/// their indices in the module. A callee returns the types its caller does.
pub(super) type TailCallSites = FxHashMap<u32, FxHashSet<u32>>;

const CODE_SECTION: u8 = 10;
const RETURN_CALL: u8 = 0x12;

fn malformed(error: BinaryReaderError) -> WasmError {
    WasmError::Emission(format!("the encoded module cannot be read back: {error}"))
}

fn write_u32(out: &mut Vec<u8>, mut value: u32) {
    while value >= 0x80 {
        out.push(value as u8 | 0x80);
        value >>= 7;
    }
    out.push(value as u8);
}

/// `bytes` with the tail calls of `sites` as `return_call`s. `imported` is
/// the number of imported functions, which take the first indices.
pub(super) fn rewrite(
    bytes: Vec<u8>,
    imported: u32,
    sites: &TailCallSites,
) -> std::result::Result<Vec<u8>, WasmError> {
    if sites.is_empty() {
        return Ok(bytes);
    }
    // The header, then sections: an id, a size and that many bytes.
    let mut out = bytes[..8].to_vec();
    let mut reader = BinaryReader::new(&bytes[8..], 8);
    while !reader.eof() {
        let start = reader.original_position();
        let id = reader.read_u8().map_err(malformed)?;
        let size = reader.read_var_u32().map_err(malformed)? as usize;
        let mut section = reader
            .skip(|reader| reader.read_bytes(size).map(drop))
            .map_err(malformed)?;
        if id != CODE_SECTION {
            out.extend_from_slice(&bytes[start..reader.original_position()]);
            continue;
        }
        let count = section.read_var_u32().map_err(malformed)?;
        let mut code = Vec::with_capacity(size);
        write_u32(&mut code, count);
        for index in imported..imported + count {
            let size = section.read_var_u32().map_err(malformed)? as usize;
            let body = section.read_bytes(size).map_err(malformed)?;
            let rewritten = match sites.get(&index) {
                Some(callees) => rewrite_body(body, callees).map_err(malformed)?,
                None => body.to_vec(),
            };
            write_u32(&mut code, rewritten.len() as u32);
            code.extend_from_slice(&rewritten);
        }
        out.push(CODE_SECTION);
        write_u32(&mut out, code.len() as u32);
        out.extend_from_slice(&code);
    }
    Ok(out)
}

/// The body of a function with each call of one of `callees` that the body
/// returns the results of at once as a `return_call`. Between such a call
/// and its `return`, or the end of the body, WAFFLE pops results into locals
/// and pushes the same locals back.
fn rewrite_body(body: &[u8], callees: &FxHashSet<u32>) -> Result<Vec<u8>> {
    let mut reader = FunctionBody::new(BinaryReader::new(body, 0)).get_operators_reader()?;
    let mut operators = Vec::new();
    while !reader.eof() {
        operators.push(reader.read_with_offset()?);
    }
    let mut out = Vec::with_capacity(body.len());
    let mut copied = 0;
    let mut index = 0;
    while let Some((operator, start)) = operators.get(index) {
        index += 1;
        let &Operator::Call { function_index } = operator else {
            continue;
        };
        if !callees.contains(&function_index) {
            continue;
        }
        let mut next = index;
        let mut locals = Vec::new();
        while let Some((Operator::LocalSet { local_index }, _)) = operators.get(next) {
            locals.push(*local_index);
            next += 1;
        }
        let pushed_back = locals.iter().rev().enumerate().all(|(offset, local)| {
            matches!(operators.get(next + offset),
                Some((Operator::LocalGet { local_index }, _)) if local_index == local)
        });
        next += locals.len();
        // The end of the body returns what is on the stack; keep it.
        let end = match operators.get(next) {
            Some((Operator::Return, _)) => operators.get(next + 1).map(|&(_, offset)| offset),
            Some(&(Operator::End, offset)) if next + 1 == operators.len() => Some(offset),
            _ => None,
        };
        if let Some(end) = end.filter(|_| pushed_back) {
            out.extend_from_slice(&body[copied..*start]);
            out.push(RETURN_CALL);
            write_u32(&mut out, function_index);
            copied = end;
            index = next;
        }
    }
    out.extend_from_slice(&body[copied..]);
    Ok(out)
}
