use hex::FromHex as _;
use sonatina_ir::U256;

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct EvmConfig {
    pub stack_reach: Option<u8>,
    pub emit_debug_trace: Option<bool>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct EvmCase {
    pub name: String,
    pub calldata: Vec<u8>,
    pub expect: EvmExpect,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum EvmExpect {
    Return(Vec<u8>),
    Revert(Vec<u8>),
}

fn parse_evm_config(module_comments: &[String]) -> Result<EvmConfig, String> {
    let mut cfg = EvmConfig::default();

    for raw in module_comments {
        let Some(line) = raw.strip_prefix("#!") else {
            continue;
        };
        let line = line.trim();
        if line.is_empty() {
            continue;
        }

        let Some(spec) = line.strip_prefix("evm.config:") else {
            continue;
        };
        parse_evm_config_object(spec.trim(), &mut cfg)?;
    }

    Ok(cfg)
}

pub(crate) fn stack_reach_depth(module_comments: &[String]) -> Result<u8, String> {
    Ok(parse_evm_config(module_comments)?.stack_reach.unwrap_or(16))
}

pub(crate) fn emit_debug_trace(module_comments: &[String]) -> Result<bool, String> {
    Ok(parse_evm_config(module_comments)?
        .emit_debug_trace
        .unwrap_or(false))
}

pub(crate) fn parse_evm_cases(module_comments: &[String]) -> Result<Vec<EvmCase>, String> {
    let mut cases: Vec<EvmCaseBuilder> = Vec::new();
    let mut current: Option<EvmCaseBuilder> = None;

    for raw in module_comments {
        let Some(line) = raw.strip_prefix("#!") else {
            continue;
        };
        let line = line.trim();
        if line.is_empty() {
            continue;
        }

        if let Some(name) = line.strip_prefix("evm.case:") {
            if let Some(c) = current.take() {
                cases.push(c);
            }

            let name = name.trim();
            if name.is_empty() {
                return Err("evm.case: missing case name".to_string());
            }
            current = Some(EvmCaseBuilder::new(name));
            continue;
        }

        let Some(cur) = current.as_mut() else {
            continue;
        };

        if let Some(spec) = line.strip_prefix("calldata:") {
            cur.calldata = Some(parse_bytespec(spec.trim()).map_err(|e| format!("calldata: {e}"))?);
            continue;
        }

        if let Some(spec) = line.strip_prefix("expect:") {
            cur.expect = Some(parse_expect(spec.trim()).map_err(|e| format!("expect: {e}"))?);
            continue;
        }

        return Err(format!(
            "unknown evm directive `{line}` (expected `calldata:` or `expect:`)",
        ));
    }

    if let Some(c) = current.take() {
        cases.push(c);
    }

    cases
        .into_iter()
        .map(EvmCaseBuilder::finish)
        .collect::<Result<Vec<_>, _>>()
}

struct EvmCaseBuilder {
    name: String,
    calldata: Option<Vec<u8>>,
    expect: Option<EvmExpect>,
}

impl EvmCaseBuilder {
    fn new(name: &str) -> Self {
        Self {
            name: name.to_string(),
            calldata: None,
            expect: None,
        }
    }

    fn finish(self) -> Result<EvmCase, String> {
        let Some(calldata) = self.calldata else {
            return Err(format!("evm.case `{}` missing `calldata:`", self.name));
        };
        let Some(expect) = self.expect else {
            return Err(format!("evm.case `{}` missing `expect:`", self.name));
        };

        Ok(EvmCase {
            name: self.name,
            calldata,
            expect,
        })
    }
}

fn parse_expect(spec: &str) -> Result<EvmExpect, String> {
    if let Some(rest) = spec.strip_prefix("return") {
        return Ok(EvmExpect::Return(parse_bytespec(rest.trim())?));
    }
    if let Some(rest) = spec.strip_prefix("revert") {
        return Ok(EvmExpect::Revert(parse_bytespec(rest.trim())?));
    }

    Err(format!("unsupported expect kind: `{spec}`"))
}

fn parse_evm_config_object(spec: &str, cfg: &mut EvmConfig) -> Result<(), String> {
    let spec = spec.trim();
    let Some(spec) = spec.strip_prefix('{') else {
        return Err("expected `{ ... }`".to_string());
    };
    let Some(spec) = spec.strip_suffix('}') else {
        return Err("expected `{ ... }`".to_string());
    };

    for part in spec.split(',') {
        let part = part.trim();
        if part.is_empty() {
            continue;
        }

        let Some((key, value)) = part.split_once(':') else {
            return Err(format!("expected `key: value`, got `{part}`"));
        };
        let key = key.trim();
        let value = value.trim();

        match key {
            "stack_reach" => {
                if cfg.stack_reach.is_some() {
                    return Err("duplicate `stack_reach`".to_string());
                }
                cfg.stack_reach = Some(parse_u8_literal(value).map_err(|e| format!("{key}: {e}"))?);
            }
            "emit_debug_trace" => {
                if cfg.emit_debug_trace.is_some() {
                    return Err("duplicate `emit_debug_trace`".to_string());
                }
                cfg.emit_debug_trace =
                    Some(parse_bool_literal(value).map_err(|e| format!("{key}: {e}"))?);
            }
            _ => {
                // Ignore unknown keys for forward compatibility.
            }
        }
    }

    Ok(())
}

fn parse_bytespec(spec: &str) -> Result<Vec<u8>, String> {
    let spec = spec.trim();
    if spec.is_empty() {
        return Ok(vec![]);
    }

    let mut out: Vec<u8> = Vec::new();
    for token in spec.split_whitespace() {
        if let Some(hex) = token.strip_prefix("0x") {
            out.extend(
                Vec::<u8>::from_hex(hex).map_err(|e| format!("invalid hex `{token}`: {e}"))?,
            );
            continue;
        }

        if let Some(body) = token.strip_prefix("bytes(")
            && let Some(body) = body.strip_suffix(')')
        {
            let hex = body.strip_prefix("0x").unwrap_or(body);
            out.extend(
                Vec::<u8>::from_hex(hex)
                    .map_err(|e| format!("invalid bytes(...) token `{token}`: {e}"))?,
            );
            continue;
        }

        if let Some(body) = token.strip_prefix("u32be(")
            && let Some(body) = body.strip_suffix(')')
        {
            let n = parse_u32_literal(body).map_err(|e| format!("invalid u32be `{token}`: {e}"))?;
            out.extend_from_slice(&n.to_be_bytes());
            continue;
        }

        if let Some(body) = token.strip_prefix("u256(")
            && let Some(body) = body.strip_suffix(')')
        {
            let bytes =
                parse_u256_be_32(body).map_err(|e| format!("invalid u256 `{token}`: {e}"))?;
            out.extend_from_slice(&bytes);
            continue;
        }

        return Err(format!("unsupported calldata token `{token}`"));
    }

    Ok(out)
}

fn parse_u32_literal(lit: &str) -> Result<u32, String> {
    let lit = lit.trim();
    if let Some(hex) = lit.strip_prefix("0x") {
        return u32::from_str_radix(hex, 16).map_err(|e| format!("{e}"));
    }

    lit.parse::<u32>().map_err(|e| format!("{e}"))
}

fn parse_u8_literal(lit: &str) -> Result<u8, String> {
    let n = parse_u32_literal(lit)?;
    u8::try_from(n).map_err(|_| "literal is out of range for u8".to_string())
}

fn parse_bool_literal(lit: &str) -> Result<bool, String> {
    match lit.trim() {
        "true" => Ok(true),
        "false" => Ok(false),
        _ => Err("expected `true` or `false`".to_string()),
    }
}

fn parse_u256_be_32(lit: &str) -> Result<[u8; 32], String> {
    let lit = lit.trim();

    let v = if let Some(hex) = lit.strip_prefix("0x") {
        let bytes = Vec::<u8>::from_hex(hex).map_err(|e| format!("{e}"))?;
        if bytes.len() > 32 {
            return Err("hex literal is longer than 32 bytes".to_string());
        }
        let mut be = [0u8; 32];
        be[32 - bytes.len()..].copy_from_slice(&bytes);
        return Ok(be);
    } else {
        U256::from_dec_str(lit).map_err(|e| format!("{e}"))?
    };

    let bytes = v.to_big_endian();
    let bytes: &[u8] = bytes.as_ref();
    if bytes.len() > 32 {
        return Err("decimal literal is longer than 32 bytes".to_string());
    }

    let mut be = [0u8; 32];
    be[32 - bytes.len()..].copy_from_slice(bytes);
    Ok(be)
}
