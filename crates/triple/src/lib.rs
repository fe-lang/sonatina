use thiserror::Error;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TargetTriple {
    pub architecture: Architecture,
    pub chain: Chain,
    pub version: Version,
}

impl TargetTriple {
    pub fn new(architecture: Architecture, chain: Chain, version: Version) -> Self {
        Self {
            architecture,
            chain,
            version,
        }
    }
    pub fn parse<'a>(s: &'a str) -> Result<Self, InvalidTriple<'a>> {
        let mut triple = s.split('-');

        let arch = Architecture::parse(
            triple
                .next()
                .ok_or_else(|| InvalidTriple::InvalidFormat(s))?,
        )?;
        let chain = Chain::parse(
            triple
                .next()
                .ok_or_else(|| InvalidTriple::InvalidFormat(s))?,
        )?;
        let version = Version::parse(
            arch,
            chain,
            triple
                .next()
                .ok_or_else(|| InvalidTriple::InvalidFormat(s))?,
        )?;

        if triple.next().is_none() {
            Ok(Self::new(arch, chain, version))
        } else {
            Err(InvalidTriple::InvalidFormat(s))
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Architecture {
    Evm,
}

impl Architecture {
    fn parse<'a>(s: &'a str) -> Result<Self, InvalidTriple<'a>> {
        match s {
            "evm" => Ok(Self::Evm),
            _ => Err(InvalidTriple::ArchitectureNotSupported),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Chain {
    Ethereum,
}

impl Chain {
    fn parse<'a>(s: &'a str) -> Result<Self, InvalidTriple<'a>> {
        match s {
            "ethereum" => Ok(Chain::Ethereum),
            _ => Err(InvalidTriple::ChainNotSupported),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Version {
    EvmVersion(EvmVersion),
}

impl Version {
    fn parse<'a>(arch: Architecture, chain: Chain, s: &'a str) -> Result<Self, InvalidTriple<'a>> {
        match (arch, chain) {
            (Architecture::Evm, Chain::Ethereum) => {
                let evm_version = match s {
                    "frontier" => EvmVersion::Frontier,
                    "homestead" => EvmVersion::Homestead,
                    "byzantium" => EvmVersion::Byzantium,
                    "constantinople" => EvmVersion::Constantinople,
                    "istanbul" => EvmVersion::Istanbul,
                    "london" => EvmVersion::London,
                    _ => return Err(InvalidTriple::VersionNotSupported),
                };
                Ok(Self::EvmVersion(evm_version))
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EvmVersion {
    Frontier,
    Homestead,
    Byzantium,
    Constantinople,
    Istanbul,
    London,
}
#[derive(Debug, Clone, Copy, Error)]
pub enum InvalidTriple<'a> {
    #[error("the format of triple must be `architecture-chain-version: but got `{0}`")]
    InvalidFormat(&'a str),

    #[error("given architecture is not supported")]
    ArchitectureNotSupported,

    #[error("given chain is not supported")]
    ChainNotSupported,

    #[error("given version is not supported")]
    VersionNotSupported,

    #[error("given triple consists of invalid combination")]
    InvalidCombination,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test() {
        let target = "evm-ethereum-istanbul";
        let triple = TargetTriple::parse(target).unwrap();

        assert_eq!(triple.architecture, Architecture::Evm);
        assert_eq!(triple.chain, Chain::Ethereum);
        assert_eq!(triple.version, Version::EvmVersion(EvmVersion::Istanbul));
    }
}
