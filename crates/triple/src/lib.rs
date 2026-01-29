use std::fmt::{Display, Formatter};

use thiserror::Error;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TargetTriple {
    /// An architecture.
    pub architecture: Architecture,
    /// A vendor or chain.
    pub vendor: Vendor,
    /// An operating system or VM.
    pub operating_system: OperatingSystem,
}

impl TargetTriple {
    pub const fn new(
        architecture: Architecture,
        vendor: Vendor,
        operating_system: OperatingSystem,
    ) -> Self {
        Self {
            architecture,
            vendor,
            operating_system,
        }
    }
    pub fn parse(s: &str) -> Result<Self, InvalidTriple> {
        let mut triple = s.split('-');

        let arch = Architecture::parse(
            triple
                .next()
                .ok_or_else(|| InvalidTriple::InvalidFormat(s.to_string()))?,
        )?;
        let chain = Vendor::parse(
            triple
                .next()
                .ok_or_else(|| InvalidTriple::InvalidFormat(s.to_string()))?,
        )?;
        let version = OperatingSystem::parse(
            arch,
            chain,
            triple
                .next()
                .ok_or_else(|| InvalidTriple::InvalidFormat(s.to_string()))?,
        )?;

        if triple.next().is_none() {
            Ok(Self::new(arch, chain, version))
        } else {
            Err(InvalidTriple::InvalidFormat(s.to_string()))
        }
    }
}

impl Display for TargetTriple {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}-{}-{}",
            self.architecture, self.vendor, self.operating_system
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Architecture {
    Evm,
}

impl Architecture {
    fn parse(s: &str) -> Result<Self, InvalidTriple> {
        match s {
            "evm" => Ok(Self::Evm),
            _ => Err(InvalidTriple::ArchitectureNotSupported),
        }
    }
}

impl Display for Architecture {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Evm => write!(f, "evm"),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Vendor {
    Ethereum,
}

impl Vendor {
    fn parse(s: &str) -> Result<Self, InvalidTriple> {
        match s {
            "ethereum" => Ok(Vendor::Ethereum),
            _ => Err(InvalidTriple::VendorNotSupported),
        }
    }
}

impl Display for Vendor {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Vendor::Ethereum => write!(f, "ethereum"),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OperatingSystem {
    Evm(EvmVersion),
}

impl OperatingSystem {
    fn parse(arch: Architecture, chain: Vendor, s: &str) -> Result<Self, InvalidTriple> {
        match (arch, chain) {
            (Architecture::Evm, Vendor::Ethereum) => {
                let evm_version = match s {
                    "frontier" => EvmVersion::Frontier,
                    "homestead" => EvmVersion::Homestead,
                    "byzantium" => EvmVersion::Byzantium,
                    "constantinople" => EvmVersion::Constantinople,
                    "berlin" => EvmVersion::Berlin,
                    "istanbul" => EvmVersion::Istanbul,
                    "london" => EvmVersion::London,
                    "paris" => EvmVersion::Paris,
                    "shanghai" => EvmVersion::Shanghai,
                    "cancun" => EvmVersion::Cancun,
                    "osaka" => EvmVersion::Osaka,
                    _ => return Err(InvalidTriple::OsNotSupported),
                };
                Ok(Self::Evm(evm_version))
            }
        }
    }
}

impl Display for OperatingSystem {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Evm(evm_version) => write!(f, "{evm_version}"),
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
    Berlin,
    London,
    Paris,
    Shanghai,
    Cancun,
    Osaka,
}

#[derive(Debug, Clone, Error)]
pub enum InvalidTriple {
    #[error("the format of triple must be `architecture-chain-version: but got `{0}`")]
    InvalidFormat(String),

    #[error("given architecture is not supported")]
    ArchitectureNotSupported,

    #[error("given vendor is not supported")]
    VendorNotSupported,

    #[error("given operating system is not supported")]
    OsNotSupported,

    #[error("given triple consists of invalid combination")]
    InvalidCombination,
}

impl Display for EvmVersion {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Frontier => write!(f, "frontier"),
            Self::Homestead => write!(f, "homestead"),
            Self::Byzantium => write!(f, "byzantium"),
            Self::Constantinople => write!(f, "constantinople"),
            Self::Istanbul => write!(f, "istanbul"),
            Self::Berlin => write!(f, "berlin"),
            Self::London => write!(f, "london"),
            Self::Paris => write!(f, "paris"),
            Self::Shanghai => write!(f, "shanghai"),
            Self::Cancun => write!(f, "cancun"),
            Self::Osaka => write!(f, "osaka"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test() {
        for (target, want) in [
            ("evm-ethereum-istanbul", EvmVersion::Istanbul),
            ("evm-ethereum-shanghai", EvmVersion::Shanghai),
            ("evm-ethereum-cancun", EvmVersion::Cancun),
            ("evm-ethereum-osaka", EvmVersion::Osaka),
        ] {
            let triple = TargetTriple::parse(target).unwrap();
            assert_eq!(triple.architecture, Architecture::Evm);
            assert_eq!(triple.vendor, Vendor::Ethereum);
            assert_eq!(triple.operating_system, OperatingSystem::Evm(want));
            assert_eq!(target, triple.to_string());
        }
    }
}
