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
    pub const SP1: Self = Self::new(
        Architecture::Riscv64im,
        Vendor::Succinct,
        OperatingSystem::ZkvmElf,
    );

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
        let mut triple = s.splitn(3, '-');

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

        Ok(Self::new(arch, chain, version))
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
    X86_64,
    Aarch64,
    Riscv64im,
}

impl Architecture {
    fn parse(s: &str) -> Result<Self, InvalidTriple> {
        match s {
            "evm" => Ok(Self::Evm),
            "x86_64" => Ok(Self::X86_64),
            "aarch64" => Ok(Self::Aarch64),
            "riscv64im" => Ok(Self::Riscv64im),
            _ => Err(InvalidTriple::ArchitectureNotSupported),
        }
    }
}

impl Display for Architecture {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Evm => write!(f, "evm"),
            Self::X86_64 => write!(f, "x86_64"),
            Self::Aarch64 => write!(f, "aarch64"),
            Self::Riscv64im => write!(f, "riscv64im"),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Vendor {
    Ethereum,
    Unknown,
    Succinct,
}

impl Vendor {
    fn parse(s: &str) -> Result<Self, InvalidTriple> {
        match s {
            "ethereum" => Ok(Vendor::Ethereum),
            "unknown" => Ok(Vendor::Unknown),
            "succinct" => Ok(Vendor::Succinct),
            _ => Err(InvalidTriple::VendorNotSupported),
        }
    }
}

impl Display for Vendor {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Vendor::Ethereum => write!(f, "ethereum"),
            Vendor::Unknown => write!(f, "unknown"),
            Vendor::Succinct => write!(f, "succinct"),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OperatingSystem {
    Evm(EvmVersion),
    Native,
    ZkvmElf,
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
            (Architecture::X86_64 | Architecture::Aarch64, Vendor::Unknown) => match s {
                "native" => Ok(Self::Native),
                _ => Err(InvalidTriple::OsNotSupported),
            },
            (Architecture::Riscv64im, Vendor::Succinct) => match s {
                "zkvm-elf" => Ok(Self::ZkvmElf),
                _ => Err(InvalidTriple::OsNotSupported),
            },
            _ => Err(InvalidTriple::InvalidCombination),
        }
    }
}

impl Display for OperatingSystem {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Evm(evm_version) => write!(f, "{evm_version}"),
            Self::Native => write!(f, "native"),
            Self::ZkvmElf => write!(f, "zkvm-elf"),
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
    #[error("expected an architecture-vendor-system target, but got `{0}`")]
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

    #[test]
    fn native_triples_round_trip() {
        for (target, architecture) in [
            ("x86_64-unknown-native", Architecture::X86_64),
            ("aarch64-unknown-native", Architecture::Aarch64),
        ] {
            let triple = TargetTriple::parse(target).unwrap();
            assert_eq!(triple.architecture, architecture);
            assert_eq!(triple.vendor, Vendor::Unknown);
            assert_eq!(triple.operating_system, OperatingSystem::Native);
            assert_eq!(target, triple.to_string());
        }
    }

    #[test]
    fn invalid_native_combinations_are_rejected() {
        for target in [
            "evm-unknown-native",
            "x86_64-ethereum-osaka",
            "aarch64-unknown-osaka",
        ] {
            assert!(TargetTriple::parse(target).is_err(), "accepted {target}");
        }
    }

    #[test]
    fn sp1_triple_round_trips_and_rejects_other_riscv_targets() {
        let target = "riscv64im-succinct-zkvm-elf";
        assert_eq!(TargetTriple::parse(target).unwrap(), TargetTriple::SP1);
        assert_eq!(TargetTriple::SP1.to_string(), target);
        for target in [
            "riscv32im-succinct-zkvm-elf",
            "riscv64gc-succinct-zkvm-elf",
            "riscv64im-unknown-native",
            "riscv64im-unknown-none-elf",
            "riscv64im-succinct-zkvm",
            "riscv64im-succinct-zkvm-elf-extra",
            "x86_64-succinct-zkvm-elf",
            "evm-ethereum-osaka-extra",
        ] {
            assert!(TargetTriple::parse(target).is_err(), "accepted {target}");
        }
    }
}
