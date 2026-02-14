#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VerificationLevel {
    Fast,
    Standard,
    Full,
}

#[derive(Debug, Clone)]
pub struct VerifierConfig {
    pub level: VerificationLevel,
    pub max_diagnostics: usize,
    pub allow_unreachable_blocks: bool,
    pub allow_detached_entities: bool,
    pub check_users: bool,
    pub check_value_caches: bool,
    pub check_dominance: bool,
    pub deep_sanity: bool,
}

impl VerifierConfig {
    pub fn for_level(level: VerificationLevel) -> Self {
        match level {
            VerificationLevel::Fast => Self {
                level,
                max_diagnostics: 200,
                allow_unreachable_blocks: true,
                allow_detached_entities: true,
                check_users: false,
                check_value_caches: false,
                check_dominance: false,
                deep_sanity: false,
            },
            VerificationLevel::Standard => Self {
                level,
                max_diagnostics: 200,
                allow_unreachable_blocks: true,
                allow_detached_entities: false,
                check_users: false,
                check_value_caches: false,
                check_dominance: false,
                deep_sanity: false,
            },
            VerificationLevel::Full => Self {
                level,
                max_diagnostics: 500,
                allow_unreachable_blocks: true,
                allow_detached_entities: false,
                check_users: true,
                check_value_caches: true,
                check_dominance: true,
                deep_sanity: true,
            },
        }
    }

    pub fn should_check_types(&self) -> bool {
        !matches!(self.level, VerificationLevel::Fast)
    }

    pub fn should_check_dominance(&self) -> bool {
        self.check_dominance || matches!(self.level, VerificationLevel::Full)
    }

    pub fn should_check_users(&self) -> bool {
        self.check_users || matches!(self.level, VerificationLevel::Full)
    }

    pub fn should_check_value_caches(&self) -> bool {
        self.check_value_caches || matches!(self.level, VerificationLevel::Full)
    }

    pub fn should_run_deep_sanity(&self) -> bool {
        self.deep_sanity || matches!(self.level, VerificationLevel::Full)
    }
}

impl Default for VerifierConfig {
    fn default() -> Self {
        Self::for_level(VerificationLevel::Standard)
    }
}
