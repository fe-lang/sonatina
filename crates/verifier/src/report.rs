use std::fmt;

use crate::diagnostic::Diagnostic;

#[derive(Debug, Clone, Default)]
pub struct VerificationReport {
    pub diagnostics: Vec<Diagnostic>,
}

impl VerificationReport {
    pub fn is_ok(&self) -> bool {
        !self.has_errors()
    }

    pub fn has_errors(&self) -> bool {
        self.diagnostics.iter().any(Diagnostic::is_error)
    }

    pub fn errors(&self) -> impl Iterator<Item = &Diagnostic> {
        self.diagnostics.iter().filter(|diag| diag.is_error())
    }

    pub fn warnings(&self) -> impl Iterator<Item = &Diagnostic> {
        self.diagnostics.iter().filter(|diag| !diag.is_error())
    }

    pub(crate) fn push(&mut self, diagnostic: Diagnostic, max_diagnostics: usize) {
        if max_diagnostics == 0 || self.diagnostics.len() < max_diagnostics {
            self.diagnostics.push(diagnostic);
        }
    }

    pub(crate) fn extend_with_limit(&mut self, mut other: Vec<Diagnostic>, max_diagnostics: usize) {
        if max_diagnostics == 0 {
            self.diagnostics.extend(other);
            return;
        }

        let remaining = max_diagnostics.saturating_sub(self.diagnostics.len());
        if remaining == 0 {
            return;
        }

        if other.len() > remaining {
            other.truncate(remaining);
        }
        self.diagnostics.extend(other);
    }
}

impl fmt::Display for VerificationReport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.diagnostics.is_empty() {
            return "verification succeeded".fmt(f);
        }

        for (index, diagnostic) in self.diagnostics.iter().enumerate() {
            if index > 0 {
                writeln!(f)?;
            }
            write!(f, "{diagnostic}")?;
        }

        Ok(())
    }
}
