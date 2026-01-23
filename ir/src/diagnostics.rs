//! Types and traits related to diagnostics.

use std::fmt;

/// In-progress validation
#[derive(Debug, Default)]
pub struct Validation<D> {
    errors: Vec<D>,
    warnings: Vec<D>,
}

impl<D> Validation<D> {
    /// Creates a new validation.
    pub fn new() -> Self {
        Self {
            errors: vec![],
            warnings: vec![],
        }
    }

    /// Appends a warning.
    pub fn with_warning(&mut self, warning: D) {
        self.warnings.push(warning)
    }

    /// Appends an error.
    pub fn with_error(&mut self, error: D) {
        self.errors.push(error)
    }

    /// Appends a list of warnings.
    pub fn with_warnings(&mut self, warnings: impl IntoIterator<Item = D>) {
        self.warnings.extend(warnings)
    }

    /// Appends a list of errors.
    pub fn with_errors(&mut self, errors: impl IntoIterator<Item = D>) {
        self.errors.extend(errors)
    }

    /// Appends a list of diagnostics.
    pub fn append(&mut self, diags: impl IntoIterator<Item = D>)
    where
        D: Diagnostic,
    {
        let (errors, warnings): (Vec<_>, Vec<_>) = diags.into_iter().partition(D::is_error);
        self.with_warnings(warnings);
        self.with_errors(errors);
    }

    /// Appends a list of diagnostics from a result.
    pub fn append_from_result<C>(&mut self, result: Result<Vec<D>, Vec<D>>, context: &C)
    where
        D: Diagnostic,
        C: std::fmt::Display + ?Sized,
    {
        match result {
            Ok(warnings) => self.append(warnings.into_iter().map(|w| w.contextualize(context))),
            Err(errors) => self.append(errors.into_iter().map(|e| e.contextualize(context))),
        }
    }
}

impl<D> From<Validation<D>> for Result<Vec<D>, Vec<D>> {
    fn from(mut value: Validation<D>) -> Self {
        if value.errors.is_empty() {
            Ok(value.warnings)
        } else {
            value.errors.extend(value.warnings);
            Err(value.errors)
        }
    }
}

/// Diagnostic kinds
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum DiagnosticKind {
    /// Warnings
    Warning,
    /// Errors
    Error,
    /// Others
    Other,
}

/// Marker trait for a diagnostic.
pub trait Diagnostic: fmt::Display {
    /// Gets the kind of diagnostic.
    fn kind(&self) -> DiagnosticKind;

    /// Returns true if it's an error diagnostic.
    fn is_error(&self) -> bool {
        self.kind() == DiagnosticKind::Error
    }

    /// Adds additional context to the diagnostic.
    fn contextualize<C>(self, context: &C) -> Self
    where
        C: ToString + ?Sized,
        Self: Sized;
}

/// Simple diagnostics implementation.
#[derive(Debug, Clone)]
pub struct SimpleDiagnostic {
    kind: DiagnosticKind,
    message: String,
}

impl SimpleDiagnostic {
    /// Creates a warning diagnostic.
    pub fn warn(message: impl ToString) -> Self {
        Self {
            kind: DiagnosticKind::Warning,
            message: message.to_string(),
        }
    }

    /// Creates an error diagnostic.
    pub fn error(message: impl ToString) -> Self {
        Self {
            kind: DiagnosticKind::Error,
            message: message.to_string(),
        }
    }

    /// Creates a diagnostic of another  kind.
    pub fn other(message: impl ToString) -> Self {
        Self {
            kind: DiagnosticKind::Other,
            message: message.to_string(),
        }
    }
}

impl Diagnostic for SimpleDiagnostic {
    fn kind(&self) -> DiagnosticKind {
        self.kind
    }

    fn contextualize<C>(self, context: &C) -> Self
    where
        C: ToString + ?Sized,
    {
        let mut final_message = context.to_string();
        if final_message.is_empty() {
            return self;
        }
        final_message.reserve(2 + self.message.len());
        final_message.push_str(": ");
        final_message.push_str(&self.message);
        Self {
            kind: self.kind,
            message: final_message,
        }
    }
}

impl fmt::Display for SimpleDiagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}: {}",
            match self.kind {
                DiagnosticKind::Warning => "warning",
                DiagnosticKind::Error => "error",
                DiagnosticKind::Other => "other",
            },
            self.message
        )
    }
}

/// Error type for a collection of diagnostics
pub struct DiagnosticsError {
    diags: Vec<Box<dyn Diagnostic>>,
}

impl std::fmt::Debug for DiagnosticsError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("DiagnosticsError")
            .field("n_diags", &self.diags.len())
            .finish()
    }
}

impl std::fmt::Display for DiagnosticsError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.diags
            .iter()
            .map(AsRef::as_ref)
            .try_for_each(|diag| writeln!(f, "- {diag}\n"))
    }
}

impl<D: Diagnostic + 'static> FromIterator<D> for DiagnosticsError {
    fn from_iter<T: IntoIterator<Item = D>>(iter: T) -> Self {
        Self {
            diags: iter
                .into_iter()
                .map(|d| -> Box<dyn Diagnostic> { Box::new(d) })
                .collect(),
        }
    }
}

impl<I: IntoIterator> From<I> for DiagnosticsError
where
    I::Item: Diagnostic + 'static,
{
    fn from(value: I) -> Self {
        Self::from_iter(value)
    }
}
