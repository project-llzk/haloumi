//! Types and traits for human-friendly printing of the IR.

use std::fmt::{Formatter, Write};

/// Prints a human-friendly representation of the IR meant for debugging.
///
/// The structure of the output emitted by the printer is never considered stable and shouldn't be
/// relied upon as it may change unexpectedly. The purpose of the printer is to be a debugging aid
/// for inspecting the shape of the IR and not a serialization/deserialization format.
#[derive(Copy, Clone)]
pub struct IRPrinter<'ir> {
    ir: &'ir dyn IRPrintable,
}

impl std::fmt::Display for IRPrinter<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut ctx = IRPrinterCtx::new(f);
        self.ir.fmt(&mut ctx)
    }
}

impl std::fmt::Debug for IRPrinter<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("IRPrinter").finish()
    }
}

impl<'ir, T: IRPrintable> From<&'ir T> for IRPrinter<'ir> {
    fn from(ir: &'ir T) -> Self {
        Self { ir }
    }
}

/// Alias type to a formatting result.
pub type Result = std::fmt::Result;

/// Trait defining the common behavior of printable IR objects.
pub trait IRPrintable {
    /// Format the IR object using the given context.
    fn fmt(&self, ctx: &mut IRPrinterCtx<'_, '_>) -> Result;

    /// Computes the depth of the IR tree to give hints to the printer.
    fn depth(&self) -> usize {
        1
    }
}

/// Printing context.
///
/// Implements [`std::fmt::Write`] and it's meant to be used as the first argument of [`write!`].
pub struct IRPrinterCtx<'a, 'f> {
    f: &'a mut Formatter<'f>,
    indent: Vec<usize>,
    indent_pending: bool,
}

impl<'a, 'f> IRPrinterCtx<'a, 'f> {
    fn new(f: &'a mut Formatter<'f>) -> Self {
        Self {
            f,
            indent: vec![],
            indent_pending: true,
        }
    }

    /// Adds a new line to the output.
    pub fn nl(&mut self) -> Result {
        if !self.indent_pending {
            self.indent_pending = true;
            writeln!(self.f)?;
        }
        Ok(())
    }

    fn push_indent(&mut self, value: usize) {
        self.indent.push(value);
    }

    fn pop_indent(&mut self) {
        self.indent.pop();
    }

    fn do_indent(&mut self) -> Result {
        if !self.indent_pending {
            return Ok(());
        }

        write!(self.f, "{}", " ".repeat(self.indent.iter().sum()))?;
        self.indent_pending = false;
        Ok(())
    }

    /// Adds a list to the output and then a new line.
    pub fn list_nl(
        &mut self,
        atom: &str,
        body: impl FnOnce(&mut IRPrinterCtx) -> Result,
    ) -> Result {
        self.list(atom, body)?;
        self.nl()
    }

    /// Adds a list to the output.
    pub fn list(&mut self, atom: &str, body: impl FnOnce(&mut IRPrinterCtx) -> Result) -> Result {
        write!(self, "(")?;
        if !atom.is_empty() {
            write!(self, "{atom} ")?;
        }
        body(self)?;
        write!(self, ")")
    }

    /// Adds a list to the output indenting the output inside it.
    pub fn block(&mut self, atom: &str, body: impl FnOnce(&mut IRPrinterCtx) -> Result) -> Result {
        self.list(atom, |ctx| {
            ctx.push_indent(2 + atom.len());
            body(ctx)?;
            ctx.pop_indent();
            Ok(())
        })
    }

    pub(crate) fn fmt_call<I: IRPrintable, O: IRPrintable>(
        &mut self,
        callee: &str,
        inputs: &[I],
        outputs: &[O],
        id: Option<usize>,
    ) -> Result {
        self.block("call", |ctx| {
            if let Some(id) = id {
                write!(ctx, "{id} ")?;
            }
            writeln!(ctx, "\"{}\" ", callee)?;
            ctx.block("inputs", |ctx| {
                let do_nl = inputs.iter().any(|expr| expr.depth() > 1);
                let mut is_first = true;
                for expr in inputs {
                    if do_nl && !is_first {
                        ctx.nl()?;
                    }
                    is_first = false;
                    expr.fmt(ctx)?;
                }
                Ok(())
            })?;
            ctx.nl()?;
            ctx.list("outputs", |ctx| {
                for output in outputs {
                    output.fmt(ctx)?;
                }
                Ok(())
            })
        })
    }
}

impl Write for IRPrinterCtx<'_, '_> {
    fn write_str(&mut self, s: &str) -> Result {
        let ends_with_nl = s.ends_with('\n');
        let mut lines = s.lines().peekable();
        loop {
            let Some(line) = lines.next() else {
                self.indent_pending = ends_with_nl;
                return Ok(());
            };
            let not_done = lines.peek().is_some();
            self.do_indent()?;

            write!(self.f, "{}", line)?;
            if not_done || ends_with_nl {
                writeln!(self.f)?;
            }
        }
    }
}

impl std::fmt::Debug for IRPrinterCtx<'_, '_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("IRPrinterCtx")
            .field("indent", &self.indent)
            .field("indent_pending", &self.indent_pending)
            .finish()
    }
}
