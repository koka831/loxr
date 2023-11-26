use std::io;

use miette::{LabeledSpan, MietteDiagnostic};

use crate::error::LoxError;
use crate::span::Span;

pub trait Report {
    fn report(&self, source: &str) -> miette::Report;
}

pub struct DiagnosticReporter<'a, W: io::Write> {
    writer: &'a mut W,
}

impl<'a, W: io::Write> DiagnosticReporter<'a, W> {
    pub fn new(writer: &'a mut W) -> Self {
        miette::set_hook(Box::new(|_| {
            Box::new(miette::MietteHandlerOpts::new().unicode(false).build())
        }))
        .unwrap_or_else(|e| panic!("failed to setup miette: {e}"));

        DiagnosticReporter { writer }
    }

    pub fn report(&mut self, e: &LoxError, source: &str) {
        let report = e.report(source);
        write!(self.writer, "{report:?}").unwrap();
        self.writer.flush().unwrap();
    }
}

impl Report for LoxError {
    fn report(&self, source: &str) -> miette::Report {
        match self {
            LoxError::LexError { e, span } => {
                let mut diag = MietteDiagnostic::new(e.to_string());
                diag = diag.with_label(LabeledSpan::new_with_span(Some(self.to_string()), *span));
                miette::Report::new(diag).with_source_code(source.to_string())
            }
            LoxError::UnexpectedToken { expect, actual } => {
                let mut diag = MietteDiagnostic::new(self.to_string());
                diag = diag.with_label(LabeledSpan::new_with_span(
                    Some(format!("expect {expect}")),
                    actual.span,
                ));
                miette::Report::new(diag).with_source_code(source.to_string())
            }
            LoxError::SyntaxError { message, span } => {
                let mut diag = MietteDiagnostic::new(message);
                diag = diag.with_label(LabeledSpan::new_with_span(Some(self.to_string()), *span));
                miette::Report::new(diag).with_source_code(source.to_string())
            }
            _ => {
                let diag = MietteDiagnostic::new(self.to_string());
                miette::Report::new(diag).with_source_code(source.to_string())
            }
        }
    }
}

impl From<Span> for miette::SourceSpan {
    fn from(span: Span) -> Self {
        miette::SourceSpan::new(span.base.into(), span.len.into())
    }
}
