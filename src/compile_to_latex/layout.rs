use super::helper::{display, escape_text, inline};
use super::language::{phrase, Phrase};
use crate::launch_command::OutputLanguage;

/// Declarations use block typography; a proof keeps its nested prose inline.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum Flow {
    Block,
    Inline,
}

impl Flow {
    pub fn paragraph(self, text: &str) -> String {
        match self {
            Self::Block => format!("\\par\\noindent {text}\\par\n"),
            Self::Inline => format!("{text} "),
        }
    }

    pub fn heading(self, key: Phrase, title: &str, lang: OutputLanguage) -> String {
        let label = format!(
            "{}{}{}.",
            phrase(lang, key),
            if title.is_empty() { "" } else { " " },
            escape_text(title)
        );
        match self {
            Self::Block => {
                format!("\\par\\medskip\\noindent\\textbf{{{label}}}\\par\\nopagebreak[4]\n")
            }
            Self::Inline => format!("\\textbf{{{label}}} "),
        }
    }

    pub fn quote(self, text: &str) -> String {
        match self {
            Self::Block => format!("\\begin{{quote}}\n{text}\\end{{quote}}\n"),
            Self::Inline => text.into(),
        }
    }

    pub fn math(self, text: &str) -> String {
        match self {
            Self::Block => display(text),
            Self::Inline => format!("{} ", inline(text)),
        }
    }

    pub fn begin_items(self) -> &'static str {
        if self == Self::Block {
            "\\begin{description}\n"
        } else {
            ""
        }
    }

    pub fn end_items(self) -> &'static str {
        if self == Self::Block {
            "\\end{description}\n"
        } else {
            ""
        }
    }

    pub fn item(self, label: &str, body: &str) -> String {
        match self {
            Self::Block => format!("\\item[{label}] {body}\n"),
            Self::Inline => format!("{label} {body} "),
        }
    }
}
