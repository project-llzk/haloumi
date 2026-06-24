#[derive(Debug)]
pub enum Note {
    NoNote,
    Note(String),
}

impl std::fmt::Display for Note {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Note::NoNote => Ok(()),
            Note::Note(note) => write!(f, ": {note}"),
        }
    }
}

impl From<String> for Note {
    fn from(value: String) -> Self {
        Self::Note(value)
    }
}

impl From<&str> for Note {
    fn from(value: &str) -> Self {
        value.to_owned().into()
    }
}
