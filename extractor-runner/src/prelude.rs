#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, clap::ValueEnum)]
pub enum Preludes {
    Spread,
    Automaton,
}

const SPREAD_PRELUDE: &str = include_str!("spread.picus.inc");
const AUTOMATON_PRELUDE: &str = include_str!("automaton.picus.inc");

impl std::fmt::Display for Preludes {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Preludes::Spread => {
                writeln!(f, "{SPREAD_PRELUDE}")
            }
            Preludes::Automaton => {
                writeln!(f, "{AUTOMATON_PRELUDE}")
            }
        }
    }
}
