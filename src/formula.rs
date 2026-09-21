use std::collections::BTreeSet;
use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Formula {
    Atom(String),
    Not(Box<Formula>),
    And(Box<Formula>, Box<Formula>),
    Or(Box<Formula>, Box<Formula>),
    Implies(Box<Formula>, Box<Formula>),
    Equivalent(Box<Formula>, Box<Formula>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Rule {
    Premise,
    Assumption,
    AndElimination(usize),
    AndIntroduction(usize, usize),
    ImpliesElimination(usize, usize),
    ImpliesIntroduction(usize, usize),
    OrElimination(usize, usize, usize),
    OrIntroduction(usize),
    NotElimination(usize),
    NotIntroduction(usize, usize),
    EquivalentElimination(usize),
    EquivalentIntroduction(usize, usize),
}

#[derive(Debug, Clone)]
pub struct ProofLine {
    pub premises_dependencies: BTreeSet<usize>, // BTreeSet sorts the dependencys
    pub line_number: usize,
    pub formula: Formula,
    pub rule: Rule,
}

#[derive(Debug, Clone)]
pub struct Proof {
    pub premises: Vec<Formula>,
    pub conclusion: Formula,
    pub lines: Vec<ProofLine>,
}







// Formatting of formulas
impl fmt::Display for Formula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Formula::Atom(name) => write!(f, "{}", name),
            Formula::Not(phi) => write!(f, "¬{}", phi),
            Formula::And(phi, psi) => write!(f, "({} & {})", phi, psi),
            Formula::Or(phi, psi) => write!(f, "({} v {})", phi, psi),
            Formula::Implies(phi, psi) => write!(f, "({} ➜ {})", phi, psi),
            Formula::Equivalent(phi, psi) => write!(f, "({} ↔ {})", phi, psi),
        }
    }
}

// Formatting of rules
impl fmt::Display for Rule {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Rule::Premise => write!(f, "A*"),
            Rule::Assumption => write!(f, "A"),
            Rule::AndElimination(j) => write!(f, "&-B:{}", j),
            Rule::AndIntroduction(j, k) => write!(f, "&-E:{},{}", j, k),
            Rule::ImpliesElimination(j, k) => write!(f, "➜-B:{},{}", j, k),
            Rule::ImpliesIntroduction(j, k) => write!(f, "➜-E:{},{}", j, k),
            Rule::OrElimination(j, k, l) => write!(f, "v-B:{},{},{}", j, k, l),
            Rule::OrIntroduction(j) => write!(f, "v-E:{}", j),
            Rule::NotElimination(j) => write!(f, "¬-B:{}", j),
            Rule::NotIntroduction(j, k) => write!(f, "¬-E:{},{}", j, k),
            Rule::EquivalentElimination(j) => write!(f, "↔-B:{}", j),
            Rule::EquivalentIntroduction(j, k) => write!(f, "↔-E:{},{}", j, k),
        }
    }
}

// Formatting of the proof
impl fmt::Display for Proof {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let prem_strs: Vec<String> = self.premises.iter().map(|p| p.to_string()).collect();
        writeln!(f, "{} ⊦ {}", prem_strs.join(", "), self.conclusion)?;
        writeln!(f, "--------------------------------------------------")?;

        for line in &self.lines {
            let deps: Vec<String> = line.premises_dependencies.iter().map(|d| d.to_string()).collect();
            let deps_str = deps.join(",");

            writeln!(
                f, "{:<8} ({:<2}) {:<25} {}",
                deps_str,
                line.line_number,
                line.formula.to_string(),
                line.rule
            )?;
        }
        Ok(())
    }
}