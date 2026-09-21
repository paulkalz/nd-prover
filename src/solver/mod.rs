pub mod brute_force;
pub mod backward;

use crate::formula::{Formula, Proof};

// Common interface for all solving algorithms
pub trait LogicSolver {
    fn solve(&self, premises: &[Formula], conclusion: &Formula) -> Option<Proof>;
}