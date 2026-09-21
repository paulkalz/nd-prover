use crate::formula::{Formula, Proof};
use crate::solver::LogicSolver;

pub struct BruteForceSolver;

impl LogicSolver for BruteForceSolver {
    fn solve(&self, _premises: &[Formula], _conclusion: &Formula) -> Option<Proof> {
        // currently not implemented
        None
    }
}