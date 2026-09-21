use nd_prover::formula::Formula;
use nd_prover::formula::Proof;
use nd_prover::formula::ProofLine;
use nd_prover::checker::ProofChecker;
use std::collections::BTreeSet;
use nd_prover::formula::Rule;



#[cfg(test)]
mod tests {
use super::*;

    // Helper function
    fn atom(name: &str) -> Formula {
        Formula::Atom(name.to_string())
    }

    #[test]
    fn test_verify_implies_introduction_success() { // proves A -> A
        
        let proof = Proof {
            premises: vec![atom("A")],
            conclusion: Formula::Implies(Box::new(atom("A")), Box::new(atom("A"))),
            lines: vec![
                ProofLine {
                    line_number: 1,
                    formula: atom("A"),
                    rule: Rule::Assumption,
                    premises_dependencies: BTreeSet::from([1]),
                },
                ProofLine {
                    line_number: 2,
                    formula: Formula::Implies(Box::new(atom("A")), Box::new(atom("A"))),
                    rule: Rule::ImpliesIntroduction(1, 1),
                    premises_dependencies: BTreeSet::new(),
                },
            ],
        };

        let result = ProofChecker::verify(&proof);
        
        assert!(result.is_ok(), "The valid proof for A -> A was wrongfully rejected: {:?}", result);
    }

    #[test]
    fn test_verify_implies_introduction_fails_missing_dependency() { // invalid proof for A -> B
        
        let proof = Proof {
            premises: vec![atom("A"), atom("B")],
            conclusion: Formula::Implies(Box::new(atom("A")), Box::new(atom("B"))),
            lines: vec![
                ProofLine {
                    line_number: 1,
                    formula: atom("A"),
                    rule: Rule::Assumption,
                    premises_dependencies: BTreeSet::from([1]),
                },
                ProofLine {
                    line_number: 2,
                    formula: atom("B"),
                    rule: Rule::Assumption,
                    premises_dependencies: BTreeSet::from([2]),
                },
                ProofLine {
                    line_number: 3,
                    formula: Formula::Implies(Box::new(atom("A")), Box::new(atom("B"))),
                    rule: Rule::ImpliesIntroduction(1, 2),
                    premises_dependencies: BTreeSet::from([2]),
                },
            ]
        };

        let result = ProofChecker::verify(&proof);
        
        assert!(result.is_err(), "The invalid proof for A -> B was wrongfully accepted.");
    }

    #[test]
    fn test_verify_and_elimination_and_introduction_success() { // (A & B) |- (B & A)
        
        let proof = Proof {
            premises: vec![Formula::And(Box::new(atom("A")), Box::new(atom("B")))],
            conclusion: Formula::And(Box::new(atom("B")), Box::new(atom("A"))),
            lines: vec![
                ProofLine {
                    line_number: 1,
                    formula: Formula::And(Box::new(atom("A")), Box::new(atom("B"))),
                    rule: Rule::Premise,
                    premises_dependencies: BTreeSet::from([1]),
                },
                ProofLine {
                    line_number: 2,
                    formula: atom("A"),
                    rule: Rule::AndElimination(1),
                    premises_dependencies: BTreeSet::from([1]),
                },
                ProofLine {
                    line_number: 3,
                    formula: atom("B"),
                    rule: Rule::AndElimination(1),
                    premises_dependencies: BTreeSet::from([1]),
                },
                ProofLine {
                    line_number: 4,
                    formula: Formula::And(Box::new(atom("B")), Box::new(atom("A"))),
                    rule: Rule::AndIntroduction(3, 2),
                    premises_dependencies: BTreeSet::from([1]),
                },
            ],
        };

        assert!(ProofChecker::verify(&proof).is_ok());
    }

    #[test]
    fn test_verify_not_elimination_success() { // !!A |- A
        
        let double_not = Formula::Not(Box::new(Formula::Not(Box::new(atom("A")))));
        let proof = Proof {
            premises: vec![double_not.clone()],
            conclusion: atom("A"),
            lines: vec![
                ProofLine {
                    line_number: 1,
                    formula: double_not,
                    rule: Rule::Premise,
                    premises_dependencies: BTreeSet::from([1]),
                },
                ProofLine {
                    line_number: 2,
                    formula: atom("A"),
                    rule: Rule::NotElimination(1),
                    premises_dependencies: BTreeSet::from([1]),
                },
            ],
        };

        assert!(ProofChecker::verify(&proof).is_ok());
    }

    #[test]
    fn test_verify_equivalent_elimination_success() { // (A <-> B) |- (A -> B)
        
        let proof = Proof {
            premises: vec![Formula::Equivalent(Box::new(atom("A")), Box::new(atom("B")))],
            conclusion: Formula::Implies(Box::new(atom("A")), Box::new(atom("B"))),
            lines: vec![
                ProofLine {
                    line_number: 1,
                    formula: Formula::Equivalent(Box::new(atom("A")), Box::new(atom("B"))),
                    rule: Rule::Premise,
                    premises_dependencies: BTreeSet::from([1]),
                },
                ProofLine {
                    line_number: 2,
                    formula: Formula::Implies(Box::new(atom("A")), Box::new(atom("B"))),
                    rule: Rule::EquivalentElimination(1),
                    premises_dependencies: BTreeSet::from([1]),
                },
            ],
        };

        assert!(ProofChecker::verify(&proof).is_ok());
    }

    #[test]
    fn test_verify_komplex_proof_success() { // |- (P v !P)
        
        let proof = Proof {
            premises: vec![],
            conclusion: Formula::Or(Box::new(atom("P")), Box::new(Formula::Not(Box::new(atom("P"))))),
            lines: vec![
                ProofLine {
                    line_number: 1,
                    formula: Formula::Not(Box::new(Formula::Or(Box::new(atom("P")), Box::new(Formula::Not(Box::new(atom("P"))))))),
                    rule: Rule::Assumption,
                    premises_dependencies: BTreeSet::from([1]),
                },
                ProofLine {
                    line_number: 2,
                    formula: atom("P"),
                    rule: Rule::Assumption,
                    premises_dependencies: BTreeSet::from([2]),
                },
                ProofLine {
                    line_number: 3,
                    formula: Formula::Or(Box::new(atom("P")), Box::new(Formula::Not(Box::new(atom("P"))))),
                    rule: Rule::OrIntroduction(2),
                    premises_dependencies: BTreeSet::from([2]),
                },
                ProofLine {
                    line_number: 4,
                    formula: Formula::And(Box::new(Formula::Not(Box::new(Formula::Or(Box::new(atom("P")), Box::new(Formula::Not(Box::new(atom("P")))))))), Box::new(Formula::Or(Box::new(atom("P")), Box::new(Formula::Not(Box::new(atom("P"))))))),
                    rule: Rule::AndIntroduction(1, 3),
                    premises_dependencies: BTreeSet::from([1, 2]),
                },
                ProofLine {
                    line_number: 5,
                    formula: Formula::Not(Box::new(atom("P"))),
                    rule: Rule::NotIntroduction(2, 4),
                    premises_dependencies: BTreeSet::from([1]),
                },
                ProofLine {
                    line_number: 6,
                    formula: Formula::Not(Box::new(atom("P"))),
                    rule: Rule::Assumption,
                    premises_dependencies: BTreeSet::from([6]),
                },
                ProofLine {
                    line_number: 7,
                    formula: Formula::Or(Box::new(atom("P")), Box::new(Formula::Not(Box::new(atom("P"))))),
                    rule: Rule::OrIntroduction(6),
                    premises_dependencies: BTreeSet::from([6]),
                },
                ProofLine {
                    line_number: 8,
                    formula: Formula::And(Box::new(Formula::Not(Box::new(Formula::Or(Box::new(atom("P")), Box::new(Formula::Not(Box::new(atom("P")))))))), Box::new(Formula::Or(Box::new(atom("P")), Box::new(Formula::Not(Box::new(atom("P"))))))),
                    rule: Rule::AndIntroduction(1, 7),
                    premises_dependencies: BTreeSet::from([1, 6]),
                },
                ProofLine {
                    line_number: 9,
                    formula: Formula::Not(Box::new(Formula::Not(Box::new(atom("P"))))),
                    rule: Rule::NotIntroduction(6, 8),
                    premises_dependencies: BTreeSet::from([1]),
                },
                ProofLine {
                    line_number: 10,
                    formula: Formula::And(Box::new(Formula::Not(Box::new(atom("P")))), Box::new(Formula::Not(Box::new(Formula::Not(Box::new(atom("P"))))))),
                    rule: Rule::AndIntroduction(5, 9),
                    premises_dependencies: BTreeSet::from([1]),
                },
                ProofLine {
                    line_number: 11,
                    formula: Formula::Not(Box::new(Formula::Not(Box::new(Formula::Or(Box::new(atom("P")), Box::new(Formula::Not(Box::new(atom("P"))))))))),
                    rule: Rule::NotIntroduction(1, 10),
                    premises_dependencies: BTreeSet::from([]),
                },
                ProofLine {
                    line_number: 12,
                    formula: Formula::Or(Box::new(atom("P")), Box::new(Formula::Not(Box::new(atom("P"))))),
                    rule: Rule::NotElimination(11),
                    premises_dependencies: BTreeSet::from([]),
                },
            ],
        };

        assert!(ProofChecker::verify(&proof).is_ok());
    }

    #[test]
    fn test_verify_fails_wrong_final_conclusion() { // conclusion-line is missing
        let proof = Proof {
            premises: vec![atom("A")],
            conclusion: atom("B"),
            lines: vec![
                ProofLine {
                    line_number: 1,
                    formula: atom("A"),
                    rule: Rule::Assumption,
                    premises_dependencies: BTreeSet::from([1]),
                },
            ],
        };

        assert!(ProofChecker::verify(&proof).is_err());
    }

    #[test]
    fn test_verify_fails_line_number_mismatch() { // The lines are not numbered consecutively in ascending order
        let proof = Proof {
            premises: vec![atom("A")],
            conclusion: atom("A"),
            lines: vec![
                ProofLine {
                    line_number: 1,
                    formula: atom("A"),
                    rule: Rule::Assumption,
                    premises_dependencies: BTreeSet::from([1]),
                },
                ProofLine {
                    line_number: 3,
                    formula: atom("A"),
                    rule: Rule::Assumption,
                    premises_dependencies: BTreeSet::from([3]),
                },
            ],
        };

        assert!(ProofChecker::verify(&proof).is_err());
    }
}