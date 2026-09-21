use nd_prover::parser;
use nd_prover::solver::backward::BackwardSolver;
use nd_prover::solver::LogicSolver;
use nd_prover::formatter;
use nd_prover::checker::ProofChecker;


#[cfg(test)]
mod tests {
use super::*;

    // this helper function automates parsing, proving, formatting and checking
    fn assert_prover_and_checker(input: &str) {
        let (premises, conclusion) = parser::parse(input);
        let solver = BackwardSolver;
        
        let proof = solver.solve(&premises, &conclusion)
            .expect(&format!("No prove could be found for: {}", input));
            
        let clean_proof = formatter::clean_proof(&proof);
        
        /*
        println!("\n==========================================");
        println!("Found proof for: {}", input);
        println!("{}", proof);
        println!("--formatted:----------------------------------------");
        println!("{}", clean_proof);
        println!("==========================================\n");
        */
            
        let verification = ProofChecker::verify(&clean_proof);
        assert!(
            verification.is_ok(),
            "The prover generated a proof, but the checker rejected! Error: {:?}", 
            verification.unwrap_err()
        );
    }

    #[test]
    fn test_identity_success() {
        assert_prover_and_checker("A |- (A -> A)");
    }

    #[test]
    fn test_chain_success() {
        assert_prover_and_checker("(P -> Q), (Q <-> R), (R -> P) |- (R <-> P)");
    }

    #[test]
    fn test_excluded_middle_problem() {
        assert_prover_and_checker("|- (P v !P)");
    }

    #[test]
    fn test_sheet5_2b() {
        assert_prover_and_checker("(P v Q), !P |- Q");
    }

    #[test]
    fn test_sheet5_2c() {
        assert_prover_and_checker("(P -> Q), (P v !Q) |- (P <-> Q)");
    }

    #[test]
    fn test_zusatz_1a() {
        assert_prover_and_checker("|- (P -> (P v Q))");
    }

    #[test]
    fn test_zusatz_1b() {
        assert_prover_and_checker("|- ((P & (!P v Q)) -> Q)");
    }

    #[test]
    fn test_zusatz_2a() {
        assert_prover_and_checker("|- (((P v Q) & (!Q v !R)) -> (R -> P))");
    }

    #[test]
    fn test_zusatz_2b() {
        assert_prover_and_checker("|- (P <-> (!P -> P))");
    }

    #[test]
    fn test_zusatz_2c() {
        assert_prover_and_checker("|- ((P & !P) -> P)");
    }

    #[test]
    fn test_zusatz_3b() {
        assert_prover_and_checker("|- (((P v Q) & R) -> (P v (Q & R)))");
    }

    #[test]
    fn test_ex_falso_quodlibet_problem() {
        assert_prover_and_checker("P |- (!P -> Q)");
    }

    #[test]
    fn test_contraposition_problem() {
        assert_prover_and_checker("(P -> Q) |- (!Q -> !P)");
    }

    #[test]
    fn test_modus_tollens_variant_problem() {
        assert_prover_and_checker("!!Q, (P -> !Q) |- !P");
    }

    #[test]
    fn test_panic_in_try_elimination() {
        assert_prover_and_checker("(Q <-> R), (Q v P), (P -> R) |- R");
    }

    #[test]
    fn test_constructive_dilemma_variant_problem() {
        assert_prover_and_checker("(Q -> R), (Q v P) |- (P v R)");
    }

    // Testcases for every rule
    #[test]
    fn test_rule_conjunction_introduction() {
        assert_prover_and_checker("P, Q |- (P & Q)");
    }

    #[test]
    fn test_rule_conjunction_elimination() {
        assert_prover_and_checker("(P & Q) |- P");
    }

    #[test]
    fn test_rule_disjunction_introduction() {
        assert_prover_and_checker("P |- (P v Q)");
    }

    #[test]
    fn test_rule_disjunction_elimination() {
        assert_prover_and_checker("(P v Q), (P -> R), (Q -> R) |- R");
    }

    #[test]
    fn test_rule_implication_introduction() {
        assert_prover_and_checker("P |- (Q -> P)");
    }

    #[test]
    fn test_rule_implication_elimination() {
        assert_prover_and_checker("P, (P -> Q) |- Q");
    }

    #[test]
    fn test_rule_negation_introduction() {
        assert_prover_and_checker("(P -> Q), (P -> !Q) |- !P");
    }

    #[test]
    fn test_rule_negation_elimination() {
        assert_prover_and_checker("!!P |- P");
    }

    #[test]
    fn test_rule_bi_implication_introduction() {
        assert_prover_and_checker("(P -> Q), (Q -> P) |- (P <-> Q)");
    }

    #[test]
    fn test_rule_bi_implication_elimination() {
        assert_prover_and_checker("(P <-> Q), P |- Q");
    }

    #[test]
    fn test_rule_proof_by_contradiction() {
        assert_prover_and_checker("(!P -> Q), (!P -> !Q) |- P");
    }
}