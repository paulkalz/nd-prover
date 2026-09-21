use std::env;
use nd_prover::formatter;
use nd_prover::parser;
use nd_prover::solver::backward::BackwardSolver;
use nd_prover::solver::LogicSolver;
use nd_prover::checker::ProofChecker;

fn main() {
    // Collect command line arguments
    let args: Vec<String> = env::args().collect();
    
    // Use the first argument as input string, or fall back to the formula below
    let input_string = if args.len() > 1 {
        &args[1]
    } else {
        println!("No input provided. Running formula from main script.\n");
        "((H & W) -> D), (H & !D), (!D -> F), (F <-> (R v I)), !I |- R" // Input
    };
    
    println!("Starting Prover with: {}", input_string);
    
    let (premises, conclusion) = parser::parse(input_string);
    
    let solver = BackwardSolver;
    if let Some(proof) = solver.solve(&premises, &conclusion) {
        let formatted_proof = formatter::clean_proof(&proof);
        
        /*
        println!("Found proof:\n{}", proof);
        match ProofChecker::verify(&proof) {
            Ok(_) => println!("The proof is valid!"),
            Err(e) => println!("The proof is invalid! Reason: {}", e),
        }
        */

        println!("Formatted proof:\n{}", formatted_proof);
        match ProofChecker::verify(&formatted_proof) {
            Ok(_) => println!("The formatted proof is valid!"),
            Err(e) => println!("The formatted proof is invalid! Reason: {}", e),
        }

    } else {
        println!("No proof was found. The argument may be invalid. Otherwise try increasing MAX_ITERATIONS and MAX_NESTING_DEPTH.");
    }
}
