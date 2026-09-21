use nd_prover::formula::Formula;
use nd_prover::parser::parse;

#[test]
fn test_parse_atoms_and_negation() {
    let (premises, conclusion) = parse("P |- !Q");
    
    assert_eq!(premises.len(), 1);
    assert_eq!(premises[0], Formula::Atom("P".to_string()));
    
    let expected_conclusion = Formula::Not(Box::new(Formula::Atom("Q".to_string())));
    assert_eq!(conclusion, expected_conclusion);
}

#[test]
fn test_parse_binary_operations() {
    let valid_cases = vec!(
        ("(P & Q)", Formula::And(
            Box::new(Formula::Atom("P".to_string())), 
            Box::new(Formula::Atom("Q".to_string()))
        )),
        ("(P v Q)", Formula::Or(
            Box::new(Formula::Atom("P".to_string())), 
            Box::new(Formula::Atom("Q".to_string()))
        )),
        ("(P -> Q)", Formula::Implies(
            Box::new(Formula::Atom("P".to_string())), 
            Box::new(Formula::Atom("Q".to_string()))
        )),
        ("(P <-> Q)", Formula::Equivalent(
            Box::new(Formula::Atom("P".to_string())), 
            Box::new(Formula::Atom("Q".to_string()))
        )),
    );

    for (input_str, expected_formula) in valid_cases {
        let input = format!(" |- {}", input_str); // no premises
        let (_, conclusion) = parse(&input);
        assert_eq!(conclusion, expected_formula, "Error while parsing: {}", input_str);
    }
}

#[test]
fn test_parse_nested_formulas() {
    let input = "|- (P & (Q -> !R))";
    let (_, conclusion) = parse(input);

    let expected = Formula::And(
        Box::new(Formula::Atom("P".to_string())),
        Box::new(Formula::Implies(
            Box::new(Formula::Atom("Q".to_string())),
            Box::new(Formula::Not(Box::new(Formula::Atom("R".to_string()))))
        ))
    );
    assert_eq!(conclusion, expected);
}

#[test]
#[should_panic(expected = "Expected token RParen, instead found None")]
fn test_parse_missing_bracket_panics() {
    parse("|- (P & Q"); 
}

#[test]
fn test_complex_nested_expression() {
    let input = "|- ((P & Q) -> (R v !S))";
    let (_, conclusion) = parse(input);

    let expected = Formula::Implies(
        Box::new(Formula::And(Box::new(Formula::Atom("P".to_string())), Box::new(Formula::Atom("Q".to_string())))),
        Box::new(Formula::Or(
            Box::new(Formula::Atom("R".to_string())),
            Box::new(Formula::Not(Box::new(Formula::Atom("S".to_string()))))
        ))
    );
    assert_eq!(conclusion, expected);
}

#[test]
fn test_negation_of_complex_formula() {
    let input = " |- !((P v Q) <-> R)";
    let (_, conclusion) = parse(input);

    let expected = Formula::Not(Box::new(Formula::Equivalent(
        Box::new(Formula::Or(Box::new(Formula::Atom("P".to_string())), Box::new(Formula::Atom("Q".to_string())))),
        Box::new(Formula::Atom("R".to_string()))
    )));
    assert_eq!(conclusion, expected);
}

#[test]
fn test_complex_premises_and_conclusion() {
    let input = "(P -> Q), !(Q v R) |- (!P & !R)";
    let (premises, conclusion) = parse(input);

    assert_eq!(premises.len(), 2);
    
    assert_eq!(
        premises[0],
        Formula::Implies(Box::new(Formula::Atom("P".to_string())), Box::new(Formula::Atom("Q".to_string())))
    );
    
    assert_eq!(
        premises[1],
        Formula::Not(Box::new(Formula::Or(Box::new(Formula::Atom("Q".to_string())), Box::new(Formula::Atom("R".to_string())))))
    );

    let expected_conclusion = Formula::And(
        Box::new(Formula::Not(Box::new(Formula::Atom("P".to_string())))),
        Box::new(Formula::Not(Box::new(Formula::Atom("R".to_string()))))
    );
    assert_eq!(conclusion, expected_conclusion);
}

#[test]
fn test_chain_of_implications() {
    let input = "|- (A -> (B -> (C -> D)))";
    let (_, conclusion) = parse(input);

    let expected = Formula::Implies(
        Box::new(Formula::Atom("A".to_string())),
        Box::new(Formula::Implies(
            Box::new(Formula::Atom("B".to_string())),
            Box::new(Formula::Implies(Box::new(Formula::Atom("C".to_string())), Box::new(Formula::Atom("D".to_string()))))
        ))
    );
    assert_eq!(conclusion, expected);
}

#[test]
#[should_panic]
fn test_integration_malformed_deep_structure() {
    parse("((P & Q) -> (R !S)) |- T");
}