use crate::formula::{Formula, Proof, ProofLine, Rule};
use std::collections::BTreeSet;

pub struct ProofChecker;

impl ProofChecker {
    pub fn verify(proof: &Proof) -> Result<(), String> {
        let lines = &proof.lines;

        // Proof is not empty
        if lines.is_empty() { return Err("Proof contains no lines.".to_string()); }

        // Conclusion is in the last line
        let last_line = lines.last().unwrap();
        if last_line.formula != proof.conclusion {
            return Err(format!("Conclusion mismatch. Expected: {}, found: {}", proof.conclusion, last_line.formula));
        }

        // Collect line numbers of all premises
        let valid_source_deps: BTreeSet<usize> = lines
            .iter()
            .filter(|line| matches!(line.rule, Rule::Premise) && proof.premises.contains(&line.formula))
            .map(|line| line.line_number)
            .collect();

        // Conclusion can only depend on premises
        if !last_line.premises_dependencies.is_subset(&valid_source_deps) {
            return Err("The conclusion does not depend solely on premises.".to_string());
        }

        // Collect line numbers of all assumptions (including premises)
        let assumption_lines: BTreeSet<usize> = lines 
            .iter()
            .filter(|line| (matches!(line.rule, Rule::Assumption) || matches!(line.rule, Rule::Premise)))
            .map(|line| line.line_number)
            .collect();

        for (i, line) in proof.lines.iter().enumerate() {
            // Line numbers must be in ascending order
            if line.line_number != i + 1 {
                return Err(format!("Line {} has a false number.", line.line_number));
            }

            // Every line can only depend on assumptions
            if !line.premises_dependencies.is_subset(&assumption_lines) {
                return Err(format!("Line {} does not depend solely on assumptions.", line.line_number));
            }
        }

        // Check every line for correct application of derivation rules (in reverse order)
        for line in lines.iter().rev() {
            Self::check_line_validity(line, lines)?;
        }

        Ok(())
    }

    fn check_line_validity(line: &ProofLine, all_lines: &[ProofLine]) -> Result<(), String> {
        match &line.rule {
            Rule::Premise => { // premises and assumptions can always be introduced
                Ok(())
            }
            Rule::Assumption => {
                Ok(())
            }
            Rule::AndElimination(parent_idx) => { // AndElimination requires a conjunction that includes the derived formula
                let parent = get_line(all_lines, *parent_idx)?;
                if let Formula::And(phi, psi) = &parent.formula {
                    if line.formula == **phi || line.formula == **psi {
                        check_deps(&line.premises_dependencies, &parent.premises_dependencies)?;
                        Ok(())
                    } else { Err("AndElimination: Formula is not included.".into()) }
                } else { Err("AndElimination requires a conjunction".into()) }
            }
            Rule::ImpliesElimination(idx_a, idx_b) => { // ImpliesElimination requires an implication with the correct antecedent
                let line_a = get_line(all_lines, *idx_a)?;
                let line_b = get_line(all_lines, *idx_b)?;

                // Match for correct combination of implication and antecedent.
                match (&line_a.formula, &line_b.formula) {
                    (Formula::Implies(p, q), phi) if **p == *phi && **q == line.formula => {
                        let mut expected = line_a.premises_dependencies.clone();
                        expected.extend(&line_b.premises_dependencies);
                        check_deps(&line.premises_dependencies, &expected)?;
                        Ok(())
                    }
                    (phi, Formula::Implies(p, q)) if **p == *phi && **q == line.formula => {
                        let mut expected = line_b.premises_dependencies.clone();
                        expected.extend(&line_a.premises_dependencies);
                        check_deps(&line.premises_dependencies, &expected)?;
                        Ok(())
                    }
                    _ => Err("ImpliesElimination: Found no valid combination of implication and antecedent.".into())
                }
            }
            Rule::OrElimination(idx_a, idx_b, idx_c) => { // OrElimination requires a disjunction and two implications
                let line_a = get_line(all_lines, *idx_a)?;
                let line_b = get_line(all_lines, *idx_b)?;
                let line_c = get_line(all_lines, *idx_c)?;

                // Match for correct combination of disjunction and implications
                match (&line_a.formula, &line_b.formula, &line_c.formula) {
                    // line_a is the disjunction, b and c are implications
                    (Formula::Or(p, q), Formula::Implies(p1, r1), Formula::Implies(p2, r2))
                        if ((**p1 == **p && **p2 == **q) || (**p1 == **q && **p2 == **p))
                            && **r1 == line.formula && **r2 == line.formula => 
                    {
                        let mut expected = line_a.premises_dependencies.clone();
                        expected.extend(&line_b.premises_dependencies);
                        expected.extend(&line_c.premises_dependencies);
                        check_deps(&line.premises_dependencies, &expected)?;
                        Ok(())
                    }

                    // line_b is the disjunction, a and c are implications
                    (Formula::Implies(p1, r1), Formula::Or(p, q), Formula::Implies(p2, r2))
                        if ((**p1 == **p && **p2 == **q) || (**p1 == **q && **p2 == **p))
                            && **r1 == line.formula && **r2 == line.formula => 
                    {
                        let mut expected = line_a.premises_dependencies.clone();
                        expected.extend(&line_b.premises_dependencies);
                        expected.extend(&line_c.premises_dependencies);
                        check_deps(&line.premises_dependencies, &expected)?;
                        Ok(())
                    }

                    // line_c is the disjunction, a and b are the implications
                    (Formula::Implies(p1, r1), Formula::Implies(p2, r2), Formula::Or(p, q))
                        if ((**p1 == **p && **p2 == **q) || (**p1 == **q && **p2 == **p))
                            && **r1 == line.formula && **r2 == line.formula => 
                    {
                        let mut expected = line_a.premises_dependencies.clone();
                        expected.extend(&line_b.premises_dependencies);
                        expected.extend(&line_c.premises_dependencies);
                        check_deps(&line.premises_dependencies, &expected)?;
                        Ok(())
                    }

                    _ => Err("OrElimination: Found no valid combination of disjunction and implications.".into())
                }
            }
            Rule::NotElimination(parent_idx) => { // NotElimination requires a double negated formula
                let parent = get_line(all_lines, *parent_idx)?;
                match &parent.formula {
                    Formula::Not(inner) => match inner.as_ref() {
                        Formula::Not(phi) if line.formula == **phi => {
                            check_deps(&line.premises_dependencies, &parent.premises_dependencies)?;
                            Ok(())
                        }
                        Formula::Not(_) => Err("NotElimination: The inner formula does not match the resulting formula.".into()),
                        _ => Err("NotElimination can only be applied to a double negation.".into()),
                    },
                    _ => Err("NotElimination can only be applied to a negation.".into()),
                }
            }
            Rule::EquivalentElimination(parent_idx) => { // EquivalentElimination requires an eqivalent
                let parent = get_line(all_lines, *parent_idx)?;
                if let Formula::Equivalent(phi, psi) = &parent.formula {
                    if let Formula::Implies(p, q) = &line.formula {
                        if (**p == **phi && **q == **psi) || (**p == **psi && **q == **phi) { // checks if (phi -> psi) or (psi -> phi)
                            check_deps(&line.premises_dependencies, &parent.premises_dependencies)?;
                            return Ok(());
                        }
                    }
                    Err("EquivalentElimination: resulting formula is not correct.".into())
                } else { 
                    Err("EquivalentElimination can only be applied to an equivalent.".into()) 
                }
            }
            Rule::AndIntroduction(phi_idx, psi_idx) => { // AndIntroduction requires both parts of the resulting conjunction
                let phi = get_line(all_lines, *phi_idx)?;
                let psi = get_line(all_lines, *psi_idx)?;

                if let Formula::And(p, q) = &line.formula {
                    if (**p == phi.formula && **q == psi.formula)
                    || (**q == phi.formula && **p == psi.formula) {
                        let mut expected = phi.premises_dependencies.clone();
                        expected.extend(&psi.premises_dependencies);
                        check_deps(&line.premises_dependencies, &expected)?;
                        return Ok(());
                    }
                    Err("AndIntroduction: resulting formula is not correct.".into())
                } else {
                    Err("AndIntroduction does not result in a conjunction.".into())
                }
            }
            Rule::ImpliesIntroduction(idx_a, idx_b) => { // ImpliesIntroduction requires an assumption and a formula depending on this assumption
                if let Formula::Implies(phi, psi) = &line.formula {
                    let line_a = get_line(all_lines, *idx_a)?;
                    let line_b = get_line(all_lines, *idx_b)?;

                    // identify assumption (Phi) and derived formula (Psi)
                    let (assump_idx, conc_line) = if line_a.formula == **phi 
                        && (matches!(line_a.rule, Rule::Assumption) || matches!(line_a.rule, Rule::Premise))
                        && line_b.formula == **psi 
                    {
                        (*idx_a, line_b)
                    } else if line_b.formula == **phi 
                        && (matches!(line_b.rule, Rule::Assumption) || matches!(line_a.rule, Rule::Premise))
                        && line_a.formula == **psi 
                    {
                        (*idx_b, line_a)
                    } else {
                        return Err("ImpliesIntroduction: referenced lines do not match required assumption and derived line.".into());
                    };

                    // derived formula (Psi) has to depend on assumption (Phi)
                    if !conc_line.premises_dependencies.contains(&assump_idx) {
                        return Err(format!(
                            "ImpliesIntroduction Fehler: Line {} does not depend on assumption in line {}.",
                            conc_line.line_number, assump_idx
                        ));
                    }

                    // Check dependencys (resulting line needs dependencys of psi - line of phi)
                    let mut expected_deps = conc_line.premises_dependencies.clone();
                    expected_deps.remove(&assump_idx);
                    check_deps(&line.premises_dependencies, &expected_deps)?;
                    Ok(())
                } else {
                    Err("ImpliesIntroduction does not result in an implication.".into())
                }
            }
            Rule::OrIntroduction(parent_idx) => { // OrIntroduction requires a formula
                let parent = get_line(all_lines, *parent_idx)?;
                
                if let Formula::Or(phi, psi) = &line.formula {
                    if parent.formula == **phi || parent.formula == **psi {
                        check_deps(&line.premises_dependencies, &parent.premises_dependencies)?;
                        Ok(())
                    } else {
                        Err("OrIntroduction: No side of the disjunction was found.".into())
                    }
                } else {
                    Err("OrIntroduction does not result in a disjunction.".into())
                }
            }
            Rule::NotIntroduction(idx_a, idx_b) => { // NotIntroduction requires an assumption and a contradiction that depends on the assumption
                if let Formula::Not(phi) = &line.formula {
                    let line_a = get_line(all_lines, *idx_a)?;
                    let line_b = get_line(all_lines, *idx_b)?;

                    // match assumption and contradiction
                    let (assump_idx, contra_line) = if line_a.formula == **phi && (matches!(line_a.rule, Rule::Assumption) || matches!(line_a.rule, Rule::Premise)) {
                        (*idx_a, line_b)
                    } else if line_b.formula == **phi && (matches!(line_b.rule, Rule::Assumption) || matches!(line_a.rule, Rule::Premise)) {
                        (*idx_b, line_a)
                    } else {
                        return Err("NotIntroduction: referenced lines do not match required assumption and contradiction.".into());
                    };

                    // contra_line has to be a valid contradiction
                    match &contra_line.formula {
                        Formula::And(left, right) => match (left.as_ref(), right.as_ref()) {
                            (p1, Formula::Not(p2)) if p1 == p2.as_ref() => {}
                            (Formula::Not(p2), p1) if p2.as_ref() == p1 => {}
                            _ => return Err(format!("NotIntroduction: Line {} does not contain a valid contradiction (P ∧ ¬P).", contra_line.line_number).into()),
                        },
                        _ => return Err(format!("NotIntroduction: Line {} does not contain a valid contradiction (P ∧ ¬P).", contra_line.line_number).into()),
                    }

                    // the contradiction has to depend on the assumption
                    if !contra_line.premises_dependencies.contains(&assump_idx) {
                        return Err(format!(
                            "NotIntroduction: The contradiction in line {} does not depend on the assumption in line {}.",
                            contra_line.line_number, assump_idx
                        ));
                    }

                    // Check dependencys (resulting line has dependencys of the contradiction except from the assumption line number)
                    let mut expected_deps = contra_line.premises_dependencies.clone();
                    expected_deps.remove(&assump_idx);
                    check_deps(&line.premises_dependencies, &expected_deps)?;
                    Ok(())
                } else {
                    Err("NotIntroduction does not result in a negation.".into())
                }
            }
            Rule::EquivalentIntroduction(idx_a, idx_b) => { // EquivalentIntroduction requires two mirrored implications
                if let Formula::Equivalent(phi, psi) = &line.formula {
                    let line_a = get_line(all_lines, *idx_a)?;
                    let line_b = get_line(all_lines, *idx_b)?;

                    // match both combinations of the implications
                    let valid = match (&line_a.formula, &line_b.formula) {
                        (Formula::Implies(p1, q1), Formula::Implies(p2, q2)) => {
                            ((**p1 == **phi && **q1 == **psi) && (**p2 == **psi && **q2 == **phi)) ||
                            ((**p1 == **psi && **q1 == **phi) && (**p2 == **phi && **q2 == **psi))
                        }
                        _ => false
                    };

                    if valid {
                        let mut expected = line_a.premises_dependencies.clone();
                        expected.extend(&line_b.premises_dependencies);
                        check_deps(&line.premises_dependencies, &expected)?;
                        Ok(())
                    } else {
                        Err("EquivalentIntroduction: The lines do not contain the mirrored implications.".into())
                    }
                } else {
                    Err("EquivalentIntroduction does not result in an equivalent.".into())
                }
            }
        }
    }
}

/// Checks whether the dependencies have been inherited correctly.
fn check_deps(actual: &BTreeSet<usize>, expected: &BTreeSet<usize>) -> Result<(), String> {
    if actual == expected {
        Ok(())
    } else {
        Err("Dependencys do not match.".to_string())
    }
}

fn get_line<'a>(lines: &'a [ProofLine], num: usize) -> Result<&'a ProofLine, String> {
    lines.iter().find(|l| l.line_number == num)
        .ok_or_else(|| format!("Reference to invalid line {}", num))
}

