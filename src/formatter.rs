use std::collections::{BTreeSet, HashMap, HashSet};
use crate::formula::{Formula, Proof, ProofLine, Rule};

/// Cleans a valid proof. Removes duplicate lines, eliminates non-referenced lines and restores the line numeration.
pub fn clean_proof(proof: &Proof) -> Proof {
    if proof.lines.is_empty() {
        return proof.clone();
    }

    // line deduplication (forward pass)

    // collect line numbers of all premises
    let mut seen_premises: HashMap<Formula, usize> = HashMap::new();
    for line in &proof.lines {
        if matches!(line.rule, Rule::Premise) {
            seen_premises.entry(line.formula.clone()).or_insert(line.line_number);
        }
    }

    let mut seen_facts: HashMap<(Formula, BTreeSet<usize>), usize> = HashMap::new(); // <(Formula, Dependencys), line number of first occurence>
    let mut replacement_map: HashMap<usize, usize> = HashMap::new(); // old line number, original line number (first occurence of this line)
    let mut deduplicated_lines = Vec::new(); // stores unique proof-lines

    for line in &proof.lines {
        // Assuming a premise is unnecessary. The assumption is replaced by an existing premise with the same formula.
        if matches!(line.rule, Rule::Assumption) {
            if let Some(&premise_line_num) = seen_premises.get(&line.formula) {
                replacement_map.insert(line.line_number, premise_line_num);
                continue;
            }
        }

        let key = (line.formula.clone(), line.premises_dependencies.clone());

        if let Some(&original_line_num) = seen_facts.get(&key) {
            // Found a line with a combination of formula and dependency-set, we have seen before. This line is a duplicate, so the original occurence can be referenced.
            replacement_map.insert(line.line_number, original_line_num);
        } else {
            // Found a new unique line.
            seen_facts.insert(key, line.line_number);
            deduplicated_lines.push(line.clone());
        }
    }

    // Fix line numbers in the rules
    for line in &mut deduplicated_lines {
        line.rule = remap_rule(&line.rule, &replacement_map);
    }

    // Dead-line-elimination (backward pass) // removes lines that are not referenced by the conclusion, thus are not necessary for the proof

    let mut required_lines = HashSet::new();

    // Premises are always kept, regardless of whether they have been used.
    for line in &deduplicated_lines {
        if matches!(line.rule, Rule::Premise) {
            required_lines.insert(line.line_number);
        }
    }

    // Finds the conlusion-line
    let target_line = deduplicated_lines
        .iter()
        .rfind(|line| line.formula == proof.conclusion)
        .unwrap_or_else(|| &deduplicated_lines[deduplicated_lines.len() - 1]);

    let mut queue = vec![target_line.line_number]; // queue of line-numbers referenced by the conclusion-line

    while let Some(current_num) = queue.pop() {
        if required_lines.insert(current_num) {
            if let Some(line) = deduplicated_lines.iter().find(|l| l.line_number == current_num) { // get proof-line
                queue.extend(get_rule_references(&line.rule)); // queue referenced lines
                //queue.extend(line.premises_dependencies.iter().cloned()); // not necessary, the rules list all references
            }
        }
    }

    // Fix line numbers

    let mut final_mapping = HashMap::new(); // current line number -> new line number
    let mut new_counter = 1;
    for line in &deduplicated_lines {
        if required_lines.contains(&line.line_number) {
            final_mapping.insert(line.line_number, new_counter);
            new_counter += 1;
        }
    }

    let mut final_lines = Vec::new();
    for line in &deduplicated_lines {
        if required_lines.contains(&line.line_number) {
            let new_line_number = final_mapping[&line.line_number];

            let mut new_deps = BTreeSet::new();
            for dep in &line.premises_dependencies {
                if let Some(&new_dep) = final_mapping.get(dep) {
                    new_deps.insert(new_dep);
                }
            }

            let new_rule = remap_rule(&line.rule, &final_mapping);

            final_lines.push(ProofLine {
                premises_dependencies: new_deps,
                line_number: new_line_number,
                formula: line.formula.clone(),
                rule: new_rule,
            });
        }
    }

    Proof {
        premises: proof.premises.clone(),
        conclusion: proof.conclusion.clone(),
        lines: final_lines,
    }
}


/// Returns a vector with line-numbers referenced by a rule
fn get_rule_references(rule: &Rule) -> Vec<usize> {
    match rule {
        Rule::Premise => vec![],
        Rule::Assumption => vec![],
        Rule::AndElimination(j) => vec![*j],
        Rule::AndIntroduction(j, k) => vec![*j, *k],
        Rule::ImpliesElimination(j, k) => vec![*j, *k],
        Rule::ImpliesIntroduction(j, k) => vec![*j, *k],
        Rule::OrElimination(j, k, l) => vec![*j, *k, *l],
        Rule::OrIntroduction(j) => vec![*j],
        Rule::NotElimination(j) => vec![*j],
        Rule::NotIntroduction(j, k) => vec![*j, *k],
        Rule::EquivalentElimination(j) => vec![*j],
        Rule::EquivalentIntroduction(j, k) => vec![*j, *k],
    }
}

/// Replaces line-numbers in a rule based on a replacement map
fn remap_rule(rule: &Rule, map: &HashMap<usize, usize>) -> Rule {
    let get_new = |old| *map.get(&old).unwrap_or(&old);

    match rule {
        Rule::Premise => Rule::Premise,
        Rule::Assumption => Rule::Assumption,
        Rule::AndElimination(j) => Rule::AndElimination(get_new(*j)),
        Rule::AndIntroduction(j, k) => Rule::AndIntroduction(get_new(*j), get_new(*k)),
        Rule::ImpliesElimination(j, k) => Rule::ImpliesElimination(get_new(*j), get_new(*k)),
        Rule::ImpliesIntroduction(j, k) => Rule::ImpliesIntroduction(get_new(*j), get_new(*k)),
        Rule::OrElimination(j, k, l) => Rule::OrElimination(get_new(*j), get_new(*k), get_new(*l)),
        Rule::OrIntroduction(j) => Rule::OrIntroduction(get_new(*j)),
        Rule::NotElimination(j) => Rule::NotElimination(get_new(*j)),
        Rule::NotIntroduction(j, k) => Rule::NotIntroduction(get_new(*j), get_new(*k)),
        Rule::EquivalentElimination(j) => Rule::EquivalentElimination(get_new(*j)),
        Rule::EquivalentIntroduction(j, k) => Rule::EquivalentIntroduction(get_new(*j), get_new(*k)),
    }
}