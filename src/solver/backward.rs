use crate::formula::{Formula, Proof, ProofLine, Rule};
use crate::solver::LogicSolver;
use std::collections::{BTreeSet};

pub struct BackwardSolver;

#[derive(Debug, Clone, PartialEq)]
pub struct Goal {
    pub formula: Formula, // Formula that we want to reach
    pub allowed_dependencies: BTreeSet<usize>, // allowed dependencys for the goal-line
}
impl Goal {
    fn new(formula: Formula, allowed_dependencies: BTreeSet<usize>) -> Self {
        Goal { formula: formula, allowed_dependencies: allowed_dependencies }
    }
}

pub struct ProofState {
    lines: Vec<ProofLine>, // current lines in the proof
    next_line_number: usize,
    active_goals: Vec<Goal>, // list of sub-goals
    num_premises: usize, // Number of premises (also line_num of last premise)
}
impl ProofState {
    fn new(num_premises: usize) -> Self {
        ProofState {
            lines: Vec::new(),
            next_line_number: 1,
            active_goals: Vec::new(),
            num_premises: num_premises,
        }
    }

    // adds a line to the proof
    fn push_line(&mut self, dependencies: BTreeSet<usize>, formula: Formula, rule: Rule) -> usize {
        let line_num = self.next_line_number;
        let line = ProofLine {
            premises_dependencies: dependencies.clone(),
            line_number: line_num,
            formula: formula.clone(),
            rule,
        };
        self.lines.push(line);
        self.next_line_number += 1;
        line_num
    }

    // helper function that creates assumptions or references existing ones
    fn get_or_create_assumption(&mut self, formula: Formula) -> usize {
        for (i, line) in self.lines.iter().enumerate() {
            if matches!(line.rule, Rule::Assumption | Rule::Premise) && line.formula == formula { // check if this assumption already exists
                return i + 1;
            }
        }

        // if the assumption does not exist create a new one
        let asm_line = self.next_line_number;
        let mut asm_deps = BTreeSet::new();
        asm_deps.insert(asm_line);
        self.push_line(asm_deps, formula.clone(), Rule::Assumption);
        
        asm_line
    }

    fn find_proven_line(&self, formula: &Formula) -> Option<usize> {
        for line in self.lines.iter().rev() {
            if line.formula == *formula {
                if line.premises_dependencies.iter().all(|dep| self.num_premises >= *dep) { // formula only depends on premises
                    return Some(line.line_number);
                }
            }
        }
        None
    }

    // Find line_num with given formula, that depends only on a subset of allowed_dependencys
    pub fn find_valid_line(&self, goal: &Goal) -> Option<usize> {
        for line in self.lines.iter().rev() {
            if line.formula == goal.formula && line.premises_dependencies.is_subset(&goal.allowed_dependencies) {
                return Some(line.line_number);
            }
        }
        None
    }

}

/// The atomic steps of the solver.
#[derive(Debug, Clone)]
enum Task {
    Solve(Goal),
    SolveForward(Goal),  // Elimination-rules (implicitly covers all deterministic elimination-rules (except rule 6))
    SolveBackward(Goal), // Introduction-rules // rule 2, 4, 6, 8, 10
    SolveIndirect(Goal), // Proof by contradiction

    // Introduction Rules (Backwards)
    BuildAndIntroduction(Formula, Formula, Goal),               // rule 3
    BuildImpliesIntroduction(usize, Formula, Formula, Goal),    // rule 5
    BuildOrIntroductionLeft(Formula, Goal),                     // rule 7
    BuildOrIntroductionRight(Formula, Goal),                    // rule 7
    BuildNotIntroduction(usize, Goal),                          // rule 9
    BuildEquivalentIntroduction(Formula, Formula, Goal),        // rule 11

    // Elimination Rules (Forward)
    // rule 6 (Or Elimination) is the only non-deterministic elimination-rule
    ApplyOrElimination { fact_line: usize, phi: Formula, psi: Formula, goal: Goal },
    ApplyOrEliminationPart2 { fact_line: usize, asm_phi: usize, psi: Formula, goal: Goal },
    ApplyOrEliminationFinal { fact_line: usize, asm_phi: usize, line_goal_phi: usize, asm_psi: usize, psi: Formula, goal: Goal },

    // Search Contradictions (Regel 9 / Reductio ad Absurdum)
    SearchContradiction { assumption_line: usize, goal: Goal, fallback_depth: usize, max_line_index: usize},
    
    // Stack Cleanup
    PopGoal(Goal),
}

impl BackwardSolver {
    const MAX_ITERATIONS: usize = 10_000_000;
    const MAX_NESTING_DEPTH: usize = 1; // maximum allowed number of nested levels of assumptions while constructing contradictions. 0 for simple proofs, 1 is fine for medium complex proofs. This parameter exponentially increases runtime and needed number of iterations.

    fn run_solver(&self, initial_goal: Goal, state: &mut ProofState) {
        let mut agenda: Vec<Task> = vec![Task::Solve(initial_goal)]; // Stack for Tasks

        let mut iterations = 0;
        while let Some(task) = agenda.pop() && iterations < Self::MAX_ITERATIONS {
            iterations += 1;
            
            match task {
                Task::Solve(goal) => { // Start proof for new (sub-)goal
                    if state.find_valid_line(&goal).is_some() { // Goal was already reached
                        continue;
                    }

                    // Check for Cycles (An iteration is a cycle, when its goal is identical to a previous goal // Goals are identical, when formulas and allowed_dependencys match.)
                    if state.active_goals.iter().any(|g| {
                        g.formula == goal.formula && goal.allowed_dependencies.is_subset(&g.allowed_dependencies)
                    }) {
                        println!("Cycle detected, with goal: {:?}", goal);
                        break; // continue; // Cycles should not be possible, this is only an assurance
                    }
                    // println!("Solve: {:?}", goal);

                    state.active_goals.push(goal.clone());
                    agenda.push(Task::PopGoal(goal.clone()));

                    // Forward -> Backward -> Indirect
                    agenda.push(Task::SolveIndirect(goal.clone())); // Try proving by contradiction as a last resort
                    agenda.push(Task::SolveBackward(goal.clone())); // Deduce backwards from the goal with introduction-rules
                    agenda.push(Task::SolveForward(goal.clone())); // Deduce as much as possible with elimination-rules
                }

                Task::SolveForward(goal) => {
                    if state.find_valid_line(&goal).is_some() { continue; }
                    
                    let mut progress = true;
                    while progress { // as long as we can deduce new formulas
                        progress = false;

                        if state.find_valid_line(&goal).is_some() { break; }
                        
                        let valid_facts: Vec<(Formula, usize)> = state.lines.iter()
                            .filter(|line| line.premises_dependencies.is_subset(&goal.allowed_dependencies)) // use only lines that could derive the goal with valid dependencys
                            .map(|line| (line.formula.clone(), line.line_number))
                            .collect();

                        for (fact, line_fact) in &valid_facts {
                            if self.derive_new_facts(fact, *line_fact, &goal, state, &mut agenda) {
                                progress = true;
                                if state.find_valid_line(&goal).is_some() {
                                    break;
                                }
                            }
                        }
                    }
                }

                Task::SolveBackward(goal) => {
                    if state.find_valid_line(&goal).is_some() { continue; }

                    match &goal.formula {
                        // And Introduction, goal: (A & B) -> find: A, B
                        Formula::And(phi, psi) => {
                            agenda.push(Task::BuildAndIntroduction(*phi.clone(), *psi.clone(), goal.clone()));

                            agenda.push(Task::Solve(Goal::new(*psi.clone(), goal.allowed_dependencies.clone())));
                            agenda.push(Task::Solve(Goal::new(*phi.clone(), goal.allowed_dependencies.clone())));
                        }
                        // Implication Introduction, goal: (A->B) -> find: A(Assumption), B(depends on A_line)
                        Formula::Implies(phi, psi) => {
                            let asm_line = state.get_or_create_assumption(*phi.clone());

                            let mut new_allowed = goal.allowed_dependencies.clone();
                            new_allowed.insert(asm_line);

                            agenda.push(Task::BuildImpliesIntroduction(asm_line, *phi.clone(), *psi.clone(), goal.clone()));
                            agenda.push(Task::Solve(Goal::new(*psi.clone(), new_allowed)));
                        }
                        // Or Introduction, goal: (AvB) -> find: A or find: B
                        Formula::Or(phi, psi) => {
                            let goal_phi = Goal::new(*phi.clone(), goal.allowed_dependencies.clone());
                            let goal_psi = Goal::new(*psi.clone(), goal.allowed_dependencies.clone());

                            if state.find_valid_line(&goal_phi).is_some() { // find the left side (phi)
                                agenda.push(Task::BuildOrIntroductionLeft(*psi.clone(), goal.clone()));
                            } else if state.find_valid_line(&goal_psi).is_some() { // find the right side (psi)
                                agenda.push(Task::BuildOrIntroductionRight(*phi.clone(), goal.clone()));
                            } else { // if no side was found, we have to solve for phi or psi (searching for both in random order)
                                agenda.push(Task::BuildOrIntroductionRight(*phi.clone(), goal.clone()));
                                agenda.push(Task::Solve(goal_psi));

                                agenda.push(Task::BuildOrIntroductionLeft(*psi.clone(), goal.clone()));
                                agenda.push(Task::Solve(goal_phi));
                            }
                        }
                        // Not Introduction, goal: !A -> find: A(Assumption), Contradiction(depends on A_line)
                        Formula::Not(phi) => {
                            let asm_line = state.get_or_create_assumption(*phi.clone());

                            let mut new_allowed = goal.allowed_dependencies.clone();
                            new_allowed.insert(asm_line); // also allowes the assumption to construct the contradiction

                            let forward_goal = Goal::new(goal.formula.clone(), new_allowed);

                            agenda.push(Task::BuildNotIntroduction(asm_line, goal.clone()));
                            agenda.push(Task::SearchContradiction { assumption_line: asm_line, goal: forward_goal.clone(), fallback_depth: 0, max_line_index: state.lines.len()});
                            agenda.push(Task::SolveForward(forward_goal)); 
                        }
                        // Equivalent Introduction, goal: (A<->B) -> find: (A->B), (B->A)
                        Formula::Equivalent(phi, psi) => {
                            let impl1 = Formula::Implies(phi.clone(), psi.clone());
                            let impl2 = Formula::Implies(psi.clone(), phi.clone());
                            
                            agenda.push(Task::BuildEquivalentIntroduction(impl1.clone(), impl2.clone(), goal.clone()));
                            agenda.push(Task::Solve(Goal::new(impl2, goal.allowed_dependencies.clone())));
                            agenda.push(Task::Solve(Goal::new(impl1, goal.allowed_dependencies.clone())));
                        }
                        _ => {}
                    }
                }

                Task::SolveIndirect(goal) => {
                    if state.find_valid_line(&goal).is_some() { continue; }

                    let not_goal_formula = Formula::Not(Box::new(goal.formula.clone()));
                    let goal_not_goal = Goal::new(not_goal_formula.clone(), goal.allowed_dependencies.clone());
                    if state.find_valid_line(&goal_not_goal).is_some() {
                        continue;
                    }

                    let line_not_goal = state.get_or_create_assumption(not_goal_formula.clone());
                    //println!("-> Assume: {:?} (for Contradiction Proof)", not_goal_formula);

                    // add the new assumption to allowed dependencys for the contradiction
                    let mut sub_context = goal.allowed_dependencies.clone();
                    sub_context.insert(line_not_goal);
                    let sub_goal = Goal::new(goal.formula.clone(), sub_context);

                    agenda.push(Task::SearchContradiction { 
                        assumption_line: line_not_goal, 
                        goal: sub_goal.clone(),
                        fallback_depth: 0,
                        max_line_index: state.lines.len()
                    });
                    
                    agenda.push(Task::Solve(sub_goal));
                }

                Task::SearchContradiction { assumption_line, goal, fallback_depth: nesting_depth, max_line_index} => {
                    let mut parent_deps = goal.allowed_dependencies.clone();
                    parent_deps.remove(&assumption_line);
                    let parent_goal = Goal::new(goal.formula.clone(), parent_deps);
                    
                    if state.find_valid_line(&parent_goal).is_some() { 
                        continue; 
                    }

                    let mut found = false;
                    
                    // Search for a pair of formulas (C and !C) to construct a contradiction
                    for i in 0..state.lines.len() {
                        let line_num_c = i + 1;
                        let goal_c = Goal::new(state.lines[i].formula.clone(), goal.allowed_dependencies.clone());
                        
                        // test if C is valid
                        if state.find_valid_line(&goal_c) == Some(line_num_c) {
                            let not_c = Formula::Not(Box::new(state.lines[i].formula.clone()));
                            let goal_not_c = Goal::new(not_c, goal.allowed_dependencies.clone());
                            
                            // Search a valid !C
                            if let Some(line_num_not_c) = state.find_valid_line(&goal_not_c) {
                                // Found a contradiction
                                let formula_c = state.lines[line_num_c - 1].formula.clone();
                                let formula_asm = state.lines[assumption_line - 1].formula.clone();
                                
                                // Here we perform an AndIntroduction and an AndElimination to get C depending on the assumption
                                // This trick is common in the calculus of natural deduction as we defined it
                                let mut mixed_deps = state.lines[line_num_c - 1].premises_dependencies.clone();
                                mixed_deps.insert(assumption_line);
                                
                                let mixed_and = Formula::And(Box::new(formula_c.clone()), Box::new(formula_asm));
                                let line_mixed = state.push_line(mixed_deps.clone(), mixed_and, Rule::AndIntroduction(line_num_c, assumption_line));
                                let line_forced_c = state.push_line(mixed_deps, formula_c, Rule::AndElimination(line_mixed));
                                
                                // Building the final contradiction (C & !C)
                                let mut contra_deps = state.lines[line_forced_c - 1].premises_dependencies.clone();
                                contra_deps.extend(&state.lines[line_num_not_c - 1].premises_dependencies);
                                
                                let formula_not_c = state.lines[line_num_not_c - 1].formula.clone();
                                let contra_formula = Formula::And(Box::new(state.lines[line_forced_c - 1].formula.clone()), Box::new(formula_not_c));
                                let line_contra = state.push_line(contra_deps, contra_formula, Rule::AndIntroduction(line_forced_c, line_num_not_c));
                                
                                let mut discharged_deps = state.lines[line_contra - 1].premises_dependencies.clone();
                                discharged_deps.remove(&assumption_line);
                                
                                let negated_asm = Formula::Not(Box::new(state.lines[assumption_line - 1].formula.clone()));
                                
                                if goal.formula == negated_asm { // direct proof (!assumption is the goal)
                                    state.push_line(discharged_deps, goal.formula.clone(), Rule::NotIntroduction(assumption_line, line_contra));
                                } else { // indirect proof (assumption was a negation) then we get !!goal so a NotElimination is needed
                                    let line_double_not = state.push_line(discharged_deps.clone(), negated_asm, Rule::NotIntroduction(assumption_line, line_contra));
                                    state.push_line(discharged_deps, goal.formula.clone(), Rule::NotElimination(line_double_not));
                                }
                                
                                //println!("-> Proof by contradiction successfully completed!");
                                found = true;
                                break;
                            }
                        }
                    }
                    
                    // If there exists no combination of formulas to create a contradiciton, we need to create a contradiction by searching for negations of known formulas
                    if !found && nesting_depth < Self::MAX_NESTING_DEPTH {
                        for i in 0..max_line_index {
                            let goal_c = Goal::new(state.lines[i].formula.clone(), goal.allowed_dependencies.clone());
                            if state.find_valid_line(&goal_c).is_some() {
                                let partner_formula = match &state.lines[i].formula {
                                    Formula::Not(inner) => (**inner).clone(),
                                    other => Formula::Not(Box::new(other.clone())),
                                };
                                let goal_partner = Goal::new(partner_formula.clone(), goal.allowed_dependencies.clone());

                                let is_circular = partner_formula == goal.formula;

                                let already_solving = state.active_goals.iter().any(|active_g| {
                                    active_g.formula == partner_formula 
                                        && active_g.allowed_dependencies == goal_partner.allowed_dependencies
                                        //&& goal_partner.allowed_dependencies.is_subset(&active_g.allowed_dependencies)
                                });
                                
                                if !is_circular && !already_solving && state.find_valid_line(&goal_partner).is_none() {
                                    agenda.push(Task::SearchContradiction { assumption_line, goal: goal.clone(), fallback_depth: nesting_depth+1, max_line_index});
                                    agenda.push(Task::Solve(goal_partner));
                                    break;
                                }

                            }
                        }
                    }
                }

                // Line Builder (when everything that is needed exists in the proof a new line can be constructed)
                Task::BuildAndIntroduction(phi, psi, goal) => {
                    if state.find_valid_line(&goal).is_some() { continue; }

                    let goal_phi = Goal::new(phi, goal.allowed_dependencies.clone());
                    let goal_psi = Goal::new(psi, goal.allowed_dependencies.clone());

                    if let (Some(l_phi), Some(l_psi)) = (state.find_valid_line(&goal_phi), state.find_valid_line(&goal_psi)) {
                        let mut deps = state.lines[l_phi - 1].premises_dependencies.clone();
                        deps.extend(&state.lines[l_psi - 1].premises_dependencies);

                        state.push_line(deps, goal.formula.clone(), Rule::AndIntroduction(l_phi, l_psi));
                        //println!("-> AndIntroduction: {:?}", goal.formula);
                    }
                }
                Task::BuildImpliesIntroduction(asm_line, phi, psi, goal) => {
                    if state.find_valid_line(&goal).is_some() { continue; }
                    
                    let mut sub_context = goal.allowed_dependencies.clone();
                    sub_context.insert(asm_line);
                    let goal_psi = Goal::new(psi.clone(), sub_context);

                    if let Some(l_psi) = state.find_valid_line(&goal_psi) {
                        let mut final_l_psi = l_psi;

                        // To get psi depending on phi, we apply an AndIntroduction and an AndElimination
                        if !state.lines[l_psi - 1].premises_dependencies.contains(&asm_line) {
                            let mut and_deps = state.lines[l_psi - 1].premises_dependencies.clone();
                            and_deps.insert(asm_line);
                            
                            // build (psi & phi)
                            let and_formula = Formula::And(Box::new(psi.clone()), Box::new(phi.clone()));
                            let line_and = state.push_line(
                                and_deps.clone(), 
                                and_formula, 
                                Rule::AndIntroduction(l_psi, asm_line)
                            );
                            
                            // get psi with the correct dependencys
                            final_l_psi = state.push_line(
                                and_deps, 
                                psi.clone(), 
                                Rule::AndElimination(line_and)
                            );
                        }

                        let mut deps = state.lines[l_psi - 1].premises_dependencies.clone();
                        deps.remove(&asm_line);

                        state.push_line(deps, goal.formula.clone(), Rule::ImpliesIntroduction(asm_line, final_l_psi));
                        //println!("-> ImpliesIntroduction: {:?}", goal.formula);
                    }
                }
                Task::BuildOrIntroductionLeft(_psi, goal) => {
                    if state.find_valid_line(&goal).is_some() { continue; }

                    if let Formula::Or(phi, _) = &goal.formula {
                        let goal_phi = Goal::new(*phi.clone(), goal.allowed_dependencies.clone());
                        if let Some(l_phi) = state.find_valid_line(&goal_phi) {
                            let deps = state.lines[l_phi - 1].premises_dependencies.clone();
                            state.push_line(deps, goal.formula.clone(), Rule::OrIntroduction(l_phi));
                            //println!("-> OrIntroductionLeft: {:?}", goal.formula);
                        }
                    }
                }
                Task::BuildOrIntroductionRight(_psi, goal) => {
                    if state.find_valid_line(&goal).is_some() { continue; }

                    if let Formula::Or(_, psi) = &goal.formula {
                        let goal_psi = Goal::new(*psi.clone(), goal.allowed_dependencies.clone());
                        if let Some(l_psi) = state.find_valid_line(&goal_psi) {
                            let deps = state.lines[l_psi - 1].premises_dependencies.clone();
                            state.push_line(deps, goal.formula.clone(), Rule::OrIntroduction(l_psi));
                            //println!("-> OrIntroductionRight {:?}", goal.formula);
                        }
                    }
                }
                Task::BuildNotIntroduction(asm_line, goal) => {
                    if state.find_valid_line(&goal).is_some() { continue; }

                    let mut sub_context = goal.allowed_dependencies.clone();
                    sub_context.insert(asm_line);

                    let mut contradiction_line_num = None;

                    // Searching backwards for the correct contradiction-line
                    for line in state.lines.iter().rev() {
                        if !line.premises_dependencies.is_subset(&sub_context) {
                            continue;
                        }
                        if !line.premises_dependencies.contains(&asm_line) { // contradiction has to depend on the assumption
                            continue;
                        }
                        if let Formula::And(left, right) = &line.formula { // a contradiction has the syntax (C & ~C) or (~C & C)
                            let is_contradiction = match (&**left, &**right) {
                                (c, Formula::Not(inner)) => c == &**inner,
                                (Formula::Not(inner), c) => c == &**inner,
                                _ => false,
                            };

                            if is_contradiction {
                                contradiction_line_num = Some(line.line_number);
                                break;
                            }
                        }
                    }

                    if let Some(l_contra) = contradiction_line_num { // contradiction was found
                        let mut deps = state.lines[l_contra - 1].premises_dependencies.clone();
                        deps.remove(&asm_line);

                        state.push_line(deps, goal.formula.clone(), Rule::NotIntroduction(asm_line, l_contra));
                        //println!("-> NotIntroduction {:?} using contradiciton in line: {}", goal.formula, l_contra);
                    }
                }
                Task::BuildEquivalentIntroduction(impl_lr, impl_rl, goal) => {
                    if state.find_valid_line(&goal).is_some() { continue; }

                    let goal_lr = Goal::new(impl_lr, goal.allowed_dependencies.clone());
                    let goal_rl = Goal::new(impl_rl, goal.allowed_dependencies.clone());

                    if let (Some(l_lr), Some(l_rl)) = (state.find_valid_line(&goal_lr), state.find_valid_line(&goal_rl)) {
                        let mut deps = state.lines[l_lr - 1].premises_dependencies.clone();
                        deps.extend(&state.lines[l_rl - 1].premises_dependencies);

                        state.push_line(deps, goal.formula.clone(), Rule::EquivalentIntroduction(l_lr, l_rl));
                        //println!("-> EquivalentIntroduction: {:?}", goal.formula);
                    }
                }

                // Elimination rules (non-deterministic branching)
                Task::ApplyOrElimination { fact_line, phi, psi, goal } => {
                    if state.find_valid_line(&goal).is_some() { continue; }
                    
                    // New assumption for the left path
                    let asm_phi = state.get_or_create_assumption(phi.clone());
                    //println!("--> Assume: {:?} for OrElimination (Left Branch)", phi);

                    let mut context_phi = goal.allowed_dependencies.clone();
                    context_phi.insert(asm_phi);
                    let goal_phi = Goal::new(goal.formula.clone(), context_phi);

                    agenda.push(Task::ApplyOrEliminationPart2 { 
                        fact_line, 
                        asm_phi, 
                        psi, 
                        goal: goal.clone() 
                    });
                    agenda.push(Task::Solve(goal_phi));
                }

                Task::ApplyOrEliminationPart2 { fact_line, asm_phi, psi, goal } => {
                    let mut context_phi = goal.allowed_dependencies.clone();
                    context_phi.insert(asm_phi);
                    let goal_phi = Goal::new(goal.formula.clone(), context_phi);

                    if let Some(line_goal_phi) = state.find_valid_line(&goal_phi) {
                        // new assumption for the right path
                        let asm_psi = state.get_or_create_assumption(psi.clone());
                        //println!("--> Assume: {:?} for OrElimination (Right Branch)", psi);

                        let mut context_psi = goal.allowed_dependencies.clone();
                        context_psi.insert(asm_psi);
                        let goal_psi = Goal::new(goal.formula.clone(), context_psi);

                        agenda.push(Task::ApplyOrEliminationFinal { 
                            fact_line, 
                            asm_phi, 
                            line_goal_phi,
                            asm_psi, 
                            psi, 
                            goal: goal.clone() 
                        });
                        agenda.push(Task::Solve(goal_psi));
                    }
                }

                Task::ApplyOrEliminationFinal { fact_line, asm_phi, line_goal_phi, asm_psi, psi, goal } => {
                    let mut context_psi = goal.allowed_dependencies.clone();
                    context_psi.insert(asm_psi);
                    let goal_psi = Goal::new(goal.formula.clone(), context_psi);

                    if let Some(line_goal_psi) = state.find_valid_line(&goal_psi) {
                        let phi_formula = state.lines[asm_phi - 1].formula.clone();
                        
                        // left implication (phi -> goal)
                        let impl_phi_formula = Formula::Implies(Box::new(phi_formula.clone()), Box::new(goal.formula.clone()));
                        let goal_impl_phi = Goal::new(impl_phi_formula.clone(), goal.allowed_dependencies.clone());
                        
                        let line_impl_phi = if let Some(existing_line) = state.find_valid_line(&goal_impl_phi) {
                            existing_line
                        } else {
                            // check if the assumption was used, else add the dependency with the AndIntroductionElimination trick
                            let mut final_line_phi = line_goal_phi;
                            if !state.lines[line_goal_phi - 1].premises_dependencies.contains(&asm_phi) {
                                let mut and_deps = state.lines[line_goal_phi - 1].premises_dependencies.clone();
                                and_deps.insert(asm_phi);
                                
                                // AndIntroduction
                                let and_formula = Formula::And(Box::new(goal.formula.clone()), Box::new(phi_formula));
                                let line_and = state.push_line(and_deps.clone(), and_formula, Rule::AndIntroduction(line_goal_phi, asm_phi));
                                
                                // AndElimination
                                final_line_phi = state.push_line(and_deps, goal.formula.clone(), Rule::AndElimination(line_and));
                            }

                            let mut deps_phi = state.lines[final_line_phi - 1].premises_dependencies.clone();
                            deps_phi.remove(&asm_phi);
                            state.push_line(deps_phi, impl_phi_formula, Rule::ImpliesIntroduction(asm_phi, final_line_phi))
                        };

                        // right implication (psi -> goal)
                        let impl_psi_formula = Formula::Implies(Box::new(psi.clone()), Box::new(goal.formula.clone()));
                        let goal_impl_psi = Goal::new(impl_psi_formula.clone(), goal.allowed_dependencies.clone());

                        let line_impl_psi = if let Some(existing_line) = state.find_valid_line(&goal_impl_psi) {
                            existing_line
                        } else {
                            // check if the assumption was used, else add the dependency with the AndIntroductionElimination trick
                            let mut final_line_psi = line_goal_psi;
                            if !state.lines[line_goal_psi - 1].premises_dependencies.contains(&asm_psi) {
                                let mut and_deps = state.lines[line_goal_psi - 1].premises_dependencies.clone();
                                and_deps.insert(asm_psi);
                                
                                // AndIntroduction
                                let and_formula = Formula::And(Box::new(goal.formula.clone()), Box::new(psi));
                                let line_and = state.push_line(and_deps.clone(), and_formula, Rule::AndIntroduction(line_goal_psi, asm_psi));
                                
                                // AndElimination
                                final_line_psi = state.push_line(and_deps, goal.formula.clone(), Rule::AndElimination(line_and));
                            }

                            let mut deps_psi = state.lines[final_line_psi - 1].premises_dependencies.clone();
                            deps_psi.remove(&asm_psi);
                            state.push_line(deps_psi, impl_psi_formula, Rule::ImpliesIntroduction(asm_psi, final_line_psi))
                        };

                        // final OrElimination
                        let mut combined_deps = state.lines[fact_line - 1].premises_dependencies.clone();
                        combined_deps.extend(&state.lines[line_impl_phi - 1].premises_dependencies);
                        combined_deps.extend(&state.lines[line_impl_psi - 1].premises_dependencies);

                        state.push_line(combined_deps, goal.formula.clone(), Rule::OrElimination(fact_line, line_impl_phi, line_impl_psi));
                        //println!("-> OrElimination: {:?}", goal.formula);
                    }
                }

                // Stack Cleanup
                Task::PopGoal(goal) => {
                    if let Some(pos) = state.active_goals.iter().rposition(|g| {
                        g.formula == goal.formula && g.allowed_dependencies == goal.allowed_dependencies
                    }) {
                        state.active_goals.remove(pos);
                    }
                    //println!("Pop: {:?}", goal);
                }
            }
        }
    }

    fn derive_new_facts(&self, fact: &Formula, line_fact: usize, goal: &Goal, state: &mut ProofState, agenda: &mut Vec<Task>) -> bool { // is called for every formula
        if state.find_valid_line(goal).is_some() {
            return false;
        }
        let mut added_new = false;

        match fact {
            Formula::And(phi, psi) => {
                let deps = state.lines[line_fact - 1].premises_dependencies.clone();
                for part in [phi, psi] {
                    let sub_goal = Goal::new(*part.clone(), goal.allowed_dependencies.clone());

                    if state.find_valid_line(&sub_goal).is_none() {
                        state.push_line(deps.clone(), *part.clone(), Rule::AndElimination(line_fact));
                        //println!("-> AndElimination: {:?} (found by Forward Search)", *part.clone());
                        added_new = true;
                    }
                }
            }
            Formula::Implies(phi, psi) => {
                let phi_goal = Goal::new(*phi.clone(), goal.allowed_dependencies.clone());

                if let Some(line_phi) = state.find_valid_line(&phi_goal) {
                    let psi_goal = Goal::new(*psi.clone(), goal.allowed_dependencies.clone());

                    if state.find_valid_line(&psi_goal).is_none() {
                        let mut combined_deps = state.lines[line_fact - 1].premises_dependencies.clone();
                        combined_deps.extend(&state.lines[line_phi - 1].premises_dependencies);
                        state.push_line(combined_deps, *psi.clone(), Rule::ImpliesElimination(line_fact, line_phi));
                        //println!("-> ImpliesElimination: {:?} (found by Forward)", *psi.clone());
                        added_new = true;
                    }
                }
            }
            Formula::Or(phi, psi) => {
                let already_eliminated = state.lines.iter().any(|line| {
                    let is_assumption = matches!(line.rule, Rule::Assumption);
                    let is_matching_formula = line.formula == **phi || line.formula == **psi;
                    let is_currently_allowed = goal.allowed_dependencies.contains(&line.line_number);

                    is_assumption && is_matching_formula && is_currently_allowed
                });

                if already_eliminated { // we are currently in a sub-proof of this OrElimination
                    return false; 
                }

                // For the OrElimination two implications are required
                let req_impl_phi = Formula::Implies(phi.clone(), Box::new(goal.formula.clone()));
                let req_impl_psi = Formula::Implies(psi.clone(), Box::new(goal.formula.clone()));

                let goal_phi = Goal::new(req_impl_phi, goal.allowed_dependencies.clone());
                let goal_psi = Goal::new(req_impl_psi, goal.allowed_dependencies.clone());

                if let (Some(l_phi), Some(l_psi)) = (state.find_valid_line(&goal_phi), state.find_valid_line(&goal_psi)) { // if both required Implications exists
                    if state.find_valid_line(goal).is_none() {
                        let mut combined_deps = state.lines[line_fact - 1].premises_dependencies.clone();
                        combined_deps.extend(&state.lines[l_phi - 1].premises_dependencies);
                        combined_deps.extend(&state.lines[l_psi - 1].premises_dependencies);

                        state.push_line(combined_deps, goal.formula.clone(), Rule::OrElimination(line_fact, l_phi, l_psi));
                        //println!("-> OrElimination applyed, using lines {}, {} and {}", line_fact, l_phi, l_psi);
                        added_new = true;
                    }
                } else { // if the required implications are missing -> create new task
                    let already_working = state.active_goals.contains(&goal_phi) || state.active_goals.contains(&goal_psi);

                    if !already_working {
                        let already_pushed = agenda.iter().any(|t| match t {
                            Task::ApplyOrElimination { fact_line, goal: task_goal, .. } => {
                                *fact_line == line_fact && task_goal.formula == goal.formula
                            }
                            _ => false
                        });

                        if !already_pushed {
                            agenda.push(Task::ApplyOrElimination {
                                fact_line: line_fact, 
                                phi: *phi.clone(), 
                                psi: *psi.clone(), 
                                goal: goal.clone()
                            });
                        }
                    }
                }
            }
            Formula::Not(inner) => {
                if let Formula::Not(phi) = inner.as_ref() {
                    let phi_goal = Goal::new(*phi.clone(), goal.allowed_dependencies.clone());

                    if state.find_valid_line(&phi_goal).is_none() {
                        let deps = state.lines[line_fact - 1].premises_dependencies.clone();
                        state.push_line(deps, *phi.clone(), Rule::NotElimination(line_fact));
                        //println!("-> NotElimination: {:?} (found by Forward Search)", *phi.clone());
                        added_new = true;
                    }
                }
            }
            Formula::Equivalent(phi, psi) => {
                let impl1 = Formula::Implies(phi.clone(), psi.clone());
                let impl2 = Formula::Implies(psi.clone(), phi.clone());
                for imp in [impl1, impl2] {
                    let imp_goal = Goal::new(imp.clone(), goal.allowed_dependencies.clone());

                    if state.find_valid_line(&imp_goal).is_none() {
                        let deps = state.lines[line_fact - 1].premises_dependencies.clone();
                        state.push_line(deps, imp.clone(), Rule::EquivalentElimination(line_fact));
                        //println!("-> EquivalentElimination: {:?} (found by Forward Search)", imp);
                        added_new = true;
                    }
                }
            }
            
            _ => {}
        }
        added_new
    }
}

impl LogicSolver for BackwardSolver {
    fn solve(&self, premises: &[Formula], conclusion: &Formula) -> Option<Proof> {
        let mut state = ProofState::new(premises.len());

        // Assume all premises
        for premise in premises {
            let mut deps = BTreeSet::new();
            let line_num = state.next_line_number;
            deps.insert(line_num);
            
            state.push_line(deps, premise.clone(), Rule::Premise);
        }

        // Start the iterative agenda-mainloop
        let allowed_deps: BTreeSet<usize> = state.lines.iter().map(|line| line.line_number).collect();
        self.run_solver(Goal::new(conclusion.clone(), allowed_deps), &mut state);

        if let Some(_final_line) = state.find_proven_line(conclusion) { // Found conclusion, depending only on premises
            Some(Proof {
                premises: premises.to_vec(),
                conclusion: conclusion.clone(),
                lines: state.lines,
            })
        } else {
            let proof = Proof { // No proof was found. The tried steps can still be helpful.
                premises: premises.to_vec(),
                conclusion: conclusion.clone(),
                lines: state.lines,
            };
            println!("Proof could not be found:\n{}", proof);
            None
        }
    }
}