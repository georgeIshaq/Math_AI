import time

# --- Representation ---
# Facts and predicates are represented as simple strings for this proof-of-concept.
# e.g., "Parent(Alice, Bob)"

# --- Knowledge Base ---
# Axioms are implemented as Python functions.
# Each function takes the current set of known facts and returns a set of newly derived facts based on that axiom.

def axiom1_parent_ancestor(facts):
    """Applies the rule: ∀x,y (Parent(x, y) → Ancestor(x, y))"""
    new_facts = set()
    for fact in facts:
        if fact.startswith("Parent("):
            content = fact[7:-1]
            parts = content.split(',')
            if len(parts) == 2:
                x, y = parts[0].strip(), parts[1].strip()
                new_fact = f"Ancestor({x},{y})"
                if new_fact not in facts:
                    new_facts.add(new_fact)
    return new_facts

def axiom2_ancestor_transitive(facts):
    """Applies the rule: ∀x,y,z (Ancestor(x, y) ∧ Ancestor(y, z) → Ancestor(x, z))"""
    new_facts = set()
    # Create a list of ancestor pairs for efficient lookup
    ancestor_pairs = []
    for fact in facts:
        if fact.startswith("Ancestor("):
            content = fact[9:-1]
            parts = content.split(',')
            if len(parts) == 2:
                ancestor_pairs.append((parts[0].strip(), parts[1].strip()))

    # Check all combinations for transitivity (can be computationally expensive)
    # Iterate through pairs (x, y1) and (y2, z)
    for x, y1 in ancestor_pairs:
        for y2, z in ancestor_pairs:
            # If the intermediate nodes match (y1 == y2)
            if y1 == y2:
                # Derive the new transitive relationship
                new_fact = f"Ancestor({x},{z})"
                if new_fact not in facts:
                    new_facts.add(new_fact)
    return new_facts


def axiom5_ancestor_hasdna(facts):
    """Applies the rule: ∀x,y (Ancestor(x, y) → HasDNA(x, y))"""
    new_facts = set()
    for fact in facts:
        if fact.startswith("Ancestor("):
            content = fact[9:-1]
            parts = content.split(',')
            if len(parts) == 2:
                x, y = parts[0].strip(), parts[1].strip()
                new_fact = f"HasDNA({x},{y})"
                if new_fact not in facts:
                    new_facts.add(new_fact)
    return new_facts

def axiom8_dna_famous_trait(facts):
    """Applies the rule: ∀x,y (HasDNA(x, y) ∧ IsFamous(x) → MightInheritTrait(y))"""
    new_facts = set()
    has_dna_pairs = []
    is_famous_people = []

    for fact in facts:
        if fact.startswith("HasDNA("):
             content = fact[7:-1]
             parts = content.split(',')
             if len(parts) == 2:
                 has_dna_pairs.append((parts[0].strip(), parts[1].strip()))
        elif fact.startswith("IsFamous("):
             person = fact[9:-1].strip()
             is_famous_people.append(person)

    for famous_person in is_famous_people:
        for dna_x, dna_y in has_dna_pairs:
            if dna_x == famous_person:
                new_fact = f"MightInheritTrait({dna_y})"
                if new_fact not in facts:
                    new_facts.add(new_fact)
    return new_facts

def axiom10_sibling_shared_parent(facts):
    """Applies the rule: ∀x,y (Sibling(x,y) → ∃z (Parent(z,x) ∧ Parent(z,y)))"""
    new_facts = set()
    processed_siblings = set()
    existing_shared_parents = set()
    for fact in facts:
        if fact.startswith("Parent(SharedParent_"):
            content = fact[7:-1]
            parts = content.split(',')
            if len(parts) == 2:
                existing_shared_parents.add(parts[0].strip())

    for fact in facts:
        if fact.startswith("Sibling("):
            content = fact[8:-1]
            parts = content.split(',')
            if len(parts) == 2:
                x, y = sorted((parts[0].strip(), parts[1].strip()))
                sibling_pair = (x, y)
                if sibling_pair not in processed_siblings:
                    shared_parent_name = f"SharedParent_{x}_{y}"
                    if shared_parent_name not in existing_shared_parents:
                        fact1 = f"Parent({shared_parent_name},{x})"
                        fact2 = f"Parent({shared_parent_name},{y})"
                        if fact1 not in facts: new_facts.add(fact1)
                        if fact2 not in facts: new_facts.add(fact2)
                    processed_siblings.add(sibling_pair)
    return new_facts

def axiom11_hasdna_symmetric(facts):
    """Applies the rule: ∀x,y (HasDNA(x, y) → HasDNA(y, x))"""
    new_facts = set()
    for fact in facts:
        if fact.startswith("HasDNA("):
            content = fact[7:-1]
            parts = content.split(',')
            if len(parts) == 2:
                x, y = parts[0].strip(), parts[1].strip()
                new_fact = f"HasDNA({y},{x})"
                if new_fact not in facts:
                    new_facts.add(new_fact)
    return new_facts

# --- Lemma Definition ---
# This represents a known, valid inference rule that might be complex
# or non-obvious for the basic solver to apply quickly.
def lemma_link_parent_sibling_ancestor(facts):
    """Applies Lemma: ∀a,b,c (Parent(a,b) ∧ Sibling(b,c) → Ancestor(a,c))
       This lemma encodes the inference that if 'a' is a parent of 'b', and 'b' is a sibling
       of 'c', then 'a' is an ancestor of 'c' (implicitly assuming 'a' is the relevant
       shared parent for this link).
    """
    new_facts = set()
    parent_pairs = []
    sibling_pairs = []

    # Collect relevant facts
    for fact in facts:
        if fact.startswith("Parent("):
            content = fact[7:-1]
            parts = content.split(',')
            if len(parts) == 2:
                parent_pairs.append((parts[0].strip(), parts[1].strip()))
        elif fact.startswith("Sibling("):
            content = fact[8:-1]
            parts = content.split(',')
            if len(parts) == 2:
                 b, c = parts[0].strip(), parts[1].strip()
                 # Store both orders to match easily
                 sibling_pairs.append((b, c))
                 sibling_pairs.append((c, b))

    # Check conditions for the lemma
    for a, b1 in parent_pairs:         # Parent(a, b1)
        for b2, c in sibling_pairs:    # Sibling(b2, c)
            if b1 == b2:               # If b1 and b2 are the same 'b'
                # Derive the consequence of the lemma
                new_fact = f"Ancestor({a},{c})"
                if new_fact not in facts:
                    new_facts.add(new_fact)
    return new_facts


# List of all axiom functions to be applied by the solver
# Note: Lemma is NOT included here; it's applied strategically by the hint
axioms = [
    axiom1_parent_ancestor,
    axiom2_ancestor_transitive, # Added transitivity
    axiom5_ancestor_hasdna,
    axiom8_dna_famous_trait,
    axiom10_sibling_shared_parent,
    axiom11_hasdna_symmetric
]

# --- Initial Set of Known Facts ---
initial_facts = {
    "Person(Alice)",
    "Person(Bob)",
    "Person(Charles)",
    "Parent(Alice, Bob)",
    "Sibling(Bob, Charles)",
    "IsFamous(Alice)"
}

# --- Goal to Prove ---
goal = "MightInheritTrait(Charles)"

# --- Simple Forward Chaining Solver Implementation ---
def solve_forward_chaining(axioms_to_use, initial_facts_state, target_goal, max_depth, max_iterations=30, current_depth=0, is_rerun=False, verbose=True):
    """
    Performs basic forward chaining inference.
    Args:
        axioms_to_use (list): A list of axiom functions to apply.
        initial_facts_state (set): The starting set of known facts.
        target_goal (str): The fact the solver is trying to derive.
        max_depth (int): The maximum number of inference steps (depths) to perform.
        max_iterations (int): A safety limit on the total number of loop iterations.
        current_depth (int): The starting depth (used for reruns).
        is_rerun (bool): Flag to suppress initial messages during reruns.
        verbose (bool): Flag to control printing of steps.
    Returns:
        tuple: (solved (bool), final_facts (set), final_depth_reached (int))
    """
    known_facts = set(initial_facts_state)
    if not is_rerun and verbose:
        print(f"Initial Facts ({len(known_facts)}): {known_facts}")

    final_depth_reached = current_depth
    iterations = 0
    start_time = time.time() # Start timing

    for depth in range(current_depth, max_depth):
        if iterations >= max_iterations:
             if verbose: print(f"Stopping: Reached max iterations ({max_iterations})")
             break
        iterations += 1

        final_depth_reached = depth + 1
        if verbose and (not is_rerun or depth >= current_depth):
             print(f"\n--- Depth {depth + 1} ---")

        newly_derived_facts_this_step = set()
        made_progress = False
        current_state_facts = set(known_facts)

        for axiom_func in axioms_to_use:
            derived_by_axiom = axiom_func(current_state_facts)
            really_new_facts = derived_by_axiom - known_facts
            if really_new_facts:
                 newly_derived_facts_this_step.update(really_new_facts)
                 made_progress = True

        if not made_progress and not newly_derived_facts_this_step :
             if verbose: print("No new facts derived by any axiom (Fixed Point). Stopping.")
             break

        if target_goal in newly_derived_facts_this_step:
             if verbose: print(f"Goal '{target_goal}' derived at depth {depth + 1}!")
             known_facts.update(newly_derived_facts_this_step)
             if verbose: print(f"Final Facts ({len(known_facts)}): {known_facts}")
             end_time = time.time()
             if verbose: print(f"Time taken: {end_time - start_time:.4f} seconds")
             return True, known_facts, final_depth_reached

        if newly_derived_facts_this_step:
             if verbose and (not is_rerun or depth >= current_depth):
                  print(f"Derived this step: {newly_derived_facts_this_step}")
             known_facts.update(newly_derived_facts_this_step)
             if verbose and (not is_rerun or depth >= current_depth):
                  print(f"Total Known Facts: {len(known_facts)}")

    end_time = time.time() # End timing
    total_time = end_time - start_time

    if target_goal in known_facts:
        if verbose: print(f"\nGoal '{target_goal}' was reached within {final_depth_reached} steps.")
        if verbose: print(f"Time taken: {total_time:.4f} seconds")
        return True, known_facts, final_depth_reached
    else:
        if not is_rerun:
            if verbose:
                print(f"\nSolver stopped at depth {final_depth_reached}. Goal '{target_goal}' not reached.")
                print(f"Final Known Facts ({len(known_facts)}): {known_facts}")
                print(f"Time taken: {total_time:.4f} seconds")
                print("\n--- SIMULATING STUCK STATE ---")
                print("This is where the LLM would be called for a strategic hint.")
                print("Hint Suggestion: 'Apply Lemma_Link with a=Alice, b=Bob, c=Charles'")
        return False, known_facts, final_depth_reached

# --- Execution ---

# 1. Run the solver with a strict depth limit to show it gets stuck
print("--- Run 1: Limited Depth Solver ---")
DEPTH_LIMIT_STUCK = 3
solved1, final_facts1, stopped_depth1 = solve_forward_chaining(
    axioms, initial_facts, goal, DEPTH_LIMIT_STUCK, verbose=True
)
print(f"\nRun 1 Result: Solved={solved1}, Stopped at Depth={stopped_depth1}")

print("\n" + "="*30 + "\n")

# 2. Run the solver with a large depth limit (baseline without hint)
print("--- Run 2: Baseline Solver (Large Depth Limit) ---")
DEPTH_LIMIT_BASELINE = 10 # Allow more steps
solved_baseline, final_facts_baseline, stopped_depth_baseline = solve_forward_chaining(
    axioms, initial_facts, goal, DEPTH_LIMIT_BASELINE, verbose=True
)
print(f"\nRun 2 Result (Baseline): Solved={solved_baseline}, Stopped at Depth={stopped_depth_baseline}")

print("\n" + "="*30 + "\n")

# 3. Simulate applying the LLM hint if the first solver got stuck
print("--- Run 3: Solver with Simulated Lemma Hint ---")
if not solved1:
    print("Simulating LLM Hint: Suggesting application of Lemma_Link for a=Alice, b=Bob, c=Charles.")
    # Apply the lemma manually to the state where solver 1 got stuck
    facts_for_lemma_check = set(final_facts1) # Use facts from the stuck state
    derived_by_lemma = lemma_link_parent_sibling_ancestor(facts_for_lemma_check)

    if not derived_by_lemma:
         print("Could not apply the suggested lemma instance to the current facts.")
         knowledge_updated = False
    else:
        print(f"Lemma application derived: {derived_by_lemma}")
        # Add the derived fact(s)
        current_facts_with_hint = set(final_facts1)
        knowledge_updated = False
        for new_fact in derived_by_lemma:
            if new_fact not in current_facts_with_hint:
                current_facts_with_hint.add(new_fact)
                knowledge_updated = True

        if knowledge_updated:
            print(f"Facts after adding hint ({len(current_facts_with_hint)}): {current_facts_with_hint}")
            # Re-run the solver from the hint-updated state until completion
            print("\nRe-running solver from hint-updated state until completion...")
            DEPTH_LIMIT_RERUN = 10 # Use same limit as baseline for fair comparison
            solved_after_hint, final_facts_after_hint, stopped_depth_after_hint = solve_forward_chaining(
                axioms,
                current_facts_with_hint, # Start with facts + lemma result
                goal,
                DEPTH_LIMIT_RERUN,
                current_depth=stopped_depth1, # Start counting depth after initial run
                is_rerun=True,
                verbose=True # Set verbose=False for less output if desired
            )
            print(f"\nRun 3 Result (Hint): Solved={solved_after_hint}, Stopped at Depth={stopped_depth_after_hint}")

            # 4. Comparison
            print("\n--- Comparison ---")
            print(f"Baseline run (no hint): Solved={solved_baseline}, Steps={stopped_depth_baseline}")
            if solved_after_hint:
                 print(f"Hint run: Solved={solved_after_hint}, Steps={stopped_depth_after_hint} (started after {stopped_depth1} initial steps)")
                 if solved_baseline and stopped_depth_after_hint < stopped_depth_baseline:
                     print("Conclusion: Hint potentially improved efficiency (fewer steps needed after hint).")
                 elif solved_baseline:
                     print("Conclusion: Hint allowed solving, but took same or more steps than baseline.")
                 else:
                     print("Conclusion: Hint allowed solving where baseline failed.")
            else:
                 print(f"Hint run: Solved={solved_after_hint}, Stopped at Depth={stopped_depth_after_hint}")
                 print("Conclusion: Hint did not lead to solution within limit.")

        else:
             print("Hint application did not yield new facts.")
             print(f"\nRun 3 Result (Hint): Failed to apply hint.")

else:
    print("Run 1 already solved the goal, skipping hint simulation.")


print("\n--- End of Script ---")
