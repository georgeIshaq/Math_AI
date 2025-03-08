import heapq

class Rule:
    """
    Represents a FOL rule.
    
    - premises: a set of atomic formulas (here, just strings) that must all be in the state.
    - conclusions: a list of possible atomic formulas that can be added (if more than one,
      the rule is disjunctive and each conclusion leads to a separate branch).
    """
    def __init__(self, premises, conclusions):
        self.premises = set(premises)
        # Ensure conclusions is a list (even if it's a single string)
        if isinstance(conclusions, list):
            self.conclusions = conclusions
        else:
            self.conclusions = [conclusions]

    def applicable(self, state):
        """Check if the rule's premises are satisfied in the current state."""
        return self.premises.issubset(state)

    def apply(self, state):
        """
        If the rule is applicable, return a list of new states,
        one for each disjunct in the conclusion.
        """
        new_states = []
        if self.applicable(state):
            for concl in self.conclusions:
                new_state = set(state)
                new_state.add(concl)
                new_states.append(frozenset(new_state))
        return new_states

    def __repr__(self):
        return f"Rule({self.premises} -> {self.conclusions})"

# Dummy heuristic function.
# For now, this just returns 0 if any goal atom is present; otherwise, 1.
# Later, you might integrate GPT-4 to produce a more nuanced value.
def heuristic(state, goal_set):
    return 0 if not goal_set.isdisjoint(state) else 1

# Placeholder for GPT-4 guidance.
# This function can be extended to make an API call to GPT-4, which can analyze 'state' and 'goal_set'
# and return a heuristic value.
def gpt4_guidance(state, goal_set):
    # For now, just defer to our dummy heuristic.
    return heuristic(state, goal_set)

def goal_test(state, goal_set):
    """Return True if the state contains at least one of the goal atoms."""
    return not goal_set.isdisjoint(state)

def a_star_search_with_goal_set(initial_state, goal_set, rules):
    """
    A* search where:
      - initial_state: a set of atomic formulas (e.g. {"A"})
      - goal_set: a set of goal atoms (e.g. {"F", "G"})
      - rules: a list of Rule objects
    """
    open_set = []
    closed_set = set()
    
    initial = frozenset(initial_state)
    # The priority is g + h; here g is the number of steps taken.
    heapq.heappush(open_set, (0 + gpt4_guidance(initial, goal_set), 0, initial, []))
    
    while open_set:
        f, g, state, path = heapq.heappop(open_set)
        
        if goal_test(state, goal_set):
            return path, state, g
        
        if state in closed_set:
            continue
        closed_set.add(state)
        
        # Try applying every rule
        for rule in rules:
            new_states = rule.apply(state)
            for new_state in new_states:
                if new_state not in closed_set:
                    new_path = path + [rule]
                    new_g = g + 1
                    h = gpt4_guidance(new_state, goal_set)
                    heapq.heappush(open_set, (new_g + h, new_g, new_state, new_path))
                    
    return None, None, None

# === Define the restricted FOL rules ===

rules = [
    Rule(["A"], "B"),       # A -> B
    Rule(["B"], "C"),       # B -> C
    Rule(["C"], ["D", "E"]),  # C -> D OR E (disjunctive rule)
    Rule(["D"], "F"),       # D -> F (goal branch)
    Rule(["E"], "G"),       # E -> G (goal branch)
    Rule(["A"], "H"),       # Irrelevant branch
    Rule(["H"], "I"),       # Irrelevant branch
    Rule(["A"], "J"),       # Irrelevant branch
    Rule(["J"], "K"),       # Irrelevant branch
]

# Define the initial state and goal.
initial_state = {"A"}
goal_set = {"F", "G"}  # Either F or G is acceptable as a goal.

# === Run the A* search ===

path, final_state, steps = a_star_search_with_goal_set(initial_state, goal_set, rules)
if path is not None:
    print("Proof found in", steps, "steps.")
    print("Final state:", final_state)
    print("Sequence of applied rules:")
    for rule in path:
        print(f"  {rule.premises} -> {rule.conclusions}")
else:
    print("No proof found.")
