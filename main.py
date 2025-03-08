import heapq
import openai
import os
import re
from dotenv import load_dotenv
from itertools import count
from collections import deque

load_dotenv()
openai.api_key = os.getenv("OPENAI_API_KEY")

class Rule:
    """Represents a restricted FOL rule with premises and possible conclusions."""
    def __init__(self, premises, conclusions):
        self.premises = set(premises)
        self.conclusions = conclusions if isinstance(conclusions, list) else [conclusions]

    def applicable(self, state):
        """Check if the rule is applicable in the current state."""
        return self.premises.issubset(state)

    def apply(self, state):
        """Apply rule and return new states."""
        if not self.applicable(state):
            return []
        return [frozenset(state | {concl}) for concl in self.conclusions]

    def __repr__(self):
        return f"Rule({self.premises} -> {self.conclusions})"

def build_rule_graph(rules):
    """Constructs a directed graph from premises to conclusions for heuristic estimation."""
    graph = {}
    for rule in rules:
        for premise in rule.premises:
            graph.setdefault(premise, []).extend(rule.conclusions)
    return graph

def bfs_heuristic(state, goal_set, rule_graph):
    """Estimate the shortest path to a goal using BFS."""
    queue = deque([(s, 0) for s in state if s in rule_graph])
    visited = set(state)

    while queue:
        node, steps = queue.popleft()
        if node in goal_set:
            return steps
        for neighbor in rule_graph.get(node, []):
            if neighbor not in visited:
                visited.add(neighbor)
                queue.append((neighbor, steps + 1))

    return float('inf')  # No path found

def gpt4_guidance(state, goal_set, rule_graph, rules):
    """
    Use GPT-4o-mini to estimate heuristic cost.
    - Includes the rule graph explicitly.
    - Penalizes dead-end states.
    - Uses a backup BFS heuristic if GPT fails.
    """
    rules_text = "\n".join(f"{list(r.premises)} -> {r.conclusions}" for r in rules)
    prompt = (
        f"The goal is to derive one of {goal_set} from the current state {set(state)}.\n"
        "You are provided with the following inference rules:\n"
        f"{rules_text}\n"
        "Estimate the minimum steps required to reach a goal.\n"
        "If the path seems blocked, return a large penalty (e.g., 100).\n"
        "Return only a number, no additional text."
    )
    
    try:
        response = openai.chat.completions.create(
            model="gpt-4o-mini",
            messages=[
                {"role": "system", "content": "You are a heuristic estimator for a guided proof search."},
                {"role": "user", "content": prompt},
            ],
            max_tokens=10,
            temperature=0.0,
        )
        content = response.choices[0].message.content.strip()
        print(f"GPT-4 Response: {content}")  # Debugging output
        
        match = re.search(r"([-+]?\d*\.\d+|\d+)", content)
        if match:
            return float(match.group(0))
        else:
            raise ValueError("No numeric value found in GPT-4 response.")
    except Exception as e:
        print(f"GPT-4 heuristic failed ({e}), falling back to BFS heuristic.")
        return bfs_heuristic(state, goal_set, rule_graph)

def goal_test(state, goal_set):
    """Check if the state satisfies the goal."""
    return not goal_set.isdisjoint(state)


def a_star_search(initial_state, goal_set, rules):
    """
    A* search with GPT-4 guidance and BFS fallback.
    """
    rule_graph = build_rule_graph(rules)
    open_set = []
    closed_set = set()
    counter = count()

    initial = frozenset(initial_state)
    heapq.heappush(open_set, (bfs_heuristic(initial, goal_set, rule_graph), 0, next(counter), initial, []))
    
    steps = 0
    while open_set:
        if steps > MAX_STEPS:
            print("Search aborted: exceeded maximum allowed steps.")
            return None, None, None
        steps += 1
        
        f, g, _, state, path = heapq.heappop(open_set)
        if goal_test(state, goal_set):
            return path, state, g
        
        if state in closed_set:
            continue
        closed_set.add(state)
        
        for rule in rules:
            for new_state in rule.apply(state):
                if new_state not in closed_set:
                    new_path = path + [rule]
                    new_g = g + 1
                    h = bfs_heuristic(new_state, goal_set, rule_graph)
                    heapq.heappush(open_set, (new_g + h, new_g, next(counter), new_state, new_path))
    
    return None, None, None

# === Define a more complex set of restricted FOL rules ===
rules = [
    Rule(["A"], "B"),
    Rule(["B"], "C"),
    Rule(["C"], ["D", "E"]),  # Disjunction: branch D vs. branch E

    # Dead-end branch from D:
    Rule(["D"], "J"),
    Rule(["J"], "K"),
    Rule(["K"], "L"),  # Dead end

    # Correct branch from E:
    Rule(["E"], "M"),
    Rule(["M"], "N"),
    Rule(["N"], "O"),
    Rule(["O"], "P"),
    Rule(["P"], "Q"),
    Rule(["Q"], "R"),
    Rule(["R"], "S"),
    Rule(["S"], "T"),
    Rule(["T"], "F"),  # Goal reached

    # Decoy branches:
    Rule(["A"], "X"),
    Rule(["X"], "Y"),
    Rule(["Y"], "Z"),  # Dead end
    Rule(["A"], "U"),
    Rule(["U"], "V"),
    Rule(["V"], "W"),  # Dead end
]

# Define the initial state and goal.
initial_state = {"A"}
goal_set = {"F"}

# === Run the A* search ===
MAX_STEPS = 10000  # Safety cutoff

path, final_state, steps = a_star_search(initial_state, goal_set, rules)
if path is not None:
    print("Proof found in", steps, "steps.")
    print("Final state:", set(final_state))
    print("Sequence of applied rules:")
    for rule in path:
        print(f"  {rule.premises} -> {rule.conclusions}")
else:
    print("No proof found.")