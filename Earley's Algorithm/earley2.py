"""
Sa se scrie un program pentru implementarea algoritmului de analiza sintactica Earley.
Programul primeste la intrare elementele unei gramatici independente de context oarecare, inclusiv cu lambda-productii.
Programul accepta un numar oarecare de siruri peste alfabetul terminalilor.
Pentru fiecare sir se creeaza si se afiseaza tabelele Earley corespondente si
daca sirul apartine limbajului generat de gramatica,
afiseaza derivarile acelui sir plecand din simbolul de start.
"""

from typing import List, Set
import sys

class Production:
    def __init__(self, *components):
        self.components = components

    def __len__(self):
        return len(self.components)

    def __getitem__(self, index):
        return self.components[index]

    def __iter__(self):
        return iter(self.components)

    def __hash__(self):
        return hash(self.components)
    
    def __str__(self) -> str:
        return " ".join(str(comp) for comp in self.components)


class Rule(object):
    def __init__(self, name, *productions):
        self.name = name
        self.productions = list(productions)

    def __str__(self):
        return self.name

    def add(self, *productions):
        self.productions.extend(productions)


class State(object):
    finish_idx: int | None
    origin_idx: int

    def __init__(self, name, production, dot_index, origin_idx: int):
        self.name = name
        self.production = production
        self.origin_idx = origin_idx
        self.finish_idx = None
        self.dot_index = dot_index
        self.rules = [t for t in production if isinstance(t, Rule)]

    def __repr__(self):
        terms = [str(p) for p in self.production]
        terms.insert(self.dot_index, u"$")
        return "%-5s -> %-16s [%s-%s]" % (self.name, " ".join(terms), self.origin_idx, self.finish_idx)

    def __eq__(self, other: 'State'):
        return (self.name, self.production, self.dot_index, self.origin_idx) == \
            (other.name, other.production, other.dot_index, other.origin_idx)

    def __ne__(self, other):
        return not (self == other)

    def __hash__(self):
        return hash((self.name, self.production))

    def is_completed(self):
        return self.dot_index >= len(self.production)

    def get_next_component(self) -> str | None:
        if self.is_completed():
            return None
        return self.production[self.dot_index]


class Node(object):
    def __init__(self, value, children):
        self.value = value
        self.children = children

    def print(self, level=0):
        print("  " * level + str(self.value))
        for child in self.children:
            child.print(level + 1)


EarleyStates = List[List[State]]


class EarleyParser:
    START_RULE = "@P"

    # Avem nevoie separat de `List` si `Set` pentru ca se arunca o eroare in momentul
    # in care se itereaza printr un set si acestuia i se adauga noi elemente
    # din loop body.
    states_set: List[Set[State]]
    states: EarleyStates

    root_rule: Rule

    def __init__(self, root_rule: Rule) -> None:
        self.root_rule = root_rule

    def _predict(self, word_idx: int, rule: Rule):
        for prod in rule.productions:
            new_state = State(rule.name, prod, 0, word_idx)
            if new_state in self.states_set[word_idx]:
                continue

            self.states_set[word_idx].add(new_state)
            self.states[word_idx].append(new_state)
            new_state.finish_idx = word_idx

    def _scan(self, word_idx: int, ch: str, state: State, prediction_str: str | None):
        if prediction_str != ch:
            return
        new_state = State(state.name, state.production,
                          state.dot_index + 1, state.origin_idx)
        if new_state in self.states_set[word_idx]:
            return

        self.states_set[word_idx].add(new_state)
        self.states[word_idx].append(new_state)
        new_state.finish_idx = word_idx

    def _complete(self, word_idx: int, state: State):
        if not state.is_completed():
            return
        for st in self.states[state.origin_idx]:
            term = st.get_next_component()
            if not isinstance(term, Rule):
                continue
            if term.name == state.name:
                new_state = State(st.name, st.production,
                                  st.dot_index + 1, st.origin_idx)
                if new_state in self.states_set[word_idx]:
                    return

                self.states_set[word_idx].add(new_state)
                self.states[word_idx].append(new_state)
                new_state.finish_idx = word_idx

    def parse(self, raw_words: str):
        words = raw_words.strip().lower().split()
        words_len = len(words)

        self.states_set = [set() for i in range(0, words_len + 1)]
        self.states = [list() for i in range(0, words_len + 1)]

        # Adaugam `P -> S.`.
        start_state = State(self.START_RULE, Production(self.root_rule), 0, 0)
        self.states_set[0].add(start_state)
        self.states[0].append(start_state)

        for i in range(0, words_len + 1):
            for state in self.states[i]:
                if state.is_completed():
                    self._complete(i, state)
                else:
                    term = state.get_next_component()
                    if isinstance(term, Rule):
                        self._predict(i, term)
                    elif i + 1 < words_len + 1:
                        self._scan(i + 1, words[i], state, term)

        for st in self.states[-1]:
            if st.name == self.START_RULE and st.is_completed():
                return st
        else:
            raise Exception("An error occurred while parsing.")

    def get_derivation_trees(self, root_state: State):
        return self._get_derivation_trees_helper([], root_state, len(root_state.rules) - 1, root_state.finish_idx)

    def _get_derivation_trees_helper(self, children, start_state: State, rule_index, finish_idx):
        if rule_index < 0:
            return [Node(start_state, children)]

        rule = start_state.rules[rule_index]
        results = []

        for state in self.states[finish_idx]:
            if state is start_state:
                break
            if not state.is_completed() or state.name != rule.name:
                continue
            for sub_tree in self.get_derivation_trees(state):
                for node in self._get_derivation_trees_helper([sub_tree] + children, start_state, rule_index - 1, state.origin_idx):
                    results.append(node)
        return results


def print_states(states: EarleyStates):
    states_len = len(states)
    for state_idx in range(0, states_len):
        print("S({}): ".format(state_idx))

        for state_value_idx, state_value in enumerate(states[state_idx]):
            print(
                "{}: production={}, origin_state_idx={}, finish_state_idx:{}".format(
                    state_value_idx, state_value.production, state_value.origin_idx, state_value.finish_idx
                )
            )
        print("=" * 30)


if __name__ == '__main__':
    NUMBER = Rule(
        "NUMBER",
        Production("1"), Production("2"), Production("3"), Production("4")
    )

    # Le definim si pe acestea pt ca ele vor reprezenta noduri atunci cand se va afisa
    # arborele cu derivarile.
    PLUS = Rule("+", Production("+"))
    MULTIPLY = Rule("*", Production("*"))

    M = Rule("M")
    M.add(Production(M, MULTIPLY, NUMBER), Production(NUMBER))

    S = Rule("S")
    S.add(Production(S, PLUS, M), Production(M))

    words = "2 + 3 * 4"
    # words = "2 + 3 * 4 + 1"
    # words = "1 + 2 + 3 * 4"
    # words = "2 + 3 * 4 * 1"

    parser = EarleyParser(S)

    for raw_words in sys.stdin:
        words = raw_words.strip()
        if not len(words):
            break

        try:
            parser_root_rule = parser.parse(words)

            print('The string is accepted by the grammar:')
            forest = parser.get_derivation_trees(parser_root_rule)
            forest[0].print()
        except:
            print('The string is not accepted by the grammar.')
        finally:
            print("\nThe states table:")
            print_states(parser.states)
        

