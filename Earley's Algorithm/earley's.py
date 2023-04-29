"""
Sa se scrie un program pentru implementarea algoritmului de analiza sintactica Earley.
Programul primeste la intrare elementele unei gramatici independente de context oarecare, inclusiv cu lambda-productii.
Programul accepta un numar oarecare de siruri peste alfabetul terminalilor.
Pentru fiecare sir se creeaza si se afiseaza tabelele Earley corespondente si
daca sirul apartine limbajului generat de gramatica,
afiseaza derivarile acelui sir plecand din simbolul de start.
"""
import itertools as I
import random

"""
Implmentat ca un program dinamic -  rezolva subprobleme mai simple
O(n^3) 
Accepta si lambda-productii
"""
START = '<start>'


def show_dot(sym, rule, pos, dotstr='.', extents=''):
    """
    Afiseaza punctul la pozitia actuala din regula.
    sym = numele neterminaluluis
    """
    extents = str(extents)
    return sym + '::= ' + ' '.join([
        str(p)
        for p in [*rule[0:pos], dotstr, *rule[pos:]]]) + extents


def is_nt(k):
    return (k[0], k[-1]) == ('<', '>')


def rem_terminals(g):
    g_cur = {}
    for k in g:
        alts = []
        for alt in g[k]:
            ts = [t for t in alt if not is_nt(t)]
            if not ts:
                alts.append(alt)
        if alts:
            g_cur[k] = alts
    return g_cur


def nullable(g):
    """
    :param g: gramatica
    :return: lista de neterminali care pot ajung lambda
    """
    nullable_keys = {k for k in g if [] in g[k]}

    unprocessed = list(nullable_keys)

    g_cur = rem_terminals(g)
    while unprocessed:
        nxt, *unprocessed = unprocessed
        g_nxt = {}
        for k in g_cur:
            g_alts = []
            for alt in g_cur[k]:
                alt_ = [t for t in alt if t != nxt]
                if not alt_:
                    nullable_keys.add(k)
                    unprocessed.append(k)
                    break
                else:
                    g_alts.append(alt_)
            if g_alts:
                g_nxt[k] = g_alts
        g_cur = g_nxt

    return nullable_keys


class O:
    """
    Clasa pentru afisarea arborilor de derivare
    """

    def __init__(self, **keys): self.__dict__.update(keys)


OPTIONS = O(V='│', H='─', L='└', J='├')


def format_node(node):
    key = node[0]
    if key and (key[0], key[-1]) == ('<', '>'): return key
    return repr(key)


def get_children(node):
    return node[1]


def display_tree(node, format_node=format_node, get_children=get_children,
                 options=OPTIONS):
    print(format_node(node))
    for line in format_tree(node, format_node, get_children, options):
        print(line)


def format_tree(node, format_node, get_children, options, prefix=''):
    children = get_children(node)
    if not children: return
    *children, last_child = children
    for child in children:
        next_prefix = prefix + options.V + '   '
        yield from format_child(child, next_prefix, format_node, get_children,
                                options, prefix, False)
    last_prefix = prefix + '    '
    yield from format_child(last_child, last_prefix, format_node, get_children,
                            options, prefix, True)


def format_child(child, next_prefix, format_node, get_children, options,
                 prefix, last):
    sep = (options.L if last else options.J)
    yield prefix + sep + options.H + ' ' + format_node(child)
    yield from format_tree(child, format_node, get_children, options, next_prefix)


format_parsetree = display_tree

def tree_to_str(tree):
    expanded = []
    to_expand = [tree]
    while to_expand:
        (key, children, *rest), *to_expand = to_expand
        if is_nt(key):
            to_expand = list(children) + list(to_expand)
        else:
            assert not children
            expanded.append(key)
    return ''.join(expanded)

class Column:
    """
    Set de stari. Fiecare coloana corespunde unui caracter/token.
    Starile unei coloane corespund expresiei parsate de dupa citirea caracterului.
    Fara stari duplicate - recursivitate stanga
    """

    def __init__(self, index, letter):
        self.index, self.letter = index, letter
        self.states = []
        self._unique = {}

    def __str__(self):
        return "%s chart[%d]\n%s" % (self.letter, self.index, "\n".join(
            str(state) for state in self.states if state.finished()))

    def to_repr(self):
        return "%s chart[%d]\n%s" % (self.letter, self.index, "\n".join(
            str(state) for state in self.states))

    def add(self, state):
        if state in self._unique:
            return self._unique[state]
        self._unique[state] = state
        self.states.append(state)
        state.e_col = self
        return self._unique[state]


class State:
    """
    Starea reprezinta un drum de parsare de la punctul curent.
    Fiecare stare are:
    @nume: neterminalul pe care aceasta regula il reprezinta
    @expr: regula care este urmata
    @punct: punctul pana la care a ajuns parsarea in regula
    @s_col: punctul de start pentru regula
    @e_col: punctul de final pentru regula
    """

    def __init__(self, name, expr, dot, s_col, e_col=None):
        self.name, self.expr, self.dot = name, expr, dot
        self.s_col, self.e_col = s_col, e_col

    def finished(self):
        return self.dot >= len(self.expr)

    def at_dot(self):
        return self.expr[self.dot] if self.dot < len(self.expr) else None

    def __str__(self):
        def idx(var):
            return var.index if var else -1

        return show_dot(self.name, self.expr, self.dot)

    def copy(self):
        return State(self.name, self.expr, self.dot, self.s_col, self.e_col)

    def _t(self):
        return self.name, self.expr, self.dot, self.s_col.index

    def __hash__(self):
        return hash(self._t())

    def __eq__(self, other):
        return self._t() == other._t()

    def advance(self):
        return State(self.name, self.expr, self.dot + 1, self.s_col)


class EarleyParser():
    """
    Parserul Earley se ocupa de labda-productii separat.
    """

    def __init__(self, grammar, log=False, parse_exceptions=True, **kwargs):
        self._grammar = grammar
        self.epsilon = nullable(grammar)
        self.log = log
        self.parse_exceptions = parse_exceptions

    def chart_parse(self, tokens, start, alts):
        chart = [self.create_column(i, tok) for i, tok in enumerate([None, *tokens])]
        for alt in alts:
            chart[0].add(self.create_state(start, tuple(alt), 0, chart[0]))
        return self.fill_chart(chart)

    def create_column(self, i, tok):
        return Column(i, tok)

    def create_state(self, sym, alt, num, col):
        return State(sym, alt, num, col)

    def predict(self, col, sym, state):
        """
        Adauga expansiunea neterminalului coloanei curente.
        Daca termenul este nullable, avansam in starea curenta si adaugam asta la coloana curenta.
        """
        for alt in self._grammar[sym]:
            col.add(self.create_state(sym, tuple(alt), 0, col))
        if sym in self.epsilon:
            col.add(state.advance())

    def scan(self, col, state, letter):
        """
        Daca starea se potriveste cu urmatorul termen, muta punctul cu o pozitie
        si adauga noua stare la coloana
        """
        if letter == col.letter:
            col.add(state.advance())

    def complete(self, col, state):
        """
        Daca s-a finalizat o regula, trebuie avansate starile care au neterminalul
        analizat in fata punctului.
        """
        parent_states = [st for st in state.s_col.states
                         if st.at_dot() == state.name]
        for st in parent_states:
            col.add(st.advance())

    def fill_chart(self, chart):
        """
        Daca punctul este la un neterminal, adaugam regulile neterminalului
        la coloana curenta.
        Daca punctul indica finalizarea analizei unui neterminal, cautam
        starile parinte si le avansam analiza.
        Daca suntem la un terminal, verificam daca starea curenta poate avansa.
        """
        for i, col in enumerate(chart):
            for state in col.states:
                if state.finished():
                    self.complete(col, state)
                else:
                    sym = state.at_dot()
                    if sym in self._grammar:
                        self.predict(col, sym, state)
                    else:
                        if i + 1 >= len(chart):
                            continue
                        self.scan(chart[i + 1], state, sym)
            if self.log:
                print(col.to_repr(), '\n')
        return chart

    def parse_prefix(self, text, start_symbol):
        alts = [tuple(alt) for alt in self._grammar[start_symbol]]
        self.table = self.chart_parse(text, start_symbol, alts)
        for col in reversed(self.table):
            states = [st for st in col.states
                      if st.name == start_symbol and st.expr in alts and st.s_col.index == 0
                      ]
            if states:
                return col.index, states
        return -1, []

    def parse_on(self, text, start_symbol):
        starts = self.recognize_on(text, start_symbol)
        forest = self.parse_forest(self.table, starts)
        for tree in self.extract_trees(forest):
            yield tree

    def recognize_on(self, text, start_symbol):
        cursor, states = self.parse_prefix(text, start_symbol)
        starts = [s for s in states if s.finished()]

        if self.parse_exceptions:
            if cursor < len(text) or not starts:
                raise SyntaxError("at " + repr(text[cursor:]))
        return starts

    def parse_paths(self, named_expr, chart, frm, til):
        def paths(state, start, k, e):
            if not e:
                return [[(state, k)]] if start == frm else []
            else:
                return [[(state, k)] + r
                        for r in self.parse_paths(e, chart, frm, start)]

        *expr, var = named_expr
        if var not in self._grammar:
            starts = ([(var, til - len(var),
                        't')] if til > 0 and chart[til].letter == var else [])
        else:
            starts = [(s, s.s_col.index, 'n') for s in chart[til].states
                      if s.finished() and s.name == var]

        return [p for s, start, k in starts for p in paths(s, start, k, expr)]

    def forest(self, s, kind, chart):
        return self.parse_forest(chart, [s]) if kind == 'n' else (s, [])

    def _parse_forest(self, chart, state):
        pathexprs = self.parse_paths(state.expr, chart, state.s_col.index,
                                     state.e_col.index) if state.expr else []
        return (state.name, [[(v, k, chart) for v, k in reversed(pathexpr)]
                             for pathexpr in pathexprs])

    def parse_forest(self, chart, states):
        names = list({s.name for s in states})
        assert len(names) == 1
        forest = [self._parse_forest(chart, state) for state in states]
        return names[0], [e for name, expr in forest for e in expr]

    def extract_a_tree(self, forest_node):
        name, paths = forest_node
        if not paths:
            return (name, [])
        return (name, [self.extract_a_tree(self.forest(*p)) for p in paths[0]])

    def extract_trees(self, forest_node):
        name, paths = forest_node
        if not paths:
            yield (name, [])
        results = []
        for path in paths:
            ptrees = [self.extract_trees(self.forest(*p)) for p in path]
            for p in I.product(*ptrees):
                yield (name, p)

class SimpleExtractor:
    """
    Acest extractor evita problema in care padurea de arbori de derivare poate fi infinita
    si incercan sa ii extragem pe toti simultan
    """
    def __init__(self, parser, text, start_symbol):
        self.parser = parser
        cursor, states = parser.parse_prefix(text, start_symbol)
        starts = [s for s in states if s.finished()]
        if cursor < len(text) or not starts:
            raise SyntaxError("at " + repr(cursor))
        self.my_forest = parser.parse_forest(parser.table, starts)

    def extract_a_node(self, forest_node):
        name, paths = forest_node
        if not paths:
            return ((name, 0, 1), []), (name, [])
        cur_path, i, l = self.choose_path(paths)
        child_nodes = []
        pos_nodes = []
        for s, kind, chart in cur_path:
            f = self.parser.forest(s, kind, chart)
            postree, ntree = self.extract_a_node(f)
            child_nodes.append(ntree)
            pos_nodes.append(postree)

        return ((name, i, l), pos_nodes), (name, child_nodes)

    def choose_path(self, arr):
        l = len(arr)
        i = random.randrange(l)
        return arr[i], i, l

    def extract_a_tree(self):
        pos_tree, parse_tree = self.extract_a_node(self.my_forest)
        return parse_tree


class ChoiceNode:
    """
    Tinem cont de arborii explorati
    """
    def __init__(self, parent, total):
        self._p, self._chosen = parent, 0
        self._total, self.next = total, None

    def chosen(self):
        assert not self.finished()
        return self._chosen

    def __str__(self):
        return '%d(%s/%s %s)' % (self._i, str(self._chosen),
                                 str(self._total), str(self.next))
    def __repr__(self):
        return repr((self._i, self._chosen, self._total))

    def increment(self):
        # as soon as we increment, next becomes invalid
        self.next = None
        self._chosen += 1
        if self.finished():
            if self._p is None:
                return None
            return self._p.increment()
        return self

    def finished(self):
        return self._chosen >= self._total


class EnhancedExtractor(SimpleExtractor):
    """
    Asigura unicitatea arborilor de derivare tinant cont de
    drumurile deja explorate
    """
    def __init__(self, parser, text, start_symbol):
        super().__init__(parser, text, start_symbol)
        self.choices = choices = ChoiceNode(None, 1)

    def choose_path(self, arr, choices):
        """
        Primeste un array si un nod ales si intoarce elementul din array
        care corespunde urmatorului nod ales (daca exista)
        """
        arr_len = len(arr)
        if choices.next is not None:
            if choices.next.finished():
                return None, None, None, choices.next
        else:
            choices.next = ChoiceNode(choices, arr_len)
        next_choice = choices.next.chosen()
        choices = choices.next
        return arr[next_choice], next_choice, arr_len, choices


    def extract_a_node(self, forest_node, seen, choices):
        name, paths = forest_node
        if not paths:
            return (name, []), choices

        cur_path, _i, _l, new_choices = self.choose_path(paths, choices)
        if cur_path is None:
            return None, new_choices
        child_nodes = []
        for s, kind, chart in cur_path:
            if kind == 't':
                child_nodes.append((s, []))
                continue
            nid = (s.name, s.s_col.index, s.e_col.index)
            if nid in seen:
                return None, new_choices
            f = self.parser.forest(s, kind, chart)
            ntree, newer_choices = self.extract_a_node(f, seen | {nid}, new_choices)
            if ntree is None:
                return None, newer_choices
            child_nodes.append(ntree)
            new_choices = newer_choices
        return (name, child_nodes), new_choices

    def extract_a_tree(self):
        while not self.choices.finished():
            parse_tree, choices = self.extract_a_node(self.my_forest, set(), self.choices)
            choices.increment()
            if parse_tree is not None:
                return parse_tree
        return None


if __name__ == '__main__':
    grammar = {
        '<start>': [['<expr>']],
        '<expr>': [
            ['<term>', '+', '<expr>'],
            ['<term>', '-', '<expr>'],
            ['<term>']],
        '<term>': [
            ['<fact>', '*', '<term>'],
            ['<fact>', '/', '<term>'],
            ['<fact>']],
        '<fact>': [
            ['<digits>'],
            ['(', '<expr>', ')']],
        '<digits>': [
            ['<digit>', '<digits>'],
            ['<digit>']],
        '<digit>': [["%s" % str(i)] for i in range(10)],
    }
    # aceeași ca mai sus, dar ambigua
    a_grammar = {
        '<start>': [['<expr>']],
        '<expr>': [
            ['<expr>', '+', '<expr>'],
            ['<expr>', '-', '<expr>'],
            ['<expr>', '*', '<expr>'],
            ['<expr>', '/', '<expr>'],
            ['(', '<expr>', ')'],
            ['<integer>']],
        '<integer>': [
            ['<digits>']],
        '<digits>': [
            ['<digit>', '<digits>'],
            ['<digit>']],
        '<digit>': [["%s" % str(i)] for i in range(10)],
    }

    sample_grammar = {
        '<start>': [['<A>', '<B>']],
        '<A>': [['a', '<B>', 'c'], ['a', '<A>']],
        '<B>': [['b', '<C>'], ['<D>']],
        '<C>': [['c']],
        '<D>': [['d']]
    }

    # nt_name = '<B>'
    # nt_expr = tuple(sample_grammar[nt_name][1])
    # col_0 = Column(0, None)
    # a_state = State(nt_name, tuple(nt_expr), 0, col_0)
    # # print(a_state.at_dot())
    # b_state = a_state.advance()
    # # print(b_state)
    # # print(b_state.finished())

    """EXAMPLE NULLABLE"""
    nullable_grammar = {
        '<start>': [['<A>', '<B>']],
        '<A>': [['a'], [], ['<C>']],
        '<B>': [['b']],
        '<C>': [['<A>'], ['<B>']]
    }
    # print(nullable(nullable_grammar))


    """IMPORTANT! EXEMPLE PARSARE EARLEY + AFISEAZA TABELUL"""
    # ep = EarleyParser(sample_grammar)
    # ep.fill_chart = lambda s: s
    #
    # v = ep.chart_parse(list('a'), START, sample_grammar[START])
    # print(v[0].states[0])
    #
    # ep = EarleyParser(sample_grammar)
    # ep.fill_chart = lambda s: s
    #
    # chart = ep.chart_parse(list('a'), START, sample_grammar[START])
    #
    # for s in chart[0].states:
    #     print(s)
    #
    # ep.predict(chart[0], '<A>', s)
    # for s in chart[0].states:
    #     print(s)
    #
    # ep = EarleyParser(sample_grammar)
    # ep.fill_chart = lambda s: s
    #
    # chart = ep.chart_parse(list('a'), START, sample_grammar[START])
    # ep.predict(chart[0], '<A>', s)
    #
    # new_state = chart[0].states[1]
    # print(new_state)
    #
    # ep.scan(chart[1], new_state, 'a')
    # for s in chart[1].states:
    #     print(s)
    #
    # ep = EarleyParser(sample_grammar)
    # ep.fill_chart = lambda s: s
    #
    # chart = ep.chart_parse(list('ad'), START, sample_grammar[START])
    # ep.predict(chart[0], '<A>', s)
    # for s in chart[0].states:
    #     print(s)
    # print(chart[1].letter)
    # for state in chart[0].states:
    #     if state.at_dot() not in sample_grammar:
    #         ep.scan(chart[1], state, 'a')
    # for s in chart[1].states:
    #     print(s)
    #
    # for state in chart[1].states:
    #     if state.at_dot() in sample_grammar:
    #         ep.predict(chart[1], state.at_dot(), state)
    # for s in chart[1].states:
    #     print(s)
    # print(chart[2])
    # for state in chart[1].states:
    #     if state.at_dot() not in sample_grammar:
    #         ep.scan(chart[2], state, state.at_dot())
    #
    # for s in chart[2].states:
    #     print(s)
    #
    # for state in chart[2].states:
    #     if state.finished():
    #         ep.complete(chart[2], state)
    #
    # for s in chart[2].states:
    #     print(s)
    #
    # ep = EarleyParser(sample_grammar, log=True)
    # columns = ep.chart_parse('adcd', START, sample_grammar[START])
    # for c in columns: print(c)
    # last_col = columns[-1]
    # for s in last_col.states:
    #     if s.name == '<start>':
    #         print(s)

    # print("DERIVARI")
    # ep = EarleyParser(sample_grammar)
    # cursor, last_states = ep.parse_prefix('adcd', START)
    # print(cursor, [str(s) for s in last_states])
    # print(sample_grammar[START])
    # ep = EarleyParser(sample_grammar)
    # completed_start = last_states[0]
    # paths = ep.parse_paths(completed_start.expr, columns, 0, 4)
    # for path in paths:
    #     print([list(str(s_) for s_ in s) for s in path])
    #
    # ep = EarleyParser(sample_grammar)
    # result = ep.parse_forest(columns, last_states)
    # print(result)

    """Exemple Arbori de Derivare"""
    tree = ('<start>', [('<expr>', [('<expr>', [('<expr>', [('<integer>', [('<digits>', [('<digit>', [('1', [])])])])]),
                                                ('+', []), ('<expr>', [
            ('<integer>', [('<digits>', [('<digit>', [('2', [])])])])])]), ('+', []),
                                    ('<expr>', [('<integer>', [('<digits>', [('<digit>', [('4', [])])])])])])])
    # print(format_parsetree(tree))
    #
    # mystring = '1+2+4'
    # parser = EarleyParser(a_grammar)
    # for tree in parser.parse_on(mystring, START):
    #     print(format_parsetree(tree))

    # Almost infinite parse trees
    directly_self_referring = {
        '<start>': [['<query>']],
        '<query>': [['<expr>']],
        "<expr>": [["<expr>"], ['a']],
    }

    indirectly_self_referring = {
        '<start>': [['<query>']],
        '<query>': [['<expr>']],
        '<expr>': [['<aexpr>'], ['a']],
        '<aexpr>': [['<expr>']],
    }

    """EXEMPLE ARBORI INFINITI"""
    # mystring = 'a'
    # for grammar in [directly_self_referring, indirectly_self_referring]:
    #     ep = EarleyParser(grammar)
    #     forest = ep.parse_on(mystring, START)
    #     print('recognized', mystring)
    #     try:
    #         for tree in forest:
    #             print(tree)
    #     except RecursionError as e:
    #         print("Recursion error", e)
    #
    # de = SimpleExtractor(EarleyParser(directly_self_referring), mystring, START)
    # for i in range(5):
    #     tree = de.extract_a_tree()
    #     print(tree_to_str(tree))
    #     print(format_parsetree(tree))
    #
    # ie = SimpleExtractor(EarleyParser(indirectly_self_referring), mystring, START)
    # for i in range(5):
    #     tree = ie.extract_a_tree()
    #     print(tree_to_str(tree))
    #     print(format_parsetree(tree))

    """IMPORTANT! AFISAREA ARBORILOR DE DERIVARE"""
    print("Enhanced extractor example")
    mystring = 'a'
    ee = EnhancedExtractor(EarleyParser(indirectly_self_referring), mystring, START)
    i = 0
    while True:
        i += 1
        t = ee.extract_a_tree()
        if t is None: break
        s = tree_to_str(t)
        assert s == mystring
        print(tree_to_str(tree))
        print(format_parsetree(tree))