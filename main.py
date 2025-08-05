import re
from collections import defaultdict, deque
import copy

# ======== Classe da Gramática ========

class CFG:
    def __init__(self):
        self.productions = defaultdict(list)
        self.start_symbol = None

    def read_from_file(self, filename):
        with open(filename, 'r') as file:
            for line in file:
                if '->' in line:
                    head, body = map(str.strip, line.strip().split('->'))
                    if not self.start_symbol:
                        self.start_symbol = head
                    for prod in body.split('|'):
                        self.productions[head].append(prod.strip())

    def display(self, title="Gramática"):
        print(f"\n=== {title} ===")
        for head, bodies in self.productions.items():
            print(f"{head} -> {' | '.join(bodies)}")

    def copy(self):
        new_cfg = CFG()
        new_cfg.start_symbol = self.start_symbol
        new_cfg.productions = copy.deepcopy(self.productions)
        return new_cfg


# ======== Simplificação ========

def remove_unreachable(cfg):
    reachable = set()
    agenda = deque([cfg.start_symbol])
    while agenda:
        symbol = agenda.popleft()
        if symbol not in reachable:
            reachable.add(symbol)
            for production in cfg.productions[symbol]:
                for char in production:
                    if char.isupper():
                        agenda.append(char)
    cfg.productions = {k: v for k, v in cfg.productions.items() if k in reachable}

def remove_nonproductive(cfg):
    productive = set()
    changed = True
    while changed:
        changed = False
        for head, bodies in cfg.productions.items():
            for body in bodies:
                if all(c.islower() or c in productive for c in body):
                    if head not in productive:
                        productive.add(head)
                        changed = True
    cfg.productions = {k: [b for b in v if all(c.islower() or c in productive for c in b)]
                       for k, v in cfg.productions.items() if k in productive}

def remove_epsilon_productions(cfg):
    nullable = set()
    changed = True
    while changed:
        changed = False
        for head, bodies in cfg.productions.items():
            for body in bodies:
                if body == '' or all(c in nullable for c in body):
                    if head not in nullable:
                        nullable.add(head)
                        changed = True
    new_productions = defaultdict(set)
    for head, bodies in cfg.productions.items():
        for body in bodies:
            positions = [i for i, c in enumerate(body) if c in nullable]
            n = len(positions)
            for i in range(1 << n):
                new_body = list(body)
                for j in range(n):
                    if (i >> j) & 1:
                        new_body[positions[j]] = ''
                candidate = ''.join([c for c in new_body if c != ''])
                new_productions[head].add(candidate)
    cfg.productions = {k: list(v - {''}) for k, v in new_productions.items()}

def remove_unit_productions(cfg):
    unit_pairs = set()
    for head, bodies in cfg.productions.items():
        for body in bodies:
            if len(body) == 1 and body.isupper():
                unit_pairs.add((head, body))
    while True:
        new_pairs = unit_pairs.copy()
        for (a, b) in unit_pairs:
            for (c, d) in unit_pairs:
                if b == c:
                    new_pairs.add((a, d))
        if new_pairs == unit_pairs:
            break
        unit_pairs = new_pairs
    new_productions = defaultdict(list)
    for head, bodies in cfg.productions.items():
        for body in bodies:
            if not (len(body) == 1 and body.isupper()):
                new_productions[head].append(body)
    for (a, b) in unit_pairs:
        for prod in cfg.productions[b]:
            if not (len(prod) == 1 and prod.isupper()):
                new_productions[a].append(prod)
    cfg.productions = new_productions


# ======== Forma Normal de Chomsky ========

def chomsky_normal_form(cfg):
    cfg = cfg.copy()
    new_cfg = CFG()
    new_cfg.start_symbol = cfg.start_symbol

    term_map = {}
    new_var_count = 1

    # Substituir terminais em produções longas
    for head, bodies in cfg.productions.items():
        for body in bodies:
            if len(body) > 1:
                new_body = ''
                for symbol in body:
                    if symbol.islower():
                        if symbol not in term_map:
                            term_var = f"T{new_var_count}"
                            term_map[symbol] = term_var
                            new_cfg.productions[term_var].append(symbol)
                            new_var_count += 1
                        new_body += term_map[symbol]
                    else:
                        new_body += symbol
                new_cfg.productions[head].append(new_body)
            else:
                new_cfg.productions[head].append(body)

    # Quebrar produções longas
    updated = defaultdict(list)
    counter = 1
    for head, bodies in new_cfg.productions.items():
        for body in bodies:
            if len(body) <= 2:
                updated[head].append(body)
            else:
                prev = head
                for i in range(len(body) - 2):
                    new_var = f"X{counter}"
                    updated[prev].append(body[i] + new_var)
                    prev = new_var
                    counter += 1
                updated[prev].append(body[-2:])
    new_cfg.productions = updated
    return new_cfg


# ======== Forma Normal de Greibach (Simplificada) ========

def greibach_normal_form(cfg):
    cfg = chomsky_normal_form(cfg)
    new_cfg = CFG()
    new_cfg.start_symbol = cfg.start_symbol
    for head, bodies in cfg.productions.items():
        for body in bodies:
            if body[0].islower():
                new_cfg.productions[head].append(body)
            elif body[0].isupper() and len(body) > 1:
                for prod in cfg.productions[body[0]]:
                    new_cfg.productions[head].append(prod + body[1:])
    return new_cfg


# ======== Melhorias ========

def left_factoring(cfg):
    new_cfg = CFG()
    new_cfg.start_symbol = cfg.start_symbol
    counter = 1
    for head, bodies in cfg.productions.items():
        prefix_map = defaultdict(list)
        for body in bodies:
            if body:
                prefix_map[body[0]].append(body)
        for prefix, group in prefix_map.items():
            if len(group) == 1:
                new_cfg.productions[head].append(group[0])
            else:
                new_nonterm = f"{head}'{counter}"
                counter += 1
                new_cfg.productions[head].append(prefix + new_nonterm)
                for alt in group:
                    suffix = alt[1:] if len(alt) > 1 else ''
                    new_cfg.productions[new_nonterm].append(suffix)
    cfg.productions = new_cfg.productions

def remove_left_recursion(cfg):
    nonterminals = list(cfg.productions.keys())
    new_productions = defaultdict(list)
    for Ai in nonterminals:
        alpha = []
        beta = []
        for prod in cfg.productions[Ai]:
            if prod.startswith(Ai):
                alpha.append(prod[1:])
            else:
                beta.append(prod)
        if alpha:
            Ai_prime = Ai + "'"
            for b in beta:
                new_productions[Ai].append(b + Ai_prime)
            for a in alpha:
                new_productions[Ai_prime].append(a + Ai_prime)
            new_productions[Ai_prime].append('')
        else:
            new_productions[Ai] = cfg.productions[Ai]
    cfg.productions = new_productions


# ======== Execução Principal ========

if __name__ == "__main__":
    cfg = CFG()
    cfg.read_from_file("gramatica.txt")
    cfg.display("Gramática Original")

    remove_unreachable(cfg)
    remove_nonproductive(cfg)
    cfg.display("Após remover símbolos inúteis/inalcançáveis")

    remove_epsilon_productions(cfg)
    cfg.display("Após remover produções vazias (ε)")

    remove_unit_productions(cfg)
    cfg.display("Após substituição de produções unitárias")

    cfg_chomsky = chomsky_normal_form(cfg)
    cfg_chomsky.display("Forma Normal de Chomsky")

    cfg_greibach = greibach_normal_form(cfg)
    cfg_greibach.display("Forma Normal de Greibach (simplificada)")

    left_factoring(cfg)
    cfg.display("Após fatoração à esquerda")

    remove_left_recursion(cfg)
    cfg.display("Após remoção de recursão à esquerda")
