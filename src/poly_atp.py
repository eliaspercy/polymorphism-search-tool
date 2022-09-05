from itertools import product, chain, permutations
import numpy as np
from typing import Callable, List
import os
import subprocess
import warnings
from copy import copy
from functools import partial
import time
from digraph_lib import Digraph

"""
Code for the implementation of the automated theorem proving approach
"""


"""
CSP Axioms follow
"""

# <<<<<<<<<< WNU AXIOMS <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<

def wnu_axiom(str1: str, str2: str, fs: str, title: str) -> str:
    """
    str1: a string of Xi's
    str2: another such string
    fs: the function symbol
    title: the clause title 
    """
    return (
        f"cnf({title},axiom,\n" +
        f"    ( {fs}({str1}) = {fs}({str2}) )).\n"
    )


def wnu_axioms(arity: int, fs: str, title_prefix: str = 'polywnu', promise: bool = False) -> str:
    """
    arity: the arity of the polymorphism
    title_prefix: the prefix to the title the clauses shall have
    """
    assert arity >= 2

    vars = ['X' for _ in range(arity-1)] + ['Y']
    cycles = list(
        map(','.join, reversed([vars[i:]+vars[:i%arity] for i in range(arity)]))
    )

    init_str = ','.join(['X' for _ in range(arity)])
    init = (
        f"cnf({title_prefix}_0,axiom,\n" +
        f"    ( {fs}({init_str}) = X )).\n"
    )
    
    axiom = lambda str1, str2, num: (
        f"cnf({title_prefix}_{num},axiom,\n" +
        f"    ( {fs}({str1}) = {fs}({str2}) )).\n"
    ) 
    return '\n'.join(
        ([init] if not promise else []) + 
        [axiom(cycles[i], cycles[i+1], i+1) for i in range(arity-1)]
    )

# <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<

# <<<<<<<<<< CYCLIC AXIOMS <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<

def cyclic_axioms(arity: int, fs: str, title_prefix: str = 'polycyclic', promise: bool = True) -> str:
    """
    arity: the arity of the polymorphism
    title_prefix: the prefix to the title the clauses shall have
    """
    assert arity >= 2

    vars = [f'X{i}' for i in range(arity)]
    cycles = list(
        map(','.join, reversed([vars[i:]+vars[:i%arity] for i in range(arity)]))
    )

    init_str = ','.join(['X' for _ in range(arity)])
    init = (
        f"cnf({title_prefix}_0,axiom,\n" +
        f"    ( {fs}({init_str}) = X )).\n"
    )
    
    axiom = lambda str1, str2, num: (
        f"cnf({title_prefix}_{num},axiom,\n" +
        f"    ( {fs}({str1}) = {fs}({str2}) )).\n"
    ) 
    return '\n'.join(
        ([init] if not promise else []) + 
        [axiom(cycles[i], cycles[i+1], i+1) for i in range(arity-1)]
    )

# <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<

# <<<<<<<<<< TS AXIOMS <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<


def ts_axioms(arity: int, fs: str, title_prefix: str = 'polyts', promise: bool = False) -> str:
    xs = [f'X{i+1}' for i in range(arity)]

    # match arity

    if arity == 3:
        perms = list(permutations(xs))
        maps = {','.join(perms[i]): ','.join(perms[0]) for i in range(1,len(perms))}
    elif arity == 4:
        maps = {}
        maps[f"{xs[1]},{xs[0]},{xs[2]},{xs[3]}"] = f"{xs[0]},{xs[1]},{xs[2]},{xs[3]}"
        maps[f"{xs[0]},{xs[2]},{xs[1]},{xs[3]}"] = f"{xs[0]},{xs[1]},{xs[2]},{xs[3]}"
        maps[f"{xs[0]},{xs[1]},{xs[3]},{xs[2]}"] = f"{xs[0]},{xs[1]},{xs[2]},{xs[3]}"
        maps[f"{xs[0]},{xs[1]},{xs[1]},{xs[2]}"] = f"{xs[0]},{xs[0]},{xs[1]},{xs[2]}"
        maps[f"{xs[0]},{xs[0]},{xs[1]},{xs[1]}"] = f"{xs[0]},{xs[0]},{xs[0]},{xs[1]}"
        maps[f"{xs[0]},{xs[1]},{xs[1]},{xs[1]}"] = f"{xs[0]},{xs[0]},{xs[0]},{xs[1]}"


    init_str = ','.join(['X1' for _ in range(arity)])
    init = (
        f"cnf({title_prefix}_0,axiom,\n" +
        f"    ( {fs}({init_str}) = X1 )).\n"
    ) 

    axiom = lambda str1, str2, num: (
        f"cnf({title_prefix}_{num},axiom,\n" +
        f"    ( {fs}({str1}) = {fs}({str2}) )).\n"
    )

    return "\n".join(
        ([init] if not promise else []) + 
        [axiom(maps[s], s, i+1) for i, s in enumerate(maps)]
    )


# <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<


def siggers_axioms(arity: int, fs: str, title_prefix: str = 'polysiggers', promise:bool=False) -> str:
    assert (arity == 4 or arity == 6)
    if arity == 4:
        vars1 = "X1,X2,X1,X3"
        vars2 = "X2,X1,X3,X2"
    elif arity == 6:
        vars1 = "X1,X2,X1,X3,X2,X3"
        vars2 = "X2,X1,X3,X1,X3,X2"

    init_str = ','.join(['X1' for _ in range(arity)])
    init = (
        f"cnf({title_prefix}_0,axiom,\n" +
        f"    ( {fs}({init_str}) = X1 )).\n"
    ) 
    axiom = (
        f"cnf({title_prefix}_1,axiom,\n" +
        f"    ( {fs}({vars1}) = {fs}({vars2}) )).\n"
    )
    return '\n'.join([init, axiom]) if not promise else axiom

# <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<

def preserves_axiom(arity: int, axiom_title: str = 'preserves', fs: str = 'f') -> str:
    """
    arity: arity of polymorphism
    axiom_title: the title/reference of the specific axiom being made 
    fs: function symbol (of the polymorphism)
    """
    notation1 = lambda i: f'X{i}'
    l1 = list(map(notation1, range(0,2*arity,2))) 
    l2 = list(map(notation1, range(1,2*arity,2)))

    notation2 = lambda x: f'~ gr({x[0]},{x[1]})'
    body = '\n    | '.join(map(notation2, zip(l1, l2)))
    former, latter = ','.join(l1), ','.join(l2)
    last = f'gr({fs}({former}),{fs}({latter}))'
    return (
        f"cnf({axiom_title},axiom,\n" +
        f"    ( {body}\n" +
        f"    | {last} )).\n"
    )   

def csp_polymorphism_axioms(arity: int, poly_type: str, fs: str = 'f') -> str:
    """
    arity: arity of polymorphism
    poly_type: the specific type of polymorphism being searched for
    fs: function symbol (of the polymorphism)
    csp: distinguish between CSP and PCSP variants
    """
    if poly_type is None:
        raise NotImplementedError
    elif poly_type == 'wnu':
        poly_axs = wnu_axioms(arity, fs)
    elif poly_type == 'ts':
        poly_axs = ts_axioms(arity, fs)
    elif poly_type == 'siggers':
        poly_axs = siggers_axioms(arity, fs)

    pres_ax = preserves_axiom(arity, fs=fs) 

    return '\n'.join([poly_axs, pres_ax])


"""
PCSP Axioms follow
"""

def promise_olsak_axioms(arity: int, fs: str = 'f', title_prefix: str = 'polyolsak') -> str:
    assert arity == 6

    axioms = (
        f"cnf({title_prefix}_1,axiom,\n" +
        f"    ( {fs}(X,X,Y,Y,Y,X) = {fs}(X,Y,X,Y,X,Y) )).\n\n" +
        f"cnf({title_prefix}_2,axiom,\n" +
        f"    ( {fs}(X,Y,X,Y,X,Y) = {fs}(Y,X,X,X,Y,Y) )).\n"
    )

    return axioms


def promise_wnu_axioms(arity: int, fs: str = 'f', title_prefix: str = 'polywnu') -> str:
    """
    arity: the arity of the polymorphism
    title_prefix: the prefix to the title the clauses shall have
    """
    assert arity >= 2

    vars = ['X' for _ in range(arity-1)] + ['Y']
    cycles = list(
        map(','.join, reversed([vars[i:]+vars[:i%arity] for i in range(arity)]))
    )
    
    axiom = lambda str1, str2, num: (
        f"cnf({title_prefix}_{num},axiom,\n" +
        f"    ( {fs}({str1}) = {fs}({str2}) )).\n"
    ) 
    return '\n'.join(
        [axiom(cycles[i], cycles[i+1], i+1) for i in range(arity-1)]
    )   


def promise_preserves_axiom(arity: int, axiom_title: str = 'preserves', fs: str = 'f') -> str:
    """
    arity: arity of polymorphism
    axiom_title: the title/reference of the specific axiom being made 
    fs: function symbol (of the polymorphism)
    """
    notation1 = lambda i: f'X{i}'
    l1 = list(map(notation1, range(0,2*arity,2))) 
    l2 = list(map(notation1, range(1,2*arity,2)))

    notation2 = lambda x: f'~ g({x[0]},{x[1]})'    # G = graph mapping comes from
    body = '\n    | '.join(map(notation2, zip(l1, l2)))
    former, latter = ','.join(l1), ','.join(l2)
    last = f'h({fs}({former}),{fs}({latter}))'     # H = graph mapping goes to
    return (
        f"cnf({axiom_title},axiom,\n" +
        f"    ( {body}\n" +
        f"    | {last} )).\n"
    )   

def pcsp_polymorphism_axioms(arity: int, poly_type: str, fs: str = 'f') -> str:
    
    if poly_type is None:
        raise NotImplementedError
    elif poly_type == 'cyclic':
        poly_axs = cyclic_axioms(arity, fs, promise=True)
    elif poly_type == 'wnu':
        poly_axs = wnu_axioms(arity, fs, promise=True)
    elif poly_type == 'siggers':
        poly_axs = siggers_axioms(arity, fs, promise=True)
    elif poly_type == 'ts':
        poly_axs = ts_axioms(arity, fs, promise=True)
    elif poly_type:
        poly_axs = promise_olsak_axioms(arity, fs)
    else:
        raise NotImplementedError

    pres_ax = promise_preserves_axiom(arity, fs=fs)

    return  '\n'.join([poly_axs, pres_ax])


"""
Graph axioms follow
"""


def node_ineq_axiom(ni: str, nj: str, title: str = None) -> str:
    """
    ni: a node
    nj: a node
    title: the title of this axiom, has a defualt
    """
    if title is None:
        title = f'elems_{ni}_{nj}'
    return (
        f"cnf({title},axiom,\n" + 
        f"    ( {ni} != {nj} )).\n"
    )


def edge_axiom(ni: str, nj: str, edge: bool, graph_name: str = 'gr', title: str = None) -> str:
    """
    ni: a node
    nj: a node
    edge: true if (ni,nj) is an edge else false
    title: the title of this axiom, has a default
    """  
    if title is None:
        title = f'{graph_name}_{ni}_{nj}'
    sign = '~ ' if not edge else ''
    return (
        f"cnf({title},axiom,\n" + 
        f"    ( {sign}{graph_name}({ni},{nj}) )).\n"
    )



def graph_axioms(H: np.ndarray, vertex_label: str = 'n', graph_name: str = 'gr') -> str:
    n = len(H)
    node_notation = lambda i: f'{vertex_label}{i}'
    nodes = list(map(node_notation, range(n)))

    i2n = {idx: node for idx, node in enumerate(nodes)}
    check = lambda i, j: True if H[i, j] == 1 else False  # indicator function
    edge_axioms = '\n'.join(
        [edge_axiom(i2n[i], i2n[j], check(i, j), graph_name)
         for i in range(0,n)
         for j in range(0,n)]
    )

    return edge_axioms, nodes

def vertex_distinctness(nodes: List[str]) -> str: 
    return '\n'.join(
        [node_ineq_axiom(nodes[i], nj)
         for i in range(len(nodes)-1)
         for nj in nodes[i+1:]]
    )


def elems_axiom(nodes: List[str], title: str = 'elems') -> str:
    """
    Define the elements that serve as the inputs to the polymorphism
    """
    # notation = lambda ni, eq: f'X {eq} {ni}'
    body = '\n    | '.join(map(lambda n: f'X {n[1]} {n[0]}', nodes))
    return (
        f"cnf({title},axiom,\n" + 
        f"    ( {body} )).\n"
    )

def maps_to_axiom(arity: int, nodes: List[str], title: str = 'maps_to', fs: str = 'f') -> str:
    """
    Determine the vertices to which the polymorphism should map (i.e., the vertices of H, not G)
    """
    inputs = ','.join([f'X{i}' for i in range(arity)]) 
    body = '\n    | '.join(map(lambda n: f'{fs}({inputs}) = {n}', nodes))
    return (
        f"cnf({title},axiom,\n" +
        f"    ( {body} )).\n"
    )


def build_formula(H: np.ndarray, arity: int, G: np.ndarray, poly_type: str,
                  filename: str, fs: str = 'f') -> None:
    assert filename[-2:] == '.p'
    
    # CSP
    if G is None:
        gr_axioms, nodes = graph_axioms(H)
        ineqs = vertex_distinctness(nodes)
        domain_axiom = elems_axiom(list(map(lambda n: (n, '='), nodes)))
        poly_axioms = csp_polymorphism_axioms(arity, poly_type, fs)

    # PCSP
    else:
        G_axioms, G_nodes = graph_axioms(G, 'v', 'g')   # '=' because the vertices of G are args to the polymorphism
        H_axioms, H_nodes = graph_axioms(H, 'v', 'h')   # '!=' because the args to poly cannot be the vertices of H 
        ineqs = vertex_distinctness(max(G_nodes, H_nodes, key=len))
        gr_axioms = '\n'.join([G_axioms, H_axioms, ineqs])
        domain_axiom = elems_axiom(list(map(lambda n: (n, '='), max(G_nodes, H_nodes, key=len))))
        this_maps_to_axiom = maps_to_axiom(arity, H_nodes, fs=fs)
        poly_axioms = pcsp_polymorphism_axioms(arity, poly_type, fs)
        poly_axioms = '\n'.join([poly_axioms, this_maps_to_axiom])

    formula = '\n'.join([poly_axioms, gr_axioms, ineqs, domain_axiom])
    with open(f'{filename}', 'w') as file:
        file.write(formula)    

build_formula_csp = partial(build_formula, G=None)



def check_formula(filename: str, 
                  command: str = 'vampire_z3_rel_master_5963',
                  options: str = '--mode casc_sat -t 300',
                  verbose: bool = False) -> bool:
    """
    filename: the name of the file containing the formula
    command: refers to the theorem prover to be used
    """
    cmd = f'{command} {options} {filename}'.split(' ')
    result = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    result = result.stdout.decode('utf-8')
    if not verbose:
        if 'status Satisfiable' in result:
            return True 
        else:
            return False
    return result
    # os.system(f'{command} {options} {filename}') 


def find_poly(H: np.ndarray, arity: int, G: np.ndarray = None, poly_type: str = None, filename: str = 'formula.p',
              command: str = 'vampire_z3_rel_master_5963', fs: str = 'f', solve: bool = False,
              delete_file: bool = True, verbose: bool = False, time_limit: str = None) -> None:
    """
    Run the whole damn thing
    """

    if isinstance(H, Digraph):
        H = copy(H).to_matrix()
    if G is not None and isinstance(G, Digraph):
        G = copy(G).to_matrix()

    print(f"Searching for a polymorphism of arity {arity} from a graph of {len(G)} vertices to a graph of {len(H)} vertices.")

    t1 = time.time()
    if G is None: #or np.array_equal(H, G):
        build_formula_csp(H=H, arity=arity, poly_type=poly_type, filename=filename, fs=fs)
    else:
        build_formula(H, arity, G, poly_type, filename, fs) 
    t2 = time.time()

    print(f"Formula constructed, see file '{filename}'.")

    if solve:
        with warnings.catch_warnings():
            result = check_formula(filename, command, verbose=verbose)
    else:
        result = f"See the file {filename} for the CNF formula in TPTP syntax."
    if delete_file:
        os.remove(f'{filename}')
    
    print(result)
    print(f"(Formula construction took {t2-t1:.3f} seconds)")


def fix_graphs(H: np.ndarray, G: np.ndarray = None) -> Callable:
    """Fix the one or two digraphs and partially apply the find_poly function"""
    def f(arity: int, poly_type: str, delete_file: bool = True, verbose: bool = False):
        return find_poly(H=H, arity=arity, G=G, poly_type=poly_type, delete_file=delete_file, verbose=verbose)
    return f

# build_formula(H=nu4, arity=4, poly_type='wnu', filename='test.p')
# print(nu4)

def print_special_polymorphisms() -> None:
    print("cyclic, weak near unanimity (wnu), totally symmetric (ts), siggers, olsak")


# build_formula(H=sea_devil, arity=5, poly_type='wnu', filename='formulas/sd_5wnu.p')
# find_poly(H=mat_pow(sea_devil, 5), arity=1, poly_type='wnu')
