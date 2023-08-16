# Polymorphisms, SAT based appraoch

from functools import partial
from math import factorial
from typing import Callable, Dict, Union, List, Set, Tuple
from pysat.solvers import Lingeling, Glucose3, Glucose4, Mergesat3, Minisat22
from itertools import product, combinations, permutations, chain
import time
import networkx as nx
import matplotlib.pyplot as plt
import copy
import numpy as np
from scipy import sparse
import sys
from digraph_lib import Digraph, RelationalStructure


"""
Code for the SAT-solving approach
"""



solvers = (
    "Lingeling",
    "Glucose 3",
    "Glucose 4",
    "MiniSAT 22",
    "MergeSAT 3"
)


DEFAULT_SOLVER = Lingeling


class PCSP():
    def __init__(self, G: Union[Digraph, RelationalStructure], H: Union[Digraph, RelationalStructure], solver: str = None) -> None:
        assert G.check_similar(H)
        if isinstance(G, Digraph):
            self.find_polymorphism = self.find_digraph_polymorphism 
            self.G: Digraph = Digraph.cvt2str(G)
            self.H: Digraph = Digraph.cvt2str(H)
        else:
            self.find_polymorphism = self.find_general_polymorphism
            self.G: RelationalStructure = G 
            self.H: RelationalStructure = H 
            try: 
                self.G.cvt2str()
                self.H.cvt2str()
            except:
                self.G = Digraph.cvt2str(G)
                self.H = Digraph.cvt2str(H)

        self.morphism: list = None
        self.polymorphisms = []
        self.map_vars = dict() 

        if solver is None: 
            self.solver = DEFAULT_SOLVER 
        elif solver.lower() == "lingeling":
            self.solver = Lingeling
        elif solver.lower() == "glucose 3":
            self.solver = Glucose3
        elif solver.lower() == "glucose 4":
            self.solver = Glucose4 
        elif solver.lower() == "minisat 22":
            self.solver = Minisat22 
        elif solver.lower() == "mergesat 3":
            self.solver = Mergesat3
        else:
            raise Exception
        self.solver_name = solver
        
        # Initialise various attributes to None
        self.formula = None 
        self.share = None 
        self.possible_maps = None
        self.G_domain = None 
        self.m = None  
        self.n = None 

    @staticmethod
    def print_mapping(homomorphism: dict = None, function_symbol: str ="f") -> None:
        print(", ".join(sorted([f"{function_symbol}({m})={homomorphism[m]}" for m in homomorphism])))
    
    def obtain_shared_variables(self, G_domain: List[str], H_domain: List[str], map_vars: dict, poly_func: Callable) -> dict: 
        share = dict()
        seen = set()
        for u in G_domain:
            if u not in seen:
                share[u] = u
                if (u_poly := poly_func(u)):
                    if isinstance(u_poly, str):
                        u_poly = [u_poly]
                    for u_p in u_poly:
                        if u_p not in seen: 
                            seen.add(u_p)
                            share[u_p] = u
                            for v in H_domain:
                                map_vars[(u_p, v)] = map_vars[(u, v)]
        return share

    def homomorphism_clauses(self, G_domain: List[str], H_domain: List[str], map_vars: dict, formula, share) -> None:
        l = len(H_domain)
        seen = set()

        # f(u1) = v  =>  f(u2) = v   -- i.e., clause for special polymorphisms indicating if u1 is mapped to v, then u2 must also be mapped to v
        map_implies   = lambda v, u1, u2: formula.add_clause([-map_vars[(u1, v)], map_vars[(u2, v)]])
        map_iff       = lambda v, u1, u2: (map_implies(v, u1, u2), map_implies(v, u2, u1))  # same as above but now if and only if

        # clause to ensure u (in G) is mapped to at least one vertex v of H (represents existence of mapping)
        exist_clause  = lambda u: formula.add_clause(list(map(lambda v: map_vars[(u, v)], H_domain))) 

        # clause saying: if f(u) = vi, then f(u) != vj, where vi and vj are the i-th and j-th vertices of H, respectively
        unique_clause  = lambda u, i, j: formula.add_clause(
            [-map_vars[(u, H_domain[i])], -map_vars[(u, H_domain[j])]]
        )
        unique_clauses = lambda u, i: list(map(lambda j: unique_clause(u, i, j), range(i + 1, l)))

        for u in G_domain:
            if share[u] not in seen:
                seen.add(u)
                for i in range(l):
                    unique_clauses(u, i)
                exist_clause(u)

    def relation_preservation_clauses(self, G_power: RelationalStructure, share: Dict[str, str], map_vars: Dict[Tuple[str, str], int], formula) -> None:
        """
        Clauses for ensuring the polymorphism preserves the relations of general relational structures.
        """
        for i in range(len(G_power.relations)):
            G_rel = list(G_power.relations[i])
            H_rel = self.H.relations[i]
            if len(G_rel) == 0:
                continue
            ar = len(G_rel[0])  # obtain the arity of this relation
            
            # Iterate over all possible relations of H 
            for r_H in product(*(self.H.domain for _ in range(ar))): 
                if r_H not in H_rel:
                    for r_G in G_rel:
            
                        # If r_H is not a relation in r_G, then ensure the elements of the relation r_G are not mapped precisely to those of r_H
                        formula.add_clause([-map_vars[(share[r_G[i]], r_H[i])] for i in range(ar)])
            

    def edge_preservation_clauses(self, G_vertices: List[str], H_vertices: List[str], map_vars: dict, formula, arity: int, share: dict, directed: bool = False, silent: bool = False) -> None:
        """
        Clauses for ensuring the polymorphism preserves the edges (i.e., the binary relation) of digraphs.
        Note: this function is optimised for digraphs only, not general relational structures.
        """
        # obtain clauses pertaining to structure preservation 
        G, H = self.G, self.H
        H.check_for_loop() 
        edge_prod = list(product(H_vertices, H_vertices))

        # Clause says: if vertex eg[0] in G^arity is mapped to vertex eh[0] in H, then eg[1] cannot be mapped to eh[1]
        preserve_edge     = lambda eg, eh: [-map_vars[(eg[0], eh[0])], -map_vars[(eg[1], eh[1])]]
        preserve_edge_inv = lambda eg, eh: [-map_vars[(eg[1], eh[0])], -map_vars[(eg[0], eh[1])]]

        # Treat a directed edge as an undirected edge, if necessary
        undirected_edge   = lambda edge: (min(edge), max(edge))

        # obtain the pairs of vertices of H that are not edges of H
        def isin(edge, graph):
            if directed: return True if edge in graph.edges else False
            return True if undirected_edge(edge) in graph.edges else False
        not_H_edges = [eh for eh in edge_prod if not isin(eh, H)]


        # ALTERNATIVE: obtain the vertices each vertex of H is connected to
        H_edges = {}
        for v in H_vertices: 
            H_edges[v] = []
            for u in H_vertices: 
                if (v,u) in H.edges:
                    H_edges[v].append(u)

        num_edges = len(list(H.edges)) 
        num_non_edges = len(not_H_edges)
        # print(num_edges)
        # print(num_non_edges)

        # obtain sparse matrix representation of G^arity, doing some scipy sparse matrix tricks for efficiency
        Gmat = sparse.csr_matrix(G.to_matrix().astype(np.bool_))  # store the matrix as a boolean matrix
        Gmat_ = copy.deepcopy(Gmat)
        for _ in range(arity - 1):
            Gmat_ = sparse.kron(Gmat_, Gmat)
        if not directed:
            # If we're dealing with undirected graphs, we need only the upper right half of the adjacency matrix for edges
            Gmat_ = sparse.triu(Gmat_)
        Gmat_edges = Gmat_.nonzero()
        l = len(Gmat_edges[0])
        if not silent: print(f"Obtained sparse matrix for edges of G^{arity}.")

        # construct the clauses
        seen = set()
        skipped = 0
        for i in range(l):
            Gedge = (G_vertices[Gmat_edges[0][i]], G_vertices[Gmat_edges[1][i]])
            shared_edge = (share[Gedge[0]], share[Gedge[1]])
            if not directed:
                shared_edge = undirected_edge(shared_edge)

            if not H.contains_loop:
                if shared_edge[0] == shared_edge[1]:
                    # If this is so, then there cannot be a polymorphism of the kind we want! Thus, add a contradiction and stop.
                    # (i.e., the case is that two vertices must be mapped to distinct (but connected) edges in H, yet these two vertices are the same!)
                    formula.add_clause([1])
                    formula.add_clause([-1])
                    break

            if shared_edge not in seen:
                seen.add(shared_edge)

                # Method optimised for when H has fewer edges than non edges (such as cycles)
                if num_edges < num_non_edges:
                    for v in H_vertices:
                        formula.add_clause([-map_vars[(Gedge[0], v)]] + [map_vars[(Gedge[1], u)] for u in H_edges[v]])
                        if not directed: 
                            formula.add_clause([-map_vars[(Gedge[1], v)]] + [map_vars[(Gedge[0], u)] for u in H_edges[v]])
                
                # Method optimised for when H has more edges than non edges (such as complete graphs)
                else:
                    for eh in not_H_edges:            
                        formula.add_clause(preserve_edge(Gedge, eh))
                        if not directed:
                            formula.add_clause(preserve_edge_inv(Gedge, eh))
            else:
                skipped += 1
        if not silent: print(f"Number of edge preservation clauses skipped: {skipped}")

    def reduction_to_sat(self, G=None, H=None, arity=1, special=None, verbose=False, custom_func=None, silent=False, directed=False, formula=None) -> None:

        if G is None:
            G = self.G
        if H is None:
            H = self.H

        print(f"Searching for an arity {arity} {(special is not None)*str(special)+' '}polymorphism.")

        t = time.time()
        if not silent: print("Commencing reduction.")
        formula = self.solver()

        # obtain the vertices of G^{arity} -- sorting is important (to match kronecker product of matrix later)
        if isinstance(G, Digraph):
            Gd = sorted(list(G.domain))
            G_domain = copy.deepcopy(Gd) 
            for _ in range(arity - 1):
                G_domain = list(map(",".join, product(G_domain, Gd)))
        else:
            G_power = G**arity 
            G_domain = G_power.domain

        H_domain = list(H.domain)
        n, m = len(G_domain), len(H_domain)        
        possible_maps = list(product(G_domain, H_domain))   
         
        # Variables to ensure edges in G are mapped to edges in H
        map_vars = {
            mapping: variable + 1 
            for variable, mapping in enumerate(possible_maps) 
        }

        # Variables ensuring each vertex of G is mapped to one and only one vertex in H
        if special is None: 
            share = {u: u for u in G_domain}
        else:
            special = special.lower()
            if   special == "cyclic":      poly_func = cycles_of_string
            elif special == "siggers":     poly_func = siggers_perm
            elif special == "wnu":         poly_func = wnu_strings
            elif special == "ts":          poly_func = symmetric_strings
            elif special == "olsak":       poly_func = olsak_strings
            elif special == "sub_siggers": poly_func = sub_siggers
            elif custom_func is not None:  poly_func = custom_func
            else: raise Exception(f"Unknown special polymorphism type: {special}.")

            # have polymorphism variables share mappings
            # if not silent: print(f"Initial number of unique propositional variables: {len(set(map_vars.values()))}")
            share = self.obtain_shared_variables(G_domain, H_domain, map_vars, poly_func)
            if not silent: print(f"Final number of unique propositional variables:   {len(set(map_vars.values()))}")

        self.homomorphism_clauses(G_domain, H_domain, map_vars, formula, share)
        
        if not silent: print("Obtained general mapping clauses.")
        if isinstance(G, Digraph): 
            self.edge_preservation_clauses(G_domain, H_domain, map_vars, formula, arity, share, directed, silent=silent)
        else:
            self.relation_preservation_clauses(G_power, share, map_vars, formula)

        # Obtain clauses pertaining to preservation of edges
        if not silent: print("Obtained edge/relation preservation clauses.")

        if not silent: print("The problem has been reduced to SAT; commmencing SAT solving.")
        if not silent: print(f"(Reduction took {time.time() - t:.3f} seconds.)")

        self.formula = formula 
        self.map_vars = map_vars 
        self.share = share 
        self.possible_maps = possible_maps
        self.G_domain = G_domain
        self.m = m 
        self.n = n
        return self.solve_formula(arity, verbose, silent, special)

    def solve_formula(self, arity: int = 2, verbose: bool = False, silent: bool = False, special: str = None):

        t = time.time()
        s = self.formula.solve()
        if not silent: print("The formula has been solved.")
        if not silent: print(f"(SAT solving took {time.time()-t:.3f} seconds.)")
        nt = "NOT "
        hm = "homomorphism"
        pl = "polymorphism"
        of = f" of arity {arity}"
        spec = "" if special is None else special+" "
        
        print(f"There does {(not s)*nt}exist a {spec}{pl if arity > 1 else hm}{(arity is not None)*of}.\n")
        
        if s:
            model = self.formula.get_model()
            polymorphism = dict()
            for val in model[:self.n*self.m]:
                if val > 0:
                    polymorphism[self.possible_maps[val-1][0]] = self.possible_maps[val-1][1] 

            # Ensure any variables sharing mappings are accounted for
            for u in self.G_domain:
                polymorphism[u] = polymorphism[self.share[u]]

            self.polymorphisms.append(polymorphism)
            self.morphism = polymorphism
        if verbose:
            self.print_mapping(polymorphism)     
        return s

    def print_map(self) -> None:
        if self.morphism is not None:
            self.print_mapping(self.morphism)
        else:
            raise Exception("No homomorphism or polymorphism found (yet).")

    def print_cycles(self, base: str) -> list:
        """
        Sanity check when searching for cyclic polymorphisms
        """
        if self.morphism is not None:
            if base not in self.morphism:
                raise Exception("Invalid base.")
            return [f"f({cyc})={self.morphism[cyc]}" for cyc in cycles_of_string(base)]
        else:
            raise Exception("No homomorphism or polymorphism found (yet).")

    def print_siggers(self, base: str) -> list:
        """
        Sanity check for siggers polymorphisms.
        """
        if self.morphism is not None:
            if base not in self.morphism:
                raise Exception("Invalid base.")
            base_siggers = siggers_perm(base)
            return [f"f({base})={self.morphism[base]}", f"f({base_siggers})={self.morphism[base_siggers]}"]
        else:
            raise Exception("No homomorphism or polymorphism found (yet).")

    def print_olsak(self, base: str):
        """
        Sanity check for Olšák polymorphisms 
        """
        if self.morphism is not None:
            if base not in self.morphism or not (olsak := olsak_strings(base)):
                raise Exception("Invalid base.")
            return [f"f({s})={self.morphism[s]}" for s in [base] + olsak]
        else:
            raise Exception("No homomorphism or polymorphism found (yet)")

    def print_symmetries(self, base: str) -> list:
        """
        Sanity check for ts polymorphisms
        """
        if self.morphism is not None:
            if base not in self.morphism:
                raise Exception("Invalid base.")
            return [f"f({sym})={self.morphism[sym]}" for sym in symmetric_strings(base)]

    def find_digraph_polymorphism(self, arity=2, directed=True, special=None, verbose=False, get_power=False, custom_func=None, silent=False, keep_formula: bool = False):
        # endo = self.G == self.H
        G = copy.deepcopy(self.G) 
        H = copy.deepcopy(self.H)
        self.original_vertices_G = list(Digraph.cvt2str(G).vertices)
        if get_power:
            t = time.time()
            G = G**arity
            if not silent: print(f"Time taken to obtain graph power: {time.time() - t:.3f} seconds.")
        if not directed:
            t = time.time()
            G = Digraph.cvt2undirected(G)
            H = Digraph.cvt2undirected(H)
            if not silent: print(f"Time taken to convert graphs to undirected form: {time.time() - t:.3f}")
        s = self.reduction_to_sat(G=G, H=H, arity=arity, special=special, verbose=verbose, silent=silent, directed=directed, custom_func=custom_func)
        if not keep_formula:
            del self.formula 
            self.formula = None
        if s is False:
            del self.morphism
            self.morphism = None 
        return s

    def find_general_polymorphism(self, arity=2,  directed: bool=True, special: str = None, verbose: bool = True, get_power=False, custom_func=None, silent=False, keep_formula: bool = False):
        s =  self.reduction_to_sat(G=self.G, H=self.H, arity=arity, special=special, silent=silent, custom_func=custom_func)
        if not keep_formula:
            del self.formula 
            self.formula = None
        if s is False:
            del self.morphism
            self.morphism = None 
        return s


    def collect_polymorphisms(self, arity=2, directed=True, special=None, verbose=False, get_power=False, custom_func=None, silent=False, collect_all=True) -> None: 
        self.polymorphisms = []
        s = self.find_polymorphism(arity, directed, special, verbose, get_power, custom_func, silent, keep_formula=True)
        n = 0
        while s is True:
            n += 1
            if n % 1000 == 0:
                print(f"Have found {n} polymorphisms.")

            if n == 50000:
                print("Warning: Have found 50000 polymorphisms. Are you sure you want to continue?")

            # use this quasi-diagonalisation technique to obtain a different polymorphism -- this big clause basically says the polymorphism must be different to the one just found in at least one place
            l = len(self.polymorphisms[-1])
            poly_list = list(self.polymorphisms[-1].keys())
            
            # # Original way:   -- ensure any other polymorphisms are distinct from this one
            self.formula.add_clause([-self.map_vars[u, self.polymorphisms[-1][u]] for u in self.polymorphisms[-1]]) 

            if not collect_all:
                # obtain permutations of each vertex
                in_perms = {u: ret_permutations(u) for u in poly_list}

                # ensure any more permutations differ from the one just found in at least one way, up to permutations of vertices
                num_permutations = factorial(arity)
                for _ in range(num_permutations):
                    new_clause = []
                    for i in range(l):
                        u = poly_list[i]
                        v = ','.join(next(in_perms[u]))
                        new_clause.append(-self.map_vars[v, self.polymorphisms[-1][u]])
                    self.formula.add_clause(new_clause)       

            s = self.solve_formula(arity, verbose, silent=True, special=special)
            
        print(f"Found {len(self.polymorphisms)} polymorphisms.")

    def has_homomorphism(self):
        self.reduction_to_sat(self.G, self.H, arity=1)



"""
Functions for minion homomorphisms to projections follow
"""


def get_rearrangements(set_size: int = 3, num_elems: int = 3) -> List[Tuple[int, int, int]]:
    # return all possible ordered sets of size set_size with num_elems distinct elements
    elems = list(range(num_elems))
    every_pi = list(product(*(elems for _ in range(set_size))))
    return every_pi


def rearrange(v: str, p: Tuple[int, int, int]) -> str:
    # Function for applying the rearrangements obtained in the previous function
    l = v.split(',')
    return ','.join([l[p_] for p_ in p])


def get_projections(num_elems: int = 2, arity: int = 3) -> Dict[str, int]:
    """
    Return all of the projections (up to isomorphism) of arity 'arity' over set of size 'num_elems'
    """
    projections: List[Dict[str, str]] = []
    inputs = list(map(lambda t: tuple(map(str, t)), get_rearrangements(num_elems=num_elems, set_size=arity)))
    for i in range(arity):
        # add the i projection (i.e., returns the i-th input)
        projections.append({','.join(a): a[i] for a in inputs})
    return projections


def obtain_minors(functions: List[Dict[str, str]], rearrangements: List[Tuple[int]] = None, vertices: List[str] = None, arity: int = 3) -> List[Dict[str, str]]:
    """
    Note that the minors are returned in the form of a dictionary. The dictionary keys are the indices of the functions in the input list.
    Each index is mapped to another dictionary. This dictionary maps the indices of the possible rearrangements, contained in 'pi', 
    """
    
    minors: Dict[int, Dict[int, List[int]]] = dict() # Store the minors for each function in a dictionary
    if rearrangements is None:
        rearrangements = get_rearrangements(arity, arity)
    if vertices is None:
        vertices = list(functions[0].keys())

    for f_idx, f in enumerate(functions):
        f_minors: Dict[int, List[int]] = dict()
        
        for pi_idx, pi in enumerate(rearrangements):
            for g_idx, g in enumerate(functions):
                if f_idx == g_idx:
                    continue

                indicator = True

                # Check if function is a minor of g under the rearrangement pi
                for v in vertices:
                    if f[v] != g[rearrange(v, pi)]:
                        indicator = False
                        break
                
                # If indicator is True, then f is a minor of g under pi
                if indicator:
                    if pi_idx not in f_minors:
                        f_minors[pi_idx] = [g_idx]
                    else:
                        f_minors[pi_idx].append(g_idx) 
        
        minors[f_idx] = f_minors
    
    return minors 

def general_mapping_clauses(map_from: List[int], map_to: List[int], map_vars: dict, formula) -> None:
    """
    Construct the clauses that ensure the homomorphism is indeed a valid homomorphism. This entails
    ensuring every polymorphism (map_from) is mapped to at least, and no more than, one projection (map_to).
    """
    
    len_to = len(map_to)

    # clause to ensure u (in G) is mapped to at least one vertex v of H (represents existence of mapping)
    exist_clause  = lambda u: formula.add_clause(list(map(lambda v: map_vars[(u, v)], map_to))) 

    # clause saying: if f(u) = vi, then f(u) != vj, where vi and vj are the i-th and j-th vertices of H, respectively
    unique_clause = lambda u, i, j: formula.add_clause(
        [-map_vars[(u, map_to[i])], -map_vars[(u, map_to[j])]]
    )
    unique_clauses = lambda u, i: list(map(lambda j: unique_clause(u, i, j), range(i + 1, len_to)))

    for u in map_from:            
        for i in range(len_to):
            unique_clauses(u, i)
        exist_clause(u)

    return formula


def minor_preservation_clauses(poly_indices: List[int], proj_indices: List[int], proj_minors: list, poly_minors: list, map_vars: dict, formula): 
    """
    Construct the clauses of the formula that ensure the homomorphism preserves taking minors
    """

    # Clause says: if nth polymorphism mapped to mth projection, then the pi minors of the former must be mapped to any of those of the latter
    preserve_minors = lambda poly_idx, proj_idx, pi_idx: (
        [-map_vars[(poly_idx, proj_idx)]] +                         
        [map_vars[(g, h)] for g in poly_minors[poly_idx][pi_idx] for h in proj_minors[proj_idx][pi_idx]]
    )

    for poly_idx in poly_indices:
        for proj_idx in proj_indices:
            clauses = []
            
            # Find the (indices of the) rearrangements pi under which the poly_idx-th polymorphism is a minor, check
            # whether the proj_idx-th projection is also a minor under pi, and if so ensure such minors are preserved
            # by the homomorphism
            for pi_idx in poly_minors[poly_idx]:
                if pi_idx in proj_minors[proj_idx]:
                    clauses.append(preserve_minors(poly_idx, proj_idx, pi_idx)) 
                else: 
                    # if such a minor is not present in this projection, ensure this polymorphism is not mapped to this projection
                    clauses = [[-map_vars[(poly_idx, proj_idx)]]]
                    break 
            for clause in clauses:
                formula.add_clause(clause)

    return formula 


def extract_homomorphism(formula, map_vars: dict) -> dict:
    homomorphism = {}
    model = formula.get_model()
    for var in map_vars.keys():
        if map_vars[var] in model:
            homomorphism[var[0]] = var[1]
    return homomorphism


def minion_homomorphism_to_projection(polymorphisms: List[Dict[str, str]], arity: int = 3, solver = DEFAULT_SOLVER, verbose: bool = True) -> bool: 
    """
    Search for and return, if existing, a minion homomorphism to projections for the set of polymorphisms.
    Note that the homomorphism h : N -> N will be represented by a Python dictionary from the indices of the polymorphism in 
    the list of polymorphisms to the indices of the projections in the list of projections. The list of polymorphisms is the input,
    while the list of projections will be returned along with the homomorphism itself (for the purpose of validation).
    """


    print("Constructing propositional formula.")
    t = time.time()

    print("Obtaining minors for polymorphisms.")    
    pi = get_rearrangements(set_size=arity, num_elems=arity) # pi represents all possible "minor permutations"
    vertices = list(polymorphisms[0].keys())
    poly_minors = obtain_minors(polymorphisms, pi, vertices, arity=arity)
    print("Obtained minors for polymorphisms.")

    print("Obtaining minors for 2-element-set projections.")
    proj_2 = get_projections(num_elems=2, arity=arity)
    proj_minors = obtain_minors(proj_2, pi, list(proj_2[0].keys()), arity=arity)
    print("Obtained minors for projections.")

    formula = solver()
    poly_indices = list(range(len(polymorphisms)))
    proj_indices = list(range(len(proj_minors)))

    possible_maps = list(product(poly_indices, proj_indices))
    map_vars = {mapping: i+1 for i, mapping in enumerate(possible_maps)}

    # General homomorphism clauses s.t. homomorphism rules are obeyed (i.e., functions assigned exactly one projection)
    formula = general_mapping_clauses(poly_indices, proj_indices, map_vars, formula)

    # minor preservation clauses
    formula = minor_preservation_clauses(poly_indices, proj_indices, proj_minors, poly_minors, map_vars, formula)
    
    print("Formula constructed, commencing SAT solving.")
    print(f"(Formula construction took {time.time() - t:.3f} s)")
    t = time.time()
    # SAT solving
    s = formula.solve()
    print(f"SAT solving finished. Result: homomorphism {(not s)*'not '}found.")
    if s: print("The PCSP does not satisfy any non-trivial bipartite minor condition of arity at most three, hence is NP-complete.")
    print(f"(SAT solving took {time.time() - t:.3f} s)")

    if not s:
        return s
    else:
        return s, proj_2, extract_homomorphism(formula, map_vars)
    # return s, formula, map_vars, polymorphisms, proj_2


"""
Various helper functions
"""

def CSP(G: Digraph) -> PCSP:
    return PCSP(G, G) 

def is_edge(s: str, t: str, R: Set[Tuple[str, str]], arity: int) -> bool:
    """
    Check if an edge exists between two higher dimensional vertices
    """
    ls = s.split(",")
    lt = t.split(",")
    for i in range(arity):
        if (ls[i], lt[i]) not in R:
            return False 
    return True


def cycles_of_string(s: str) -> list: 
    l = s.split(",")
    return [",".join(l[i:]+l[:i%len(l)]) for i in range(len(l))]

def is_siggers_style(s: str) -> bool:
    l = s.split(",")
    if len(l) == 6: 
        if (l[0] != l[2] or l[1] != l[4] or l[3] != l[5]) and (l[0] != l[5] or l[1] != l[3] or l[2] != l[4]):
           return False
    elif len(l) == 4:
        if (l[1] != l[2]) and (l[1] != l[3]):
            return False
    else:
        raise "Must be arity 4 or 6 for Siggers....!!!!"  
    return True     


def siggers_perm(s: str) -> str:
    l = s.split(",")
    if len(l) == 6: 
        if l[0] != l[2] or l[1] != l[4] or l[3] != l[5]:
           return False
           # raise Exception("No Siggers permutation for such a string.")
        x, y, z = l[0], l[1], l[3]
        return f"{y},{x},{z},{x},{z},{y}" 
    elif len(l) == 4:
        if l[1] != l[2]:
            return False 
        x, y, z = l[0],l[1],l[3]
        return f"{y},{x},{z},{x}"
    else:
        raise Exception("Siggers polymorphisms must be 6-ary or 4-ary.")


def sub_siggers_vertices(vertex_list: List[str]) -> List[str]:
    g = lambda l: l[0] == l[2]
    f = lambda v: g(v.split(','))
    return [v for v in vertex_list if f(v)]


def sub_siggers(s: str, z: str) -> str:
    l = s.split(',')
    x = l[0]
    y = l[1]
    return f"{y},{x},{z}"
    # return (f'{z},{y},{z}', f'{y},{x},{z}', f'{x},{z},{y}')


def wnu_strings(s: str) -> list:
    l = s.split(",")
    if len(l) == 1:
        return False
    y = l[0]
    if any(y == x for x in l[1:]):
        return False
    x = l[1]
    if any(x != x_ for x_ in l[1:]):
        return False
    return cycles_of_string(s)

def symmetric_strings(s: str) -> list:
    l = s.split(",")
    return [",".join(sym) for sym in permutations(l)]

def ret_permutations(s: str) -> permutations:
    l = s.split(",")
    return permutations(l)

def olsak_strings(s: str) -> list:
    l = s.split(",")
    if len(l) != 6:
        raise Exception("Olšák polymorphisms must be 6-ary.")
    x, y = l[0], l[2]
    if x != l[1] or x != l[5] or y != l[3] or y != l[4]:
        return False 
    return [f"{x},{y},{x},{y},{x},{y}", f"{y},{x},{x},{x},{y},{y}"]


def custom_polymorphism(identities: list, arity: int) -> list:
    """
    Function to construct a function for obtaining the strings for a custom
    polymorphism identity (use specifiable)
    """

    def get_elem_dict(lst) -> Dict[str, int]:
        i = 0
        elem_dict = {}
        for e in lst:
            if e not in elem_dict:
                elem_dict[e] = i 
                i += 1
        return elem_dict

    as_lists = list(map(lambda s: s.split(','), identities))
    elem_dict = get_elem_dict(as_lists[0])
    as_lists = list(map(lambda l: list(map(lambda e: elem_dict[e], l)), as_lists))

    def get_elem_dict_alt(l):
        ref = as_lists[0]
        this_elem_dict = {}
        for i in range(arity):
            curr = ref[i]
            if curr in this_elem_dict:
                if this_elem_dict[curr] != l[i]:
                    return False 
            else:
                this_elem_dict[curr] = l[i]
        return this_elem_dict
        

    def custom_func(s: str) -> List[str]:
        l = s.split(',')

        if len(l) != arity:
            return False

        this_elem_dict = get_elem_dict_alt(l)

        # Check the string fits the first criteria
        if this_elem_dict is False:
            return False

        # Now generate the identity strings
        l_identities = []
        for identity in as_lists[1:]:
            curr = list(map(lambda i: this_elem_dict[i], identity))
            l_identities.append(','.join(curr))
        return l_identities

    return custom_func 



if __name__ == '__main__':
    H = eval(sys.argv[1])
    G = eval(sys.argv[2])
    arity = eval(sys.argv[3])
    special = str(sys.argv[4])
    a = 5
    if special == 'custom':
        print(eval(sys.argv[5]))
        custom_func = custom_polymorphism(eval(sys.argv[5]), arity)
        print(custom_func('x,y,z'))
        a += 1
    else:
        custom_func = None

    if len(sys.argv) > a:
        directed = eval(sys.argv[a])
        if directed == 'undirected':
            directed = False 
        else:
            directed = True
    else:
        directed = False
    a += 1
    if len(sys.argv) > a:
        silent = eval(sys.argv[a])
    else:
        silent = False

    r = PCSP(H=H, G=G).find_polymorphism(arity=arity, directed=directed, special=special, get_power=False, custom_func=custom_func, silent=silent)
    


