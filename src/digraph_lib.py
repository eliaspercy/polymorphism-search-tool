import math
import networkx as nx 
import numpy as np
from typing import List, Set, Tuple, Union
from itertools import chain, product
from copy import copy
import random

"""
Classes for defining relational structures, and digraphs in particular, together with various helper functions for handling them.
"""


class RelationalStructure:
    def __init__(self, domain: List[str], relations: List[Set[Tuple[str, ...]]]) -> None: 
        self.domain = domain 
        self.relations = relations 
    
    def cvt2str(self) -> None:
        to_str = lambda lst: list(map(str, lst))
        self.domain = to_str(self.domain)
        self.relations = [set(map(lambda x: tuple(to_str(x)), R)) for R in self.relations]

    def check_similar(self, other: 'RelationalStructure') -> bool:
        
        # Check number of relations is the same
        if len(self.relations) != len(other.relations):
            return False

        # Check all relations are of the same arity 
        for R, S in zip(self.relations, other.relations):
            R_lst, S_lst = list(R), list(S)            
            if len(R_lst) != 0 and len(S_lst) != 0 and len(R_lst[0]) != len(S_lst[0]):
                return False 

        return True 

    def __repr__(self) -> str:
        return f"Relational Structure with domain size of {len(self.domain)} and {len(self.relations)} relations."

    def __str__(self) -> str:
         return f"RelationalStructure(\n"         \
                f"    Domain={self.domain},\n"     \
                f"    Relations={self.relations}\n" \
                f")"     

    def __mul__(self, other: 'RelationalStructure') -> 'RelationalStructure':
        # Obtain the direct product of two similar relational structures        

        assert self.check_similar(other)

        join_rel = lambda r1, r2: tuple(r1[i] + ',' + r2[i] for i in range(len(r1)))
        mult_rel = lambda R1, R2: set([join_rel(r1, r2) for r2 in list(R1) for r1 in list(R2)])

        return RelationalStructure(
            domain=list(map(",".join, product(self.domain, other.domain))),
            relations=[mult_rel(R1, R2) for R1, R2 in zip(self.relations, other.relations)] 
        )

    def __pow__(self, p: int) -> 'RelationalStructure':
        if p < 1: raise "Not valid!"
        H = RelationalStructure(domain=self.domain, relations=self.relations) 
        for _ in range(p-1): H *= self
        return H   
    

class Digraph(RelationalStructure):
    def __init__(self, vertices: List[str], edges: Set[Tuple[str, str]], directed: bool = True) -> None:
        self.vertices = vertices
        self.edges = edges
        self.directed = directed
        self.contains_loop = False

        self.domain = vertices
        self.relations = [edges]

    def check_similar(self, other: 'RelationalStructure') -> bool: 
        return isinstance(other, Digraph)

    def __repr__(self) -> str:
        return f"Digraph with {len(self.vertices)} vertices and {len(self.edges)} edges."

    def __str__(self) -> str:
         return f"Digraph(\n"                     \
                f"    vertices={self.vertices},\n" \
                f"    edges={self.edges}\n"         \
                f")"     

    def __mul__(self, other: 'Digraph') -> 'Digraph':
        if self.directed and other.directed:
            return Digraph(
                vertices=list(map(",".join, product(self.vertices, other.vertices))),
                edges=set(
                    (self_edge[0] + "," + other_edge[0], self_edge[1] + "," + other_edge[1]) 
                    for other_edge in other.edges for self_edge in self.edges
                )
            )

        elif self.directed != other.directed:
            raise Exception("Cannot multiply directed with undirected graphs!")

        def check(u, v):
            return (
                (v[:n],u[:n]) in self.edges and (v[n:],u[n:]) in other.edges or
                (v[:n],u[:n]) in self.edges and (u[n:],v[n:]) in other.edges or
                (u[:n],v[:n]) in self.edges and (v[n:],u[n:]) in other.edges or
                (u[:n],v[:n]) in self.edges and (u[n:],v[n:]) in other.edges
            )

        n = len(list(self.vertices)[0])
        new_vertices = list(map(",".join, product(self.vertices, other.vertices)))
        new_edges = [(min(v,u),max(v,u)) for v in new_vertices for u in new_vertices if check(u,v)] 
 
        return Digraph(
            vertices=set(new_vertices),
            edges=set(new_edges),
            directed=False
        )


    def __pow__(self, p: int) -> 'Digraph':
        if p < 1: raise "Not valid!"
        H = Digraph(vertices=self.vertices, edges=self.edges, directed=self.directed) 
        for _ in range(p-1): H*=self
        return H   
    
    def __eq__(self, other: 'Digraph') -> bool:
        return True if self.vertices == other.vertices and self.edges == other.edges else False

    def to_matrix(self, aslist: bool = False) -> Union[np.ndarray, List[List[int]]]:

        # important for the vertices to be sorted in this instance, for when handling direct product of lists of vertices
        vertices = sorted(list(self.vertices), key=int)
        vertex_numbering = {idx: vertex for idx, vertex in enumerate(vertices)}
        n = len(self.vertices)
        matrix = np.zeros((n,n), dtype=np.int8)
        for i in range(n):
            for j in range(n):
                if (vertex_numbering[i], vertex_numbering[j]) in self.edges:
                    matrix[i, j] = 1
                    if not self.directed:
                        matrix[j, i] = 1   # symmetry, s.t. works for undirected graphs too
        return matrix if not aslist else matrix.tolist()

    def check_for_loop(self) -> None:
        self.contains_loop = any((v, v) in self.edges for v in self.vertices)

    @staticmethod 
    def from_matrix(mat: np.ndarray) -> 'Digraph':
        n = mat.shape[0]
        vertices = [str(i) for i in range(1, n+1)]
        edges = []
        for i in range(n):
            for j in range(n):
                if mat[i][j] == 1:
                    edges.append((vertices[i], vertices[j]))
        return Digraph(
            vertices=list(vertices),
            edges=set(edges)
        )

    @staticmethod    
    def cvt2str(G: 'Digraph') -> 'Digraph':
        return Digraph(
            vertices=list(map(str, list(G.vertices))),
            edges=set(map(lambda e: (str(e[0]), str(e[1])), list(G.edges)))
        )

    @staticmethod
    def cvt2undirected(G: 'Digraph') -> 'Digraph':
        return Digraph(
            vertices=G.vertices,
            edges=set((min(e), max(e)) for e in G.edges),
            directed=False
        )

    @staticmethod
    def random_graph(num_vertices: int, num_edges: int = None, edge_prob: float = 0.5, allow_loops: bool = False) -> 'Digraph':
        """
        An algorithm for random generating graphs, partly based on the Erdos-Renyi model
        """
        # randomly order list of 0 to n-1
        # go thru in two for-loops, and based on edge prob add an edge (ignoring loops if specified)
        # if num_edges reached, end
        # else, if num_edges not reached, restart

        if num_vertices < 1:
            raise ValueError
    
        if num_edges is None:
            num_edges = math.inf 
        else:
            if num_edges < 0:
                raise ValueError

            if num_edges > pow(num_vertices, 2) - num_vertices:
                print("Too many edges for this many vertices.\n")
                return False 

        adj_matrix = np.zeros(shape=(num_vertices, num_vertices))
        rows = list(range(num_vertices))
        cols = list(range(num_vertices))
        random.shuffle(rows)
        random.shuffle(cols)
        edges = 0
        while edges < num_edges:
            for i in rows: 
                for j in cols:
                    if edges < num_edges:
                        if i != j or allow_loops:
                            if adj_matrix[i, j] == 0 and random.random() <= edge_prob: 
                                adj_matrix[i, j] = 1 
                                edges += 1
            if num_edges == math.inf:
                break 
        return Digraph.from_matrix(adj_matrix)


def kron_prod(G: np.ndarray, H: np.ndarray) -> np.ndarray:
    """
    Get the tensor product of two graphs in terms of adjacency matrices (equiv. to kronecker product of the adjacency matrices)
    """
    return np.kron(G, H)

def mat_pow(G: np.ndarray, p: int) -> np.ndarray: 
    if p < 1: raise "Not valid!"
    H = copy(G) 
    for _ in range(p-1): H = kron_prod(H, G)
    return H 

def get_connected_components(G: np.ndarray) -> List[np.ndarray]:
    Gnx = nx.from_numpy_array(G)
    components = []
    for c in nx.connected_components(Gnx):
        l = sorted(list(c))
        components.append(G[np.ix_(l, l)])
    return components 


def K(n: int, m: int = None, directed: bool = True) -> Digraph:
    """
    Return a complete graph with k vertices
    """
    if m is None:
        vertices = [str(i) for i in range(1,n+1)] 
        return Digraph(
            vertices=list(vertices),
            edges=set([(i,j) for i, j in product(vertices, vertices) if i != j])
        )
        

def C(n: int, directed: bool = False) -> Digraph:
    """
    Return an undirected cycle with k vertices
    """
    if n == 1:
        return Digraph(vertices={'1'}, edges=set()) 
    vertices = [str(i) for i in range(1,n+1)]
    
    if not directed:
        edges=set(chain.from_iterable(
            [[(str(i), str(i % n + 1)), (str(i % n + 1), str(i))] for i in range(1, n + 1)]
        ))
    else: 
        edges=set(
            [(str(i), str(i % n + 1)) for i in range(1, n + 1)]
        )
    return Digraph(
        vertices=list(vertices),
        edges=set(edges)
    )


def P(n: int, directed: bool = True) -> Digraph:
    if n == 1:
        return Digraph(vertices=['1'], edges=set())
    vertices = [str(i) for i in range(1,n+1)]
    return Digraph(
        vertices=list(vertices),
        edges=set([(vertices[i], vertices[i+1]) for i in range(len(vertices)-1)] + 
                  (not directed)*[(vertices[i+1], vertices[i]) for i in range(len(vertices)-1)])
    )


def D(n: int) -> Digraph: 
    """
    Construct the digraphs that are directed cycles with n vertices, but an additional edge
    between two (previously adjacent) vertices.
    """
    if n == 1:
        return Digraph(vertices={'1'}, edges=set())
    digraph = C(n, directed=True).to_matrix()
    digraph[1][0] = 1
    digraph[0][1] = 1
    return Digraph.from_matrix(digraph)




clique = lambda k: K(k)
cycle = lambda k: C(k)



"""
Various graphs
"""

loop = Digraph(
    vertices={1},
    edges={(1,1)}
)

C_1  = C(1)
C_2  = C(2)
C_3  = C(3)
C_4  = C(4)
C_5  = C(5)
C_6  = C(6)
C_7  = C(7)
C_8  = C(8)
C_9  = C(9)
C_10 = C(10)
vertex   = C_1
edge     = C_2
triangle = C_3
square   = C_4
pentagon = C_5 
hexagon  = C_6 
heptagon = C_7 
octagon  = C_8 
nonagon  = C_9
decagon  = C_10

K_3 = K(3)
K_4 = K(4)
K_5 = K(5)
K_6 = K(6)
K_7 = K(7)
K_8 = K(8)
K_9 = K(9)



"""
Some minimal graphs for certain polymorphisms
"""


nu4 = Digraph(
    vertices={'1','2','3','4'},
    edges={
        ('1','2'),('1','3'),('1','4'),
        ('2','3'),('2','4'),
        ('4','1'),('4','2')
    }
).to_matrix()



nu3 = Digraph(
    vertices={'0','1'},
    edges={
        ('0','1'),
        ('1','0'),('1','1')
    }
).to_matrix()


nu4 = Digraph(
    vertices={'1','2','3','4'},
    edges={
        ('1','2'),('1','3'),('1','4'),
        ('2','3'),('2','4'),
        ('4','1'),('4','2'),('4','4')
    }
).to_matrix()




nu5 = np.array([
    [0,1,1,1],
    [1,0,1,0],
    [1,0,1,1],
    [1,1,1,1]
], dtype=np.int8)


wnu5 = np.array([
    [0,0,0,0,0,0],
    [0,0,0,0,0,0],
    [0,1,0,0,1,0],
    [0,1,0,1,0,0],
    [1,0,0,0,0,1],
    [1,0,1,0,0,0]
], dtype=np.int8)


ts4 = np.array([
    [0,1,1,1],
    [0,0,1,0],
    [0,1,0,0],
    [1,0,0,1]
], dtype=np.int8)



sea_devil = Digraph(
    vertices={1,2,3,4,5,6,},
    edges={(2,1),(3,1),(3,2),(2,4),(4,3),(4,5),(6,5),(6,6)}
).to_matrix()




# print(sea_devil)



test = np.array([
    [1,0,0,0],
    [0,0,0,1],
    [1,0,0,0],
    [0,1,0,1]
])


test1 = np.array([
    [0,1,0],
    [1,0,1],
    [0,1,0]
])


def directed_get_connected_components(G):
    if isinstance(G, Digraph):
        Gnx = nx.DiGraph() 
        Gnx.add_edges_from(G.edges)
    elif not isinstance(G, nx.DiGraph):
        Gnx = nx.DiGraph(G)
    components = []
    for c in nx.weakly_connected_components(Gnx):
        subgraph = nx.subgraph(Gnx, c)
        components.append(Digraph(
            vertices=c,
            edges=set(nx.edges(subgraph))
        ))
    return components 


def undirected_get_connected_components(G):
    if isinstance(G, Digraph):
        Gnx = nx.Graph() 
        Gnx.add_edges_from(G.edges)
    elif not isinstance(G, nx.Graph):
        Gnx = nx.Graph(G)
    components = []
    for c in nx.connected_components(Gnx):
        subgraph = nx.subgraph(Gnx, c)
        components.append(Digraph(
            vertices=c,
            edges=set(nx.edges(subgraph))
        ))
    return components 




"""
Various relational structures of some interest
"""

def perms(set_size: int = 3, num_elems: int = 3) -> List[Tuple[int, int, int]]:
    # return all possible ordered sets of size set_size with num_elems distinct elements
    elems = list(range(num_elems))
    every_pi = list(product(*(elems for _ in range(set_size))))
    return every_pi


s_ijk = set(perms(set_size=3, num_elems=2)) 
s_ijk_2 = set(perms(set_size=2, num_elems=2)) 

three_sat = RelationalStructure(
    domain=[0,1],
    relations=[
        s_ijk - {(0,0,0)},   # s_000
        s_ijk - {(0,0,1)},   # s_001 
        # s_ijk - {(0,1,0)},
        s_ijk - {(0,1,1)},
        # s_ijk - {(1,0,0)},
        # s_ijk - {(1,0,1)},
        # s_ijk - {(1,1,0)},
        s_ijk - {(1,1,1)},
    ]
)

two_sat = RelationalStructure(
    domain=[0,1],
    relations=[
        s_ijk_2 - {(0,0)},   # s_000
        s_ijk_2 - {(0,1)},   # s_001 
        # s_ijk_2 - {(1,0)},
        s_ijk_2 - {(1,1)}
    ]
)

one_in_three_sat = RelationalStructure(
    domain=[0,1],
    relations=[{(0,0,1),(0,1,0),(1,0,0)}]
)

horn_three_sat = RelationalStructure(
    domain=[0,1],
    relations=[
        {tuple([0])},{tuple([1])},
        s_ijk - {(0,1,1)},
        s_ijk - {(1,1,1)},
    ]
)

digraph_unreachability = RelationalStructure(
    domain=[0,1], 
    relations=[
        {tuple([0])},{tuple([1])},{(0,0),(0,1),(1,1)}
    ]
)


def ham(t: tuple) -> int:
    return sum(t) 

def two_plus_eps_sat(k: int) -> Tuple[RelationalStructure, RelationalStructure]:
    return (
        RelationalStructure(
            domain=[0,1],
            relations=[
                set([t for t in perms(set_size=2*k + 1, num_elems=2) if ham(t) >= k]),
                {(0,1),(1,0)}
            ]
        ),
        RelationalStructure(
            domain=[0,1],
            relations=[
                set([t for t in perms(set_size=2*k + 1, num_elems=2) if ham(t) >= 1]),
                {(0,1),(1,0)}
            ]
        )
    )


one_in_three_sat = RelationalStructure(
    domain=[0,1],
    relations=[{(1,0,0),(0,1,0),(0,0,1)}]
)
not_all_equal_sat = RelationalStructure(
    domain=[0,1],
    relations=[set(perms(3, 2)) - {(0,0,0),(1,1,1)}]
)


def hypergraph_col(k: int) -> RelationalStructure:
    return RelationalStructure(
        domain=list(range(k)),
        relations=[set(perms(3,k)) - set([(a,a,a) for a in range(k)])]
    )

def strong_vs_normal_hypergraph_colouring(k, c) -> Tuple[RelationalStructure, RelationalStructure]:
    return (
        RelationalStructure(
            domain=list(range(k+1)),
            relations=[set([t for t in perms(k, k+1) if len(set(t)) == k])]  # i.e., all k-tuples such that all elements in the tuple are distinct 
        ),
        RelationalStructure(
            domain=list(range(c)),
            relations=[set([t for t in perms(k, c) if len(set(t)) > 1])]  # i.e., all k-tuples such that not all elements are the same (that is, some pair of elements are distinct)
        )
    )

def rainbow_vs_hypergraph_colouring(k: int, q: int, c: int) -> Tuple[RelationalStructure, RelationalStructure]:
    return (
        RelationalStructure(
            domain=list(range(q)),
            relations=[set([t for t in perms(k, q) if set(t) == set(range(q))])]
        ),
        RelationalStructure(
            domain=list(range(c)),
            relations=[set([t for t in perms(k, c) if len(set(t)) > 1])]  # i.e., all k-tuples such that not all elements are the same (that is, some pair of elements are distinct)
        )
    )