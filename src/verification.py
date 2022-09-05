
from typing import Callable, Dict, List, Tuple, Union
from digraph_lib import Digraph
from poly_sat import rearrange
"""
Functions for verifying the correctness of polymorphisms and homomorphisms.
(Note: for internal use only -- i.e., these are not part of the UI)
"""
Mapping = Dict[Union[str, int], Union[str, int]]


def verify_digraph_poly(polymorphisms: Union[Dict[str, str], List[Dict[str, str]]], G: Digraph, H: Digraph, arity: int, poly_func: Callable = None, verbose: bool = False) -> bool:
    """
    Function to ensure a polymorphism (or list of polymorphisms) is valid by ensuring:
     (1) the polymorphism preserves edges
     (2) the polymorphism is defined for the entire domain
     (3) any conditions for special polymorphisms are satisfied
    """ 
    if isinstance(polymorphisms, dict):
        polymorphisms = [polymorphisms]
    elif not isinstance(polymorphisms, list):
        print("Must input a dict or a list for polymorphism(s).")
        return False 
    G_ = G**arity

    for polymorphism in polymorphisms:

        # Check each vertex of G^arity to ensure it is accounted for by the polymorphism
        if verbose: print("Verifying completeness of polymorphism.")
        for vertex in G_.vertices:
            if vertex not in polymorphism:
                print("Polymorphism is not a total function.")
                return False
        if verbose: print("Completeness verified.")

        # Check each edge of G^arity, ensuring it is mapped to an edge of H (i.e., is preserved)
        if verbose: print("Verifying edge preservation of polymorphism.")
        for edge in G_.edges:
            if (polymorphism[edge[0]], polymorphism[edge[1]]) not in H.edges:
                print("Polymorphism does not preserve edges.")
                return False
        if verbose: print("Preservation verified.")

        # If a polymorphism identity has been provided, ensure this is satisfied by the polymorphism
        to_list = lambda x: x if isinstance(x, list) else [x] 
        if poly_func is not None:
            if verbose: print("Verifying special polymorphism condition.") 
            seen = set()
            for vertex in G_.vertices:
                if vertex not in seen:
                    seen.add(vertex)
                    poly_vertices = to_list(poly_func(vertex))
                    for poly_vertex in poly_vertices:
                        seen.add(poly_vertex)
                        if polymorphism[vertex] != polymorphism[poly_vertex]:
                            print("Specified polymorphism condition not satisfied.")
                            return False 
            if verbose: print("Condition verified.")
    
    return True           

def verify_minors(functions: List[Mapping], function_minors: Dict[int, Dict[int, List[int]]], pi: List[Tuple[int, ...]]) -> bool:
    inputs = list(functions[0].keys())

    # Verify that the minors obtained are indeed valid minors
    for i, function in enumerate(functions):

        # Obtain the minors for this function
        pis = function_minors[i]
        for pi_idx in list(pis.keys()):
            p = pi[pi_idx]
            pi_minors = pis[pi_idx]
            for minor_idx in pi_minors:
                minor = functions[minor_idx]

                # Ensure that each input to the function is mapped to the same place as 
                # each rearrangment (as per pi) of the inputs to the minor
                for inp in inputs:
                    if function[inp] != minor[rearrange(inp, p)]:
                        return False 

    return True


def verify_minion_homo(homomorphism: Mapping, polymorphisms: List[Mapping], poly_minors: Dict[int, List[int]], projections: List[Dict[str, str]], proj_minors: Dict[int, List[int]], pi: List[Tuple[int, ...]], check_minors: bool = True) -> None:
    """
    Function for verifying that a given minion homomorphism to projections from a set of polymorphisms is valid.
    Note that this procedure has a considerably high time complexity, hence should only be used on sufficiently small homomorphisms.
    """
    # same = lambda f, g: any((f[inp] != g[inp] for inp in inputs))

    if check_minors:
        if not verify_minors(polymorphisms, poly_minors, pi):
            return False 
        if not verify_minors(projections,   proj_minors, pi):
            return False

    for poly_idx, poly in enumerate(polymorphisms):

        # Ensure the homomomorphism is defined for this polymorphism
        if poly_idx not in homomorphism:
            print("Homomorphism is not defined for all polymorphisms.")
            return False

        # Obtain the projection to which this polymorphism is mapped
        proj_idx = homomorphism[poly_idx]
        # proj = projections[proj_idx]

        # Iterate through the minors of the polymorphism
        for pi_idx in list(poly_minors[poly_idx].keys()):
            if pi_idx not in proj_minors[proj_idx]:
                print("Minors not preserved.")
                return False
            
            pi_poly_minors = poly_minors[poly_idx][pi_idx]
            pi_proj_minors = proj_minors[proj_idx][pi_idx]
            
            for f_idx in pi_poly_minors:
                if homomorphism[f_idx] not in pi_proj_minors:
                    print("Taking minors is not preserved.")
                    return False  
    
    return True

