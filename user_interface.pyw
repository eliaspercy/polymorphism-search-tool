import traceback
import PySimpleGUI as sg
import os.path 
import sys 
sys.path.append('./src')
from src.digraph_lib import Digraph, C, K, RelationalStructure
from src.poly_sat import PCSP, custom_polymorphism, cycles_of_string, wnu_strings, symmetric_strings, minion_homomorphism_to_projection
from src.poly_atp import find_poly, build_formula
import ast

"""
Code for the user-interface
"""

sg.theme('gray gray gray')  


variables = {
    
    # Graph variables
    'G': None,          # The digraph (or structure) G         
    'H': None,          # The digraph (or structure) H
    'G_type': 'custom',
    'G_dir' : None,
    'G_size': None,
    'H_type': 'custom',
    'H_dir' : None,
    'H_size': None, 
    'directed': True, 
    'struc_type': 'Digraph',   # specify if the structures with which we are dealing are digraphs or arbitrary relational structures   

    # Random graph stuff
    'G_rand_vertices': None,
    'G_rand_edges':    None, 
    'H_rand_vertices': None,
    'H_rand_edges':    None,

    # Polymorphism variables
    'poly_type': 'None',
    'poly_func': None,   # necessary if custom poly identity is specified
    'arity': 1, 
    'custom_identity': None,

    # Solving 
    'method': 'sat',  # alt: 'atp'
    'solver': 'lingeling',
    'silent': True,
    'accumulate': False,

    # Current state
    'state': None    # the current PCSP class

}

poly_types = (
    "None",
    "Olsak",
    "Siggers",
    "Cyclic",
    "WNU",
    "TS",
    "Custom"
)
graph_types = (
    'Custom',
    'Cycle',
    'Clique',
    'Random graph'
)
sat_solvers = (
    "Lingeling",
    "Glucose 3",
    "Glucose 4",
    "MiniSAT 22",
    "MergeSAT 3"
)


# Assistant functions


def read_in_structure(filename: str, G_or_H: str = 'G', undirected: bool = False) -> RelationalStructure:
    # assert struc_type == 'Digraph' or struc_type == 'RelationalStructure'

    with open(filename, 'r') as f:
        info = f.read().splitlines()
        f.seek(0)
    try:
        info = [l for l in info if l != '']  # remove blank lines

        if len(info) < 2:
            print("Not enough information in file.")
            raise SyntaxError

        domain = ast.literal_eval(info[0])
        relations = []
        arities = []

        for line in info[1:]:
            if line == '':
                continue
            l_list = line.split(' ')
            l_list = [l for l in l_list if l != '']            
            ar = int(l_list[0])
            relations.append(set(map(ast.literal_eval, l_list[1:])))
            arities.append(ar) 

    except SyntaxError as e:
        print(e)
        print(f"Syntax error in input file for structure {graph}.")
        return False
    except ValueError:
        print(f"Arities not specified correctly in input file for structure {graph}.")
        return False

    if len(arities) == 1 and arities[0] == 2:
        return Digraph(vertices=domain, edges=relations[0])
    else:
        return RelationalStructure(domain=domain, relations=relations)




# UI Functions

undirected_toggle = [sg.Check("Undirected (for digraphs)", default=False, enable_events=True, key="-UNDIRECTED TOGGLE-")]
select_graph = lambda graph: [
    sg.Text(f"Structure {graph}:", size=(8, 1)), sg.InputCombo(graph_types, size=(20, 1), enable_events=True, key=f"-GRAPH TYPE {graph}-", default_value='Custom'),
    sg.Button(f"Print {graph}")
]
clique_cycle = lambda graph: [sg.pin(sg.Column([[   
    sg.Text("Num. vertices:", size=(10,1)), sg.In(size=(4, 1), enable_events=True, key=f"-GRAPH SIZE {graph}-")
]], visible=False, key=f'-CLIQUE SIZE {graph}-'))]

random_graph = lambda graph: [sg.pin(sg.Column([[   
    sg.Text("Num. vertices:", size=(10,1)), sg.In(size=(4, 1), enable_events=True, key=f"-RANDOM VERTICES {graph}-"),
    sg.Text("Num. edges:",    size=(9,1)), sg.In(size=(4, 1), enable_events=True, key=f"-RANDOM EDGES {graph}-"),
    sg.Button(f'Generate {graph}')
]], visible=False, key=f'-RANDOM {graph}-'))]


custom_graph = lambda graph: [sg.pin(sg.Column([[
    sg.In(size=(32,1), enable_events=True, key=f"-FOLDER {graph}-"), sg.FileBrowse(file_types=(("Text Files", "*.txt"),))
]], visible=True, key=f"-CUSTOM GRAPH {graph}-"))]

select_poly = [
    sg.InputCombo(poly_types, size=(20, 1), enable_events=True, key="-POLY TYPE-", default_value='None'),
    sg.Text(f"Arity:", size=(4, 1)), sg.In(size=(5, 1), enable_events=True, key="-POLY ARITY-", default_text='1'), 
    sg.Button('Print identity')
]
custom_poly = [sg.pin(sg.Column([[
    sg.Text("Input identity:", size=(10, 1)), sg.In(size=(25, 1), enable_events=True, key="-POLY IDENTITY-") 
]], visible=False, key="-CUSTOM POLY-"))]

solving_type = [
    sg.Text("Select method:", size=(12, 1)), 
    sg.Radio('SAT Solver', 'method', size=(8, 1), default=True, enable_events=True, key='-METHOD S-'), 
    sg.Radio('Theorem Prover', 'method', size=(12, 1), enable_events=True, key='-METHOD A-')
]

select_sat_solver = [sg.pin(sg.Column([[
    sg.Text("Select solver:", size=(10, 1)), 
    sg.InputCombo(sat_solvers, size=(15, 1), enable_events=True, key=f"-SELECT SOLVER-", default_value='Lingeling'),
    sg.Check("Accumulate", default=False, enable_events=True, key="-ACCUMULATE-") 
]], visible=True, key='-SAT-'))]

atp_output_dir = [sg.pin(sg.Column([[
    sg.Text("File directory:", size=(11, 1)), sg.In(size=(25, 1), enable_events=True, key="-OUT DIR-")
]], visible=False, key='-ATP-'))]

search_btn = [sg.pin(sg.Column([[
    sg.Button('Search'), sg.Check('Verbose', default=False, enable_events=True, key='-VERBOSE-')
]], visible=True, key='-SAT SEARCH-'))]

construct_btn = [sg.pin(sg.Column([[
    sg.SaveAs(button_text='Construct formula', default_extension='.p', enable_events=True, target='-CONSTRUCT-', file_types=(("Text Files", "*.p"),)), 
    sg.InputText(key='-CONSTRUCT-', do_not_clear=False, enable_events=True, visible=False),
]], visible=False, key='-ATP CONSTRUCT-'))]



settings_column = [
    [sg.Text("Select relational structures.")],
    undirected_toggle,
    
    select_graph('G'),
    custom_graph('G'),
    clique_cycle('G'),
    random_graph('G'),

    select_graph('H'),
    custom_graph('H'),
    clique_cycle('H'),
    random_graph('H'),

    [sg.HSeparator()],

    [sg.Text("Select polymorphism.")],
    select_poly,
    custom_poly,
    solving_type,
    select_sat_solver, 

    # atp_output_dir,

    search_btn,
    construct_btn
]

stdout_column = [
    [sg.Text("Output will appear in the following box.")],
    [sg.Output(size=(65,15), key="-OUTPUT-")],
    [sg.Button('Clear'), 
     sg.SaveAs(button_text='Save polymorphism', default_extension='.txt', enable_events=True, target='-SAVE-', file_types=(("Text Files", "*.txt"),)), 
     sg.InputText(key='-SAVE-', do_not_clear=False, enable_events=True, visible=False),
     sg.Text("Check mapping:", size=(12, 1)), sg.In(size=(15, 1), enable_events=True, key="-MAPPING-"), sg.Button('Check') 
    ],
    [sg.Button("Find minion homomorphism to projections")] 
]


layout = [
    [sg.Column(settings_column), sg.VSeparator(), sg.Column(stdout_column)] #sg.Column(image_viewer_column)]
]


def obtain_graph(graph: str):
    if variables[f'{graph}_type'].lower() == 'custom':
        if variables[f'{graph}_dir'] is None:
            print(f"Structure {graph} not specified.\n")
            return False
        elif not variables[f'{graph}_dir'].endswith('.txt'):
            print(f"Input for structure {graph} not a text (.txt) file.\n")
            return False
        elif not os.path.isfile(variables[f'{graph}_dir']):
            print(f"Input file for structure {graph} not found.\n") 
            return False

        S = read_in_structure(variables[f'{graph}_dir'], graph)
        return S
    elif variables[f'{graph}_type'].lower() == 'random graph':
        if variables[graph] is None:
            print(f"Must generate graph {G} first.")
            return False 
        else:
            return variables[graph]
    
    if not str(variables[f'{graph}_size']).isnumeric():
        print("Must input an integer for graph size.\n")
        return False
    n = int(variables[f'{graph}_size'])
    if n < 1:
        print("Graph size must be nonnegative.\n")
        return False
    if variables[f'{graph}_type'].lower() == 'cycle':
        return C(n)
    elif variables[f'{graph}_type'].lower() == 'clique':
        return K(n)
    
def handle_sat():
    required = [
        variables['G_type'],
        variables['H_type'],
        variables['poly_type'],
        variables['arity']
    ]
    if any(map(lambda x: x is None, required)):
        print("Please ensure both structures are specified.\n")
        return
    G = obtain_graph('G')
    if not G:  # i.e., obtain_graph returns false if there has been an error
        return 

    H = obtain_graph('H')
    if not H:
        return
 
    if not G.check_similar(H):
        print("The input structures are not similar!\n")
        return

    if not str(variables['arity']).isnumeric():
        print("Must input an integer for polymorphism arity.\n")
        return 
    arity = int(variables['arity'])
    if arity < 1:
        print("Arity must be nonnegative.\n")
        return
    poly_type = variables['poly_type'].lower()
    if poly_type == 'custom':
        if variables['custom_identity'] is None:
            print("Identitity not specified.\n")
            return
        try:
            idty = variables['custom_identity'].split(' ')
            idty = [i for i in idty if i != '']

            for i in idty: 
                i_list = i.split(',') 
                if len(i_list) != int(values['-POLY ARITY-']):
                    print("Error in specified identity (either a syntax error, or it does not match polymorphism arity).\n") 
                    return 

            custom_func = custom_polymorphism(idty, arity)

        except SyntaxError:
            print("Syntax error with custom identity.\n")
            return
    else:
        custom_func = None
    
    if poly_type == 'siggers':
        if arity != 4 and arity != 6:
            print("Siggers polymorphisms must be of arity 4 or 6.\n")
            return 
    elif poly_type == 'olsak':
        if arity != 6:
            print("Olsak polymorphisms must be of arity 6.\n")
            return 
    elif poly_type == 'none':
        poly_type = None

    directed = variables['directed']

    solver = variables['solver']
    
    silent = variables['silent']

    poly = PCSP(H=H, G=G, solver=solver)
    if variables["accumulate"]:
        r = poly.collect_polymorphisms(
            arity=arity, directed=directed, special=poly_type, get_power=False,
            custom_func=custom_func, silent=silent
        ) 

    else:
        r = poly.find_polymorphism(
            arity=arity, directed=directed, special=poly_type, get_power=False, 
            custom_func=custom_func, silent=silent
        )
    return poly


window = sg.Window("Digraph polymorphism finder", layout) 


# The following event loop comprises the program's logic
try:
    while True: 
        event, values = window.read() 
        
        if event == "Exit" or event == sg.WIN_CLOSED:
            break

        elif event == "-DIGRAPH TOGGLE-":
            variables['struc_type'] = 'Digraph' if values["-DIGRAPH TOGGLE-"] else 'RelationalStructure'
            print(variables['struc_type'])

        elif event == "-UNDIRECTED TOGGLE-":
            variables['directed'] = not values['-UNDIRECTED TOGGLE-']
        
        elif event == "-VERBOSE-":
            variables['silent'] = not values['-VERBOSE-']

        elif event.startswith("-GRAPH TYPE "):
            graph = event[12]
            variables[f'{graph}_type'] = values[f"-GRAPH TYPE {graph}-"].lower()
            
            # If custom was selected, open the section to input a custom graph from file
            window[f'-CUSTOM GRAPH {graph}-'].update(visible=variables[f'{graph}_type'] == "custom")
            window[f'-CLIQUE SIZE {graph}-'].update(visible=(variables[f'{graph}_type'] == "clique" or variables[f'{graph}_type'] == "cycle"))
            window[f'-RANDOM {graph}-'].update(visible=variables[f'{graph}_type'] == "random graph")


        elif event.startswith('-FOLDER '):
            graph = event[8]
            variables[f'{graph}_dir'] = values[event]                 

        if event.startswith("-GRAPH SIZE "):
            graph = event[12]
            variables[f'{graph}_size'] = values[f"-GRAPH SIZE {graph}-"].lower()


        elif event == "-POLY TYPE-":
            variables['poly_type'] = values["-POLY TYPE-"].lower()
            
            # If custom was selected, open the section to input a custom polymorphism identity
            window["-CUSTOM POLY-"].update(visible=variables["poly_type"].lower() == "custom")

        elif event == "-POLY ARITY-":
            variables['arity'] = values["-POLY ARITY-"] 

        elif event.lower() == "clear":
            window["-OUTPUT-"].update('')


        elif event == '-POLY IDENTITY-':
            variables['custom_identity'] = values[event]

        elif event.startswith('-METHOD '):

            if values["-METHOD S-"]:
                variables['method'] = 'sat'
                window["-SAT-"].update(visible=True)
                # window["-ATP-"].update(visible=False)
                window["-SAT SEARCH-"].update(visible=True)
                window["-ATP CONSTRUCT-"].update(visible=False)
            else:  
                variables['method'] = 'atp'
                window["-SAT-"].update(visible=False)
                # window["-ATP-"].update(visible=True)
                window["-SAT SEARCH-"].update(visible=False)
                window["-ATP CONSTRUCT-"].update(visible=True)

        elif event == "-SELECT SOLVER-":
            variables['solver'] = values['-SELECT SOLVER-']
        
        elif event == "-ACCUMULATE-":
            variables["accumulate"] = values["-ACCUMULATE-"]

        elif event.lower() == 'print identity':
            if variables['poly_type'] == 'custom':
                if variables['custom_identity'] is None:
                    print("Identity not specified.\n")
                else:
                    try:
                        idty = variables['custom_identity'].split(' ')
                        idty = [i for i in idty if i != '']
                        if len(idty) == 0:
                            raise TypeError
                        st = ''
                        eq = " = "                    
                        for n, i in enumerate(idty): 
                            i_list = i.split(',') 
                            if len(i_list) != int(values['-POLY ARITY-']):
                                raise ValueError 
                            st += f"{bool(n)*eq}f({i})"

                        print(st)
                    except SyntaxError:
                        print("Syntax error in identity specified.\n")
                    except ValueError:
                        print("Syntax error in identity, or it does not match polymorphism arity.\n")
                    except TypeError:
                        print("Identity not specified.\n")

            elif variables['poly_type'].lower() == 'olsak':
                try:
                    if int(variables['arity']) != 6:
                        raise ValueError
                    print("f(x,x,y,y,y,x) = f(x,y,x,y,x,y) = f(y,x,x,x,y,y)\n") 
                except ValueError:
                    print("Olsak polymorphisms must have arity 6.\n")

            elif variables['poly_type'].lower() == 'siggers':
                try:
                    if int(variables['arity']) == 6:
                        print("f(x,y,x,z,y,z) = f(y,x,z,x,z,y)\n") 
                    elif int(variables['arity']) == 4:
                        print("f(x,y,y,z) = f(y,x,z,x)\n")
                    else:
                        raise ValueError
                except ValueError:
                    print("Siggers polymorphisms must have arity 4 or 6.\n")

            elif variables['poly_type'].lower() == 'cyclic':
                try: 
                    if int(variables['arity']) < 2:
                        raise ValueError
                    string = ','.join(f'x{i}' for i in range(1, int(variables['arity'])+1))
                    cycles = cycles_of_string(string)
                    st = f'f({string})'
                    for cyc in reversed(cycles[1:]):
                        st += f' = f({cyc})'
                    print(st + '\n')
                except ValueError:
                    print("Arity for cyclic polymorphisms has to be an integer at least 2.\n")

            elif variables['poly_type'].lower() == 'wnu':
                try:
                    if int(variables['arity']) < 2:
                        raise ValueError
                    string = ','.join(['y'] + ['x' for _ in range(int(variables['arity'])-1)])
                    wnus = wnu_strings(string)
                    st = f'f({string})'
                    for wnu in reversed(wnus[1:]):
                        st += f' = f({wnu})'
                    print(st + '\n')
                except ValueError:
                    print("Arity for weak near-unanimity polymorphisms has to be an integer at least 2.\n")

            elif variables['poly_type'].lower() == 'ts':
                try:
                    if int(variables['arity']) < 2:
                        raise ValueError
                    string = ','.join(f'x{i}' for i in range(1, int(variables['arity'])+1))
                    syms = symmetric_strings(string)
                    st = f'f({string})'
                    for sym in syms[1:]:
                        st += f' = f({sym})'
                    print(st + '\n')
                except ValueError:
                    print("Arity for totally symmetric polymorphisms has to be an integer at least 2.\n")

            else:
                print("No identity specified.\n")

        elif event.lower() == 'search': 

            if variables['method'] == 'sat':
                new_state = handle_sat()
                if new_state is not None:
                    variables['state'] = new_state
            else: 
                print("Not yet implemented.")        
    
        elif event == '-CONSTRUCT-':
            G = obtain_graph('G')
            if not G:  # i.e., obtain_graph returns false if there has been an error
                continue

            H = obtain_graph('H')
            if not H:
                continue 

            if not isinstance(G, Digraph) or not isinstance(G, Digraph):
                print("Structures must be digraphs for the ATP approach.\n")
                continue

            poly_type = variables['poly_type']
            if poly_type not in {'siggers', 'olsak', 'ts', 'cyclic'}:
                print("Specified polymorphism type not available for ATP approach.\n")
                continue
            
            try:
                ar = int(variables['arity'])
            except ValueError:
                print("Arity must be integer.")
                continue

            if poly_type == 'siggers' and (ar != 4 or ar != 6):
                print("Siggers polymorphisms must be arity 4 or 6.\n")
                continue
            elif poly_type == 'olsak' and ar != 6:
                print("Olsak polymorphisms must be of arity 6.\n")
                continue

            filename = values['-CONSTRUCT-']
            if filename:
                build_formula(G=G.to_matrix(), H=H.to_matrix(), poly_type=poly_type, arity=ar, filename=filename)
                print("Formula constructed.\n")

        elif event == '-SAVE-':
            if variables['state'] is None:
                print("No polymorphism in memory.\n")
            elif variables['state'].morphism is None:
                print("No polymorphism in memory.\n")
            else:
                path = values['-SAVE-']
                if path:
                    inputs = sorted(list(variables['state'].morphism.keys()))
                    poly_file = ''
                    for i in inputs:
                        poly_file += f'f({i}) = {variables["state"].morphism[i]}\n'
                    with open(path, 'w') as f:
                        f.write(poly_file)
                    print("Polymorphism saved.\n")
                
        elif event.lower() == 'check':
            if values['-MAPPING-'] is None:
                print("Input not specified.\n")
            elif variables['state'] is None or variables['state'].morphism is None:
                print("No polymorphism in memory.\n")
            else:
                inp = values['-MAPPING-']
                if inp not in variables['state'].morphism:
                    print("Invalid input.\n")
                else:
                    print(f'f({inp}) = {variables["state"].morphism[inp]}\n')

        elif event.lower() == 'find minion homomorphism to projections':
            if variables['state'] is None:
                print("Must accumulate polymorphisms first.\n") 
            elif variables['state'].polymorphisms is None:
                print("Must accumulate polymorphisms first.\n")
            else:
                try:
                    minion_homomorphism_to_projection(variables['state'].polymorphisms, arity=int(variables['arity']))
                except Exception as e:
                    print(e)

        elif event.lower().startswith('print'):
            graph = event[6]
            G = obtain_graph(graph)
            if G:
                print(G)


        elif event.startswith('-RANDOM VERTICES'):
            graph = event[17]
            variables[f'{graph}_rand_vertices'] = values[event]

        elif event.startswith('-RANDOM EDGES'):
            graph = event[14]
            variables[f'{graph}_rand_edges'] = values[event]

        elif event.lower().startswith('generate '):
            graph = event[9]
            try:
                variables[graph] = Digraph.random_graph(num_vertices=int(variables[f'{graph}_rand_vertices']), num_edges=int(variables[f'{graph}_rand_edges']))
                if not variables[graph]:
                    variables[graph] = None
                else:
                    print("Random graph generated.\n")
                
            except ValueError:
                print("Graph sizes must be positive integers.\n")
                

    window.close()

except Exception as e:
    tb = traceback.format_exc()
    sg.Print(f'An error as occurred: {e}, {tb}')
    sg.popup_error(f'Error: {e}, {tb}')

