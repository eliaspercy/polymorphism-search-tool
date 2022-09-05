The main Python files in this folder are:

(1) digraph_lib.py
(2) poly_sat.py
(3) poly_atp.py
(4) validation.py
(5) user_interface.pyw * (this is now in the outside folder)

File (1) contains the classes defining Relational Structure and Digraphs, with various functions pertaining to these (e.g., obtaining the k-th power, generating random graphs, etc.).

File (2) contains the bulk of the implementation for the SAT-solving approach. That is, the reduction to Boolean Satisfiability is implemented, within a class entitled PCSP. This file also contains the functions for generating different polymorphism identities, and functions for locating minion homomorphisms to projections.

File (3) contains the automated theorem approach. Specifically, if contains methods for constucting a formula in TPTP syntax that can then be used by automated theorem provers on the System on TPTP interface (online - see reference 23 in paper).

File (4) contains various functions for validating the program. In particular, this includes functions for validating the correctness of polymorphisms and minion homomorphisms. This has not been attached to the UI as it isn't really intended for use by users; instead it has been used for validating the program during development.

File (5) contains the code for the user interface. In particular, this file should be an executable file that will open the user interface just by clicking on it. If not, you should be able to open it by calling 'python user_interface.pyw' from the command line. The code itself brings the main functionality of the program together within various functions.

Note that these files should be stored together within the same folder for the UI to work.