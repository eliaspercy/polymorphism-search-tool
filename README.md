# polymorphism-search-tool
 
## Intstructions

### Setup

After opening the UI, you should see three panels: top left, bottom left, and right.

The top left panel is where you will specify the structures between which you wish to find polymorphisms. There are some preset options, such as cliques and cycles, but users are able to input completely arbitrary relational structures (which includes but is not limited to directed graphs). To input custom structures, just select the "Custom" option from the drop-down menu and select a valid text file. The format of such a text file is best explained by example, so see the "example-structures" folder. 

### SAT-solving

After selecting the type of polymorphism to be searched for and the polymorphism arity, you may select a SAT-solver from the drop down menu (Lineling or Glucose usually works best) and then click search. If a polymorphism is found, you can save it by clicking "Save polymorphism" on the lower right panel, which will just download a text file specifying the map. 

If the structures are sufficiently small, you can also click the "Accumulate" option which will gather all of the polymorphiss of the specified type and arity between the structures, and follow this with "Find minion homomorphism to projections" which will attempt to locate a minion homomorphism from this gathered set of polymorphisms to to the set of 2-ary projections. 


### Automated Theorem Proving

This functionality hasn't been scrutinised to the same extent as the SAT-solving approach since, in general, it did not perform quite as well. Nevertheless, one can use it as an alternative if SAT-solving is unable to obtain a result in a reasonable amount of time, or perhaps to verify any results that are obtained. Note also that this has been developed to only work for *digraphs*, and not arbitrary relational structures.

To use, simply set everything up as before and then click "Construct formula". This will download a file with the ".p" extension. This file will contain a formula in "TPTP syntax" which can be used by various automated theorem provers and model finders to determine satisfiability. This can be done at https://www.tptp.org/cgi-bin/SystemOnTPTP, where you are able to simply upload this ".p" file then select one of the theorem provers from the list (I would recommend Vampire-SAT or Paradox), and attempt to solve. The formula will be satisfiable if and only if a polymorphism of the specified type does exist.

The locating of minion homomorphisms to projections feature is not available for this approach.
