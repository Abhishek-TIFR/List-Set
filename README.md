# List-Set 
Towards a formal verification of perfect garph theorems in Coq Proof Assistant 

The project is split into the following files: 

1. GenReflect.v: Contains common results on reflection techniques.

2. SetSpecs.v: Common predicates over sets.

3. Sorting.v: Sorting a list using a decidable binary relation.

4. MinMax.v: Min and Max in a list.

5. DecType.v: Type with decidable equality. 

6. SetReflect.v: Reflection lemmas for sets on decidable types

7. DecList.v: Lists on decidable types

8.  OrdType.v: A type with decidable equality and ordering among elements.

9. OrdList.v: Lists of elements of ordType

10. OrdSet.v: Sets as ordered lists 

11. SetMaps.v: Functions over sets

12. Powerset.v: Power sets as sets

13. UG.v: Undirected graphs with decidable edge relations.

14. MoreUG.v: Graph theory on decidable undirected graphs

15. IsoUG.v: Graph Isomorphism  

16. PreLovas:  Definition of vertex repetition as a relation

17. LovaszRep.v:  Lovasz Replication Lemma Proof for one vertex expansion


The file sets.sh can be used to compile the files on sets and power sets (i.e. up to Powerset.v). The file graphs.sh can be used to compile the files on undirected graphs (i.e. UG.v MoreUG.v and IsoUG.v). To compile the whole project run all.sh. 
