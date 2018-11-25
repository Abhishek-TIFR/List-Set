# List-Set 
Formalisation of Perfect Graph theorems in Coq Proof Assistant 

This work aims to formally verify perfect graph theorems (WPGT and SPGT) in the coq proof assistant. 
The project is split into the following files: 

1. GenReflect.v: Contains common results on reflection techniques.

2. SetSpecs.v: Common predicates over sets.

3. Sorting.v: Sorting a list using a decidable binary relation.

4. MinMax.v: Min and Max in a list.

5. DecType.v: Type with decidable equality. 

6. SetReflect.v: Reflection lemmas for sets on decidable types

7. DecList.v: Lists on decidable types

8. MoreDecList.v: Lists on decidable types

9.  OrdType.v: A type with decidable equality and ordering among elements.

10. OrdList.v: Lists of elements of ordType

11. OrdSet.v: Sets as ordered lists 

12. SetMaps.v: Functions over sets

13. Powerset.v: Power sets as sets

14. DecUG.v: Undirected graphs with decidable edge relations.

15. MoreDecUG.v: Graph theory on decidable undirected graphs

16. IsoUG.v: Graph Isomorphism  

17. Lovasz.v: Vertex Replication and the new edge relation

18. LovaszRep.v: Lovasz replication Lemma.


The file sets.sh can be used to compile the files on sets and power sets (i.e. up to Powerset.v)
The file graphs.sh can be used to compile the files on undirected graphs (i.e. DecUG.v MoreDecUG.v and IsoUG.v) 
