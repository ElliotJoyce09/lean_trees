# Tree Equivalence in Lean 4

This repository contains proofs and definitions related to tree equivalence in **Lean 4**.

## Definitions

- **hasACycle** ✅ – Determines if the graph has a cycle.
- **isAcyclic** ✅ – Determines if the graph is acyclic.
- **nonEdgeSet** ✅ – The set of all edges not present in the graph.
- **addEdgeToGraph** ✅ – Adds an edge to a graph.
- **deleteEdgeFromGraph** ✅ – Deletes an edge from a graph.
- **isMaximallyAcyclic** ✅ – Determines if the graph is maximally acyclic.
- **isUniquePath** ✅ – Determines if all paths between two vertices in a graph are unique.
- **Tree** ✅ – Definition of a tree.
- **putElemInSet** ✅ – Puts an element in a set.

## Main Proofs

- **treeImpliesTwoVerticiesConnectedByUniquePath** ✅ (Elliot)  
  _T is a tree implies any two vertices in T are connected by a unique path._  
  (_Proved using `SimpleGraph.Acyclic`._)

- **twoVerticesConnectedByUniquePathImpliesTree** ✅ (Elliot)  
  _Any two vertices in T being connected by a unique path implies T is a tree._  
  (_Proved using `SimpleGraph.Acyclic`._)

- **twoVerticesConnectedByUniquePathImpliesMinimallyConnected** ⬜ (Olivia)  
  _Any two vertices in T being connected by a unique path implies T is minimally connected._

- **treeIsMinimallyConnected** ✅ (Elliot)  
  _T is minimally connected implies T is a tree._  
  (_Proved using `SimpleGraph.Acyclic`. Contains two `sorry` statements, likely due to definitional equivalence._)

- **(Olivia's Proofs)** ⬜ ⬜

- **(Daniel's Proofs)**
- onetwothreefour_implies_five ✅
  _The proof that (1,2,3,4) → (5) (Where the numbers reference the original statement of the theorem from the MA4J3 Graph Theorylecture notes). That is, if a graph G on a finite and nonempty vertex set is a tree, then we have |E(G)| = |V(G)| - 1.
- five_implies_onetwothreefour_acyclic_part ✅
  _The first part of the proof of (5) → (1,2,3,4). It is a proof that a connected graph with one less edge than vertices is acyclic.
- five_implies_onetwothreefour ✅
  _The proof of (5) → (1,2,3,4). If a graph G on a finite vertex set is connected and has one less edge than it does vertices, then it is a tree.


- **(Krisha's Proofs)** ⬜ ⬜

## Other Theorems

Explanations for each of my lemmas/theorems/definitions can be found commented above them in the lean code - Daniel
- **secondVertexInWalk** ✅ (Daniel)
- **putElemInSet** ✅ (Daniel)
- **twoElemsInSetMeansCardGTOne** ✅ (Daniel)
- **nat_minus_one_eq_zero_implies_eq_one** ✅ (Daniel)
- **oneVertexbutEdgeIsFalse** ✅ (Daniel)
- **connectedComponentToSubGraph** ✅ (Daniel)
- **edgeConversionG'CoeToG** ✅ (Daniel)
- **map_to_membership_or_sink** ✅ (Daniel)
  _This result has been marked as noncomputable in lean due to its usage of an if statement
- **spanningCoeToCoeHom** ✅  (Daniel)
  _This result has also been marked noncomputable due to its reliance on the above result
- **reachableByCompImpliesconnComp** ✅ (Daniel)
- **connected_component_coe_is_connected** ✅ (Daniel)
- **subgraph_to_graph_hom** ✅ (Daniel)
- **subgraph_hom_eq_implies_eq** ✅ (Daniel)
- **subgraph_hom_inj** ✅ (Daniel)
- **Walk_map** ✅ (Daniel)
- **conn_comp_acyclic** ✅ (Daniel)
- **my_card_congr** ✅ (Daniel)
  _This result is not entirely my work, but instead is an adaptation of a prexisting lemma to my use case
- **my_set_fintype_card_eq_univ_iff** ✅ (Daniel)
  _This result is not entirely my work, but instead is an adaptation of a prexisting lemma to my use case
- type_eq_set_iff_card_the_same** ✅ (Daniel)
- my_card_congr'** ✅ (Daniel)
  _This result is not entirely my work, but instead is an adaptation of a prexisting lemma to my use case
- subgraph_edgeSet_card_eq_coe_card** ✅ (Daniel)
- split_up_card_of_union** ✅ (Daniel)
- union_minus_intersection_eq_sum_of_sets** ✅ (Daniel)
- conn_comp_empty_intersection** ✅ (Daniel)
- getVert_in_support** ✅ (Daniel)
- getVert_to_support_index_map** ✅ (Daniel)
- takeUntil_length_lt_if_endpoints_neq** ✅ (Daniel)
- my_set_fintype_card_le_univ** ✅ (Daniel)
  _This result is not entirely my work, but instead is an adaptation of a prexisting lemma to my use case
- edges_of_p_cut_in_G_e_removed** ✅ (Daniel)
- reachableToAllVerts** ✅ (Daniel)
- edge_not_in_connComp_implies_vert_not_in** ✅ (Daniel)
- both_cards_eq_one_gives_contradiction** ✅ (Daniel)
- not_zero_or_gt_1_implies_eq_one** ✅ (Daniel)
- have_edge_contradiction** ✅ (Daniel)
- deletingEdgeMeansNotInEdgeSet** ✅ (Daniel)
- not_in_FinsetEdgeSet_equals_not_in_edgeSet** ✅ (Daniel)
- subset_and_neq_means_card_le** ✅ (Daniel)
- Finset_subset_and_has_less_elems_implies_not_equal** ✅ (Daniel)
- subgraphImpliesLeqEdges** ✅ (Daniel)
- SetToFinsetToSetEqSet** ✅ (Daniel)

- **minusEmptyGraph** ✅ – The edges not present in the empty graph are the same as the edges present in the complete graph.
- **emptyGraphToPathGraphOnTwoVertices** ✅ – Adding an edge to the empty graph gives the path graph on two vertices.
- **maximallyAcyclicP3** ⬜ – The path graph on three vertices is maximally acyclic.

---

### ✅ = Completed | ⬜ = Pending
