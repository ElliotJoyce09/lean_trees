# Tree Equivalence in Lean 4

This repository contains proofs and definitions related to tree equivalence in **Lean 4**.

## Comments 

**Daniel**

Overall, I am extremely satisfied with the end result of the project. Whilst the goals assigned to me were lofty, I was able to complete them all. The only exception to this is a “sorry”’d out  have statement “deleteableEdgeSets_Nonempty”. This was a result equivalent to proving that each connected graph has a minimum spanning tree, which would have been an extremely large task. As I am satisfied with the quantity and quality of my other work, I have decided to consider this result beyond the scope of the project, and so have left a sorry as a substitute for a proof. I also have two definitions marked as “noncomputable” in Lean. This is because the only method I could conceive to create them involved using an ‘if’ statement. Whilst I do consider this a weakness in my proof, it is still logically sound and compiles in Lean, so I still believe this to be an acceptable solution.

The process of completing my goals included learning the intricacies of many facets of lean, such as Simple Graphs, Finiteness, and Cardinality. Over the course of the project, I believe I have improved greatly not only at theorem proving in lean but at theorem proving as a whole. We were all equally involved in the planning phase, then separately continued our work over the time from then until hand-in. As I finished the bulk of my work earlier than others, I spent the time afterwards helping other people in my group finish their workload and stay on track for our deadline, as well as helping put all the code together into one cohesive file. In conclusion, I am extremely happy with the result our group has delivered, and believe we have proved the theorem to the best of our ability. 

I would also like to state that all contributions viewable in the git history attributed to me are accurate and representative of my contribution to the project.


**Elliot**

Overall, I found proving the required theorems to be quite challenging. As a result, I ultimately relied on the Acyclic package to complete my work. However, I take pride in the fact that the proofs are my own rather than simply adapting examples from the package’s documentation.

In my third theorem, there are two ‘sorry’ statements that I believe are trivial, but I struggled to formally prove them. Despite spending a significant amount of time over the holidays attempting to construct theorems without the Acyclic package, I often found myself going in circles. This wasn’t due to a lack of effort but rather a difficulty in understanding how Lean works at a deeper level.

That said, I am particularly pleased with my work on the addEdgeToGraph and removeEdgeToGraph definitions, especially proving that adding an edge to an empty graph results in P2. The finite nature of these cases made them more intuitive for me to reason through. However, when it came to more abstract proofs, I found that while I could conceptualize them in my head, translating them into Lean proved to be a significant challenge. For example, I understand intuitively that if a graph contains two non-unique paths between the same vertices, it must contain a cycle. This seems almost trivial to me, yet I struggled to formalize it in Lean due to the intricacies of the definition of a cycle. Despite extensive effort, I was unable to reach a satisfactory conclusion.

Because I relied on the Acyclic package, I feel that I don’t deserve the same marks as the other members of my group, as my approach was ultimately an easier one. I also want to acknowledge Daniel’s contributions—he was incredibly helpful to all of us and demonstrated a deep understanding of Lean.

**Olivia**

I am pleased with how this project has turned out. The final result of this proof strongly resembles the plan we had laid out for it, with all objectives in my section as well as the group as a whole being complete and satisfactory. Throughout the project I have become stronger at using lean of course, with a lot of focus on SimpleGraphs, Walks, Paths and a bit on Subgraphs and transferance. During term 1 I worked alongside Elliot to set up a lot of the definitions and lemmas which we would then need for our theorems, and then since the break we have worked more independently on our individual theorems as laid out in the planning section. 

I have also left a couple of 'sorry' statements in my theorems on what I believe to be relatively minor, but necessary, results that just won't drop out correctly when trying to solve them despite numerous hours spent trying. These 'sorry' statements are strictly my own and nobody else in the group should lose marks for these should you believe the statements deserve to be penalised. 

The github commit history is not entitrely accurate of my contribution to this project. As Elliot and myself worked together during term 1, it was only Elliot who added anything to the github during this time. My work includes the work done with Elliot in setting up definitions and lemmas as well as the proofs of Unique Path -> Minimally Connected, Tree -> Maximally Acyclic, and Maximally Acyclic -> Tree, the three of which should hopefully be accurately listed as sections which I personally have added to the code. (Theorems start on line xxxx of Lean file)


**Krishna**



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

- **treeIsMinimallyConnected** ✅ (Elliot)  
  _T is minimally connected implies T is a tree._  
  (_Proved using `SimpleGraph.Acyclic`. Contains two `sorry` statements, likely due to definitional equivalence._)


**(Olivia's Proofs)** 
- **twoVerticesConnectedByUniquePathImpliesMinimallyConnected** ✅ (Olivia)  
  _Any two vertices in T being connected by a unique path implies T is minimally connected._

- **TreeIsMaximallyAcyclic** ✅ (Olivia)  
  _Any graph which is a tree is maximally acyclic, meaning if any edge not currently in the edge set is added to
  the graph, then the graph will contain a cycle._

- **MaximallyAcyclicIsTree** ✅ (Olivia)  
  _Any graph which is maximally acylic is a tree, meaning that the graph is connected and acylic._
  

**(Daniel's Proofs)**
- **onetwothreefour_implies_five** ✅ (Daniel)
 
  _The proof that (1,2,3,4) → (5) (Where the numbers reference the original statement of the theorem from the MA4J3 Graph Theory lecture notes). That is, if a graph G on a finite and nonempty vertex set is a tree, then we have |E(G)| = |V(G)| - 1._  
  
- **five_implies_onetwothreefour_acyclic_part** ✅ (Daniel)
  
  _The first part of the proof of (5) → (1,2,3,4). It is a proof that a connected graph with one less edge than vertices is acyclic._
  
- **five_implies_onetwothreefour** ✅ (Daniel)
  
  _The proof of (5) → (1,2,3,4). If a graph G on a finite vertex set is connected and has one less edge than it does vertices, then it is a tree._


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
  
  _This result has been marked as noncomputable in lean due to its usage of an if statement._
- **spanningCoeToCoeHom** ✅  (Daniel)
  
  _This result has also been marked noncomputable due to its reliance on the above result._
  
- **reachableByCompImpliesconnComp** ✅ (Daniel)
- **connected_component_coe_is_connected** ✅ (Daniel)
- **subgraph_to_graph_hom** ✅ (Daniel)
- **subgraph_hom_eq_implies_eq** ✅ (Daniel)
- **subgraph_hom_inj** ✅ (Daniel)
- **Walk_map** ✅ (Daniel)
- **conn_comp_acyclic** ✅ (Daniel)
- **my_card_congr** ✅ (Daniel)
  
  _This result is not entirely my work, but instead is an adaptation of a prexisting lemma to my use case._
  
- **my_set_fintype_card_eq_univ_iff** ✅ (Daniel)
  
  _This result is not entirely my work, but instead is an adaptation of a prexisting lemma to my use case._
  
- type_eq_set_iff_card_the_same** ✅ (Daniel)
- my_card_congr'** ✅ (Daniel)
  
  _This result is not entirely my work, but instead is an adaptation of a prexisting lemma to my use case._
  
- subgraph_edgeSet_card_eq_coe_card** ✅ (Daniel)
- split_up_card_of_union** ✅ (Daniel)
- union_minus_intersection_eq_sum_of_sets** ✅ (Daniel)
- conn_comp_empty_intersection** ✅ (Daniel)
- getVert_in_support** ✅ (Daniel)
- getVert_to_support_index_map** ✅ (Daniel)
- takeUntil_length_lt_if_endpoints_neq** ✅ (Daniel)
- my_set_fintype_card_le_univ** ✅ (Daniel)
  
  _This result is not entirely my work, but instead is an adaptation of a prexisting lemma to my use case._
  
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

- **minusEmptyGraph** ✅ (Elliot) – The edges not present in the empty graph are the same as the edges present in the complete graph. 
- **emptyGraphToPathGraphOnTwoVertices** ✅ (Elliot) – Adding an edge to the empty graph gives the path graph on two vertices.
- **maximallyAcyclicP3** ⬜ (Elliot) – The path graph on three vertices is maximally acyclic.

---

### ✅ = Completed | ⬜ = Pending
