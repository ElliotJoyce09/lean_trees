# Tree Equivalence in Lean 4

This repository contains proofs and definitions related to tree equivalence in **Lean 4**.

**The theorem to prove:**
The following statements are equivalent for a graph T:


(1) T is a tree.


(2) Any two vertices in T are connected by a unique path.


(3) T is minimally connected, i.e. T is connected but T − e is disconnected for any edge
e ∈ E(T).


(4) T is maximally acyclic, i.e. T is acyclic but T + uv contains a cycle for any two nonadjacent vertices u, v of T.


(5) T is connected and |E(T)| = |V (T)| − 1.


(6) T is acyclic and |E(T)| = |V (T)| − 1

**The followed proof is from the MA4J3 Lecture Notes**

_With the exception of the proof of (1,2,3,4,5) => (6)_

## Comments 

**Daniel**

Overall, I am extremely satisfied with the end result of the project. Whilst the goals assigned to me were lofty, I was able to complete them all. The only exception to this is a “sorry”’d out  have statement “deleteableEdgeSets_Nonempty”. This was a result equivalent to proving that each connected graph has a minimum spanning tree, which would have been an extremely large task. As I am satisfied with the quantity and quality of my other work, I have decided to consider this result beyond the scope of the project, and so have left a sorry as a substitute for a proof. I also have two definitions marked as “noncomputable” in Lean. This is because the only method I could conceive to create them involved using an ‘if’ statement. Whilst I do consider this a weakness in my proof, it is still logically sound and compiles in Lean, so I still believe this to be an acceptable solution.

The process of completing my goals included learning the intricacies of many facets of lean, such as Simple Graphs, Finiteness, and Cardinality. Over the course of the project, I believe I have improved greatly not only at theorem proving in lean but at theorem proving as a whole. We were all equally involved in the planning phase, then separately continued our work over the time from then until hand-in. As I finished the bulk of my work earlier than others, I spent the time afterwards helping other people in my group finish their workload and stay on track for our deadline, as well as helping put all the code together into one cohesive file, and connecting the results into a single theorem. In conclusion, I am extremely happy with the result our group has delivered, and believe we have proved the theorem to the best of our ability. 

I would also like to state that all contributions viewable in the git history attributed to me are accurate and representative of my contribution to the project.


**Elliot**

Overall, I found proving the required theorems to be quite challenging. As a result, I ultimately relied on the Acyclic package to complete my work. However, I take pride in the fact that the proofs are my own rather than simply adapting examples from the package’s documentation.

In my third theorem, there are two ‘sorry’ statements that I believe are trivial, but I struggled to formally prove them. Despite spending a significant amount of time over the holidays attempting to construct theorems without the Acyclic package, I often found myself going in circles. This wasn’t due to a lack of effort but rather a difficulty in understanding how Lean works at a deeper level.

That said, I am particularly pleased with my work on the addEdgeToGraph and removeEdgeToGraph definitions, especially proving that adding an edge to an empty graph results in P2. The finite nature of these cases made them more intuitive for me to reason through. However, when it came to more abstract proofs, I found that while I could conceptualize them in my head, translating them into Lean proved to be a significant challenge. For example, I understand intuitively that if a graph contains two non-unique paths between the same vertices, it must contain a cycle. This seems almost trivial to me, yet I struggled to formalize it in Lean due to the intricacies of the definition of a cycle. Despite extensive effort, I was unable to reach a satisfactory conclusion.

Because I relied on the Acyclic package, I feel that I don’t deserve the same marks as the other members of my group, as my approach was ultimately an easier one. I also want to acknowledge Daniel’s contributions—he was incredibly helpful to all of us and demonstrated a deep understanding of Lean. I also messed up realising at the end I did not prove 3 -> 2, but actually ended up proving 1 -> 3. Again this isn't any of my group members issues, but instead mine.

**Olivia**

I am pleased with how this project has turned out. The final result of this proof strongly resembles the plan we had laid out for it, with all objectives in my section as well as the group as a whole being complete and satisfactory. Throughout the project I have become stronger at using lean of course, with a lot of focus on SimpleGraphs, Walks, Paths and a bit on Subgraphs and transferance. During term 1 I worked alongside Elliot to set up a lot of the definitions and lemmas which we would then need for our theorems, and then since the break we have worked more independently on our individual theorems as laid out in the planning section. 

Despite my best effort, I have had to leave a couple of 'sorry' statements in my theorems on what I believe to be relatively minor, but necessary, results that just won't drop out correctly when trying to solve them with numerous hours spent trying. These 'sorry' statements are strictly my own and nobody else in the group should lose marks for these should you believe the statements deserve to be penalised. 

The github commit history is not entitrely accurate of my contribution to this project. As Elliot and myself worked together during term 1, it was only Elliot who added anything to the github during this time. My work includes the work done with Elliot in setting up definitions and lemmas as well as the proofs of Unique Path -> Minimally Connected, Tree -> Maximally Acyclic, and Maximally Acyclic -> Tree, the three of which should hopefully be accurately listed as sections which I personally have added to the code. (Theorems on lines 5079 through to 5717 of Lean file)


**Krishna**

All in all I am quite satisfied with the quality of the parts I completed in this project. I was successfully able to prove the equivalence relation assigned to me along with a few supporting lemmas. I had a massive hiccup halfway through the project with the realisation that formalising concepts involving a countable number of connected components was going to be an extremely complicated undertaking on lean 4. As a result of this, I had to completely rethink the proof of 'six_implies_onetwothreefourfive_step_one' and stray away from the direction provided by the MA4J3 lecture notes. I then came up with an inductive proof that required various other lemmas. I was very pleased with myself, considering I encountered a pretty difficult obstacle and was able to overcome it in what I would consider a pretty creative way.

The one weakness in my proof would be my assumption of a lemma claiming that any acyclic graph has a leaf. The proof of this lemma required the use of maximal chains in set theory, which would have a maximal element, and then adapting graph theory notation for that. Since this was a very set theoretic proof, I thought it strayed quite a bit away from the topics we were concerned with, thus it is considered beyond the scope of this project. Nevertheless, I have laid out a proof in notes on the code and a possible direction one may take to prove this formally in lean - just adding 'sorry's to the parts which would require further thinking and use of the Set library in Mathlib more extensively.

I would say the project for me was a huge learning curve. I went from spending 10-15 hours combing through mathlib and other sources but making very little progress, to proving large chunks of my proofs in one sitting. By the end, I would consider myself somewhat proficient, to the point where I feel like I use lean (or logical) tactics in casual debates with my friends to formally prove a point. I am pleased with how my quarter of the project turned out, especially considering how it started out. I have about 1350 lines of code that can be attributed to me, that successfully prove what I have set out to prove (ie: they compile just fine in lean). My contributions should also be accurately represented on the git history.


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


**(Krisha's Proofs)**

- **onetwothreefourfive_implies_six** ✅ (Krishna)
  
  _The proof of (1,2,3,4,5) → (6). It is a proof that a connected acyclic graph has one less edge than it has vertices_

- **six_implies_onetwothreefourfive_step_one** ✅ (Krishna)
  
  _The First part of the proof of (6) → (1,2,3,4,5). It a proof that an acyclic graph with one less edge than vertices is Connected_
  
- **six_implies_onetwothreefourfive_step_two** ✅ (Krishna)
  
  _The Second part of the proof of (6) → (1,2,3,4,5). It is completes the proof that an acyclic graph with one less edge than vertices is a tree_

- **onetwothreefourfive_equiv_six** ✅ (Krishna)
  
  _The proof of equivalence between (6) and (1,2,3,4,5)_
 

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


- **hasACycle** ✅ – Determines if the graph has a cycle.
- **isAcyclic** ✅ – Determines if the graph is acyclic.
- **nonEdgeSet** ✅ – The set of all edges not present in the graph.
- **addEdgeToGraph** ✅ – Adds an edge to a graph.
- **deleteEdgeFromGraph** ✅ – Deletes an edge from a graph.
- **isMaximallyAcyclic** ✅ – Determines if the graph is maximally acyclic.
- **isUniquePath** ✅ – Determines if all paths between two vertices in a graph are unique.
- **Tree** ✅ – Definition of a tree.
- **putElemInSet** ✅ – Puts an element in a set.
- **hasLeaf** ✅ - Definition of a Leaf
- **type_to_set** ✅ - Converting vertices of type V into vertices in a Set V
- **subgraph_without_vertex_set** ✅ - Defines a Subgraph of a graph without a set of specified vertices


- **any_subgraph_of_an_acyclic_graph_is_acyclic** ✅ (Krishna)

_Most of my other lemmas are simply have statements in my code as they weren't particularly useful to anyone else_

- **acyclic_graphs_have_a_leaf** ✅ (Krishna) - This result has not been proven as the proof uses zorn's lemma which is very set theoretic and out of the scope of this project. I have given a rough 80 line layout on how the proof could be done on lean to demonstrate provability without using other packages.


- **minusEmptyGraph** ✅ (Elliot) – The edges not present in the empty graph are the same as the edges present in the complete graph. 
- **emptyGraphToPathGraphOnTwoVertices** ✅ (Elliot) – Adding an edge to the empty graph gives the path graph on two vertices.
- **maximallyAcyclicP3** ⬜ (Elliot) – The path graph on three vertices is maximally acyclic.

---

### ✅ = Completed | ⬜ = Pending
