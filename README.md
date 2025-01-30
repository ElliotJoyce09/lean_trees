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
  (_Proved using `SimpleGraph.Acyclic` but contains two `sorry` statements, likely due to definitional equivalence._)

- **(Olivia's Proofs)** ⬜ ⬜

- **(Dan's Proofs)** ⬜ ⬜

- **(Krisha's Proofs)** ⬜ ⬜

## Other Theorems

- **minusEmptyGraph** ✅ – The edges not present in the empty graph are the same as the edges present in the complete graph.
- **emptyGraphToPathGraphOnTwoVertices** ✅ – Adding an edge to the empty graph gives the path graph on two vertices.
- **maximallyAcyclicP3** ⬜ – The path graph on three vertices is maximally acyclic.

---

### ✅ = Completed | ⬜ = Pending
