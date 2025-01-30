Tree Equivalence in Lean4
Definitions:
[x] **hasACycle** Determines if the graph has a cycle
[x] **isAcyclic** Determines if the graph is acyclic
[x] **nonEdgeSet** The set of all edges not present in the graph
[x] **addEdgeToGraph** Adds an edge to a graph
[x] **deleteEdgeFromGraph** Deletes an edge from a graph
[x] **isMaximallyAcyclic** Determines if the graph is maximally acyclic
[x] **isUniquePath** Determines if all paths between two verticies in a graph are unique
[x] **Tree** Definition of a tree
[] **putElemInSet** Puts an element in a set

Main Proof:
[x] (Elliot) **treeImpliesTwoVerticiesConnectedByUniquePath** T is a tree implies any two verticies in T are connected by a unique path (is proved using SimpleGraph.Acyclic)
[x] (Elliot) **twoVerticesConnectedByUniquePathImpliesTree** Any two verticies in T being connected by a unique path implies T is a tree (is proved using SimpleGraph.Acyclic)
[]  (Olivia) Any two verticies in T being connected by a unique path implies T is minimally connected
[x] (Elliot) **treeIsMinimallyConnected** T is minimally connected implies T is a tree (is proved using SimpleGraph.Acyclic) 
    - Here there are two 'sorry' statements, which I believe are due to definitional equivalence though I believe are trivially true.
[] (Olivia)
[] (Olivia)
[] (Dan)
[] (Dan)
[] (Krisha)
[] (Krisha)

Other theorems:
[x] **minusEmptyGraph** The edges not present in the empty graph is the same as the edges present in the complete graph
[x] **emptyGraphToPathGraphOnTwoVertices** Adding an edge to the empty graph gives the path graph on two verticies
[] **maximallyAcyclicP3** The path graph on three verticies is maximally acyclic
