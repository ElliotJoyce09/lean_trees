import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph


namespace trees

-- For whoever does part 3 the following could be useful, so I am uploading it (I'm also using it in my proof)

def secondVertexInWalk {V : Type} (G : SimpleGraph V) (v : V) (p : G.Walk v v)  : V := -- returns the first vertex along a given walk from v to v in a graph G
  p.getVert 1

def firstEdgeInWalk {V : Type} (G : SimpleGraph V) (v : V) (p : G.Walk v v)  : Sym2 V := -- gets the edge between the first vertex (v) and the second vertex in a give walk from v to v in a graph G
  s(v, (secondVertexInWalk G v p))


def putEdgeInSet {V : Type} (x : Sym2 V) : Set (Sym2 V) := -- places the given edge (as a Sym2 V) into a set on its own
  {x}

def graphWithEdgeRemoved {V : Type} (G : SimpleGraph V) (v : V) (p : G.Walk v v) (h : p.IsCycle) : SimpleGraph V := -- Creates a subgraph of G without the first edge in a walk from v to v, v ∈ V(G)
  G.deleteEdges (putEdgeInSet ( firstEdgeInWalk G v p ) ) -- NOTE TO DELETE LATER: this is a subgraph of G but I have just made it as a simple graph (if this is a problem later, try changing this)

def hasACycle {V: Type} (G: SimpleGraph V) : Prop := -- This is in SimpleGraph.Path, so are some others, do we want to strip back what we are using or just use the premade ones?
  -- should take a vertex in V and check if there is a path which starts
  -- from that vertex and end at that vertex
  ∃ (u : V), ∃ (p : G.Walk u u), p.IsCycle

def isAcyclic {V : Type} (G : SimpleGraph V) : Prop :=
  -- should take all verticies in V and check if that vertex has a cycle
  ¬ hasACycle G

def nonEdgeSet {V : Type} (G : SimpleGraph V) :=
  (completeGraph V).edgeSet \ G.edgeSet

theorem minusEmptyGraph {V : Type} : nonEdgeSet (emptyGraph V) = (completeGraph V).edgeSet := by
  simp [nonEdgeSet]

def addEdgeToGraph {V : Type} (G : SimpleGraph V) (e : Sym2 V) : SimpleGraph V :=
{ Adj := fun (x y) => G.Adj x y ∨ (x ∈ e ∧ y ∈ e ∧ x ≠ y),
  symm := by
    intros x y h
    cases' h with hp hq
    left
    apply G.adj_symm
    assumption
    right
    cases' hq with hqp hqq
    cases' hqq with hqqp hqqq
    -- angle brackets are for construction conjunctions
    exact ⟨hqqp, hqp, hqqq.symm⟩
}

-- ----------------------------------------------------------------------------------------------------------------------

def Tree {V: Type} (G: SimpleGraph V) : Prop :=
  -- should satisfy that G is Connected and Acyclic
  G.Connected ∧ isAcyclic G

def Disconnected {V : Type} (G : SimpleGraph V) : Prop :=
  ¬ G.Connected

theorem Disconnected_implies_connected_components {V : Type} (G : SimpleGraph V) (h1 : ∃ (G1 : G.Subgraph) (G2 : G.Subgraph), (G1.verts ∩ G2.verts = ∅ ∧ G1.edgeSet ∪ G2.edgeSet = G.edgeSet))
  : (Disconnected G) := by
  -- by contradiction:
  -- if G1 and G2 are such subgraphs, but G is connected, then there is a path from a vertex in G1 to a vertex in G2.
  -- so there must be an edge, e ∈ G, from a vertex in G1 to a vertex in G2
  -- but E(G1) ∪ E(G2) = E(G), and e ∉ E(G1) and e ∉ E(G2)
  -- so we have found an edge in G that is neither in G1 nor in G2 (Contradiction) 
  -- so G is disconnected
  sorry

def RemoveEdgeFromGraph {V:Type} (G : SimpleGraph V) (e : Sym2 V) : SimpleGraph V :=
{ Adj := fun (x y) => G.Adj x y ∨ (x ∉ e ∧ y ∉ e ∧ x ≠ y),
  symm := by
    intros x y h
    cases' h with hp hq
    left
    apply G.adj_symm
    assumption
    right
    cases' hq with hqp hqq
    cases' hqq with hqqp hqqq
    -- angle brackets are for construction conjunctions
    exact ⟨hqqp, hqp, hqqq.symm⟩

}

def MinimallyConnected {V : Type} (G : SimpleGraph V): Prop :=
  -- removing any edge disconnects the graph
  ∀ e ∈ G.edgeSet, (RemoveEdgeFromGraph G e).Connected

def ConnectedComponent {V : Type} (U : Set V) (G : SimpleGraph U) : Prop :=
  G.Connected
  -- or (G : SimpleGraph V) (H : G.Subgraph)
  -- H.Connected

lemma onetwothreefour_implies_five_part2 {V : Type} (VFinset : Finset V) (G : SimpleGraph VFinset) (FinEdgeSet : Finset G.edgeSet) (g_is_connected : G.Connected):
    (FinEdgeSet.card = VFinset.card - 1) := by
  
  sorry
  
lemma any_subgraph_of_an_acyclic_graph_is_acyclic {V : Type} (VFinset : Finset V) (UFinset : Set VFinset) (G : SimpleGraph VFinset) (FinEdgeSet : Finset G.edgeSet) (H : G.Subgraph) (h : isAcyclic G) : isAcyclic H.coe := by
  unfold isAcyclic
  unfold hasACycle
  by_contra
  -- u and p are a vertex and walk in H, so they are the same in G
  -- p is a cycle in G so False result is obtained
  sorry

lemma onetwothreefourfive_implies_six {V : Type} (VFinset : Finset V) (G : SimpleGraph VFinset) (FinEdgeSet : Finset G.edgeSet) : (isAcyclic G) ∧ (FinEdgeSet.card = VFinset.card - 1) := by
  -- This part of the proof is 'obvious' in the lecture notes being referenced
  -- Clearly since (5) tells us that G is connected and |E(T)| = |V (T)| − 1, we have that |E(T)| = |V (T)| − 1
  -- (4) Tells us that G is maximally acyclic. Therefore G is acyclic.
  -- So G is acyclic and |E(T)| = |V (T)| − 1.
  sorry

lemma six_implies_onetwothreefourfive_step_one {V : Type} (VFinset : Finset V) (G : SimpleGraph VFinset) (FinEdgeSet : Finset G.edgeSet) (g_is_acyclic : isAcyclic G) (CardinalityCondition : FinEdgeSet.card = VFinset.card - 1): G.Connected := by
  -- The notes state that (6) => (1,2,3,4,5) is equivalant to (6) => G is Connected.
  -- We will prove this equivalence in 'step_two'
  -- Assuming the opposite, that G is disconnected, it has connected components G_1, ..., G_k
  -- G is Acyclic so all G_i components are connected and acyclic => they are trees
  -- so |G_i| = |V(G_i)| - 1
  -- so ∑|G_i| = ∑(|V(G_i)| - 1) = (∑|V(G_i)|) - k = |V(G_1 ∪ ... ∪ G_k)| - 1 since G_1, ..., G_k are disjoint
  -- so ∑|G_i| = |V(G)| - 1 since G_1 ∪ ... ∪ G_k = G
  sorry
lemma six_implies_onetwothreefourfive_step_two {V : Type} (VFinset : Finset V) (G : SimpleGraph VFinset) (FinEdgeSet : Finset G.edgeSet) (g_is_acyclic : isAcyclic G) (g_is_connected : G.Connected) : Tree G := by
  sorry


lemma onetwothreefourfive_equiv_six {V : Type} (VFinset : Finset V) (G : SimpleGraph VFinset) (FinEdgeSet : Finset G.edgeSet) : (isAcyclic G ∧ FinEdgeSet.card = VFinset.card - 1) = Tree G := by
  unfold Tree
  simp_all only [eq_iff_iff]
  apply Iff.intro
  · intro a
    simp_all only [and_true]
    obtain ⟨g_is_acyclic, CardinalityCondition⟩ := a
    exact
      six_implies_onetwothreefourfive_step_one VFinset G FinEdgeSet g_is_acyclic
        CardinalityCondition
  · intro a
    simp_all only [true_and]
    obtain ⟨g_is_connected, g_is_acyclic⟩ := a
    exact onetwothreefour_implies_five_part2 VFinset G FinEdgeSet g_is_connected
    
    

