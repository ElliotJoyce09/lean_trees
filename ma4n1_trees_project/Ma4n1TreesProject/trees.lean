import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Logic.Basic
import Mathlib.Order.Cover
import Mathlib.Data.Set.Basic

namespace trees

def hasACycle {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ (u : V), ∃ (p : G.Walk u u), p.IsCycle

def isAcyclic {V : Type} (G : SimpleGraph V) : Prop :=
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

theorem emptyGraphToPathGraphOnTwoVertices : SimpleGraph.pathGraph 2 = addEdgeToGraph (emptyGraph (Fin 2)) (Sym2.mk (0, 1)):= by
  ext a b
  simp [SimpleGraph.pathGraph, addEdgeToGraph]
  apply Iff.intro
  intro h
  cases' h with h1 h2
  have h1_eq : a = 0 ∧ b = 1 := by
    fin_cases a
    fin_cases b
    simp at h1
    cases' h1 with h1_1 h1_2
    contradiction
    simp
    fin_cases b
    simp at h1
    cases' h1 with h1_1 h1_2
    contradiction
    cases' h1 with h1_1 h1_2
    contradiction
  simp [h1_eq]
  have h2_eq : a = 1 ∧ b = 0 := by
    fin_cases a
    fin_cases b
    simp at h2
    cases' h2 with h2_1 h2_2
    contradiction
    cases' h2 with h2_1 h2_2
    contradiction
    fin_cases b
    simp
    simp at h2
    cases' h2 with h2_1 h2_2
    contradiction
  simp [h2_eq]
  intro h
  cases' h with h1 h2
  cases' h2 with h2_1 h2_2
  cases' h1 with h1_1 h1_2
  cases' h2_1 with h2_1_1 h2_1_2
  exfalso
  apply h2_2
  subst h1_1
  subst h2_1_1
  rfl
  constructor
  subst h1_1
  subst h2_1_2
  apply covBy_of_eq_or_eq
  simp
  simp
  intro h
  intro h_1
  have h1_eq : h = 0 ∨ h = 1 := by
    fin_cases h
    simp
    simp
  simp [h1_eq]
  cases' h2_1 with h2_1_1 h2_1_2
  right
  subst h2_1_1
  subst h1_2
  apply covBy_of_eq_or_eq
  simp
  simp
  intro h
  intro h_1
  have h1_eq : h = 0 ∨ h = 1 := by
    fin_cases h
    simp
    simp
  simp [h1_eq]
  exfalso
  apply h2_2
  subst h1_2
  subst h2_1_2
  rfl

def isMaximallyAcyclic {V : Type} (G : SimpleGraph V) : Prop :=
  ¬hasACycle G ∧ (∀ e ∈ nonEdgeSet G, hasACycle (addEdgeToGraph G e))

theorem maximallyAcyclicP3 : isMaximallyAcyclic (SimpleGraph.pathGraph 3) := by
  apply And.intro
  unfold hasACycle
  simp
  intro x h
  intro i
  fin_cases x
  simp at h
  cases' i with isACircuit tailContainsNoDuplicates
  rw [@SimpleGraph.Walk.isCircuit_def] at isACircuit
  simp at isACircuit
  obtain ⟨isATrail, isNotAPath⟩ := isACircuit
  rw [@SimpleGraph.Walk.isTrail_def] at isATrail
  rw [← @SimpleGraph.Walk.isPath_iff_eq_nil] at isNotAPath
  rw [← @SimpleGraph.Walk.isTrail_def] at isATrail
  -- we use the fact that it is a trail to show no edges are repeated
  have noEdgesRepeated : ∀ e ∈ h.edges, Multiset.count e h.edges = 1 := by
    intro h1 h2
    refine Multiset.count_eq_one_of_mem ?d h2
    simp
    exact isATrail.edges_nodup
  -- we use the fact it is not a path to show a vertex has to be repeated
  have aVertexRepeated : ∃ v : (Fin 3), Multiset.count v h.support > 1 := by
    contrapose! isNotAPath
    simp at isNotAPath
    rw [@SimpleGraph.Walk.isPath_def]
    exact List.nodup_iff_count_le_one.mpr isNotAPath
  -- NEED TO SHOW THAT A VERTEX REPEATED IMPLIES AN EDGE IS REPEATED ON A PATH GRAPH ON 3 VERTICIES
  -- COULD TRY THAT IF IT IS IN THE SUPPORT OF A WALK, THEN THERE IS AN EDGE GOING TO/FROM IT
  obtain ⟨vertex, vertexIsRepeated⟩ := aVertexRepeated

  sorry

def isUniquePath {V : Type} (G: SimpleGraph V) : Prop :=
  ∀ (u v : V) (p q : G.Path u v), p = q

def Tree {V: Type} (G : SimpleGraph V) : Prop :=
  G.Connected ∧ G.IsAcyclic

theorem pathImpliesWalk {V : Type} (G : SimpleGraph V) {u v : V} (p : G.Path u v) : ∃ (w : G.Walk u v), w = p := by
  simp

theorem treeImpliesTwoVerticiesConnectedByUniquePath {V : Type} (G : SimpleGraph V) : Tree G → ∀ (u v : V), isUniquePath G := by
  unfold Tree
  unfold isUniquePath
  intro tree
  cases' tree with connected acyclic
  apply SimpleGraph.isAcyclic_iff_path_unique.mp at acyclic
  intros u v
  exact acyclic

-- IF ANY TWO VERTICIES IN A GRAPH ARE CONNECTED BY A UNIQUE PATH THEN IT IS A TREE
-- If any two vertices in T are connected by a path, T is connected. Since the path is unique, T is acyclic. Therefore, T is a tree.
theorem twoVerticesConnectedByUniquePathImpliesTree {V : Type} (G : SimpleGraph V) [h : Nonempty V]: (∀ u v : V, isUniquePath G) → Tree G := by
  unfold isUniquePath
  unfold Tree
  intros uniquePath
  apply And.intro
  rw [@SimpleGraph.connected_iff]
  apply And.intro
  unfold SimpleGraph.Preconnected
  unfold SimpleGraph.Reachable
  let ⟨x⟩ := h
  intros u v

  sorry
  exact h
  rw [SimpleGraph.isAcyclic_iff_path_unique]
  intro v w p q
  simp_all only [Subtype.forall, Subtype.mk.injEq]
  obtain ⟨val, property⟩ := p
  obtain ⟨val_1, property_1⟩ := q
  simp_all only [Subtype.mk.injEq]
  apply uniquePath
  · exact v
  · exact v
  · simp_all only
  · simp_all only

/-- A trivial function that takes an element of some Type V and returns a Set of Type V containing only that element-/
def putElemInSet {V : Type} (u : V) : Set V :=
  {u}

/-- This is a stand in for the actual proof, which is not assigned to me-/
theorem treeIsMinimallyConnected {V : Type} {G : SimpleGraph V} (graphIsTree : G.IsTree) : ∀ e ∈ G.edgeSet, G.Connected ∧ ¬(G.deleteEdges (putElemInSet (e))).Connected := by
  intros edge edgeInEdgeSet
  have graphIsConnected : G.Connected := graphIsTree.1
  have graphWithoutEdgeIsDisconnected : ¬(G.deleteEdges (putElemInSet edge)).Connected := by
    apply Aesop.BuiltinRules.not_intro
    intro h
    sorry
  exact ⟨graphIsConnected, graphWithoutEdgeIsDisconnected⟩
