import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Combinatorics.SimpleGraph.Basic

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

def Cycle {V: Type} (G: SimpleGraph V) : Prop := -- This is in SimpleGraph.Path, so are some others, do we want to strip back what we are using or just use the premade ones?
  -- should take a vertex in V and check if there is a path which starts
  -- from that vertex and end at that vertex
  sorry

def Acyclic {V : Type} (G : SimpleGraph V) : Prop :=
  -- should take all verticies in V and check if that vertex has a cycle
  sorry

def Tree {V: Type} (G: SimpleGraph V) : Prop :=
  -- should satisfy that G is Connected and Acyclic
sorry


-- This should work for any type that has exactly two distinct elements. that is what "neq" and "h" are asserting
-- The completeGraph is equivalent to the path graph on 2 vertices, the empty graph is just already defined in SimpleGraph.basic
theorem addEdgeToEmptyGraphGivesPathGaphOnTwoVerticies {V : Type} (x y : V) (neq : x ≠ y) (h : ¬ (∃ z : V, z ≠ x ∧ z ≠ y)) 
  : (completeGraph V).edgeSet = (emptyGraph V).edgeSet ∪ {s(x,y)} := by
  have emptyEdgeSetIsEmptySet : (emptyGraph V).edgeSet = ∅ := by 
    exact SimpleGraph.edgeSet_eq_empty.mpr rfl
  rw [emptyEdgeSetIsEmptySet]
  simp only [Set.union_singleton, insert_emptyc_eq]

  have xyedgeInPathGraph : s(x,y) ∈ (completeGraph V).edgeSet := by
    exact neq
  have superset : (completeGraph V).edgeSet ⊇ {s(x,y)} := by
    exact Set.singleton_subset_iff.mpr xyedgeInPathGraph
  have subset : (completeGraph V).edgeSet ⊆ {s(x,y)} := by
    by_contra not_subset
    have other_edge_in_path : ∃ e ∈ (completeGraph V).edgeSet, e ≠ s(x,y) := by
      simp_all
    obtain ⟨edge, property⟩ := other_edge_in_path
    obtain ⟨edge_val_1, edge_val_2⟩ := edge
    have x_or_y_val_1 : edge_val_1 = x ∨ edge_val_1 = y := by
      by_contra suppose_not
      simp_all
      obtain ⟨left, right⟩ := suppose_not
      have is_y : edge_val_1 = y := by 
        exact h edge_val_1 left
      exact neq (h x fun a => right is_y)
    have x_or_y_val_2 : edge_val_2 = x ∨ edge_val_2 = y := by
      by_contra suppose_not
      simp_all
      obtain ⟨left, right⟩ := suppose_not
      have is_y : edge_val_2 = y := by 
        exact h edge_val_2 left
      exact neq (h x fun a => right is_y)
    simp_all
    obtain ⟨left, right⟩ := property
    obtain ⟨left_2, right⟩ := right
    cases x_or_y_val_1 with
    | inl h_1 =>
      cases x_or_y_val_2 with
      | inl h_2 =>
        subst h_2 h_1
        simp_all only [not_true_eq_false]
      | inr h_3 =>
        subst h_3 h_1
        simp_all only [not_false_eq_true, not_true_eq_false, imp_false]
    | inr h_2 =>
      cases x_or_y_val_2 with
      | inl h_1 =>
        subst h_2 h_1
        simp_all only [not_false_eq_true, not_true_eq_false, false_implies, imp_false]
      | inr h_3 =>
        subst h_3 h_2
        simp_all only [not_false_eq_true, not_true_eq_false]
  have equal : (completeGraph V).edgeSet = {s(x,y)} := by
    exact Eq.symm (Set.Subset.antisymm superset subset)
  exact equal








-- Got rid of the finite simple graph as that doesn't work. What I believe functions as a finite graph is by writing {V : Type} (Vfinite : Fintype V) (G : SimpleGraph V) (finsetEdgeset : Finset G.edgeSet) as part of the given lemma's hypothesis. Cardinality can then be accessed with finsetEdgeset.card & Vfinite.card
-- This is my current proof of the of (1,2,3,4) -> (5), which is complete for the base case. This base case proof is however, is contingent on a reuse of the inductive hypothesis (Size of vertex set is 1), which I do not know how to restate
lemma twoElemsInSetMeansCardGTOne {V : Type} (VFinset : Finset V) (x y : VFinset) (h: x ≠ y)
  : VFinset.card > 1 := by
  by_contra h1
  rw [gt_iff_lt] at h1
  rw [not_lt] at h1
  simp_all only [ne_eq] -- not needed?
  interval_cases value : VFinset.card
  · simp_all [zero_le] -- break down
    have V_Nonempty : Nonempty VFinset := by
      exact Nonempty.intro x
    apply Fintype.card_ne_zero at V_Nonempty
    subst value
    simp_all only [Finset.not_mem_empty, Fintype.card_ofIsEmpty, ne_eq, not_true_eq_false]
  · simp_all only [le_refl] -- break down
    rw [VFinset.card_eq_one] at value -- set is size one means there must be one element that is the whole set
    obtain ⟨w, h1⟩ := value
    obtain ⟨x_val, x_prop⟩ := x -- break down x and y into their value and membership relation
    obtain ⟨y_val, y_prop⟩ := y
    simp_all only [Subtype.mk.injEq] -- break down
    simp_all only [Finset.mem_singleton, not_true_eq_false] -- break down


lemma oneVertexbutEdgeIsFalse {V : Type} (VFinset : Finset V) (G : SimpleGraph VFinset) (e : Sym2 VFinset) (h : e ∈ G.edgeSet) (h1 : VFinset.card = 1)
  : False := by
  obtain ⟨x, y⟩ := e
  let h2 := (x = y)
  by_cases h2
  · rename_i h2_holds -- x = y
    simp_all only [h2]
    subst h2_holds
    obtain ⟨x_val, x_property⟩ := x
    simp_all only [SimpleGraph.mem_edgeSet, SimpleGraph.irrefl]
  · rename_i h2_not_holds -- x ≠ y
    simp_all only [SimpleGraph.mem_edgeSet, h2]
    have h3 : (VFinset.card > 1) := by
      apply twoElemsInSetMeansCardGTOne VFinset x y h2_not_holds
    simp_all only [gt_iff_lt, lt_self_iff_false]

lemma onetwothreefour_implies_five_part2 {V : Type} (VFinset : Finset V) (G : SimpleGraph VFinset) (FinEdgeSet : Finset G.edgeSet) (g_is_connected : G.Connected):
    (FinEdgeSet.card = VFinset.card - 1) := by
  -- damiano said to use unfold to solve edgeset size conundrum
  --We prove |E(T)| = |V (T)| − 1 by induction on n = |V (T)|.
  induction (VFinset.card - 1) with-- equiv to starting at 1?
  -- For n = 1, 2, true.
  -- proof says for 2, do i need this? guess I shall find out
  | zero     =>
  by_contra h -- suppose the edgeset is non empty
  apply nat_not_zero_implies_gt_one at h -- then the edgeset has a positive value
  simp_all only [Nat.succ_eq_add_one, Nat.exists_eq_add_one]-- BREAK THIS DOWN LATER ( I GUESS JUST TRY TO D THIS FOR ALL SIMP ALLS)
  simp_all only [Finset.card_pos]
  apply Finset.Nonempty.exists_mem at h
  simp_all only [Subtype.exists]
  obtain ⟨w, h⟩ := h
  obtain ⟨w_1, h⟩ := h
  have ind_hyp : VFinset.card = 1 := by sorry -- this is our inductive hypothesis, how do I abstract this?
  exact oneVertexbutEdgeIsFalse VFinset G w w_1 ind_hyp

 -- x is either y or not

  -- if x = y then we have an edge from x to yo
  -- both in V
  -- but size of V is
  -- Assume true for less than n vertices
  -- let T be a tree with n vertices
  | succ y hy =>
  subst hy
  simp_all only [self_eq_add_right, one_ne_zero]
  sorry
  -- UNUSED: let T' := (G.deleteEdges (putEdgeInSet (e)))

  -- let e = ab be an edge in T.

  -- By (3), T − e is disconnected.

  --Let T1 and T2 be connected components of T − e.
  --Obviously, T1 and T2 are trees.

  --Since each of them has fewer vertices than T, we know that |E(T1)| = |V (T1)| − 1

  -- and |E(T2)| = |V (T2)| − 1.

  --We also know that |V (T)| = |V (T1)| + |V (T2)|

  --and |E(T)| = |E(T1)| + |E(T2)| + 1.

  --Therefore, |E(T)| = |(V (T1)| − 1 + |V (T2)| − 1) + 1 = |V (T)| − 2 + 1 = |V (T)| − 1, as required.

  done
