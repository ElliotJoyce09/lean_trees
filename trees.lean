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
