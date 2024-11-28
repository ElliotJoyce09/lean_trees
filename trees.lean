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

def putEdgeInSet {V : Type} (x : Sym2 V) : Set (Sym2 V) := -- places the given edge (as a Sym2 V) into a set on its own
  {x}

-- I did this for elliot:
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

-- This exists until whomever is responsible for this proves it
lemma three_implies_T_without_e_disconnected {V : Type} [Finite V] (G : SimpleGraph V) (e : Sym2 V) -- e might not be an edge???
 : ¬(G.deleteEdges (putEdgeInSet (e))).Connected  := by
  sorry
  done

-- Want to show that the first four sections of the theorem holding imply the graph is connected
lemma onetwothreefour_implies_five_part1 {V : Type} (G : SimpleGraph V) (G_is_tree : isTree G) : --we only need G is a tree (From part 1 of the theorem) for this, so don't take uneccessary assumptions
    (G.Connected) := by
  unfold isTree at G_is_tree -- as G is a tree we see it is connected and acylic
  simp [G_is_tree] -- G being connected is exactly what we need
  done

lemma twoElemsInSetMeansCardGTOne {V : Type} [Finite V] (G : SimpleGraph V) (x y : V) (h : x ≠ y) (h_x : x ∈ (Fintype.ofFinite V).elems) (h_y : y ∈ (Fintype.ofFinite V).elems)
  : (Fintype.ofFinite V).card > 1 := by
  by_contra h1 -- suppose |V (G)| is not less than one

  rw [gt_iff_lt] at h1
  rw [not_lt] at h1 -- we see this is equivalent to supposing it ≤ 1
  simp_all only [ne_eq] -- rewrite the hypothesis h : x ≠ y for later computations

  interval_cases cardinality_V : (Fintype.ofFinite V).card -- as |V (G)| ≤ 1 and is a natural number, we see it is either 0 or 1
  -- if |V (G)| = 0
  · simp_all [zero_le]
    have V_Nonempty : Nonempty V := by -- we see that V is nonempty by the existance of x of type V
      exact Nonempty.intro x
    simp_all only [Fintype.card_ne_zero] -- so V is nonempty & is has cardinality 0, this is a contradiction
  -- if |V (G)| = 1
  · simp_all only [le_refl]
    unfold Fintype.card at cardinality_V -- we unfold (Fintype.ofFinite V).elems.card to be closer to Fintype.elems, which we know x and y are in
    unfold Finset.univ at cardinality_V
    rw [(Fintype.ofFinite V).elems.card_eq_one] at cardinality_V -- set is size one means there must be one element that is the whole set i.e V is a singleton
    obtain ⟨w, h1⟩ := cardinality_V -- we split the relation we have acquired from the cardinality of V(G) into the element and the defintion of (Fintype.ofFinite V).elems
    simp_all only [Finset.mem_singleton, not_true_eq_false] -- as x and y are both in this set, which we have shown has only one element, we get a contradiction, and the proof is done.

lemma nat_minus_one_eq_zero_implies_eq_one {x : ℕ} (h : x - 1 = 0) (neq: x ≠ 0) : x = 1 := by
  have gt_0 : x > 0 := by
    exact Nat.zero_lt_of_ne_zero neq
  have one_gt_0 : 1 > 0 := by
    exact Nat.one_pos
  exact Eq.symm (Nat.sub_one_cancel one_gt_0 gt_0 (id (Eq.symm h)))

lemma oneVertexbutEdgeIsFalse {V : Type} [v_is_finite : Finite V] (G : SimpleGraph V) (e : Sym2 V) (h : e ∈ G.edgeSet) (h1 : (Fintype.ofFinite V).card = 1)
  : False := by
  obtain ⟨x, y⟩ := e -- we split our edge into each its end points
  let h2 := (x = y)
  by_cases h2 -- These points are either equal to eachother, or different
  -- If x = y
  · rename_i h2_holds
    simp_all only [h2]
    subst h2_holds
    simp_all only [SimpleGraph.mem_edgeSet, SimpleGraph.irrefl] -- we then get an edge from a vertex to itself, a contradition to the irreflexivity property of simple graphs

  -- If x ≠ y
  · rename_i h2_not_holds
    simp_all only [SimpleGraph.mem_edgeSet, h2]
    -- we prove x and y are both in (Fintype.ofFinite V).elems, which is clearly true
    have h_x : (x ∈ (Fintype.ofFinite V).elems) := by
      exact (Fintype.ofFinite V).complete x

    have h_y : (y ∈ (Fintype.ofFinite V).elems) := by
      exact (Fintype.ofFinite V).complete y

    have h3 : ((Fintype.ofFinite V).card > 1) := by
      apply twoElemsInSetMeansCardGTOne G x y h2_not_holds h_x h_y -- this is a proof of our h3

    simp_all only [gt_iff_lt, lt_self_iff_false] -- h1 & h3 contradict eachother, so we have accquired the desired result

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

def connectedComponentToSimpleGraph {V : Type} [Finite V] (G : SimpleGraph V) (connComponent : Set V): G.Subgraph :=
  { verts := connComponent
    Adj := fun (x y) => G.Adj x y ∧ (x ∈ connComponent) ∧ (y ∈ connComponent)
    adj_sub := by
      intro v w a
      simp_all only
    edge_vert := by
      intro v w a
      simp_all only
    symm := by
      intro v w properties
      simp_all only [and_self, and_true]
      obtain ⟨GAdj, properties⟩ := properties
      exact id (SimpleGraph.adj_symm G GAdj)
  }

theorem onetwothreefour_implies_five_part2 {V : Type} [Finite V] (G : SimpleGraph V) (g_is_connected : G.Connected) (nonempty: Nonempty V):
    ((Fintype.ofFinite G.edgeSet).card = (Fintype.ofFinite V).card - 1) := by
--We prove |E(G)| = |V (G)| − 1 by induction on n = |V (G)|.
 -- `generalize` creates a "new" variable `nV` which can then be used for induction
 generalize hnV : (Fintype.ofFinite V).card - 1 = nV
 -- you may have to split out the case where `(Fintype.ofFinite V).card = 0`, though. TO DO
 induction nV with -- equiv to starting at |V (G)| = 1
  --We prove |E(G)| = |V (G)| − 1 by induction on n = |V (G)|.
  | zero     =>
  by_contra h -- Suppose |E (G)| is non empty

  apply Nat.exists_eq_succ_of_ne_zero at h -- Then |E (G)| has value succ k for some k ∈ ℕ
  simp_all only [Nat.succ_eq_add_one, Nat.exists_eq_add_one] -- Then |E (G)| > 0

  unfold Fintype.card at h
  unfold Finset.univ at h

  simp_all only [Finset.card_pos]
  apply Finset.Nonempty.exists_mem at h
  simp_all only [Subtype.exists]

  obtain ⟨w, h⟩ := h
  obtain ⟨w_1, h⟩ := h
  have nonzero:  (Fintype.ofFinite V).card ≠ 0 := by
    simp_all only [ne_eq, Fintype.card_ne_zero, not_false_eq_true] -- DONT LIKE THIS
  have ind_hyp : (Fintype.ofFinite V).card = 1 := by  -- Clearly this holds, as |V (T)| = 1 is what I am assuming for the zero section of the induction,
    exact nat_minus_one_eq_zero_implies_eq_one hnV nonzero
  exact oneVertexbutEdgeIsFalse G w w_1 ind_hyp
  -- Now must prove it holds for |V (G)| − 1 = n + 1 if it holds for |V (G)| − 1 = n
  | succ y hy =>

  have NonemptyEdgeset : (Nonempty G.edgeSet) := by -- We need the edgeset to be nonempty, as G is connected and we have more than one vertex, this is true
    have card_not_zero : (Fintype.ofFinite V).card > 1 := by -- this follows from us being in the inductive step
      exact Nat.lt_of_sub_eq_succ hnV

    by_contra no_edges -- Suppose the edgeset is not nonempty

    have edgeSet_is_emptySet : G.edgeSet = ∅ := by -- That is to say, it is the empty set
      exact Set.not_nonempty_iff_eq_empty'.mp no_edges -- This is a natural result of having no edges

    have g_is_empty_graph : G = emptyGraph V := by -- Having an empty edge set is the same as being the empty graph, so this is true
      rw [SimpleGraph.edgeSet_eq_empty] at edgeSet_is_emptySet -- This falls out of some lemmas already in SimpleGraph.Basic
      rw [SimpleGraph.emptyGraph_eq_bot]
      exact edgeSet_is_emptySet

    have not_connected : ¬ G.Connected := by -- As the empty graph is on a finite type with cardinality > 1, there are two edges in the empty graph, thus it cannot be connected

      by_contra suppose_G_connected -- suppose it is connected

      have two_elems_in_V :  ∃ x y : V, x ≠ y := by -- as (Fintype.ofFinite V).card > 1 there are at least two distinct elements in V, must prove this

        by_contra all_same_elem -- suppose not, then if an element is in V then it is the same element
        simp [not_exists] at all_same_elem

        have V_is_one_elem : ∃ v : V, (∀ u : V,  v = u) := by -- Want to show that there is a specific value in V that all of its elements take, and we call this V

          by_contra not_just_v -- Suppose this is not true, this means there is not such a V, thus there must be two elements in V with differing values

          have elem_exists_in_V : ∃ v : V, v ∈ (Fintype.ofFinite V).elems := by -- We know there is at least one element in V, this follows from its cardinality being greater than one

            have nonempty_finset_V : Nonempty (Fintype.ofFinite V).elems := by -- The finset that is associate with the Fintype we gain from our Finite V is nonempty, as V is nonempty

              by_contra is_empty -- Suppose not, that is to say this set is empty

              simp_all only [nonempty_subtype, not_exists] -- Then there does not exist an element v : V, such that v is in this set
              have V_empty : ¬ Nonempty V := by -- This implies that V is empty
                exact not_nonempty_iff_imp_false.mpr all_same_elem
              exact V_empty nonempty -- But we know V is nonempty, a contradiction

            exact nonempty_subtype.mp nonempty_finset_V -- As (Fintype.ofFinite V).elems is nonempty, it follow there exists an element of V in it, and thus an element in V

          obtain ⟨a, a_prop⟩ := elem_exists_in_V -- let a be this element, and a_prop its membership property

          have other_elem_exists : ∃ b : V, a ≠ b := by -- We see there is another b : V not equal to a, as this is the result of  not_just_v
            rw [not_exists] at not_just_v
            simp_all only [forall_const]

          obtain ⟨b, a_b_ineq⟩ := other_elem_exists -- let b be this other element, and a_b_ineq its relation to a

          have a_eq_b : a = b := by -- Our other assumption, that all the elements in V are the same, tells us that a and b are equal
            exact all_same_elem a b

          exact a_b_ineq (all_same_elem a b) -- Thus a = b & a ≠ b, which is impossible, so we found a contradiction and ∃ v : V, (∀ u : V,  v = u)

        have V_card_one : (Fintype.ofFinite V).card = 1 := by -- As we have shown V is all the same element, its cardinality is clearly one
          obtain ⟨w, h⟩ := V_is_one_elem -- obtain this single element
          exact (Fintype.ofFinite V).card_eq_one_of_forall_eq fun j => all_same_elem j w -- Apply a property of Fintypes to close the goal

        simp_all only [reduceCtorEq] -- WHAT DOES THIS DO!!!!!!! TO DO TO DO TO DO
        --So we have shown there exist two element in V, not equal to eachother

      obtain ⟨x, prop⟩ := two_elems_in_V -- Let x be this first element
      obtain ⟨y, prop⟩ := prop -- Let y be the second, and let prop be their relation

      have no_path : ¬ (G.Reachable x y) := by -- As x and y are not the same element of V and G is the empty graph, there is no edges at either of them
                                               -- thus there does not exist a path between them
        rw [SimpleGraph.emptyGraph_eq_bot] at g_is_empty_graph -- The proof falls out of properies of the empty graph
        simp_all only [SimpleGraph.reachable_bot]
        rw [not_false_eq_true]
        trivial

      have every_elem_in_V_connected_in_G : ∀ m n : V, G.Reachable m n := by -- Want to show there exists a path in G between all pairs of V
        have G_preconnected : G.Preconnected := by -- Preconnected means every pair of vertices is reachable from one another. It falls out of the defintion of connectivty in matlib
          exact g_is_connected.preconnected
        unfold SimpleGraph.Preconnected at G_preconnected -- We can see Preconnected is the same as our goal, so we are done
        exact G_preconnected

      exact no_path (every_elem_in_V_connected_in_G x y) -- This contradicts the lack of path we found between x and y, thus we have found our contradiction and G must not be connected

    exact not_connected g_is_connected -- Have proved G is not connected here, but we know it is, thus the edgeset cannot be empty

  have exist_elem_in_G : ∃ e : Sym2 V, e ∈ G.edgeSet := by
    exact nonempty_subtype.mp NonemptyEdgeset

  obtain ⟨e_val, e_prop⟩ := exist_elem_in_G

  have three_result : (¬(G.deleteEdges (putEdgeInSet (e_val))).Connected) := by -- we acquire the result that 3 already holding gives us
    exact three_implies_T_without_e_disconnected G e_val -- ie By (3), T − e is disconnected.

  --simp_all only [nonempty_subtype] This messes with hy
  let G_e_removed := G.deleteEdges (putEdgeInSet (e_val)) -- this is G without the edge e

  obtain ⟨e_val_1, e_val_2⟩ := e_val
  -- Let T1 and T2 be connected components of T − e.

  let G_1_connComponent := G_e_removed.connectedComponentMk e_val_1 -- as removing e disconnects G, and the rest of G is connected, we now have two connected components in this new graph
  let G_2_connComponent := G_e_removed.connectedComponentMk e_val_2 -- each of these contains exactly one endpoint of e, so we can simply find the connected components containing each of them

  let G_1_verts := G_1_connComponent.supp -- To do this we use the built in method to find the connectedComponents then take all the vertices in the component as a set
  let G_2_verts := G_2_connComponent.supp

  let G_1_subgraph := connectedComponentToSimpleGraph G G_1_verts -- Then create subgraph of all vertices in this component (We need this as connectedComponent is not naturally a graph)
  let G_2_subgraph := connectedComponentToSimpleGraph G G_2_verts

  let G_1 := SimpleGraph.Subgraph.coe G_1_subgraph-- Subgraphs are not Simple Graphs in lean, so must use coersion to turn them into Simple Graphs
  let G_2 := SimpleGraph.Subgraph.coe G_2_subgraph

  have G_1_isTree : isTree G_1 := by
    have connected : G_1.Connected := by
      --connected as is connected compomponent
      sorry
    have acylic : isAcyclic G_1 := by
      -- acyclic as subgraphs of G acyclic
      sorry
    unfold isTree
    exact ⟨connected, acylic⟩

  have G_2_isTree : isTree G_2 := by
    have connected : G_2.Connected := by
      --connected as is connected compomponent
      sorry
    have acylic : isAcyclic G_2 := by
      -- acyclic as subgraphs of G acyclic
      sorry
    unfold isTree
    exact ⟨connected, acylic⟩

  -- from notes: Since each of them has fewer vertices than T, we know that |E(T1)| = |V (T1)| − 1 & |E(T2)| = |V (T2)| − 1.
  let G_1_vertSetSize : ℕ := (Fintype.ofFinite G_1_verts).card -- Number of vertices in G_1
  let G_1_edgeSetSize : ℕ := (Fintype.ofFinite G_1.edgeSet).card -- Number of edges in G_1

  -- from notes: We also know that |V (T)| = |V (T1)| + |V (T2)| and |E(T)| = |E(T1)| + |E(T2)| + 1.
  let G_2_vertSetSize : ℕ := (Fintype.ofFinite G_2_verts).card -- Number of vertices in G_2
  let G_2_edgeSetSize : ℕ := (Fintype.ofFinite G_2.edgeSet).card -- Number of edges in G_2

  have h_G_1 : (G_1_edgeSetSize = G_1_vertSetSize - 1) := by
    -- has less vertices
    -- inductive hypothesis
    sorry

  have h_G_2 : (G_2_edgeSetSize = G_2_vertSetSize - 1) := by
    -- has less vertices
    -- inductive hypothesis
    sorry

  have vertSetEquality : (Fintype.ofFinite V).card = G_1_vertSetSize + G_2_vertSetSize := by
    -- follows from how they were made
    sorry

  have edgeSetEquality : (Fintype.ofFinite G.edgeSet).card = G_1_edgeSetSize + G_2_edgeSetSize + 1 := by
    -- follows from def, may be hard to get.... this suuuuuucks
    sorry

  rw [h_G_1, h_G_2] at edgeSetEquality
  
  --Therefore, |E(T)| = |(V (T1)| − 1 + |V (T2)| − 1) + 1 = |V (T)| − 2 + 1 = |V (T)| − 1, as required.

  sorry

/- Unused I think? could be useful DONT DELETE
theorem edgeOfSubgraphIsEdgeOfParent {V : Type} [Finite V] (G G' : SimpleGraph V) (h_subgraph : G' ≤ G) (e : Sym2 V) (h : e ∈ G'.edgeSet) : (e ∈ G.edgeSet) := by -- a proof that if we have a subgraph G' of G, and e an edge of G', then e is an edge of G also
  by_contra h1
  obtain ⟨e_1, e_2⟩ := e
  simp_all only [SimpleGraph.mem_edgeSet]
  exact h1 (h_subgraph h)
-/

lemma edgeInCycleMeansEdgeInGraph {V : Type} [Finite V] (G : SimpleGraph V) {v : V} (p : G.Walk v v) {e : Sym2 V} (e_in_path : e ∈ p.edges)
  : e ∈ G.edgeSet := by
  exact SimpleGraph.Walk.edges_subset_edgeSet p e_in_path

lemma deletingEdgeMeansNotInEdgeSet {V : Type} [Finite V] (deletedEdges : Set (Sym2 V)) {G G' : SimpleGraph V} (h: G' = G.deleteEdges deletedEdges) {e : Sym2 V} (e_member : e ∈ deletedEdges)
: e ∉ G'.edgeSet := by
  by_contra contra_h
  subst h
  sorry -- THIS IS SO OBVIOUSLY TRUE, I AM GOING TO KILL MYSELF

lemma not_in_FinsetEdgeSet_equals_not_in_edgeSet {V : Type} [Finite V] (G : SimpleGraph V) [Fintype G.edgeSet] (e : Sym2 V): e ∉ G.edgeSet ↔ e ∉ G.edgeFinset := by
  rw [Set.mem_toFinset]

lemma subset_and_neq_means_card_le {U : Type} [Finite U] (A B : Finset U) (subset : A ⊆ B) (not_equal : A ≠ B) : (A.card < B.card):= by
  have A_strict_subset : A ⊂ B := by
    exact HasSubset.Subset.ssubset_of_ne subset not_equal
  exact Finset.card_lt_card A_strict_subset

lemma Finset_subset_and_has_less_elems_implies_not_equal {U : Type} (A B : Finset U) (subset : A ⊆ B) (x : U) (h1 : x ∈ B) (h2 : x ∉ A) : A ≠ B := by
  by_contra equal -- suppose A = B
  subst equal -- Then x is in A and not in A
  exact h2 (subset (subset (subset h1))) -- contradiction, so we are done

lemma subgraphImpliesLeqEdges {V : Type} [Finite V] (deletedEdges : Set (Sym2 V)) {G G' : SimpleGraph V} (G_finiteEdgeSet : Fintype G.edgeSet) (h : G' = G.deleteEdges deletedEdges) (subGraph: G' ≤ G) (G'_finiteEdgeSet : Fintype G'.edgeSet)  (subset_of_G_edges : deletedEdges ⊆ G.edgeSet) (h1 : Nonempty deletedEdges)
: (G'.edgeFinset).card < (G.edgeFinset).card := by
  simp_all only [nonempty_subtype] -- there is an element in deletedEdges (as Nonempty)
  obtain ⟨deletedEdge_edge, deletedEdge_prop⟩ := h1

  have edge_not_in_G' : deletedEdge_edge ∉ G'.edgeFinset := by -- this element has been deleted from G', so is not in its edgeFinset
    have not_in_edgeSet : deletedEdge_edge ∉ G'.edgeSet := by
      exact deletingEdgeMeansNotInEdgeSet deletedEdges h deletedEdge_prop
    exact (not_in_FinsetEdgeSet_equals_not_in_edgeSet G' deletedEdge_edge).mp not_in_edgeSet

  have edge_in_G : deletedEdge_edge ∈ G.edgeFinset := by -- We can see there is at least one edge in the edgeFinset of G
    exact SimpleGraph.mem_edgeFinset.mpr (subset_of_G_edges deletedEdge_prop)

  have G'_edgeFinset_is_subset : G'.edgeFinset ⊆ G.edgeFinset := by -- As G' is a subgraph of G, the edgeset of G' is also a subset of G, by def. of a subgraph
    rw [Set.subset_toFinset]
    rw [Set.coe_toFinset] -- we see this is equivalent to the edgesets being subsets
    rw [SimpleGraph.edgeSet_subset_edgeSet] -- and our subgraph assumption is definitionally equivalent to the edgesets being subsets
    simp_all only [Set.mem_toFinset] -- RIDDLE ME THIS

  have edgeFinsets_neq : G.edgeFinset ≠ G'.edgeFinset := by
    exact
      Ne.symm
        (Finset_subset_and_has_less_elems_implies_not_equal G'.edgeFinset G.edgeFinset
          G'_edgeFinset_is_subset deletedEdge_edge edge_in_G edge_not_in_G')
  exact
    subset_and_neq_means_card_le G'.edgeFinset G.edgeFinset G'_edgeFinset_is_subset
      (id (Ne.symm edgeFinsets_neq))

theorem five_implies_onetwothreefour_acyclic_part1 {V : Type} [Finite V] (G : SimpleGraph V) (g_is_connected : G.Connected) (edge_vert_equality: (Fintype.ofFinite G.edgeSet).card = (Fintype.ofFinite V).card - 1) :
  (isAcyclic G) := by

  by_contra not_acyclic-- suppose that G is not acyclic, that is it has a cycle

  --this isn't quite right, it will delete all edges in acycle, rather than just one

  --  TO DO Say what this is:
  let deleteableEdgeSets := { eSet : Set (Sym2 V) | (G.deleteEdges eSet).Connected ∧ (isAcyclic (G.deleteEdges eSet)) ∧ (∀ e ∈ eSet, e ∈ G.edgeSet)} -- there are multiple of these sets, but can just take one

  have deleteableEdgeSets_Nonempty : Nonempty deleteableEdgeSets := by
    by_contra no_set_exists
    simp_all [deleteableEdgeSets]
    sorry
    -- This is essentially a proof that each connected graph has a minimum spanning tree, MIGHT NOT BE MINIMUM SPANNING TREE BUT SOME OTHER CONCEPT
    -- which is a true statement. However, this proof is outside the scope of this project, and have used sorry here,

  have exists_element_in_deleteableEdgeSets : ∃ edgesToDelete : Set (Sym2 V), edgesToDelete ∈ deleteableEdgeSets := by
    exact nonempty_subtype.mp deleteableEdgeSets_Nonempty

  obtain ⟨edgesToDelete, edgesToDelete_rel⟩ := exists_element_in_deleteableEdgeSets
  let G_0 := G.deleteEdges edgesToDelete

  have G_0_subgraph : G_0.IsSubgraph G := by -- G_0 is clearly a subgraph, as we have only removed edges that were already in G
    exact SimpleGraph.deleteEdges_le edgesToDelete
  rw [SimpleGraph.isSubgraph_eq_le] at G_0_subgraph

  have G_0_connected : G_0.Connected := by -- G_0 is also clearly connected, as it is a subgraph of a connected grpah and its contrsuction did not break connectivity
    simp_all only [Set.coe_setOf, nonempty_subtype, Set.mem_setOf_eq, SimpleGraph.isSubgraph_eq_le, deleteableEdgeSets, G_0] -- DO NOT LIKE THIS!!!!!!!!!!

  have G_0_acyclic : isAcyclic G_0 := by
    simp_all only [deleteableEdgeSets, G_0]
    simp_all only [Set.mem_setOf_eq] -- DO NOT LIKE THIS!!!!!!!!!!

    -- TO DO I kinda want to make this work becasue (somehow) it makes more sense and is very close to done
    /-
    by_contra supposeNotAcyclic -- suppose ∃ a cycle in G_0 (this cannot be true as, by definition, we have removed all edges from it that create a cycle
    unfold isAcyclic at supposeNotAcyclic
    simp at supposeNotAcyclic
    unfold hasACycle at supposeNotAcyclic -- we see that if the graph is not acylic then there must exist a path in G_0 that is a cycle
    obtain ⟨v, cycle_property⟩ := supposeNotAcyclic -- we can attain this cycle and a vertex v which it is said to start and end at
    obtain ⟨cycle, cycle_property⟩ := cycle_property -- we break down this cycle into the fact is is a walk along G_0, and also a cycle

    have h : ¬ (∃ e : Sym2 V, e ∈ edgesToDelete ∧ (e ∈ cycle.edges)) := by -- Want to show that there cannot be an edge both in this cycle and in the set of edges deleted from G to create G_0
      by_contra share_an_edge -- Suppose this is not true, that there is such an edge
      obtain ⟨shared_edge, share_an_edge⟩ := share_an_edge  -- shared_edge is this edge
      obtain ⟨edge_in_edgesToDelete, edge_in_G_0_cycle⟩ := share_an_edge -- we gain the both membership properties that this edge has

      have edge_in_G_0 : shared_edge ∈ G_0.edgeSet := by -- This edge is in the edgeset of G_0, as it is in a cycle within this Graph
        exact edgeInCycleMeansEdgeInGraph G_0 cycle edge_in_G_0_cycle -- A proof that if a graph contains a cycle, and we have an edge in that cycle, the edge is in the graph

      have edge_not_in_G_0 : shared_edge ∉ G_0.edgeSet := by -- This edge is NOT in the edgeset of G_0, as it is in "edgesToDelete", the set of edges deleted in G_0 at its construction
        have equality : G_0 = G.deleteEdges edgesToDelete := by -- A trivial property needed for the theorem used below
          rfl
        exact deletingEdgeMeansNotInEdgeSet edgesToDelete equality edge_in_edgesToDelete -- A proof that if a graph is the same as deleting a set of edges from another graph, then a deleted edge is not in the graph

      exact not_acyclic fun a => edge_not_in_G_0 edge_in_G_0 -- So the edge is both in and not in the edgeset of G_0, a clear contradiction

    let cycle_in_G := SimpleGraph.Walk.mapLe G_0_subgraph cycle -- As  G_0 is a subgraph of G, we see that "cycle" is also a Walk/Path that can be found in G

    have cycle_in_G_is_cycle : cycle_in_G.IsCycle := by -- G_0 is also a cycle in G, as nothing has changed about it in G
      simp only [cycle_in_G]
      simp only [SimpleGraph.Walk.mapLe_isCycle]
      exact cycle_property

    -- now must show one of the edges in the cycle is also in edgesToDelete (true by defition)
    have h1 : ∃ e ∈ cycle_in_G.edges, e ∈ edgesToDelete := by
      -- edgesToDeleete
      -/


    -- get this edge
    -- edge is also in cycle.edge
    -- contradiction
    -- boom
  have G_0_is_Tree : isTree G_0 := by --Clearly, G0 is a tree, since deletion of an edge from a cycle cannot destroy the connectivity.

    have G_0_Acylic_and_Connected : G_0.Connected ∧ (isAcyclic G_0) := by -- combine our two previous proofs into one statement
     simp_all only [and_self]

    unfold isTree -- we can unfold the defintion of isTree to see it is exactly this statement
    exact G_0_Acylic_and_Connected -- thus, we are done

  have edgeSet_less_than : (Fintype.ofFinite G_0.edgeSet).card < (Fintype.ofFinite G.edgeSet).card := by

    have G_edgeSet_Fintype : Fintype G.edgeSet := by -- We must first acquire a series of properties for the intended lemma, most of these are trivial
      exact Fintype.ofFinite ↑G.edgeSet

    have G_0_edgeSet_Fintype : Fintype G_0.edgeSet := by
      exact Fintype.ofFinite ↑G_0.edgeSet

    have value_of_G_0 : G_0 = G.deleteEdges edgesToDelete := by
      exact rfl

    have edgesToDelete_subset_of_G_edges : edgesToDelete ⊆ G.edgeSet := by
      simp_all only [Set.mem_setOf_eq, true_and, deleteableEdgeSets] -- EXPLAIN ME BREAK DOWN
      exact edgesToDelete_rel

    have nonempty_edgesToDelete : Nonempty edgesToDelete := by
      by_contra empty -- assume edgesToDelete is not Nonempty
      apply Set.not_nonempty_iff_eq_empty'.mp at empty -- That is, it is the empty set

      have G_Acylic : isAcyclic G := by -- G' = G, as we are deleting and empty set from , and G' is acylclic, so G is acylic
        simp_all only [SimpleGraph.deleteEdges_empty]
      exact not_acyclic G_Acylic -- So G is acyclic and not acyclic, a contradiction

    have finset_less_than : G_0.edgeFinset.card < G.edgeFinset.card := by
      exact subgraphImpliesLeqEdges edgesToDelete G_edgeSet_Fintype value_of_G_0 G_0_subgraph G_0_edgeSet_Fintype edgesToDelete_subset_of_G_edges nonempty_edgesToDelete
    #check Finset
    have G_0_edgeFinset_card_eq_edgeSet_card : (Fintype.ofFinite G_0.edgeFinset.toSet).card = G_0.edgeFinset.card := by
      simp_all only [Set.coe_setOf, nonempty_subtype, Set.mem_setOf_eq, true_and, Set.toFinset_card, Set.coe_toFinset,
        deleteableEdgeSets, G_0] -- FIX THIS
      sorry
      --might not actually hold
      -- one solution is to redo everything as Finset if I really think it is correct

    have G_edgeFinset_card_eq_edgeSet_card : G.edgeFinset.card = (Fintype.ofFinite G.edgeSet).card := by
      sorry

    simp_all only [Set.toFinset_card]

  have edge_vert_equality_G_0 : (Fintype.ofFinite G_0.edgeSet).card = (Fintype.ofFinite V).card - 1 := by -- We know that |E(G0)| = |V (G0)| − 1 as G0 is a tree, and thus we can apply our previous work
    have nonempty_V : Nonempty V := by -- this is requied for the usage of "onetwothreefour_implies_five_part2"
      exact g_is_connected.nonempty
    exact onetwothreefour_implies_five_part2 G_0 G_0_connected nonempty_V

  --On the other hand, we did not delete any vertex of G, i.e. |V (G0)| = |V (G)| (This does not need to be proved in lean by nature of G & G_0's construction).
  have h1 : (Fintype.ofFinite G_0.edgeSet).card = (Fintype.ofFinite G.edgeSet).card := by --Therefore, |E(T0)| = |V (G0))| − 1 = |V (T)| − 1 = |E(T)| and hence E(T0) = E(T), i.e. no edge has been deleted from T.
    simp_all only [G_0] -- follows from the assumption : edge_vert_equality

  simp_all only [lt_self_iff_false, G_0] --In other words, G is acyclic

theorem five_implies_onetwothreefour_part2 {V : Type} [Finite V] (G : SimpleGraph V) (g_is_connected : G.Connected) (edge_vert_equality: (Fintype.ofFinite G.edgeSet).card = (Fintype.ofFinite V).card - 1) :
  (isTree G) := by
  -- only need show G is Acylcic as we are given G is connected and G being a tree requires it to be Acylic and Connected
  have G_Acyclic : isAcyclic G := by exact five_implies_onetwothreefour_acyclic_part1 G g_is_connected edge_vert_equality
  have G_Acylic_and_Connected : G.Connected ∧ (isAcyclic G) := by simp_all only [and_self]
  unfold isTree
  exact G_Acylic_and_Connected
  done
