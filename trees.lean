import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Combinatorics.SimpleGraph.Basic

namespace trees

def hasACycle {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ (u : V), ∃ (p : G.Walk u u), p.IsCycle

def isAcyclic {V : Type} (G : SimpleGraph V) : Prop :=
  ¬ hasACycle G

def isTree {V : Type} (G : SimpleGraph V) : Prop :=
  G.Connected ∧ isAcyclic G

def isCycleAtV {V : Type} (G : SimpleGraph V) (v : V) : Prop := -- if there exists a cycle in G starting at v, then this is true
  ∃ (p : G.Walk v v), p.IsCycle

def secondVertexInWalk {V : Type} (G : SimpleGraph V) {v u : V} (p : G.Walk v u)  : V := -- returns the first vertex along a given walk from v to u in a graph G
  p.getVert 1

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

-- This is a stand in for the action proof
lemma three_implies_G_without_e_disconnected {V : Type} [Finite V] (G : SimpleGraph V) (e : Sym2 V)
 : ¬(G.deleteEdges (putEdgeInSet (e))).Connected  := by
  sorry

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

/--A proof that if x - 1 = 0 for some x, and x is not 0, then x = 1-/
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

def connectedComponentToSubGraph {V : Type} [Finite V] (G : SimpleGraph V) (connComponent : Set V): G.Subgraph :=
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

lemma edgeConversionG'CoeToG {V : Type} {G : SimpleGraph V} (G' : G.Subgraph) (x y : ↑G'.verts) (h : G'.coe.Adj ↑x y) : G.Adj x y := by
  simp_all only [SimpleGraph.Subgraph.coe_adj, SimpleGraph.Subgraph.coe_adj_sub]

def map_to_membership_or_sink {V : Type} {G : SimpleGraph V} {G' : G.Subgraph} (sink : ↑G'.verts) (v : V) : G'.verts := by
  let h := v ∈ G'.verts
  by_cases h
  · rename_i h_1
    simp_all only [h]
    exact ⟨v, h_1⟩
  · exact sink

def spanningCoeToCoeHom {V : Type} {G : SimpleGraph V} {G' : G.Subgraph} (sink : ↑G'.verts): G'.spanningCoe →g G'.coe  where
  toFun := fun v => map_to_membership_or_sink sink v

  map_rel' := by
    intro a b a_1
    simp_all only [SimpleGraph.Subgraph.spanningCoe_adj, SimpleGraph.Subgraph.coe_adj]
    unfold map_to_membership_or_sink
    simp_all only
    obtain ⟨val, property⟩ := sink
    split
    next h =>
      simp_all only
      split
      next h_1 => simp_all only
      next h_1 =>
        simp_all only
        have adj_implies_in_vert : b ∈ G'.verts := by exact G'.edge_vert (id (SimpleGraph.Subgraph.adj_symm G' a_1))
        exact False.elim (h_1 adj_implies_in_vert)
    next h =>
      simp_all only
      split
      next h_1 =>
        simp_all only
        have adj_implies_in_vert : a ∈ G'.verts := by exact G'.edge_vert a_1
        exact False.elim (h adj_implies_in_vert)
      next h_1 =>
        simp_all only
        have adj_implies_in_vert : a ∈ G'.verts :=
          by exact G'.edge_vert a_1
        exact False.elim (h adj_implies_in_vert)

lemma reachableByCompImpliesconnComp {V : Type} [Finite V] [Nonempty V] {G : SimpleGraph V} {G' : G.ConnectedComponent} {x : V} (h : G' = G.connectedComponentMk x) {y : V} (reachable : G.Reachable x y) : y ∈ G' := by
  subst h
  have same_component : G.connectedComponentMk x = G.connectedComponentMk y := by
    exact SimpleGraph.ConnectedComponent.sound reachable
  exact id (Eq.symm same_component)

lemma connected_component_coe_is_connected {V : Type} [Finite V] [Nonempty V] {G G_e_removed : SimpleGraph V} (x : V) {y : V} (h : s(x,y) ∈ G.edgeSet) (def_of_G_e : G_e_removed = G.deleteEdges (putEdgeInSet ( s(x,y) ) ) )
  : (connectedComponentToSubGraph G (G_e_removed.connectedComponentMk x).supp).coe.Connected := by

  let G'_connComponent := G_e_removed.connectedComponentMk x -- we recreate the variables in the goal so we can work our  way to the desired result
  let G'_verts := G'_connComponent.supp
  let G' := connectedComponentToSubGraph G G'_verts

  have h1 : G'_connComponent = Quot.mk G_e_removed.Reachable x := by -- we state our defintion of G'_connComponent for below and some lemmas used later on
    exact rfl
  have isNonempty : Nonempty ↑G'.verts := by -- We require this property, as connected means vertex set (Nonempty ↑G'.verts) nonempty & preconnected
  --it follows from V being nonempty and h1 stating there is an element in the set (x)
    simp_all only [nonempty_subtype]
    apply Exists.intro
    · exact h1

   -- As we know the vertex set is nonempty, must now show it is preconnected
  have isPreconnected : (connectedComponentToSubGraph G (G_e_removed.connectedComponentMk x).supp).coe.Preconnected := by
    by_contra not_preconnected -- Suppose it is not preconnected

    have h2 : ∀ a b : G'_verts, G_e_removed.Reachable a b := by -- I claim that we have all vertices in G' are connected by a path of edges in G_e_removed
      by_contra not_reachable -- suppose they are not as so

      simp_all [G'_connComponent]

      obtain ⟨vert_1, prop⟩ := not_reachable -- Then there exists (at least) one pair of vertices in G' that are not connected by a path
                                            -- We call this pair vert_1 and vert_2, and acquire their properties
      obtain ⟨vert_1_mem, prop⟩ := prop

      obtain ⟨vert_2, prop⟩ := prop

      obtain ⟨vert_2_mem, prop⟩ := prop

      unfold SimpleGraph.ConnectedComponent at G'_connComponent

      have reachable : G_e_removed.Reachable vert_1 vert_2 := by -- I claim there is a path between vert 1 and 2 (this would be a contradiction)

        have reachable1: G_e_removed.Reachable x vert_1 := by -- They are both reachable from x, by defintion of the connected component

          exact SimpleGraph.Reachable.symm (SimpleGraph.ConnectedComponent.exact vert_1_mem)

        have reachable2: G_e_removed.Reachable x vert_2 := by
        -- falls out of connected component I hope
          exact SimpleGraph.Reachable.symm (SimpleGraph.ConnectedComponent.exact vert_2_mem)

        exact SimpleGraph.Reachable.trans (id (SimpleGraph.Reachable.symm reachable1)) reachable2 -- Thus we can go from vert 1 to x to vert 2 and find a walk

      simp_all only [not_true_eq_false] -- Thus we have found a contradiction, and have proved this property

    have h3 : ∀ a b : G'_verts, G_e_removed.Reachable a b → G'.coe.Reachable a b := by -- We want to show that reachability of vertices in G_e_removed implies reachabiltiy in G'
      -- We will then be able to apply this with h2 to find a contradiction

      by_contra doesnt_hold
      simp [not_forall] at doesnt_hold -- Suppose not, that is to say, there exist a and b that are reachable in G_e_removed but not in G'.coe

      --There is a lot of information in "doesnt_hold", we must parcel it into different statements
      obtain ⟨a, doesnt_hold⟩ := doesnt_hold

      obtain ⟨a_mem, doesnt_hold⟩ := doesnt_hold

      obtain ⟨b, doesnt_hold⟩ := doesnt_hold

      obtain ⟨a_b_reachable, doesnt_hold⟩ := doesnt_hold

      obtain ⟨b_mem, doesnt_hold⟩ := doesnt_hold

      -- As a and b are reachable in G_e_removed, they are connected by a walk by defintion, and from this we obtain a path
      have exists_path : ∃ p : G_e_removed.Walk a b, p.IsPath := by

        rw [SimpleGraph.reachable_iff_nonempty_univ] at a_b_reachable -- reachability between a and b implies that the set of

        have exists_walk : ∃ w, w ∈ (Set.univ : Set (G_e_removed.Walk a b)) := by -- Nonempty implies there exists a member
          exact a_b_reachable

        obtain ⟨w, _⟩ := exists_walk -- obtain this walk and its property

        have V_has_DecidableEq : DecidableEq V := by -- This follows from the properties of V. It is needed for "toPath"
          exact Classical.typeDecidableEq V

        let p_path := SimpleGraph.Walk.toPath w -- convert this walk to a path (This is done by removing edges used twice)

        obtain ⟨p_path_walk, p_path_prop⟩ := p_path -- gain walk part of this path and its property

        exact Exists.intro p_path_walk p_path_prop -- Thus we have found a path of the desired patttern

      obtain ⟨path_a_b, path_is_path⟩ := exists_path -- Obtain the path between a and b ewe have proven to exist

      have all_edges_in_sub : ∀ e ∈ path_a_b.edges, e ∈ G'.edgeSet := by -- want to show all the edges of this path are also in the edgeSet of G'

        by_contra exists_edge_only_in_parent -- suppose not
        simp [not_forall] at exists_edge_only_in_parent -- that is, there exists an edge in the path not in G'.edgeSet

        obtain ⟨edge, edge_prop⟩ := exists_edge_only_in_parent -- obtain this edge and its properties
        obtain ⟨edge_in_path, edge_not_in_G'⟩ := edge_prop

        have edge_is_in_parent : edge ∈ G_e_removed.edgeSet := by -- we see this edge is in G_e_removed, as G' is a subgraph of it
          exact SimpleGraph.Walk.edges_subset_edgeSet path_a_b edge_in_path

        obtain ⟨edge_val_1, edge_val_2⟩ := edge -- obtain the edgepoints of this edge

        have edge_has_val_outside_of_G': edge_val_1 ∉ G'.verts ∨ edge_val_2 ∉ G'.verts := by -- I claim one of these must be not in G'
          by_contra both_in_G'verts -- suppose not, that is to say they are both in G'.verts

          have all_edges_of_verts_are_in_G' : ∀ i j : G'.verts, G.Adj i j → G'.Adj i j := by -- I claim that all edges between the vertices of G' in G are also in G'
            intro i j i_j_adj -- let i and j be any two adjacent vertices in G that are also in G'

            have in_conn_comp : ↑i ∈ G'_connComponent := by -- They are both in G'_connComponent by definition
              simp_all only [SetLike.coe_mem]
            have in_conn_comp : ↑j ∈ G'_connComponent := by
              simp_all only [SetLike.coe_mem]

            -- We must clarify the adjacency condition of G' (This can be observed in the defintion of Adj in connectedComponentToSubGraph)
            have G'Adj_def : ∀ t u : V, G.Adj ↑t ↑u ∧ (↑t ∈ G'_connComponent) ∧ (↑u ∈ G'_connComponent) ↔ G'.Adj ↑t ↑u := by
              intro relations
              exact fun u => Iff.symm (Eq.to_iff rfl)

            rw [← G'Adj_def] -- Rewrite our goal to be to fufil this condition
            simp_all only [and_self] -- We see we have already fufilled each of the properties of the statement

          simp_all only [SimpleGraph.mem_edgeSet, Subtype.forall, SimpleGraph.Subgraph.mem_edgeSet, SimpleGraph.deleteEdges_adj, not_or, not_not, not_true_eq_false]
          -- COMMENT THIS LATER

        have a_to_1 : G_e_removed.Reachable a edge_val_1 := by -- We see there is a path from a to edge_val_1

          have in_support : edge_val_1 ∈ path_a_b.support := by -- As the edge which edge_val_1 is an endpoint of is in the part from a to b
                                                                -- edge_val_1 is clearly a point along this path
            exact SimpleGraph.Walk.fst_mem_support_of_mem_edges path_a_b edge_in_path

          -- This states that a walk can be split up into two subwalks starting/ending at any point along the walk
          rw [SimpleGraph.Walk.mem_support_iff_exists_append] at in_support

          exact nonempty_of_exists in_support -- We can then take the sub-walk starting at a and ending at edge_val_1 to compelete the proof

        have a_to_2 : G_e_removed.Reachable a edge_val_2 := by -- We see there is a path from a to edge_val_2
          -- Method is same as above

          have in_support : edge_val_2 ∈ path_a_b.support := by --
            exact SimpleGraph.Walk.snd_mem_support_of_mem_edges path_a_b edge_in_path

          rw [SimpleGraph.Walk.mem_support_iff_exists_append] at in_support

          exact nonempty_of_exists in_support

        have in_conn_comp : edge_val_1 ∈ G'_connComponent  ∧ edge_val_2 ∈ G'_connComponent := by

          have x_to_a : G_e_removed.Reachable x a := by -- There is a path from x to a as they are both in the same connected component
            exact SimpleGraph.Reachable.symm (SimpleGraph.ConnectedComponent.exact a_mem)

          have inclusion_1 : edge_val_1 ∈ G'_connComponent := by

            have x_to_1 : G_e_removed.Reachable x edge_val_1 := by -- We can then find a path from x to edge_val_1 by going from x to a then to edge_val_1
              exact SimpleGraph.Reachable.trans x_to_a a_to_1

            -- We then invoke a lemma I proved, stating that if two points are reachable, then the latter (edge_val_1) is in the connected component of the former (x)
            exact reachableByCompImpliesconnComp h1 x_to_1

          have inclusion_2 : edge_val_2 ∈ G'_connComponent := by -- Same as above

            have x_to_2 : G_e_removed.Reachable x edge_val_2 := by
              exact SimpleGraph.Reachable.trans x_to_a a_to_2

            exact reachableByCompImpliesconnComp  h1 x_to_2

          exact ⟨inclusion_1, inclusion_2⟩ -- Thus we have both parts of our desired and stament

        have both_in_verts :  edge_val_1 ∈ G'.verts ∧ edge_val_2 ∈ G'.verts := by -- As both vertices are in the connected component, they are in G' by defintion
          exact in_conn_comp

        simp_all [or_self] -- This is a contradiction to edge_has_val_outside_of_G', so we are done

      let a_G' : ↑G'.verts := ⟨a, a_mem⟩ -- Let use reconstruct the points we have claimed are not reachable in G'.coe (Though we shall prove they are)
      let b_G' : ↑G'.verts := ⟨b, b_mem⟩

      have exists_walk : Nonempty (G'.coe.Walk a_G' b_G') := by -- might not even need thise

        have edge_map : ∀ e, e ∈ path_a_b.edges → e ∈ G'.edgeSet := by
          exact fun e a => all_edges_in_sub e a

        let p := SimpleGraph.Walk.transfer path_a_b G'.spanningCoe edge_map

        have reachable_in_spanning : G'.spanningCoe.Reachable a b := by
          exact SimpleGraph.Walk.reachable p

        have reachable_in_coe : G'.coe.Reachable a_G' b_G' := by
          let h := SimpleGraph.Reachable.map (spanningCoeToCoeHom a_G') reachable_in_spanning

          have hom_on_a : spanningCoeToCoeHom a_G' a = a_G' := by

            have eq : spanningCoeToCoeHom a_G' a = (map_to_membership_or_sink a_G' a) := by -- not right
              exact rfl

            unfold map_to_membership_or_sink at eq

            have eq1 : (map_to_membership_or_sink a_G' a) = a_G' := by
              simp_all only
              split at eq
              next h_4 => exact eq
              next h_4 => exact False.elim (h_4 a_mem)
            exact eq1

          have hom_on_b : spanningCoeToCoeHom a_G' b = b_G' := by

            have eq : spanningCoeToCoeHom a_G' b = (map_to_membership_or_sink a_G' b) := by -- not right
              exact rfl

            unfold map_to_membership_or_sink at eq

            have eq1 : (map_to_membership_or_sink a_G' b) = b_G' := by
              simp_all only
              split at eq
              next h_4 => exact eq
              next h_4 => exact False.elim (h_4 b_mem)
            exact eq1

          rw [hom_on_a, hom_on_b] at h
          exact h

        exact reachable_in_coe

      exact doesnt_hold exists_walk

    exact not_preconnected fun u v => h3 u v (h2 u v)
  exact SimpleGraph.Connected.mk isPreconnected -- G'.coe has Nonempty edgeset, is preconnected, and is exactly our desired graph, so we are done

def subgraph_to_graph_hom {V : Type} {G : SimpleGraph V} {G' : G.Subgraph} :  G'.coe →g G where
  toFun := fun
    | .mk val property => val
  map_rel' := by
    exact fun {a b} a_1 => edgeConversionG'CoeToG G' a b a_1

lemma subgraph_hom_eq_implies_eq {V : Type} {G : SimpleGraph V} {G' : G.Subgraph} (x y : G'.verts) (h : subgraph_to_graph_hom x = subgraph_to_graph_hom y) : x = y := by
  obtain ⟨val, property⟩ := x
  obtain ⟨val_1, property_1⟩ := y
  subst h
  simp_all only [Subtype.mk.injEq]
  rfl

lemma subgraph_hom_inj  {V : Type} {G : SimpleGraph V} {G' : G.Subgraph} : ∀ x y : G'.verts, subgraph_to_graph_hom x = subgraph_to_graph_hom y → x = y := by
  exact fun x y a => subgraph_hom_eq_implies_eq x y a

def Walk_map {V : Type} {G : SimpleGraph V} {G' : G.Subgraph} {x y : G'.verts} (G'_walk : G'.coe.Walk x y) : G.Walk x y :=
  SimpleGraph.Walk.map subgraph_to_graph_hom G'_walk

lemma conn_comp_acyclic {V : Type} [Finite V] [Nonempty V] {G G_e_removed : SimpleGraph V} (G_is_tree : isTree G)
  {x y : V} (h : s(x,y) ∈ G.edgeSet) (def_of_G_e : G_e_removed = G.deleteEdges (putEdgeInSet ( s(x,y) ) ) )
  : isAcyclic (connectedComponentToSubGraph G (G_e_removed.connectedComponentMk x).supp).coe := by
  have G_Acyclic : isAcyclic G := by
    unfold isTree at G_is_tree
    obtain ⟨conn, acyc⟩ := G_is_tree
    exact acyc

  unfold isAcyclic
  unfold hasACycle

  simp_all only [SimpleGraph.mem_edgeSet, Subtype.exists, not_exists]
  intro cycle_vert cycle_vert_rel cycle
  by_contra hasACycle
  let G_walk := Walk_map cycle

  have G_walk_is_Cycle : G_walk.IsCycle := by
    rw [← SimpleGraph.Walk.map_isCycle_iff_of_injective subgraph_hom_inj] at hasACycle
    exact hasACycle

  unfold isAcyclic at G_Acyclic
  unfold hasACycle at G_Acyclic
  simp [not_exists] at G_Acyclic
  simp_all only

lemma my_card_congr {α β} (a : Fintype α) (b : Fintype β) (f : α ≃ β) : Fintype.card α = Fintype.card β := by -- an adaptation of Fintype.card_congr where the two fintypes are entered explicitly (rather than implicitly)
  rw [← Fintype.ofEquiv_card f]; congr!

theorem my_set_fintype_card_eq_univ_iff (V : Fintype α) (s : Set α) [Fintype s] : -- same as above but for set_fintype_card_eq_univ_iff
    Fintype.card s = Fintype.card α ↔ s = Set.univ := by
  rw [← Set.toFinset_card, Finset.card_eq_iff_eq_univ, ← Set.toFinset_univ, Set.toFinset_inj]

lemma type_eq_set_iff_card_the_same {V : Type} [Finite V] (set : Set V) : (∀ v : V, v ∈ set) ↔ (Fintype.ofFinite set).card = (Fintype.ofFinite V).card := by
  apply Iff.intro
  · intro all_in_set -- →
    have eq : V ≃ set := by -- We see that V and 'set' are isomorphic as a result of our assumptions
      exact (Equiv.subtypeUnivEquiv all_in_set).symm -- This follows from a result in matlib
    exact my_card_congr (Fintype.ofFinite ↑set) (Fintype.ofFinite V) (id eq.symm) -- Use the lemma my_card_congr to show that cardinality equality follows
  · intro card_eq v  -- ←
    rw [my_set_fintype_card_eq_univ_iff] at card_eq -- We see the set is the whole universe
    subst card_eq -- So want to show v is in its own universe
    exact trivial -- Trivially true

theorem my_card_congr' {α β} (x : Fintype α) (y : Fintype β) (h : α = β) : x.card = y.card := by
  exact Fintype.card_congr' h

def putElemInSet {V : Type} (u : V) : Set V := {u}-- trivial function needed to issues with {u} below

/--A proof that removing an element from a set of type V, where V is finite, decreases the cardinlity of the set by 1-/
lemma finset_removing_elem_decrease_card_by_one {V : Type} [Finite V] [DecidableEq V] (set : Set V) (w : set) [Fintype ↑set] : (set \ {↑w}).toFinset.card = set.toFinset.card - 1:= by

  rw [Set.toFinset_diff]
  rw [Finset.card_sdiff] -- We see that we can split up (set2 \ {w}).toFinset.card

  rw [Set.toFinset_singleton, Finset.card_singleton] -- The cardinality of a singleton is always one, and {w} is a singelton
  -- This is closes out goal, but card_sdiff required {w}.toFinset ⊆ set2.toFinset, so we must now prove that

  -- This is the same as w being in set2, as {w} is a singleton
  rw [Set.toFinset_singleton, Set.subset_toFinset, Finset.coe_singleton, Set.singleton_subset_iff]
  exact w.prop-- This is exactly one of the assumptions

lemma union_minus_intersection_eq_sum_of_sets {V : Type} [Finite V] [Nonempty V]
  : ∀ a b : Set V, ∅ = a ∩ b → (Fintype.ofFinite a).card + (Fintype.ofFinite b).card  = (Fintype.ofFinite ↑(a ∪ b)).card := by
  intro a b empty_inter
  let a_card := (Fintype.ofFinite a).card
  let b_card := (Fintype.ofFinite b).card
  generalize hu : (Fintype.ofFinite ↑(a ∪ b)).card = u_card

  induction u_card with -- equiv to starting at |V (G)| = 1
  --We prove |E(G)| = |V (G)| − 1 by induction on n = |V (G)|.
  | zero     =>
  rw [(Fintype.ofFinite ↑(a ∪ b)).card_eq_zero_iff] at hu
  have a_card_eq_zero : a_card = 0 := by
    have a_empty : IsEmpty a := by
      simp_all only [isEmpty_subtype]
      simp [Set.mem_union] at hu
      intro x
      simp_all only [not_false_eq_true]
    rw [← (Fintype.ofFinite a).card_eq_zero_iff] at a_empty
    exact a_empty
  have b_card_eq_zero : b_card = 0 := by
    have b_empty : IsEmpty b := by
      simp_all only [isEmpty_subtype]
      simp [Set.mem_union] at hu
      intro x
      simp_all only [not_false_eq_true]
    rw [← (Fintype.ofFinite b).card_eq_zero_iff] at b_empty
    exact b_empty
  exact Linarith.eq_of_eq_of_eq a_card_eq_zero b_card_eq_zero
  | succ y hy =>

  have nonempty_union : Nonempty ↑(a ∪ b) := by
    have card_gt_0 : 0 < (Fintype.ofFinite ↑(a ∪ b)).card := by
      exact Nat.lt_of_sub_eq_succ hu
    rw [(Fintype.ofFinite ↑(a ∪ b)).card_pos_iff] at card_gt_0
    exact card_gt_0
  rw [nonempty_subtype] at nonempty_union -- As nonempty, there must be at least one element in the union
  obtain ⟨u, u_prop⟩ := nonempty_union -- obtain this  element and its relation
  rw [Set.mem_union] at u_prop
  have only_in_one : (u ∈ a ∧ u ∉ b) ∨ ((u ∈ b ∧ u ∉ a)):= by
    by_contra in_intersection -- The opposite of the statement above only occurs if u is in and b (i.e the union)
    simp_all only [not_or, not_and, not_not]
    obtain ⟨a_imp_b, b_imp_a⟩ := in_intersection
    cases u_prop with
    | inl in_a =>
      have nonempty_inter : ∅ ≠ a ∩ b := by

        have in_inter : u ∈ a ∩ b := by

          have u_in_b : u ∈ b := by
            exact a_imp_b in_a

          exact Set.mem_inter in_a u_in_b

        exact Ne.symm (ne_of_mem_of_not_mem' in_inter fun a => a)

      exact nonempty_inter empty_inter
    | inr in_b =>
      have nonempty_inter : ∅ ≠ a ∩ b := by

        have in_inter : u ∈ a ∩ b := by

          have u_in_a : u ∈ a := by
            exact b_imp_a in_b

          exact Set.mem_inter u_in_a in_b

        exact Ne.symm (ne_of_mem_of_not_mem' in_inter fun a => a)

      exact nonempty_inter empty_inter

  cases only_in_one with
  | inl in_a_not_b =>

    obtain ⟨in_a, not_in_b⟩ := in_a_not_b
    have card_union_without_u_eq_minus_one : (Fintype.ofFinite ↑((a ∪ b) \ {u})).card = (Fintype.ofFinite ↑(a ∪ b)).card - 1 := by

        simp [← Set.toFinset_card] -- We change to form of the goal so lemmas realting to finset cardinality can be applied

        have decidableEq : DecidableEq V:= by exact Classical.typeDecidableEq V

        have my_Fintype : Fintype ↑(a ∪ b) := by exact Fintype.ofFinite ↑(a ∪ b) -- must assert this for Set.toFinset_diff to work

        rw [Set.toFinset_diff, Finset.card_sdiff] -- We see that we can split up ((a ∪ b) \ {u}).toFinset.card

        rw [Set.toFinset_singleton, Finset.card_singleton] -- The cardinality of a singleton is always one, and {u} is a singelton

       -- There is some peculairity of Fintypes that means this must be asserted before we close hthe goal
        have card_eq : my_Fintype.card = (Fintype.ofFinite ↑(a ∪ b)).card := by
          exact my_card_congr' my_Fintype (Fintype.ofFinite ↑(a ∪ b)) rfl

        simp [Set.toFinset_card] -- We return the form of the equation to that involving Fintype.card
        exact congrFun (congrArg HSub.hSub card_eq) 1 -- And we see that card_eq means both sides of our goal are equal

        -- This is closes out goal, but card_sdiff required {u}.toFinset ⊆ (a ∪ b).toFinset, so we must now prove that
        rw [Set.toFinset_singleton, Set.subset_toFinset, Finset.coe_singleton, Set.singleton_subset_iff] -- We see this is equivalent to u ∈ (a ∪ b)
        exact u_prop-- This is exactly one of the assumptions


    have card_union_without_u_eq_y  : (Fintype.ofFinite ↑((a ∪ b) \ {u})).card = y := by
      simp_all only [add_tsub_cancel_right]

    have a_plus_b_without_u : (Fintype.ofFinite ↑(a \ {u})).card + (Fintype.ofFinite ↑(b \ {u})).card = y := by
      have eq :  (a ∪ b) \ {u} = ((a \ {u}) ∪ (b \ {u})) := by
        exact Set.union_diff_distrib

      have card_eq : (Fintype.ofFinite ↑((a ∪ b) \ {u})).card =  ( Fintype.ofFinite ↑( (a \ {u}) ∪ (b \ {u}) ) ).card := by
        exact my_card_congr' (Fintype.ofFinite ↑((a ∪ b) \ {u})) (Fintype.ofFinite ↑(a \ {u} ∪ b \ {u})) (congrArg Set.Elem eq)

      rw [card_eq] at card_union_without_u_eq_y

      -- apply hy at card_union_without_u_eq_y WHEN ITS FIXED
      sorry

    have a_without_u_card_eq_minus_one : (Fintype.ofFinite ↑(a \ {u})).card = (Fintype.ofFinite a).card - 1 := by -- the same as the proof for the union above
      simp [← Set.toFinset_card]

      have decidableEq : DecidableEq V:= by exact Classical.typeDecidableEq V

      have my_Fintype : Fintype ↑a := by exact Fintype.ofFinite ↑a

      rw [Set.toFinset_diff, Finset.card_sdiff]
      rw [Set.toFinset_singleton, Finset.card_singleton]

      have card_eq : my_Fintype.card = (Fintype.ofFinite ↑a).card := by
        exact my_card_congr' my_Fintype (Fintype.ofFinite ↑a) rfl

      simp [Set.toFinset_card]
      exact congrFun (congrArg HSub.hSub card_eq) 1
      rw [Set.toFinset_singleton, Set.subset_toFinset, Finset.coe_singleton, Set.singleton_subset_iff]
      exact in_a


    have b_card_without_u_eq_b_card : (Fintype.ofFinite ↑(b \ {u})).card = (Fintype.ofFinite b).card := by

      have b_without_u_eq_b : ↑b = ↑(b \ {u}):= by
        exact Eq.symm (Set.diff_singleton_eq_self not_in_b)

      exact my_card_congr' (Fintype.ofFinite ↑(b \ {u})) (Fintype.ofFinite ↑b) (congrArg Set.Elem (id (Eq.symm b_without_u_eq_b)))

    rw [a_without_u_card_eq_minus_one] at a_plus_b_without_u -- apply the above results to a_plus_b_without_u
    rw [b_card_without_u_eq_b_card] at a_plus_b_without_u


    -- As u is in a, clearly it is nonempty, thus its cardinality is >0 , that is equal to succ n for some n
    have a_card_eq_succ : ∃ n, (Fintype.ofFinite a).card = Nat.succ n := by

      have zero_lt_card : 0 < (Fintype.ofFinite a).card := by

        have nonempty : Nonempty a := by
          rw [nonempty_subtype]
          apply Exists.intro
          · exact in_a

        exact (Fintype.ofFinite a).card_pos

      exact Nat.exists_eq_add_one.mpr zero_lt_card

    obtain ⟨n, n_rel⟩ := a_card_eq_succ -- obtain this n and its relation to a


    rw [add_comm] at a_plus_b_without_u -- swap around the cardinalities
    rw [add_comm]
    rw [n_rel] at a_plus_b_without_u  -- substituee a's cardinality for succ n
    rw [Nat.succ_eq_add_one] at a_plus_b_without_u -- rewrite succ n as n + 1
    rw [add_tsub_cancel_right] at a_plus_b_without_u -- the +1 and -1 in the equation cancel out
    subst a_plus_b_without_u -- We then substute this in
    simp_all only [add_tsub_cancel_right] -- and simplify
    rfl -- the left and right side to our goal are the same as succ n = n + 1, so we are done

    -- shoudl use whatever the opppositve of insert is rather than \ i think -- GET RID OF THIS
    -- card (union \ u) = card (union) - 1
    -- subst hu to get card (union \ u) = y + 1 - 1 = y
    -- so apply hy to get card (a \ u) +  card (b \ u) = y
    -- card (b \ u) = card (b) as u not in b (so card the same)
    -- card (a \ u) = card (a) - 1
    -- so card (b) + card (a) = y + 1 (add 1 to both sides)
    -- done
  | inr in_b_not_a =>
    -- copy of above with b, maybe make a lemma (okay... definitely)
    sorry

/-- This a proof of the fact that if an acyclic graph on V (finite, nonempty) has two connected
 components generated from the endpoint of an edge removed from G, the intesection of the connected
 components verticies is empty -/
lemma conn_comp_empty_intersection {V : Type} [Finite V] [Nonempty V] {G : SimpleGraph V} (G_Acyclic : isAcyclic G) {x y : V}
                                   (in_edgeSet : s(x,y) ∈ G.edgeSet) (G_del_edge : SimpleGraph V) {G1 G2 : G_del_edge.ConnectedComponent}
                                   (G_del_edge_val : G_del_edge = G.deleteEdges (putEdgeInSet s(x,y)))
                                   (G1_val : G1 = G_del_edge.connectedComponentMk x) (G2_val : G2 = G_del_edge.connectedComponentMk y)
                                  : G1.supp ∩ G2.supp = ∅ := by
  --TO DO: COMMENT THIS

  unfold SimpleGraph.ConnectedComponent.supp
  by_contra not_emptyset

  have exists_mem : ∃ v : V, v ∈ (G1.supp ∩ G2.supp) := by
    have nonempty : Nonempty ↑(G1.supp ∩ G2.supp) := by
      exact Set.nonempty_iff_ne_empty'.mpr not_emptyset
    exact nonempty_subtype.mp nonempty
  obtain ⟨v,v_prop⟩ := exists_mem
  have eq : G1 = G2 := by
    rw [Set.mem_inter_iff] at v_prop
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at v_prop
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at v_prop
    obtain ⟨left, right⟩ := v_prop
    subst right left
    rfl
  unfold isAcyclic at G_Acyclic
  unfold hasACycle at G_Acyclic
  simp [not_exists] at G_Acyclic
  unfold SimpleGraph.ConnectedComponent.supp at v_prop
  have deleted_reachable : G_del_edge.Reachable x y := by
    subst G_del_edge_val G1_val G2_val
    rw [SimpleGraph.ConnectedComponent.eq] at eq
    exact eq
  have x_cycle_exists : ∃ p : G.Walk y y , p.IsCycle := by
    rw [SimpleGraph.mem_edgeSet] at in_edgeSet
    unfold SimpleGraph.Reachable at deleted_reachable

    have exists_walk : ∃ p, p ∈ (Set.univ : Set (G_del_edge.Walk x y)) := by

      have nonempty : Nonempty (SimpleGraph.Walk G_del_edge x y) := by -- needed implicitly for the exact below, follows from deleted_reachable
        exact deleted_reachable

      exact Set.exists_mem_of_nonempty (SimpleGraph.Walk G_del_edge x y)

    obtain ⟨p_sub,p_sub_prop⟩ := exists_walk

    have del_is_subgraph : G_del_edge ≤ G := by
      rw [G_del_edge_val]
      exact SimpleGraph.deleteEdges_le (putEdgeInSet s(x, y))

    have y_x_Adj : G.Adj y x := by exact id (SimpleGraph.adj_symm G in_edgeSet)

    let p1 := SimpleGraph.Walk.mapLe del_is_subgraph p_sub
    have dec_eq_V : DecidableEq V := by exact Classical.typeDecidableEq V
    let p1_path_from_to_path := SimpleGraph.Walk.toPath p1-- takes the underlying path of p1
    let p1_path := p1_path_from_to_path.val
    let p2 := SimpleGraph.Walk.cons y_x_Adj p1_path

    have p2_is_cycle : p2.IsCycle := by

      have x_y_edge_not_in_p1_path : s(y,x) ∉ p1_path.edges := by
          by_contra e_in_p1_path

          have in_p_sub : s(y,x) ∈ p_sub.edges := by

            have subset_edges : p1_path.edges ⊆ p_sub.edges  := by

              have subset_edges_p1_path : p1_path.edges ⊆ p1.edges := by
                exact SimpleGraph.Walk.edges_bypass_subset p1

              have subset_edges_p1_sub : p1.edges = p_sub.edges := by
                have p1_def : p1 = SimpleGraph.Walk.mapLe del_is_subgraph p_sub := by rfl
                unfold SimpleGraph.Walk.mapLe at p1_def
                simp_all only [SimpleGraph.Walk.edges_map, p1]
                ext n a : 2
                simp_all only [List.getElem?_map, Option.mem_def, Option.map_eq_some',
                  SimpleGraph.Hom.mapSpanningSubgraphs_apply, Sym2.map_id', id_eq, exists_eq_right]
                -- figure out later...

              exact subset_of_subset_of_eq subset_edges_p1_path subset_edges_p1_sub

            exact subset_edges e_in_p1_path

          have in_G_del : s(y,x) ∈ G_del_edge.edgeSet := by
            exact SimpleGraph.Walk.edges_subset_edgeSet p_sub in_p_sub

          have symm_in_G_del : s(x, y) ∈ G_del_edge.edgeSet := by
            have y_x_Adj : G_del_edge.Adj y x := by exact in_G_del
            exact id (SimpleGraph.adj_symm G_del_edge y_x_Adj)

          subst G_del_edge_val
          unfold putEdgeInSet at symm_in_G_del

          rw [SimpleGraph.mem_edgeSet] at symm_in_G_del

          rw [SimpleGraph.deleteEdges_adj] at symm_in_G_del

          rw [Set.mem_singleton_iff] at symm_in_G_del

          simp_all only --One of the statements in symm_in_G_del is a contradiction, so we are done
      exact SimpleGraph.Path.cons_isCycle p1_path_from_to_path y_x_Adj x_y_edge_not_in_p1_path

    exact False.elim (G_Acyclic y p2 p2_is_cycle)

  subst G_del_edge_val-- sort this out later
  simp_all only [exists_const]

/-- A proof that for all paths p and n ≤ p.length, p.getVert n ∈ p.support -/
lemma getVert_in_support {V : Type} [Finite V] [Nonempty V] {G : SimpleGraph V} {x y : V} (p : G.Walk x y) {n : ℕ} (h : n ≤ p.length) : p.getVert n ∈ p.support := by
  rw [SimpleGraph.Walk.mem_support_iff_exists_getVert]
  exact Filter.frequently_principal.mp fun a => a rfl h

def getVert_to_support_index_map {V : Type} [Finite V] [Nonempty V] {G : SimpleGraph V} {x y : V} (p : G.Walk x y) (p_length_gt_zero : p.length > 0) (v : V)
  :  {n : ℕ| p.getVert n = v ∧ 0 < n ∧ n < p.length} → {n : Fin p.length | p.support[n] = v } :=fun
    | .mk val property => {
      val := by
        exact Fin.ofNat' val p_length_gt_zero
      property := by
        obtain ⟨is_getVert, property⟩ := property
        obtain ⟨gt_0, lt_length⟩ := property
        subst is_getVert
        simp_all only [Fin.getElem_fin, Set.mem_setOf_eq, Fin.val_ofNat']
        have mod_does_nothing : val % p.length = val := by
            exact Nat.mod_eq_of_lt lt_length
        simp_all only
        unfold SimpleGraph.Walk.support
        split
        next v x_1 => simp_all only [SimpleGraph.Walk.length_nil, not_lt_zero']
        next v x_1 v_1 h q =>
          simp_all only [SimpleGraph.Walk.length_cons] -- maybe get rid of
          generalize hnV : (SimpleGraph.Walk.cons h q).length - 1 = nV
          induction nV using Nat.case_strong_induction_on with -- DIDNT FIX IT
          | hz =>
            simp_all only [SimpleGraph.Walk.length_cons, add_tsub_cancel_right, zero_add, Nat.lt_one_iff,
              List.getElem_cons_zero, SimpleGraph.Walk.getVert_zero]
          | hi y hy =>
            have hypothesis_should_be : q.support[Fin.ofNat' (val - 1) p_length_gt_zero] = q.getVert (val - 1) := by
              sorry

            have mod_does_nothing2 : val % (y + 1 + 1) = val := by
              simp_all only [SimpleGraph.Walk.length_cons, add_tsub_cancel_right, Nat.mod_succ_eq_iff_lt]

            simp_all only [SimpleGraph.Walk.length_cons, add_tsub_cancel_right, Fin.getElem_fin, Fin.val_ofNat', Nat.succ_eq_add_one, add_right_eq_self, one_ne_zero, false_implies]


            rw [SimpleGraph.Walk.getVert_cons]

            have support_equality : (x :: q.support)[Fin.ofNat' val p_length_gt_zero] = (q.support)[Fin.ofNat' (val - 1) p_length_gt_zero] := by
              let neq_zero := Nat.not_eq_zero_of_lt gt_0
              let exists_n := Nat.exists_eq_succ_of_ne_zero neq_zero
              obtain ⟨n, n_prop⟩ := exists_n
              simp_all only [Nat.succ_eq_add_one, add_tsub_cancel_right]
              dsimp at *
              simp_all only [add_lt_add_iff_right, List.getElem_cons_succ]
              have mod_eq : n % (y + 1 + 1) = n := by
                simp_all only [Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one, add_lt_add_iff_right]
                exact Nat.lt_add_right 1 lt_length
              simp_all only

            dsimp at support_equality

            simp_all only [Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one, ne_eq]

            have mod_does_nothing2 : val % (y + 1 + 1) = val := by -- why have to do twice
              simp_all only [SimpleGraph.Walk.length_cons, add_tsub_cancel_right, Nat.mod_succ_eq_iff_lt]

            simp_all only [Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one]
            exact Nat.not_eq_zero_of_lt gt_0

    }

def takeUntil_length_lt_if_endpoints_neq {V : Type} [Finite V] [Nonempty V] [DecidableEq V] {G : SimpleGraph V} {x y z : V} (p : G.Walk x y) (in_sup : z ∈ p.support)
                 (neq : z ≠ y) : (p.takeUntil z in_sup).length < p.length := by

  have leq : (p.takeUntil z in_sup).length ≤ p.length := by -- A natural property takeUntil possesses
    exact SimpleGraph.Walk.length_takeUntil_le p in_sup

  have neq : (p.takeUntil z in_sup).length ≠ p.length := by -- I claim they cannot be equal
    simp_all only [ne_eq]
    by_contra eq -- Suppose they're equal

    have p_eq : p = (p.takeUntil z in_sup).append (p.dropUntil z in_sup) := by -- We split p up into takeUntil and the remainder of the walk
      exact Eq.symm (SimpleGraph.Walk.take_spec p in_sup)

    have dropUntilzIsNil : (p.dropUntil z in_sup).Nil := by -- I claim (p.dropUntil z in_sup) is an empty walk (Nil)

      refine SimpleGraph.Walk.nil_iff_length_eq.mpr ?_ -- We see our goal is equivalent to the walk having length zero

      have length_equality : p.length = ((p.takeUntil z in_sup).append (p.dropUntil z in_sup)).length := by -- Follows naturally from p_eq
        exact congrArg SimpleGraph.Walk.length p_eq

      rw [length_equality] at eq -- sub this new length in at eq
      rw [SimpleGraph.Walk.length_append] at eq -- Apply ((p.takeUntil).append (p.dropUntil).length = (p.takeUntil).length + (p.dropUntil).length

      exact Nat.self_eq_add_right.mp eq -- We cancel out the (p.takeUntil z in_sup).length on both sides, and we are done

    have y_eq_z : y = z := by
      apply SimpleGraph.Walk.Nil.eq at dropUntilzIsNil -- As the graph is Nil, its start and endpoints are the same
      exact id (Eq.symm dropUntilzIsNil)

    subst y_eq_z -- We sub this is and see neq states y ≠ y
    simp_all only [not_true_eq_false] -- This can never be true

  exact Nat.lt_of_le_of_ne leq neq -- Less than or equal to and not equal naturally implies less than

theorem my_set_fintype_card_le_univ (V : Fintype α) (set : Set α) (s : Fintype set) : -- An adaptation of set_fintype_card_le_univ for my use case in onetwothreefour_implies_five_part_1
    Fintype.card set ≤ Fintype.card α :=
  Fintype.card_le_of_embedding (Function.Embedding.subtype set)

lemma edges_of_p_cut_in_G_e_removed {V : Type} [Finite V] [Nonempty V] [DecidableEq V] {G G_e_removed: SimpleGraph V}
                         {e_val_1 e_val_2 : V} (edge_in_G : s(e_val_1, e_val_2) ∈ G.edgeSet)
                         (G_e_removed_val : G_e_removed = G.deleteEdges (putEdgeInSet s(e_val_1, e_val_2))) {G' G'' : G.Subgraph}
                         (G'_val : G' = connectedComponentToSubGraph G (G_e_removed.connectedComponentMk e_val_1))
                         (G''_val : G'' = connectedComponentToSubGraph G (G_e_removed.connectedComponentMk e_val_2))
                         {v : V} (v_in_G' : v ∈ G'.verts) (empty_intersection : G'.verts ∩ G''.verts = ∅)
                         {e_num : V} {p : G.Walk e_num v} (p_is_path : p.IsPath)
                         (v_neq_e_val_1 : v ≠ e_val_1)(v_neq_e_val_2 : v ≠ e_val_2)
                         {my_val : V} (my_val_in_sup : my_val ∈ p.support)
                         (my_val_eq_or : my_val = e_val_1 ∨ my_val = e_val_2)
                         (e_num_not_in_G' : e_num ∉ G'.verts) (e_num_not_in_G'' : e_num ∉ G''.verts)
                         (v_not_e_num_reachable : ¬(G.deleteEdges (putEdgeInSet s(e_val_1, e_val_2))).Reachable e_num v)
                         {n_1 n_2 : ℕ} (n_1_prop_1 : p.getVert n_1 = my_val) (n_1_prop_2 : n_1 ≤ p.length)
                        (n_2_prop_1 : p.getVert n_2 ∈ {e_val_1, e_val_2} \ putElemInSet my_val)
                         (n_2_prop_2 : n_2 ≤ p.length) (not_equal : n_1 < n_2)
                         : ∀ e, e ∈ (p.takeUntil my_val my_val_in_sup).edges → e ∈ G_e_removed.edgeSet := by

  let p_cut := SimpleGraph.Walk.takeUntil p my_val my_val_in_sup
  by_contra exists_edge_not_in_G_e_removed
  simp [not_forall] at exists_edge_not_in_G_e_removed
  obtain ⟨x, x_props⟩ := exists_edge_not_in_G_e_removed
  obtain ⟨x_in_p_cut, x_not_in_G_e_removed⟩ := x_props
  have eq_e_val : x = s(e_val_1, e_val_2) := by
    have in_G_edgeSet : x ∈ G.edgeSet := by
      exact SimpleGraph.Walk.edges_subset_edgeSet p_cut x_in_p_cut

    have only_edge_removed_is_e_val : G.edgeSet \ G_e_removed.edgeSet = {s(e_val_1, e_val_2) } := by
      rw [G_e_removed_val]
      rw [SimpleGraph.edgeSet_deleteEdges, sdiff_sdiff_right_self]
      unfold putEdgeInSet
      rw [← Set.singleton_subset_iff] at edge_in_G
      rw [inf_of_le_right]
      exact edge_in_G

    have x_in_G_without_G_e_removed : x ∈ G.edgeSet \ G_e_removed.edgeSet := by
      exact Set.mem_diff_of_mem in_G_edgeSet x_not_in_G_e_removed

    simp_all only [Set.mem_singleton_iff]

  have other_val_in_support : p.getVert n_2 ∈ p_cut.support := by-- follows from the edge containing e_val_2 being in the path
    rw [eq_e_val] at x_in_p_cut
    cases my_val_eq_or with
    | inl eq_val_1 =>
    have eq_other_val : p.getVert n_2 = e_val_2 := by
      unfold putElemInSet at n_2_prop_1
      rw [eq_val_1] at n_2_prop_1
      simp_all only [Set.mem_singleton_iff, Set.insert_diff_of_mem, Set.mem_diff]

    rw [eq_other_val]
    exact SimpleGraph.Walk.snd_mem_support_of_mem_edges p_cut x_in_p_cut
    | inr eq_val_2 =>
    have eq_other_val : p.getVert n_2 = e_val_1 := by
      unfold putElemInSet at n_2_prop_1
      rw [eq_val_2] at n_2_prop_1
      obtain ⟨left, right⟩ := n_2_prop_1
      simp_all only [Set.mem_insert_iff, or_false]

    rw [eq_other_val]
    exact SimpleGraph.Walk.fst_mem_support_of_mem_edges p_cut x_in_p_cut

  rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at other_val_in_support
  obtain ⟨n_2_cut, props⟩ := other_val_in_support
  obtain ⟨n_2_cut_prop_1, n_2_cut_prop_2⟩ := props

  have getVert_length_eq_e_val_1 : p_cut.getVert p_cut.length = my_val := by
    exact SimpleGraph.Walk.getVert_length p_cut

  have index_eq {n m : ℕ} (h_n1 : n ≤ p_cut.length) (h_n2 : n < p.length) (h_n3 : (0 < n))
                          (h_m2 : m < p.length) (h_m3 : (0 < m))
                          (h_eq : p_cut.getVert n = p.getVert m) : n = m := by

    have p_getVert_eq : p_cut.getVert n = p.getVert n := by

      have p_eq : p = (p.takeUntil my_val my_val_in_sup ).append (p.dropUntil my_val my_val_in_sup ) := by -- We split p up into takeUntil and the remainder of the walk
        exact Eq.symm (SimpleGraph.Walk.take_spec p my_val_in_sup )

      rw [p_eq]
      rw [SimpleGraph.Walk.getVert_append]
      split
      · exact rfl
      · rename_i not_less_than_length
        rw [not_lt] at not_less_than_length

        have n_eq_length : n = p_cut.length := by
          exact Eq.symm (Nat.le_antisymm not_less_than_length h_n1)
        subst n_eq_length

        have eq_0 : p_cut.length - (p.takeUntil my_val my_val_in_sup).length = 0:= by  -- defitinely doesn need own have
          exact Nat.sub_self p_cut.length

        rw [eq_0]
        rw [SimpleGraph.Walk.getVert_zero, SimpleGraph.Walk.getVert_length]

    have p_length_gt_0 : 0 < p.length := by -- n lies strictly between 0 and p.length, so p.length cannot be 0
      exact Nat.zero_lt_of_lt h_n2

    let v := p.getVert n

    let getVert_to_sup_map := getVert_to_support_index_map p p_length_gt_0 v

    have n_properties : p.getVert n = p.getVert n ∧ 0 < n ∧ n < p.length := by
      simp_all only [true_and] -- All the statement in the 'and' are given as assumptions
    let my_n : ↑{x | p.getVert x = p.getVert n ∧ 0 < x ∧ x < p.length} := ⟨n, n_properties⟩ -- Thus we can construct an element of this set related to n

    have m_properties : p.getVert m = p.getVert n ∧ 0 < m ∧ m < p.length := by-- An also one related to m
      simp_all only [true_and]
    let my_m : ↑{x | p.getVert x = p.getVert n ∧ 0 < x ∧ x < p.length} := ⟨m, m_properties⟩

    let mapped_n := getVert_to_sup_map my_n -- We map my_n to teh correspondent getVert_to_sup_map and label it mapped_n

    let mapped_m := getVert_to_sup_map my_m -- We do the same for my_m

    have supp_eq : p.support[mapped_n.val.val] = p.support[mapped_m.val.val] := by
      have n_eq_v : p.support[mapped_n.val.val] = v := by
        have val_has_property : p.support[mapped_n.val] = v := by
          exact mapped_n.prop -- This is the property mapped_n's set membership implies
        rw [Fin.getElem_fin] at val_has_property
        exact val_has_property

      have m_eq_v : p.support[mapped_m.val.val] = v := by-- exact same as above but with m
        have val_has_property : p.support[mapped_m.val] = v := by
          exact mapped_m.prop
        rw [Fin.getElem_fin] at val_has_property
        exact val_has_property

      simp_all only -- both equal to v implies they are the same, so we are done

    have p_nodup : p.support.Nodup := by -- We have there are no duplicates in p.support as p_prop says p is a path
      exact p_is_path.support_nodup

    -- No duplicates means that mapped_n.val.val and mapped_m.val.val are the same index
    rw [List.Nodup.getElem_inj_iff p_nodup] at supp_eq

    have mapped_n_eq_n : mapped_n.val = n := by
      have eq_mod : mapped_n.val.val = n % p.length := by

        have val_val_eq_Fin : mapped_n.val.val = (Fin.ofNat' n p_length_gt_0).val := by
          exact rfl -- Follows from construction

        rw [Fin.val_ofNat'] at val_val_eq_Fin -- this lemma gives Fin.ofNat' in the desired format
        exact val_val_eq_Fin

      have given_property : n < p.length := by
        simp_all only -- We are given this at the start, just need its own result now

      have mod_eq_n : n % p.length = n := by -- as n < p.length, the % does not change the value
        exact Nat.mod_eq_of_lt given_property

      rw [mod_eq_n] at eq_mod-- subsite this result into mapped_n.val.val = n % p.length to get the desired result
      exact eq_mod
    have mapped_m_eq_m : mapped_m.val.val = m := by -- same as above but for m
      have eq_mod : mapped_m.val.val = m % p.length := by

        have val_val_eq_Fin : mapped_m.val.val = (Fin.ofNat' m p_length_gt_0).val := by
          exact rfl

        rw [Fin.val_ofNat'] at val_val_eq_Fin
        exact val_val_eq_Fin

      have given_property : m < p.length := by
        simp_all only

      have mod_eq_m : m % p.length = m := by
        exact Nat.mod_eq_of_lt given_property

      rw [mod_eq_m] at eq_mod
      exact eq_mod

    rw [mapped_n_eq_n, mapped_m_eq_m] at supp_eq -- Thus, this equation becomes m = n, and we are done
    exact supp_eq

  -- The result below is used multiple times, so is defined here instead of with the other properties most relevant to it
  have n_2_cut_lt_p_cut_length : n_2_cut < p_cut.length := by
    have neq : p_cut.length ≠ n_2_cut := by
      by_contra eq -- Suppose they are equal

      have getVertEq : p_cut.getVert n_2_cut = my_val := by
        rw [← eq] -- sub in p_cut.length
        rw [p_cut.getVert_length] -- follows from prexistant lemma

      rw [n_2_cut_prop_1] at getVertEq -- We see the above implies e_val_1 = e_val_2

      have in_other_val_set : my_val ∈ {e_val_1, e_val_2} \ putElemInSet my_val := by
        exact Set.mem_of_eq_of_mem (id (Eq.symm getVertEq)) n_2_prop_1

      unfold putElemInSet at in_other_val_set
      cases my_val_eq_or with
      | inl eq_val_1 =>
        rw [eq_val_1] at in_other_val_set
        simp_all only [Set.mem_singleton_iff, Set.mem_diff]
      | inr eq_val_2 =>
        rw [eq_val_2] at in_other_val_set
        simp_all only [Set.mem_singleton_iff, Set.mem_diff]

    exact Nat.lt_of_le_of_ne n_2_cut_prop_2 (id (Ne.symm neq))

  have n_2_cut_eq_n2 : n_2_cut = n_2 := by

    have n_2_lt_p_length : n_2 < p.length := by -- for n_1 case have n_1 < n_2 so use that

      have neq : n_2 ≠ p.length := by
        by_contra eq

        have n_2_eq_v : p.getVert n_2 = v := by
          rw [eq] -- This is p.getVert p.length = v
          apply SimpleGraph.Walk.getVert_length -- Which this lemma states as an identity

        rw [n_2_eq_v] at n_2_prop_1 -- So we have e_val_2 = v
        cases my_val_eq_or with
        | inl eq_val_1 =>
        have eq_other_val : p.getVert n_2 = e_val_2 := by
          unfold putElemInSet at n_2_prop_1
          rw [eq_val_1] at n_2_prop_1
          simp_all only [Set.mem_singleton_iff, Set.insert_diff_of_mem, Set.mem_diff]

        rw [eq_other_val] at n_2_eq_v
        rw [← n_2_eq_v] at v_in_G' -- v ∈ G_1.verts means e_val_2 is in G_1.verts

        have e_val_2_in_union : e_val_2 ∈ G'.verts ∩ G''.verts := by
          rw [G''_val]
          exact Set.mem_inter v_in_G' rfl

        rw [empty_intersection] at e_val_2_in_union
        exact e_val_2_in_union

        | inr eq_val_2 =>
        have eq_other_val : p.getVert n_2 = e_val_1 := by
          unfold putElemInSet at n_2_prop_1
          rw [eq_val_2] at n_2_prop_1
          obtain ⟨left, right⟩ := n_2_prop_1
          simp_all only [Set.mem_insert_iff, or_false]

        rw [eq_other_val] at n_2_eq_v

        exact v_neq_e_val_1 (id (Eq.symm n_2_eq_v))

      exact Nat.lt_of_le_of_ne n_2_prop_2 neq

    have n_2_gt_zero : 0 < n_2 := by
      by_contra not_gt_zero

      have eq_zero : n_2 = 0 := by
        exact Nat.eq_zero_of_not_pos not_gt_zero

      have getVert_eq_e_num : p.getVert n_2 = e_num := by
        rw [eq_zero]
        exact SimpleGraph.Walk.getVert_zero p

      rw [getVert_eq_e_num] at n_2_prop_1

      cases my_val_eq_or with
      | inl eq_val_1 =>
        have eq_other_val : p.getVert n_2 = e_val_2 := by
          unfold putElemInSet at n_2_prop_1
          rw [eq_val_1] at n_2_prop_1
          simp_all only [Set.mem_singleton_iff, Set.insert_diff_of_mem, Set.mem_diff]

        rw [eq_other_val] at getVert_eq_e_num
        rw [G''_val] at e_num_not_in_G''
        exact e_num_not_in_G'' (congrArg G_e_removed.connectedComponentMk (id (Eq.symm getVert_eq_e_num)))
      | inr eq_val_2 =>
        have eq_other_val : p.getVert n_2 = e_val_1 := by
          unfold putElemInSet at n_2_prop_1
          rw [eq_val_2] at n_2_prop_1
          obtain ⟨left, right⟩ := n_2_prop_1
          simp_all only [Set.mem_insert_iff, or_false]

        rw [eq_other_val] at getVert_eq_e_num
        rw [G''_val] at e_num_not_in_G''
        rw [G'_val] at e_num_not_in_G'
        exact e_num_not_in_G' (congrArg G_e_removed.connectedComponentMk (id (Eq.symm getVert_eq_e_num)))

    have n_2_cut_gt_zero : 0 < n_2_cut := by
      by_contra not_gt_zero

      have eq_zero : n_2_cut = 0 := by
        exact Nat.eq_zero_of_not_pos not_gt_zero

      have getVert_eq_e_num : p_cut.getVert n_2_cut = e_num := by
        rw [eq_zero]
        exact SimpleGraph.Walk.getVert_zero p_cut

      rw [getVert_eq_e_num] at n_2_cut_prop_1

      cases my_val_eq_or with
      | inl eq_val_1 =>
        have eq_other_val : p.getVert n_2 = e_val_2 := by
          unfold putElemInSet at n_2_prop_1
          rw [eq_val_1] at n_2_prop_1
          simp_all only [Set.mem_singleton_iff, Set.insert_diff_of_mem, Set.mem_diff]

        rw [eq_other_val] at n_2_cut_prop_1
        rw [G''_val] at e_num_not_in_G''
        exact e_num_not_in_G'' (congrArg G_e_removed.connectedComponentMk n_2_cut_prop_1)
      | inr eq_val_2 =>
        have eq_other_val : p.getVert n_2 = e_val_1 := by
          unfold putElemInSet at n_2_prop_1
          rw [eq_val_2] at n_2_prop_1
          obtain ⟨left, right⟩ := n_2_prop_1
          simp_all only [Set.mem_insert_iff, or_false]

        rw [eq_other_val] at n_2_cut_prop_1
        rw [G'_val] at e_num_not_in_G'
        exact e_num_not_in_G' (congrArg G_e_removed.connectedComponentMk n_2_cut_prop_1)


    have n_2_cut_lt_p_length : n_2_cut < p.length := by
      have cut_length_lt : p_cut.length ≤ p.length := by
        exact SimpleGraph.Walk.length_takeUntil_le p my_val_in_sup
      exact Nat.lt_of_lt_of_le n_2_cut_lt_p_cut_length cut_length_lt

    exact index_eq n_2_cut_prop_2 n_2_cut_lt_p_length n_2_cut_gt_zero n_2_lt_p_length n_2_gt_zero n_2_cut_prop_1

  have p_cut_length_eq_n_1 : p_cut.length = n_1 := by

    have getVert_eq : p_cut.getVert p_cut.length = p.getVert n_1 := by
      rw [n_1_prop_1]
      rw [getVert_length_eq_e_val_1]

    have n_1_lt_p_length : n_1 < p.length := by
      by_contra not_less_than

      have eq : n_1 = p.length := by
        rw [not_lt] at not_less_than
        exact Eq.symm (Nat.le_antisymm not_less_than n_1_prop_2)

      have eq2: p.getVert n_1 = p.getVert p.length := by
          exact congrArg p.getVert eq

      rw [n_1_prop_1, SimpleGraph.Walk.getVert_length] at eq2

      cases my_val_eq_or with
      | inl eq_val_1 =>
      rw [eq_val_1] at eq2
      exact v_neq_e_val_1 (id (Eq.symm eq2))
      | inr eq_val_2 =>
      rw [eq_val_2] at eq2
      exact v_neq_e_val_2 (id (Eq.symm eq2))

    have p_cut_lt_p_length : p_cut.length < p.length := by
      have v_neq_my_val : v ≠ my_val := by
        cases my_val_eq_or with
        | inl eq_val_1 => exact Ne.symm (ne_of_eq_of_ne eq_val_1 (id (Ne.symm v_neq_e_val_1)))
        | inr eq_val_1 => exact Ne.symm (ne_of_eq_of_ne eq_val_1 (id (Ne.symm v_neq_e_val_2)))
      exact takeUntil_length_lt_if_endpoints_neq p my_val_in_sup fun a =>
          v_neq_my_val (id (Eq.symm a))

    have n_1_gt_zero : 0 < n_1 := by
      by_contra not_gt_zero

      have eq_zero : n_1 = 0 := by
        exact Nat.eq_zero_of_not_pos not_gt_zero

      have getVert_eq_e_num : p.getVert n_1 = e_num := by
        rw [eq_zero]
        exact SimpleGraph.Walk.getVert_zero p

      have val_eq_num : my_val = e_num := by
        rw [n_1_prop_1] at getVert_eq_e_num
        exact getVert_eq_e_num
      cases my_val_eq_or with
      | inl eq_val_1 =>
      rw [eq_val_1] at val_eq_num
      rw [G'_val] at e_num_not_in_G'
      exact e_num_not_in_G' (congrArg G_e_removed.connectedComponentMk (id (Eq.symm val_eq_num)))
      | inr eq_val_2 =>
      rw [eq_val_2] at val_eq_num
      rw [G''_val] at e_num_not_in_G''
      exact e_num_not_in_G'' (congrArg G_e_removed.connectedComponentMk (id (Eq.symm val_eq_num)))

    have p_cut_lt_zero: 0 < p_cut.length := by
      by_contra not_gt_zero
      have length_eq_zero : p_cut.length = 0 := by exact Nat.eq_zero_of_not_pos not_gt_zero
      apply SimpleGraph.Walk.eq_of_length_eq_zero at length_eq_zero
      cases my_val_eq_or with
      | inl eq_val_1 =>
      rw [eq_val_1] at length_eq_zero
      rw [G'_val] at e_num_not_in_G'
      exact e_num_not_in_G' (congrArg G_e_removed.connectedComponentMk length_eq_zero)
      | inr eq_val_2 =>
      rw [eq_val_2] at length_eq_zero
      rw [G''_val] at e_num_not_in_G''
      exact e_num_not_in_G'' (congrArg G_e_removed.connectedComponentMk length_eq_zero)

    have p_cut_leq_p_cut : p_cut.length ≤ p_cut.length := by
      exact Nat.le_refl p_cut.length

    -- We have all the prerequisites for index_eq, so we are done
    exact index_eq p_cut_leq_p_cut p_cut_lt_p_length p_cut_lt_zero n_1_lt_p_length n_1_gt_zero getVert_eq

  have n_1_lt_self : n_1 < n_1 := by -- ALREADY COMMENTED??
    rw [p_cut_length_eq_n_1] at n_2_cut_lt_p_cut_length -- Get n_2_cut < n_1
    rw [n_2_cut_eq_n2 ] at n_2_cut_lt_p_cut_length -- Get n_2 < n_1
    exact Nat.lt_trans not_equal n_2_cut_lt_p_cut_length

  exact (lt_self_iff_false n_1).mp n_1_lt_self --  n_1_lt_self cannot be true, so we have found a contradiction

lemma reachableToAllVerts {V : Type} [Finite V] [Nonempty V] {G G_e_removed: SimpleGraph V} (G_preconnected : G.Preconnected)
                         {e_val_1 e_val_2 : V} (edge_in_G : s(e_val_1, e_val_2) ∈ G.edgeSet)
                         (G_e_removed_val : G_e_removed = G.deleteEdges (putEdgeInSet s(e_val_1, e_val_2))) {G' G'' : G.Subgraph}
                         (G'_val : G' = connectedComponentToSubGraph G (G_e_removed.connectedComponentMk e_val_1))
                         (G''_val : G'' = connectedComponentToSubGraph G (G_e_removed.connectedComponentMk e_val_2))
                         (empty_intersection : G'.verts ∩ G''.verts = ∅)
                         {e_num : V} (e_num_not_in_G' : e_num ∉ G'.verts) (e_num_not_in_G'' : e_num ∉ G''.verts)
                         : ∀ v, v ∈ G'.verts ∧ v ≠ e_val_1 ∧ v ≠ e_val_2 →  G_e_removed.Reachable e_num v := by
  by_contra exists_exception
  let e_val := s(e_val_1, e_val_2)
  simp [not_forall] at exists_exception
  obtain ⟨v, v_prop⟩ := exists_exception
  obtain ⟨v_in_G_1, v_prop⟩ := v_prop
  obtain ⟨v_neq_e_val_1, v_prop⟩ := v_prop
  obtain ⟨v_neq_e_val_2, v_not_e_num_reachable⟩ := v_prop

  have exists_walk : ∃ p, p ∈ (Set.univ : Set (G.Walk e_num v)) := by
    have nonempty : Nonempty (SimpleGraph.Walk G e_num v) := by
      exact G_preconnected e_num v
    exact Set.exists_mem_of_nonempty (SimpleGraph.Walk G e_num v)

  have dec_eq_V : DecidableEq V := by -- needed for multiple lemmas used below
      exact Classical.typeDecidableEq V

  obtain ⟨p, p_prop⟩ := exists_walk
  let p_to_path := p.toPath
  obtain ⟨p, p_prop⟩ := p.toPath

  let e_val_in_path := e_val ∈ p.edges
  by_cases e_val_in_path
  · rename_i in_path
    simp_all only [e_val_in_path] -- If e_val is in the edgeset

    have edge_val_1_in_support : e_val_1 ∈ p.support := by -- this follow from the edge containing them being in p
      exact p.fst_mem_support_of_mem_edges in_path
    have edge_val_2_in_support : e_val_2 ∈ p.support := by
      exact p.snd_mem_support_of_mem_edges in_path

    have exists_getVert_1 : ∃ n, p.getVert n = e_val_1 ∧ n ≤ p.length  := by
      rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at edge_val_1_in_support -- MAYBE MAKE THIS A LEMMA USED 3+ TIMES
      obtain ⟨n, props⟩ := edge_val_1_in_support
      obtain ⟨prop_1, prop_2⟩ := props
      exact Filter.frequently_principal.mp fun a => a prop_1 prop_2
    obtain ⟨n_1, n_1_props⟩ := exists_getVert_1
    obtain ⟨n_1_prop_1, n_1_prop_2⟩ := n_1_props

    have exists_getVert_2 : ∃ m, p.getVert m = e_val_2 ∧ m ≤ p.length := by
      rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at edge_val_2_in_support
      obtain ⟨n, props⟩ := edge_val_2_in_support
      obtain ⟨prop_1, prop_2⟩ := props
      exact Filter.frequently_principal.mp fun a => a prop_1 prop_2
    obtain ⟨n_2, n_2_props⟩ := exists_getVert_2
    obtain ⟨n_2_prop_1, n_2_prop_2⟩ := n_2_props

    have subgraph : G_e_removed ≤ G := by --needed in both sides of the by_cases below. it is trivial -- MIGHT NOT BE NEEDED
      rw [G_e_removed_val]
      exact SimpleGraph.deleteEdges_le (putEdgeInSet (Quot.mk (Sym2.Rel V) (e_val_1, e_val_2)))

    let val_1_first := n_1 < n_2
    by_cases val_1_first -- suppose e_val_1 appears first in p
    · rename_i val_1_comes_first
      simp [val_1_first] at val_1_comes_first
      let p_cut := SimpleGraph.Walk.takeUntil p e_val_1 edge_val_1_in_support
      have edges_of_p_cut_in_G_e_removed : ∀ e, e ∈ p_cut.edges → e ∈ G_e_removed.edgeSet := by

        rw [G_e_removed_val] at v_in_G_1 empty_intersection e_num_not_in_G' e_num_not_in_G''

        have e_val_1_eq_or : e_val_1 = e_val_1 ∨ e_val_1 = e_val_2 := by
          exact Or.symm (Or.inr rfl)

        have n_2_prop_1_formatted : p.getVert n_2 ∈ {e_val_1, e_val_2} \ putElemInSet e_val_1 := by
          unfold putElemInSet
          simp_all only [Set.mem_diff, Set.mem_insert_iff, true_or, true_and]
          by_contra not_in
          simp_all only [SimpleGraph.mem_edgeSet, Set.mem_singleton_iff, or_true, true_and, Decidable.not_not, SimpleGraph.irrefl]

        rw [G_e_removed_val]

        exact edges_of_p_cut_in_G_e_removed edge_in_G rfl rfl rfl v_in_G_1 empty_intersection
                                            p_prop v_neq_e_val_1 v_neq_e_val_2 edge_val_1_in_support
                                            e_val_1_eq_or e_num_not_in_G' e_num_not_in_G'' v_not_e_num_reachable n_1_prop_1
                                            n_1_prop_2 n_2_prop_1_formatted n_2_prop_2 val_1_comes_first

      let p_cut_sub := SimpleGraph.Walk.transfer p_cut G_e_removed edges_of_p_cut_in_G_e_removed

      have e_val_1_v_reachable : G_e_removed.Reachable e_val_1 v := by
        exact SimpleGraph.Reachable.symm (SimpleGraph.ConnectedComponent.exact v_in_G_1)

      have e_num_e_val_1_reachable : G_e_removed.Reachable e_num e_val_1 := by
        exact SimpleGraph.Walk.reachable p_cut_sub

      have e_num_v_reachable : G_e_removed.Reachable e_num v := by -- Apply transitivity of reachabilty to the above
        exact SimpleGraph.Reachable.trans e_num_e_val_1_reachable e_val_1_v_reachable

      rw [G_e_removed_val] at e_num_v_reachable
      exact v_not_e_num_reachable e_num_v_reachable -- These two statements are opposites, so we have found a contradiction
    · rename_i val_2_comes_first
      simp_all only [val_1_first]
      rw [not_lt] at val_2_comes_first -- We see this case means that n_2 ≤ n_1

      have val_2_comes_first : n_2 < n_1 := by -- I clain this implies they are less tham

        have n_1_neq_n_2 : n_1 ≠ n_2 := by --First, show they are not equal
          by_contra are_eq
          subst are_eq -- Suppose they are equal

          simp_all only [le_refl, SimpleGraph.mem_edgeSet, SimpleGraph.irrefl]
          -- We have their respective vertices are adjacent, but they are now the same vertices, a contradiction to looplessness of G

        exact Nat.lt_of_le_of_ne val_2_comes_first fun a => n_1_neq_n_2 (id (Eq.symm a))

      let p_cut := SimpleGraph.Walk.takeUntil p e_val_2 edge_val_2_in_support
      have edges_of_p_cut_in_G_e_removed : ∀ e, e ∈ p_cut.edges → e ∈ G_e_removed.edgeSet := by

        rw [G_e_removed_val] at v_in_G_1 empty_intersection e_num_not_in_G' e_num_not_in_G''

        have e_val_2_eq_or : e_val_2 = e_val_1 ∨ e_val_2 = e_val_2 := by
          exact Or.inr rfl

        have n_1_prop_1_formatted : p.getVert n_1 ∈ {e_val_1, e_val_2} \ putElemInSet e_val_2 := by
          unfold putElemInSet
          simp_all only [Set.mem_diff, Set.mem_insert_iff, true_or, true_and]
          by_contra not_in
          simp_all only [SimpleGraph.mem_edgeSet, Set.mem_singleton_iff,SimpleGraph.irrefl]

        rw [G_e_removed_val]
        exact edges_of_p_cut_in_G_e_removed edge_in_G rfl rfl rfl v_in_G_1 empty_intersection
                                            p_prop v_neq_e_val_1 v_neq_e_val_2 edge_val_2_in_support
                                            e_val_2_eq_or e_num_not_in_G' e_num_not_in_G'' v_not_e_num_reachable n_2_prop_1
                                            n_2_prop_2 n_1_prop_1_formatted n_1_prop_2 val_2_comes_first

      have e_num_in : e_num ∈ G''.verts := by
        rw [G''_val]
        let p_cut_sub := SimpleGraph.Walk.transfer p_cut G_e_removed edges_of_p_cut_in_G_e_removed
        have e_num_e_val_2_reachable : G_e_removed.Reachable e_val_2 e_num := by
          exact SimpleGraph.Walk.reachable (id p_cut_sub.reverse)
        have connComps_are_eq : G_e_removed.connectedComponentMk e_val_2 = G_e_removed.connectedComponentMk e_num := by
          exact SimpleGraph.ConnectedComponent.sound e_num_e_val_2_reachable
        exact id (Eq.symm connComps_are_eq)

      rw [G''_val] at e_num_in
      exact e_num_not_in_G'' e_num_in -- So e_num is both in and not in G''.verts, a contradiction

  · rename_i not_in_path
    simp_all only [e_val_in_path] -- suppose e_val is not in p.edges

    let p_del := SimpleGraph.Walk.toDeleteEdge e_val p not_in_path
    --
    have e_num_v_reachable : (G.deleteEdges (putEdgeInSet s(e_val_1, e_val_2))).Reachable e_num v := by -- As there exists a walk between them, we have reachability from e_num to v
      exact SimpleGraph.Walk.reachable p_del

    exact v_not_e_num_reachable e_num_v_reachable

/--A proof that if an edge is in a graph G and in a subgraph of it then if the edge is not in a connected component of this subgraph its first vertex is also not in this connected component-/
lemma edge_not_in_connComp_implies_vert_not_in {V : Type} [Finite V] [Nonempty V] {G G_e_removed: SimpleGraph V} {e_val_1 : V} {G' : G.Subgraph}
                                    (G'_val : G' = connectedComponentToSubGraph G (G_e_removed.connectedComponentMk e_val_1)) {e_num_1 e_num_2 : V}
                                    (e_num_not_in_G' : s(e_num_1, e_num_2) ∉ G'.edgeSet) (e_num_in_G : s(e_num_1, e_num_2) ∈ G.edgeSet)
                                    (e_num_in_G_e_removed : s(e_num_1, e_num_2) ∈ G_e_removed.edgeSet) : e_num_1 ∉ G'.verts := by

  let G'_connComponent := (G_e_removed.connectedComponentMk e_val_1)
  rw [G'_val]

  by_contra is_in -- Suppose it is in the vertex set

  have G_e_removed_adj : G_e_removed.Adj e_num_1 e_num_2 := by -- This is a trivial statement equivalent to edgeSet membership
    exact e_num_in_G_e_removed

  have e_num_1_in_connComp : e_num_1 ∈ G'_connComponent := by -- Equivalent to being in the vertex set, which is_in gives
    exact is_in

  -- This theorem turns the statment into one showing the connected components containing e_num_1 and e_num_2 are the same
  apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj at G_e_removed_adj

  have e_num_2_in_connComp : e_num_2 ∈ G'_connComponent := by -- I claim e_num_2 is also in the component

    have num_1_in_supp : e_num_1 ∈ G'_connComponent.supp := by -- e_num_1 is in the supp as it is in the component
      exact is_in

    -- We see that membership to  the compoent is equivalent to being the same connected component as e_val_1, as e_num_1
    -- is in the component its component has this property. G_e_removed_adj shows that this component is also the same as that containing
    -- e_num_2, so it must be in the G''s component and we are done
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff, G_e_removed_adj, ← SimpleGraph.ConnectedComponent.mem_supp_iff] at num_1_in_supp
    exact num_1_in_supp

  have e_num_in_G' : s(e_num_1, e_num_2) ∈ G'.edgeSet := by
    -- Follows from collecting the statements above and also edge_in_G
    have in_edgeSet : (G.Adj e_num_1 e_num_2) ∧ e_num_1 ∈ G'_connComponent ∧ e_num_2 ∈ G'_connComponent := by
      rw [← SimpleGraph.mem_edgeSet]
      simp_all only [true_and]

    rw [G'_val]
    exact in_edgeSet -- in_edgeSet is exactly the adjacency condition that connectedComponentToSubGraph specifies, so the edge is in the edge set
  exact e_num_not_in_G' e_num_in_G'

/--A proof that if (Fintype.ofFinite G_1.verts).card = 1 and (Fintype.ofFinite G_2.verts).card = 1 (Where they are defined as usual), there is a contradiction. A few other conditions are also assumed.-/
lemma both_cards_eq_one_gives_contradiction {V : Type} [Finite V] [Nonempty V] {G G_e_removed: SimpleGraph V} (G_preconnected : G.Preconnected)
                 {e_val_1 e_val_2 : V} (e_val_edge : s(e_val_1, e_val_2) ∈ G.edgeSet) {G_1 G_2 : G.Subgraph}
                 (G_1_val : G_1 = connectedComponentToSubGraph G (G_e_removed.connectedComponentMk e_val_1))
                 (G_2_val : G_2 = connectedComponentToSubGraph G (G_e_removed.connectedComponentMk e_val_2))
                 (cards_eq_one : (Fintype.ofFinite G_1.verts).card = 1 ∧ (Fintype.ofFinite G_2.verts).card = 1)
                 (empty_intersection : G_1.verts ∩ G_2.verts = ∅)
                 (G_e_removed_val : G_e_removed = G.deleteEdges (putEdgeInSet s(e_val_1, e_val_2)))
                 (nonempty_G_e_removed : Nonempty G_e_removed.edgeSet )
                 (not_subset : ¬G.edgeSet ⊆ G_1.edgeSet ∪ G_2.edgeSet ∪ {s(e_val_1, e_val_2)})
                  : False := by
  obtain ⟨G_1_eq_one, G_2_eq_one⟩ := cards_eq_one -- Split up out assumed and statement

  have G_1_eq_e_val_1 : G_1.verts = {e_val_1} := by -- As the cardinality is one, G_1.verts is a singleton

    -- We see the cardinality being one implies there exists an element of the set, and every elemlemnt of the set is the same
    rw [(Fintype.ofFinite G_1.verts).card_eq_one_iff] at G_1_eq_one

    simp_all only [Subtype.forall, Subtype.exists, Subtype.mk.injEq, nonempty_prop]
    obtain ⟨set_value, value_properties⟩ := G_1_eq_one -- Let set_value be this value
    obtain ⟨set_value_in_verts, elems_of_set_eq_set_value⟩ := value_properties -- We see that it is in the set, and all elements of the set equal it

    have e_val_1_in : e_val_1 ∈ ↑G_1.verts := by -- By contruction of G_1, this holds
      simp_all only
      rfl

    subst G_1_val
    apply elems_of_set_eq_set_value at e_val_1_in -- We see that set value and e_val_1 are the same by the equality property of G_1.verts

    subst e_val_1_in -- So elems_of_set_eq_set_value now states every element of the set is equal to e_val_1
    exact Eq.symm (Set.Subset.antisymm (fun ⦃a⦄ => congrArg G_e_removed.connectedComponentMk) elems_of_set_eq_set_value) -- This is equivalent to them being equal


  have G_2_eq_e_val_2 : G_2.verts = {e_val_2} := by -- Same structure and proof as above
    rw [(Fintype.ofFinite G_2.verts).card_eq_one_iff] at G_2_eq_one
    have e_val_2_in : e_val_2 ∈ ↑G_2.verts := by
      simp_all only
      rfl
    subst G_2_val
    simp_all only [Subtype.forall, Subtype.exists, Subtype.mk.injEq, nonempty_prop]
    obtain ⟨set_value, value_properties⟩ := G_2_eq_one
    obtain ⟨set_value_in_verts, elems_of_set_eq_set_value⟩ := value_properties
    apply elems_of_set_eq_set_value at e_val_2_in
    subst e_val_2_in
    ext x : 1
    simp_all only [Set.mem_singleton_iff]
    apply Iff.intro
    · intro a
      simp_all only
    · intro a
      subst a
      simp_all only

  -- There must be another element of G_e_removed.edgeSet otherwise G_e_removed.edgeSet is the emptyset
  have exists_edge_in_G_e_removed_neq_e_val : ∃ e : G_e_removed.edgeSet, e.val ≠ s(e_val_1, e_val_2) := by
    by_contra no_such_element
    simp [not_forall] at no_such_element
    have e_val_not_in : s(e_val_1, e_val_2) ∉ G_e_removed.edgeSet := by
      rw [SimpleGraph.mem_edgeSet]
      rw [G_e_removed_val]
      rw [SimpleGraph.deleteEdges_adj]
      exact not_and_not_right.mpr (congrFun rfl)

    have in_edgeSet_implies_not_in_edgeSet : ∀ x ∈ G_e_removed.edgeSet, x ∉ G_e_removed.edgeSet := by
      intro x x_membership
      let x_prop := no_such_element x x_membership
      rw [← x_prop] at e_val_not_in
      exact fun a => e_val_not_in x_membership

    rw [nonempty_subtype] at nonempty_G_e_removed
    obtain ⟨elem, elem_in_G_e_removed⟩ := nonempty_G_e_removed
    let elem_not_in_G_e_removed := in_edgeSet_implies_not_in_edgeSet elem elem_in_G_e_removed
    exact elem_not_in_G_e_removed elem_in_G_e_removed

  obtain ⟨e, e_neq_e_val⟩ := exists_edge_in_G_e_removed_neq_e_val -- Obtain this edge and its properties
  obtain ⟨e, e_prop⟩ :=  e
  obtain ⟨vert_1, vert_2⟩ := e

  have vert_1_neq : vert_1 ≠ e_val_1 ∧ vert_1 ≠ e_val_2 := by -- We have that vert_1 is neither of the e_val_i's
    by_contra equals_one
    apply or_iff_not_and_not.mpr at equals_one -- Suppose not, then it is equal to e_val_1 or e_val_2
    cases equals_one with
    | inl eq_val_1 => -- vert_1 = e_val_1
      have vert_2_in_G_1 : vert_2 ∈ G_1.verts := by -- As e_val_1 is in G_1.verts, we see this means vert_2 is too

        have val_1_vert_2_Adj : G_e_removed.Adj e_val_1 vert_2 := by -- They are adjacent in G_e_removed due to e_prop and  vert_1 = e_val_1
          rw [eq_val_1] at e_prop
          exact e_prop

        have vert_2_in_connComp : vert_2 ∈ (G_e_removed.connectedComponentMk e_val_1) := by -- Thus, vert_2 is in the connected component containing e_val_2
          apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj at val_1_vert_2_Adj -- Adjacency implies connected components are the same
          exact id (Eq.symm val_1_vert_2_Adj) -- Which is equivalent to membership

        rw [G_1_val] -- We see this conncected component is the same as G_1.verts
        exact vert_2_in_connComp -- So we are done

      simp_all only -- As G_1.verts equals {e_val_1}
      subst vert_2_in_G_1 -- The result above implies vert_2 = e_val_1, thus vert_1 = vert_2
      rw [SimpleGraph.mem_edgeSet, eq_val_1] at e_prop-- But they are adjacent in G_e_removed, thus irreflexibilty of graphs gives a contradiction
      apply SimpleGraph.irrefl at e_prop
      exact e_prop
    | inr eq_val_2 => -- vert_1 = e_val_2
      have vert_2_in_G_2 : vert_2 ∈ G_2.verts := by -- Same proof as the case above but with e_val's and G_i's swapped
        have val_2_vert_2_Adj : G_e_removed.Adj e_val_2 vert_2 := by
          rw [eq_val_2] at e_prop
          exact e_prop

        have vert_2_in_connComp : vert_2 ∈ (G_e_removed.connectedComponentMk e_val_2) := by
          apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj at val_2_vert_2_Adj
          exact id (Eq.symm val_2_vert_2_Adj)

        rw [G_2_val]
        exact vert_2_in_connComp
      simp_all only
      subst vert_2_in_G_2
      simp_all only [SimpleGraph.mem_edgeSet, SimpleGraph.irrefl]

  have e_val_1_vert_1_reachable : G.Reachable e_val_1 vert_1 := by -- This is a natural result of e_val_1_vert_1_reachable being reachable
    exact G_preconnected e_val_1 vert_1

  have exists_walk : ∃ p : G.Walk e_val_1 vert_1, p ∈ (Set.univ : Set (G.Walk e_val_1 vert_1)) := by
    rw [SimpleGraph.reachable_iff_nonempty_univ] at e_val_1_vert_1_reachable
    exact e_val_1_vert_1_reachable

  obtain ⟨p, p_prop⟩ :=  exists_walk

  have all_getVert_e_val : ∀ i : ℕ, i ≤ p.length → p.getVert i = e_val_1 ∨ p.getVert i = e_val_2 := by
    intro i lt_length -- obtain such an i and its assumed property, then induct on it
    induction i with
    | zero =>
      simp [SimpleGraph.Walk.getVert_zero] -- p.getVert 0 is e_val_1 by construction, so we are done

    | succ j hi => -- Assuming it holds ∀ i < j + 1, we want to show its holds for j

      have j_sub_one_leq_p_length : j ≤ p.length := by
        exact Nat.le_of_succ_le lt_length -- as j+1 has this property by lt_length, clearly j (a value less than it) has it too
      apply hi at j_sub_one_leq_p_length -- Thus we can apply hi for j to see p.getVert j = e_val_1 ∨ p.getVert j = e_val_2

      have j_sub_one_lt_p_length : j < p.length := by -- j is less than p.length also due to lt_length
        exact lt_length

      let G_adj_getVert := SimpleGraph.Walk.adj_getVert_succ p j_sub_one_lt_p_length -- We see that p.getVert j and p.getVert j + 1 are adjacent in G
      cases j_sub_one_leq_p_length with
      | inl j_get_vert_eq_val_1 => -- Suppose p.getVert j = e_val_1 was the part of j_sub_one_leq_p_length that was true
        have val_1_neighbourSet : G.neighborSet e_val_1 = {e_val_2} := by

          have val_in_neighborSet : e_val_2 ∈ G.neighborSet e_val_1 := by -- As e_val_1 and e_val_2 are adjacent e_val_2 is in the neighbours set
            exact e_val_edge

          by_contra not_equal_to_val -- Suppose that there is another elem

          -- I claim this means there exists another distinct element of the neighbour set
          have exists_other_elem : ∃ a, a ≠ e_val_2 ∧ a ∈ G.neighborSet e_val_1 := by

            have neighborSet_nonempty : ((G.neighborSet e_val_1) \ {e_val_2}).Nonempty := by -- We see that the set without e_val_2 is still nonempty
              rw [Set.diff_nonempty] -- This statement is equivalent to G.neighborSet e_val_1 not being a subset of {e_val_2}
              by_contra is_subset -- Suppose it is a subset

              have eq_e_val : G.neighborSet e_val_1 = {e_val_2} := by -- Then I claim we contradict not_equal_to_val

                have e_val_2_is_subset : {e_val_2} ⊆ G.neighborSet e_val_1 := by -- Clearly {e_val_2} is a subset, as it is in G.neighborSet e_val_1
                  exact Set.singleton_subset_iff.mpr val_in_neighborSet

                exact Eq.symm (Set.Subset.antisymm e_val_2_is_subset is_subset) -- So subset holds from both sides, so we are done

              exact not_equal_to_val eq_e_val -- But we assumed it was not_eval, a contradiction

            -- As the set is nonempty, it must have a member, and such a member would be in the form the goal specificies
            exact Set.inter_nonempty_iff_exists_right.mp neighborSet_nonempty

          obtain ⟨a, a_props⟩ := exists_other_elem -- Obtain this a and label its properties
          obtain ⟨a_neq_val, a_in_n_set⟩ := a_props

          have a_in_G_1 : a ∈ G_1.verts := by -- I claim we have this a is in G_1

            have edges_neq : s(e_val_1, a) ≠ s(e_val_1, e_val_2) := by -- First, we see the edge linking it to e_val_1 is not s(e_val_1, e_val_2)
              rw [ne_eq, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq]
              simp_all only [Set.inter_singleton_eq_empty]
              simp [true_and, false_or] --This is equivalent to showing that e_val_1 = e_val_2 means a ≠ e_val_1wa
              exact fun a _ => empty_intersection (id (Eq.symm a))
              -- This follows from empty_intersection, as e_val_1 = e_val_2 would put them both in the intersection, even though its an empty set

            have in_G_e_removed_edgeSet :  s(e_val_1, a) ∈ G_e_removed.edgeSet := by-- Second, we see s(e_val_1, a) is in G_e_removed
              rw [G_e_removed_val]
              unfold putEdgeInSet
              rw [SimpleGraph.mem_edgeSet, SimpleGraph.deleteEdges_adj]
              -- As s(e_val_1, e_val_2) is the only edge deleted from G in G_e_removed, membership is equaivalent to
              -- not being s(e_val_1, e_val_2) and being an edge in G
              apply And.intro
              · exact a_in_n_set -- As a ∈ G.neighborSet e_val_1, the edge connecting them must be adjacent in G
              · exact edges_neq -- Done above

            have a_in_connComp : a ∈ (G_e_removed.connectedComponentMk e_val_1) := by -- I calim a in the same connected component as e_val_1 in G_e_removed
              apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj at in_G_e_removed_edgeSet
              -- As a and e_val_1 are adjacent, they are in the same connected component
              exact id (Eq.symm in_G_e_removed_edgeSet) -- As a is in its own connected component, being in e_val_1 follows from this

            rw [G_1_val]
            exact a_in_connComp -- a_in_connComp is equivalent to G_1.verts membership, so we are done

          simp_all only [SimpleGraph.mem_neighborSet, Set.mem_singleton_iff, SimpleGraph.irrefl]
          -- We previously showed G_1.verts = {e_val_1}, so a_in_G_1 means a is equal to e_val_1
          -- But a and e_val_1 are adjacent in G, contradicting irreflexitivity of simple graphs.

        rw [← SimpleGraph.mem_neighborSet] at G_adj_getVert -- We get that p.getVert (j + 1) is in the neighbor set of p.getVert j in G

        simp_all only [Set.mem_singleton_iff, true_or] -- As this neighbor set only consists of only e_val_2, we see p.getVert (j + 1) = e_val_2

        exact Or.symm ((fun p => (true_or p).mpr) (e_val_2 = e_val_1) trivial) -- Which was exactly one side of the 'or' statement in the goal, so we are done

      | inr j_get_vert_eq_val_2 => -- Suppose p.getVert j = e_val_2 was true, then the proof is the same as above

        have val_2_neighbourSet : G.neighborSet e_val_2 = {e_val_1} := by

          have val_in_neighborSet : e_val_1 ∈ G.neighborSet e_val_2 := by
            exact id (SimpleGraph.adj_symm G e_val_edge)

          by_contra other_elem

          have exists_other_elem : ∃ a, a ≠ e_val_1 ∧ a ∈ G.neighborSet e_val_2 := by

            have neighborSet_nonempty : ((G.neighborSet e_val_2) \ {e_val_1}).Nonempty := by
              rw [Set.diff_nonempty]
              by_contra is_subset

              have eq_e_val : G.neighborSet e_val_2 = {e_val_1} := by

                have e_val_1_is_subset : {e_val_1} ⊆ G.neighborSet e_val_2 := by
                  exact Set.singleton_subset_iff.mpr val_in_neighborSet

                exact Eq.symm (Set.Subset.antisymm e_val_1_is_subset is_subset)

              exact other_elem eq_e_val

            exact Set.inter_nonempty_iff_exists_right.mp neighborSet_nonempty

          obtain ⟨a, a_props⟩ := exists_other_elem
          obtain ⟨a_neq_val, a_in_n_set⟩ := a_props

          have a_in_G_2 : a ∈ G_2.verts := by

            have edges_neq : s(e_val_2, a) ≠ s(e_val_1, e_val_2) := by
              simp_all only [ne_eq, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, false_and, Prod.swap_prod_mk,
                not_false_eq_true, Set.inter_singleton_eq_empty, Set.mem_singleton_iff, and_false]

            have in_G_e_removed_edgeSet :  s(e_val_2, a) ∈ G_e_removed.edgeSet := by
              rw [G_e_removed_val]
              unfold putEdgeInSet
              rw [SimpleGraph.mem_edgeSet]
              rw [SimpleGraph.deleteEdges_adj]
              apply And.intro
              · exact a_in_n_set
              · exact edges_neq

            have a_in_connComp : a ∈ (G_e_removed.connectedComponentMk e_val_2) := by
              apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj at in_G_e_removed_edgeSet
              exact id (Eq.symm in_G_e_removed_edgeSet)

            rw [G_2_val]
            exact a_in_connComp

          simp_all only [SimpleGraph.mem_neighborSet, Set.mem_singleton_iff, SimpleGraph.irrefl]

        rw [← SimpleGraph.mem_neighborSet] at G_adj_getVert
        simp_all only [Set.mem_singleton_iff, true_or]

  have triv_lt : p.length ≤ p.length := by
    exact Nat.le_refl p.length
  apply all_getVert_e_val at triv_lt
  simp [SimpleGraph.Walk.getVert_length] at triv_lt
  simp_all only [ne_eq, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, false_and, Prod.swap_prod_mk, or_self,
    not_false_eq_true]

/-- A proof that if the cardinality of a connected component generated by the endpoint of an edge is not one, and the parent graph G is preconnected, then there is no edge not in the connected component-/
lemma have_edge_contradiction {V : Type} [Finite V] [Nonempty V] {G G_e_removed: SimpleGraph V} (G_preconnected : G.Preconnected)
                              {e_val_1 e_val_2 : V} (edge_in_G : s(e_val_1, e_val_2) ∈ G.edgeSet)
                              (G_e_removed_val : G_e_removed = G.deleteEdges (putEdgeInSet s(e_val_1, e_val_2))) {G' G'' : G.Subgraph}
                              (G'_val : G' = connectedComponentToSubGraph G (G_e_removed.connectedComponentMk e_val_1))
                              (G''_val : G'' = connectedComponentToSubGraph G (G_e_removed.connectedComponentMk e_val_2))
                              (empty_intersection : G'.verts ∩ G''.verts = ∅) (card_neq_one : (Fintype.ofFinite G'.verts).card ≠ 1)
                              {e_num_1 e_num_2 : V} (e_num_not_in_G' : s(e_num_1, e_num_2) ∉ G'.edgeSet)
                              (e_num_not_in_G'' : s(e_num_1, e_num_2) ∉ G''.edgeSet) (e_num_in_G : s(e_num_1, e_num_2) ∈ G.edgeSet)
                              (e_num_in_G_e_removed : s(e_num_1, e_num_2) ∈ G_e_removed.edgeSet) : False := by

  let G'_connComponent := (G_e_removed.connectedComponentMk e_val_1)

  rw [G'_val, G''_val, G_e_removed_val] at empty_intersection

  have e_1_G_e_removed_not_reachable : ∀ v, v ∈ G'.verts ∧ v ≠ e_val_1 ∧ v ≠ e_val_2 → G_e_removed.Reachable e_num_1 v := by

    have e_num_1_not_in_G' : e_num_1 ∉ G'.verts := by -- Required for below
      exact edge_not_in_connComp_implies_vert_not_in G'_val e_num_not_in_G' e_num_in_G e_num_in_G_e_removed -- We use another result proving this
    have e_num_1_not_in_G'' : e_num_1 ∉ G''.verts := by
      exact edge_not_in_connComp_implies_vert_not_in G''_val e_num_not_in_G'' e_num_in_G e_num_in_G_e_removed

    rw [G_e_removed_val] at G'_val -- Sort out values for reachableToAllVerts to handle
    rw [G'_val] at e_num_1_not_in_G'
    rw [G''_val, G_e_removed_val] at e_num_1_not_in_G''
    rw [G_e_removed_val, G'_val]
    exact reachableToAllVerts G_preconnected edge_in_G rfl rfl rfl empty_intersection e_num_1_not_in_G' e_num_1_not_in_G''

  have e_2_G_e_removed_not_reachable: ∀ v, v ∈ G'.verts ∧ v ≠ e_val_1 ∧ v ≠ e_val_2 → G_e_removed.Reachable e_num_2 v := by

    have edge_symm : s(e_num_1, e_num_2) = s(e_num_2, e_num_1) := by -- We swap the edges around so that we can use the same lemma as the e_num_1 case
      rw [Sym2.eq_swap]
    rw [edge_symm] at e_num_not_in_G' e_num_not_in_G'' e_num_in_G e_num_in_G_e_removed

    have e_num_2_not_in_G' : e_num_2 ∉ G'.verts := by
      exact edge_not_in_connComp_implies_vert_not_in G'_val e_num_not_in_G' e_num_in_G e_num_in_G_e_removed

    have e_num_2_not_in_G'' : e_num_2 ∉ G''.verts := by
      exact edge_not_in_connComp_implies_vert_not_in G''_val e_num_not_in_G'' e_num_in_G e_num_in_G_e_removed

    rw [G_e_removed_val] at G'_val
    rw [G'_val] at e_num_2_not_in_G'
    rw [G''_val, G_e_removed_val] at e_num_2_not_in_G''
    rw [G_e_removed_val, G'_val]
    exact reachableToAllVerts G_preconnected edge_in_G rfl rfl rfl empty_intersection e_num_2_not_in_G' e_num_2_not_in_G''

  have e_num_in_G' : Quot.mk (Sym2.Rel V) (e_num_1, e_num_2) ∈ G'.edgeSet := by

    have exists_other_vert : ∃ v ∈ G'.verts, v ≠ e_val_1 ∧ v ≠ e_val_2 := by
      have without_e_val_nonempty : Nonempty ↑(G'.verts \ (putElemInSet e_val_1)) := by
        unfold putElemInSet
        by_contra is_empty
        rw [not_nonempty_iff] at is_empty -- If this is not true, then the set is empty

        have eq : G'.verts = {e_val_1} := by -- As it is empty, (putElemInSet e_val_1) must've been the whole se t
          simp_all only [isEmpty_subtype, Set.mem_diff, not_and, not_not]
          exact Eq.symm (Set.Subset.antisymm (fun ⦃a⦄ => congrArg G_e_removed.connectedComponentMk) is_empty)
          -- We now have they are both subsets of one and other so are equal

        have card_eq_one : (Fintype.ofFinite G'.verts).card = 1 := by -- So cardinality is one
          rw [eq] -- sub in the above
          simp_all only [Fintype.card_unique] -- Single element sets always have cardanilty one

        exact card_neq_one card_eq_one -- But it was an assumption that the cardinality was not one, so we are done

      simp_all only [nonempty_subtype]
      obtain ⟨a, a_props⟩ := without_e_val_nonempty

      have a_neq_e_val_2 : a ≠ e_val_2 := by 
        by_contra eq_val_2

        rw [← G'_val] at a_props 
        have a_in_G' : a ∈ G'.verts := by
          exact Set.mem_of_mem_diff a_props

        have a_in_G'' : a ∈ G''.verts := by
          rw [eq_val_2, G''_val]
          rfl
        
        have a_in_inter : a ∈ G'.verts ∩ G''.verts := by
          exact Set.mem_inter a_in_G' a_in_G''

        rw [← G_e_removed_val, ← G'_val, ← G''_val] at empty_intersection 
        rw [empty_intersection] at a_in_inter
        exact a_in_inter -- So a is in empty set, a contradiction
      
      simp_all only [ne_eq]
      obtain ⟨left, right⟩ := a_props
      apply Exists.intro
      · apply And.intro
        · exact left
        · simp_all only [not_false_eq_true, and_true]
          exact right -- As the set in which such a v would be in is nonempty, it must exist

    obtain ⟨v, v_props⟩ := exists_other_vert

    have num_1_in_connComp : e_num_1 ∈ G'_connComponent := by

      have e_1_e_val_1_reachable : G_e_removed.Reachable e_num_1 e_val_1 := by

        have e_1_v_reachable : G_e_removed.Reachable e_num_1 v  := by
          exact e_1_G_e_removed_not_reachable v v_props

        obtain ⟨v_in_verts, v_neq_e_val_1⟩ := v_props

        have v_e_val_1_reachable : G_e_removed.Reachable v e_val_1 := by
          rw [G'_val] at v_in_verts
          exact SimpleGraph.ConnectedComponent.exact v_in_verts

        exact SimpleGraph.Reachable.trans e_1_v_reachable v_e_val_1_reachable

      -- As it is reachable from e_val_1, it is in the connected component
      exact reachableByCompImpliesconnComp rfl (id (SimpleGraph.Reachable.symm e_1_e_val_1_reachable))

    have num_2_in_connComp : e_num_2 ∈ G'_connComponent := by

      have e_2_e_val_1_reachable : G_e_removed.Reachable e_num_2 e_val_1 := by

        have e_2_v_reachable : G_e_removed.Reachable e_num_2 v  := by
          exact e_2_G_e_removed_not_reachable v v_props

        obtain ⟨v_in_verts, v_neq_e_val_1⟩ := v_props

        have v_e_val_1_reachable : G_e_removed.Reachable v e_val_1 := by
          rw [G'_val] at v_in_verts
          exact SimpleGraph.ConnectedComponent.exact v_in_verts

        exact SimpleGraph.Reachable.trans e_2_v_reachable v_e_val_1_reachable

      exact reachableByCompImpliesconnComp rfl (id (SimpleGraph.Reachable.symm e_2_e_val_1_reachable))

    rw [SimpleGraph.mem_edgeSet] at edge_in_G

    rw [SimpleGraph.Subgraph.mem_edgeSet] -- We see our goal is to show adjacency in G_e_removed

    have in_edgeSet : (G.Adj e_num_1 e_num_2) ∧ e_num_1 ∈ G'_connComponent ∧ e_num_2 ∈ G'_connComponent := by -- Follows from collecting the statements above and edge_in_G
      rw [← SimpleGraph.mem_edgeSet]
      simp_all only [true_and]

    rw [G'_val]
    exact in_edgeSet

  exact e_num_not_in_G' e_num_in_G'

/-- The first part of the proof that (1,2,3,4) → (5). If a graph G on a finite and nonempty vertex set is a tree, then we have |E(G)| = |V(G)| - 1 -/
theorem onetwothreefour_implies_five {V : Type} [Finite V] (G : SimpleGraph V) (G_is_tree : isTree G) (nonempty: Nonempty V):
  ((Fintype.ofFinite G.edgeSet).card = (Fintype.ofFinite V).card - 1) := by
  have G_is_connected : G.Connected := by
    unfold isTree at G_is_tree -- as G is a tree we see it is connected and acylic
    simp [G_is_tree] -- G being connected is exactly what we need

  --We prove |E(G)| = |V (G)| − 1 by induction on n = |V (G)|.
  -- `generalize` creates a "new" variable `nV` which can then be used for induction
  generalize hnV : (Fintype.ofFinite V).card - 1 = nV
  induction nV using Nat.case_strong_induction_on with -- equivalent to starting at |V (G)| = 1
  --We prove |E(G)| = |V (G)| − 1 by induction on n = |V (G)|.

  -- TRY   induction p generalizing i with
  --| nil => simp
  --| cons h p ih => cases i <;> simp [getVert, ih, Nat.succ_lt_succ_iff]

  | hz     =>
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
    simp_all only [ne_eq, Fintype.card_ne_zero, not_false_eq_true]

  have ind_hyp : (Fintype.ofFinite V).card = 1 := by  -- Clearly this holds, as |V (T)| = 1 is what I am assuming for the zero section of the induction,
    exact nat_minus_one_eq_zero_implies_eq_one hnV nonzero
  exact oneVertexbutEdgeIsFalse G w w_1 ind_hyp

  -- Now must prove it holds for |V (G)| − 1 = n + 1 if it holds for |V (G)| − 1 = n
  | hi y hy=>

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

        simp_all only [reduceCtorEq]
        --So we have shown there exist two element in V, not equal to eachother

      obtain ⟨x, prop⟩ := two_elems_in_V -- Let x be this first element
      obtain ⟨y, prop⟩ := prop -- Let y be the second, and let prop be their relation

      have no_path : ¬(G.Reachable x y) := by -- As x and y are not the same element of V and G is the empty graph, there is no edges at either of them
                                                -- thus there does not exist a path between them
        rw [SimpleGraph.emptyGraph_eq_bot] at g_is_empty_graph -- The proof falls out of properies of the empty graph
        simp_all only [SimpleGraph.reachable_bot]
        rw [not_false_eq_true]
        trivial

      have every_elem_in_V_connected_in_G : ∀ m n : V, G.Reachable m n := by -- Want to show there exists a path in G between all pairs of V
        have G_preconnected : G.Preconnected := by -- Preconnected means every pair of vertices is reachable from one another. It falls out of the defintion of connectivty in matlib
          exact G_is_connected.preconnected
        unfold SimpleGraph.Preconnected at G_preconnected -- We can see Preconnected is the same as our goal, so we are done
        exact G_preconnected

      exact no_path (every_elem_in_V_connected_in_G x y) -- This contradicts the lack of path we found between x and y, thus we have found our contradiction and G must not be connected

    exact not_connected G_is_connected -- Have proved G is not connected here, but we know it is, thus the edgeset cannot be empty

  have exist_elem_in_G : ∃ e : Sym2 V, e ∈ G.edgeSet := by
    exact nonempty_subtype.mp NonemptyEdgeset

  obtain ⟨e_val, e_prop⟩ := exist_elem_in_G

  have three_result : (¬(G.deleteEdges (putEdgeInSet (e_val))).Connected) := by -- we acquire the result that 3 already holding gives us
    exact three_implies_G_without_e_disconnected G e_val -- ie By (3), G − e is disconnected.

  let G_e_removed := G.deleteEdges (putEdgeInSet (e_val)) -- this is G without the edge e

  obtain ⟨e_val_1, e_val_2⟩ := e_val
  let e_val := Quot.mk (Sym2.Rel V) (e_val_1, e_val_2) -- redefine e_val for usage later (Otherwise lean gets confused due to the nature of obtain)

  -- Let G1 and G2 be connected components of G − e.
  let G_1_connComponent := G_e_removed.connectedComponentMk e_val_1 -- as removing e disconnects G, and the rest of G is connected, we now have two connected components in this new graph
  let G_2_connComponent := G_e_removed.connectedComponentMk e_val_2 -- each of these contains exactly one endpoint of e, so we can simply find the connected components containing each of them

 -- Then create subgraph of all vertices in this component (We need this as connectedComponent is not naturally a graph)
  let G_1 := connectedComponentToSubGraph G G_1_connComponent.supp
  let G_2 := connectedComponentToSubGraph G G_2_connComponent.supp

  have G_is_acylic : isAcyclic G := by -- needed to obtain next two properties
    unfold isTree at G_is_tree -- as G is a tree we see it is connected and acylic
    simp [G_is_tree] -- G being connected is exactly what we need

  have G_1_isTree : isTree G_1.coe := by
    have connected : G_1.coe.Connected := by
      exact connected_component_coe_is_connected e_val_1 e_prop rfl

    have acylic : isAcyclic G_1.coe := by
      exact conn_comp_acyclic G_is_tree e_prop rfl
    unfold isTree
    exact ⟨connected, acylic⟩

  have G_2_isTree : isTree G_2.coe := by
    have needed_equality : G_e_removed = G.deleteEdges (putEdgeInSet ( s(e_val_2,e_val_1) ) ) := by
      rw [Sym2.eq_swap]
    have h_e : s(e_val_2,e_val_1) ∈ G.edgeSet := by
      rw [Sym2.eq_swap]
      exact e_prop

    have connected : G_2.coe.Connected := by
      exact connected_component_coe_is_connected e_val_2 h_e needed_equality

    have acylic : isAcyclic G_2.coe := by
      exact conn_comp_acyclic G_is_tree h_e needed_equality

    unfold isTree
    exact ⟨connected, acylic⟩

  have empty_intersection : G_1.verts ∩ G_2.verts = ∅ := by -- Needed for many results below, so is proved outside of them
    exact conn_comp_empty_intersection G_is_acylic e_prop G_e_removed rfl rfl rfl -- use a proof I have written elsewhere

  -- from notes: Since each of them has fewer vertices than T, we know that |E(T1)| = |V (T1)| − 1 & |E(T2)| = |V (T2)| − 1.
  -- from notes: We also know that |V (T)| = |V (T1)| + |V (T2)| and |E(T)| = |E(T1)| + |E(T2)| + 1.

  have h_G_1 : (Fintype.ofFinite ↑G_1.edgeSet).card = (Fintype.ofFinite ↑G_1.verts).card - 1 := by
    have less_than_y : (Fintype.ofFinite ↑G_1.verts).card - 1 ≤ y := by
      by_contra not_leq
      apply Nat.gt_of_not_le at not_leq -- We see (Fintype.ofFinite ↑G_1.verts).card - 1 > y if the result doesnt hold

      have eq_V : (Fintype.ofFinite ↑G_1.verts).card = (Fintype.ofFinite V).card :=  by -- I claim this means ↑G_2.verts and V have the same cardinality

        have card_min_one_eq_y_plus_one : (Fintype.ofFinite ↑G_1.verts).card - 1 = y + 1 := by

          have card_min_1_lt : (Fintype.ofFinite ↑G_1.verts).card - 1 ≤ (Fintype.ofFinite V).card - 1:= by

            have card_lt : (Fintype.ofFinite ↑G_1.verts).card ≤ (Fintype.ofFinite V).card := by
              exact my_set_fintype_card_le_univ (Fintype.ofFinite V) G_1.verts (Fintype.ofFinite ↑G_1.verts)

            simp_all only [Nat.pred_eq_succ_iff, nonempty_subtype, Nat.add_one_sub_one, tsub_le_iff_right] -- follows from both sides of card_lt being nonempty

          rw [hnV] at card_min_1_lt --this gives (Fintype.ofFinite ↑G_1.verts).card - 1 ≤ y + 1 by inductive hypothesis
          exact Eq.symm (Nat.le_antisymm not_leq card_min_1_lt) -- (Fintype.ofFinite ↑G_1.verts).card - 1 is bounded such that it must be y +1

        simp_all only [Nat.pred_eq_succ_iff, card_min_one_eq_y_plus_one] -- follow from trivial subsitutions in card_min_one_eq_y_plus_one

      rw [← type_eq_set_iff_card_the_same] at eq_V -- Use a previous result to see that eq_V implies G_1 contains all elements of V

      have e_val_not_in : e_val_2 ∉ ↑G_1.verts := by -- But I claim e_val_2 in not in ↑G_1.verts

        by_contra is_in -- suppose e_val_1 is in the set

        have in_inter : e_val_2 ∈ ↑G_1.verts ∩ ↑G_2.verts := by -- Follows from being in both G_2 by construction and now G_1
          exact Set.mem_inter (eq_V e_val_2) rfl

        simp_all only [Set.mem_empty_iff_false] -- But this is empty, contradiction

      exact e_val_not_in (eq_V e_val_2) -- yet e_val_1 is of type V, so we have acontradiction to eq_V's statement



    -- inductive hypothesis
    sorry


  have h_G_2 : (Fintype.ofFinite ↑G_2.edgeSet).card = (Fintype.ofFinite ↑G_2.verts).card - 1 := by -- Exactly the same as above but with G_2 and e_val_1
    have less_than_y : (Fintype.ofFinite ↑G_2.verts).card - 1 ≤ y := by
      by_contra not_leq
      apply Nat.gt_of_not_le at not_leq

      have eq_V : (Fintype.ofFinite ↑G_2.verts).card = (Fintype.ofFinite V).card :=  by

        have card_min_one_eq_y_plus_one : (Fintype.ofFinite ↑G_2.verts).card - 1 = y + 1 := by

          have card_min_1_lt : (Fintype.ofFinite ↑G_2.verts).card - 1 ≤ (Fintype.ofFinite V).card - 1:= by

            have card_lt : (Fintype.ofFinite ↑G_2.verts).card ≤ (Fintype.ofFinite V).card := by
              exact my_set_fintype_card_le_univ (Fintype.ofFinite V) G_2.verts (Fintype.ofFinite ↑G_2.verts)

            simp_all only [Nat.pred_eq_succ_iff, nonempty_subtype, Nat.add_one_sub_one, tsub_le_iff_right]

          rw [hnV] at card_min_1_lt
          exact Eq.symm (Nat.le_antisymm not_leq card_min_1_lt)

        simp_all only [Nat.pred_eq_succ_iff, card_min_one_eq_y_plus_one]

      rw [← type_eq_set_iff_card_the_same] at eq_V

      have e_val_not_in : e_val_1 ∉ ↑G_2.verts := by

        by_contra is_in

        have in_inter : e_val_1 ∈ ↑G_1.verts ∩ ↑G_2.verts := by
          exact Set.mem_inter rfl (eq_V e_val_1)

        simp_all only [Set.mem_empty_iff_false]

      exact e_val_not_in (eq_V e_val_1)

    sorry

  -- This is needed in the vert and edge set cardinality statements that are proved below, thus it is defined outside of both of them
  have edgeSet_eq_union : G.edgeSet = G_1.edgeSet ∪  G_2.edgeSet ∪ {e_val}:= by
    have subset : G.edgeSet ⊆ G_1.edgeSet ∪ G_2.edgeSet ∪ (putEdgeInSet e_val) := by
      unfold putEdgeInSet
      by_contra not_subset

      have exists_edge : ∃ e : G.edgeSet, (↑e ∉ G_1.edgeSet) ∧ (↑e ∉ G_2.edgeSet) ∧ (↑e ≠ e_val) := by
        by_contra no_such_edge
        simp_all only [not_exists, not_and] -- We see this means that one of the results must fail. WLOG this is chosen to be (↑e ≠ e_val)

        -- The no_such_edge holding allows us to contradict our assumption not_subset
        have subset_holds : G.edgeSet ⊆ G_1.edgeSet ∪ G_2.edgeSet ∪ (putEdgeInSet e_val) := by
          unfold putEdgeInSet
          have in_G_implies_in_union : ∀ e ∈ G.edgeSet, e ∈ G_1.edgeSet ∪ G_2.edgeSet ∪ (putEdgeInSet e_val) := by
            intro edge edge_prop

            let in_G1 := edge ∈ G_1.edgeSet
            by_cases in_G1
            · rename_i edge_in_G1 -- edge ∈ G_1.edgeSet
              simp_all only [in_G1]
              rw [Set.union_assoc] -- Need to rewrite goal to use Set.mem_union_left
              exact Set.mem_union_left (G_2.edgeSet ∪ putEdgeInSet e_val) edge_in_G1 -- It is in one part of the union so is in the whole union, proving the goal

            · rename_i edge_not_in_G1 -- edge ∉ G_1.edgeSet
              simp_all only [in_G1]
              let in_G2 := edge ∈ G_2.edgeSet
              by_cases in_G2

              · rename_i edge_in_G2 -- edge ∈ G_2.edgeSet
                simp_all only [in_G2]
                rw [Set.union_comm G_1.edgeSet G_2.edgeSet, Set.union_assoc] -- Need to rewrite goal to use Set.mem_union_left
                exact Set.mem_union_left (G_1.edgeSet ∪ putEdgeInSet e_val) edge_in_G2 -- Then same as in G1 case

              · rename_i edge_not_in_G2 -- edge ∉ G_2.edgeSet
                simp_all only [in_G2]
                let eq_e_val := edge = e_val
                by_cases eq_e_val

                · rename_i edge_eq_e_val -- edge = e_val
                  simp_all only [eq_e_val]
                  exact Set.mem_union_right (G_1.edgeSet ∪ G_2.edgeSet) rfl -- Same as in G1/G2 case

                · rename_i edge_not_eq_e_val -- edge ≠ e_val
                  simp_all only [eq_e_val]
                  exact False.elim (no_such_edge ⟨edge, edge_prop⟩ edge_not_in_G1 edge_not_in_G2 edge_not_eq_e_val)
                  -- edge_not_eq_e_val is a contradiction to no_such_edge -- so this case cannot occur

          exact in_G_implies_in_union -- This result is equivalent to G.edgeSet being a subset

        exact not_subset subset_holds -- so it is a subset and also not a subset by our contradiction assumption, clearly this cannot be true.
        -- So we close the goal and see that such an edge must exist

      obtain ⟨edge, properties⟩ := exists_edge -- Let edge be this edge
      obtain ⟨not_in_G_1, properties⟩ := properties -- We see that edge ∉ G_1.edgeSet,
      obtain ⟨not_in_G_2, not_e_val⟩ := properties -- edge ∉ G_2.edgeSet, &  edge ≠ e_val
      obtain ⟨edge, edge_in_G⟩ := edge -- Also seperate its value and its membership to G
      obtain ⟨e_1, e_2⟩ := edge -- Let e_1 and e_2 be the endpoints of this edge

      have G_preconnected : G.Preconnected := by exact G_is_connected.preconnected
      unfold SimpleGraph.Preconnected at G_preconnected

      let cards_eq_one := (Fintype.ofFinite G_1.verts).card = 1 ∧ (Fintype.ofFinite G_2.verts).card = 1
      by_cases cards_eq_one
      · rename_i both_eq_one

        have empty_edgeSet : Nonempty G_e_removed.edgeSet := by

          have e_1_e_2_is_in : s(e_1, e_2) ∈ G_e_removed.edgeSet := by
            by_contra not_in
            rw [SimpleGraph.edgeSet_deleteEdges] at not_in

            have in_e_val_set : s(e_1, e_2) ∈ putEdgeInSet s(e_val_1, e_val_2) := by
              simp_all only [Set.mem_diff, true_and, not_not]

            exact not_e_val in_e_val_set

          rw [nonempty_subtype]
          exact Exists.intro s(e_1, e_2) e_1_e_2_is_in

        exact both_cards_eq_one_gives_contradiction G_preconnected e_prop rfl rfl both_eq_one empty_intersection rfl empty_edgeSet not_subset
      · rename_i one_neq_one
        simp_all only [cards_eq_one]

        have one_component_card_neq_one : (Fintype.ofFinite G_1.verts).card ≠ 1 ∨ (Fintype.ofFinite G_2.verts).card ≠ 1 := by -- Rewrite the statement in a manner where case analysis is possible
          exact (Decidable.not_and_iff_or_not ((Fintype.ofFinite G_1.verts).card = 1)
                ((Fintype.ofFinite G_2.verts).card = 1)).mp one_neq_one

        have e_1_e_2_edge_in_G_e_removed : s(e_1, e_2) ∈ G_e_removed.edgeSet := by -- Needed for have_edge_contradiction. Follows from not_e_val
          by_contra not_in
          have eq_e_val : s(e_1, e_2) = e_val := by -- The only edge in G but not in G_e_removed is e_val, as it was the only edge deleted
            rw [SimpleGraph.edgeSet_deleteEdges] at not_in --Follows from property of deleteEdges
            simp_all only [Set.mem_diff, Set.mem_singleton_iff, true_and, not_not] -- As the deleted edgeset was a singleton, the result follows naturally
            exact not_e_val not_in
          exact not_e_val eq_e_val -- Thus the is e_val and is not e_val, so we are done

        cases one_component_card_neq_one
        · rename_i G_1_verts_neq_1 -- If G_1.verts is not size 1
          exact have_edge_contradiction G_preconnected e_prop rfl rfl rfl empty_intersection G_1_verts_neq_1 not_in_G_1 not_in_G_2 edge_in_G e_1_e_2_edge_in_G_e_removed

        · rename_i G_2_verts_neq_1 -- If G_2.verts is not size 1

          -- In order to use have_edge_contradiction and close the goal, we must sort out some of our results to have e_val_2 be the first vertex in e_val
          rw [Set.inter_comm] at empty_intersection

          have deleteEdges_eq : G_e_removed = G.deleteEdges (putEdgeInSet s(e_val_2, e_val_1)) := by -- We gain a new defintion for G_e_removed
            simp_all [Sym2.eq_swap]
          have edge_eq : Quot.mk (Sym2.Rel V) (e_val_1, e_val_2) = Quot.mk (Sym2.Rel V) (e_val_2, e_val_1) := by -- & See s(e_val_1,e_val_2) = s(e_val_2,e_val_1)
            simp_all [Sym2.eq_swap]
          simp_all only [edge_eq, deleteEdges_eq] -- And we apply these qualities as much as we can


          -- We see we are able to swap the edge values around within G_1's defintition (simp does not do this)
          have G_1_eq : G_1 = connectedComponentToSubGraph G ↑((G.deleteEdges (putEdgeInSet s(e_val_2, e_val_1))).connectedComponentMk e_val_1) := by

            -- This equalitiy is trivial due to deleteEdges_eq and edge_eq though it must be asserted so it can be applied
            have triv_eq : G_1 = connectedComponentToSubGraph G ↑(G_e_removed.connectedComponentMk e_val_1) := by
              exact rfl

            rw [triv_eq, deleteEdges_eq]-- We rewrite with triv_eq's equality, and then deleteEdges_eq within that, and we are done

          -- This is the same as the above but for G_2
          have G_2_eq : G_2 = connectedComponentToSubGraph G ↑((G.deleteEdges (putEdgeInSet s(e_val_2, e_val_1))).connectedComponentMk e_val_2) := by

            have triv_eq : G_2 = connectedComponentToSubGraph G ↑(G_e_removed.connectedComponentMk e_val_2) := by
              exact rfl

            rw [triv_eq, deleteEdges_eq]

          -- As G_1 and G_2 equals themselves under this new ordering, naturally they have the same vertex & edge sets
          have G_1_eq_edges : G_1.edgeSet = (connectedComponentToSubGraph G ↑((G.deleteEdges (putEdgeInSet s(e_val_2, e_val_1))).connectedComponentMk e_val_1)).edgeSet := by
            exact congrArg SimpleGraph.Subgraph.edgeSet G_1_eq
          have G_2_eq_verts : G_2.verts = (connectedComponentToSubGraph G ↑((G.deleteEdges (putEdgeInSet s(e_val_2, e_val_1))).connectedComponentMk e_val_2)).verts := by
            exact congrArg SimpleGraph.Subgraph.verts G_2_eq
          have G_2_eq_edges : G_2.edgeSet = (connectedComponentToSubGraph G ↑((G.deleteEdges (putEdgeInSet s(e_val_2, e_val_1))).connectedComponentMk e_val_2)).edgeSet := by
            exact congrArg SimpleGraph.Subgraph.edgeSet G_2_eq

          -- Apply these results at other results so they can be used for have_edge_contradiction
          rw [G_1_eq, G_2_eq] at empty_intersection
          rw [G_1_eq_edges] at not_in_G_1
          rw [G_2_eq_verts] at G_2_verts_neq_1
          rw [G_2_eq_edges] at not_in_G_2

          -- And have_edge_contradiction closes the goal
          exact have_edge_contradiction G_preconnected e_prop rfl rfl rfl empty_intersection G_2_verts_neq_1 not_in_G_2 not_in_G_1 edge_in_G e_1_e_2_edge_in_G_e_removed

    have superset : G.edgeSet ⊇ G_1.edgeSet ∪ G_2.edgeSet ∪ (putEdgeInSet e_val) := by
      simp [Set.union_subset_iff]
      apply And.intro -- if we prove each part of the union is a subset, then the union is a subset
      · apply And.intro
        · exact SimpleGraph.Subgraph.edgeSet_subset G_1
        · exact SimpleGraph.Subgraph.edgeSet_subset G_2
      · unfold putEdgeInSet
        have e_val_in_edgeSet : e_val ∈ G.edgeSet := by
          exact e_prop
        exact Set.singleton_subset_iff.mpr e_prop

    exact Set.Subset.antisymm subset superset

  have vertSetEquality : (Fintype.ofFinite V).card = (Fintype.ofFinite ↑G_1.verts).card + (Fintype.ofFinite ↑G_2.verts).card := by

    have h_alpha : ∀ v : V, v ∈ (G_1.verts ∪ G_2.verts) := by
      by_contra not_in_a_component
      rw [not_forall] at not_in_a_component
      obtain ⟨v, v_prop⟩ := not_in_a_component

      have not_in_either : v ∉ G_1.verts ∧ v ∉ G_2.verts := by -- v_prop is equivalent to it being in neither set
        rw [Set.mem_union, not_or] at v_prop
        exact v_prop

      let not_in_an_edge := IsEmpty (G.neighborSet v) -- v is either in an edge of v or not. If is in in an edge

      by_cases not_in_an_edge

      · rename_i holds -- Suppose there is no edge containing v
        simp_all only [not_in_an_edge]
        have not_reachable : ¬ G.Reachable v e_val_1 := by -- then clearly e_val is not reachable
          by_contra if_reachable
          rw [SimpleGraph.reachable_iff_nonempty_univ] at if_reachable
          obtain ⟨p, p_prop⟩ := if_reachable
          let v_1 := secondVertexInWalk G p
          have in_neighborSet : v_1 ∈ G.neighborSet v := by

            have are_Adjacent : G.Adj v v_1 := by

              have neq : v ≠ e_val_1 := by
                by_contra eq

                have not_reachable : ¬ G.Reachable v e_val_1 := by
                  subst eq
                  simp [isEmpty_subtype, SimpleGraph.mem_neighborSet] at holds
                  simp [← SimpleGraph.mem_edgeSet] at holds
                  simp_all only [SimpleGraph.mem_edgeSet]

                have is_reachable : G.Reachable v e_val_1 := by-- we changed this earlier so need to reaffirm it for the contradiction
                  exact SimpleGraph.Walk.reachable p

                exact not_reachable is_reachable
              have zero_lt_walk_length : 0 < p.length := by

                have not_nil : ¬ p.Nil := by
                  exact SimpleGraph.Walk.not_nil_of_ne neq

                exact SimpleGraph.Walk.not_nil_iff_lt_length.mp not_nil

              have get_vert_adj : G.Adj (p.getVert 0) (p.getVert 1) := by
                exact SimpleGraph.Walk.adj_getVert_succ p zero_lt_walk_length

              rw [SimpleGraph.Walk.getVert_zero] at get_vert_adj
              exact get_vert_adj

            exact are_Adjacent

          have not_isEmpty : ¬ IsEmpty (G.neighborSet v) := by
            rw [not_isEmpty_iff]
            rw [isEmpty_subtype] at holds
            exact False.elim (holds v_1 in_neighborSet)

          exact not_isEmpty holds

        have G_is_preconnected : G.Preconnected := by exact G_is_connected.preconnected

        unfold SimpleGraph.Preconnected at G_is_preconnected
        exact not_reachable (G_is_preconnected v e_val_1)

      · rename_i doesnt_hold
        simp_all only [not_in_an_edge]
        rw [not_isEmpty_iff] at doesnt_hold

        have exists_other_vert : ∃ a, a ∈ ↑(G.neighborSet v) := by
          exact nonempty_subtype.mp doesnt_hold

        obtain ⟨u, u_prop⟩ := exists_other_vert
        unfold SimpleGraph.neighborSet at u_prop

        have v_u_Adj : G.Adj v u := by
          exact u_prop

        rw [← SimpleGraph.mem_edgeSet] at v_u_Adj

        have in_union_or : s(v, u) ∈ G_1.edgeSet ∨ s(v, u) ∈ G_2.edgeSet ∨ s(v, u) = e_val := by -- This follows from edgeSet_eq_union and v_u_Adj
          simp_all only [Set.union_singleton, Set.mem_insert_iff, Sym2.eq, Sym2.rel_iff', e_val]
          cases v_u_Adj with
          | inl h_1 =>
            cases h_1 with
            | inl h_2 => simp_all only [true_or, or_true]
            | inr h_3 => simp_all only [or_true]
          | inr h_2 =>
            cases h_2 with
            | inl h_1 => simp_all only [true_or]
            | inr h_3 => simp_all only [true_or, or_true]


        cases' in_union_or with h_1 h_2

        · have in_G_1 : v ∈ G_1.verts := by
            exact G_1.edge_vert h_1
          simp_all only [not_true_eq_false]

        · cases' h_2 with h_2 h_3

          · have in_G_2: v ∈ G_2.verts := by
              exact G_2.edge_vert h_2
            simp_all only [not_true_eq_false]

          · have in_G_1_or_G_2 : v ∈ G_1.verts ∨ v ∈ G_2.verts := by
              have v_eq_or : v = e_val_1 ∨ v = e_val_2 := by
                rw [Sym2.eq, Sym2.rel_iff',Prod.mk.injEq, Prod.swap_prod_mk] at h_3
                rw [Prod.mk.injEq] at h_3
                cases h_3 with
                | inl h_2 => simp_all only [true_or]
                | inr h_4 => simp_all only [or_true]

              exact Or.imp (congrArg G_e_removed.connectedComponentMk) (congrArg G_e_removed.connectedComponentMk) v_eq_or

            exact v_prop in_G_1_or_G_2

        -- all of which imply the vertex is in one of our connected component done

    let union := G_1.verts ∪ G_2.verts -- I have to turn union into a single set object otherwise Lean gets mad at me in the next line
    have eq_to_union_card : (Fintype.ofFinite V).card = (Fintype.ofFinite (union)).card := by -- We see that the cardinality of V and the union of G_1 and G_2's vertices are the same
      rw [type_eq_set_iff_card_the_same] at h_alpha
      simp_all only [union]
      -- This a proof that if all of the elements of type V are in some set, then the set and the type have the same cardinality
      -- We have the requirement for this in h_alpha

    let intersection := G_1.verts ∩ G_2.verts

    have empty_intersection : G_1.verts ∩ G_2.verts = ∅ := by
      exact conn_comp_empty_intersection G_is_acylic e_prop G_e_removed rfl rfl rfl

    have card_eq  : (Fintype.ofFinite ↑G_1.verts).card + (Fintype.ofFinite ↑G_2.verts).card = (Fintype.ofFinite union).card := by
      exact union_minus_intersection_eq_sum_of_sets G_1.verts G_2.verts (id (Eq.symm empty_intersection))

    rw [card_eq]
    exact eq_to_union_card

  have edgeSetEquality : (Fintype.ofFinite G.edgeSet).card = (Fintype.ofFinite ↑G_1.edgeSet).card + (Fintype.ofFinite ↑G_2.edgeSet).card + 1 := by

    have size_equality : (Fintype.ofFinite G.edgeSet).card = (Fintype.ofFinite G_1.edgeSet).card + (Fintype.ofFinite G_2.edgeSet).card + (Fintype.ofFinite (putEdgeInSet e_val)).card:= by

      have first_eq : (Fintype.ofFinite G.edgeSet).card = (Fintype.ofFinite ↑(G_1.edgeSet ∪  G_2.edgeSet ∪ {e_val})).card := by
        exact my_card_congr' (Fintype.ofFinite ↑G.edgeSet) (Fintype.ofFinite ↑(G_1.edgeSet ∪ G_2.edgeSet ∪ {e_val})) (congrArg Set.Elem edgeSet_eq_union)
      rw [first_eq]

      have first_disjoint : ∅ = (G_1.edgeSet ∪ G_2.edgeSet) ∩ {e_val} := by
        by_contra not_disjoint

        -- doesnt work if i dont put putEdgeInSet in the result statement, thus has to be there
        have exists_common_edge : ∃ e, e ∈ (G_1.edgeSet ∪ G_2.edgeSet) ∧ e ∈ putEdgeInSet e_val := by-- If they are not disjoint they have a common elements
          unfold putEdgeInSet

          have nonempty : Nonempty ↑((G_1.edgeSet ∪ G_2.edgeSet) ∩ {e_val}) := by -- We see the intersection is nonempty
            exact Set.nonempty_iff_ne_empty'.mpr fun a => not_disjoint (id (Eq.symm a))

          exact nonempty_subtype.mp nonempty -- And the result follows from this theorem

        obtain ⟨e, e_prop⟩ := exists_common_edge -- obtain this edge e and its properties
        obtain ⟨e_prop_1, e_prop_2⟩ := e_prop

        have e_eq_e_val : e = e_val := by -- as it is in {e_val}, clearly e is e_val
          unfold putEdgeInSet at e_prop_2
          exact e_prop_2
        subst e_eq_e_val -- We then subst e_val for e

        cases e_prop_1 with -- split the union into its two cases
        | inl h => -- if e_val is in G_1.edgeSet

        have in_inter : e_val_2 ∈ G_1.verts ∩ G_2.verts := by
          have val_2_in_1 : e_val_2 ∈ G_1.verts := by -- e_val_2 is in G_1.verts as it contains an edge with it as an endpoint
            exact SimpleGraph.Subgraph.Adj.snd_mem h

          exact Set.mem_inter val_2_in_1 rfl

        rw [empty_intersection] at in_inter -- we have already shown G_1.verts ∩ G_2.verts = ∅, so sub it in
        exact in_inter -- an element cannot be in ∅, so e_val_2 has provided a contradiction

        | inr h => -- if e_val is in G_2.edgeSet (This proof is almost identical to the case above)

        have in_inter : e_val_1 ∈ G_1.verts ∩ G_2.verts := by
          have val_1_in_1 : e_val_1 ∈ G_1.verts := by
            rfl
          have val_1_in_2 : e_val_1 ∈ G_2.verts := by
            exact SimpleGraph.Subgraph.Adj.fst_mem h
          exact Set.mem_inter val_1_in_1 val_1_in_2

        rw [empty_intersection] at in_inter
        exact in_inter

      -- We can rewrite part of the cardinality equality, by consequence of the lemma union_minus_intersection_eq_sum_of_sets and the disjointness shown above
      have second_eq : (Fintype.ofFinite ↑(G_1.edgeSet ∪ G_2.edgeSet ∪ {e_val})).card = (Fintype.ofFinite ↑(G_1.edgeSet ∪ G_2.edgeSet)).card + (Fintype.ofFinite ↑(putEdgeInSet e_val)).card := by
        unfold putEdgeInSet
        have nonempty_sym2 : Nonempty (Sym2 V) := by exact Nonempty.intro e_val
        rw [union_minus_intersection_eq_sum_of_sets (G_1.edgeSet ∪ G_2.edgeSet) {e_val} first_disjoint]
      rw [second_eq] -- change the goal to reflect this

      have second_disjoint : ∅ = G_1.edgeSet ∩ G_2.edgeSet := by
        by_contra not_disjoint -- Suppose the intersection is nonempty

        have exists_common_edge : ∃ e, e ∈ G_1.edgeSet ∧ e ∈  G_2.edgeSet := by -- Then there exists an element such that it is in both sets
          have nonempty : Nonempty ↑(G_1.edgeSet ∩ G_2.edgeSet) := by-- Set is nonempty by consequence of not_disjoint
            exact Set.nonempty_iff_ne_empty'.mpr fun a => not_disjoint (id (Eq.symm a))
          exact nonempty_subtype.mp nonempty -- nonempty → exists element by pre-existing lemma

        obtain ⟨e, e_prop⟩ := exists_common_edge -- obtain this edge and its properties
        obtain ⟨e_vert_1, e_vert_2⟩ := e

        -- Then one of the endpoints (actually both but dont need to prove that) is in the vertex set of G_1 and the vertex set of G_2
        have e_vert_1_in_both : e_vert_1 ∈ G_1.verts ∩ G_2.verts := by

          have e_1_in_verts1 : e_vert_1 ∈ G_1.verts := by -- We see it is in G_1.verts as it is part of an edge in G_1
            have adj_in_G1 : G_1.Adj e_vert_1 e_vert_2 := by
              simp_all only [SimpleGraph.Subgraph.mem_edgeSet]
            exact G_1.edge_vert adj_in_G1

          have e_1_in_verts2 : e_vert_1 ∈ G_2.verts := by -- Same as above
            have adj_in_G2 : G_2.Adj e_vert_1 e_vert_2 := by
              simp_all only [SimpleGraph.Subgraph.mem_edgeSet]
            exact G_2.edge_vert adj_in_G2

          exact Set.mem_inter e_1_in_verts1 e_1_in_verts2 -- Thus in both, so in intersection

        -- But we previously showed G_1.verts ∩ G_2.verts = ∅ , so this e_vert_1 ∈ ∅, which is impossible
        simp_all only [Set.mem_empty_iff_false] -- So we get a contradiction and are done

      --exact same logic and type of result as second_eq
      have third_eq : (Fintype.ofFinite ↑(G_1.edgeSet ∪ G_2.edgeSet)).card = (Fintype.ofFinite ↑(G_1.edgeSet)).card + (Fintype.ofFinite ↑(G_2.edgeSet)).card := by
        have nonempty_sym2 : Nonempty (Sym2 V) := by exact Nonempty.intro e_val
        rw [union_minus_intersection_eq_sum_of_sets G_1.edgeSet G_2.edgeSet second_disjoint]
      rw [third_eq]

    -- The cardinality of putEdgeInSet e_val is 1 as it contains only e_val
    have single_eq_one : (Fintype.ofFinite (putEdgeInSet e_val)).card = 1 := by
      unfold putEdgeInSet
      simp [Fintype.card_unique]

    rw [single_eq_one] at size_equality -- substitute single_eq_one in, and we are done
    exact size_equality

  -- We are now ready to complete the proof
  have edgeSetEquality : (Fintype.ofFinite G.edgeSet).card = (Fintype.ofFinite ↑G_1.verts).card + (Fintype.ofFinite ↑G_2.verts).card - 1 := by
    rw [h_G_1, h_G_2] at edgeSetEquality -- Change the goal to |E(G)| = (|(V (G1)| − 1) + (|V (G2)| − 1) + 1 using previous result s

    have G_1_succ : ∃ n : ℕ, (Fintype.ofFinite ↑G_1.verts).card = Nat.succ n := by
      rw [Nat.exists_eq_add_one] -- We see our goal is actually to show 0 < (Fintype.ofFinite ↑G_1.verts).c
      have nonempty_verts : Nonempty G_1.verts := by -- G_1.verts is notempty as we have previously show it has a members
        rw [nonempty_subtype]
        apply Exists.intro
        · rfl
      exact (Fintype.ofFinite G_1.verts).card_pos -- Nonempty implies cardinality gt_0 so we are done

    obtain ⟨n_1, G_1_succ⟩ := G_1_succ -- Obtain this cardinality and property

    have G_2_succ : ∃ n : ℕ, (Fintype.ofFinite ↑G_2.verts).card = Nat.succ n := by -- The same as for G_1.verts is performed upon G_2.verts
      rw [Nat.exists_eq_add_one]
      have nonempty_verts : Nonempty G_2.verts := by
        rw [nonempty_subtype]
        apply Exists.intro
        · rfl
      exact (Fintype.ofFinite G_2.verts).card_pos

    obtain ⟨n_2, G_2_succ⟩ := G_2_succ

    rw [G_1_succ, G_2_succ] at edgeSetEquality -- Substite these succs in to get |E(G)| = n_1.succ - 1 + (n_2.succ - 1) + 1
    simp [Nat.succ_eq_add_one] at edgeSetEquality -- Sub in value of succ and simplify: |E(G)| = n_1 + 1 - 1 + (n_2 + 1 - 1) + 1 = n_1 + n_2 + 1
    rw [add_assoc] at edgeSetEquality -- |E(G)| = n_1 + (n_2 + 1)
    rw [add_comm n_2 1] at edgeSetEquality -- |E(G)| = n_1 + (1 + n_2)
    rw [← add_assoc] at edgeSetEquality -- |E(G)| = n_1 + 1 + n_2
    rw [← Nat.succ_eq_add_one] at edgeSetEquality -- |E(G)| = (succ n_1) + n_2
    have map_to_succ_minus_one : Nat.succ n_1 + n_2 = (Nat.succ n_1 + Nat.succ n_2) - 1 := by exact rfl -- succ n_2 - 1 = n_2, so this holds
    rw [map_to_succ_minus_one] at edgeSetEquality
    rw [← G_1_succ, ← G_2_succ] at edgeSetEquality -- substite our cardinalities back in
    exact edgeSetEquality -- and we are done

  rw [← vertSetEquality] at edgeSetEquality -- substite |(V (G1)| + |V (G2)| = |V (G)| into the above
  rw [hnV] at edgeSetEquality -- And we see |E (G)| = |V (G)|, so are done
  exact edgeSetEquality

lemma edgeInCycleMeansEdgeInGraph {V : Type} [Finite V] (G : SimpleGraph V) {v : V} (p : G.Walk v v) {e : Sym2 V} (e_in_path : e ∈ p.edges)
  : e ∈ G.edgeSet := by
  exact SimpleGraph.Walk.edges_subset_edgeSet p e_in_path

lemma deletingEdgeMeansNotInEdgeSet {V : Type} [Finite V] (deletedEdges : Set (Sym2 V)) {G G' : SimpleGraph V} (h: G' = G.deleteEdges deletedEdges) {e : Sym2 V} (e_member : e ∈ deletedEdges)
: e ∉ G'.edgeSet := by
  by_contra contra_h -- suppose it is in this edgeset
  unfold SimpleGraph.deleteEdges at h
  subst h
  rw [SimpleGraph.edgeSet_sdiff] at contra_h
  rw [SimpleGraph.edgeSet_fromEdgeSet] at contra_h
  rw [SimpleGraph.edgeSet_sdiff_sdiff_isDiag] at contra_h -- This means it is the edgeset of G without the edges in deltedEdges
  rw [Set.mem_diff] at contra_h -- Which means it is in the edgeset of G and not in deletedEdges
  obtain ⟨_, fact⟩ := contra_h
  exact fact e_member -- but being in deletedEdges was an assumption, so we have a contradiction

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
    simp_all only [Set.mem_toFinset]

  have edgeFinsets_neq : G.edgeFinset ≠ G'.edgeFinset := by
    exact Ne.symm (Finset_subset_and_has_less_elems_implies_not_equal G'.edgeFinset G.edgeFinset
                   G'_edgeFinset_is_subset deletedEdge_edge edge_in_G edge_not_in_G')

  exact subset_and_neq_means_card_le G'.edgeFinset G.edgeFinset G'_edgeFinset_is_subset
        (id (Ne.symm edgeFinsets_neq))

lemma SetToFinsetToSetEqSet {V : Type} (set : Set V) [Fintype set] : set.toFinset.toSet = set := by
  exact Set.coe_toFinset set

lemma equalSetsHaveEqualCard {V : Type} [Finite V] (set1 set2 : Set (Sym2 V)) (equality : set1 = set2)
  : (Fintype.ofFinite set1).card = (Fintype.ofFinite set2).card := by
  subst equality
  simp_all only

theorem five_implies_onetwothreefour_acyclic_part1 {V : Type} [Finite V] (G : SimpleGraph V) (g_is_connected : G.Connected) (edge_vert_equality: (Fintype.ofFinite G.edgeSet).card = (Fintype.ofFinite V).card - 1) :
  (isAcyclic G) := by

  by_contra not_acyclic-- suppose that G is not acyclic, that is it has a cycle

  -- We define a set that is the set of all sets of edges in G such that if we remove the edges the graph is both still connected and also now acylcic
  let deleteableEdgeSets := { eSet : Set (Sym2 V) | (G.deleteEdges eSet).Connected ∧ (isAcyclic (G.deleteEdges eSet)) ∧ (∀ e ∈ eSet, e ∈ G.edgeSet)}
  -- there are multiple of these sets, but can just take one

  have deleteableEdgeSets_Nonempty : Nonempty deleteableEdgeSets := by
    by_contra no_set_exists
    simp_all [deleteableEdgeSets]
    sorry
    -- This is essentially a proof that each connected graph has a minimum spanning tree,
    -- which is a true statement. However, this proof is outside the scope of this project, and thus I have sorried here,

  have exists_element_in_deleteableEdgeSets : ∃ edgesToDelete : Set (Sym2 V), edgesToDelete ∈ deleteableEdgeSets := by
    exact nonempty_subtype.mp deleteableEdgeSets_Nonempty

  obtain ⟨edgesToDelete, edgesToDelete_rel⟩ := exists_element_in_deleteableEdgeSets
  let G_0 := G.deleteEdges edgesToDelete

  have G_0_subgraph : G_0.IsSubgraph G := by -- G_0 is clearly a subgraph, as we have only removed edges that were already in G
    exact SimpleGraph.deleteEdges_le edgesToDelete

  rw [SimpleGraph.isSubgraph_eq_le] at G_0_subgraph

  have G_0_connected : G_0.Connected := by -- G_0 is also clearly connected, as it is a subgraph of a connected grpah and its contrsuction did not break connectivity
    simp_all only [deleteableEdgeSets]
    simp_all only [Set.mem_setOf_eq]

  have G_0_acyclic : isAcyclic G_0 := by
    simp_all only [deleteableEdgeSets]
    simp_all only [Set.mem_setOf_eq]

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
      exact subgraphImpliesLeqEdges edgesToDelete G_edgeSet_Fintype rfl G_0_subgraph G_0_edgeSet_Fintype edgesToDelete_subset_of_G_edges nonempty_edgesToDelete
      -- this is a result of a lemma I have proved which states that if a graph is a subgraph of another graph gained by deleting at least one edge,
      -- and both their number of edges are fintypes, then the number of edges in the subgraph's edgeFinset is less than that of the parent graph

    -- POSSIBLE IMPROVEMENT, MAKE THIS RESULT (WHICH IS USED TWICE) A LEMMA
    -- We see that the edgeFinset cardinality is the same as the cardinality of the Fintype gained from casting edgeFinset to a set, then a finset, then a fintype
    have G_0_edgeFinset_card_eq_edgeSet_card : G_0.edgeFinset.card = (Fintype.ofFinite G_0.edgeFinset.toSet).card  := by
      unfold SimpleGraph.edgeFinset -- Unfold the defintion of edgeFinset in SimpleGraph.Finite
      simp [Set.toFinset_card] -- we then see these cardinalites are equal by a property of sets

    have G_0_eSet_toFinset_toSet_eq_eSet : G_0.edgeSet = G_0.edgeFinset.toSet := by -- Want to show that the edgeSet is equal to itself casted to a Finset and then coerced back to a set
      exact Eq.symm (SetToFinsetToSetEqSet G_0.edgeSet)
      -- This is the result of a lemma I have proved which states that a set on Sym2 V (for V a finite type) has this property

    -- Want to show these two cardinalities are equal to the < statement we found can be chaned to the form of the goal
    have G_0_edgeFinset_card_eq_edgeSet_card :  (Fintype.ofFinite G_0.edgeSet).card = G_0.edgeFinset.card := by
      rw [G_0_edgeFinset_card_eq_edgeSet_card] -- substitute in the equality proved with this
      exact equalSetsHaveEqualCard G_0.edgeSet G_0.edgeFinset.toSet G_0_eSet_toFinset_toSet_eq_eSet -- This is a lemma proving this result on any two finite sets that are shown two be equal

    have G_edgeFinset_card_eq_edgeSet_card : G.edgeFinset.card = (Fintype.ofFinite G.edgeFinset.toSet).card  := by -- apply exact symmetry to proof results found for G_0
      unfold SimpleGraph.edgeFinset
      simp [Set.toFinset_card]

    have G_eSet_toFinset_toSet_eq_eSet : G.edgeSet = G.edgeFinset.toSet := by
      exact Eq.symm (SetToFinsetToSetEqSet G.edgeSet)

    have G_edgeFinset_card_eq_edgeSet_card :  (Fintype.ofFinite G.edgeSet).card = G.edgeFinset.card := by
      rw [G_edgeFinset_card_eq_edgeSet_card]
      exact equalSetsHaveEqualCard G.edgeSet G.edgeFinset.toSet G_eSet_toFinset_toSet_eq_eSet

    simp_all only [Set.toFinset_card] -- Using the equality of the desired set cardinalities and the cardinality of edgeFinset.card we see we have found the desired statemnt

  have edge_vert_equality_G_0 : (Fintype.ofFinite G_0.edgeSet).card = (Fintype.ofFinite V).card - 1 := by -- We know that |E(G0)| = |V (G0)| − 1 as G0 is a tree, and thus we can apply our previous work
    have nonempty_V : Nonempty V := by -- this is requied for the usage of "onetwothreefour_implies_five_part2"
      exact g_is_connected.nonempty -- follows from connectedness
    exact onetwothreefour_implies_five G_0 G_0_is_Tree nonempty_V
    -- Applying the result from the other direction that tells us that if a graph is connected and its vertex set is Nonempty then it is

  --On the other hand, we did not delete any vertex of G, i.e. |V (G0)| = |V (G)| (This does not need to be proved in lean by nature of G & G_0's construction).
  have h1 : (Fintype.ofFinite G_0.edgeSet).card = (Fintype.ofFinite G.edgeSet).card := by --Therefore, |E(T0)| = |V (G0))| − 1 = |V (T)| − 1 = |E(T)| and hence E(T0) = E(T), i.e. no edge has been deleted from T.
    simp_all only [G_0] -- follows from the assumption edge_vert_equality

  simp_all only [lt_self_iff_false, G_0] --In other words, G is acyclic and we are done (for this part)

theorem five_implies_onetwothreefour_part2 {V : Type} [Finite V] (G : SimpleGraph V) (g_is_connected : G.Connected) (edge_vert_equality: (Fintype.ofFinite G.edgeSet).card = (Fintype.ofFinite V).card - 1) :
  (isTree G) := by
  -- only need show G is Acylcic as we are given G is connected and G being a tree requires it to be Acylic and Connected
  have G_Acyclic : isAcyclic G := by exact five_implies_onetwothreefour_acyclic_part1 G g_is_connected edge_vert_equality -- acyclic-ness is the result that part 1 proves
  have G_Acylic_and_Connected : G.Connected ∧ (isAcyclic G) := by exact ⟨g_is_connected, G_Acyclic⟩ -- This is just ∧ of two statements we have
  unfold isTree -- we see this is exactly the defintion of a tree, so are done
  exact G_Acylic_and_Connected
