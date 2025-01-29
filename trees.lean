import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Combinatorics.SimpleGraph.Walk
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic -- Don't think is needed need???? but curtrently used for interval_cases
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Fintype.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite

namespace trees

-- Definitions

def hasACycle {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ (u : V), ∃ (p : G.Walk u u), p.IsCycle
def isAcyclic {V : Type} (G : SimpleGraph V) : Prop :=
  ¬ hasACycle G
def isTree {V : Type} (G : SimpleGraph V) : Prop :=
  G.Connected ∧ isAcyclic G
def secondVertexInWalk {V : Type} (G : SimpleGraph V) {v u : V} (p : G.Walk v u) : V :=
  p.getVert 1
def putElemInSet {V : Type} (u : V) : Set V :=
  {u}
def connectedComponentToSubGraph {V : Type} [Finite V] (G : SimpleGraph V) (connComponent : Set V): G.Subgraph :=
  { verts := connComponent -- The vertex set is the set of vertices in the component
    Adj := fun (x y) => G.Adj x y ∧ (x ∈ connComponent) ∧ (y ∈ connComponent)
    -- Two vertices are adjacent if they are both in the conncected component and adjacent in G
    adj_sub := by -- As adjacency in G is a requirement for adjacency in the subgraph, this follows naturally
      intro v w a
      simp_all only
    edge_vert := by -- This also follows naturally by similar logic
      intro v w a
      simp_all only
    symm := by -- Symmetricness follows from G.Adj being symmetric
      intro v w properties
      simp_all only [and_self, and_true]
      obtain ⟨GAdj, properties⟩ := properties
      exact id (SimpleGraph.adj_symm G GAdj)
  }

-- lemmas (unproven) and definitions that use them

lemma edgeConversionG'CoeToG {V : Type} {G : SimpleGraph V} (G' : G.Subgraph) (x y : ↑G'.verts) (h : G'.coe.Adj x y) : G.Adj x y := by sorry
def subgraph_to_graph_hom {V : Type} {G : SimpleGraph V} {G' : G.Subgraph} :  G'.coe →g G where
  toFun := fun
    | .mk val property => val -- Maps to the v values of the subgraph vertex
  map_rel' := by
    exact fun {a b} a_1 => edgeConversionG'CoeToG G' a b a_1 -- Adjacency follows from another result
def Walk_map {V : Type} {G : SimpleGraph V} {G' : G.Subgraph} {x y : G'.verts} (G'_walk : G'.coe.Walk x y) : G.Walk x y :=
  SimpleGraph.Walk.map subgraph_to_graph_hom G'_walk
lemma my_card_congr {α β} (a : Fintype α) (b : Fintype β) (f : α ≃ β) : Fintype.card α = Fintype.card β := by sorry
lemma reachableByCompImpliesconnComp {V : Type} [Finite V] [Nonempty V] {G : SimpleGraph V} {G' : G.ConnectedComponent} {x : V} (h : G' = G.connectedComponentMk x) {y : V} (reachable : G.Reachable x y) : y ∈ G' := by sorry
lemma connected_component_coe_is_connected {V : Type} [Finite V] [Nonempty V] {G G_e_removed : SimpleGraph V} (x : V) {y : V} (h : s(x,y) ∈ G.edgeSet) (def_of_G_e : G_e_removed = G.deleteEdges (putElemInSet ( s(x,y) ) ) ): (connectedComponentToSubGraph G (G_e_removed.connectedComponentMk x).supp).coe.Connected := by sorry
lemma subgraph_hom_eq_implies_eq {V : Type} {G : SimpleGraph V} {G' : G.Subgraph} (x y : G'.verts) (h : subgraph_to_graph_hom x = subgraph_to_graph_hom y) : x = y := by sorry
lemma subgraph_hom_inj  {V : Type} {G : SimpleGraph V} {G' : G.Subgraph} : ∀ x y : G'.verts, subgraph_to_graph_hom x = subgraph_to_graph_hom y → x = y := by sorry
lemma type_eq_set_iff_card_the_same {V : Type} [Finite V] (set : Set V) : (∀ v : V, v ∈ set) ↔ (Fintype.ofFinite set).card = (Fintype.ofFinite V).card := by sorry
lemma subgraph_edgeSet_card_eq_coe_card {V : Type} [Finite V] {G : SimpleGraph V} (G_1 : G.Subgraph) (nonempty_edgeSet : Nonempty G_1.edgeSet) : (Fintype.ofFinite G_1.coe.edgeSet).card = (Fintype.ofFinite G_1.edgeSet).card := by sorry
lemma any_subgraph_of_an_acyclic_graph_is_acyclic {V : Type} [Finite V] (G : SimpleGraph V) (H : G.Subgraph) (h : isAcyclic G) : isAcyclic H.coe := by sorry

-- Theorems (from Daniel's part)
theorem my_card_congr' {α β} (x : Fintype α) (y : Fintype β) (h : α = β) : x.card = y.card := by sorry
theorem my_set_fintype_card_eq_univ_iff {α} (V : Fintype α) (s : Set α) [Fintype s] : Fintype.card s = Fintype.card α ↔ s = Set.univ := by sorry
theorem onetwothreefour_implies_five {V : Type} [Finite V] (G : SimpleGraph V) (G_is_tree : isTree G) (nonempty: Nonempty V): ((Fintype.ofFinite G.edgeSet).card = (Fintype.ofFinite V).card - 1) := by sorry
theorem five_implies_onetwothreefour_acyclic_part {V : Type} [Finite V] (G : SimpleGraph V) (g_is_connected : G.Connected) (edge_vert_equality: (Fintype.ofFinite G.edgeSet).card = (Fintype.ofFinite V).card - 1) : (isAcyclic G) := by sorry
theorem five_implies_onetwothreefour {V : Type} [Finite V] (G : SimpleGraph V) (g_is_connected : G.Connected) (edge_vert_equality: (Fintype.ofFinite G.edgeSet).card = (Fintype.ofFinite V).card - 1) : (isTree G) := by sorry

---------------------------------------------------------------------------------------------

def hasLeaf {V : Type} [Finite V] (G : SimpleGraph V) : Prop := ∃ (u : V), ((Fintype.ofFinite (G.neighborSet u)).card = 1)
def type_to_set (V : Type) : Set V := by exact Set.univ
def subgraph_without_vertex_set {V : Type} [Finite V] (G : SimpleGraph V) (v1 : (Set V)) : G.Subgraph :=
  { verts := type_to_set V \ v1 -- The vertex set is the set of vertices in the graph without v1
    Adj := fun (x y) => G.Adj x y ∧ (x ∈ type_to_set V \ v1) ∧ (y ∈ type_to_set V \ v1)
    -- Two vertices are adjacent if they are both in the set V \ v1 and adjacent in G
    adj_sub := by -- As adjacency in G is a requirement for adjacency in the subgraph, this follows naturally
      intro v w a
      simp_all only
    edge_vert := by -- This also follows naturally by similar logic
      intro v w a
      simp_all
    symm := by -- Symmetricness follows from G.Adj being symmetric
      intro v w properties
      simp_all only [and_self, and_true]
      obtain ⟨GAdj, _⟩ := properties
      exact id (SimpleGraph.adj_symm G GAdj)
  }
lemma acyclic_graphs_have_a_leaf {V : Type} [Finite V] (G : SimpleGraph V) (nonempty : Nonempty V) (g_is_acyclic : isAcyclic G) : hasLeaf G := by sorry
lemma onetwothreefourfive_implies_six {V : Type} [Finite V] (G : SimpleGraph V) (G_is_tree : isTree G) (nonempty: Nonempty V) : (isAcyclic G) ∧ ((Fintype.ofFinite G.edgeSet).card = (Fintype.ofFinite V).card - 1) := by sorry

---------------------------------------------------------------------------------------------

lemma six_implies_onetwothreefourfive_step_one {V : Type} [Finite V] (G : SimpleGraph V) (nonempty : Nonempty V) (g_is_acyclic : isAcyclic G) (CardinalityCondition : (Fintype.ofFinite G.edgeSet).card = (Fintype.ofFinite V).card - 1): G.Connected := by
  -- We induct on |V| - 1 = n, so we generalize the statement for this, and then induct on it
  generalize hnV : (Fintype.ofFinite V).card - 1 = nV
  induction nV using Nat.case_strong_induction_on generalizing V with
  | hz =>
    -- We start with the case that |V| - 1 = 0, first by attempting to prove |V| = 1
    -- Create the machinery to be able to do arithmetic with -1 in the naturals
    have arithmetic_with_minus_one {v : ℕ} (a : v - 1 = 0) (n: v ≠ 0) : v = 1 := by
      -- Use the fact that v is a non-zero natural number to justify the arithmetic
      have one_greaterthan_0 : 1 > 0 := by
        exact Nat.one_pos
      have v_greaterthan_zero : v > 0 := by
        exact Nat.zero_lt_of_ne_zero n
      exact Eq.symm (Nat.sub_one_cancel one_greaterthan_0 v_greaterthan_zero (id (Eq.symm a)))
    -- Use the fact that in our case, v is indeed nonzero
    have nonzero : (Fintype.ofFinite V).card ≠ 0 := by
      simp_all only [ne_eq, Fintype.card_ne_zero, not_false_eq_true, Nat.sub_self, one_ne_zero, Nat.zero_sub, le_refl,
        tsub_eq_zero_of_le, zero_le]
    -- Therefore conclude that |V| = 1
    have card_V_eq_1: (Fintype.ofFinite V).card = 1 := by
      exact arithmetic_with_minus_one hnV nonzero

    -- Use the fact that cardinality = 1 → the vertex is reachable from itself, implies preconnected and nonempty → connected
    rw [(Fintype.ofFinite V).card_eq_one_iff] at card_V_eq_1
    -- Reachability:
    have all_reachable : ∀ z w : V, G.Reachable z w := by
      intro z w
      simp_all only [ne_eq, not_false_eq_true, Nat.sub_self, one_ne_zero, Nat.zero_sub, le_refl, tsub_eq_zero_of_le,
        zero_le]
      obtain ⟨w_1, h⟩ := card_V_eq_1
      simp_all only [Nat.zero_sub, Nat.sub_self, one_ne_zero, not_false_eq_true, zero_le, tsub_eq_zero_of_le, le_refl]
      rfl
    -- Preconnected Using Reachability
    have preconnected : G.Preconnected := by
      exact all_reachable
    -- Nonempty by the fact that |V| ≠ 0
    have nonempty : Nonempty V := by
      exact nonempty_of_exists card_V_eq_1
    -- Connected by definition
    exact SimpleGraph.Connected.mk all_reachable

  |hi y hy =>
    -- Now we consider the case that |V| - 1 = y + 1, assuming that connectivity holds for all acyclic graphs which suffice the Cardinality
    -- Condition on |V| = y + 1 vertices (strictly we are assuming it for the Prop : |V| - 1 = y, which is equivalent as we will show)
    -- We start the same way as last time, proving that |V| - 1 = y + 1 ↔ |V| = y + 2
    have arithmetic_with_minus_one {v : ℕ} {k : ℕ} (a : v - 1 = k) (n: v ≠ 0) : v = k + 1 := by
      -- Using the same fact that v ≥ 1
      have one_greaterthan_0 : 1 > 0 := by
        exact Nat.one_pos
      have v_greaterthan_zero : v > 0 := by
        exact Nat.zero_lt_of_ne_zero n
      exact (Nat.sub_eq_iff_eq_add v_greaterthan_zero).mp a
    -- Using the same fact that V is nonzero since |V| ≠ 0
    have nonzero : (Fintype.ofFinite V).card ≠ 0 := by
      simp_all only [ne_eq, Fintype.card_ne_zero, not_false_eq_true, Nat.sub_self, one_ne_zero, Nat.zero_sub, le_refl,
        tsub_eq_zero_of_le, zero_le]
    -- Therefore conclude that |V| = y + 2
    have card_V_eq_y_plus_2: (Fintype.ofFinite V).card = y + 2 := by
      exact arithmetic_with_minus_one hnV nonzero

    -- We know that G has a leaf from a previous lemma, as a nontrivial acyclic graph
    have G_has_a_leaf : hasLeaf G := by
      exact acyclic_graphs_have_a_leaf G nonempty g_is_acyclic -- add nontriviality (edgeset > 0)
    -- Get the leaf in question by unfolding hasLeaf
    unfold hasLeaf at G_has_a_leaf
    obtain ⟨leaf, leaf_prop⟩ := G_has_a_leaf
    rw [(Fintype.ofFinite ↑(G.neighborSet leaf)).card_eq_one_iff] at leaf_prop
    obtain ⟨x,x_is_unique⟩ := leaf_prop

    let G' := subgraph_without_vertex_set G {leaf}
    -- let H := G'.deleteVerts {leaf}
    -- The graph of the leaf is just the leaf vertex, which is G - G'
    let leaf_graph := ⊤ \ G'

    -- To prove the Cardinality Condition on G', we first show that G' has y + 1 vertices
    have G'_has_yplus1_vertices : ((Fintype.ofFinite (G'.verts)).card) = y+1 := by
      have G'_explicit : G'.verts = type_to_set V \ {leaf} := by
        exact rfl
      -- Cardinalities of V(G') and V(G \ leaf) are equivalent
      have equal_card : ((Fintype.ofFinite (G'.verts)).card) = ((Fintype.ofFinite ↑(type_to_set V \ {leaf})).card) := by
        exact rfl

      rw [equal_card]
      -- The leaf is trivially in the Vertex set
      have leaf_in_V : leaf ∈ type_to_set V := by
        exact trivial
      
      have V_without_leaf_card_eq_minus_one : (Fintype.ofFinite ↑(type_to_set V \ {leaf})).card = (Fintype.ofFinite ↑(type_to_set V)).card - 1 := by
        simp [← Set.toFinset_card]

        have decidableEq : DecidableEq V:= by exact Classical.typeDecidableEq V

        have my_Fintype : Fintype ↑(type_to_set V) := by exact Fintype.ofFinite ↑(type_to_set V)

        rw [Set.toFinset_diff, Finset.card_sdiff]
        rw [Set.toFinset_singleton, Finset.card_singleton]

        have card_eq : my_Fintype.card = (Fintype.ofFinite ↑(type_to_set V)).card := by
          exact my_card_congr' my_Fintype (Fintype.ofFinite ↑(type_to_set V)) rfl

        simp [Set.toFinset_card]
        exact congrFun (congrArg HSub.hSub card_eq) 1
        rw [Set.toFinset_singleton, Set.subset_toFinset, Finset.coe_singleton, Set.singleton_subset_iff]
        exact leaf_in_V
      rw [V_without_leaf_card_eq_minus_one]
      have all_in_type_to_set : ∀ v : V, v ∈ (type_to_set V) := by
        exact fun v ↦ leaf_in_V

      rw [ (type_eq_set_iff_card_the_same (type_to_set V))] at all_in_type_to_set
      rw [all_in_type_to_set]
      exact hnV

    have G'_has_y_edges : ((Fintype.ofFinite ↑(G'.edgeSet)).card) = y := by

      have G_has_yplus1_edges : ((Fintype.ofFinite (G.edgeSet)).card) = y+1 := by

        have G_has_nplus2_vertices : (Fintype.ofFinite V).card = y+2 := by
          exact card_V_eq_y_plus_2

        rw [G_has_nplus2_vertices] at CardinalityCondition
        exact CardinalityCondition

      have G'_has_one_less_edge_than_G : ((Fintype.ofFinite ↑(G'.edgeSet)).card) = ((Fintype.ofFinite (G.edgeSet)).card) - 1 := by


        have x_in_n_set : x.1 ∈ (G.neighborSet leaf) := by
          exact x.2

        rw [SimpleGraph.mem_neighborSet, ←SimpleGraph.mem_edgeSet] at x_in_n_set

        have adj_iff : ∀ a b, G'.Adj a b ↔ (G.deleteEdges (G.incidenceSet leaf)).Adj a b := by
          intro a b
          apply Iff.intro

          · have adj_def : G'.Adj a b → G.Adj a b ∧ (a ∈ (type_to_set V \ {leaf})) ∧ (b ∈ (type_to_set V \ {leaf})) := by
              exact fun a ↦ a
            intro G'_adj
            apply adj_def at G'_adj

            have edge_in_edgeset_without_leaf : s(a, b) ∈ G.edgeSet \ (G.incidenceSet leaf) := by 
              let edge := s(a,b)
              -- by contra
              by_contra contradiction
              have fsae: G.incidenceSet leaf ⊆ G.edgeSet := by
                exact SimpleGraph.incidenceSet_subset G leaf

              have edge_in_incidentset_leaf : edge ∈ (G.incidenceSet leaf) := by
                refine (SimpleGraph.mk'_mem_incidenceSet_iff G).mpr ?_

                apply And.intro
                · exact G'_adj.1
                · rw [←SimpleGraph.edgeSet_deleteEdges] at contradiction
                  rw [SimpleGraph.mem_edgeSet] at contradiction
                  simp at contradiction
                  rw [SimpleGraph.mk'_mem_incidenceSet_iff] at contradiction
                  obtain ⟨r,G'_adj⟩ := G'_adj
                  apply contradiction at r
                  exact r.2

              -- unfold SimpleGraph.incidenceSet at edge_in_incidentset_leaf
              have a_in_V_minus_leaf : a ∈ type_to_set V \ {leaf} := by
                exact G'_adj.2.1
              have leaf_neq_a : leaf ≠ a := by
                have a_neq_leaf : a ≠ leaf := by
                  exact Set.mem_of_mem_inter_right a_in_V_minus_leaf
                exact a_neq_leaf.symm
              have b_in_V_minus_leaf : b ∈ type_to_set V \ {leaf} := by
                exact G'_adj.2.2
              have leaf_neq_b : leaf ≠ b := by
                have b_neq_leaf : b ≠ leaf := by
                  exact Set.mem_of_mem_inter_right b_in_V_minus_leaf
                exact b_neq_leaf.symm
              have a_or_b_eq_leaf : (leaf = a) ∨ (leaf = b) := by
                rw [←SimpleGraph.edgeSet_deleteEdges] at contradiction
                rw [SimpleGraph.mem_edgeSet] at contradiction
                simp at contradiction
                rw [SimpleGraph.mk'_mem_incidenceSet_iff] at contradiction
                obtain ⟨r,G'_adj⟩ := G'_adj
                apply contradiction at r
                obtain ⟨ r_left , r_right ⟩ := r
                exact r_right

              -- then one of a or b must be leaf
              rw [←SimpleGraph.edgeSet_deleteEdges] at contradiction
              rw [SimpleGraph.mem_edgeSet] at contradiction
              simp at contradiction
              rw [SimpleGraph.mk'_mem_incidenceSet_iff] at contradiction
              obtain ⟨r,G'_adj⟩ := G'_adj
              apply contradiction at r

              have neither_a_nor_b_eq_leaf : ¬ (leaf = a ∨ leaf = b) := by
                exact not_or_intro leaf_neq_a leaf_neq_b
              exact neither_a_nor_b_eq_leaf a_or_b_eq_leaf

              -- contradicts G'_adj
            rw [← SimpleGraph.mem_edgeSet]
            rw [SimpleGraph.edgeSet_deleteEdges]
            exact edge_in_edgeset_without_leaf

          · intro deleteEdges_Adj
            rw [SimpleGraph.deleteEdges_adj] at deleteEdges_Adj

            have adj_def : G'.Adj a b → G.Adj a b ∧ (a ∈ (type_to_set V \ {leaf})) ∧ (b ∈ (type_to_set V \ {leaf})) := by
              exact fun a ↦ a

            have asjkjkds : G.Adj a b ∧ (a ∈ (type_to_set V \ {leaf})) ∧ (b ∈ (type_to_set V \ {leaf})) := by
              apply And.intro
              · exact deleteEdges_Adj.1
              · apply And.intro
                · by_contra a_not_in_G' -- Suppose a ∉ (type_to_set V \ {leaf})

                  simp at a_not_in_G'
                  have a_is_leaf : a = leaf := by
                    exact a_not_in_G' trivial

                  have edge_eq_leaf_edge : s(a,b) = s(leaf,b) :=by
                    exact congrArg Sym2.mk (congrFun (congrArg Prod.mk (a_not_in_G' trivial)) b)

                  have leaf_edge_in_incidentset : s(leaf,b) ∈ G.incidenceSet leaf := by
                    rw[SimpleGraph.mk'_mem_incidenceSet_iff]
                    simp
                    have adj_leaf : G.Adj a b := by
                      exact deleteEdges_Adj.1
                    rw [a_is_leaf] at adj_leaf
                    exact adj_leaf

                  have edge_in_incidentset : s(a,b) ∈ G.incidenceSet leaf := by
                    exact Set.mem_of_eq_of_mem edge_eq_leaf_edge leaf_edge_in_incidentset

                  exact deleteEdges_Adj.2 edge_in_incidentset

                · by_contra b_not_in_G' -- Suppose b ∉ (type_to_set V \ {leaf})

                  simp at b_not_in_G'
                  have b_is_leaf : b = leaf := by
                    exact b_not_in_G' trivial

                  have edge_eq_leaf_edge : s(a,b) = s(a,leaf) :=by
                    exact congrArg Sym2.mk (congrArg (Prod.mk a) (b_not_in_G' trivial))

                  have leaf_edge_in_incidentset : s(a,leaf) ∈ G.incidenceSet leaf := by
                    rw[SimpleGraph.mk'_mem_incidenceSet_iff]
                    simp
                    have adj_leaf : G.Adj a b := by
                      exact deleteEdges_Adj.1
                    rw [b_is_leaf] at adj_leaf
                    exact adj_leaf

                  have edge_in_incidentset : s(a,b) ∈ G.incidenceSet leaf := by
                    exact Set.mem_of_eq_of_mem edge_eq_leaf_edge leaf_edge_in_incidentset

                  exact deleteEdges_Adj.2 edge_in_incidentset

            exact adj_def asjkjkds

        
        have G'_explicit: G'.edgeSet = G.edgeSet \ G.incidenceSet leaf := by
          
          sorry  
        have equal_card : (Fintype.ofFinite G'.edgeSet).card = (Fintype.ofFinite ↑(G.edgeSet \ G.incidenceSet leaf)).card := by
          exact my_card_congr' (Fintype.ofFinite ↑G'.edgeSet) (Fintype.ofFinite ↑(G.edgeSet \ G.incidenceSet leaf)) (congrArg Set.Elem G'_explicit)
        
        rw[equal_card]

        simp [← Set.toFinset_card]
      -- have V_without_leaf_card_eq_minus_one : (Fintype.ofFinite ↑(type_to_set V \ {leaf})).card = (Fintype.ofFinite ↑(type_to_set V)).card - 1 := by

        have decidableEq : DecidableEq ↑G.edgeSet:= by exact Classical.typeDecidableEq ↑G.edgeSet
        have decidableEq2 : DecidableEq ↑(G.edgeSet \ G.incidenceSet leaf):= by exact Classical.typeDecidableEq ↑(G.edgeSet \ G.incidenceSet leaf)
        have decidableEq3 : DecidableEq ↑(G.incidenceSet leaf):= by exact Classical.typeDecidableEq ↑(G.incidenceSet leaf)

        have my_Fintype : Fintype ↑G.edgeSet := by exact Fintype.ofFinite ↑G.edgeSet
        have my_Fintype2 : Fintype ↑(G.edgeSet \ G.incidenceSet leaf) := by exact Fintype.ofFinite ↑(G.edgeSet \ G.incidenceSet leaf)
        have my_Fintype3 : Fintype ↑(G.incidenceSet leaf) := by exact Fintype.ofFinite ↑(G.incidenceSet leaf)



        rw [Set.toFinset_diff, Finset.card_sdiff] 
        rw [Set.toFinset_singleton, Finset.card_singleton]

        -- have card_eq : my_Fintype.card = (Fintype.ofFinite ↑(type_to_set V)).card := by
        --   exact my_card_congr' my_Fintype (Fintype.ofFinite ↑(type_to_set V)) rfl

        -- simp [Set.toFinset_card]
        -- exact congrFun (congrArg HSub.hSub card_eq) 1
        -- rw [Set.toFinset_singleton, Set.subset_toFinset, Finset.coe_singleton, Set.singleton_subset_iff]
        -- exact leaf_in_V

        sorry



      rw [G_has_yplus1_edges] at G'_has_one_less_edge_than_G
      simp at G'_has_one_less_edge_than_G
      exact G'_has_one_less_edge_than_G

    -- Now we want to show G is acyclic and this follows exactly from a previous lemma
    have G'_is_acyclic : isAcyclic G'.coe := by
      exact any_subgraph_of_an_acyclic_graph_is_acyclic G G' g_is_acyclic

    have CardinalityConditionG' : (Fintype.ofFinite G'.coe.edgeSet).card = ((Fintype.ofFinite (G'.verts)).card) - 1 := by

      have G'coe_eq_G' : (Fintype.ofFinite G'.coe.edgeSet).card = (Fintype.ofFinite G'.edgeSet).card := by
        by_cases (y = 0)
        · rename_i y_eq_zero
          rw[y_eq_zero] at G'_has_y_edges
          have G'_edgeset_empty : (Fintype.ofFinite G'.edgeSet).card = 0 := by
            exact G'_has_y_edges


          -- sub y= 0 in at G'_has_y_edges
          -- have that the edgeset of G' is empty
          -- in turn this means coe must be empty
          sorry
        · have nonempty_edgeSet : Nonempty G'.edgeSet := by
            -- have cardinality nonzero
            -- then it follow from results
            -- have nonempty : Nonempty G_1.coe.edgeSet := by -- First we see G_1.coe.edgeSet is nonempty

            --   have card_not_zero : (Fintype.ofFinite G_1.coe.edgeSet).card ≠ 0 := by -- Its cardinality is non-zero by consequence of previous assumptions
            --     simp_all only [nonempty_subtype, ne_eq, AddLeftCancelMonoid.add_eq_zero, one_ne_zero,
            --       and_false, not_false_eq_true]

            --   by_contra is_empty -- Suppose it is empty

            --   have card_zero : (Fintype.ofFinite G_1.coe.edgeSet).card = 0 := by -- Then its cardianlity must be zero
            --     simp_all only [nonempty_subtype, not_false_eq_true, not_exists, isEmpty_subtype,
            --                   implies_true, Fintype.card_eq_zero]
            sorry
          exact subgraph_edgeSet_card_eq_coe_card G' nonempty_edgeSet

      rw [G'coe_eq_G', G'_has_y_edges, G'_has_yplus1_vertices]
      simp

    -- have CardinalityConditionG' : (Fintype.ofFinite G'.edgeSet).card = ((Fintype.ofFinite (G'.verts)).card) - 1 := by
    --   rw [G'_has_y_edges, G'_has_yplus1_vertices]
    --   simp

    have hyp : y ≤ y := by
      exact Nat.le_refl y

    have nonemptyG' : Nonempty ↑(G'.verts) := by
      have G'_has_gte_one_vertex : 0 < (Fintype.ofFinite ↑(G'.verts)).card := by
        have y_gte_zero : y ≥ 0 := by
          exact Nat.zero_le y
        rw [G'_has_yplus1_vertices]
        simp

      -- rw [← Fintype.card_pos] Should just be this, idk why it isnt :(
      simp


      sorry -- probs use nonzero

    have inductive_check : ((Fintype.ofFinite (G'.verts)).card) - 1 = y := by
      rw [G'_has_yplus1_vertices]
      simp

    have G'_connected : G'.coe.Connected := by
      exact hy y hyp G'.coe nonemptyG' G'_is_acyclic CardinalityConditionG' inductive_check

    have G_preconnected : G.Preconnected := by
      unfold SimpleGraph.Preconnected

      have G'_coe_precon : G'.coe.Preconnected := by
        exact G'_connected.1
      unfold SimpleGraph.Preconnected at G'_coe_precon

      have fjajld : ∀ a b : G'.verts, G.Reachable ↑a ↑b := by
        intro a b
        let reachable_in_coe := G'_coe_precon a b
        apply SimpleGraph.Reachable.map subgraph_to_graph_hom at reachable_in_coe

        have hshk : subgraph_to_graph_hom a = ↑a := by
          exact rfl

        have hsasddsahk : subgraph_to_graph_hom b = ↑b := by
          exact rfl
        rw [hshk,hsasddsahk] at reachable_in_coe
        exact reachable_in_coe

      have adkffe : ∀ a : V, G.Reachable a leaf := by

        have asdfos : G.Reachable leaf x.1 := by

          have x_in_n_set : x.1 ∈ (G.neighborSet leaf) := by
            exact x.2

          rw [SimpleGraph.mem_neighborSet, ←SimpleGraph.mem_edgeSet] at x_in_n_set
          exact SimpleGraph.Adj.reachable x_in_n_set
        have aksdfh : ∀ a : ↑G'.verts, G.Reachable x.1 a := by
          have heofi : x.1 ∈ ↑G'.verts := by
            sorry
          sorry
        sorry
      -- have everything is reaable from leaf as well, because reachable to x
      -- so then everything reachable
      sorry

    exact SimpleGraph.Connected.mk G_preconnected



    -- rw [CardinalityCondition] at G'_has_y_edges
    -- sorry
  -- induct on number of vertices
  -- n=0 trivially connected
  -- n = k assumed
  -- n = k + 1, G is acyclic and so has a vertex of degree 1 (leaf)
  -- delete the leaf and the edge to get G'. G' is a graph on n vertices with n - 1 edges
  -- inductive hypothesis concludes


  -- Assuming the opposite, that G is disconnected, it has connected components G_1, ..., G_k

  -- induct on the number of connected components
  -- 1 connected component is trivially connected (contradiction at not_connected)
  -- n+1 connected components => n connected components have V-V' vertices and 1 component has V' vertices
  -- by_contra (assume

  -- G is Acyclic so all G_i components are connected and acyclic => they are trees
  -- so |G_i| = |V(G_i)| - 1
  -- so ∑|G_i| = ∑(|V(G_i)| - 1) = (∑|V(G_i)|) - k = |V(G_1 ∪ ... ∪ G_k)| - 1 since G_1, ..., G_k are disjoint
  -- so ∑|G_i| = |V(G)| - 1 since G_1 ∪ ... ∪ G_k = G
  -- sorry


lemma six_implies_onetwothreefourfive_step_two {V : Type} [Finite V] (G : SimpleGraph V) (nonempty : Nonempty V) (g_is_acyclic : isAcyclic G) (CardinalityCondition : (Fintype.ofFinite G.edgeSet).card = (Fintype.ofFinite V).card - 1): isTree G := by
  have g_is_connected : G.Connected := by
    exact six_implies_onetwothreefourfive_step_one G nonempty g_is_acyclic CardinalityCondition
  unfold isTree
  apply And.intro
  · case left =>
      exact g_is_connected
  · case right =>
      exact g_is_acyclic

lemma onetwothreefourfive_equiv_six {V : Type} [Finite V] (G : SimpleGraph V) (FinEdgeSet : Finset G.edgeSet) (nonempty: Nonempty V): (isAcyclic G ∧ (Fintype.ofFinite G.edgeSet).card = (Fintype.ofFinite V).card - 1) = isTree G := by
  unfold isTree
  simp_all only [eq_iff_iff]
  apply Iff.intro
  · intro a
    simp_all only [and_true]
    obtain ⟨g_is_acyclic, CardinalityCondition⟩ := a
    exact
      six_implies_onetwothreefourfive_step_one G nonempty g_is_acyclic
        CardinalityCondition
  · intro a
    simp_all only [true_and]
    obtain ⟨g_is_connected, g_is_acyclic⟩ := a
    have G_is_tree: isTree G := by
      unfold isTree
      simp_all
    have forward : isAcyclic G ∧ (Fintype.ofFinite G.edgeSet).card = (Fintype.ofFinite V).card - 1 := by
      exact onetwothreefourfive_implies_six G G_is_tree nonempty
    simp_all
