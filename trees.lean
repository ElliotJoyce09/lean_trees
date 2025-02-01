import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Combinatorics.SimpleGraph.Walk
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Basic

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
      obtain ⟨GAdj, _⟩ := properties
      exact id (SimpleGraph.adj_symm G GAdj)
  }

-- lemmas (unproven) and definitions that use them

lemma edgeConversionG'CoeToG {V : Type} {G : SimpleGraph V} (G' : G.Subgraph) (x y : ↑G'.verts) (h : G'.coe.Adj x y) : G.Adj x y := by sorry
def subgraph_to_graph_hom {V : Type} {G : SimpleGraph V} {G' : G.Subgraph} :  G'.coe →g G where
  toFun := fun
    | .mk val _ => val -- Maps to the v values of the subgraph vertex
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

-- Theorems (from Daniel's part)
theorem my_card_congr' {α β} (x : Fintype α) (y : Fintype β) (h : α = β) : x.card = y.card := by sorry
theorem my_set_fintype_card_eq_univ_iff {α} (V : Fintype α) (s : Set α) [Fintype s] : Fintype.card s = Fintype.card α ↔ s = Set.univ := by sorry
theorem onetwothreefour_implies_five {V : Type} [Finite V] (G : SimpleGraph V) (G_is_tree : isTree G) (nonempty: Nonempty V): ((Fintype.ofFinite G.edgeSet).card = (Fintype.ofFinite V).card - 1) := by sorry
theorem five_implies_onetwothreefour_acyclic_part {V : Type} [Finite V] (G : SimpleGraph V) (g_is_connected : G.Connected) (edge_vert_equality: (Fintype.ofFinite G.edgeSet).card = (Fintype.ofFinite V).card - 1) : (isAcyclic G) := by sorry
theorem five_implies_onetwothreefour {V : Type} [Finite V] (G : SimpleGraph V) (g_is_connected : G.Connected) (edge_vert_equality: (Fintype.ofFinite G.edgeSet).card = (Fintype.ofFinite V).card - 1) : (isTree G) := by sorry

---------------------------------------------------------------------------------------------

-- Start of work done by Krishna

/-- This section has the various definitions that will be needed for the proof of (1,2,3,4,5) ↔ (6)-/

-- Definition of a leaf, as a vertex with a neighbor set of cardinality 1. Equivalently, a leaf can be defined as a vertex with degree 1
def hasLeaf {V : Type} [Finite V] (G : SimpleGraph V) : Prop := ∃ (u : V), ((Fintype.ofFinite (G.neighborSet u)).card = 1)

-- We will be converting from vertices of type V to verties in the set V when we talk about neighbor sets and edge sets, etc. so we need a definition which sends V : Type to Set V
def type_to_set (V : Type) : Set V := by exact Set.univ

-- In our induction, we will be considering a graph on n-1 vertices, so we need to have a notion of vertex deletion
-- Afterthought: This can also be acheived with induced subgraphs, but the method presented is equally valid
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

---------------------------------------------------------------------------------------------

-- Note: for the last part we will be assuming the following lemma to be true without proper proof, since it is out of the scope of this project
-- because it involves set theory. We will use the fact that a nonempty nontrivial acyclic graph has a leaf (a vertex of degree 1)
-- This is out of the scope of this project but is true since if such an acyclic graph didn't have a leaf, then all its vertices have degree either 0 or ≥ 2.
-- but this means that a cycle is created or the max path can be extended. A possible direction for the proof is given below:
lemma acyclic_graphs_have_a_leaf {V : Type} [Finite V] (G : SimpleGraph V) (nonempty : Nonempty V) (g_is_acyclic : isAcyclic G)
                                  (nontrivial : (Fintype.ofFinite G.edgeSet).card > 0 ) : hasLeaf G := by

  -- In order to prove this one would need to unfold all the definitions first
  unfold isAcyclic at g_is_acyclic
  unfold hasACycle at g_is_acyclic
  unfold hasLeaf

  -- Assume for contradiction that the graph has no vertex with neighbor set of degree 1
  by_contra exists_contradiction
  simp [not_exists] at exists_contradiction

  -- Every graph has a maximal path, call it the path from x to y
  have exists_max_path : ∃ x y : V, ∃ p : (G.Path x y), ∀ z w, ∀ q : (G.Path z w), q.1.length ≤ p.1.length := by

    -- Assume there is no maximal path
    by_contra no_max_path
    simp [not_exists] at no_max_path

    -- Consider the cases that |V| = 1 and |V| ≠ 1
    by_cases (Fintype.ofFinite V).card = 1

      -- First consider the case that |V| = 1
    · rename_i eq_one

      -- If there is only 1 vertex then clearly the graph has no edges
      have G_has_no_edges: (Fintype.ofFinite G.edgeSet).card = 0:= by
        sorry -- If there was an edge, then it would need a second vertex or create a loop on the 1 vertex, both of which aren't allowed

      -- This is a contradiction to nontriviality
      rw [G_has_no_edges] at nontrivial
      exact Nat.not_succ_le_zero 0 nontrivial

    -- Now consider the case that V ≠ 1
    · rename_i neq_one

      by_cases ((Fintype.ofFinite V).card = 0)
        -- V is clearly nonempty by assumption, so |V| = 0 is a contradiction
      · rename_i V_has_zero_card

        rw [← (Fintype.ofFinite V).card_pos_iff] at nonempty
        let h := ((Fintype.ofFinite V).card)
        have h_eq_0 : h = 0:= by
          exact V_has_zero_card
        have h_neq_zero : ¬ h = 0 := by
          exact Nat.not_eq_zero_of_lt nonempty
        exact h_neq_zero V_has_zero_card

        -- So assume V is nonempty
      · rename_i V_has_nonzero_card

        -- This part of the proof requires Zorn's lemma which is ultimately out of the scope of this formalization
        -- The proof would show the existence of paths, in a chain where each path is a subset of the next path in the chain
        -- By Zorn's lemma, there exists a maximal path, which is  acontradiction to our assumption that no such path exists
        sorry

  -- get v1 and v2 as the end points of a maximal path
  obtain ⟨v1, exists_max_path⟩ := exists_max_path
  obtain ⟨v2, exists_max_path⟩ := exists_max_path

  -- get the max_path from the propositions
  obtain ⟨max_path, max_path_props⟩ := exists_max_path

  -- now v1 has degree > 1 so it must be adjacent to something
  -- v1 cannot be adjacent to v2 (cycle created)
  -- v1 cannot be adjacent to any vertex in the path from v1 to 2 (cycle created)
  -- v1 cannot be adjacent to any vertex not in the path from v1 to v2 as this would create a larger path, contradicting maximality
  sorry

---------------------------------------------------------------------------------------------

/-- We will need to use the fact that a subgraph of an acyclic graph is acyclic -/
lemma any_subgraph_of_an_acyclic_graph_is_acyclic {V : Type} [Finite V] (G : SimpleGraph V) (H : G.Subgraph) (h : isAcyclic G) : isAcyclic H.coe := by

  -- First we unfold the definitons of acyclic and cyclic
  unfold isAcyclic
  unfold isAcyclic at h
  unfold hasACycle
  unfold hasACycle at h

  -- The we assume for contradiction that there is a cycle p in the subgraph
  by_contra p_is_cycle

  -- if p is a cycle in the subgraph, it is also a cycle in the parent graph
  have p_is_a_cycle_in_G : ∃ (u : V) (p : G.Walk u u), p.IsCycle := by

    -- obtain u, the vertex which the cycle begins and terminates at in H, and p, the cycle itself as a walk in H.coe
    obtain ⟨u, p⟩ := p_is_cycle

    -- Also split p intothe walk and the proprety that such a walk is a cycle
    obtain ⟨p, p_is_cycle⟩ := p

    -- As we can map from the coe to the parent graph we can map this cycle to one in G
    let G_walk := Walk_map p

    -- This is also a cycles as we have shown this map is injective
    have G_walk_is_Cycle : G_walk.IsCycle := by
      rw [← SimpleGraph.Walk.map_isCycle_iff_of_injective subgraph_hom_inj] at p_is_cycle
      exact p_is_cycle

    -- So now p is  acycle in G
    simp_all only [not_exists]

  -- Thus we have a cycle in an acyclic graph, which is a contradiction
  exact h p_is_a_cycle_in_G

/-- The First part of the proof of (6) → (1,2,3,4,5). It a proof that an acyclic graph with one less edge than vertices is Connected-/
lemma six_implies_onetwothreefourfive_step_one {V : Type} [Finite V] (G : SimpleGraph V) (nonempty : Nonempty V) (g_is_acyclic : isAcyclic G)
                                  (CardinalityCondition : (Fintype.ofFinite G.edgeSet).card = (Fintype.ofFinite V).card - 1): G.Connected := by

  -- We induct on |V| - 1 = n, so we generalize the statement for this, and then induct on it
  -- Note that we induct on |V| - 1 so that our base case is a nonempty case as well.
  -- Trivially an empty graph is both connected and disconnected since every vertex and no vertex can be reached
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
      -- Get any z and w of type V from the statement
      intro z w
      -- Use simp to simplify the cardinality condition,
      simp_all only [ne_eq, not_false_eq_true, Nat.sub_self, one_ne_zero, Nat.zero_sub, le_refl, tsub_eq_zero_of_le,
        zero_le]
      -- From card_V_eq_1 we can retreive the vertex and the property that it is the only vertex
      obtain ⟨w_1, h⟩ := card_V_eq_1
      -- Since we have only 1 unique vertex, we can simplify z and w to being the same vertex
      simp_all only [Nat.zero_sub, Nat.sub_self, one_ne_zero, not_false_eq_true, zero_le, tsub_eq_zero_of_le, le_refl]
      -- Trivially, w_1 is reachable from w_1
      rfl

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

    -- To use the fact that G has a leaf, we need that G is nontrivial as well (ie: it has a nonempty edgeset)
    -- We start by showing that |E| = y + 1, Using the cardinality Condition
    have card_E_eq_y_plus_1: (Fintype.ofFinite G.edgeSet).card = y + 1 := by
      rw [card_V_eq_y_plus_2] at CardinalityCondition
      simp at CardinalityCondition
      exact CardinalityCondition

    -- Now we can use the fact that any natural number plus 1 > 0
    have nontrivial: (Fintype.ofFinite G.edgeSet).card > 0 := by
      exact Nat.lt_of_sub_eq_succ card_E_eq_y_plus_1

    -- We know that G has a leaf from a previous lemma, as a nontrivial acyclic graph
    have G_has_a_leaf : hasLeaf G := by
      exact acyclic_graphs_have_a_leaf G nonempty g_is_acyclic nontrivial -- add nontriviality (edgeset > 0)

    -- Get the leaf in question by unfolding hasLeaf
    unfold hasLeaf at G_has_a_leaf
    obtain ⟨leaf, leaf_prop⟩ := G_has_a_leaf

    -- Use the property of a leaf to obtain the unique neighbor
    rw [(Fintype.ofFinite ↑(G.neighborSet leaf)).card_eq_one_iff] at leaf_prop
    obtain ⟨x,x_is_unique⟩ := leaf_prop

    -- Call the subgraph in question G', the subgraph without the vertex 'leaf' and any incident edges (of the induced subgraph on V \ leaf vertices)
    let G' := subgraph_without_vertex_set G {leaf}

    -- To prove the Cardinality Condition on G', we first show that G' has y + 1 vertices
    have G'_has_yplus1_vertices : ((Fintype.ofFinite (G'.verts)).card) = y+1 := by
      -- Cardinalities of V(G') and V(G \ leaf) are equivalent
      have equal_card : ((Fintype.ofFinite (G'.verts)).card) = ((Fintype.ofFinite ↑(type_to_set V \ {leaf})).card) := by
        exact rfl

      rw [equal_card]
      -- The leaf is trivially in the Vertex set
      have leaf_in_V : leaf ∈ type_to_set V := by
        exact trivial

      -- We want to show the Cardinality condition holds true for G'
      -- We start with showing that | V \ leaf | = | V | - 1
      have V_without_leaf_card_eq_minus_one : (Fintype.ofFinite ↑(type_to_set V \ {leaf})).card = (Fintype.ofFinite ↑(type_to_set V)).card - 1 := by
        -- We want to work with Set.toFinset.card in order to compare the cardinality of the sets the way we want to
        simp [← Set.toFinset_card]

        -- We need the following statements for _diff, _sdiff and _singleton lemmas from mathlib
        have decidableEq : DecidableEq V:= by exact Classical.typeDecidableEq V
        have my_Fintype : Fintype ↑(type_to_set V) := by exact Fintype.ofFinite ↑(type_to_set V)

        -- Now we can use _diff, _sdiff and singleton to equate | V \ leaf | and | V | - 1
        rw [Set.toFinset_diff, Finset.card_sdiff]
        rw [Set.toFinset_singleton, Finset.card_singleton]

        -- We need a statement defining 'my_Fintype'
        have card_eq : my_Fintype.card = (Fintype.ofFinite ↑(type_to_set V)).card := by
          exact my_card_congr' my_Fintype (Fintype.ofFinite ↑(type_to_set V)) rfl

        -- We are ready to conclude. We just need to the congrfun from earlier to chaneg the goal to showing {leaf} ⊆ V
        simp [Set.toFinset_card]
        exact congrFun (congrArg HSub.hSub card_eq) 1
        -- We can show {leaf} ⊆ V using leaf ∈ V and leaf is the only element of {leaf}
        rw [Set.toFinset_singleton, Set.subset_toFinset, Finset.coe_singleton, Set.singleton_subset_iff]
        exact leaf_in_V

      -- Now that we have | V \ leaf | = | V | - 1, we can show | V \ leaf | = y - 1 using the inductive step
      rw [V_without_leaf_card_eq_minus_one]

      -- Before we conclude, we need a result explicitly mapping all v : V to our set (type_to_set V)
      have all_in_type_to_set : ∀ v : V, v ∈ (type_to_set V) := by
        exact fun _ ↦ leaf_in_V

      -- Now we use our map to justify the claim that the Set and the Type have the same cardinality
      rw [ (type_eq_set_iff_card_the_same (type_to_set V))] at all_in_type_to_set

      -- we can use this equality and the inductive step to close this goal
      rw [all_in_type_to_set]
      exact hnV

    -- The next step to proving the cardinality condition is to show | E(G - leaf) | = | E(G) | - 1 = y.
    -- We do this by considering G - leaf as a subgraph
    -- Note: I realised later we could do this with induced subgraphs as well but the difference shouldnt be too relevant
    have G'_has_y_edges : ((Fintype.ofFinite ↑(G'.edgeSet)).card) = y := by

      -- We can show our goal by showing G has y + 1 edges, and G' has 1 less edge than G
      have G_has_yplus1_edges : ((Fintype.ofFinite (G.edgeSet)).card) = y + 1 := by

        -- We are assuming the cardinality condition on the overall graph, so we can just use |V| = y + 2 to conclude this goal
        have G_has_yplus2_vertices : (Fintype.ofFinite V).card = y + 2 := by
          exact card_V_eq_y_plus_2

        -- Using the cardinality condition to conclude |E(G)| = y + 1
        rw [G_has_yplus2_vertices] at CardinalityCondition
        exact CardinalityCondition

      -- All that is left to show is G' has 1 less edge than G
      have G'_has_one_less_edge_than_G : ((Fintype.ofFinite ↑(G'.edgeSet)).card) = ((Fintype.ofFinite (G.edgeSet)).card) - 1 := by

        -- We will be using the fact that the leaf neighbor, x, is in the neighborSet leaf (trivial)
        have x_in_n_set : x.1 ∈ (G.neighborSet leaf) := by
          exact x.2

        -- We will be using the fact that the edge (x,leaf) is present in G
        have edge : G.Adj x leaf := by
          rw [SimpleGraph.mem_neighborSet] at x_in_n_set
          exact id (SimpleGraph.adj_symm G x_in_n_set)

        -- ↑x ∈ G.neighborSet leaf now implies s(leaf, ↑x) ∈ G.edgeSet by just rewriting what we have
        rw [SimpleGraph.mem_neighborSet, ←SimpleGraph.mem_edgeSet] at x_in_n_set

        -- We will want to show that the edge set of G' = the edge set of G without s(↑x, leaf), fir which we need an iff proof of the fact that
        -- if an edge appears in G', it appears in a graph with the s(↑x, leaf) edge deleted
        have adj_iff : ∀ a b, G'.Adj a b ↔ (G.deleteEdges (G.incidenceSet leaf)).Adj a b := by

          -- let a and b be such edges in G'
          intro a b

          -- Consider each direction separately:
          apply Iff.intro

          -- LHS → RHS  ∀ a b, G'.Adj a b → (G.deleteEdges (G.incidenceSet leaf)).Adj a b
          · -- We have our basic adjacency relations of G' in the definition of subgraph_without_vertex
            have adj_def : G'.Adj a b → G.Adj a b ∧ (a ∈ (type_to_set V \ {leaf})) ∧ (b ∈ (type_to_set V \ {leaf})) := by
              exact fun a ↦ a

            -- let G'_adj be the adjacency between a and b and apply the above definition to it
            intro G'_adj
            apply adj_def at G'_adj

            -- Such an edge cannot be incident to leaf
            have edge_in_edgeset_without_leaf : s(a, b) ∈ G.edgeSet \ (G.incidenceSet leaf) := by

              -- let 'edge' be such an edge between a and b
              let edge := s(a,b)

              -- by contradiction, assume this edge ∉ G.edgeSet \ G.incidenceSet leaf
              by_contra contradiction

              -- Using the contradiction, we can show that this edge is in the Incident Set
              have edge_in_incidentset_leaf : edge ∈ (G.incidenceSet leaf) := by

                -- use the refine function to change the goal to showing (a,b) is an edge in G and either a or b is a leaf
                refine (SimpleGraph.mk'_mem_incidenceSet_iff G).mpr ?_

                -- Goal : G.Adj a b ∧ (leaf = a ∨ leaf = b), so apply And.intro and and prove both sides of the ∧.
                apply And.intro
                · -- (a,b) is an edge: a b are both in G', so this follows from G' adjacency relations
                  exact G'_adj.1
                · -- We can simplify the contradiction statement to G.Adj a b ∧ (leaf = a ∨ leaf = b) and then conclude with the right side
                  rw [←SimpleGraph.edgeSet_deleteEdges] at contradiction
                  rw [SimpleGraph.mem_edgeSet] at contradiction
                  simp at contradiction
                  rw [SimpleGraph.mk'_mem_incidenceSet_iff] at contradiction

                  -- Pull out r, the edge in G'_adj, which will complete the goal with contradiction
                  obtain ⟨r,_⟩ := G'_adj
                  apply contradiction at r

                  -- Using the right side of r (coming from our contradiction statement)
                  exact r.2

              -- We know that a ∈ V \ leaf
              have a_in_V_minus_leaf : a ∈ type_to_set V \ {leaf} := by
                exact G'_adj.2.1

              -- Therefore, leaf ≠ a
              have leaf_neq_a : leaf ≠ a := by

                -- a ≠ leaf is equivalent because = is symmetric
                have a_neq_leaf : a ≠ leaf := by
                  exact Set.mem_of_mem_inter_right a_in_V_minus_leaf

                -- = is symmetric
                exact a_neq_leaf.symm

              -- We know that b ∈ V \ leaf
              have b_in_V_minus_leaf : b ∈ type_to_set V \ {leaf} := by
                exact G'_adj.2.2

              -- Therefore, leaf ≠ b
              have leaf_neq_b : leaf ≠ b := by

                -- b ≠ leaf is equivalent because = is symmetric
                have b_neq_leaf : b ≠ leaf := by
                  exact Set.mem_of_mem_inter_right b_in_V_minus_leaf

                -- = is symmetric
                exact b_neq_leaf.symm

              -- So neither a nor b can be leaf
              have neither_a_nor_b_eq_leaf : ¬ (leaf = a ∨ leaf = b) := by
                exact not_or_intro leaf_neq_a leaf_neq_b

              -- Using the contradiction, we can prove that either a or b = leaf (this is a direct contradiction to what we just showed)
              have a_or_b_eq_leaf : (leaf = a) ∨ (leaf = b) := by
                -- Rewrite Contradiction
                rw [←SimpleGraph.edgeSet_deleteEdges] at contradiction
                rw [SimpleGraph.mem_edgeSet] at contradiction
                simp at contradiction
                rw [SimpleGraph.mk'_mem_incidenceSet_iff] at contradiction

                -- Like earlier, we now want to obtain the edge (r) and its properties, the second of which is the goal, which directly
                -- contradicts the results we have shown
                obtain ⟨r,_⟩ := G'_adj
                apply contradiction at r
                obtain ⟨ _ , r_right ⟩ := r
                exact r_right

              -- This contradiction is now direct
              exact neither_a_nor_b_eq_leaf a_or_b_eq_leaf

            -- No wour goal can be simplified into s(a, b) ∈ G.edgeSet \ G.incidenceSet leaf which is a result we showed earlier
            rw [← SimpleGraph.mem_edgeSet]
            rw [SimpleGraph.edgeSet_deleteEdges]
            exact edge_in_edgeset_without_leaf

          -- LHS ← RHS : ∀ a b, G'.Adj a b ← (G.deleteEdges (G.incidenceSet leaf)).Adj a b
          · -- Let deleteEdges_Adj be such an edge in G that isn't any edge incident to leaf, and use the definition of deleteEdges to simplify the statement
            intro deleteEdges_Adj
            rw [SimpleGraph.deleteEdges_adj] at deleteEdges_Adj

            -- We have the same adjacency definition as in the previous case
            have adj_def : G'.Adj a b → G.Adj a b ∧ (a ∈ (type_to_set V \ {leaf})) ∧ (b ∈ (type_to_set V \ {leaf})) := by
              exact fun a ↦ a

            -- We would then have to have that any such edge would have endpoints (a and b) in V \ leaf
            have a_and_b_in_V_minus_leaf : G.Adj a b ∧ (a ∈ (type_to_set V \ {leaf})) ∧ (b ∈ (type_to_set V \ {leaf})) := by

              apply And.intro -- Consider 2 sides of the ∧ operation

              -- Proving G.Adj a b
              · exact deleteEdges_Adj.1-- (a,b) is clearly an edge in G by deleteEdges_Adj

              -- Proving a and b are in type_to_set V \ {leaf}
              · apply And.intro -- Consider 2 sides of the ∧ operation

                -- Proving a is in type_to_set V \ {leaf}
                · by_contra a_not_in_G' -- Suppose a ∉ (type_to_set V \ {leaf})

                  -- Simplify to if a is in V, then a = leaf, assuming a ∈ V \ leaf
                  simp at a_not_in_G'

                  -- Clearly a is in V so a must be equal to leaf
                  have a_is_leaf : a = leaf := by
                    exact a_not_in_G' trivial

                  -- So our previously defined 'edge' is now equal to s(leaf,b)
                  have edge_eq_leaf_edge : s(a,b) = s(leaf,b) :=by
                    exact congrArg Sym2.mk (congrFun (congrArg Prod.mk (a_not_in_G' trivial)) b)

                  -- s(leaf,b) has leaf as an endpoint so it must be in the incident set of leaf
                  have leaf_edge_in_incidentset : s(leaf,b) ∈ G.incidenceSet leaf := by

                    -- This is equivalent to the goal G.Adj leaf b
                    rw[SimpleGraph.mk'_mem_incidenceSet_iff]
                    simp

                    -- (a,b) is an edge in G
                    have adj_leaf : G.Adj a b := by
                      exact deleteEdges_Adj.1

                    -- We know that a = leaf and so the goal is closed
                    rw [a_is_leaf] at adj_leaf
                    exact adj_leaf

                  -- And so trivially from the above, the edge must be in the incident set of leaf
                  have edge_in_incidentset : s(a,b) ∈ G.incidenceSet leaf := by
                    exact Set.mem_of_eq_of_mem edge_eq_leaf_edge leaf_edge_in_incidentset

                  -- So now we have both that s(a,b) is in and not in G.incidenceSet leaf, contradiction
                  exact deleteEdges_Adj.2 edge_in_incidentset

                -- Proving b is in type_to_set V \ {leaf}
                · by_contra b_not_in_G' -- Suppose b ∉ (type_to_set V \ {leaf})

                  -- Simplify: if b is in V, then b = leaf, assuming b ∈ V \ leaf
                  simp at b_not_in_G'

                  -- Clearly b is in V so b must be equal to leaf
                  have b_is_leaf : b = leaf := by
                    exact b_not_in_G' trivial

                  -- So our previously defined 'edge' is now equal to s(a,leaf)
                  have edge_eq_leaf_edge : s(a,b) = s(a,leaf) :=by
                    exact congrArg Sym2.mk (congrArg (Prod.mk a) (b_not_in_G' trivial))

                  -- s(a,leaf) has leaf as an endpoint so it must be in the incident set of leaf
                  have leaf_edge_in_incidentset : s(a,leaf) ∈ G.incidenceSet leaf := by

                    -- This is equivalent to the goal G.Adj a leaf
                    rw[SimpleGraph.mk'_mem_incidenceSet_iff]
                    simp

                    -- (a,b) is an edge in G
                    have adj_leaf : G.Adj a b := by
                      exact deleteEdges_Adj.1

                    -- We know that b = leaf and so the goal is closed
                    rw [b_is_leaf] at adj_leaf
                    exact adj_leaf

                  -- And so trivially from the above, the edge must be in the incident set of leaf
                  have edge_in_incidentset : s(a,b) ∈ G.incidenceSet leaf := by
                    exact Set.mem_of_eq_of_mem edge_eq_leaf_edge leaf_edge_in_incidentset

                  -- So now we have both that s(a,b) is in and not in G.incidenceSet leaf, contradiction
                  exact deleteEdges_Adj.2 edge_in_incidentset

            -- So we can show G'.Adj a b with the fact that a and b are in V \ leaf and the adj_def we defined earlier
            exact adj_def a_and_b_in_V_minus_leaf

        -- Something we will need is the fact that |E \ s(x,leaf)| = |E| - 1, which seems obvious since we remove 1 element from the set
        have G_without_edge_card_eq_minus_one : (Fintype.ofFinite ↑(G.edgeSet \ {s(x.1, leaf)})).card = (Fintype.ofFinite G.edgeSet).card - 1 := by

          -- We need to convert these sets to Finsets in order to use the diff and singleton lemmas
          simp [← Set.toFinset_card]

          -- These are results we need to have, and indeed have, to use the Finset library
          have decidableEq : DecidableEq V:= by exact Classical.typeDecidableEq V
          have my_Fintype : Fintype G.edgeSet := by exact Fintype.ofFinite G.edgeSet

          -- Now we can use the Finset library to consider finite sets without elements, to rewrite our goal
          rw [Set.toFinset_diff, Finset.card_sdiff]
          rw [Set.toFinset_singleton, Finset.card_singleton]

          -- Now we just have some trivial results to show G.edgeSet.toFinset.card - 1 = G.edgeSet.toFinset.card - 1
          -- Showing that the previously defined my_Fintype has the same cardinality as the set it defines
          have card_eq : my_Fintype.card = (Fintype.ofFinite G.edgeSet).card := by
            exact my_card_congr' my_Fintype (Fintype.ofFinite G.edgeSet) rfl

          -- Converting Finset cardinalities back to set cardinalities, and closing half the goal with a congruent arguement
          simp [Set.toFinset_card]
          exact congrFun (congrArg HSub.hSub card_eq) 1

          -- Now we need just need to show that the edge as a finset is a subset of the edgeset as a finset. Since the edge is a singleton, this is
          -- just a rewrite to s(x,leaf) is in G.edgeSet which is trivial ('edge' result)
          rw [Set.toFinset_singleton, Set.subset_toFinset, Finset.coe_singleton, Set.singleton_subset_iff]
          exact edge

        -- We now show that the edgeset of G' is is equivalent to the edge set of G without the edge (x,leaf)
        have G_without_x_leaf_is_G' : (G.edgeSet \ {s(x.1, leaf)}) = (G'.edgeSet) := by

          -- In order to show our goal, we need to first show that the only element in the incident set of leaf is the edge (x, leaf)
          have incidentset_eq : G.incidenceSet leaf = {s(x.1, leaf)} := by

            -- first we define this vertex explicitly (eithout the properties attached to it) and prove that it is in the neighbor set of leaf
            let x_vert := x.1
            have x_vert_in_neighborSet : x_vert ∈ G.neighborSet leaf := by
              exact x.2

            -- using this, we know that  the incident Set of leaf is nonempty
            have nonemptys : Nonempty (G.incidenceSet leaf) := by

              --Assume the incident set is empty (or not nonempty which is equivalent)
              by_contra not_nonempty
              simp at not_nonempty

              -- We have that x_vert is in the neigbor set of leaf, so s(leaf, x_vert) is an edge in the incident set
              -- In particular, this incident set cannot be empty
              rw[SimpleGraph.mem_neighborSet, ← SimpleGraph.mem_incidenceSet] at x_vert_in_neighborSet
              exact not_nonempty s(leaf, x_vert) x_vert_in_neighborSet

            -- We can split our goal into 2 cases:
            -- 1) that the incident set of G is nonempty
            -- 2) G.incidenceSet leaf is a subset of {s(↑x, leaf)}, which would show equality since the opposite is trivially true
            refine (Set.Nonempty.subset_singleton_iff ?h).mp ?_

              -- Case 1: Showing G is nonempty
            · exact Set.nonempty_of_nonempty_subtype

              -- Case 2: Showing G.incidenceSet leaf ⊆ {s(↑x, leaf)}
            · by_contra incidentset_notin_sxleaf -- Assume ¬ (G.incidenceSet leaf ⊆ s(↑x, leaf)})
              simp at incidentset_notin_sxleaf

              -- retrieve such an edge that is in the incident set but is not equal to s(x,leaf), call it x_1
              obtain ⟨x_1,incidentset_notin_sxleaf⟩ := incidentset_notin_sxleaf

              -- by construction, x_1 is not equal to s(x,leaf)
              have x1_neq_sxleaf : x_1 ≠ s(↑x, leaf) := by
                exact incidentset_notin_sxleaf.2

              -- by construction, x_1 is in the set G.incidenceSet leaf
              have incidentset_in_sxleaf : x_1 ∈ (G.incidenceSet leaf):= by
                exact incidentset_notin_sxleaf.1

              -- retrieve the endpoints of such an edge, call then u and v
              obtain ⟨u,v⟩ := x_1

              -- trvially we have that something of the form Quot.mk (Sym2.Rel V) (u, v) is equivalent to an edge s(u,v)
              have id_func : Quot.mk (Sym2.Rel V) (u, v) = s(u,v) := by
                exact rfl

              -- we use the previously defined equivalence to rewrite our goal in edge format rather than the Quot.mk (Sym2.Rel V) format
              rw [id_func] at x1_neq_sxleaf
              rw [id_func] at incidentset_notin_sxleaf
              rw [id_func] at incidentset_in_sxleaf

              -- Now we want to consider every case: (ie: u or v could either be equal to leaf, or not)
              -- Start with u or v = leaf or not
              by_cases (u = leaf ∨ v = leaf)
              · rename_i u_or_v_is_leaf

                -- if u or v are leaf, consider the case that u is leaf, or not
                by_cases (u = leaf)
                · rename_i u_is_leaf

                  -- If u = leaf,  the consider the case that v is also equal to leaf, or not
                  by_cases (v = leaf)
                  · rename_i v_is_leaf

                    -- If v = leaf, then u = v
                    have u_eq_v : u = v := by
                      rw [← v_is_leaf] at u_is_leaf
                      exact u_is_leaf

                    -- Since u = v = leaf, substitute leaf for both u and v everywhere
                    subst u v

                    -- We now have that leaf is not in the incident set of leaf, which is a direct contradiction to the definition of incident set
                    rw [SimpleGraph.mem_incidence_iff_neighbor] at incidentset_in_sxleaf
                    have leaf_not_in_NS_leaf : leaf ∉ G.neighborSet leaf := by
                      exact SimpleGraph.not_mem_neighborSet_self G
                    exact leaf_not_in_NS_leaf incidentset_in_sxleaf

                    -- Now consider the case that v is not equal to leaf
                  · rename_i not_v_is_leaf

                    -- So we have v ≠w leaf
                    have v_neq_leaf : v ≠ leaf := by
                      exact not_v_is_leaf

                    -- u = leaf so we can substitute u with leaf everywhere
                    subst u

                    -- We have that u = leaf, and (u,v) ≠ (x,leaf) so it follows that v ≠ x
                    have v_is_not_x : v ≠ ↑x := by
                      -- Assume that v is equal to x
                      by_contra v_is_x

                      -- Substitute v with x.
                      subst v

                      -- We will need the symmetry of the symmetric set in the following arguement
                      have edge_symm : s(leaf, ↑x) = s(↑x, leaf) := by
                        exact Sym2.eq_swap

                      -- So we reach a contradiction, as highlighted above
                      exact x1_neq_sxleaf edge_symm

                    -- We must have that V is in the neighborhood Set of leaf since u = leaf and (v,u) is an edge in the graph
                    have v_in_NS_leaf : v ∈ G.neighborSet leaf:= by
                      exact (SimpleGraph.mem_incidence_iff_neighbor G).mp incidentset_in_sxleaf

                    -- So we can conclude that x = v with our results. To convince lean of this, we first combine our results into a variable
                    let x_eq_v := x_is_unique ⟨ v,v_in_NS_leaf ⟩

                    -- The we show that v (which has type V) is congruent to ↑x (which has type ↑(G.neighborSet leaf))
                    have v_is_x : v = ↑x := by
                      exact congrArg Subtype.val x_eq_v

                    -- Then the goal is trivially proven from our previous results
                    exact v_is_not_x v_is_x

                  -- Now we consider the case that u is not a leaf
                · rename_i not_u_is_leaf

                  -- We do the same thing again, considering the cases that v is either equal to leaf or not
                  by_cases (¬ v = leaf)

                    -- Consider the case that v isi not equal to leaf
                  · rename_i not_v_is_leaf

                    -- So we have that both u and v are not leaf
                    have u_and_v_are_not_leaf : ¬(u = leaf ∨ v = leaf) := by
                      exact not_or_intro not_u_is_leaf not_v_is_leaf

                    -- This is equivalent to ¬ (leaf = u ∨ leaf = v) by a logical arguement laid out below
                    have not_u_or_v_leaf : ¬ (leaf = u ∨ leaf = v) := by

                      -- Once again we need the symmetry of the equal sign (with u and v) to conclude this
                      have eq_symm_u : leaf = u ↔ u = leaf:= by
                        apply Iff.intro
                        · exact fun a ↦ id (Eq.symm a)
                        · exact fun a ↦ id (Eq.symm a)

                      have eq_symm_v : leaf = v ↔ v = leaf:= by
                        apply Iff.intro
                        · exact fun a ↦ id (Eq.symm a)
                        · exact fun a ↦ id (Eq.symm a)

                      -- This goal follows on from our case-wise assumption, and the symmetry of the equals sign
                      rw [eq_symm_u, eq_symm_v]
                      exact u_and_v_are_not_leaf

                    -- Since we have that neither u nor v is equal to leaf, our contradiction will be that atleast one of them is equal to leaf
                    have u_or_v_is_leaf : (leaf = u ∨ leaf = v) := by

                      -- We will show using previous results that such an edge is an edge in the parent graph with one of its endpoints being equal to leaf
                      have edge_and_u_or_v_eq_leaf: G.Adj u v ∧ ( leaf = u ∨ leaf = v ) := by
                        exact (SimpleGraph.mk'_mem_incidenceSet_iff G).mp incidentset_in_sxleaf

                      -- So now u or v is equal to leaf
                      exact edge_and_u_or_v_eq_leaf.2

                    -- We have 2 contradicting statements which closes the goal
                    exact not_u_or_v_leaf u_or_v_is_leaf

                    -- Now consider the case that v = leaf (or more specifically not v is not equal to v which is equivalent)
                  · rename_i not_not_v_is_leaf

                    -- Once again we will find it useful to state the symmetry of the equal sign
                    have edge_symm : s(u,v) = s(v,u) := by
                      exact Sym2.eq_swap

                    -- We have that x1 = s(v,u) is not equal to s(x, leaf)
                    have x1_neq_sxleaf : s(v, u) ≠ s(↑x, leaf):= by
                      exact ne_of_eq_of_ne (id (Eq.symm edge_symm)) x1_neq_sxleaf

                    -- Despite the above, we have that s(u,v) is in the incident set of leaf
                    have incidentset_in_sxleaf : s(v, u) ∈ G.incidenceSet leaf:= by
                      exact Set.mem_of_eq_of_mem (id (Eq.symm edge_symm)) incidentset_in_sxleaf

                    -- We have that v = leaf, which is what is quoted at the start of this case
                    have v_is_leaf : v = leaf := by
                      --Assume that v is not equal to leaf, this gives a contradiction cause we know that v is not not equal to leaf
                      by_contra not_v_leaf
                      exact not_not_v_is_leaf not_v_leaf

                    -- u not equal to leaf is our assumption in this case
                    have u_neq_leaf : u ≠ leaf := by
                      exact not_u_is_leaf

                    -- Sinec v = leaf, we can substitute every v with leaf instead
                    subst v

                    -- So now we have that u is not the vertex, x, which is the unique vertex incident to leaf
                    have u_is_not_x : u ≠ ↑x := by
                      -- Assume that u = x for contradiction
                      by_contra u_is_x

                      -- Substitute u with x in all our previous results
                      subst u

                      --- We will need the symmetry of the equals sign again
                      have edge_symm : s(leaf, ↑x) = s(↑x, leaf) := by
                        exact Sym2.eq_swap

                      -- This is a contradiction since if u = x and v = leaf then (u,v) = (x,leaf) which gives us our contradiction
                      exact x1_neq_sxleaf edge_symm

                    -- So we have that u ≠ x. If we show u is still in the neighbor set of leaf then we will be trivially done
                    have u_in_NS_leaf : u ∈ G.neighborSet leaf:= by
                      exact (SimpleGraph.mem_incidence_iff_neighbor G).mp incidentset_in_sxleaf

                    -- As done before, we introduce a term for the equivalence of x and u (previously done with x and v)
                    let x_eq_u := x_is_unique ⟨ u,u_in_NS_leaf ⟩


                    -- As done earlier, u of type V is equivalent to x of type ↑(G.neighborSet leaf) is neccessary to proving our goal
                    have u_eq_x : u = ↑x := by
                      exact congrArg Subtype.val x_eq_u

                    -- And so this goal is now trivial
                    exact u_is_not_x u_eq_x

                -- Finally we have the case that neither u nor v are equal to leaf
              · rename_i u_and_v_are_not_leaf

                -- This is equivalent to ¬ (leaf = u ∨ leaf = v)
                have not_u_or_v_leaf : ¬ (leaf = u ∨ leaf = v) := by

                  -- Once again we use the symmetry of the equals sign with u and v
                  have eq_symm_u : leaf = u ↔ u = leaf:= by
                    apply Iff.intro
                    · exact fun a ↦ id (Eq.symm a)
                    · exact fun a ↦ id (Eq.symm a)
                  have eq_symm_v : leaf = v ↔ v = leaf:= by
                    apply Iff.intro
                    · exact fun a ↦ id (Eq.symm a)
                    · exact fun a ↦ id (Eq.symm a)

                  -- This is now trivial since the goal is equivalent to the assumption with the equals sign symmetry
                  rw [eq_symm_u, eq_symm_v]
                  exact u_and_v_are_not_leaf

                -- We have from our previous results that u or v must be leaf
                have u_or_v_is_leaf : (leaf = u ∨ leaf = v) := by

                  -- Since (u,v) is in the incident set of leaf, the set exists in the parent graph and u or v = leaf
                  have edge_and_u_or_v_eq_leaf: G.Adj u v ∧ ( leaf = u ∨ leaf = v ) := by
                    exact (SimpleGraph.mk'_mem_incidenceSet_iff G).mp incidentset_in_sxleaf

                  -- Using the previous result, u or v = leaf
                  exact edge_and_u_or_v_eq_leaf.2

                -- And so we get our contradiction from the assumption and the previous result
                exact not_u_or_v_leaf u_or_v_is_leaf

          -- Because we have this equivalence between G.incidenceSet leaf and {s(↑x, leaf)}, we can rewrite the goal
          rw [← incidentset_eq]

          -- To prove equality between (G.edgeSet \ G.incidenceSet leaf) and (G'.edgeSet) we can show double inclusion
          -- We will start with (G.edgeSet \ G.incidenceSet leaf) ⊆ (G'.edgeSet)
          have subset : (G.edgeSet \ G.incidenceSet leaf) ⊆ (G'.edgeSet) := by

            -- To prove the subset relationship, we need that all edges in (G.edgeSet \ (G.incidenceSet leaf)) are also edges in G'
            have z_in_Gwithoutleaf_imp_z_in_G' : ∀ z ∈ (G.edgeSet \ (G.incidenceSet leaf)), z ∈ G'.edgeSet := by

              -- Let z be such an edge and in_Set be the property that z is in (G.edgeSet \ (G.incidenceSet leaf))
              intro z in_Set

              -- Let a and b be the endpoints of the edge z
              obtain ⟨a,b⟩ := z

              -- We have from previous results and the 'deleteEdges' lemma that (G.deleteEdges (G.incidenceSet leaf)).edgeSet = G.edgeSet \ (G.incidenceSet leaf)
              have Gwithoutleaf_eq_z_in_G' : (G.deleteEdges (G.incidenceSet leaf)).edgeSet = G.edgeSet \ (G.incidenceSet leaf) := by
                exact SimpleGraph.edgeSet_deleteEdges (G.incidenceSet leaf)

              -- We can simplify in_Set to be that (a,b) is an edge in G'
              rw [← Gwithoutleaf_eq_z_in_G'] at in_Set
              rw [SimpleGraph.mem_edgeSet] at in_Set
              rw [← adj_iff] at in_Set

              -- So the goal is proven after the mem_edgeSet lemma in mathlib, with in_Set
              rw [SimpleGraph.Subgraph.mem_edgeSet]
              exact in_Set

            -- So we have shown that z is in (G.edgeSet \ (G.incidenceSet leaf)) implies that z is in G'.edgeSet
            exact z_in_Gwithoutleaf_imp_z_in_G'

          -- Next we need to prove (G'.edgeSet) ⊆ (G.edgeSet \ G.incidenceSet leaf)
          have superset : (G'.edgeSet) ⊆ (G.edgeSet \ G.incidenceSet leaf) := by

            -- To prove the subset relationship, we need that all edges in G' are also edges in (G.edgeSet \ (G.incidenceSet leaf))
            have z_in_G'_imp_z_in_Gwithoutleaf : ∀ z ∈ G'.edgeSet, z ∈ (G.edgeSet \ (G.incidenceSet leaf)) := by

              -- Let z be such an edge and in_Set be the property that z is in G'
              intro z in_Set

              -- Let a and b be the endpoints of the edge z
              obtain ⟨a,b⟩ := z

              -- Once again we try to rewrite in_Set in the form of the definition deleteEdge, which is closer to what we want to show
              rw [SimpleGraph.Subgraph.mem_edgeSet] at in_Set
              rw [adj_iff] at in_Set

              -- Now that we have in_Set in the deleteEdges form, by proving
              -- (G.deleteEdges (G.incidenceSet leaf)).edgeSet = G.edgeSet \ (G.incidenceSet leaf) the goal can be closed with in_Set
              have Gwithoutleaf_eq_z_in_G' : (G.deleteEdges (G.incidenceSet leaf)).edgeSet = G.edgeSet \ (G.incidenceSet leaf) := by
                exact SimpleGraph.edgeSet_deleteEdges (G.incidenceSet leaf)

              -- So finally rewriting in_Set gives the goal
              rw [← SimpleGraph.mem_edgeSet] at in_Set
              rw [Gwithoutleaf_eq_z_in_G'] at in_Set
              exact in_Set

            -- And so by definition (G'.edgeSet) ⊆ (G.edgeSet \ G.incidenceSet leaf)
            exact z_in_G'_imp_z_in_Gwithoutleaf

          -- So we have a double inclusion, which will result in equality
          exact Set.Subset.antisymm subset superset

        -- Introduce a variable for the congruency between the cardinalities of the finite sets G'.edgeSet and G.edgeSet \ {s(x.1, leaf)}
        let card_G'_eq_G_without_edge := my_card_congr' (Fintype.ofFinite (↑(G.edgeSet \ {s(x.1, leaf)}))) (Fintype.ofFinite ↑G'.edgeSet)

        -- Rewriting the goal with our previous results give the result
        rw [← card_G'_eq_G_without_edge]
        exact G_without_edge_card_eq_minus_one
        exact congrArg Set.Elem G_without_x_leaf_is_G'

      -- So now we just have to prove that the edge set of G' has y elements, so using |E(G')| = |E(G)| - 1, we can conclude this easily
      rw [G_has_yplus1_edges] at G'_has_one_less_edge_than_G
      simp at G'_has_one_less_edge_than_G
      exact G'_has_one_less_edge_than_G

    -- Now we want to show G is acyclic and this follows exactly from a previous lemma
    have G'_is_acyclic : isAcyclic G'.coe := by
      exact any_subgraph_of_an_acyclic_graph_is_acyclic G G' g_is_acyclic

    -- We want to show the cardinality condition holds for G', for the closure of the goal
    have CardinalityConditionG' : (Fintype.ofFinite G'.coe.edgeSet).card = ((Fintype.ofFinite (G'.verts)).card) - 1 := by

      -- We need an equivalence between the cardinality of the edge sets of G'.coe and G'
      have G'coe_eq_G' : (Fintype.ofFinite G'.coe.edgeSet).card = (Fintype.ofFinite G'.edgeSet).card := by

        -- Consider the cases that y = 0, or y > 0 (keeping in mind that cardinalities are always natural numbers)
        by_cases (y = 0)

        -- First consider the case that y = 0
        · rename_i y_eq_zero

          -- if y = 0 then G' has no edges
          rw[y_eq_zero] at G'_has_y_edges

          -- So G' has an empty edge set
          have G'_edgeset_empty : (Fintype.ofFinite G'.edgeSet).card = 0 := by
            exact G'_has_y_edges

          -- Rewriting with previous results:
          rw [G'_edgeset_empty]
          rw [(Fintype.ofFinite G'.edgeSet).card_eq_zero_iff] at G'_edgeset_empty

          --  We can use all of our results to now show that every edge in G'.coe is in G'
          have edge_in_G'_implies_edge_in_G'_coe  : ∀ x y, s(x,y) ∈ G'.coe.edgeSet → (s(x.1,y.1) ∈ G'.edgeSet) := by

            -- Let s(x,y) be an edge in G' and 'a' a proof of this membership
            intro x y a
            exact a
            -- So we can combine this membership to create elements that are in an edge of G_1.coe

          -- Simplifying isEmpty and other basic results
          simp_all only [isEmpty_subtype, exists_false]

          -- We see our goal is to show G'.coe.edgeSet is also empty
          rw [(Fintype.ofFinite G'.coe.edgeSet).card_eq_zero_iff]

          -- Assuming that G'.coe has non empty edge set
          by_contra nonempty_coe_edgeSet

          -- Clearly there exists an edge in G'.coe
          simp [isEmpty_subtype] at nonempty_coe_edgeSet

          -- let e be this edge, and x and y be the vertices in this edge
          obtain ⟨e, e_prop⟩ := nonempty_coe_edgeSet
          obtain ⟨x, y⟩ := e

          -- And so this goal is closed by the previous results
          exact edge_in_G'_implies_edge_in_G'_coe x y e_prop

          -- Now assume y is not equal to zero
        · rename_i y_neq_zero

          -- We have that G' has a nonempty edge set since G' has atleast 1 edge
          have nonempty_edgeSet : Nonempty G'.edgeSet := by

            -- G' has non-empty edgeset because of the previous assumptions
            have card_not_zero : (Fintype.ofFinite G'.edgeSet).card ≠ 0 := by
              simp_all only [nonempty_subtype, ne_eq, AddLeftCancelMonoid.add_eq_zero, one_ne_zero,
                and_false, not_false_eq_true]

            -- Assume for contradiction that the edge set is empty
            by_contra empty_edgeSet

            -- Then the cardinality of the edge set is zero
            have card_zero : (Fintype.ofFinite G'.edgeSet).card = 0 := by
              simp_all only [nonempty_subtype, not_false_eq_true, not_exists, isEmpty_subtype, implies_true, Fintype.card_eq_zero]

            -- So the contradiction arises from the assumption and the previous result
            exact card_not_zero card_zero

          -- So we can use the subgraph_edgeSet_card_eq_coe_card lemma from earlier to conclude this goal
          exact subgraph_edgeSet_card_eq_coe_card G' nonempty_edgeSet

      -- And now since we have a relationship between G'.coe and G', we can complete the goal of establishing the cardinality condition on G'
      rw [G'coe_eq_G', G'_has_y_edges, G'_has_yplus1_vertices]
      simp

    -- We will need a sort of trivial result, stating that y ≤ y for all y in the natural numbers
    have hyp : y ≤ y := by
      exact Nat.le_refl y

    -- We now need to show that G' has a non zero number of vertices to show connectivity of G'.coe
    have nonemptyG' : Nonempty ↑(G'.verts) := by

      -- G' has greater than 1 vertex because G' has y+1 vertices and y > 0
      have G'_has_gte_one_vertex : 0 < (Fintype.ofFinite ↑(G'.verts)).card := by
        rw [G'_has_yplus1_vertices]
        simp

      -- So G cannot have zero vertices so it cannot be empty
      rw [(Fintype.ofFinite ↑(↑G'.verts)).card_pos_iff] at G'_has_gte_one_vertex
      exact G'_has_gte_one_vertex

    -- We will need the arithmetically equivalent G'.verts - 1 = y, which follows exactly from the previous result
    have inductive_check : ((Fintype.ofFinite (G'.verts)).card) - 1 = y := by
      rw [G'_has_yplus1_vertices]
      simp

    -- So we now have that G'.coe is connected with our previous results
    have G'_connected : G'.coe.Connected := by
      exact hy y hyp G'.coe nonemptyG' G'_is_acyclic CardinalityConditionG' inductive_check

    -- Using this, G must be preconnected because leaf is reachable from x, which is reachable for all vertices in G'
    have G_preconnected : G.Preconnected := by

      -- We will use the definition of preconnected to show this
      unfold SimpleGraph.Preconnected

      -- Since G'.coe is connected, we have trivially that it is preconnected
      have G'_coe_precon : G'.coe.Preconnected := by
        exact G'_connected.1

      -- So we now use the definition of preconnected at the result that G'.coe is preconnected
      unfold SimpleGraph.Preconnected at G'_coe_precon

      -- As stated earlier, these results prove that every vertex in G' is reachable from any other vertex in G'
      have all_verts_in_G'_reachable : ∀ a b : G'.verts, G.Reachable ↑a ↑b := by

        -- Let a and b 2 such vertices
        intro a b

        -- let the reachability between a and b be stored in a variable and apply the homomorphism that takes a subgraph to a graph, onto this variable
        let reachable_in_coe := G'_coe_precon a b
        apply SimpleGraph.Reachable.map subgraph_to_graph_hom at reachable_in_coe

        -- Using the same homomorphism, we can map a vertex in the subgraph to the same vertex in the graph
        have a_to_up_a : subgraph_to_graph_hom a = ↑a := by
          exact rfl
        have b_to_up_b : subgraph_to_graph_hom b = ↑b := by
          exact rfl

        -- And so rewriting all the vertices in the subgraph with vertices in the graph, we can close this goal
        rw [a_to_up_a,b_to_up_b] at reachable_in_coe
        exact reachable_in_coe

      -- So we start proving reachability from leaf (ie: leaf is reachable from every vertex in V)
      have a_leaf_reachable : ∀ a : V, G.Reachable a leaf := by

        -- We can first show that leaf is reachable from x, which is a consequence of previous results
        have leaf_x_reachable : G.Reachable leaf x.1 := by

          -- x.1 is the vertex and x.2 is the property that this vertex is the only vertex that has an edge incident to leaf
          have x_in_n_set : x.1 ∈ (G.neighborSet leaf) := by
            exact x.2

          -- And so x is reachable from leaf, and vice versa
          rw [SimpleGraph.mem_neighborSet, ←SimpleGraph.mem_edgeSet] at x_in_n_set
          exact SimpleGraph.Adj.reachable x_in_n_set

        -- Now let us introduce a vertex a. Note that we have already done the work in the case that a = leaf or a = x
        intro a
        rw[SimpleGraph.reachable_comm]

        -- Splitting into the cases a = leaf and ¬ a = leaf
        by_cases (a = leaf)

          -- Consider the case that a = leaf
        · rename_i a_eq_leaf
          -- If a = leaf then trivially a is reachable from a
          rw[a_eq_leaf]

          -- Consider the case that a ≠ leaf
        · rename_i a_neq_leaf

          -- We can reach leaf from any vertex, a through x, which is in the incident set of the leaf
          -- We first show that x is in the vertices of G'
          have x_in_G'Verts : x.1 ∈ G'.verts := by

            -- We can explicitly define G'verts as type_to_set V \ {leaf}
            have G'_equiv: G'.verts = type_to_set V \ {leaf} := by
                exact rfl

            -- x cannot be the same as leaf since it is the only neighbor of leaf
            have x_neq_leaf: x.1 ≠ leaf := by
              simp

              -- Assume for contradiction that x = leaf
              by_contra x_eq_leaf
              rw [← x_eq_leaf] at G'_equiv

              -- Let x_prop be the property that x is the unique vertex adjacent to leaf and rewrite this with x = leaf
              let x_prop := x.2
              rw [x_eq_leaf] at x_prop

              -- leaf cannot be its own neighbor so this is trivial
              have not_mem_neighborSet_self : leaf ∉ G.neighborSet leaf := by simp
              exact not_mem_neighborSet_self x_prop

            -- Using previous results this is now exactly closed after rewriting G'.verts as type_to_set V \ {leaf}
            rw [G'_equiv]
            exact Set.mem_diff_of_mem trivial x_neq_leaf

          -- Now we prove that a is in G' as well to show that a is reachable from x
          have a_in_G'Verts : a ∈ G'.verts := by

            -- We define the same equivalence as earlier and can conclude in a similar way
            have G'_equiv: G'.verts = type_to_set V \ {leaf} := by
                exact rfl
            rw [G'_equiv]
            exact Set.mem_diff_of_mem trivial a_neq_leaf

          -- Now we can use the previous 2 results to show that x and a are reachable
          have x_reachable_a : G.Reachable x a := by
            exact all_verts_in_G'_reachable ⟨x,x_in_G'Verts⟩ ⟨a,a_in_G'Verts⟩

          -- Finally we can use the fact that x and a are reachable and x and leaf are reachable to show leaf and a are reachable fro all a
          exact SimpleGraph.Reachable.trans leaf_x_reachable x_reachable_a

      -- We now need to show that all u and v in G are reachable, and we can do this using the previous results and considering cases where u and/or v = leaf
      intro u v

      -- We will consider the cases that either u or v = leaf or neither u nor v are equal to leaf
      by_cases (u = leaf ∨ v = leaf)

        -- First consider the case that either u or v = leaf
      · rename_i u_or_v_is_leaf

        -- Then consider the cases that u = leaf and u ≠ leaf
        by_cases (u = leaf)

          -- So consider the first case: u = leaf
        · rename_i u_is_leaf

          -- Since u = leaf, substitute u with leaf
          subst u

          -- Any vertex (v specifically in this case) is reachable from leaf as in our previous result
          exact
            SimpleGraph.Reachable.symm
              (SimpleGraph.Reachable.mono (fun ⦃v w⦄ a ↦ a) (a_leaf_reachable v))

          -- Now consider the second case: u ≠ leaf
        · rename_i u_not_leaf

          -- Then consider the cases that v = leaf and v ≠ leaf
          by_cases (v = leaf)

            -- So consider the first case: v = leaf
          · rename_i v_is_leaf

            -- Since u = leaf, substitute u with leaf
            subst v

            -- Any vertex (v specifically in this case) is reachable from leaf as in our previous result
            exact a_leaf_reachable u

            -- Conside the second case that v ≠n leaf
          · rename_i v_not_leaf

            -- So now we have that neither u nor v is equal to leaf
            have u_neq_leaf: ¬ u=leaf → u ≠ leaf := by
              exact fun _ ↦ u_not_leaf
            have v_neq_leaf: ¬ v=leaf → v ≠ leaf := by
              exact fun _ ↦ v_not_leaf
            apply u_neq_leaf at u_not_leaf
            apply v_neq_leaf at v_not_leaf

            -- Because of the fact that u and v ≠ leaf, they are in the set V \ leaf
            have u_in_G' : u ∈ type_to_set V \ {leaf} := by
              exact
                Set.mem_diff_of_mem trivial
                  (u_neq_leaf u_not_leaf)
            have v_in_G' : v ∈ type_to_set V \ {leaf} := by
              exact
                Set.mem_diff_of_mem trivial
                  (v_neq_leaf v_not_leaf)

            -- So u and v are in G'
            have u_in_G'verts : u ∈ ↑G'.verts := by
              exact u_in_G'
            have v_in_G'verts : v ∈ ↑G'.verts := by
              exact v_in_G'

            -- Because u and v are in G', then by previous results they are reachable from each other
            exact all_verts_in_G'_reachable ⟨u,u_in_G'verts⟩ ⟨v,v_in_G'verts⟩

        -- Now consider the case that neither u nor v = leaf
      · rename_i u_and_v_are_not_leaf

        -- This case is logically equivalent to ¬ u = leaf and ¬ v = leaf
        have u_and_v_are_not_leaf : (¬ u = leaf) ∧ (¬ v = leaf) := by
          exact not_or.mp u_and_v_are_not_leaf

        -- And so we have u ≠ leaf and v ≠ leaf
        have u_neq_leaf: ¬ u=leaf → u ≠ leaf := by
          exact fun a ↦ a
        have v_neq_leaf: ¬ v=leaf → v ≠ leaf := by
          exact fun a ↦ a

        -- Because of the fact that u and v ≠ leaf, they are in the set V \ leaf
        have u_in_G' : u ∈ type_to_set V \ {leaf} := by
          exact
            Set.mem_diff_of_mem trivial
              (u_neq_leaf u_and_v_are_not_leaf.1)
        have v_in_G' : v ∈ type_to_set V \ {leaf} := by
          exact
            Set.mem_diff_of_mem trivial
              (v_neq_leaf u_and_v_are_not_leaf.2)

        -- So u and v are in G'
        have u_in_G'verts : u ∈ ↑G'.verts := by
          exact u_in_G'
        have v_in_G'verts : v ∈ ↑G'.verts := by
          exact v_in_G'

        -- Because u and v are in G', then by previous results they are reachable from each other
        exact all_verts_in_G'_reachable ⟨u,u_in_G'verts⟩ ⟨v,v_in_G'verts⟩

    -- So all vertices are reaachable from each other so G is preconnected
    exact SimpleGraph.Connected.mk G_preconnected

/-- The Second part of the proof of (6) → (1,2,3,4,5). It is completes the proof that an acyclic graph with one less edge than vertices is a tree-/
lemma six_implies_onetwothreefourfive_step_two {V : Type} [Finite V] (G : SimpleGraph V) (nonempty : Nonempty V) (g_is_acyclic : isAcyclic G)
                                      (CardinalityCondition : (Fintype.ofFinite G.edgeSet).card = (Fintype.ofFinite V).card - 1): isTree G := by

  -- Using the cardinality condition, acyclicity and step one to prove that G is a tree
  have g_is_connected : G.Connected := by

    -- this is exactly what we proved in step 1
    exact six_implies_onetwothreefourfive_step_one G nonempty g_is_acyclic CardinalityCondition

  -- Retrieve the definition of a tree
  unfold isTree

  -- We want to show that both conditions of a tree are met, and so we open the cases:
  apply And.intro
  · case left =>

      -- g is connected by assumption
      exact g_is_connected

  · case right =>

      -- g is acyclic by assumption
      exact g_is_acyclic

/-- The proof of (1,2,3,4,5) → (6) It is a proof that a connected acyclic graph has one less edge than it has vertices-/
lemma onetwothreefourfive_implies_six {V : Type} [Finite V] (G : SimpleGraph V) (G_is_tree : isTree G) (nonempty: Nonempty V)
                                      : (isAcyclic G) ∧ ((Fintype.ofFinite G.edgeSet).card = (Fintype.ofFinite V).card - 1) := by

  -- We want to show that G is both Acyclic and satisfies the cardinality condition. So we open both cases:
  apply And.intro

  · case left =>

      -- we create and prove the hypothesis that G is acyclic, using the fact that it is a tree (1) which is connected and acyclic by definition
      have g_is_acyclic : isAcyclic G := by
        unfold isTree at G_is_tree
        simp_all
      exact g_is_acyclic

  · case right =>

      -- We create and prove the hypothesis that G satisfies the cardinality condition.
      have CardinalityCondition : (Fintype.ofFinite G.edgeSet).card = (Fintype.ofFinite V).card - 1 := by

        -- by using (5), we know that any tree satisfies the cardinality condition
        exact onetwothreefour_implies_five G G_is_tree nonempty
      exact CardinalityCondition

/-- The proof of equivalence between (6) and (1,2,3,4,5)-/
theorem onetwothreefourfive_equiv_six {V : Type} [Finite V] (G : SimpleGraph V) (nonempty: Nonempty V) :
                                              (isAcyclic G ∧ (Fintype.ofFinite G.edgeSet).card = (Fintype.ofFinite V).card - 1) = isTree G := by

  -- using the defintion of what it means to be a tree (connected and acyclic)
  unfold isTree

  -- equality is equivalent to double implication
  simp_all only [eq_iff_iff]

  -- to prove double implication we split each implication up into its respective cases
  apply Iff.intro

  · intro a

    -- we are trying to prove connectivity here:
    simp_all only [and_true]

    -- we can extract acyclicity and the cardinality condition from our assumption in this case
    obtain ⟨g_is_acyclic, CardinalityCondition⟩ := a

    -- Then plugging in all our assumptions into our previous lemma proves this case
    exact
      six_implies_onetwothreefourfive_step_one G nonempty g_is_acyclic
        CardinalityCondition

  · intro a

    -- we are trying to prove the cardinality condition here:
    simp_all only [true_and]

    -- we can extract acyclicity and connectivity from our assumption in this case
    obtain ⟨g_is_connected, g_is_acyclic⟩ := a

    --by these assumptions, G is a tree
    have G_is_tree: isTree G := by
      unfold isTree
      simp_all

    -- Then plugging in all our assumptions into our previous lemma proves this case
    have forward : isAcyclic G ∧ (Fintype.ofFinite G.edgeSet).card = (Fintype.ofFinite V).card - 1 := by
      exact onetwothreefourfive_implies_six G G_is_tree nonempty
    simp_all

-- End of work done by Krishna

---------------------------------------------------------------------------------------------
