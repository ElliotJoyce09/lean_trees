import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Logic.Basic
import Mathlib.Order.Cover

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

def threeVariableXOR (p q r : Prop) : Prop :=
  (p ∨ q ∨ r) ∧ ¬((p ∧ q) ∨ (q ∧ r) ∨ (r ∧ p)) ∧ ¬(p ∧ q ∧ r)

def P3 : SimpleGraph (Fin 3) :=
  { Adj := fun (x y : Fin 3) => y - x = 1 ∨ x - y = 1}

def isP3 (G : SimpleGraph (Fin 3)) : Prop :=
  ∀ (u v w : Fin 3), threeVariableXOR (¬ G.Adj u v) (¬ G.Adj u w) (¬ G.Adj v w)

theorem P3IsP3 : isP3 P3 := by
  intro u v w
  apply And.intro
  rw [← not_and_or, ← not_and_or]
  simp [P3]
  intros hp hq
  cases' hp with hpp hpq
  rw [] at hpp --need to get u - v = 1 to be u = 1 + v


  -- if this hold we then have a cycle, so i mean what do i do now???
  sorry

theorem maximallyAcyclicP3 : isMaximallyAcyclic P3 := by
  apply And.intro


  sorry

def isUniquePath {V : Type} (u v : V) (G: SimpleGraph V) : Prop :=
  ∀ (a b : G.Path u v), a = b

def Tree {V: Type} (G : SimpleGraph V) : Prop :=
  G.Connected ∧ isAcyclic G
