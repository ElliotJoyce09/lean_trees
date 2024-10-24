import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Combinatorics.SimpleGraph.Basic

namespace trees

def Cycle {V: Type} (G: SimpleGraph V) : Prop :=
  -- should take a vertex in V and check if there is a path which starts
  -- from that vertex and end at that vertex
  sorry

def Acyclic {V : Type} (G : SimpleGraph V) : Prop :=
  -- should take all verticies in V and check if that vertex has a cycle
  sorry

def Tree {V: Type} (G: SimpleGraph V) : Prop :=
  -- should satisfy that G is Connected and Acyclic
  sorry
