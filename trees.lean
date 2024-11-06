import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Combinatorics.SimpleGraph.Basic

namespace trees

-- I made this def for a path before I realised we have Paths already (I literally typed out import SimpleGraph.Path but didn't realise lol) and also before I realised strucutres were more apt but might as well put it in.
def pathGraph : SimpleGraph ℕ where
  Adj a b := (a ≠ b) ∧ ((a = b + 1) ∨ (b = a + 1))
   -- Have used N here, probably shouldn't
  symm a b h := by
    cases h with
    | intro left right => --splits into either case of the ∧
      constructor
      · apply Ne.symm left -- left is just the goal flipped, so apply symmetry of not equal to and we are done
      · apply Or.symm right -- similar but for right goal and or
    done
  loopless a ha := by -- COMMENT LATER
    dsimp at ha
    cases ha with
    | intro left right =>
      exact left rfl 
    done

def Cycle {V: Type} (G: SimpleGraph V) : Prop := -- This is in SimpleGraph.Path, so are some others, do we want to strip back what we are using or just use the premade ones?
  -- should take a vertex in V and check if there is a path which starts
  -- from that vertex and end at that vertex
  sorry

def Acyclic {V : Type} (G : SimpleGraph V) : Prop :=
  -- should take all verticies in V and check if that vertex has a cycle
  sorry

--def Tree {V: Type} (G: SimpleGraph V) : Prop :=
  -- should satisfy that G is Connected and Acyclic
  --sorry
structure Tree : Prop where -- i have based this around how connected is definied in SimpleGraph.Basic
  protected connected (G : SimpleGraph V): G.Connected --checks if the graph is connected (connectedness is defined much the same way but for preconnected)
  --protected acyclic (G : SimpleGraph V): G.Acyclic Will remove comments once done
  protected [nonempty : Nonempty V] -- check there is at least 1 vertex
-- I dont think we should be using definitions for most of these. my understanding is definitions are for specific instances or like functions, and then structures are for general types, i.e all tree graphs. Feel free to correct me but this is just my current understanding
