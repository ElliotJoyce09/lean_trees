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

structure FiniteSimpleGraph (V : Type u) extends SimpleGraph V where
  finiteVertSet : Finite V
  finiteEdgeSet : Finset edgeSet

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
