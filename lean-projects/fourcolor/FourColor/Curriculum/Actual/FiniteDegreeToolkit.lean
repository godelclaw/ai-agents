import Mathlib.Combinatorics.SimpleGraph.Finite

namespace FourColor.Curriculum.Actual

variable {V : Type*} [Fintype V]

/-- Degree is the cardinality of the neighbor set. -/
theorem card_neighborSet_eq_degree
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    Fintype.card (G.neighborSet v) = G.degree v :=
  G.card_neighborSet_eq_degree v

/-- Any vertex degree is strictly less than the number of vertices. -/
theorem degree_lt_card_verts
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    G.degree v < Fintype.card V :=
  G.degree_lt_card_verts v

/-- The minimum degree is bounded by every vertex degree. -/
theorem minDegree_le_degree
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    G.minDegree ≤ G.degree v :=
  G.minDegree_le_degree v

/-- If the graph is nonempty, a vertex realizing minimum degree exists. -/
theorem exists_minimal_degree_vertex
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V] :
    ∃ v, G.minDegree = G.degree v :=
  G.exists_minimal_degree_vertex

/-- If the graph is nonempty, a vertex realizing maximum degree exists. -/
theorem exists_maximal_degree_vertex
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V] :
    ∃ v, G.maxDegree = G.degree v :=
  G.exists_maximal_degree_vertex

/-- Minimum degree is bounded above by maximum degree. -/
theorem minDegree_le_maxDegree
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.minDegree ≤ G.maxDegree :=
  G.minDegree_le_maxDegree

/-- If the graph is nonempty, minimum degree is strictly less than the number of vertices. -/
theorem minDegree_lt_card_verts
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V] :
    G.minDegree < Fintype.card V :=
  G.minDegree_lt_card

/-- If the graph is nonempty, maximum degree is strictly less than the number of vertices. -/
theorem maxDegree_lt_card_verts
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V] :
    G.maxDegree < Fintype.card V :=
  G.maxDegree_lt_card_verts

/-- Degree is monotone under subgraph inclusion. -/
theorem degree_mono_of_subgraph
    {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hGH : G ≤ H) (v : V) :
    G.degree v ≤ H.degree v :=
  G.degree_le_of_le (v := v) hGH

/-- Minimum degree is monotone under subgraph inclusion. -/
theorem minDegree_mono_of_subgraph
    {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hGH : G ≤ H) :
    G.minDegree ≤ H.minDegree :=
  G.minDegree_le_minDegree hGH

end FourColor.Curriculum.Actual

