import Mathlib.Combinatorics.SimpleGraph.Basic

namespace FourColor.Curriculum.Actual

variable {α : Type*} (G : SimpleGraph α)

/-- Simple graphs are loopless. -/
theorem not_adj_self (v : α) : ¬ G.Adj v v :=
  G.loopless v

/-- Adjacency is symmetric in simple graphs. -/
theorem adj_symm {v w : α} (h : G.Adj v w) : G.Adj w v :=
  G.symm h

/-- A vertex is never in its own neighbor set. -/
theorem not_mem_neighborSet_self (v : α) : v ∉ G.neighborSet v := by
  intro hv
  exact G.loopless v hv

/-- Membership in the neighbor set is adjacency. -/
theorem mem_neighborSet_iff {v w : α} : w ∈ G.neighborSet v ↔ G.Adj v w :=
  Iff.rfl

end FourColor.Curriculum.Actual
