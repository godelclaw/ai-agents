import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

namespace FourColor.Curriculum.Actual

variable {α : Type*} (G : SimpleGraph α)

/-- Every vertex is reachable from itself. -/
theorem reachable_refl (v : α) : G.Reachable v v :=
  ⟨SimpleGraph.Walk.nil⟩

/-- Reachability is symmetric in simple graphs. -/
theorem reachable_symm {u v : α} (h : G.Reachable u v) : G.Reachable v u :=
  h.symm

/-- Reachability is transitive. -/
theorem reachable_trans {u v w : α}
    (huv : G.Reachable u v) (hvw : G.Reachable v w) :
    G.Reachable u w :=
  huv.trans hvw

/-- An edge gives a reachable pair. -/
theorem adj_implies_reachable {u v : α} (h : G.Adj u v) : G.Reachable u v :=
  ⟨SimpleGraph.Walk.cons h SimpleGraph.Walk.nil⟩

end FourColor.Curriculum.Actual
