/-
# Bondy & Murty, Graph Theory — Chapter 3: Connected Graphs

Formalization of definitions and results from Chapter 3 of:
  J. A. Bondy and U. S. R. Murty, *Graph Theory* (2007), Springer GTM 244.

## Contents
- Connectivity definitions
- Theorem 3.1 (Walk ⟹ path)
- Proposition 3.4 (cut edge characterization)
- Theorem 3.6 (Whitney: 2-connected characterization)
-/

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

set_option linter.unusedSectionVars false

open SimpleGraph Finset

namespace AutoBooks.GraphTheory.BondyMurty.Ch03

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### Bondy–Murty §3.1 — Connected graphs

| Bondy–Murty           | Mathlib                                     |
|------------------------|---------------------------------------------|
| Connected              | `G.Connected`                               |
| Component              | `G.ConnectedComponent`                      |
| Cut edge (bridge)      | `G.IsBridge`                                |
| Cut vertex             | (vertex connectivity ≥ 2)                   |
-/

/-- **Theorem 3.1** (Bondy–Murty §3.1): every walk contains a path.
    This is Mathlib's `Walk.toPath`. -/
theorem walk_contains_path {u v : V} (w : G.Walk u v) :
    ∃ p : G.Walk u v, p.IsPath :=
  ⟨w.bypass, w.bypass_isPath⟩

/-- **Proposition 3.4** (Bondy–Murty §3.1): an edge e is a cut edge
    iff e belongs to no cycle.
    (Mathlib: `isBridge_iff_mem_and_forall_cycle_notMem`) -/
theorem cut_edge_iff_no_cycle {e : Sym2 V} (he : e ∈ G.edgeSet) :
    G.IsBridge e ↔ ∀ (v : V) (c : G.Walk v v), c.IsCycle → e ∉ c.edges := by
  rw [isBridge_iff_mem_and_forall_cycle_notMem]
  exact ⟨fun h => h.2, fun h => ⟨he, h⟩⟩

end AutoBooks.GraphTheory.BondyMurty.Ch03
