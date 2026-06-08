import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mettapedia.GraphTheory.FourColor.Theorem49CertificateBuilder

namespace Mettapedia.GraphTheory.FourColor

namespace Theorem49ForestRegression

open SimpleGraph

/-- The path graph on four vertices embeds as a spanning-tree candidate inside the 4-cycle. -/
example : pathGraph 4 ≤ cycleGraph 4 := pathGraph_le_cycleGraph

example : (pathGraph 4).Adj (0 : Fin 4) 1 := by
  simp [pathGraph_adj]

example : ¬ (pathGraph 4).Adj (0 : Fin 4) 2 := by
  simp [pathGraph_adj]

example : ¬ (pathGraph 4).Adj (0 : Fin 4) 3 := by
  simp [pathGraph_adj]

example : (cycleGraph 4).Adj (0 : Fin 4) 3 := by
  rw [cycleGraph_adj']
  decide

/-- This is the graph-theoretic obstruction behind the manuscript's naive Step 2 leaf heuristic:
a leaf of a chosen spanning-tree/path subgraph need not be a leaf of the ambient dual graph. In
the 4-cycle, vertex `0` has a unique incident tree edge in `pathGraph 4` (to `1`) but still has an
extra ambient dual adjacency to `3` in `cycleGraph 4`. So “leaf in a spanning forest” is not
enough by itself to justify that all other incident dual edges already lie in the removed subtree.

The live Lean route does not rely on this false implication. It instead uses the stronger
`InteriorDualBoundaryRootAdjDistancePeelData` interface, which tracks adjacent peeled child faces
with strictly larger root distance and canonically recovers the parent/height/well-founded peeling
packages consumed downstream. -/
example :
    (pathGraph 4).Adj (0 : Fin 4) 1 ∧
      ¬ (pathGraph 4).Adj (0 : Fin 4) 2 ∧
      ¬ (pathGraph 4).Adj (0 : Fin 4) 3 ∧
      (cycleGraph 4).Adj (0 : Fin 4) 3 := by
  constructor
  · simp [pathGraph_adj]
  · constructor
    · simp [pathGraph_adj]
    · constructor
      · simp [pathGraph_adj]
      · rw [cycleGraph_adj']
        decide

def twoCycleParent : Fin 2 → Option (Fin 2)
  | 0 => some 1
  | _ => some 0

example : twoCycleParent 0 = some 1 := by
  simp [twoCycleParent]

example : twoCycleParent 1 = some 0 := by
  simp [twoCycleParent]

private theorem topFinTwo_isTree : (⊤ : SimpleGraph (Fin 2)).IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  constructor
  · exact (SimpleGraph.connected_top : (⊤ : SimpleGraph (Fin 2)).Connected)
  · rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card,
      SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
    norm_num

example : (⊤ : SimpleGraph (Fin 2)).IsAcyclic := by
  exact topFinTwo_isTree.IsAcyclic

example : ∀ {f p : Fin 2}, twoCycleParent f = some p → (⊤ : SimpleGraph (Fin 2)).Adj f p := by
  intro f p hfp
  fin_cases f <;> fin_cases p <;> simp [twoCycleParent] at hfp ⊢

/-- This is the soundness obstruction behind the naive “acyclic forest plus parent-edge adjacency
implies well-founded parent peeling” idea. Even on the two-vertex tree, a parent map can point the
two endpoints at each other; every parent edge lies in the forest, but the induced parent relation
has a 2-cycle and is therefore not well founded. Any correct reduction to well-founded peeling
needs an extra descending invariant, such as root-distance or an explicit height. -/
example :
    (⊤ : SimpleGraph (Fin 2)).IsAcyclic ∧
      (∀ {f p : Fin 2}, twoCycleParent f = some p → (⊤ : SimpleGraph (Fin 2)).Adj f p) ∧
      ¬ WellFounded (ParentRel twoCycleParent) := by
  refine ⟨topFinTwo_isTree.IsAcyclic, ?_, ?_⟩
  · intro f p hfp
    fin_cases f <;> fin_cases p <;> simp [twoCycleParent] at hfp ⊢
  · exact not_wellFounded_parentRel_of_twoCycle (parentFace := twoCycleParent)
      (f := 0) (g := 1)
      (by simp [twoCycleParent]) (by simp [twoCycleParent])

end Theorem49ForestRegression

end Mettapedia.GraphTheory.FourColor
