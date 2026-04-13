import Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import FourColor.Curriculum.Actual.SevenVertexRefinedBounds

namespace FourColor.Curriculum.Actual

section IncidenceBranch

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The extremal seven-vertex `K₅`-free case `|E| = 18` is impossible for incidence-critical
non-`4`-colorable graphs.

Source: Turán maximality turns equality at the seven-vertex `K₅`-free edge bound into complete
multipartite structure, hence an explicit `4`-coloring contradiction. -/
theorem IsIncidenceCriticalNonColorable.card_edgeFinset_ne_eighteen_of_card_eq_seven_of_cliqueFree
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    G.edgeFinset.card ≠ 18 := by
  intro hedge
  have hmax : G.IsTuranMaximal 4 := by
    refine ⟨hfree, ?_⟩
    intro H _ hH
    simpa [hedge] using
      (card_edgeFinset_le_eighteen_of_card_eq_seven_of_cliqueFree (G := H) hcard hH)
  have hcmp : G.IsCompleteMultipartite := by
    intro a b c hab hbc
    exact hmax.not_adj_trans hab hbc
  have hcol : G.Colorable 4 := by
    simpa using hcmp.colorable_of_cliqueFree hfree
  exact h.not_colorable hcol

/-- On seven vertices, a `K₅`-free incidence-critical non-`4`-colorable graph has at most `17`
edges.

Source: the previous refined window `[15, 18]` together with the new exclusion of the extremal
`|E| = 18` case. -/
theorem IsIncidenceCriticalNonColorable.card_edgeFinset_le_seventeen_of_card_eq_seven_of_cliqueFree
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    G.edgeFinset.card ≤ 17 := by
  have hle18 := (h.refined_edge_bounds_of_card_eq_seven_of_cliqueFree hcard hfree).2
  by_contra hgt17
  have hge18 : 18 ≤ G.edgeFinset.card :=
    Nat.succ_le_of_lt (Nat.lt_of_not_ge hgt17)
  have hedge : G.edgeFinset.card = 18 := le_antisymm hle18 hge18
  exact h.card_edgeFinset_ne_eighteen_of_card_eq_seven_of_cliqueFree hcard hfree hedge

/-- On seven vertices, a `K₅`-free incidence-critical non-`4`-colorable graph has edge count in
the sharpened interval `[15, 17]`.

Source: the previous refined lower bound plus the new extremal-endpoint exclusion. -/
theorem IsIncidenceCriticalNonColorable.further_refined_edge_bounds_of_card_eq_seven_of_cliqueFree
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    15 ≤ G.edgeFinset.card ∧ G.edgeFinset.card ≤ 17 := by
  exact ⟨
    (h.refined_edge_bounds_of_card_eq_seven_of_cliqueFree hcard hfree).1,
    h.card_edgeFinset_le_seventeen_of_card_eq_seven_of_cliqueFree hcard hfree
  ⟩

end IncidenceBranch

section VertexBranch

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Vertex-critical lift of the seven-vertex `|E| = 18` exclusion. -/
theorem IsVertexCriticalNonColorable.card_edgeFinset_ne_eighteen_of_card_eq_seven_of_cliqueFree
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    G.edgeFinset.card ≠ 18 :=
  h.toIncidenceCritical_four.card_edgeFinset_ne_eighteen_of_card_eq_seven_of_cliqueFree
    hcard hfree

/-- Vertex-critical lift of the sharpened seven-vertex upper bound `|E| ≤ 17`. -/
theorem IsVertexCriticalNonColorable.card_edgeFinset_le_seventeen_of_card_eq_seven_of_cliqueFree
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    G.edgeFinset.card ≤ 17 :=
  h.toIncidenceCritical_four.card_edgeFinset_le_seventeen_of_card_eq_seven_of_cliqueFree
    hcard hfree

/-- Vertex-critical lift of the sharpened seven-vertex edge window `[15, 17]`. -/
theorem IsVertexCriticalNonColorable.further_refined_edge_bounds_of_card_eq_seven_of_cliqueFree
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    15 ≤ G.edgeFinset.card ∧ G.edgeFinset.card ≤ 17 :=
  h.toIncidenceCritical_four.further_refined_edge_bounds_of_card_eq_seven_of_cliqueFree
    hcard hfree

end VertexBranch

section MinimalBranch

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Minimal-counterexample lift of the seven-vertex `|E| = 18` exclusion. -/
theorem IsMinimalNonColorable.card_edgeFinset_ne_eighteen_of_card_eq_seven_of_cliqueFree_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    G.edgeFinset.card ≠ 18 :=
  (h.toIncidenceCritical hadj).card_edgeFinset_ne_eighteen_of_card_eq_seven_of_cliqueFree
    hcard hfree

/-- Minimal-counterexample lift of the sharpened seven-vertex upper bound `|E| ≤ 17`. -/
theorem IsMinimalNonColorable.card_edgeFinset_le_seventeen_of_card_eq_seven_of_cliqueFree_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    G.edgeFinset.card ≤ 17 :=
  (h.toIncidenceCritical hadj).card_edgeFinset_le_seventeen_of_card_eq_seven_of_cliqueFree
    hcard hfree

/-- Minimal-counterexample lift of the sharpened seven-vertex edge window `[15, 17]`. -/
theorem IsMinimalNonColorable.further_refined_edge_bounds_of_card_eq_seven_of_cliqueFree_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    15 ≤ G.edgeFinset.card ∧ G.edgeFinset.card ≤ 17 :=
  (h.toIncidenceCritical hadj).further_refined_edge_bounds_of_card_eq_seven_of_cliqueFree
    hcard hfree

end MinimalBranch

end FourColor.Curriculum.Actual
