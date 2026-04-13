import FourColor.Curriculum.Actual.SupportReduction
import FourColor.Curriculum.Actual.SevenVertexSeventeenProfileThreeTwoTwo

namespace FourColor.Curriculum.Actual

section MinimalEdgeBounds

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- On seven vertices, a `K₅`-free minimal non-`4`-colorable graph has edge count in `[14,18]`
without any extra no-isolated-vertices hypothesis.

Source: the support-reduction theorem forces every vertex to have a neighbor on this frontier, so
the older minimal-to-incidence bridge applies automatically. -/
theorem IsMinimalNonColorable.edge_bounds_of_card_eq_seven_of_cliqueFree
    (h : IsMinimalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    14 ≤ G.edgeFinset.card ∧ G.edgeFinset.card ≤ 18 := by
  let hinc : IsIncidenceCriticalNonColorable G 4 :=
    h.toIncidenceCritical (h.forall_exists_adj_of_card_eq_seven_of_cliqueFree hcard hfree)
  exact
    hinc.edge_bounds_of_card_eq_seven_of_cliqueFree hcard hfree

/-- On seven vertices, a `K₅`-free minimal non-`4`-colorable graph has at least `15` edges
without any extra no-isolated-vertices hypothesis. -/
theorem IsMinimalNonColorable.card_edgeFinset_ge_fifteen_of_card_eq_seven_of_cliqueFree
    (h : IsMinimalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    15 ≤ G.edgeFinset.card := by
  let hinc : IsIncidenceCriticalNonColorable G 4 :=
    h.toIncidenceCritical (h.forall_exists_adj_of_card_eq_seven_of_cliqueFree hcard hfree)
  exact
    hinc.card_edgeFinset_ge_fifteen_of_card_eq_seven_of_cliqueFree hcard hfree

/-- On seven vertices, a `K₅`-free minimal non-`4`-colorable graph has edge count in `[15,18]`
without any extra no-isolated-vertices hypothesis. -/
theorem IsMinimalNonColorable.refined_edge_bounds_of_card_eq_seven_of_cliqueFree
    (h : IsMinimalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    15 ≤ G.edgeFinset.card ∧ G.edgeFinset.card ≤ 18 := by
  let hinc : IsIncidenceCriticalNonColorable G 4 :=
    h.toIncidenceCritical (h.forall_exists_adj_of_card_eq_seven_of_cliqueFree hcard hfree)
  exact
    hinc.refined_edge_bounds_of_card_eq_seven_of_cliqueFree hcard hfree

/-- On seven vertices, the extremal `|E| = 18` case is impossible for `K₅`-free minimal
non-`4`-colorable graphs without any extra no-isolated-vertices hypothesis. -/
theorem IsMinimalNonColorable.card_edgeFinset_ne_eighteen_of_card_eq_seven_of_cliqueFree
    (h : IsMinimalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    G.edgeFinset.card ≠ 18 := by
  let hinc : IsIncidenceCriticalNonColorable G 4 :=
    h.toIncidenceCritical (h.forall_exists_adj_of_card_eq_seven_of_cliqueFree hcard hfree)
  exact
    hinc.card_edgeFinset_ne_eighteen_of_card_eq_seven_of_cliqueFree hcard hfree

/-- On seven vertices, a `K₅`-free minimal non-`4`-colorable graph has at most `17` edges
without any extra no-isolated-vertices hypothesis. -/
theorem IsMinimalNonColorable.card_edgeFinset_le_seventeen_of_card_eq_seven_of_cliqueFree
    (h : IsMinimalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    G.edgeFinset.card ≤ 17 := by
  let hinc : IsIncidenceCriticalNonColorable G 4 :=
    h.toIncidenceCritical (h.forall_exists_adj_of_card_eq_seven_of_cliqueFree hcard hfree)
  exact
    hinc.card_edgeFinset_le_seventeen_of_card_eq_seven_of_cliqueFree hcard hfree

/-- On seven vertices, a `K₅`-free minimal non-`4`-colorable graph has edge count in `[15,17]`
without any extra no-isolated-vertices hypothesis. -/
theorem IsMinimalNonColorable.further_refined_edge_bounds_of_card_eq_seven_of_cliqueFree
    (h : IsMinimalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    15 ≤ G.edgeFinset.card ∧ G.edgeFinset.card ≤ 17 := by
  let hinc : IsIncidenceCriticalNonColorable G 4 :=
    h.toIncidenceCritical (h.forall_exists_adj_of_card_eq_seven_of_cliqueFree hcard hfree)
  exact
    hinc.further_refined_edge_bounds_of_card_eq_seven_of_cliqueFree hcard hfree

/-- On seven vertices, the `|E| = 15` case is impossible for `K₅`-free minimal non-`4`-colorable
graphs without any extra no-isolated-vertices hypothesis. -/
theorem IsMinimalNonColorable.card_edgeFinset_ne_fifteen_of_card_eq_seven_of_cliqueFree
    (h : IsMinimalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    G.edgeFinset.card ≠ 15 := by
  let hinc : IsIncidenceCriticalNonColorable G 4 :=
    h.toIncidenceCritical (h.forall_exists_adj_of_card_eq_seven_of_cliqueFree hcard hfree)
  exact
    hinc.card_edgeFinset_ne_fifteen_of_card_eq_seven hcard

/-- On seven vertices, a `K₅`-free minimal non-`4`-colorable graph has at least `16` edges
without any extra no-isolated-vertices hypothesis. -/
theorem IsMinimalNonColorable.card_edgeFinset_ge_sixteen_of_card_eq_seven_of_cliqueFree
    (h : IsMinimalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    16 ≤ G.edgeFinset.card := by
  let hinc : IsIncidenceCriticalNonColorable G 4 :=
    h.toIncidenceCritical (h.forall_exists_adj_of_card_eq_seven_of_cliqueFree hcard hfree)
  exact
    hinc.card_edgeFinset_ge_sixteen_of_card_eq_seven_of_cliqueFree hcard hfree

/-- On seven vertices, a `K₅`-free minimal non-`4`-colorable graph has edge count in `[16,17]`
without any extra no-isolated-vertices hypothesis. -/
theorem IsMinimalNonColorable.sharp_edge_bounds_of_card_eq_seven_of_cliqueFree
    (h : IsMinimalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    16 ≤ G.edgeFinset.card ∧ G.edgeFinset.card ≤ 17 := by
  let hinc : IsIncidenceCriticalNonColorable G 4 :=
    h.toIncidenceCritical (h.forall_exists_adj_of_card_eq_seven_of_cliqueFree hcard hfree)
  exact
    hinc.sharp_edge_bounds_of_card_eq_seven_of_cliqueFree hcard hfree

/-- On seven vertices, the `|E| = 17` case is impossible for `K₅`-free minimal non-`4`-colorable
graphs without any extra no-isolated-vertices hypothesis. -/
theorem IsMinimalNonColorable.card_edgeFinset_ne_seventeen_of_card_eq_seven_of_cliqueFree
    (h : IsMinimalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    G.edgeFinset.card ≠ 17 := by
  let hinc : IsIncidenceCriticalNonColorable G 4 :=
    h.toIncidenceCritical (h.forall_exists_adj_of_card_eq_seven_of_cliqueFree hcard hfree)
  exact
    hinc.card_edgeFinset_ne_seventeen_of_card_eq_seven_of_cliqueFree hcard hfree

/-- On seven vertices, a `K₅`-free minimal non-`4`-colorable graph therefore has exactly `16`
edges without any extra no-isolated-vertices hypothesis. -/
theorem IsMinimalNonColorable.card_edgeFinset_eq_sixteen_of_card_eq_seven_of_cliqueFree
    (h : IsMinimalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    G.edgeFinset.card = 16 := by
  let hinc : IsIncidenceCriticalNonColorable G 4 :=
    h.toIncidenceCritical (h.forall_exists_adj_of_card_eq_seven_of_cliqueFree hcard hfree)
  exact
    hinc.card_edgeFinset_eq_sixteen_of_card_eq_seven_of_cliqueFree hcard hfree

end MinimalEdgeBounds

end FourColor.Curriculum.Actual
