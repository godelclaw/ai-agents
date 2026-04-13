import FourColor.Curriculum.Actual.CriticalIso
import FourColor.Curriculum.Actual.SupportReduction
import FourColor.Curriculum.Actual.SevenVertexSixteenCriticalWitness
import FourColor.Curriculum.Actual.SevenVertexMinimalEdgeBounds
import FourColor.Curriculum.Actual.SevenVertexSixteenMinimalWitness
import FourColor.Curriculum.Actual.SevenVertexSixteenWitnessIso

namespace FourColor.Curriculum.Actual

section IncidenceCharacterization

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- On seven vertices, the `K₅`-free incidence-critical non-`4`-colorable frontier is exactly the
canonical witness `K₂ ⋈ C₅` up to isomorphism, and therefore has exactly `16` edges.

Source: combines the exact seven-vertex edge bound with the new witness realization and the
isomorphism-invariance layer for incidence-criticality. -/
theorem cliqueFree_incidenceCritical_iff_card_edgeFinset_eq_sixteen_and_nonempty_iso_sevenVertexSixteenWitness_of_card_eq_seven
    (hcard : Fintype.card V = 7) :
    (G.CliqueFree 5 ∧ IsIncidenceCriticalNonColorable G 4) ↔
      (G.edgeFinset.card = 16 ∧ Nonempty (sevenVertexSixteenWitness ≃g G)) := by
  constructor
  · rintro ⟨hfree, hcrit⟩
    refine ⟨hcrit.card_edgeFinset_eq_sixteen_of_card_eq_seven_of_cliqueFree hcard hfree, ?_⟩
    exact hcrit.nonempty_iso_sevenVertexSixteenWitness_of_card_eq_seven_of_cliqueFree hcard hfree
  · rintro ⟨_, ⟨φ⟩⟩
    refine ⟨?_, ?_⟩
    · exact
        (SimpleGraph.Iso.cliqueFree_iff (f := φ) (n := 5)).1
          sevenVertexSixteenWitness_cliqueFree_five
    · exact
        (SimpleGraph.Iso.isIncidenceCriticalNonColorable_iff (f := φ) (n := 4)).1
          sevenVertexSixteenWitness_isIncidenceCriticalNonColorable

end IncidenceCharacterization

section VertexCharacterization

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- On seven vertices, the `K₅`-free vertex-critical non-`4`-colorable frontier is exactly the
canonical witness `K₂ ⋈ C₅` up to isomorphism, and therefore has exactly `16` edges.

Source: combines the exact seven-vertex edge bound with the new witness realization and the
isomorphism-invariance layer for vertex-criticality. -/
theorem cliqueFree_vertexCritical_iff_card_edgeFinset_eq_sixteen_and_nonempty_iso_sevenVertexSixteenWitness_of_card_eq_seven
    (hcard : Fintype.card V = 7) :
    (G.CliqueFree 5 ∧ IsVertexCriticalNonColorable G 4) ↔
      (G.edgeFinset.card = 16 ∧ Nonempty (sevenVertexSixteenWitness ≃g G)) := by
  constructor
  · rintro ⟨hfree, hcrit⟩
    refine ⟨hcrit.card_edgeFinset_eq_sixteen_of_card_eq_seven_of_cliqueFree hcard hfree, ?_⟩
    exact hcrit.nonempty_iso_sevenVertexSixteenWitness_of_card_eq_seven_of_cliqueFree hcard hfree
  · rintro ⟨_, ⟨φ⟩⟩
    refine ⟨?_, ?_⟩
    · exact
        (SimpleGraph.Iso.cliqueFree_iff (f := φ) (n := 5)).1
          sevenVertexSixteenWitness_cliqueFree_five
    · exact
        (SimpleGraph.Iso.isVertexCriticalNonColorable_iff (f := φ) (n := 4)).1
          sevenVertexSixteenWitness_isVertexCriticalNonColorable

end VertexCharacterization

section MinimalCharacterization

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- On seven vertices, the `K₅`-free minimal non-`4`-colorable frontier with the usual
no-isolated-vertices hypothesis is exactly the canonical witness `K₂ ⋈ C₅` up to isomorphism, and
therefore has exactly `16` edges.

Source: combines the exact seven-vertex edge bound with the witness realization and the new
isomorphism-invariance layer for minimal non-colorability. -/
theorem cliqueFree_minimal_with_forall_exists_adj_iff_card_edgeFinset_eq_sixteen_and_nonempty_iso_sevenVertexSixteenWitness_of_card_eq_seven
    (hcard : Fintype.card V = 7) :
    (G.CliqueFree 5 ∧ IsMinimalNonColorable G 4 ∧ (∀ v : V, ∃ w, G.Adj v w)) ↔
      (G.edgeFinset.card = 16 ∧ Nonempty (sevenVertexSixteenWitness ≃g G)) := by
  constructor
  · rintro ⟨hfree, hmin, _hadj⟩
    refine
      ⟨hmin.card_edgeFinset_eq_sixteen_of_card_eq_seven_of_cliqueFree hcard hfree, ?_⟩
    exact
      hmin.nonempty_iso_sevenVertexSixteenWitness_of_card_eq_seven_of_cliqueFree hcard hfree
  · rintro ⟨_, ⟨φ⟩⟩
    refine ⟨?_, ?_, ?_⟩
    · exact
        (SimpleGraph.Iso.cliqueFree_iff (f := φ) (n := 5)).1
          sevenVertexSixteenWitness_cliqueFree_five
    · exact
        (SimpleGraph.Iso.isMinimalNonColorable_iff (f := φ) (n := 4)).1
          sevenVertexSixteenWitness_isMinimalNonColorable
    · have hvc :
          IsVertexCriticalNonColorable G 4 := by
        exact
          (SimpleGraph.Iso.isVertexCriticalNonColorable_iff (f := φ) (n := 4)).1
            sevenVertexSixteenWitness_isVertexCriticalNonColorable
      intro v
      exact hvc.exists_adj v

/-- On seven vertices, the `K₅`-free minimal non-`4`-colorable frontier is exactly the canonical
witness `K₂ ⋈ C₅` up to isomorphism, and therefore has exactly `16` edges.

Source: the support-reduction theorem eliminates isolated vertices on this frontier, so the older
no-isolated-vertices characterization now applies without an extra hypothesis. -/
theorem cliqueFree_minimal_iff_card_edgeFinset_eq_sixteen_and_nonempty_iso_sevenVertexSixteenWitness_of_card_eq_seven
    (hcard : Fintype.card V = 7) :
    (G.CliqueFree 5 ∧ IsMinimalNonColorable G 4) ↔
      (G.edgeFinset.card = 16 ∧ Nonempty (sevenVertexSixteenWitness ≃g G)) := by
  constructor
  · rintro ⟨hfree, hmin⟩
    have hadj : ∀ v : V, ∃ w, G.Adj v w :=
      hmin.forall_exists_adj_of_card_eq_seven_of_cliqueFree hcard hfree
    exact
      (cliqueFree_minimal_with_forall_exists_adj_iff_card_edgeFinset_eq_sixteen_and_nonempty_iso_sevenVertexSixteenWitness_of_card_eq_seven
        (G := G) hcard).1 ⟨hfree, hmin, hadj⟩
  · rintro hchar
    rcases
        (cliqueFree_minimal_with_forall_exists_adj_iff_card_edgeFinset_eq_sixteen_and_nonempty_iso_sevenVertexSixteenWitness_of_card_eq_seven
          (G := G) hcard).2 hchar with
      ⟨hfree, hmin, _⟩
    exact ⟨hfree, hmin⟩

end MinimalCharacterization

end FourColor.Curriculum.Actual
