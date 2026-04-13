import Mathlib.Combinatorics.SimpleGraph.Coloring
import FourColor.Curriculum.Actual.SevenVertexSixteenWitness
import FourColor.Curriculum.Actual.VertexCritical

namespace FourColor.Curriculum.Actual

private abbrev WitnessV := Fin 2 ⊕ Fin 5

/-- A concrete `3`-coloring of the five-cycle side of `K₂ ⋈ C₅` after one apex is deleted. -/
private def witnessCycleColor : Fin 5 → Fin 4
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 1
  | 4 => 2

/-- Coloring used when deleting one apex from the seven-vertex `K₂ ⋈ C₅` witness:
the remaining apex gets color `3`, and the `C₅` side gets the fixed `3`-coloring
`0,0,1,1,2`. -/
private def witnessColorDeleteApex
    (i : Fin 2) : ({Sum.inl i}ᶜ : Set WitnessV) → Fin 4 := fun x =>
  match x.1 with
  | Sum.inl _ => 3
  | Sum.inr j => witnessCycleColor j

/-- Deleting either apex from `K₂ ⋈ C₅` leaves a `4`-colorable graph. -/
theorem sevenVertexSixteenWitness_colorable_induce_compl_inl
    (i : Fin 2) :
    (sevenVertexSixteenWitness.induce ({Sum.inl i}ᶜ)).Colorable 4 := by
  refine ⟨SimpleGraph.Coloring.mk (witnessColorDeleteApex i) ?_⟩
  intro x y hxy
  fin_cases i
  · revert x y hxy
    decide
  · revert x y hxy
    decide

/-- A concrete `2`-coloring of the remaining path on the five-cycle side after deleting one
cycle vertex from `K₂ ⋈ C₅`.

Rows index the deleted cycle vertex, columns index the remaining cycle vertex. -/
private def witnessCyclePathColor : Fin 5 → Fin 5 → Fin 4
  | 0, 0 => 0
  | 0, 1 => 0
  | 0, 2 => 0
  | 0, 3 => 1
  | 0, 4 => 1
  | 1, 0 => 1
  | 1, 1 => 0
  | 1, 2 => 0
  | 1, 3 => 0
  | 1, 4 => 1
  | 2, 0 => 1
  | 2, 1 => 1
  | 2, 2 => 0
  | 2, 3 => 0
  | 2, 4 => 0
  | 3, 0 => 0
  | 3, 1 => 1
  | 3, 2 => 1
  | 3, 3 => 0
  | 3, 4 => 0
  | 4, 0 => 0
  | 4, 1 => 0
  | 4, 2 => 1
  | 4, 3 => 1
  | 4, 4 => 0

/-- Coloring used when deleting one cycle vertex from the seven-vertex `K₂ ⋈ C₅` witness:
the two apex vertices get colors `2` and `3`, and the remaining cycle-side path gets a
case-split `2`-coloring. -/
private def witnessColorDeleteCycle
    (j : Fin 5) : ({Sum.inr j}ᶜ : Set WitnessV) → Fin 4 := fun x =>
  match x.1 with
  | Sum.inl 0 => 2
  | Sum.inl 1 => 3
  | Sum.inr k => witnessCyclePathColor j k

/-- Deleting any cycle vertex from `K₂ ⋈ C₅` leaves a `4`-colorable graph. -/
theorem sevenVertexSixteenWitness_colorable_induce_compl_inr
    (j : Fin 5) :
    (sevenVertexSixteenWitness.induce ({Sum.inr j}ᶜ)).Colorable 4 := by
  refine ⟨SimpleGraph.Coloring.mk (witnessColorDeleteCycle j) ?_⟩
  intro x y hxy
  fin_cases j
  · revert x y hxy
    decide
  · revert x y hxy
    decide
  · revert x y hxy
    decide
  · revert x y hxy
    decide
  · revert x y hxy
    decide

/-- Deleting any vertex from the seven-vertex witness leaves a `4`-colorable induced graph. -/
theorem sevenVertexSixteenWitness_colorable_induce_compl_singleton
    (v : WitnessV) :
    (sevenVertexSixteenWitness.induce ({v}ᶜ)).Colorable 4 := by
  cases v with
  | inl i =>
      simpa using sevenVertexSixteenWitness_colorable_induce_compl_inl i
  | inr j =>
      simpa using sevenVertexSixteenWitness_colorable_induce_compl_inr j

/-- The explicit seven-vertex witness `K₂ ⋈ C₅` is vertex-critical non-`4`-colorable. -/
theorem sevenVertexSixteenWitness_isVertexCriticalNonColorable :
    IsVertexCriticalNonColorable sevenVertexSixteenWitness 4 := by
  refine ⟨sevenVertexSixteenWitness_not_colorable_four, ?_⟩
  intro v
  exact sevenVertexSixteenWitness_colorable_induce_compl_singleton v

/-- The explicit seven-vertex witness `K₂ ⋈ C₅` is incidence-critical non-`4`-colorable. -/
theorem sevenVertexSixteenWitness_isIncidenceCriticalNonColorable :
    IsIncidenceCriticalNonColorable sevenVertexSixteenWitness 4 :=
  sevenVertexSixteenWitness_isVertexCriticalNonColorable.toIncidenceCritical_four

/-- The explicit witness packages the exact seven-vertex `16`-edge frontier data together with
vertex-critical non-`4`-colorability. -/
theorem sevenVertexSixteenWitness_vertexCritical_package :
    Fintype.card WitnessV = 7 ∧
      sevenVertexSixteenWitness.edgeFinset.card = 16 ∧
      sevenVertexSixteenWitness.CliqueFree 5 ∧
      IsVertexCriticalNonColorable sevenVertexSixteenWitness 4 := by
  exact ⟨sevenVertexSixteenWitness_card, sevenVertexSixteenWitness_card_edgeFinset,
    sevenVertexSixteenWitness_cliqueFree_five,
    sevenVertexSixteenWitness_isVertexCriticalNonColorable⟩

/-- The explicit witness packages the exact seven-vertex `16`-edge frontier data together with
incidence-critical non-`4`-colorability. -/
theorem sevenVertexSixteenWitness_incidenceCritical_package :
    Fintype.card WitnessV = 7 ∧
      sevenVertexSixteenWitness.edgeFinset.card = 16 ∧
      sevenVertexSixteenWitness.CliqueFree 5 ∧
      IsIncidenceCriticalNonColorable sevenVertexSixteenWitness 4 := by
  exact ⟨sevenVertexSixteenWitness_card, sevenVertexSixteenWitness_card_edgeFinset,
    sevenVertexSixteenWitness_cliqueFree_five,
    sevenVertexSixteenWitness_isIncidenceCriticalNonColorable⟩

/-- There exists a seven-vertex `16`-edge `K₅`-free graph that is vertex-critical
non-`4`-colorable. -/
theorem exists_seven_vertex_sixteen_edge_cliqueFree_five_vertexCritical_nonColorable_four :
    ∃ G : SimpleGraph WitnessV,
      ∃ _ : Fintype ↑G.edgeSet,
      ∃ _ : DecidableRel G.Adj,
      Fintype.card WitnessV = 7 ∧
      G.edgeFinset.card = 16 ∧
      G.CliqueFree 5 ∧
      IsVertexCriticalNonColorable G 4 := by
  exact ⟨sevenVertexSixteenWitness, inferInstance, inferInstance,
    sevenVertexSixteenWitness_card, sevenVertexSixteenWitness_card_edgeFinset,
    sevenVertexSixteenWitness_cliqueFree_five,
    sevenVertexSixteenWitness_isVertexCriticalNonColorable⟩

/-- There exists a seven-vertex `16`-edge `K₅`-free graph that is incidence-critical
non-`4`-colorable. -/
theorem exists_seven_vertex_sixteen_edge_cliqueFree_five_incidenceCritical_nonColorable_four :
    ∃ G : SimpleGraph WitnessV,
      ∃ _ : Fintype ↑G.edgeSet,
      ∃ _ : DecidableRel G.Adj,
      Fintype.card WitnessV = 7 ∧
      G.edgeFinset.card = 16 ∧
      G.CliqueFree 5 ∧
      IsIncidenceCriticalNonColorable G 4 := by
  exact ⟨sevenVertexSixteenWitness, inferInstance, inferInstance,
    sevenVertexSixteenWitness_card, sevenVertexSixteenWitness_card_edgeFinset,
    sevenVertexSixteenWitness_cliqueFree_five,
    sevenVertexSixteenWitness_isIncidenceCriticalNonColorable⟩

end FourColor.Curriculum.Actual
