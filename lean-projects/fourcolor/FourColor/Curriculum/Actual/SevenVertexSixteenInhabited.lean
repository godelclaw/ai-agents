import Mathlib.Data.Fintype.EquivFin
import Mathlib.Combinatorics.SimpleGraph.Finite
import FourColor.Curriculum.Actual.SevenVertexSixteenCriticalWitness

namespace FourColor.Curriculum.Actual

private abbrev WitnessV := Fin 2 ⊕ Fin 5

section Transfer

variable {V : Type*} [Fintype V] [DecidableEq V]

private noncomputable def sevenVertexSixteenWitnessEquiv
    (hcard : Fintype.card V = 7) : V ≃ WitnessV :=
  Fintype.equivOfCardEq (hcard.trans sevenVertexSixteenWitness_card.symm)

/-- The explicit seven-vertex `16`-edge witness transported to an arbitrary seven-vertex type. -/
noncomputable abbrev sevenVertexSixteenWitnessOn
    (hcard : Fintype.card V = 7) : SimpleGraph V :=
  let e := sevenVertexSixteenWitnessEquiv (V := V) hcard
  sevenVertexSixteenWitness.map e.symm.toEmbedding

private noncomputable def sevenVertexSixteenWitnessOnIso
    (hcard : Fintype.card V = 7) :
    sevenVertexSixteenWitness ≃g sevenVertexSixteenWitnessOn (V := V) hcard := by
  let e := sevenVertexSixteenWitnessEquiv (V := V) hcard
  simpa [sevenVertexSixteenWitnessOn] using
    (SimpleGraph.Iso.map e.symm sevenVertexSixteenWitness)

/-- The transported witness still has exactly sixteen edges. -/
theorem sevenVertexSixteenWitnessOn_card_edgeFinset
    (hcard : Fintype.card V = 7) :
    (sevenVertexSixteenWitnessOn (V := V) hcard).edgeFinset.card = 16 := by
  let e := sevenVertexSixteenWitnessEquiv (V := V) hcard
  change (sevenVertexSixteenWitness.map e.symm.toEmbedding).edgeFinset.card = 16
  rw [SimpleGraph.edgeFinset_map, Finset.card_map]
  exact sevenVertexSixteenWitness_card_edgeFinset

/-- The transported witness remains `K₅`-free. -/
theorem sevenVertexSixteenWitnessOn_cliqueFree_five
    (hcard : Fintype.card V = 7) :
    (sevenVertexSixteenWitnessOn (V := V) hcard).CliqueFree 5 := by
  exact
    SimpleGraph.CliqueFree.comap
      ((sevenVertexSixteenWitnessOnIso (V := V) hcard).symm.toEmbedding)
      sevenVertexSixteenWitness_cliqueFree_five

/-- The transported witness remains non-`4`-colorable. -/
theorem sevenVertexSixteenWitnessOn_not_colorable_four
    (hcard : Fintype.card V = 7) :
    ¬ (sevenVertexSixteenWitnessOn (V := V) hcard).Colorable 4 := by
  intro hcol
  exact
    sevenVertexSixteenWitness_not_colorable_four
      (SimpleGraph.Colorable.of_hom
        (sevenVertexSixteenWitnessOnIso (V := V) hcard) hcol)

private noncomputable def sevenVertexSixteenWitnessOnDeletedHom
    (hcard : Fintype.card V = 7) (v : V) :
    ((sevenVertexSixteenWitnessOn (V := V) hcard).induce ({v}ᶜ)) →g
      (sevenVertexSixteenWitness.induce
        ({sevenVertexSixteenWitnessEquiv (V := V) hcard v}ᶜ)) := by
  let e := sevenVertexSixteenWitnessEquiv (V := V) hcard
  let u : WitnessV := e v
  refine
    SimpleGraph.induceHom
      ((sevenVertexSixteenWitnessOnIso (V := V) hcard).symm.toHom) ?_
  intro x hx
  change e x ∈ ({u}ᶜ : Set WitnessV)
  rw [Set.mem_compl_iff, Set.mem_singleton_iff]
  have hx' : x ≠ v := by
    simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hx
  intro hEq
  exact hx' (e.injective (by simpa [u] using hEq))

/-- Deleting any vertex from the transported witness leaves a `4`-colorable graph. -/
theorem sevenVertexSixteenWitnessOn_colorable_induce_compl_singleton
    (hcard : Fintype.card V = 7) (v : V) :
    ((sevenVertexSixteenWitnessOn (V := V) hcard).induce ({v}ᶜ)).Colorable 4 := by
  let e := sevenVertexSixteenWitnessEquiv (V := V) hcard
  let u : WitnessV := e v
  exact
    SimpleGraph.Colorable.of_hom
      (sevenVertexSixteenWitnessOnDeletedHom (V := V) hcard v)
      (sevenVertexSixteenWitness_colorable_induce_compl_singleton u)

/-- The transported witness is vertex-critical non-`4`-colorable. -/
theorem sevenVertexSixteenWitnessOn_isVertexCriticalNonColorable
    (hcard : Fintype.card V = 7) :
    IsVertexCriticalNonColorable (sevenVertexSixteenWitnessOn (V := V) hcard) 4 := by
  refine ⟨sevenVertexSixteenWitnessOn_not_colorable_four (V := V) hcard, ?_⟩
  intro v
  exact sevenVertexSixteenWitnessOn_colorable_induce_compl_singleton (V := V) hcard v

/-- The transported witness is incidence-critical non-`4`-colorable. -/
theorem sevenVertexSixteenWitnessOn_isIncidenceCriticalNonColorable
    (hcard : Fintype.card V = 7) :
    IsIncidenceCriticalNonColorable (sevenVertexSixteenWitnessOn (V := V) hcard) 4 :=
  (sevenVertexSixteenWitnessOn_isVertexCriticalNonColorable (V := V) hcard).toIncidenceCritical_four

/-- On any seven-vertex type, there exists a `16`-edge `K₅`-free graph that is vertex-critical
non-`4`-colorable. This shows the exact seven-vertex `|E| = 16` frontier is genuinely inhabited. -/
theorem exists_sixteen_edge_cliqueFree_five_vertexCritical_nonColorable_four_of_card_eq_seven
    (hcard : Fintype.card V = 7) :
    ∃ G : SimpleGraph V, ∃ _ : DecidableRel G.Adj,
      G.edgeFinset.card = 16 ∧
      G.CliqueFree 5 ∧
      IsVertexCriticalNonColorable G 4 := by
  refine ⟨sevenVertexSixteenWitnessOn (V := V) hcard, inferInstance, ?_⟩
  exact
    ⟨sevenVertexSixteenWitnessOn_card_edgeFinset (V := V) hcard,
      sevenVertexSixteenWitnessOn_cliqueFree_five (V := V) hcard,
      sevenVertexSixteenWitnessOn_isVertexCriticalNonColorable (V := V) hcard⟩

/-- On any seven-vertex type, there exists a `16`-edge `K₅`-free graph that is incidence-critical
non-`4`-colorable. This is the abstract sharpness theorem for the exact seven-vertex frontier. -/
theorem exists_sixteen_edge_cliqueFree_five_incidenceCritical_nonColorable_four_of_card_eq_seven
    (hcard : Fintype.card V = 7) :
    ∃ G : SimpleGraph V, ∃ _ : DecidableRel G.Adj,
      G.edgeFinset.card = 16 ∧
      G.CliqueFree 5 ∧
      IsIncidenceCriticalNonColorable G 4 := by
  refine ⟨sevenVertexSixteenWitnessOn (V := V) hcard, inferInstance, ?_⟩
  exact
    ⟨sevenVertexSixteenWitnessOn_card_edgeFinset (V := V) hcard,
      sevenVertexSixteenWitnessOn_cliqueFree_five (V := V) hcard,
      sevenVertexSixteenWitnessOn_isIncidenceCriticalNonColorable (V := V) hcard⟩

end Transfer

end FourColor.Curriculum.Actual
