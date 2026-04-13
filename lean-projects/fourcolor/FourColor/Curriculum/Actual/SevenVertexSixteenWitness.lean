import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Sum
import FourColor.Curriculum.Actual.SevenVertexSixteenIsolatedObstruction

namespace FourColor.Curriculum.Actual

/-- The rigid seven-vertex `|E| = 16` obstruction branch as a concrete complement graph:
two isolated vertices together with a `5`-cycle.

This is the complement-side realization of the branch isolated by
`SevenVertexSixteenIsolatedSupport`. Its original graph is `K₂ ⋈ C₅`. -/
abbrev sevenVertexSixteenWitnessCompl : SimpleGraph (Fin 2 ⊕ Fin 5) :=
  (⊥ : SimpleGraph (Fin 2)) ⊕g SimpleGraph.cycleGraph 5

/-- The concrete seven-vertex obstruction candidate obtained by complementing
`2K₁ ⊔ C₅`. Equivalently, this is the join `K₂ ⋈ C₅`. -/
abbrev sevenVertexSixteenWitness : SimpleGraph (Fin 2 ⊕ Fin 5) :=
  sevenVertexSixteenWitnessComplᶜ

instance : DecidableRel sevenVertexSixteenWitnessCompl.Adj := by
  intro a b
  cases a with
  | inl a =>
      cases b with
      | inl b => exact isFalse (by simp [sevenVertexSixteenWitnessCompl])
      | inr b => exact isFalse (by simp [sevenVertexSixteenWitnessCompl])
  | inr a =>
      cases b with
      | inl b => exact isFalse (by simp [sevenVertexSixteenWitnessCompl])
      | inr b =>
          change Decidable ((SimpleGraph.cycleGraph 5).Adj a b)
          infer_instance

instance : DecidableRel sevenVertexSixteenWitness.Adj := by
  unfold sevenVertexSixteenWitness
  infer_instance

/-- The isolated complement vertices in the concrete witness have degree `0`. -/
theorem sevenVertexSixteenWitnessCompl_degree_inl (i : Fin 2) :
    sevenVertexSixteenWitnessCompl.degree (Sum.inl i) = 0 := by
  fin_cases i <;> decide

/-- The support-side complement vertices in the concrete witness have degree `2`. -/
theorem sevenVertexSixteenWitnessCompl_degree_inr (i : Fin 5) :
    sevenVertexSixteenWitnessCompl.degree (Sum.inr i) = 2 := by
  fin_cases i <;> decide

/-- The concrete witness lives on seven vertices. -/
theorem sevenVertexSixteenWitness_card :
    Fintype.card (Fin 2 ⊕ Fin 5) = 7 := by
  decide

/-- The concrete witness complement has support of cardinality `5`. -/
theorem sevenVertexSixteenWitnessCompl_card_support :
    Fintype.card sevenVertexSixteenWitnessCompl.support = 5 := by
  set_option maxRecDepth 10000 in
    decide

/-- The complement support of the concrete witness is `2`-regular. -/
theorem sevenVertexSixteenWitnessCompl_induce_support_isRegularOfDegree_two :
    (sevenVertexSixteenWitnessCompl.induce sevenVertexSixteenWitnessCompl.support).IsRegularOfDegree 2 := by
  intro x
  rcases x with ⟨x, hx⟩
  cases x with
  | inl i =>
      exfalso
      exact
        ((SimpleGraph.degree_eq_zero_iff_notMem_support
          (G := sevenVertexSixteenWitnessCompl) (v := Sum.inl i)).mp
            (sevenVertexSixteenWitnessCompl_degree_inl i)) hx
  | inr i =>
      rw [SimpleGraph.degree_induce_support]
      exact sevenVertexSixteenWitnessCompl_degree_inr i

/-- The complement of the concrete witness has `2`-regular support.

This restates `sevenVertexSixteenWitnessCompl_induce_support_isRegularOfDegree_two` with the
complement written in the form needed by the generic obstruction theorem. -/
theorem sevenVertexSixteenWitness_compl_induce_support_isRegularOfDegree_two :
    ((sevenVertexSixteenWitnessᶜ).induce (sevenVertexSixteenWitnessᶜ.support)).IsRegularOfDegree 2 := by
  intro x
  rcases x with ⟨x, hx⟩
  cases x with
  | inl i =>
      exfalso
      have hdeg0 : (sevenVertexSixteenWitnessᶜ).degree (Sum.inl i) = 0 := by
        fin_cases i <;> decide
      exact
        ((SimpleGraph.degree_eq_zero_iff_notMem_support
          (G := sevenVertexSixteenWitnessᶜ) (v := Sum.inl i)).mp hdeg0) hx
  | inr i =>
      rw [SimpleGraph.degree_induce_support]
      change (sevenVertexSixteenWitnessᶜ).degree (Sum.inr i) = 2
      fin_cases i <;> decide

/-- The concrete witness is `K₅`-free. -/
theorem sevenVertexSixteenWitness_cliqueFree_five :
    sevenVertexSixteenWitness.CliqueFree 5 := by
  set_option maxRecDepth 10000 in
    intro s
    revert s
    decide

/-- The concrete witness has exactly sixteen edges. -/
theorem sevenVertexSixteenWitness_card_edgeFinset :
    sevenVertexSixteenWitness.edgeFinset.card = 16 := by
  set_option maxRecDepth 10000 in
    decide

/-- The concrete witness is not `4`-colorable.

Source: apply the generic obstruction theorem to the explicit complement shape
`2K₁ ⊔ C₅`. -/
theorem sevenVertexSixteenWitness_not_colorable_four :
    ¬ sevenVertexSixteenWitness.Colorable 4 := by
  refine
    not_colorable_four_of_two_compl_degree_eq_zero_card_support_eq_five_and_induce_support_isRegularOfDegree_two
      (G := sevenVertexSixteenWitness) (u := Sum.inl 0) (v := Sum.inl 1) ?_ ?_ ?_ ?_ ?_
  · decide
  · simpa [sevenVertexSixteenWitness] using sevenVertexSixteenWitnessCompl_degree_inl 0
  · simpa [sevenVertexSixteenWitness] using sevenVertexSixteenWitnessCompl_degree_inl 1
  · simpa [sevenVertexSixteenWitness] using sevenVertexSixteenWitnessCompl_card_support
  · exact sevenVertexSixteenWitness_compl_induce_support_isRegularOfDegree_two

/-- There exists a seven-vertex `K₅`-free graph that is not `4`-colorable.

Together with `sevenVertexSixteenWitness_card_edgeFinset`, this witnesses that the exact
seven-vertex `|E| = 16` frontier cannot be closed by a blanket `4`-colorability statement. -/
theorem exists_seven_vertex_cliqueFree_five_not_colorable_four :
    ∃ G : SimpleGraph (Fin 2 ⊕ Fin 5),
      Fintype.card (Fin 2 ⊕ Fin 5) = 7 ∧
      G.CliqueFree 5 ∧ ¬ G.Colorable 4 := by
  refine ⟨sevenVertexSixteenWitness, ?_, ?_, ?_⟩
  · exact sevenVertexSixteenWitness_card
  · exact sevenVertexSixteenWitness_cliqueFree_five
  · exact sevenVertexSixteenWitness_not_colorable_four

end FourColor.Curriculum.Actual
