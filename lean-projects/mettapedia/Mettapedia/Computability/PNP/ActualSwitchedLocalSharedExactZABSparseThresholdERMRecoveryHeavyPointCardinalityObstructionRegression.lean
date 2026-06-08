import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoveryHeavyPointCardinalityObstruction
import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoveryPayloadObstructionRegression
import Mathlib.Tactic

namespace Mettapedia.Computability.PNP

open scoped ENNReal

/-- The theorem-shape canary: on the pure-measure three-point surface, any
hypothetical sparse-threshold recovery packet for the genuinely non-surjective
`Fin 5` family would already force that injective family to have at most two
predictors. -/
theorem fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayload_card_le_two_of_nonempty_recovery_regression
    {q : ℝ≥0∞}
    (hmass : q < fin3PureMeasureActualSparseRecoveryPayload fin3ZeroVisiblePointActualSparseRecoveryPayload)
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          fin3PureMeasureActualSparseRecoveryPayload
          fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayload
          fin3ToBitVec0ActualSparseRecoveryPayload
          q)) :
    Fintype.card (Fin 5) ≤ 2 := by
  rcases h with ⟨h⟩
  exact
    h.card_le_two_of_injective_predict_of_lt_apply
      hmass
      fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayload_injective_predict

private theorem three_quarters_lt_one_actualSparseRecoveryHeavyPointCardinality :
    (3 : ℝ≥0∞) / 4 < 1 := by
  have h₁ : (1 : ℝ≥0∞) = (4 : ℝ≥0∞) / 4 := by
    rw [ENNReal.div_self (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by simp)]
  rw [h₁]
  exact ENNReal.div_lt_div_right (by norm_num) (by simp) (by norm_num)

private theorem three_quarters_lt_pure_mass_zero_actualSparseRecoveryHeavyPointCardinality :
    (3 : ℝ≥0∞) / 4 <
      fin3PureMeasureActualSparseRecoveryPayload fin3ZeroVisiblePointActualSparseRecoveryPayload := by
  simpa [fin3PureMeasureActualSparseRecoveryPayload] using
    three_quarters_lt_one_actualSparseRecoveryHeavyPointCardinality

private theorem two_lt_card_fin5_actualSparseRecoveryHeavyPointCardinality :
    2 < Fintype.card (Fin 5) := by
  norm_num

/-- Distinct-axis negative canary: on the pure atom at the zero visible point,
any recovery threshold below `1` collapses an injective actual family to at most
two predictors, so the genuinely non-surjective `Fin 5` family is impossible at
`q = 3/4`. -/
theorem fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayload_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_heavyPointCardinality_regression :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          fin3PureMeasureActualSparseRecoveryPayload
          fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayload
          fin3ToBitVec0ActualSparseRecoveryPayload
          ((3 : ℝ≥0∞) / 4)) := by
  exact
    ActualSwitchedLocalInterface.not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_two_lt_card_of_injective_predict_of_lt_apply
      (μ := fin3PureMeasureActualSparseRecoveryPayload)
      (T := fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayload)
      (r := 0)
      (Index := Fin 5)
      (zfeat := fin3ToBitVec0ActualSparseRecoveryPayload)
      fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayload_injective_predict
      three_quarters_lt_pure_mass_zero_actualSparseRecoveryHeavyPointCardinality
      two_lt_card_fin5_actualSparseRecoveryHeavyPointCardinality

end Mettapedia.Computability.PNP
