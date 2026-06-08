import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoveryPairwiseAgreementObstruction
import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoveryPayloadObstructionRegression
import Mathlib.Tactic

namespace Mettapedia.Computability.PNP

open scoped ENNReal

theorem fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayload_predict_zero_ne_predict_two :
    fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayload.predictorFamily.predict 0 ≠
      fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayload.predictorFamily.predict 2 := by
  intro h
  have hinj :=
    fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayload_injective_predict
  have h02 : (0 : Fin 5) ≠ 2 := by decide
  exact h02 (hinj h)

/-- The theorem-shape canary: any hypothetical recovery packet on the
non-surjective `Fin 5` family would already force the two distinct realized
predictors at indices `0` and `2` to have agreement mass at most `q`. -/
theorem fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayload_agreementMass_le_of_nonempty_recovery_regression (q : ℝ≥0∞)
    (h : Nonempty
      (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
        fin3PureMeasureActualSparseRecoveryPayload
        fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayload
        fin3ToBitVec0ActualSparseRecoveryPayload
        q)) :
    agreementMass
        fin3PureMeasureActualSparseRecoveryPayload
        (fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayload.predictorFamily.predict 0)
        (fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayload.predictorFamily.predict 2)
      ≤ q := by
  rcases h with ⟨h⟩
  exact
    h.agreementMass_le_of_predict_ne
      (0 : Fin 5) (2 : Fin 5)
      fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayload_predict_zero_ne_predict_two.symm

theorem fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayload_agreementMass_predict_zero_predict_two_eq_one :
    agreementMass
        fin3PureMeasureActualSparseRecoveryPayload
        (fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayload.predictorFamily.predict 0)
        (fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayload.predictorFamily.predict 2)
      = 1 := by
  apply agreementMass_pure_eq_one_of_agrees
  simp [fin3ZeroVisiblePointActualSparseRecoveryPayload,
    fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayload,
    fin5ProbeFamilyActualSparseRecoveryPayload]

private noncomputable def fin5ProbeActualSparseRecoveryPayloadThreeQuarters : ℝ≥0∞ :=
  (3 : ℝ≥0∞) / 4

private theorem fin5ProbeActualSparseRecoveryPayloadThreeQuarters_lt_one :
    fin5ProbeActualSparseRecoveryPayloadThreeQuarters < 1 := by
  have h₁ : fin5ProbeActualSparseRecoveryPayloadThreeQuarters = (3 : ℝ≥0∞) / 4 := by
    rfl
  have h₂ : (1 : ℝ≥0∞) = (4 : ℝ≥0∞) / 4 := by
    rw [ENNReal.div_self (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by simp)]
  rw [h₁, h₂]
  exact ENNReal.div_lt_div_right (by norm_num) (by simp) (by norm_num)

/-- Distinct-axis negative canary: the same genuinely non-surjective `Fin 5`
family is blocked for `q = 3/4` because its distinct realized predictors at
indices `0` and `2` already agree on full `μ`-mass. -/
theorem fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayload_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_pairwise_regression :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          fin3PureMeasureActualSparseRecoveryPayload
          fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayload
          fin3ToBitVec0ActualSparseRecoveryPayload
          fin5ProbeActualSparseRecoveryPayloadThreeQuarters) := by
  exact
    ActualSwitchedLocalInterface.not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_lt_agreementMass_of_predict_ne
      (μ := fin3PureMeasureActualSparseRecoveryPayload)
      (T := fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayload)
      (r := 0)
      (zfeat := fin3ToBitVec0ActualSparseRecoveryPayload)
      (q := fin5ProbeActualSparseRecoveryPayloadThreeQuarters)
      0
      2
      fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayload_predict_zero_ne_predict_two.symm
      (by
        rw [fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayload_agreementMass_predict_zero_predict_two_eq_one]
        exact fin5ProbeActualSparseRecoveryPayloadThreeQuarters_lt_one)

end Mettapedia.Computability.PNP
