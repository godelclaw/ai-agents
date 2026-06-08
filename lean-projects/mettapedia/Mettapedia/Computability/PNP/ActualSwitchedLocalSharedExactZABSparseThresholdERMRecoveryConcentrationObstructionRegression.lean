import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoveryConcentrationObstruction
import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMDataRegression
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic

namespace Mettapedia.Computability.PNP

open scoped ENNReal

def bool0FalseVisiblePointActualSparseRecoveryConcentration :
    ExactVisiblePostSwitchSurface Bool 0 :=
  ⟨false, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩

def bool0TrueVisiblePointActualSparseRecoveryConcentration :
    ExactVisiblePostSwitchSurface Bool 0 :=
  ⟨true, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩

noncomputable def bool0UniformMeasureActualSparseRecoveryConcentration :
    PMF (ExactVisiblePostSwitchSurface Bool 0) :=
  PMF.ofFintype
    (fun _ => (2 : ℝ≥0∞)⁻¹)
    (by
      classical
      have hsum :
          ∑ a : ExactVisiblePostSwitchSurface Bool 0, (2 : ℝ≥0∞)⁻¹
            = ∑ b : Bool, (2 : ℝ≥0∞)⁻¹ := by
        simpa using
          (Fintype.sum_equiv exactVisiblePostSwitchSurfaceBool0EquivActualSparse
            (fun _ : ExactVisiblePostSwitchSurface Bool 0 => (2 : ℝ≥0∞)⁻¹)
            (fun _ : Bool => (2 : ℝ≥0∞)⁻¹)
            (by intro b; rfl))
      calc
        ∑ a : ExactVisiblePostSwitchSurface Bool 0, (2 : ℝ≥0∞)⁻¹
            = ∑ b : Bool, (2 : ℝ≥0∞)⁻¹ := hsum
        _ = 1 := by
          simpa [two_mul] using ENNReal.inv_two_add_inv_two)

private theorem zero_lt_inv_two_ennreal : (0 : ℝ≥0∞) < (2 : ℝ≥0∞)⁻¹ := by
  norm_num

theorem fullRuleActualSwitchedLocalInterface_sharedExactZABSparseThresholdERMRecoveryData_half_le_bool0_uniform_regression
    {q : ℝ≥0∞}
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          bool0UniformMeasureActualSparseRecoveryConcentration
          (fullRuleActualSwitchedLocalInterface Bool 0)
          boolToBitVec1ActualSparse
          q)) :
    (2 : ℝ≥0∞)⁻¹ ≤ q := by
  have hxy :
      bool0FalseVisiblePointActualSparseRecoveryConcentration ≠
        bool0TrueVisiblePointActualSparseRecoveryConcentration := by
    intro hEq
    have hz := congrArg (fun u => u.z) hEq
    simp [bool0FalseVisiblePointActualSparseRecoveryConcentration,
      bool0TrueVisiblePointActualSparseRecoveryConcentration] at hz
  rcases h with ⟨h⟩
  exact
    h.half_le_of_surjective_predict_of_exists_ne
      (fullRuleActualSwitchedLocalInterface_surjective Bool 0)
      hxy

theorem fullRuleActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_bool0_uniform_zero_regression :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          bool0UniformMeasureActualSparseRecoveryConcentration
          (fullRuleActualSwitchedLocalInterface Bool 0)
          boolToBitVec1ActualSparse
          0) := by
  have hxy :
      bool0FalseVisiblePointActualSparseRecoveryConcentration ≠
        bool0TrueVisiblePointActualSparseRecoveryConcentration := by
    intro hEq
    have hz := congrArg (fun u => u.z) hEq
    simp [bool0FalseVisiblePointActualSparseRecoveryConcentration,
      bool0TrueVisiblePointActualSparseRecoveryConcentration] at hz
  exact
    ActualSwitchedLocalInterface.fullRuleActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_lt_half_of_exists_ne
      (μ := bool0UniformMeasureActualSparseRecoveryConcentration)
      (x := bool0FalseVisiblePointActualSparseRecoveryConcentration)
      (y := bool0TrueVisiblePointActualSparseRecoveryConcentration)
      (zfeat := boolToBitVec1ActualSparse)
      hxy
      zero_lt_inv_two_ennreal

theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_bool0_uniform_zero_regression :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          bool0UniformMeasureActualSparseRecoveryConcentration
          (boundedSamplePluginMajorityActualSwitchedLocalInterface Bool 0 2)
          boolToBitVec1ActualSparse
          0) := by
  have hxy :
      bool0FalseVisiblePointActualSparseRecoveryConcentration ≠
        bool0TrueVisiblePointActualSparseRecoveryConcentration := by
    intro hEq
    have hz := congrArg (fun u => u.z) hEq
    simp [bool0FalseVisiblePointActualSparseRecoveryConcentration,
      bool0TrueVisiblePointActualSparseRecoveryConcentration] at hz
  exact
    ActualSwitchedLocalInterface.boundedSamplePluginMajorityActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_lt_half_of_exists_ne
      (μ := bool0UniformMeasureActualSparseRecoveryConcentration)
      (k := 0)
      (r := 1)
      (sampleBound := 2)
      (x := bool0FalseVisiblePointActualSparseRecoveryConcentration)
      (y := bool0TrueVisiblePointActualSparseRecoveryConcentration)
      (zfeat := boolToBitVec1ActualSparse)
      (by
        simp [card_exactVisiblePostSwitchSurface_bool0_actualSparse])
      hxy
      zero_lt_inv_two_ennreal

end Mettapedia.Computability.PNP
