import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoveryInjectiveConcentrationObstruction
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Tactic

namespace Mettapedia.Computability.PNP

open scoped ENNReal

local instance exactVisiblePostSwitchSurfaceBitVec1k1NonemptyActualSparseRecoveryInjectiveConcentration :
    Nonempty (ExactVisiblePostSwitchSurface (BitVec 1) 1) :=
  ⟨⟨zeroVec, zeroVec, zeroVec⟩⟩

def zeroVisiblePointActualSparseRecoveryInjectiveConcentration :
    ExactVisiblePostSwitchSurface (BitVec 1) 1 :=
  ⟨zeroVec, zeroVec, zeroVec⟩

def idBitVec1ActualSparseRecoveryInjectiveConcentration : BitVec 1 → BitVec 1 := fun x => x

noncomputable def uniformMeasureBitVec1k1ActualSparseRecoveryInjectiveConcentration :
    PMF (ExactVisiblePostSwitchSurface (BitVec 1) 1) :=
  PMF.uniformOfFintype _

def constFalseActualSwitchedLocalInterfaceBitVec1k1ActualSparseRecoveryInjectiveConcentration :
    ActualSwitchedLocalInterface
      (BitVec 1)
      1
      Unit
      (ExactVisiblePostSwitchSurface (BitVec 1) 1) where
  zOf := fun u => u.z
  aOf := fun _ u => u.a
  bOf := fun u => u.b
  localRule := fun _ _ => false
  output := fun _ _ => false
  output_eq_local := by
    intro _ _
    rfl

theorem constFalseActualSwitchedLocalInterfaceBitVec1k1ActualSparseRecoveryInjectiveConcentration_not_surjective :
    ¬ Function.Surjective
        constFalseActualSwitchedLocalInterfaceBitVec1k1ActualSparseRecoveryInjectiveConcentration.predictorFamily.predict := by
  intro hsurj
  rcases hsurj (fun _ => true) with ⟨u, htrue⟩
  cases u
  have h := congrFun htrue zeroVisiblePointActualSparseRecoveryInjectiveConcentration
  simp [constFalseActualSwitchedLocalInterfaceBitVec1k1ActualSparseRecoveryInjectiveConcentration] at h

theorem constFalseActualSwitchedLocalInterfaceBitVec1k1ActualSparseRecoveryInjectiveConcentration_one_sub_pow_inv_regression
    {q : ℝ≥0∞}
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          uniformMeasureBitVec1k1ActualSparseRecoveryInjectiveConcentration
          constFalseActualSwitchedLocalInterfaceBitVec1k1ActualSparseRecoveryInjectiveConcentration
          idBitVec1ActualSparseRecoveryInjectiveConcentration
          q)) :
    1 - (2 ^ 3 : ℝ≥0∞)⁻¹ ≤ q := by
  rcases h with ⟨h⟩
  exact
    ActualSwitchedLocalInterface.one_sub_pow_inv_le_of_injective_zfeat
      (μ := uniformMeasureBitVec1k1ActualSparseRecoveryInjectiveConcentration)
      (T := constFalseActualSwitchedLocalInterfaceBitVec1k1ActualSparseRecoveryInjectiveConcentration)
      (zfeat := idBitVec1ActualSparseRecoveryInjectiveConcentration)
      h
      (fun _ _ hxy => hxy)
      (by norm_num)
      ()

private theorem three_quarters_lt_seven_eighths_actualSparseRecoveryInjectiveConcentration :
    (3 : ℝ≥0∞) / 4 < (7 : ℝ≥0∞) / 8 := by
  have h₁ : (3 : ℝ≥0∞) / 4 = 6 / 8 := by
    refine (ENNReal.div_eq_div_iff (by norm_num) (by simp) (by norm_num) (by simp)).2 ?_
    norm_num
  rw [h₁]
  exact ENNReal.div_lt_div_right (by norm_num) (by simp) (by norm_num)

theorem constFalseActualSwitchedLocalInterfaceBitVec1k1ActualSparseRecoveryInjectiveConcentration_not_nonempty_three_quarters_regression :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          uniformMeasureBitVec1k1ActualSparseRecoveryInjectiveConcentration
          constFalseActualSwitchedLocalInterfaceBitVec1k1ActualSparseRecoveryInjectiveConcentration
          idBitVec1ActualSparseRecoveryInjectiveConcentration
          ((3 : ℝ≥0∞) / 4)) := by
  exact
    ActualSwitchedLocalInterface.not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_injective_zfeat_of_lt_one_sub_pow_inv
      (μ := uniformMeasureBitVec1k1ActualSparseRecoveryInjectiveConcentration)
      (T := constFalseActualSwitchedLocalInterfaceBitVec1k1ActualSparseRecoveryInjectiveConcentration)
      (zfeat := idBitVec1ActualSparseRecoveryInjectiveConcentration)
      (fun _ _ hxy => hxy)
      (by norm_num)
      ()
      (by
        have hthreshold : 1 - (2 ^ 3 : ℝ≥0∞)⁻¹ = (7 : ℝ≥0∞) / 8 := by
          have hsum : (1 : ℝ≥0∞) = (7 : ℝ≥0∞) / 8 + (2 ^ 3 : ℝ≥0∞)⁻¹ := by
            have hinv : ((2 ^ 3 : ℝ≥0∞)⁻¹) = (1 : ℝ≥0∞) / 8 := by
              norm_num
            calc
              (1 : ℝ≥0∞) = (8 : ℝ≥0∞) / 8 := by
                    exact (ENNReal.div_self (by norm_num) (by simp)).symm
              _ = ((7 : ℝ≥0∞) + 1) / 8 := by norm_num
              _ = (7 : ℝ≥0∞) / 8 + (1 : ℝ≥0∞) / 8 := by
                    simpa using
                      (ENNReal.div_add_div_same
                        (a := (7 : ℝ≥0∞))
                        (b := (1 : ℝ≥0∞))
                        (c := (8 : ℝ≥0∞))).symm
              _ = (7 : ℝ≥0∞) / 8 + (2 ^ 3 : ℝ≥0∞)⁻¹ := by
                    rw [hinv]
          exact ENNReal.sub_eq_of_eq_add (by simp) hsum
        rw [hthreshold]
        exact three_quarters_lt_seven_eighths_actualSparseRecoveryInjectiveConcentration)

end Mettapedia.Computability.PNP
