import Mettapedia.Computability.PNP.BitFamilyUniformRecoveryBinary

/-!
# Regression checks for binary-input bit-family recovery

These wrappers pin the `s < m` specialization of the finite bit-budget recovery
threshold on two-point input domains.
-/

namespace Mettapedia.Computability.PNP.BitFamilyUniformRecoveryBinaryRegression

open Mettapedia.Computability.PNP

universe u

theorem card_two_threshold_regression
    {Input : Type u} [Fintype Input] {s m : ℕ}
    (hcard : Fintype.card Input = 2) (hsm : s < m) :
    2 ^ s * (Fintype.card Input - 1) ^ m <
      Fintype.card Input ^ m := by
  exact
    BitEncodedClassifierFamily.bitBudget_bound_lt_of_card_eq_two_of_lt_sampleSize
      (Input := Input) (s := s) hcard hsm

theorem card_two_exact_recovery_regression
    {Input : Type u} [Fintype Input] {s m : ℕ}
    (F : BitEncodedClassifierFamily Input s)
    (hcard : Fintype.card Input = 2)
    (target : Input → Bool)
    (htarget : ∃ c : BitCode s, F.decode c = target)
    (hsm : s < m) :
    ∃ sample : PointSample Input m,
      F.empiricalRiskPredictor (labeledByTarget target sample) = target := by
  exact
    F.exists_sample_empiricalRiskPredictor_eq_target_of_card_eq_two_of_lt_sampleSize
      hcard target htarget hsm

theorem bool_exact_recovery_regression
    {s m : ℕ} (F : BitEncodedClassifierFamily Bool s)
    (target : Bool → Bool)
    (htarget : ∃ c : BitCode s, F.decode c = target)
    (hsm : s < m) :
    ∃ sample : PointSample Bool m,
      F.empiricalRiskPredictor (labeledByTarget target sample) = target := by
  exact
    F.exists_bool_sample_empiricalRiskPredictor_eq_target_of_lt_sampleSize
      target htarget hsm

end Mettapedia.Computability.PNP.BitFamilyUniformRecoveryBinaryRegression
