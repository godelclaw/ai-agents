import Mettapedia.Computability.PNP.BitFamilyUniformRecovery

/-!
# Regression checks for finite uniform bit-budget recovery

These wrappers pin the pure counting form of the grassroots bit-budget bridge.
They sit below the rational-rate layer: the only hypothesis is the finite
cardinality threshold with an explicit `2^s` code budget.
-/

namespace Mettapedia.Computability.PNP.FiniteUniformRecoveryRegression

open Mettapedia.Computability.PNP

universe u

theorem bit_family_nondeceptive_sample_exists_regression
    {Input : Type u} [Fintype Input]
    {s : ℕ} (F : BitEncodedClassifierFamily Input s)
    (target : Input → Bool) (m : ℕ)
    (hbound :
      2 ^ s * (Fintype.card Input - 1) ^ m <
        Fintype.card Input ^ m) :
    ∃ sample : PointSample Input m,
      ¬ F.toEncodedFamily.IsDeceptiveSample target sample := by
  exact F.exists_nondeceptiveSample_of_bitBudget_bound_lt target m hbound

theorem bit_family_exact_recovery_sample_exists_regression
    {Input : Type u} [Fintype Input]
    {s : ℕ} (F : BitEncodedClassifierFamily Input s)
    (target : Input → Bool) (m : ℕ)
    (htarget : ∃ c : BitCode s, F.decode c = target)
    (hbound :
      2 ^ s * (Fintype.card Input - 1) ^ m <
        Fintype.card Input ^ m) :
    ∃ sample : PointSample Input m,
      F.empiricalRiskPredictor (labeledByTarget target sample) = target := by
  exact
    F.exists_sample_empiricalRiskPredictor_eq_target_of_bitBudget_bound_lt
      target m htarget hbound

end Mettapedia.Computability.PNP.FiniteUniformRecoveryRegression
