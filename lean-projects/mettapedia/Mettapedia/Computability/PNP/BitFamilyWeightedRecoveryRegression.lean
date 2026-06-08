import Mettapedia.Computability.PNP.BitFamilyWeightedRecovery

/-!
# Regression checks for weighted bit-family recovery

These wrappers pin the epsilon-form weighted exact-recovery theorem for
bit-encoded families.  They keep the same-route PNP recovery certificate
available as a small downstream obligation over `ENNReal` sample mass.
-/

namespace Mettapedia.Computability.PNP.BitFamilyWeightedRecoveryRegression

open Mettapedia.Computability.PNP
open scoped ENNReal

universe u

theorem bit_family_weighted_exact_recovery_epsilon_regression
    {Input : Type u} [Fintype Input]
    {s : ℕ} (F : BitEncodedClassifierFamily Input s)
    (μ : PMF Input) (target : Input → Bool) (m : ℕ)
    (htarget : ∃ c : BitCode s, F.decode c = target)
    {q epsilon : ℝ≥0∞}
    (hq : ∀ c : F.toEncodedFamily.BadCodes target, agreementMass μ target (F.decode c.1) ≤ q)
    (hepsilon : (2 ^ s : ℝ≥0∞) * q ^ m ≤ epsilon) :
    1 - epsilon ≤ F.bitExactRecoverySampleMass μ target m := by
  exact
    F.exactRecoverySampleMass_ge_one_sub_of_bitBudget_mul_pow_le
      μ target m htarget hq hepsilon

end Mettapedia.Computability.PNP.BitFamilyWeightedRecoveryRegression
