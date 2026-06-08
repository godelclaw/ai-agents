import Mettapedia.Computability.PNP.SameRouteInterface

/-!
# P vs NP grassroots: weighted bit-family recovery corollaries

This file exposes epsilon-form corollaries of the weighted finite-class ERM
bound specialized to bit-encoded classifier families.  It is the weighted
analogue of the uniform success-rate wrappers: a same-route rescue may discharge
the single quantitative obligation `(2^s) * q^m <= epsilon` instead of carrying
the exact failure term through downstream statements.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

universe u

namespace BitEncodedClassifierFamily

section WeightedRecovery

variable {Input : Type u} [Fintype Input]
variable {s : ℕ} (F : BitEncodedClassifierFamily Input s)

/-- Epsilon form of weighted exact recovery for bit-encoded families.  If every
bad code agrees with the target on at most `q` input mass and the resulting
bit-budget failure term is at most `epsilon`, exact ERM recovery has sample mass
at least `1 - epsilon`. -/
theorem exactRecoverySampleMass_ge_one_sub_of_bitBudget_mul_pow_le
    (μ : PMF Input) (target : Input → Bool) (m : ℕ)
    (htarget : ∃ c : BitCode s, F.decode c = target)
    {q epsilon : ℝ≥0∞}
    (hq : ∀ c : F.toEncodedFamily.BadCodes target, agreementMass μ target (F.decode c.1) ≤ q)
    (hepsilon : (2 ^ s : ℝ≥0∞) * q ^ m ≤ epsilon) :
    1 - epsilon ≤ F.bitExactRecoverySampleMass μ target m := by
  exact
    le_trans
      (tsub_le_tsub_left hepsilon 1)
      (F.exactRecoverySampleMass_ge_one_sub_bitBudget_mul_pow_of_agreementMass_le
        μ target m htarget hq)

end WeightedRecovery

end BitEncodedClassifierFamily

end Mettapedia.Computability.PNP
