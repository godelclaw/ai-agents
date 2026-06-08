import Mettapedia.Computability.PNP.ExactVisibleCompressionObstruction
import Mettapedia.Computability.PNP.ExactZABTargetInterface
import Mettapedia.Computability.PNP.BitVecZABERMInterface
import Mathlib.Tactic

/-!
# P vs NP crux: bit-valued exact `(z, a, b)` routes still face truth-table explosion

When the latent local datum is already a bitvector `z : BitVec r`, the exact
visible manuscript surface `(z, a, b)` has `r + 2k` visible bits.  So the full
Boolean rule class on that surface requires truth-table budget `2^(r + 2k)`.

This file records two concrete consequences:

* the exact visible surface itself has cardinality `2^(r + 2k)`;
* therefore any exact `(z, a, b)` route using only the linear budget
  `r + 2k + 1` cannot realize the full exact rule class once `r + 2k ≥ 2`.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {r k s : ℕ} {Index : Type*}

/-- For bit-valued latent data, the full exact visible post-switch surface has
cardinality `2^(r + 2k)`. -/
theorem card_exactVisiblePostSwitchSurface_bitVec (r k : ℕ) :
    Fintype.card (ExactVisiblePostSwitchSurface (BitVec r) k) = 2 ^ (r + 2 * k) := by
  calc
    Fintype.card (ExactVisiblePostSwitchSurface (BitVec r) k)
        = Fintype.card (BitVec r) * 2 ^ k * 2 ^ k := by
            simpa using
              (card_exactVisiblePostSwitchSurface (Z := BitVec r) (k := k))
    _ = 2 ^ r * 2 ^ k * 2 ^ k := by simp [BitVec]
    _ = 2 ^ (r + 2 * k) := by
      rw [← Nat.pow_add, ← Nat.pow_add]
      simp [two_mul, Nat.add_left_comm, Nat.add_comm]

/-- On the bit-valued exact visible surface, any exact compression target for a
surjective family needs at least `2^(r + 2k)` code bits. -/
theorem exactVisibleCompressionTarget_bitVecSurfaceCard_le_of_surjective_predict
    {G : ExactVisibleSwitchedFamily (BitVec r) k Index}
    (hsurj : Function.Surjective G.predict)
    (hsmall : ExactVisibleCompressionTarget
      (Z := BitVec r) (k := k) (Index := Index) G s) :
    2 ^ (r + 2 * k) ≤ s := by
  simpa [card_exactVisiblePostSwitchSurface_bitVec] using
    (exactVisibleCompressionTarget_surfaceCard_le_of_surjective_predict
      (Z := BitVec r) (k := k) (s := s) (Index := Index) hsurj hsmall)

/-- Therefore no exact compression target below `2^(r + 2k)` can cover the
full Boolean rule class on the bit-valued exact visible surface. -/
theorem not_exactVisibleCompressionTarget_bitVec_of_lt
    {G : ExactVisibleSwitchedFamily (BitVec r) k Index}
    (hs : s < 2 ^ (r + 2 * k))
    (hsurj : Function.Surjective G.predict) :
    ¬ ExactVisibleCompressionTarget (Z := BitVec r) (k := k) (Index := Index) G s := by
  intro hsmall
  exact Nat.not_le_of_lt hs <|
    exactVisibleCompressionTarget_bitVecSurfaceCard_le_of_surjective_predict
      (r := r) (k := k) (s := s) (Index := Index) hsurj hsmall

/-- The linear exact `(z, a, b)` decision-list budget is strictly below the
truth-table threshold as soon as the raw visible width `r + 2k` is at least `2`. -/
theorem exactZABDecisionListBudget_lt_bitVecTruthTable_of_two_le
    (hwidth : 2 ≤ r + 2 * k) :
    r + 2 * k + 1 < 2 ^ (r + 2 * k) := by
  have hmain : ∀ m : ℕ, m + 3 < 2 ^ (m + 2) := by
    intro m
    induction m with
    | zero =>
        norm_num
    | succ m ih =>
        have hle : m + 4 ≤ 2 * (m + 3) := by
          omega
        have hlt : 2 * (m + 3) < 2 * 2 ^ (m + 2) := by
          exact Nat.mul_lt_mul_of_pos_left ih Nat.zero_lt_two
        exact lt_of_le_of_lt hle <| by
          simpa [Nat.pow_succ, Nat.add_assoc, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hlt
  rcases Nat.exists_eq_add_of_le hwidth with ⟨m, hm⟩
  rw [hm]
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hmain m

/-- If the raw exact `(z, a, b)` decision-list route on bit-valued latent data
is truly surjective onto the full exact rule class, its linear budget would
contradict the truth-table lower bound. -/
theorem ExactZABDecisionListTargetData.not_surjective_predict_of_identity_of_budget_lt
    {G : ExactVisibleSwitchedFamily (BitVec r) k Index}
    (h :
      ExactZABDecisionListTargetData
        (Z := BitVec r) (r := r) (k := k) (Index := Index) identityZExtractor G)
    (hbudget : r + 2 * k + 1 < 2 ^ (r + 2 * k)) :
    ¬ Function.Surjective G.predict := by
  intro hsurj
  have hbound : 2 ^ (r + 2 * k) ≤ r + 2 * k + 1 :=
    exactVisibleCompressionTarget_bitVecSurfaceCard_le_of_surjective_predict
      (r := r) (k := k) (s := r + 2 * k + 1) (Index := Index)
      hsurj h.compressionTarget_twoMul
  exact Nat.not_le_of_lt hbudget hbound

/-- In particular, the raw exact `(z, a, b)` decision-list route cannot be
surjective once the raw visible width is at least `2`. -/
theorem ExactZABDecisionListTargetData.not_surjective_predict_of_identity_of_two_le
    {G : ExactVisibleSwitchedFamily (BitVec r) k Index}
    (h :
      ExactZABDecisionListTargetData
        (Z := BitVec r) (r := r) (k := k) (Index := Index) identityZExtractor G)
    (hwidth : 2 ≤ r + 2 * k) :
    ¬ Function.Surjective G.predict := by
  exact
    h.not_surjective_predict_of_identity_of_budget_lt
      (exactZABDecisionListBudget_lt_bitVecTruthTable_of_two_le
        (r := r) (k := k) hwidth)

/-- The same contradiction applies to the recovery wrapper, since it already
packages the same exact compression target. -/
theorem ExactZABDecisionListRecoveryData.not_surjective_predict_of_identity_of_two_le
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec r) k)}
    {G : ExactVisibleSwitchedFamily (BitVec r) k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABDecisionListRecoveryData
        (Z := BitVec r) (r := r) (k := k) (Index := Index) μ identityZExtractor G q)
    (hwidth : 2 ≤ r + 2 * k) :
    ¬ Function.Surjective G.predict := by
  exact h.targetData.not_surjective_predict_of_identity_of_two_le hwidth

/-- Likewise for the final bit-valued ERM interface. -/
theorem BitVecZABERMRecoveryData.not_surjective_predict_of_two_le
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec r) k)}
    {G : ExactVisibleSwitchedFamily (BitVec r) k Index}
    {q : ℝ≥0∞}
    (h : BitVecZABERMRecoveryData (r := r) (k := k) (Index := Index) μ G q)
    (hwidth : 2 ≤ r + 2 * k) :
    ¬ Function.Surjective G.predict := by
  intro hsurj
  have hbound : 2 ^ (r + 2 * k) ≤ r + 2 * k + 1 :=
    exactVisibleCompressionTarget_bitVecSurfaceCard_le_of_surjective_predict
      (r := r) (k := k) (s := r + 2 * k + 1) (Index := Index)
      hsurj h.compressionTarget
  exact
    Nat.not_le_of_lt
      (exactZABDecisionListBudget_lt_bitVecTruthTable_of_two_le
        (r := r) (k := k) hwidth)
      hbound

end

end Mettapedia.Computability.PNP
