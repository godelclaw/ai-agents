import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMBitCode
import Mettapedia.Computability.PNP.BitVecZABCompressionObstruction
import Mathlib.Tactic

/-!
# P vs NP crux: actual switched-local shared exact sparse-threshold ERM data
still faces a visible-budget obstruction

`ActualSwitchedLocalSharedExactZABSparseThresholdERMBitCode` shows that exact
identification with the point-block shared exact sparse-threshold ERM family
already yields bounded-code data at budget
`2 * allAffinePointBlockFeatureCount (r + 2*k)`.

This file turns that bounded-code witness into the corresponding actual-local
surjectivity obstruction.  No recovery-side agreement estimate and no finite
counting-gap liveness hypothesis are used here.

If an actual switched-local family carrying this sparse-threshold ERM packet is
still surjective on the exact visible surface, then the exact visible surface
cardinality must fit inside that point-block bit budget.  On `BitVec n` this
forces the explicit unconditional width inequality

* `n ≤ 2*r + 2*k + 1`.

So even before the stronger injective-branch arguments are invoked, the current
shared sparse-threshold route cannot repair the full-rule actual-local endpoint
with extractor width below roughly half the visible width.
-/

namespace Mettapedia.Computability.PNP

universe u v w

namespace ActualSwitchedLocalInterface

section Abstract

variable {Z : Type v} [Fintype Z] {k r : ℕ} {Index : Type u} {Block : Type w}
variable {T : ActualSwitchedLocalInterface Z k Index Block}
variable {zfeat : Z → BitVec r}

/-- Surjective actual-local shared exact sparse-threshold ERM data forces the
exact visible surface to fit inside the point-block sparse-threshold bit
budget. -/
theorem SharedExactZABSparseThresholdERMData.surfaceCard_le_of_surjective_predict
    (h : SharedExactZABSparseThresholdERMData T zfeat)
    (hsurj : Function.Surjective T.predictorFamily.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      2 * allAffinePointBlockFeatureCount (r + (k + k)) := by
  exact
    exactVisibleCompressionTarget_surfaceCard_le_of_surjective_predict
      (Z := Z) (k := k)
      (s := 2 * allAffinePointBlockFeatureCount (r + (k + k)))
      (Index := Index) hsurj
      h.compressionTarget

/-- Therefore such a packet cannot remain surjective once the point-block
visible bit budget is strictly below the exact visible surface cardinality. -/
theorem SharedExactZABSparseThresholdERMData.not_surjective_predict_of_lt_surfaceCard
    (h : SharedExactZABSparseThresholdERMData T zfeat)
    (hs :
      2 * allAffinePointBlockFeatureCount (r + (k + k)) <
        Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective T.predictorFamily.predict := by
  intro hsurj
  exact Nat.not_le_of_lt hs (h.surfaceCard_le_of_surjective_predict hsurj)

/-- So no surjective actual-local family can carry shared exact sparse-threshold
ERM data below the point-block visible-budget threshold. -/
theorem not_nonempty_sharedExactZABSparseThresholdERMData_of_surjective_predict_of_lt_surfaceCard
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (zfeat : Z → BitVec r)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    (hs :
      2 * allAffinePointBlockFeatureCount (r + (k + k)) <
        Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Nonempty (SharedExactZABSparseThresholdERMData T zfeat) := by
  rintro ⟨h⟩
  exact h.not_surjective_predict_of_lt_surfaceCard hs hsurj

/-- In particular, the full-rule actual-local counterexample is excluded below
the same point-block visible-budget threshold. -/
theorem fullRuleActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMData_of_lt_surfaceCard
    (zfeat : Z → BitVec r)
    (hs :
      2 * allAffinePointBlockFeatureCount (r + (k + k)) <
        Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Nonempty
        (SharedExactZABSparseThresholdERMData
          (fullRuleActualSwitchedLocalInterface Z k)
          zfeat) := by
  exact
    not_nonempty_sharedExactZABSparseThresholdERMData_of_surjective_predict_of_lt_surfaceCard
      (T := fullRuleActualSwitchedLocalInterface Z k)
      zfeat
      (fullRuleActualSwitchedLocalInterface_surjective Z k)
      hs

end Abstract

section BitVec

variable {n k r : ℕ} {Index : Type u} {Block : Type w}
variable {T : ActualSwitchedLocalInterface (BitVec n) k Index Block}
variable {zfeat : BitVec n → BitVec r}

/-- The point-block sparse-threshold visible budget has the explicit closed form
`2^(2*d + 1)`. -/
theorem sparseThresholdPointBlockVisibleBudget_eq_pow (d : ℕ) :
    2 * allAffinePointBlockFeatureCount d = 2 ^ (2 * d + 1) := by
  calc
    2 * allAffinePointBlockFeatureCount d
        = 2 * (2 ^ d * 2 ^ d) := by
            rw [allAffinePointBlockFeatureCount_eq]
    _ = 2 * 2 ^ (d + d) := by
          rw [← Nat.pow_add]
    _ = 2 ^ 1 * 2 ^ (d + d) := by
          simp
    _ = 2 ^ (1 + (d + d)) := by
          rw [← Nat.pow_add]
    _ = 2 ^ (2 * d + 1) := by
          simp [two_mul, Nat.add_assoc, Nat.add_comm]

/-- On `BitVec n`, surjective actual-local shared exact sparse-threshold ERM
data already forces the visible width to fit inside the point-block budget
`2*r + 2*k + 1`. -/
theorem SharedExactZABSparseThresholdERMData.visibleWidth_le_two_mul_extractorWidth_add_two_mul_k_succ_of_surjective_predict
    (h : SharedExactZABSparseThresholdERMData T zfeat)
    (hsurj : Function.Surjective T.predictorFamily.predict) :
    n ≤ 2 * r + 2 * k + 1 := by
  have hbudget :
      2 ^ (n + 2 * k) ≤ 2 * allAffinePointBlockFeatureCount (r + (k + k)) := by
    simpa [card_exactVisiblePostSwitchSurface_bitVec] using
      h.surfaceCard_le_of_surjective_predict hsurj
  rw [sparseThresholdPointBlockVisibleBudget_eq_pow (d := r + (k + k))] at hbudget
  have hwidth :
      n + 2 * k ≤ 2 * (r + (k + k)) + 1 := by
    exact (Nat.pow_le_pow_iff_right Nat.one_lt_two).1 hbudget
  omega

/-- Hence no surjective `BitVec n` actual-local family can carry shared exact
sparse-threshold ERM data once the extractor width is below the unconditional
point-block visible-budget threshold. -/
theorem not_nonempty_sharedExactZABSparseThresholdERMData_of_surjective_predict_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
    (T : ActualSwitchedLocalInterface (BitVec n) k Index Block)
    (zfeat : BitVec n → BitVec r)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    (hgap : 2 * r + 2 * k + 1 < n) :
    ¬ Nonempty (SharedExactZABSparseThresholdERMData T zfeat) := by
  rintro ⟨h⟩
  exact Nat.not_le_of_lt hgap <|
    h.visibleWidth_le_two_mul_extractorWidth_add_two_mul_k_succ_of_surjective_predict
      hsurj

/-- The same visible-budget obstruction already kills the entire extractor
choice at once: below the half-width threshold, no `BitVec n → BitVec r`
extractor can support surjective actual-local shared exact sparse-threshold ERM
data. -/
theorem not_exists_sharedExactZABSparseThresholdERMData_of_surjective_predict_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
    (T : ActualSwitchedLocalInterface (BitVec n) k Index Block)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    (hgap : 2 * r + 2 * k + 1 < n) :
    ¬ ∃ zfeat : BitVec n → BitVec r,
        Nonempty (SharedExactZABSparseThresholdERMData T zfeat) := by
  rintro ⟨zfeat, hdata⟩
  exact
    not_nonempty_sharedExactZABSparseThresholdERMData_of_surjective_predict_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
      (T := T) (zfeat := zfeat) hsurj hgap hdata

/-- In particular, the full-rule actual-local counterexample is excluded on
`BitVec n` whenever `2*r + 2*k + 1 < n`. -/
theorem fullRuleActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMData_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
    (zfeat : BitVec n → BitVec r)
    (hgap : 2 * r + 2 * k + 1 < n) :
    ¬ Nonempty
        (SharedExactZABSparseThresholdERMData
          (fullRuleActualSwitchedLocalInterface (BitVec n) k)
          zfeat) := by
  exact
    not_nonempty_sharedExactZABSparseThresholdERMData_of_surjective_predict_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
      (T := fullRuleActualSwitchedLocalInterface (BitVec n) k)
      zfeat
      (fullRuleActualSwitchedLocalInterface_surjective (BitVec n) k)
      hgap

/-- So the full-rule actual-local route cannot evade the visible-budget
obstruction by changing the extractor: below the half-width threshold, no
extractor at all can support the shared exact sparse-threshold ERM packet. -/
theorem fullRuleActualSwitchedLocalInterface_not_exists_sharedExactZABSparseThresholdERMData_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
    (hgap : 2 * r + 2 * k + 1 < n) :
    ¬ ∃ zfeat : BitVec n → BitVec r,
        Nonempty
          (SharedExactZABSparseThresholdERMData
            (fullRuleActualSwitchedLocalInterface (BitVec n) k)
            zfeat) := by
  exact
    not_exists_sharedExactZABSparseThresholdERMData_of_surjective_predict_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
      (T := fullRuleActualSwitchedLocalInterface (BitVec n) k)
      (fullRuleActualSwitchedLocalInterface_surjective (BitVec n) k)
      hgap

end BitVec

end ActualSwitchedLocalInterface

end Mettapedia.Computability.PNP
