import Mettapedia.Computability.PNP.ExactZABTargetInterface
import Mettapedia.Computability.PNP.SharedExactZABTargetInterface
import Mettapedia.Computability.PNP.BitVecZABCompressionObstruction
import Mettapedia.Computability.PNP.ProductSuccessKpolyBridgeObstruction
import Mathlib.Tactic

/-!
# P vs NP crux: small exact-ZAB classes miss the full exact-visible rule family

The live injective `z+a+b` branch is not just an ERM-sample-selection issue.
Below the verified size thresholds, the underlying exact-ZAB hypothesis classes
themselves cannot realize the full Boolean rule family on the exact visible
surface.

This file upgrades the recent ERM-target contradictions to class-level
full-family obstructions:

* the raw exact `(zfeat(z), a, b)` decision-list class;
* the shared exact affine-feature class;
* the shared exact sparse-threshold class;
* the shared exact affine-decision-list class.
-/

namespace Mettapedia.Computability.PNP

section

variable {n p r k : ℕ}

theorem fullExactVisibleRuleFamily_not_realizedByRawExactZABDecisionListFamily_of_extractorWidth_lt_truthTableGap
    (zfeat : BitVec n → BitVec r)
    (hgap : r < 2 ^ (n + 2 * k) - (2 * k + 1)) :
    ¬ RealizedByRawExactZABDecisionListFamily
        (Z := BitVec n) (r := r) (k := k)
        zfeat (fullExactVisibleRuleFamily (BitVec n) k) := by
  intro hreal
  let htarget :
      ExactZABDecisionListTargetData
        (Z := BitVec n) (r := r) (k := k)
        (Index := ExactVisibleRule (BitVec n) k)
        zfeat (fullExactVisibleRuleFamily (BitVec n) k) := ⟨hreal⟩
  have hs :
      r + 2 * k + 1 < Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k) := by
    have hs' : r + 2 * k + 1 < 2 ^ (n + 2 * k) := by
      omega
    simpa [card_exactVisiblePostSwitchSurface_bitVec] using hs'
  exact
    (htarget.not_surjective_predict_of_lt_surfaceCard hs)
      (fullExactVisibleRuleFamily_surjective (BitVec n) k)

theorem fullExactVisibleRuleFamily_not_realizedBySharedExactZABAffineFeatureFamily_of_featureCount_lt_visibleWidth
    (zfeat : BitVec n → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (hfeat : p < n + 2 * k) :
    ¬ RealizedBySharedExactZABAffineFeatureFamily
        (Z := BitVec n) (p := p) (r := r) (k := k)
        zfeat features (fullExactVisibleRuleFamily (BitVec n) k) := by
  intro hreal
  let htarget :
      SharedExactZABAffineFeatureTargetData
        (Z := BitVec n) (p := p) (r := r) (k := k)
        (Index := ExactVisibleRule (BitVec n) k)
        zfeat features (fullExactVisibleRuleFamily (BitVec n) k) := ⟨hreal⟩
  have hs :
      2 ^ p < Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k) := by
    have hs' : 2 ^ p < 2 ^ (n + 2 * k) := by
      exact (Nat.pow_lt_pow_iff_right Nat.one_lt_two).2 hfeat
    simpa [card_exactVisiblePostSwitchSurface_bitVec] using hs'
  exact
    (htarget.not_surjective_predict_of_lt_surfaceCard hs)
      (fullExactVisibleRuleFamily_surjective (BitVec n) k)

theorem fullExactVisibleRuleFamily_not_realizedBySharedExactZABSparseThresholdAffineFamily_of_linearBudget_lt_surfaceCard
    (zfeat : BitVec n → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (hlin : 2 * p < 2 ^ (n + 2 * k)) :
    ¬ RealizedBySharedExactZABSparseThresholdAffineFamily
        (Z := BitVec n) (p := p) (r := r) (k := k)
        zfeat features (fullExactVisibleRuleFamily (BitVec n) k) := by
  intro hreal
  let htarget :
      SharedExactZABSparseThresholdTargetData
        (Z := BitVec n) (p := p) (r := r) (k := k)
        (Index := ExactVisibleRule (BitVec n) k)
        zfeat features (fullExactVisibleRuleFamily (BitVec n) k) := ⟨hreal⟩
  have hs :
      2 * p < Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k) := by
    simpa [card_exactVisiblePostSwitchSurface_bitVec] using hlin
  exact
    (htarget.not_surjective_predict_of_lt_surfaceCard hs)
      (fullExactVisibleRuleFamily_surjective (BitVec n) k)

theorem fullExactVisibleRuleFamily_not_realizedBySharedExactZABAffineDecisionListFamily_of_combinerWidth_lt_truthTableGap
    (zfeat : BitVec n → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (hgap : p < 2 ^ (n + 2 * k) - 1) :
    ¬ RealizedBySharedExactZABAffineDecisionListFamily
        (Z := BitVec n) (p := p) (r := r) (k := k)
        zfeat features (fullExactVisibleRuleFamily (BitVec n) k) := by
  intro hreal
  let htarget :
      SharedExactZABDecisionListTargetData
        (Z := BitVec n) (p := p) (r := r) (k := k)
        (Index := ExactVisibleRule (BitVec n) k)
        zfeat features (fullExactVisibleRuleFamily (BitVec n) k) := ⟨hreal⟩
  have hs :
      p + 1 < Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k) := by
    have hs' : p + 1 < 2 ^ (n + 2 * k) := by
      omega
    simpa [card_exactVisiblePostSwitchSurface_bitVec] using hs'
  exact
    (htarget.not_surjective_predict_of_lt_surfaceCard hs)
      (fullExactVisibleRuleFamily_surjective (BitVec n) k)

end

end Mettapedia.Computability.PNP
