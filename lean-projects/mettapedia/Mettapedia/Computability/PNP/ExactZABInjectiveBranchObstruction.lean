import Mettapedia.Computability.PNP.BitVecZABCompressionObstruction
import Mettapedia.Computability.PNP.ExactZABERMRoute
import Mettapedia.Computability.PNP.SharedExactZABFeatureERMRoute
import Mettapedia.Computability.PNP.SharedExactZABERMRoute
import Mathlib.Tactic

/-!
# P vs NP crux: the live injective exact-ZAB branch still forces huge budgets

The noninjective extractor branch is already blocked by visible collisions.
This file targets the live alternative branch: even if the extractor is
injective, any surjective exact/shared exact `z+a+b` ERM route still has to pay
explicit lower bounds on its route parameters.

In particular:

* the raw exact decision-list ERM route needs extractor width
  `r ≥ 2^(n + 2k) - (2k + 1)`;
* the shared exact affine-feature ERM route needs at least `n + 2k` shared
  features;
* the shared exact affine-decision-list ERM route needs combiner width
  `p ≥ 2^(n + 2k) - 1`.

These statements do not use noninjectivity at all, so they speak directly to
the remaining injective-encoder branch.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section Route

variable {n p r k : ℕ} {Index : Type*}

theorem exactZABDecisionListERMFamily_extractorWidthLowerBound_of_surjective_predict
    (zfeat : BitVec n → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool)
    (hsurj :
      Function.Surjective
        (exactZABDecisionListERMFamily
          (Z := BitVec n) (r := r) (k := k) zfeat samples).predict) :
    2 ^ (n + 2 * k) - (2 * k + 1) ≤ r := by
  let s := 2 ^ (n + 2 * k)
  have hs : s ≤ r + 2 * k + 1 := by
    simpa [s, card_exactVisiblePostSwitchSurface_bitVec] using
      (exactZABDecisionListERMFamily_surfaceCard_le_of_surjective_predict
        (Z := BitVec n) (r := r) (k := k) (Index := Index) zfeat samples hsurj)
  rw [Nat.sub_le_iff_le_add]
  simpa [s, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hs

theorem exactZABDecisionListERMFamily_not_surjective_of_extractorWidth_lt_truthTableGap
    (zfeat : BitVec n → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool)
    (hgap : r < 2 ^ (n + 2 * k) - (2 * k + 1)) :
    ¬ Function.Surjective
        (exactZABDecisionListERMFamily
          (Z := BitVec n) (r := r) (k := k) zfeat samples).predict := by
  intro hsurj
  exact Nat.not_le_of_lt hgap <|
    exactZABDecisionListERMFamily_extractorWidthLowerBound_of_surjective_predict
      (n := n) (r := r) (k := k) (Index := Index) zfeat samples hsurj

theorem sharedExactZABAffineFeatureERMFamily_featureCountLowerBound_of_surjective_predict
    (zfeat : BitVec n → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool)
    (hsurj :
      Function.Surjective
        (sharedExactZABAffineFeatureERMFamily
          (Z := BitVec n) (p := p) (r := r) (k := k) zfeat features samples).predict) :
    n + 2 * k ≤ p := by
  have hpow :
      2 ^ (n + 2 * k) ≤ 2 ^ p := by
    simpa [card_exactVisiblePostSwitchSurface_bitVec] using
      (sharedExactZABAffineFeatureERMFamily_surfaceCard_le_of_surjective_predict
        (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index)
        zfeat features samples hsurj)
  exact (Nat.pow_le_pow_iff_right Nat.one_lt_two).1 hpow

theorem sharedExactZABAffineFeatureERMFamily_not_surjective_of_featureCount_lt_visibleWidth
    (zfeat : BitVec n → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool)
    (hfeat : p < n + 2 * k) :
    ¬ Function.Surjective
        (sharedExactZABAffineFeatureERMFamily
          (Z := BitVec n) (p := p) (r := r) (k := k) zfeat features samples).predict := by
  intro hsurj
  exact Nat.not_le_of_lt hfeat <|
    sharedExactZABAffineFeatureERMFamily_featureCountLowerBound_of_surjective_predict
      (n := n) (p := p) (r := r) (k := k) (Index := Index) zfeat features samples hsurj

theorem sharedExactZABAffineDecisionListERMFamily_combinerWidthLowerBound_of_surjective_predict
    (zfeat : BitVec n → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool)
    (hsurj :
      Function.Surjective
        (sharedExactZABAffineDecisionListERMFamily
          (Z := BitVec n) (p := p) (r := r) (k := k)
          zfeat features samples).predict) :
    2 ^ (n + 2 * k) - 1 ≤ p := by
  let s := 2 ^ (n + 2 * k)
  have hs : s ≤ p + 1 := by
    simpa [s, card_exactVisiblePostSwitchSurface_bitVec] using
      (sharedExactZABAffineDecisionListERMFamily_surfaceCard_le_of_surjective_predict
        (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index)
        zfeat features samples hsurj)
  rw [Nat.sub_le_iff_le_add]
  simpa [s, Nat.add_comm] using hs

theorem sharedExactZABAffineDecisionListERMFamily_not_surjective_of_combinerWidth_lt_truthTableGap
    (zfeat : BitVec n → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool)
    (hgap : p < 2 ^ (n + 2 * k) - 1) :
    ¬ Function.Surjective
        (sharedExactZABAffineDecisionListERMFamily
          (Z := BitVec n) (p := p) (r := r) (k := k)
          zfeat features samples).predict := by
  intro hsurj
  exact Nat.not_le_of_lt hgap <|
    sharedExactZABAffineDecisionListERMFamily_combinerWidthLowerBound_of_surjective_predict
      (n := n) (p := p) (r := r) (k := k) (Index := Index)
      zfeat features samples hsurj

end Route

end Mettapedia.Computability.PNP
