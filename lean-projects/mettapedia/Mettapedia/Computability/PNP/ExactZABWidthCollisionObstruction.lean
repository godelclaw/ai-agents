import Mettapedia.Computability.PNP.ExactZABVisibleCollisionObstruction

/-!
# P vs NP crux: width-compressing exact `z+a+b` extractors force visible collisions

The exact and shared exact `z+a+b` routes only see the visible summary
`(zfeat(z), a, b)`.  If the extractor compresses `BitVec n` into `BitVec r`
with `r < n`, then it is automatically noninjective, so every such route falls
into the visible-collision obstruction branch.

This closes the width-compressing extractor branch for the named exact ZAB ERM
surfaces, not only for the raw decision-list presentation.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section Core

theorem not_injective_bitVecExtractor_of_width_lt
    {n r : ℕ}
    (zfeat : BitVec n → BitVec r)
    (hwidth : r < n) :
    ¬ Function.Injective zfeat := by
  apply not_injective_of_card_gt_bitVec (Z := BitVec n) (r := r) zfeat
  simpa [BitVec] using (Nat.pow_lt_pow_right Nat.one_lt_two hwidth)

end Core

section Route

variable {n p r k : ℕ} {Index : Type*}

theorem exactZABDecisionListERMFamily_not_surjective_of_width_lt
    (zfeat : BitVec n → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool)
    (hwidth : r < n) :
    ¬ Function.Surjective
        (exactZABDecisionListERMFamily
          (Z := BitVec n) (r := r) (k := k) zfeat samples).predict := by
  exact
    exactZABDecisionListERMFamily_not_surjective_of_not_injective_zfeat
      (Z := BitVec n) (r := r) (k := k) (Index := Index)
      zfeat samples
      (not_injective_bitVecExtractor_of_width_lt zfeat hwidth)

theorem exactZABAffineFeatureERMFamily_not_surjective_of_width_lt
    (zfeat : BitVec n → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool)
    (hwidth : r < n) :
    ¬ Function.Surjective
        (exactZABAffineFeatureERMFamily
          (Z := BitVec n) (p := p) (r := r) (k := k) zfeat samples).predict := by
  exact
    exactZABAffineFeatureERMFamily_not_surjective_of_not_injective_zfeat
      (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index)
      zfeat samples
      (not_injective_bitVecExtractor_of_width_lt zfeat hwidth)

theorem exactZABSparseThresholdAffineERMFamily_not_surjective_of_width_lt
    (zfeat : BitVec n → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool)
    (hwidth : r < n) :
    ¬ Function.Surjective
        (exactZABSparseThresholdAffineERMFamily
          (Z := BitVec n) (p := p) (r := r) (k := k) zfeat samples).predict := by
  exact
    exactZABSparseThresholdAffineERMFamily_not_surjective_of_not_injective_zfeat
      (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index)
      zfeat samples
      (not_injective_bitVecExtractor_of_width_lt zfeat hwidth)

theorem sharedExactZABAffineFeatureERMFamily_not_surjective_of_width_lt
    (zfeat : BitVec n → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool)
    (hwidth : r < n) :
    ¬ Function.Surjective
        (sharedExactZABAffineFeatureERMFamily
          (Z := BitVec n) (p := p) (r := r) (k := k) zfeat features samples).predict := by
  exact
    sharedExactZABAffineFeatureERMFamily_not_surjective_of_not_injective_zfeat
      (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index)
      zfeat features samples
      (not_injective_bitVecExtractor_of_width_lt zfeat hwidth)

theorem sharedExactZABSparseThresholdAffineERMFamily_not_surjective_of_width_lt
    (zfeat : BitVec n → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool)
    (hwidth : r < n) :
    ¬ Function.Surjective
        (sharedExactZABSparseThresholdAffineERMFamily
          (Z := BitVec n) (p := p) (r := r) (k := k) zfeat features samples).predict := by
  exact
    sharedExactZABSparseThresholdAffineERMFamily_not_surjective_of_not_injective_zfeat
      (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index)
      zfeat features samples
      (not_injective_bitVecExtractor_of_width_lt zfeat hwidth)

theorem sharedExactZABAffineDecisionListERMFamily_not_surjective_of_width_lt
    (zfeat : BitVec n → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool)
    (hwidth : r < n) :
    ¬ Function.Surjective
        (sharedExactZABAffineDecisionListERMFamily
          (Z := BitVec n) (p := p) (r := r) (k := k) zfeat features samples).predict := by
  exact
    sharedExactZABAffineDecisionListERMFamily_not_surjective_of_not_injective_zfeat
      (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index)
      zfeat features samples
      (not_injective_bitVecExtractor_of_width_lt zfeat hwidth)

end Route

end Mettapedia.Computability.PNP
