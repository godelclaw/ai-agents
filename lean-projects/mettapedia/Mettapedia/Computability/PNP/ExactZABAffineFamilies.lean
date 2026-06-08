import Mettapedia.Computability.PNP.ExactZABDecisionListFamily
import Mettapedia.Computability.PNP.ExactAffineRecovery

/-!
# P vs NP grassroots: affine candidate families on the exact `(zfeat(z), a, b)` surface

This file reuses the generic affine-family machinery on top of the exact visible
bit extractor `(zfeat(z), a, b)`.

Fixing one shared extractor `zfeat : Z → BitVec r`, we obtain three exact
candidate ladders on the full visible bit surface:

* bounded affine-feature predictors on `(zfeat(z), a, b)`,
* sparse-threshold affine predictors on `(zfeat(z), a, b)`,
* affine decision-list predictors on `(zfeat(z), a, b)`.

Unlike the shared-basis route, these families keep the full non-shared code
budgets explicit.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {Z : Type*} {p r k : ℕ}

/-- The exact-surface bit family induced by bounded affine-feature predictors
on the exact visible bit surface `(zfeat(z), a, b)`. -/
noncomputable def exactZABAffineFeatureBitFamily
    (Z : Type*) (p r k : ℕ) (zfeat : Z → BitVec r) :
    BitEncodedClassifierFamily (ExactVisiblePostSwitchSurface Z k)
      (p * ((r + (k + k)) + 1) + 2 ^ p) :=
  IndexedPredictorFamily.pullbackBitFamily
    (exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat)
    (affineFeatureBitFamily p (r + (k + k)))

/-- The exact-surface bit family induced by sparse-threshold affine predictors
on the exact visible bit surface `(zfeat(z), a, b)`. -/
noncomputable def exactZABSparseThresholdAffineBitFamily
    (Z : Type*) (p r k : ℕ) (zfeat : Z → BitVec r) :
    BitEncodedClassifierFamily (ExactVisiblePostSwitchSurface Z k)
      (p * ((r + (k + k)) + 3)) :=
  IndexedPredictorFamily.pullbackBitFamily
    (exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat)
    (sparseThresholdAffineBitFamily p (r + (k + k)))

/-- The exact-surface bit family induced by affine decision-list predictors on
the exact visible bit surface `(zfeat(z), a, b)`. -/
noncomputable def exactZABAffineDecisionListBitFamily
    (Z : Type*) (p r k : ℕ) (zfeat : Z → BitVec r) :
    BitEncodedClassifierFamily (ExactVisiblePostSwitchSurface Z k)
      (p * ((r + (k + k)) + 2) + 1) :=
  IndexedPredictorFamily.pullbackBitFamily
    (exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat)
    (affineDecisionListBitFamily p (r + (k + k)))

/-- Exact-surface specialization: the switched family depends only on a bounded
affine-feature summary of the exact visible bits `(zfeat(z), a, b)`. -/
abbrev RealizedByExactZABAffineFeatureFamily
    {Z : Type*} {Index : Type*}
    (zfeat : Z → BitVec r)
    (G : ExactVisibleSwitchedFamily Z k Index) : Prop :=
  RealizedByAffineFeatureFamily (r := p) (k := r + (k + k))
    (exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat) G

/-- Exact-surface specialization: the switched family depends only on a
sparse-threshold affine summary of the exact visible bits `(zfeat(z), a, b)`. -/
abbrev RealizedByExactZABSparseThresholdAffineFamily
    {Z : Type*} {Index : Type*}
    (zfeat : Z → BitVec r)
    (G : ExactVisibleSwitchedFamily Z k Index) : Prop :=
  RealizedBySparseThresholdAffineFamily (r := p) (k := r + (k + k))
    (exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat) G

/-- Exact-surface specialization: the switched family depends only on an
affine decision-list summary of the exact visible bits `(zfeat(z), a, b)`. -/
abbrev RealizedByExactZABAffineDecisionListFamily
    {Z : Type*} {Index : Type*}
    (zfeat : Z → BitVec r)
    (G : ExactVisibleSwitchedFamily Z k Index) : Prop :=
  RealizedByAffineDecisionListFamily (r := p) (k := r + (k + k))
    (exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat) G

theorem exactVisibleCompressionTarget_of_realizedByExactZABAffineFeatureFamily
    {Z : Type*} {Index : Type*}
    (zfeat : Z → BitVec r)
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hreal :
      RealizedByExactZABAffineFeatureFamily
        (p := p) (Z := Z) (r := r) (k := k) (Index := Index) zfeat G) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G
      (p * ((r + (k + k)) + 1) + 2 ^ p) := by
  exact hasBitBudget_of_realizedByAffineFeatureFamily
    (r := p) (k := r + (k + k)) hreal

theorem exactVisibleCompressionTarget_of_realizedByExactZABSparseThresholdAffineFamily
    {Z : Type*} {Index : Type*}
    (zfeat : Z → BitVec r)
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hreal :
      RealizedByExactZABSparseThresholdAffineFamily
        (p := p) (Z := Z) (r := r) (k := k) (Index := Index) zfeat G) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G
      (p * ((r + (k + k)) + 3)) := by
  exact hasBitBudget_of_realizedBySparseThresholdAffineFamily
    (r := p) (k := r + (k + k)) hreal

theorem exactVisibleCompressionTarget_of_realizedByExactZABAffineDecisionListFamily
    {Z : Type*} {Index : Type*}
    (zfeat : Z → BitVec r)
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hreal :
      RealizedByExactZABAffineDecisionListFamily
        (p := p) (Z := Z) (r := r) (k := k) (Index := Index) zfeat G) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G
      (p * ((r + (k + k)) + 2) + 1) := by
  exact hasBitBudget_of_realizedByAffineDecisionListFamily
    (r := p) (k := r + (k + k)) hreal

@[simp] theorem exactZABAffineFeatureBitFamily_decode_code
    (zfeat : Z → BitVec r)
    (code : AffineFeatureCode p (r + (k + k))) :
    (exactZABAffineFeatureBitFamily Z p r k zfeat).decode
        (affineFeatureCodeEquivBitCode p (r + (k + k)) code)
      = fun u : ExactVisiblePostSwitchSurface Z k =>
          affineFeaturePredict code
            (exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat u) := by
  funext u
  change affineFeaturePredict
      ((affineFeatureCodeEquivBitCode p (r + (k + k))).symm
        (affineFeatureCodeEquivBitCode p (r + (k + k)) code))
      (exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat u)
      =
      affineFeaturePredict code
        (exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat u)
  simp

@[simp] theorem exactZABSparseThresholdAffineBitFamily_decode_code
    (zfeat : Z → BitVec r)
    (code : SparseThresholdAffineCode p (r + (k + k))) :
    (exactZABSparseThresholdAffineBitFamily Z p r k zfeat).decode
        (sparseThresholdAffineCodeEquivBitCode p (r + (k + k)) code)
      = fun u : ExactVisiblePostSwitchSurface Z k =>
          sparseThresholdAffinePredict code
            (exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat u) := by
  funext u
  change sparseThresholdAffinePredict
      ((sparseThresholdAffineCodeEquivBitCode p (r + (k + k))).symm
        (sparseThresholdAffineCodeEquivBitCode p (r + (k + k)) code))
      (exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat u)
      =
      sparseThresholdAffinePredict code
        (exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat u)
  simp

@[simp] theorem exactZABAffineDecisionListBitFamily_decode_code
    (zfeat : Z → BitVec r)
    (code : AffineDecisionListCode p (r + (k + k))) :
    (exactZABAffineDecisionListBitFamily Z p r k zfeat).decode
        (affineDecisionListCodeEquivBitCode p (r + (k + k)) code)
      = fun u : ExactVisiblePostSwitchSurface Z k =>
          affineDecisionListPredict code
            (exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat u) := by
  funext u
  change affineDecisionListPredict
      ((affineDecisionListCodeEquivBitCode p (r + (k + k))).symm
        (affineDecisionListCodeEquivBitCode p (r + (k + k)) code))
      (exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat u)
      =
      affineDecisionListPredict code
        (exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat u)
  simp

theorem exactZABAffineFeatureRecoveryLowerBound
    [Fintype Z]
    (zfeat : Z → BitVec r)
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (target : ExactVisiblePostSwitchSurface Z k → Bool) (m : ℕ)
    (htarget : ∃ code : AffineFeatureCode p (r + (k + k)),
      target = fun u : ExactVisiblePostSwitchSurface Z k =>
        affineFeaturePredict code
          (exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat u))
    {q : ℝ≥0∞}
    (hq :
      ∀ c : (exactZABAffineFeatureBitFamily Z p r k zfeat).toEncodedFamily.BadCodes target,
        agreementMass μ target
          ((exactZABAffineFeatureBitFamily Z p r k zfeat).decode c.1) ≤ q) :
    1 - (2 ^ (p * ((r + (k + k)) + 1) + 2 ^ p) : ℝ≥0∞) * q ^ m ≤
      (exactZABAffineFeatureBitFamily Z p r k zfeat).bitExactRecoverySampleMass μ target m := by
  rcases htarget with ⟨code, rfl⟩
  refine BitEncodedClassifierFamily.exactRecoverySampleMass_ge_one_sub_bitBudget_mul_pow_of_agreementMass_le
    (F := exactZABAffineFeatureBitFamily Z p r k zfeat)
    (μ := μ)
    (target := fun u : ExactVisiblePostSwitchSurface Z k =>
      affineFeaturePredict code
        (exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat u))
    (m := m) ?_ hq
  refine ⟨affineFeatureCodeEquivBitCode p (r + (k + k)) code, ?_⟩
  exact exactZABAffineFeatureBitFamily_decode_code
    (Z := Z) (p := p) (r := r) (k := k) zfeat code

theorem exactZABSparseThresholdAffineRecoveryLowerBound
    [Fintype Z]
    (zfeat : Z → BitVec r)
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (target : ExactVisiblePostSwitchSurface Z k → Bool) (m : ℕ)
    (htarget : ∃ code : SparseThresholdAffineCode p (r + (k + k)),
      target = fun u : ExactVisiblePostSwitchSurface Z k =>
        sparseThresholdAffinePredict code
          (exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat u))
    {q : ℝ≥0∞}
    (hq :
      ∀ c :
        (exactZABSparseThresholdAffineBitFamily Z p r k zfeat).toEncodedFamily.BadCodes target,
        agreementMass μ target
          ((exactZABSparseThresholdAffineBitFamily Z p r k zfeat).decode c.1) ≤ q) :
    1 - (2 ^ (p * ((r + (k + k)) + 3)) : ℝ≥0∞) * q ^ m ≤
      (exactZABSparseThresholdAffineBitFamily Z p r k zfeat).bitExactRecoverySampleMass
        μ target m := by
  rcases htarget with ⟨code, rfl⟩
  refine BitEncodedClassifierFamily.exactRecoverySampleMass_ge_one_sub_bitBudget_mul_pow_of_agreementMass_le
    (F := exactZABSparseThresholdAffineBitFamily Z p r k zfeat)
    (μ := μ)
    (target := fun u : ExactVisiblePostSwitchSurface Z k =>
      sparseThresholdAffinePredict code
        (exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat u))
    (m := m) ?_ hq
  refine ⟨sparseThresholdAffineCodeEquivBitCode p (r + (k + k)) code, ?_⟩
  exact exactZABSparseThresholdAffineBitFamily_decode_code
    (Z := Z) (p := p) (r := r) (k := k) zfeat code

theorem exactZABAffineDecisionListRecoveryLowerBound
    [Fintype Z]
    (zfeat : Z → BitVec r)
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (target : ExactVisiblePostSwitchSurface Z k → Bool) (m : ℕ)
    (htarget : ∃ code : AffineDecisionListCode p (r + (k + k)),
      target = fun u : ExactVisiblePostSwitchSurface Z k =>
        affineDecisionListPredict code
          (exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat u))
    {q : ℝ≥0∞}
    (hq :
      ∀ c :
        (exactZABAffineDecisionListBitFamily Z p r k zfeat).toEncodedFamily.BadCodes target,
        agreementMass μ target
          ((exactZABAffineDecisionListBitFamily Z p r k zfeat).decode c.1) ≤ q) :
    1 - (2 ^ (p * ((r + (k + k)) + 2) + 1) : ℝ≥0∞) * q ^ m ≤
      (exactZABAffineDecisionListBitFamily Z p r k zfeat).bitExactRecoverySampleMass
        μ target m := by
  rcases htarget with ⟨code, rfl⟩
  refine BitEncodedClassifierFamily.exactRecoverySampleMass_ge_one_sub_bitBudget_mul_pow_of_agreementMass_le
    (F := exactZABAffineDecisionListBitFamily Z p r k zfeat)
    (μ := μ)
    (target := fun u : ExactVisiblePostSwitchSurface Z k =>
      affineDecisionListPredict code
        (exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat u))
    (m := m) ?_ hq
  refine ⟨affineDecisionListCodeEquivBitCode p (r + (k + k)) code, ?_⟩
  exact exactZABAffineDecisionListBitFamily_decode_code
    (Z := Z) (p := p) (r := r) (k := k) zfeat code

end

end Mettapedia.Computability.PNP
