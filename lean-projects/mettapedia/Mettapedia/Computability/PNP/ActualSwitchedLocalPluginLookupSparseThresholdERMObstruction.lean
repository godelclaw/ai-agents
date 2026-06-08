import Mettapedia.Computability.PNP.ActualSwitchedLocalPluginLookupObstruction
import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoveryVisibleBudgetObstruction

/-!
# PNP crux: bare plug-in lookup still cannot be treated as the shared
  sparse-threshold ERM route

`ActualSwitchedLocalPluginLookupObstruction` records the literal finite-alphabet
endpoint from the v11/arXiv manuscript paragraph: the post-switch local rule is
an unrestricted lookup table on the exact visible alphabet.  Lean already shows
that this endpoint is surjective onto the full exact-visible Boolean rule
family.

This file turns that expressivity fact against the stronger manuscript-facing
identification with the shared exact sparse-threshold ERM route.  Once the
lookup endpoint is still surjective on the whole exact visible surface, the
existing visible-budget obstruction applies immediately, both for the exact
family packet and for the stronger recovery packet.

So a bare finite-alphabet lookup implementation is not merely outside the
current bounded-code route.  It also cannot be identified with the already
formalized shared sparse-threshold ERM / recovery route below the same
unconditional point-block visible-budget threshold.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

universe v

section Abstract

variable {Z : Type v} [Fintype Z] {k r : ℕ}

/-- The unrestricted plug-in lookup endpoint cannot be the manuscript-facing
shared exact sparse-threshold ERM family below the point-block visible-budget
threshold. -/
theorem pluginLookupActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMData_of_lt_surfaceCard
    (zfeat : Z → BitVec r)
    (hs :
      2 * allAffinePointBlockFeatureCount (r + (k + k)) <
        Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMData
          (pluginLookupActualSwitchedLocalInterface Z k)
          zfeat) := by
  exact
    ActualSwitchedLocalInterface.not_nonempty_sharedExactZABSparseThresholdERMData_of_surjective_predict_of_lt_surfaceCard
      (T := pluginLookupActualSwitchedLocalInterface Z k)
      zfeat
      (pluginLookupActualSwitchedLocalInterface_surjective Z k)
      hs

/-- The stronger manuscript-facing sparse-threshold recovery packet is likewise
impossible on the unrestricted plug-in lookup endpoint below the same
visible-budget threshold. -/
theorem pluginLookupActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_lt_surfaceCard
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (zfeat : Z → BitVec r)
    (q : ℝ≥0∞)
    (hs :
      2 * allAffinePointBlockFeatureCount (r + (k + k)) <
        Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          μ
          (pluginLookupActualSwitchedLocalInterface Z k)
          zfeat
          q) := by
  rintro ⟨h⟩
  exact Nat.not_le_of_lt hs <|
    h.surfaceCard_le_of_surjective_predict
      (pluginLookupActualSwitchedLocalInterface_surjective Z k)

end Abstract

section BitVec

variable {n k r : ℕ}

/-- On `BitVec n`, any plug-in lookup endpoint identified with one shared exact
sparse-threshold ERM family must satisfy the same unconditional half-width
ceiling as any other surjective endpoint. -/
theorem pluginLookupActualSwitchedLocalInterface_visibleWidth_le_two_mul_extractorWidth_add_two_mul_k_succ_of_nonempty_sharedExactZABSparseThresholdERMData
    (zfeat : BitVec n → BitVec r)
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMData
          (pluginLookupActualSwitchedLocalInterface (BitVec n) k)
          zfeat)) :
    n ≤ 2 * r + 2 * k + 1 := by
  rcases h with ⟨h⟩
  exact
    h.visibleWidth_le_two_mul_extractorWidth_add_two_mul_k_succ_of_surjective_predict
      (pluginLookupActualSwitchedLocalInterface_surjective (BitVec n) k)

/-- Therefore the unrestricted plug-in lookup endpoint cannot be the
manuscript-facing shared sparse-threshold ERM family once
`2*r + 2*k + 1 < n`. -/
theorem pluginLookupActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMData_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
    (zfeat : BitVec n → BitVec r)
    (hgap : 2 * r + 2 * k + 1 < n) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMData
          (pluginLookupActualSwitchedLocalInterface (BitVec n) k)
          zfeat) := by
  exact
    ActualSwitchedLocalInterface.not_nonempty_sharedExactZABSparseThresholdERMData_of_surjective_predict_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
      (T := pluginLookupActualSwitchedLocalInterface (BitVec n) k)
      zfeat
      (pluginLookupActualSwitchedLocalInterface_surjective (BitVec n) k)
      hgap

/-- The stronger manuscript-facing sparse-threshold recovery packet inherits
the same unconditional half-width obstruction on the unrestricted plug-in
lookup endpoint. -/
theorem pluginLookupActualSwitchedLocalInterface_visibleWidth_le_two_mul_extractorWidth_add_two_mul_k_succ_of_nonempty_sharedExactZABSparseThresholdERMRecoveryData
    (μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k))
    (zfeat : BitVec n → BitVec r)
    (q : ℝ≥0∞)
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          μ
          (pluginLookupActualSwitchedLocalInterface (BitVec n) k)
          zfeat
          q)) :
    n ≤ 2 * r + 2 * k + 1 := by
  rcases h with ⟨h⟩
  exact
    h.visibleWidth_le_two_mul_extractorWidth_add_two_mul_k_succ_of_surjective_predict
      (pluginLookupActualSwitchedLocalInterface_surjective (BitVec n) k)

/-- Hence the unrestricted plug-in lookup endpoint also cannot carry the
stronger sparse-threshold recovery packet below the same unconditional
visible-budget threshold. -/
theorem pluginLookupActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
    (μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k))
    (zfeat : BitVec n → BitVec r)
    (q : ℝ≥0∞)
    (hgap : 2 * r + 2 * k + 1 < n) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          μ
          (pluginLookupActualSwitchedLocalInterface (BitVec n) k)
          zfeat
          q) := by
  exact
    ActualSwitchedLocalInterface.not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_surjective_predict_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
      (T := pluginLookupActualSwitchedLocalInterface (BitVec n) k)
      (μ := μ)
      (zfeat := zfeat)
      (q := q)
      (pluginLookupActualSwitchedLocalInterface_surjective (BitVec n) k)
      hgap

end BitVec

end Mettapedia.Computability.PNP
