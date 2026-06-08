import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoveryData

/-!
# P vs NP route obstruction: manuscript-facing sparse-threshold recovery packets
  force pairwise `q`-separation among distinct realized predictors

`ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoveryData` identifies the
actual switched family with one fixed shared exact sparse-threshold bit family
and then assumes that every bad code against each realized target has agreement
mass at most `q`.

This has an immediate route-facing consequence that is stronger than the bare
bit-budget wrappers: any other *distinct realized predictor* is itself such a
bad code.  Therefore every pair of distinct realized predictors must already
have mutual agreement mass at most `q`.

So if the actual switched family contains even one distinct realized pair whose
agreement mass exceeds `q`, the manuscript-facing recovery packet is impossible,
without any appeal to surjectivity or to the finite predictor-image budget.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

universe u v w

namespace ActualSwitchedLocalInterface

section Abstract

variable {Z : Type v} [Fintype Z] {k r : ℕ} {Index : Type u} {Block : Type w}
variable {T : ActualSwitchedLocalInterface Z k Index Block}
variable {μ : PMF (ExactVisiblePostSwitchSurface Z k)} {zfeat : Z → BitVec r}
variable {q : ℝ≥0∞}

/-- Any two distinct realized predictors in a manuscript-facing sparse-threshold
recovery packet already have agreement mass at most `q`. -/
theorem SharedExactZABSparseThresholdERMRecoveryData.agreementMass_le_of_predict_ne
    (h : SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q)
    (i j : Index)
    (hij : T.predictorFamily.predict j ≠ T.predictorFamily.predict i) :
    agreementMass μ (T.predictorFamily.predict i) (T.predictorFamily.predict j) ≤ q := by
  rcases h.data.targetData.realized j with ⟨code, hcode⟩
  let c :
      (sharedExactZABSparseThresholdAffineBitFamily
        Z
        zfeat
        (allAffinePointBlockFeatures (r + (k + k)))).toEncodedFamily.BadCodes
          (T.predictorFamily.predict i) :=
    ⟨sharedSparseThresholdCodeEquivBitCode
        (allAffinePointBlockFeatureCount (r + (k + k))) code,
      by
        intro hsame
        apply hij
        calc
          T.predictorFamily.predict j
              = (sharedExactZABSparseThresholdAffineBitFamily
                  Z
                  zfeat
                  (allAffinePointBlockFeatures (r + (k + k)))).decode
                  (sharedSparseThresholdCodeEquivBitCode
                    (allAffinePointBlockFeatureCount (r + (k + k))) code) := by
                    rw [sharedExactZABSparseThresholdAffineBitFamily_decode_code]
                    exact hcode
          _ = T.predictorFamily.predict i := hsame⟩
  simpa [c, hcode] using h.agreement_le i c

/-- Therefore any actual switched family that contains a distinct realized pair
with agreement mass `> q` cannot carry the manuscript-facing sparse-threshold
recovery packet. -/
theorem not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_lt_agreementMass_of_predict_ne
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (zfeat : Z → BitVec r)
    (i j : Index)
    (hij : T.predictorFamily.predict j ≠ T.predictorFamily.predict i)
    (hgap : q < agreementMass μ (T.predictorFamily.predict i) (T.predictorFamily.predict j)) :
    ¬ Nonempty (SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q) := by
  rintro ⟨h⟩
  exact not_le_of_gt hgap (h.agreementMass_le_of_predict_ne i j hij)

end Abstract

end ActualSwitchedLocalInterface

end Mettapedia.Computability.PNP
