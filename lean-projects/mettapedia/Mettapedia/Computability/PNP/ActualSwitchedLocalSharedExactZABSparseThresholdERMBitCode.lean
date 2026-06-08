import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMData
import Mettapedia.Computability.PNP.ActualSwitchedLocalStructure

/-!
# P vs NP route bridge: actual switched-local point-block sparse-threshold ERM bit code

`ActualSwitchedLocalSharedExactZABSparseThresholdERMData` already packages the
manuscript-facing claim that one actual switched-local family is exactly one
shared exact sparse-threshold ERM family on the point-block basis.

This file extracts the simpler bounded-code consequences that require no
recovery-side agreement estimate.  The ERM-selected code itself is the witness:
once the actual family is exactly the point-block shared sparse-threshold ERM
family, the actual local rules are already selected from one fixed
`2 * allAffinePointBlockFeatureCount (r + 2*k)`-bit family.

So exact-family identification alone closes the actual-local bounded-code
interface, and therefore the finite predictor-image and clocked `Kpoly`
payloads, even before any recovery argument is supplied.
-/

namespace Mettapedia.Computability.PNP

universe u v w

namespace ActualSwitchedLocalInterface

variable {Z : Type v} {k : ℕ} {Index : Type u} {Block : Type w}

namespace SharedExactZABSparseThresholdERMData

variable {T : ActualSwitchedLocalInterface Z k Index Block} {r : ℕ}
variable {zfeat : Z → BitVec r}

/-- Exact identification with the point-block shared sparse-threshold ERM
family already yields the bounded-code actual-local interface: the witness code
for each index is the same sparse-threshold ERM code already exposed by the
exact-visible target-data witness. -/
noncomputable def bitCodeData
    (h : SharedExactZABSparseThresholdERMData T zfeat) :
    BitCodeData T
      (2 * allAffinePointBlockFeatureCount (r + (k + k))) where
  codeFamily :=
    sharedExactZABSparseThresholdAffineBitFamily
      Z
      zfeat
      (allAffinePointBlockFeatures (r + (k + k)))
  realized := by
    intro i
    rcases h.targetData.realized i with ⟨code, hcode⟩
    refine ⟨sharedSparseThresholdCodeEquivBitCode
      (allAffinePointBlockFeatureCount (r + (k + k))) code, ?_⟩
    have hlocal :
        T.localRule i =
          sharedExactZABSparseThresholdAffinePredict
            (Z := Z)
            (p := allAffinePointBlockFeatureCount (r + (k + k)))
            (r := r) (k := k)
            zfeat
            (allAffinePointBlockFeatures (r + (k + k)))
            code := by
      simpa [ActualSwitchedLocalInterface.predictorFamily] using hcode
    exact
      (sharedExactZABSparseThresholdAffineBitFamily_decode_code
        (Z := Z)
        (p := allAffinePointBlockFeatureCount (r + (k + k)))
        (r := r) (k := k)
        zfeat
        (allAffinePointBlockFeatures (r + (k + k)))
        code).trans hlocal.symm

theorem compressionTarget
    (h : SharedExactZABSparseThresholdERMData T zfeat) :
    ExactVisibleCompressionTarget
      (Z := Z) (k := k) (Index := Index)
      T.predictorFamily
      (2 * allAffinePointBlockFeatureCount (r + (k + k))) := by
  exact h.bitCodeData.exactVisibleCompressionTarget

theorem finitePredictorCover
    (h : SharedExactZABSparseThresholdERMData T zfeat) :
    T.predictorFamily.FinitePredictorCover
      (2 ^ (2 * allAffinePointBlockFeatureCount (r + (k + k)))) := by
  exact h.bitCodeData.finitePredictorCover

theorem finiteIndexRepresentativeCover
    (h : SharedExactZABSparseThresholdERMData T zfeat) :
    T.predictorFamily.FiniteIndexRepresentativeCover
      (2 ^ (2 * allAffinePointBlockFeatureCount (r + (k + k)))) := by
  exact h.bitCodeData.finiteIndexRepresentativeCover

theorem finitePredictorQuotient
    (h : SharedExactZABSparseThresholdERMData T zfeat) :
    T.predictorFamily.FinitePredictorQuotient
      (2 ^ (2 * allAffinePointBlockFeatureCount (r + (k + k)))) := by
  exact h.bitCodeData.finitePredictorQuotient

theorem clockedKpolyFiniteLearningPayload
    [Fintype Z]
    {clock : ℕ}
    (h : SharedExactZABSparseThresholdERMData T zfeat) :
    ClockedKpolyFiniteLearningPayload
      T.predictorFamily
      (2 * allAffinePointBlockFeatureCount (r + (k + k)))
      clock := by
  exact h.bitCodeData.clockedKpolyFiniteLearningPayload

end SharedExactZABSparseThresholdERMData

end ActualSwitchedLocalInterface

end Mettapedia.Computability.PNP
