import Mettapedia.Computability.PNP.CanonicalZABERMInterface

/-!
# P vs NP grassroots: exact ERM routes from projected bit-valued local data

This file specializes the final exact `z+a+b` ERM interface to a concrete class
of local extractors: coordinate projections out of a bit-valued local datum
`z : BitVec n`.

So the remaining extractor burden is reduced from “arbitrary `zfeat`” to “pick a
finite list of coordinates of `z`”.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {n r k : ℕ} {Index : Type*}

/-- Extract `r` visible summary bits from a bit-valued local datum by fixed
coordinate selection. -/
def projectedZExtractor
    (coords : Fin r → Fin n) : BitVec n → BitVec r :=
  fun z i => z (coords i)

@[simp] theorem projectedZExtractor_apply
    (coords : Fin r → Fin n) (z : BitVec n) (i : Fin r) :
    projectedZExtractor (n := n) (r := r) coords z i = z (coords i) := rfl

/-- The exact ERM-selected family induced by a fixed projection
`BitVec n → BitVec r`. -/
noncomputable def projectedZABDecisionListERMFamily
    (coords : Fin r → Fin n)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool) :
    ExactVisibleSwitchedFamily (BitVec n) k Index :=
  exactZABDecisionListERMFamily
    (Z := BitVec n) (r := r) (k := k)
    (projectedZExtractor (n := n) (r := r) coords) samples

@[simp] theorem projectedZABDecisionListERMFamily_eq
    (coords : Fin r → Fin n)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool) :
    projectedZABDecisionListERMFamily (n := n) (r := r) (k := k) (Index := Index) coords samples =
      exactZABDecisionListERMFamily
        (Z := BitVec n) (r := r) (k := k)
        (projectedZExtractor (n := n) (r := r) coords) samples := by
  rfl

structure ProjectedZABERMRecoveryData
    [Fintype (BitVec n)]
    (μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k))
    (coords : Fin r → Fin n)
    (G : ExactVisibleSwitchedFamily (BitVec n) k Index)
    (q : ℝ≥0∞) where
  samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool
  exact_family :
    G = exactZABDecisionListERMFamily
          (Z := BitVec n) (r := r) (k := k)
          (projectedZExtractor (n := n) (r := r) coords) samples
  agreement_le :
    ∀ i,
      ∀ c :
        (rawExactZABDecisionListBitFamily
          (BitVec n) r k (projectedZExtractor (n := n) (r := r) coords)).toEncodedFamily.BadCodes
            (G.predict i),
        agreementMass μ (G.predict i)
          ((rawExactZABDecisionListBitFamily
            (BitVec n) r k (projectedZExtractor (n := n) (r := r) coords)).decode c.1) ≤ q

section

variable [Fintype (BitVec n)]

def ProjectedZABERMRecoveryData.canonicalData
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {coords : Fin r → Fin n}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h : ProjectedZABERMRecoveryData
      (n := n) (r := r) (k := k) (Index := Index) μ coords G q) :
    CanonicalZABERMRecoveryData
      (Z := BitVec n) (r := r) (k := k) (Index := Index)
      μ (projectedZExtractor (n := n) (r := r) coords) G q := by
  refine ⟨h.samples, h.exact_family, h.agreement_le⟩

theorem ProjectedZABERMRecoveryData.compressionTarget
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {coords : Fin r → Fin n}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h : ProjectedZABERMRecoveryData
      (n := n) (r := r) (k := k) (Index := Index) μ coords G q) :
    ExactVisibleCompressionTarget
      (Z := BitVec n) (k := k) (Index := Index) G (r + 2 * k + 1) := by
  exact (h.canonicalData).compressionTarget

theorem ProjectedZABERMRecoveryData.finitePredictorCover
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {coords : Fin r → Fin n}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h : ProjectedZABERMRecoveryData
      (n := n) (r := r) (k := k) (Index := Index) μ coords G q) :
    G.FinitePredictorCover (2 ^ (r + 2 * k + 1)) := by
  exact (h.canonicalData).finitePredictorCover

theorem ProjectedZABERMRecoveryData.finiteIndexRepresentativeCover
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {coords : Fin r → Fin n}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h : ProjectedZABERMRecoveryData
      (n := n) (r := r) (k := k) (Index := Index) μ coords G q) :
    G.FiniteIndexRepresentativeCover (2 ^ (r + 2 * k + 1)) := by
  exact (h.canonicalData).finiteIndexRepresentativeCover

theorem ProjectedZABERMRecoveryData.finitePredictorQuotient
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {coords : Fin r → Fin n}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h : ProjectedZABERMRecoveryData
      (n := n) (r := r) (k := k) (Index := Index) μ coords G q) :
    G.FinitePredictorQuotient (2 ^ (r + 2 * k + 1)) := by
  exact (h.canonicalData).finitePredictorQuotient

omit [Fintype (BitVec n)] in
theorem projectedZABDecisionListERMCompressionTarget
    (coords : Fin r → Fin n)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool) :
    ExactVisibleCompressionTarget
      (Z := BitVec n) (k := k) (Index := Index)
      (projectedZABDecisionListERMFamily (n := n) (r := r) (k := k) (Index := Index) coords samples)
      (r + 2 * k + 1) := by
  simpa [projectedZABDecisionListERMFamily] using
    (exactZABDecisionListERMCompressionTarget_twoMul
      (Z := BitVec n) (r := r) (k := k) (Index := Index)
      (projectedZExtractor (n := n) (r := r) coords) samples)

omit [Fintype (BitVec n)] in
theorem projectedZABDecisionListERMCandidateData
    (coords : Fin r → Fin n)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool) :
    CanonicalZABDecisionListCandidateData
      (Z := BitVec n) (r := r) (k := k) (Index := Index)
      (projectedZExtractor (n := n) (r := r) coords)
      (projectedZABDecisionListERMFamily (n := n) (r := r) (k := k) (Index := Index) coords samples) := by
  simpa [projectedZABDecisionListERMFamily] using
    (canonicalZABDecisionListERMCandidateData
      (Z := BitVec n) (r := r) (k := k) (Index := Index)
      (projectedZExtractor (n := n) (r := r) coords) samples)

omit [Fintype (BitVec n)] in
theorem projectedZABDecisionListERMTargetData
    (coords : Fin r → Fin n)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool) :
    ExactZABDecisionListTargetData
      (Z := BitVec n) (r := r) (k := k) (Index := Index)
      (projectedZExtractor (n := n) (r := r) coords)
      (projectedZABDecisionListERMFamily (n := n) (r := r) (k := k) (Index := Index) coords samples) := by
  exact
    (projectedZABDecisionListERMCandidateData
      (n := n) (r := r) (k := k) (Index := Index) coords samples).targetData

omit [Fintype (BitVec n)] in
theorem projectedZABDecisionListERMFinitePredictorCover
    (coords : Fin r → Fin n)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool) :
    (projectedZABDecisionListERMFamily
      (n := n) (r := r) (k := k) (Index := Index) coords samples).FinitePredictorCover
      (2 ^ (r + 2 * k + 1)) := by
  exact
    (projectedZABDecisionListERMCandidateData
      (n := n) (r := r) (k := k) (Index := Index) coords samples).finitePredictorCover

omit [Fintype (BitVec n)] in
theorem projectedZABDecisionListERMFiniteIndexRepresentativeCover
    (coords : Fin r → Fin n)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool) :
    (projectedZABDecisionListERMFamily
      (n := n) (r := r) (k := k) (Index := Index) coords samples).FiniteIndexRepresentativeCover
      (2 ^ (r + 2 * k + 1)) := by
  exact
    (projectedZABDecisionListERMCandidateData
      (n := n) (r := r) (k := k) (Index := Index) coords samples).finiteIndexRepresentativeCover

omit [Fintype (BitVec n)] in
theorem projectedZABDecisionListERMFinitePredictorQuotient
    (coords : Fin r → Fin n)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool) :
    (projectedZABDecisionListERMFamily
      (n := n) (r := r) (k := k) (Index := Index) coords samples).FinitePredictorQuotient
      (2 ^ (r + 2 * k + 1)) := by
  exact
    (projectedZABDecisionListERMCandidateData
      (n := n) (r := r) (k := k) (Index := Index) coords samples).finitePredictorQuotient

theorem projectedZABDecisionListERMFamily_surfaceCard_le_of_surjective_predict
    (coords : Fin r → Fin n)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool)
    (hsurj :
      Function.Surjective
        (projectedZABDecisionListERMFamily
          (n := n) (r := r) (k := k) (Index := Index) coords samples).predict) :
    Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k) ≤ r + 2 * k + 1 := by
  exact
    (projectedZABDecisionListERMCandidateData
      (n := n) (r := r) (k := k) (Index := Index) coords samples).surfaceCard_le_of_surjective_predict
      hsurj

theorem projectedZABDecisionListERMFamily_not_surjective_of_lt_surfaceCard
    (coords : Fin r → Fin n)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool)
    (hs : r + 2 * k + 1 < Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k)) :
    ¬ Function.Surjective
        (projectedZABDecisionListERMFamily
          (n := n) (r := r) (k := k) (Index := Index) coords samples).predict := by
  exact
    (projectedZABDecisionListERMCandidateData
      (n := n) (r := r) (k := k) (Index := Index) coords samples).not_surjective_predict_of_lt_surfaceCard
      hs

theorem ProjectedZABERMRecoveryData.surfaceCard_le_of_surjective_predict
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {coords : Fin r → Fin n}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h : ProjectedZABERMRecoveryData
      (n := n) (r := r) (k := k) (Index := Index) μ coords G q)
    (hsurj : Function.Surjective G.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k) ≤ r + 2 * k + 1 := by
  exact (h.canonicalData).surfaceCard_le_of_surjective_predict hsurj

theorem ProjectedZABERMRecoveryData.not_surjective_predict_of_lt_surfaceCard
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {coords : Fin r → Fin n}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h : ProjectedZABERMRecoveryData
      (n := n) (r := r) (k := k) (Index := Index) μ coords G q)
    (hs : r + 2 * k + 1 < Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k)) :
    ¬ Function.Surjective G.predict := by
  exact (h.canonicalData).not_surjective_predict_of_lt_surfaceCard hs

theorem ProjectedZABERMRecoveryData.recoveryLowerBound
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {coords : Fin r → Fin n}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h : ProjectedZABERMRecoveryData
      (n := n) (r := r) (k := k) (Index := Index) μ coords G q)
    (i : Index) (m : ℕ) :
    1 - (2 ^ (r + 2 * k + 1) : ℝ≥0∞) * q ^ m ≤
      (rawExactZABDecisionListBitFamily
        (BitVec n) r k (projectedZExtractor (n := n) (r := r) coords)).bitExactRecoverySampleMass
        μ (G.predict i) m := by
  exact (h.canonicalData).recoveryLowerBound i m

end

end

end Mettapedia.Computability.PNP
