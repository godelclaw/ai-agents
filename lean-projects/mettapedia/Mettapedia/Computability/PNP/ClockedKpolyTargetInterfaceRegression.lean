import Mettapedia.Computability.PNP.ClockedKpolyTargetInterface

/-!
# Regression checks for the clocked `Kpoly` target interface

These wrappers pin the implication from an exact post-switch bit-budget witness
to the abstract clocked recovery kernel.  They still do not assert that the
manuscript decoder satisfies such a witness.
-/

namespace Mettapedia.Computability.PNP.ClockedKpolyTargetInterfaceRegression

open Mettapedia.Computability.PNP

universe u v

theorem indexed_clockedBitCodeFamilyOfHasBitBudget_realizes_regression
    {Index : Type u} {Input : Type v} {s clock : ℕ}
    {G : IndexedPredictorFamily Index Input}
    (h : G.HasBitBudget s) (i : Index) :
    (IndexedPredictorFamily.clockedBitCodeFamilyOfHasBitBudget
      (G := G) (s := s) clock h).Realizes (G.predict i) := by
  exact IndexedPredictorFamily.clockedBitCodeFamilyOfHasBitBudget_realizes
    (G := G) (s := s) clock h i

theorem indexed_clockedBitCodeFamilyOfHasBitBudget_underlying_realizes_regression
    {Index : Type u} {Input : Type v} {s clock : ℕ}
    {G : IndexedPredictorFamily Index Input}
    (h : G.HasBitBudget s) :
    G.RealizedByBitFamily
      (IndexedPredictorFamily.clockedBitCodeFamilyOfHasBitBudget
        (G := G) (s := s) clock h).toBitEncodedClassifierFamily := by
  exact IndexedPredictorFamily.clockedBitCodeFamilyOfHasBitBudget_underlying_realizes
    (G := G) (s := s) clock h

theorem indexed_clockedBitCodeFamilyOfHasBitBudget_hasBitBudget_regression
    {Index : Type u} {Input : Type v} {s clock : ℕ}
    {G : IndexedPredictorFamily Index Input}
    (h : G.HasBitBudget s) :
    G.HasBitBudget s := by
  exact IndexedPredictorFamily.clockedBitCodeFamilyOfHasBitBudget_hasBitBudget
    (G := G) (s := s) clock h

theorem indexed_exactRecoveryRate_ge_one_sub_uniformMissRatio_pow_of_hasBitBudget_regression
    {Index : Type u} {Input : Type v} [Fintype Input] [Nonempty Input]
    {s clock : ℕ}
    {G : IndexedPredictorFamily Index Input}
    (h : G.HasBitBudget s) (i : Index) (m : ℕ) :
    1 - (2 ^ s : ℚ) * uniformMissRatio Input ^ m ≤
      (IndexedPredictorFamily.clockedBitCodeFamilyOfHasBitBudget
        (G := G) (s := s) clock h).exactRecoveryRate (G.predict i) m := by
  exact
    IndexedPredictorFamily.exactRecoveryRate_ge_one_sub_uniformMissRatio_pow_of_hasBitBudget
      (G := G) (s := s) clock h i m

theorem indexed_nondeceptiveRate_ge_one_sub_uniformMissRatio_pow_of_hasBitBudget_regression
    {Index : Type u} {Input : Type v} [Fintype Input] [Nonempty Input]
    {s clock : ℕ}
    {G : IndexedPredictorFamily Index Input}
    (h : G.HasBitBudget s) (i : Index) (m : ℕ) :
    1 - (2 ^ s : ℚ) * uniformMissRatio Input ^ m ≤
      (IndexedPredictorFamily.clockedBitCodeFamilyOfHasBitBudget
        (G := G) (s := s) clock h).nondeceptiveRate (G.predict i) m := by
  exact
    IndexedPredictorFamily.nondeceptiveRate_ge_one_sub_uniformMissRatio_pow_of_hasBitBudget
      (G := G) (s := s) clock h i m

theorem exact_visible_exactRecoveryRate_ge_one_sub_uniformMissRatio_pow_regression
    {Z : Type*} [Fintype Z] [Nonempty Z]
    {k s clock : ℕ} {Index : Type u}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h : ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s)
    (i : Index) (m : ℕ) :
    1 - (2 ^ s : ℚ) * uniformMissRatio (ExactVisiblePostSwitchSurface Z k) ^ m ≤
      (IndexedPredictorFamily.clockedBitCodeFamilyOfHasBitBudget
        (G := G) (s := s) clock h).exactRecoveryRate (G.predict i) m := by
  exact
    exactRecoveryRate_ge_one_sub_uniformMissRatio_pow_of_exactVisibleCompressionTarget
      (Z := Z) (k := k) (s := s) (clock := clock) (Index := Index) h i m

theorem exact_visible_nondeceptiveRate_ge_one_sub_uniformMissRatio_pow_regression
    {Z : Type*} [Fintype Z] [Nonempty Z]
    {k s clock : ℕ} {Index : Type u}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h : ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s)
    (i : Index) (m : ℕ) :
    1 - (2 ^ s : ℚ) * uniformMissRatio (ExactVisiblePostSwitchSurface Z k) ^ m ≤
      (IndexedPredictorFamily.clockedBitCodeFamilyOfHasBitBudget
        (G := G) (s := s) clock h).nondeceptiveRate (G.predict i) m := by
  exact
    nondeceptiveRate_ge_one_sub_uniformMissRatio_pow_of_exactVisibleCompressionTarget
      (Z := Z) (k := k) (s := s) (clock := clock) (Index := Index) h i m

theorem indexed_exists_nondeceptiveSample_of_bitBudget_bound_lt_of_hasBitBudget_regression
    {Index : Type u} {Input : Type v} [Fintype Input]
    {s clock : ℕ}
    {G : IndexedPredictorFamily Index Input}
    (h : G.HasBitBudget s) (i : Index) (m : ℕ)
    (hbound :
      2 ^ s * (Fintype.card Input - 1) ^ m <
        Fintype.card Input ^ m) :
    ∃ sample : PointSample Input m,
      ¬ EncodedFamily.IsDeceptiveSample
          (BitEncodedClassifierFamily.toEncodedFamily
            (ClockedBitCodeFamily.toBitEncodedClassifierFamily
              (IndexedPredictorFamily.clockedBitCodeFamilyOfHasBitBudget
                (G := G) (s := s) clock h)))
          (G.predict i) sample := by
  exact
    IndexedPredictorFamily.exists_nondeceptiveSample_of_bitBudget_bound_lt_of_hasBitBudget
      (G := G) (s := s) clock h i m hbound

theorem indexed_exists_sample_empiricalRiskPredictor_eq_target_of_bitBudget_bound_lt_regression
    {Index : Type u} {Input : Type v} [Fintype Input]
    {s clock : ℕ}
    {G : IndexedPredictorFamily Index Input}
    (h : G.HasBitBudget s) (i : Index) (m : ℕ)
    (hbound :
      2 ^ s * (Fintype.card Input - 1) ^ m <
        Fintype.card Input ^ m) :
    ∃ sample : PointSample Input m,
      ClockedBitCodeFamily.empiricalRiskPredictor
          (IndexedPredictorFamily.clockedBitCodeFamilyOfHasBitBudget
            (G := G) (s := s) clock h)
          (labeledByTarget (G.predict i) sample) =
        G.predict i := by
  exact
    IndexedPredictorFamily.exists_sample_empiricalRiskPredictor_eq_target_of_bitBudget_bound_lt_of_hasBitBudget
      (G := G) (s := s) clock h i m hbound

theorem exact_visible_exists_nondeceptiveSample_of_bitBudget_bound_lt_regression
    {Z : Type*} [Fintype Z]
    {k s clock : ℕ} {Index : Type u}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h : ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s)
    (i : Index) (m : ℕ)
    (hbound :
      2 ^ s * (Fintype.card (ExactVisiblePostSwitchSurface Z k) - 1) ^ m <
        Fintype.card (ExactVisiblePostSwitchSurface Z k) ^ m) :
    ∃ sample : PointSample (ExactVisiblePostSwitchSurface Z k) m,
      ¬ EncodedFamily.IsDeceptiveSample
          (BitEncodedClassifierFamily.toEncodedFamily
            (ClockedBitCodeFamily.toBitEncodedClassifierFamily
              (IndexedPredictorFamily.clockedBitCodeFamilyOfHasBitBudget
                (G := G) (s := s) clock h)))
          (G.predict i) sample := by
  exact
    exists_nondeceptiveSample_of_bitBudget_bound_lt_of_exactVisibleCompressionTarget
      (Z := Z) (k := k) (s := s) (clock := clock) (Index := Index) h i m hbound

theorem exact_visible_exists_sample_empiricalRiskPredictor_eq_target_of_bitBudget_bound_lt_regression
    {Z : Type*} [Fintype Z]
    {k s clock : ℕ} {Index : Type u}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h : ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s)
    (i : Index) (m : ℕ)
    (hbound :
      2 ^ s * (Fintype.card (ExactVisiblePostSwitchSurface Z k) - 1) ^ m <
        Fintype.card (ExactVisiblePostSwitchSurface Z k) ^ m) :
    ∃ sample : PointSample (ExactVisiblePostSwitchSurface Z k) m,
      ClockedBitCodeFamily.empiricalRiskPredictor
          (IndexedPredictorFamily.clockedBitCodeFamilyOfHasBitBudget
            (G := G) (s := s) clock h)
          (labeledByTarget (G.predict i) sample) =
        G.predict i := by
  exact
    exists_sample_empiricalRiskPredictor_eq_target_of_bitBudget_bound_lt_of_exactVisibleCompressionTarget
      (Z := Z) (k := k) (s := s) (clock := clock) (Index := Index) h i m hbound

end Mettapedia.Computability.PNP.ClockedKpolyTargetInterfaceRegression
