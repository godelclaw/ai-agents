import Mettapedia.Computability.PNP.ClockedKpolyBridge
import Mettapedia.Computability.PNP.ExactSwitchedFamily

/-!
# PNP clocked `Kpoly` target interface

This file connects the abstract clocked counting kernel to the existing exact
post-switch compression target surface.

The result is still conservative.  It does not prove that the manuscript's
decoder satisfies any exact visible compression target.  Instead it states the
next honest implication:

* once an indexed predictor family is known to have an `s`-bit exact budget,
* it can be viewed as a clocked `s`-bit family for any chosen clock bound, and
* the finite-uniform recovery inequalities from `ClockedKpolyBridge.lean`
  apply to each realized predictor in that family.
-/

namespace Mettapedia.Computability.PNP

universe u v

noncomputable section

namespace IndexedPredictorFamily

variable {Index : Type u} {Input : Type v} {s clock : ℕ}
variable {G : IndexedPredictorFamily Index Input}

/-- Repackage any exact `s`-bit budget witness as a clocked `s`-bit family with
an arbitrary external clock parameter. -/
def clockedBitCodeFamilyOfHasBitBudget
    (clock : ℕ) (h : G.HasBitBudget s) : ClockedBitCodeFamily Input s clock :=
  ClockedBitCodeFamily.ofBitEncodedClassifierFamily clock (Classical.choose h)

/-- Every predictor in a family with an exact `s`-bit budget is realized by the
associated clocked family. -/
theorem clockedBitCodeFamilyOfHasBitBudget_realizes
    (clock : ℕ) (h : G.HasBitBudget s) (i : Index) :
    (clockedBitCodeFamilyOfHasBitBudget (G := G) (s := s) clock h).Realizes (G.predict i) := by
  rcases (Classical.choose_spec h) i with ⟨code, hcode⟩
  exact ⟨code, hcode⟩

/-- The underlying bit-family of the constructed clocked family is itself a
witness for the original exact bit budget. -/
theorem clockedBitCodeFamilyOfHasBitBudget_underlying_realizes
    (clock : ℕ) (h : G.HasBitBudget s) :
    G.RealizedByBitFamily
      (clockedBitCodeFamilyOfHasBitBudget (G := G) (s := s) clock h).toBitEncodedClassifierFamily := by
  intro i
  exact clockedBitCodeFamilyOfHasBitBudget_realizes
    (G := G) (s := s) clock h i

/-- The constructed clocked family re-witnesses the original exact bit budget
after forgetting the clock. -/
theorem clockedBitCodeFamilyOfHasBitBudget_hasBitBudget
    (clock : ℕ) (h : G.HasBitBudget s) :
    G.HasBitBudget s := by
  exact
    ⟨(clockedBitCodeFamilyOfHasBitBudget
        (G := G) (s := s) clock h).toBitEncodedClassifierFamily,
      clockedBitCodeFamilyOfHasBitBudget_underlying_realizes
        (G := G) (s := s) clock h⟩

/-- Therefore any exact `s`-bit budget witness yields the generic finite-uniform
recovery lower bound for every indexed predictor. -/
theorem exactRecoveryRate_ge_one_sub_uniformMissRatio_pow_of_hasBitBudget
    [Fintype Input] [Nonempty Input]
    (clock : ℕ) (h : G.HasBitBudget s) (i : Index) (m : ℕ) :
    1 - (2 ^ s : ℚ) * uniformMissRatio Input ^ m ≤
      (clockedBitCodeFamilyOfHasBitBudget (G := G) (s := s) clock h).exactRecoveryRate
        (G.predict i) m := by
  exact
    ClockedBitCodeFamily.exactRecoveryRate_ge_one_sub_uniformMissRatio_pow
      (F := clockedBitCodeFamilyOfHasBitBudget (G := G) (s := s) clock h)
      (target := G.predict i) (m := m)
      (clockedBitCodeFamilyOfHasBitBudget_realizes
        (G := G) (s := s) clock h i)

/-- Any exact `s`-bit budget witness also yields the target-independent
non-deceptive-rate lower bound for every indexed predictor. -/
theorem nondeceptiveRate_ge_one_sub_uniformMissRatio_pow_of_hasBitBudget
    [Fintype Input] [Nonempty Input]
    (clock : ℕ) (h : G.HasBitBudget s) (i : Index) (m : ℕ) :
    1 - (2 ^ s : ℚ) * uniformMissRatio Input ^ m ≤
      (clockedBitCodeFamilyOfHasBitBudget (G := G) (s := s) clock h).nondeceptiveRate
        (G.predict i) m := by
  exact
    ClockedBitCodeFamily.nondeceptiveRate_ge_one_sub_uniformMissRatio_pow
      (F := clockedBitCodeFamilyOfHasBitBudget (G := G) (s := s) clock h)
      (target := G.predict i) (m := m)

/-- Positivity form of the same implication. -/
theorem exactRecoveryRate_pos_of_bitBudget_uniformMissRatio_pow_lt_one_of_hasBitBudget
    [Fintype Input] [Nonempty Input]
    (clock : ℕ) (h : G.HasBitBudget s) (i : Index) (m : ℕ)
    (hlt : (2 ^ s : ℚ) * uniformMissRatio Input ^ m < 1) :
    0 <
      (clockedBitCodeFamilyOfHasBitBudget (G := G) (s := s) clock h).exactRecoveryRate
        (G.predict i) m := by
  exact
    ClockedBitCodeFamily.exactRecoveryRate_pos_of_bitBudget_uniformMissRatio_pow_lt_one
      (F := clockedBitCodeFamilyOfHasBitBudget (G := G) (s := s) clock h)
      (target := G.predict i) (m := m)
      (clockedBitCodeFamilyOfHasBitBudget_realizes
        (G := G) (s := s) clock h i)
      hlt

/-- Positivity form of the non-deceptive-rate implication. -/
theorem nondeceptiveRate_pos_of_bitBudget_uniformMissRatio_pow_lt_one_of_hasBitBudget
    [Fintype Input] [Nonempty Input]
    (clock : ℕ) (h : G.HasBitBudget s) (i : Index) (m : ℕ)
    (hlt : (2 ^ s : ℚ) * uniformMissRatio Input ^ m < 1) :
    0 <
      (clockedBitCodeFamilyOfHasBitBudget (G := G) (s := s) clock h).nondeceptiveRate
        (G.predict i) m := by
  exact
    ClockedBitCodeFamily.nondeceptiveRate_pos_of_bitBudget_uniformMissRatio_pow_lt_one
      (F := clockedBitCodeFamilyOfHasBitBudget (G := G) (s := s) clock h)
      (target := G.predict i) (m := m) hlt

/-- Any exact `s`-bit budget witness gives an explicit non-deceptive point
sample below the finite-counting threshold. -/
theorem exists_nondeceptiveSample_of_bitBudget_bound_lt_of_hasBitBudget
    [Fintype Input]
    (clock : ℕ) (h : G.HasBitBudget s) (i : Index) (m : ℕ)
    (hbound :
      2 ^ s * (Fintype.card Input - 1) ^ m <
        Fintype.card Input ^ m) :
    ∃ sample : PointSample Input m,
      ¬ EncodedFamily.IsDeceptiveSample
          (BitEncodedClassifierFamily.toEncodedFamily
            (ClockedBitCodeFamily.toBitEncodedClassifierFamily
              (clockedBitCodeFamilyOfHasBitBudget (G := G) (s := s) clock h)))
          (G.predict i) sample := by
  exact
    ClockedBitCodeFamily.exists_nondeceptiveSample_of_bitBudget_bound_lt
      (F := clockedBitCodeFamilyOfHasBitBudget (G := G) (s := s) clock h)
      (target := G.predict i) (m := m) hbound

/-- Any exact `s`-bit budget witness gives an explicit point sample where ERM
over the associated clocked family exactly recovers each indexed predictor. -/
theorem exists_sample_empiricalRiskPredictor_eq_target_of_bitBudget_bound_lt_of_hasBitBudget
    [Fintype Input]
    (clock : ℕ) (h : G.HasBitBudget s) (i : Index) (m : ℕ)
    (hbound :
      2 ^ s * (Fintype.card Input - 1) ^ m <
        Fintype.card Input ^ m) :
    ∃ sample : PointSample Input m,
      ClockedBitCodeFamily.empiricalRiskPredictor
          (clockedBitCodeFamilyOfHasBitBudget (G := G) (s := s) clock h)
          (labeledByTarget (G.predict i) sample) =
        G.predict i := by
  exact
    ClockedBitCodeFamily.exists_sample_empiricalRiskPredictor_eq_target_of_bitBudget_bound_lt
      (F := clockedBitCodeFamilyOfHasBitBudget (G := G) (s := s) clock h)
      (target := G.predict i) (m := m)
      (clockedBitCodeFamilyOfHasBitBudget_realizes
        (G := G) (s := s) clock h i)
      hbound

end IndexedPredictorFamily

section ExactPostSwitch

variable {Z : Type*} {k s clock : ℕ} {Index : Type*}
variable {G : ExactVisibleSwitchedFamily Z k Index}

local instance exactVisiblePostSwitchSurfaceNonempty [Nonempty Z] :
    Nonempty (ExactVisiblePostSwitchSurface Z k) :=
  ⟨⟨Classical.choice ‹Nonempty Z›, zeroVec, zeroVec⟩⟩

/-- Any exact visible compression target can be viewed as a clocked family
realizing every exact switched predictor. -/
theorem exactRecoveryRate_ge_one_sub_uniformMissRatio_pow_of_exactVisibleCompressionTarget
    [Fintype Z] [Nonempty Z]
    (h : ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s)
    (i : Index) (m : ℕ) :
    1 - (2 ^ s : ℚ) * uniformMissRatio (ExactVisiblePostSwitchSurface Z k) ^ m ≤
      (IndexedPredictorFamily.clockedBitCodeFamilyOfHasBitBudget
          (G := G) (s := s) clock h).exactRecoveryRate (G.predict i) m := by
  exact
    IndexedPredictorFamily.exactRecoveryRate_ge_one_sub_uniformMissRatio_pow_of_hasBitBudget
      (G := G) (s := s) clock h i m

/-- Any exact visible compression target also gives the matching
non-deceptive-rate lower bound for every exact switched predictor. -/
theorem nondeceptiveRate_ge_one_sub_uniformMissRatio_pow_of_exactVisibleCompressionTarget
    [Fintype Z] [Nonempty Z]
    (h : ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s)
    (i : Index) (m : ℕ) :
    1 - (2 ^ s : ℚ) * uniformMissRatio (ExactVisiblePostSwitchSurface Z k) ^ m ≤
      (IndexedPredictorFamily.clockedBitCodeFamilyOfHasBitBudget
          (G := G) (s := s) clock h).nondeceptiveRate (G.predict i) m := by
  exact
    IndexedPredictorFamily.nondeceptiveRate_ge_one_sub_uniformMissRatio_pow_of_hasBitBudget
      (G := G) (s := s) clock h i m

/-- Positivity form on the exact visible post-switch surface. -/
theorem exactRecoveryRate_pos_of_bitBudget_uniformMissRatio_pow_lt_one_of_exactVisibleCompressionTarget
    [Fintype Z] [Nonempty Z]
    (h : ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s)
    (i : Index) (m : ℕ)
    (hlt :
      (2 ^ s : ℚ) * uniformMissRatio (ExactVisiblePostSwitchSurface Z k) ^ m < 1) :
    0 <
      (IndexedPredictorFamily.clockedBitCodeFamilyOfHasBitBudget
          (G := G) (s := s) clock h).exactRecoveryRate (G.predict i) m := by
  exact
    IndexedPredictorFamily.exactRecoveryRate_pos_of_bitBudget_uniformMissRatio_pow_lt_one_of_hasBitBudget
      (G := G) (s := s) clock h i m hlt

/-- Non-deceptive-rate positivity form on the exact visible post-switch
surface. -/
theorem nondeceptiveRate_pos_of_bitBudget_uniformMissRatio_pow_lt_one_of_exactVisibleCompressionTarget
    [Fintype Z] [Nonempty Z]
    (h : ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s)
    (i : Index) (m : ℕ)
    (hlt :
      (2 ^ s : ℚ) * uniformMissRatio (ExactVisiblePostSwitchSurface Z k) ^ m < 1) :
    0 <
      (IndexedPredictorFamily.clockedBitCodeFamilyOfHasBitBudget
          (G := G) (s := s) clock h).nondeceptiveRate (G.predict i) m := by
  exact
    IndexedPredictorFamily.nondeceptiveRate_pos_of_bitBudget_uniformMissRatio_pow_lt_one_of_hasBitBudget
      (G := G) (s := s) clock h i m hlt

/-- Exact visible compression supplies an explicit non-deceptive point sample
below the finite-counting threshold. -/
theorem exists_nondeceptiveSample_of_bitBudget_bound_lt_of_exactVisibleCompressionTarget
    [Fintype Z]
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
    IndexedPredictorFamily.exists_nondeceptiveSample_of_bitBudget_bound_lt_of_hasBitBudget
      (G := G) (s := s) clock h i m hbound

/-- Exact visible compression supplies an explicit point sample where ERM over
the associated clocked family exactly recovers each exact switched predictor. -/
theorem exists_sample_empiricalRiskPredictor_eq_target_of_bitBudget_bound_lt_of_exactVisibleCompressionTarget
    [Fintype Z]
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
    IndexedPredictorFamily.exists_sample_empiricalRiskPredictor_eq_target_of_bitBudget_bound_lt_of_hasBitBudget
      (G := G) (s := s) clock h i m hbound

end ExactPostSwitch

end

end Mettapedia.Computability.PNP
