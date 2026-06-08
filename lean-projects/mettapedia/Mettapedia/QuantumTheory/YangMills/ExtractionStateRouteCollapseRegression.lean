import Mettapedia.QuantumTheory.YangMills.ExtractionStateRouteCollapse

/-!
# Yang-Mills Extraction-State Route Collapse Regression

Regression wrappers and concrete examples for the odd-cutoff route-collapse
surface.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills

/-- Simple odd-vanishing coefficient family concentrated at canonical
dimension `14`. -/
def sampleOddVanishingCoeffs : DimensionCoefficients ℤ :=
  fun n => if n = 14 then 3 else 0

theorem sampleOddVanishingCoeffs_vanishesOnOddDimensions :
    VanishesOnOddDimensions sampleOddVanishingCoeffs := by
  intro n hodd
  have hne : n ≠ 14 := by
    intro h
    subst h
    norm_num at hodd
  simp [sampleOddVanishingCoeffs, hne]

/-- Coefficient family whose odd-dimensional `15` term really distinguishes the
two cutoffs.  This is the negative regression showing that the collapse uses
the manuscript's odd-vanishing premise. -/
def sampleOddSensitiveCoeffs : DimensionCoefficients ℤ :=
  fun n => if n = 15 then 1 else 0

/-- A sample route witness that reads only the extracted/remainder state. -/
def sampleExtractionStateWitness (state : ExtractionState ℤ) : Prop :=
  state.1 14 = 3 ∧ state.2 15 = 0

/-- A route witness that detects the concrete `dmax = 15` state of the
odd-sensitive example. -/
def sampleSensitiveStateWitness (state : ExtractionState ℤ) : Prop :=
  state = extractionState 15 sampleOddSensitiveCoeffs

theorem extraction_state_fifteen_equals_fourteen_on_odd_vanishing_surface_regression
    {coeff : DimensionCoefficients ℤ}
    (hvanish : VanishesOnOddDimensions coeff) :
    extractionState 15 coeff = extractionState 14 coeff := by
  exact extractionState_fifteen_eq_fourteen_of_vanishOnOddDimensions hvanish

theorem extraction_state_route_witness_collapses_regression
    {P : ExtractionState ℤ → Prop}
    {coeff : DimensionCoefficients ℤ}
    (hvanish : VanishesOnOddDimensions coeff) :
    ExtractionStateRouteWitness P 15 coeff ↔
      ExtractionStateRouteWitness P 14 coeff := by
  exact extractionStateRouteWitness_fifteen_iff_fourteen_of_vanishOnOddDimensions hvanish

theorem sample_route_witness_collapses_on_odd_vanishing_surface_regression :
    ExtractionStateRouteWitness sampleExtractionStateWitness 15 sampleOddVanishingCoeffs ↔
      ExtractionStateRouteWitness sampleExtractionStateWitness 14 sampleOddVanishingCoeffs := by
  exact extractionStateRouteWitness_fifteen_iff_fourteen_of_vanishOnOddDimensions
    sampleOddVanishingCoeffs_vanishesOnOddDimensions

theorem sample_route_witness_holds_on_odd_vanishing_surface_regression :
    ExtractionStateRouteWitness sampleExtractionStateWitness 15 sampleOddVanishingCoeffs := by
  rw [extractionStateRouteWitness_fifteen_iff_fourteen_of_vanishOnOddDimensions
    sampleOddVanishingCoeffs_vanishesOnOddDimensions]
  unfold ExtractionStateRouteWitness sampleExtractionStateWitness extractionState
  constructor
  · simp [extendedExtraction, extractLE, sampleOddVanishingCoeffs]
  · exact extractionRemainder_apply_of_lt (d := 14) (n := 15)
      (coeff := sampleOddVanishingCoeffs) (by norm_num)

theorem sample_odd_sensitive_state_is_not_collapsed_regression :
    extractionState 15 sampleOddSensitiveCoeffs ≠
      extractionState 14 sampleOddSensitiveCoeffs := by
  intro hEq
  have h := congrArg (fun state => state.1 15) hEq
  simp [extractionState, extendedExtraction, extractLE, sampleOddSensitiveCoeffs] at h

theorem sample_sensitive_route_witness_detects_absent_odd_vanishing_regression :
    ExtractionStateRouteWitness sampleSensitiveStateWitness 15 sampleOddSensitiveCoeffs := by
  unfold ExtractionStateRouteWitness sampleSensitiveStateWitness
  rfl

theorem sample_sensitive_route_witness_fails_at_fourteen_regression :
    ¬ ExtractionStateRouteWitness sampleSensitiveStateWitness 14 sampleOddSensitiveCoeffs := by
  intro h
  unfold ExtractionStateRouteWitness sampleSensitiveStateWitness at h
  exact sample_odd_sensitive_state_is_not_collapsed_regression h.symm

end YangMills
end QuantumTheory
end Mettapedia
