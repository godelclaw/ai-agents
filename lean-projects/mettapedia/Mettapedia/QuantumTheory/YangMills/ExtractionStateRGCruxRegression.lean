import Mettapedia.QuantumTheory.YangMills.ExtractionStateRGCrux

/-!
# Yang-Mills Extraction-State Route Crux Regression

Regression wrappers for the bridge from odd-cutoff extraction-state routes to
the existing Yang-Mills RG crux.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills

/-- Simple cutoff-`14` coefficient family used to show that not every
extraction-state predicate can force the blocked contraction. -/
def sampleFourteenCoeffs : DimensionCoefficients ℤ :=
  fun n => if n = 14 then 7 else 0

/-- A sample extraction-state witness that only reads the extracted coefficient
at canonical dimension `14`. -/
def sampleFourteenExtractionStateWitness (state : ExtractionState ℤ) : Prop :=
  state.1 14 = 7

theorem sampleFourteenExtractionStateWitness_at_fourteen_regression :
    ExtractionStateRouteWitness
      sampleFourteenExtractionStateWitness 14 sampleFourteenCoeffs := by
  unfold ExtractionStateRouteWitness sampleFourteenExtractionStateWitness extractionState
  simp [extendedExtraction, extractLE, sampleFourteenCoeffs]

theorem sampleFourteenExtractionStateWitness_not_forcesSameConstantFourteenContraction_regression :
    ¬ ForcesSameConstantFourteenContraction sampleFourteenExtractionStateWitness := by
  intro hforce
  have hrg14 : HasExtendedExtractionContraction 2224 2 14 :=
    hforce sampleFourteenCoeffs
      sampleFourteenExtractionStateWitness_at_fourteen_regression
  exact not_rgContraction_2224_two_fourteen hrg14

theorem odd_vanishing_extraction_state_route_collapses_to_fourteen_gap_route_regression
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {corr : SpatialCorrelation} {Δ : ℝ}
    {P : ExtractionState ℤ → Prop}
    (hforce : ForcesSameConstantFourteenContraction P)
    (hroute : OddVanishingExtractionStateGapRoute A corr Δ P) :
    HasSpectralMassGap A Δ ∧
      SpectralGapClusteringBridge A corr ∧
        HasExtendedExtractionContraction 2224 2 14 := by
  exact sameConstantFourteenGapRoute_of_oddVanishingExtractionStateGapRoute
    hforce hroute

theorem odd_vanishing_extraction_state_route_yields_lower_extraction_gap_certificate_regression
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {corr : SpatialCorrelation} {Δ : ℝ}
    {P : ExtractionState ℤ → Prop}
    (hforce : ForcesSameConstantFourteenContraction P)
    (hroute : OddVanishingExtractionStateGapRoute A corr Δ P) :
    SameConstantLowerExtractionGapRouteCertificate A corr Δ := by
  exact
    sameConstantLowerExtractionGapRouteCertificate_of_oddVanishingExtractionStateGapRoute
      hforce hroute

theorem no_odd_vanishing_extraction_state_gap_route_regression
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {corr : SpatialCorrelation} {Δ : ℝ}
    {P : ExtractionState ℤ → Prop}
    (hforce : ForcesSameConstantFourteenContraction P) :
    ¬ OddVanishingExtractionStateGapRoute A corr Δ P := by
  exact
    not_oddVanishingExtractionStateGapRoute_of_forcesSameConstantFourteenContraction
      hforce

end YangMills
end QuantumTheory
end Mettapedia
