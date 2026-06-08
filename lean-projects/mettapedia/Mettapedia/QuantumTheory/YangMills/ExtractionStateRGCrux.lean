import Mettapedia.QuantumTheory.YangMills.ExtractionStateRouteCollapse
import Mettapedia.QuantumTheory.YangMills.RGCrux

/-!
# Yang-Mills Extraction-State Route Crux

This file binds the odd-cutoff extraction-state collapse back to the actual
Yang-Mills RG route crux.

The key interface is intentionally minimal: a manuscript repair may present
some extra route payload `P` derived from the extracted local terms and the
post-extraction remainder.  If that payload already forces the manuscript's
advertised same-constant contraction at cutoff `14`, then on the manuscript's
odd-vanishing coefficient surface the `dmax = 15` version is not a new route.
It collapses to the already-blocked `dmax = 14` gap route.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills

/-- A route payload on extraction state forces the manuscript's pointed
same-constant cutoff-`14` RG contraction if every cutoff-`14` witness yields
that contraction certificate. -/
def ForcesSameConstantFourteenContraction
    {α : Type*} [AddGroup α]
    (P : ExtractionState α → Prop) : Prop :=
  ∀ coeff : DimensionCoefficients α,
    ExtractionStateRouteWitness P 14 coeff →
      HasExtendedExtractionContraction 2224 2 14

/-- Route surface for an odd-cutoff repair witness that depends only on
extraction state.  The surrounding Hamiltonian-gap and clustering fields are
kept explicit so that the collapse theorem below lands directly on the
existing Yang-Mills gap-route crux. -/
def OddVanishingExtractionStateGapRoute
    {α H : Type*} [AddGroup α]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (A : LinearOperator H) (corr : SpatialCorrelation) (Δ : ℝ)
    (P : ExtractionState α → Prop) : Prop :=
  HasSpectralMassGap A Δ ∧
    SpectralGapClusteringBridge A corr ∧
      ∃ coeff : DimensionCoefficients α,
        VanishesOnOddDimensions coeff ∧
          ExtractionStateRouteWitness P 15 coeff

/-- If an odd-cutoff extraction-state route payload already forces the
manuscript's same-constant contraction at cutoff `14`, then every
odd-vanishing `dmax = 15` route collapses to the pointed blocked
`dmax = 14` gap route. -/
theorem sameConstantFourteenGapRoute_of_oddVanishingExtractionStateGapRoute
    {α H : Type*} [AddGroup α]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {corr : SpatialCorrelation} {Δ : ℝ}
    {P : ExtractionState α → Prop}
    (hforce : ForcesSameConstantFourteenContraction P)
    (hroute : OddVanishingExtractionStateGapRoute A corr Δ P) :
    HasSpectralMassGap A Δ ∧
      SpectralGapClusteringBridge A corr ∧
        HasExtendedExtractionContraction 2224 2 14 := by
  rcases hroute.2.2 with ⟨coeff, hvanish, h15⟩
  have h14 : ExtractionStateRouteWitness P 14 coeff :=
    (extractionStateRouteWitness_fifteen_iff_fourteen_of_vanishOnOddDimensions
      (P := P) hvanish).mp h15
  exact ⟨hroute.1, hroute.2.1, hforce coeff h14⟩

/-- Route-level collapse into the existing lower-extraction gap certificate. -/
theorem sameConstantLowerExtractionGapRouteCertificate_of_oddVanishingExtractionStateGapRoute
    {α H : Type*} [AddGroup α]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {corr : SpatialCorrelation} {Δ : ℝ}
    {P : ExtractionState α → Prop}
    (hforce : ForcesSameConstantFourteenContraction P)
    (hroute : OddVanishingExtractionStateGapRoute A corr Δ P) :
    SameConstantLowerExtractionGapRouteCertificate A corr Δ := by
  rcases sameConstantFourteenGapRoute_of_oddVanishingExtractionStateGapRoute
      hforce hroute with ⟨hgap, hbridge, hrg14⟩
  refine ⟨hgap, hbridge, ⟨14, ?_⟩⟩
  exact ⟨by norm_num, hrg14⟩

/-- Crux-out theorem: if the only new odd-cutoff ingredient factors through
extraction state and already forces the manuscript's same-constant cutoff-`14`
contraction, then the odd-vanishing `dmax = 15` repair route is impossible. -/
theorem not_oddVanishingExtractionStateGapRoute_of_forcesSameConstantFourteenContraction
    {α H : Type*} [AddGroup α]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {corr : SpatialCorrelation} {Δ : ℝ}
    {P : ExtractionState α → Prop}
    (hforce : ForcesSameConstantFourteenContraction P) :
    ¬ OddVanishingExtractionStateGapRoute A corr Δ P := by
  intro hroute
  exact
    not_sameConstantLowerExtractionGapRouteCertificate
      (sameConstantLowerExtractionGapRouteCertificate_of_oddVanishingExtractionStateGapRoute
        hforce hroute)

end YangMills
end QuantumTheory
end Mettapedia
