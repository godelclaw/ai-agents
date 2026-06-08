import Mettapedia.QuantumTheory.YangMills.ExtractionRemainder

/-!
# Yang-Mills Extraction-State Route Collapse

The Yang-Mills manuscript's RG bootstrap uses two downstream data streams:

* the extracted local terms `P≤dmax`;
* the post-extraction remainder.

On the manuscript's even-dimensional coefficient surface, the odd cutoff
`dmax = 15` contributes no new extracted term and leaves the same remainder as
`dmax = 14`.  This file packages that as a route-level collapse theorem:
any witness depending only on the pair
`(extendedExtraction dmax coeff, extractionRemainder dmax coeff)` cannot
distinguish cutoff `15` from cutoff `14` on odd-vanishing coefficient
families.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills

/-- Downstream RG state consisting of the extracted local terms together with
the post-extraction remainder. -/
abbrev ExtractionState (α : Type*) :=
  DimensionCoefficients α × DimensionCoefficients α

/-- The extraction-state data at cutoff `d`. -/
def extractionState
    {α : Type*} [AddGroup α]
    (d : CanonicalDimension) (coeff : DimensionCoefficients α) :
    ExtractionState α :=
  (extendedExtraction d coeff, extractionRemainder d coeff)

/-- On the manuscript's even-dimensional coefficient surface, the full
extraction state at cutoff `15` is exactly the same as at cutoff `14`. -/
theorem extractionState_fifteen_eq_fourteen_of_vanishOnOddDimensions
    {α : Type*} [AddGroup α]
    {coeff : DimensionCoefficients α}
    (hvanish : VanishesOnOddDimensions coeff) :
    extractionState 15 coeff = extractionState 14 coeff := by
  unfold extractionState
  rw [extendedExtraction_fifteen_eq_fourteen_of_vanishOnOddDimensions hvanish,
    extractionRemainder_fifteen_eq_fourteen_of_vanishOnOddDimensions hvanish]

/-- A route witness is determined by extraction state if equal downstream RG
data force equal witness values, regardless of how the witness is presented. -/
def DeterminedByExtractionState
    {α β : Type*} [AddGroup α]
    (R : CanonicalDimension → DimensionCoefficients α → β) : Prop :=
  ∀ ⦃d₁ d₂ : CanonicalDimension⦄
      ⦃coeff₁ coeff₂ : DimensionCoefficients α⦄,
    extractionState d₁ coeff₁ = extractionState d₂ coeff₂ →
      R d₁ coeff₁ = R d₂ coeff₂

/-- Any extraction-state-determined witness gives the same value at cutoffs
`15` and `14` on the manuscript's odd-vanishing coefficient surface. -/
theorem DeterminedByExtractionState.fifteen_eq_fourteen_of_vanishOnOddDimensions
    {α β : Type*} [AddGroup α]
    {R : CanonicalDimension → DimensionCoefficients α → β}
    (hR : DeterminedByExtractionState R)
    {coeff : DimensionCoefficients α}
    (hvanish : VanishesOnOddDimensions coeff) :
    R 15 coeff = R 14 coeff := by
  exact hR (extractionState_fifteen_eq_fourteen_of_vanishOnOddDimensions hvanish)

/-- Prop-valued version of
`DeterminedByExtractionState.fifteen_eq_fourteen_of_vanishOnOddDimensions`. -/
theorem DeterminedByExtractionState.fifteen_iff_fourteen_of_vanishOnOddDimensions
    {α : Type*} [AddGroup α]
    {R : CanonicalDimension → DimensionCoefficients α → Prop}
    (hR : DeterminedByExtractionState R)
    {coeff : DimensionCoefficients α}
    (hvanish : VanishesOnOddDimensions coeff) :
    R 15 coeff ↔ R 14 coeff := by
  have hEq :
      R 15 coeff = R 14 coeff :=
    hR.fifteen_eq_fourteen_of_vanishOnOddDimensions hvanish
  simp [hEq]

/-- Route-level blocker schema: once a manuscript witness depends only on the
extraction state and the `dmax = 14` branch is blocked, the odd-cutoff
`dmax = 15` branch is blocked as well on odd-vanishing coefficient families. -/
theorem DeterminedByExtractionState.not_fifteen_of_not_fourteen_on_oddVanishingSurface
    {α : Type*} [AddGroup α]
    {R : CanonicalDimension → DimensionCoefficients α → Prop}
    (hR : DeterminedByExtractionState R)
    (h14 : ∀ coeff : DimensionCoefficients α, ¬ R 14 coeff)
    {coeff : DimensionCoefficients α}
    (hvanish : VanishesOnOddDimensions coeff) :
    ¬ R 15 coeff := by
  intro h15
  exact h14 coeff ((hR.fifteen_iff_fourteen_of_vanishOnOddDimensions hvanish).mp h15)

/-- Concrete witness surface: the route witness is literally a predicate on the
downstream extraction state. -/
def ExtractionStateRouteWitness
    {α : Type*} [AddGroup α]
    (P : ExtractionState α → Prop)
    (d : CanonicalDimension) (coeff : DimensionCoefficients α) : Prop :=
  P (extractionState d coeff)

/-- Any literal predicate on extraction state is automatically determined by
extraction state. -/
theorem extractionStateRouteWitness_determinedByExtractionState
    {α : Type*} [AddGroup α]
    (P : ExtractionState α → Prop) :
    DeterminedByExtractionState (ExtractionStateRouteWitness P) := by
  intro d₁ d₂ coeff₁ coeff₂ hstate
  exact congrArg P hstate

/-- Manuscript-facing collapse theorem: any route witness that factors through
the extracted local terms and the post-extraction remainder identifies cutoff
`15` with cutoff `14` on odd-vanishing coefficient families. -/
theorem extractionStateRouteWitness_fifteen_iff_fourteen_of_vanishOnOddDimensions
    {α : Type*} [AddGroup α]
    {P : ExtractionState α → Prop}
    {coeff : DimensionCoefficients α}
    (hvanish : VanishesOnOddDimensions coeff) :
    ExtractionStateRouteWitness P 15 coeff ↔
      ExtractionStateRouteWitness P 14 coeff := by
  exact
    DeterminedByExtractionState.fifteen_iff_fourteen_of_vanishOnOddDimensions
      (R := ExtractionStateRouteWitness P)
      (extractionStateRouteWitness_determinedByExtractionState P)
      hvanish

/-- Blocker form of
`extractionStateRouteWitness_fifteen_iff_fourteen_of_vanishOnOddDimensions`:
if the route is already blocked at cutoff `14`, then the odd-cutoff `15`
presentation is blocked on the same odd-vanishing coefficient family. -/
theorem not_extractionStateRouteWitness_fifteen_of_not_fourteen_on_oddVanishingSurface
    {α : Type*} [AddGroup α]
    {P : ExtractionState α → Prop}
    (h14 : ∀ coeff : DimensionCoefficients α,
      ¬ ExtractionStateRouteWitness P 14 coeff)
    {coeff : DimensionCoefficients α}
    (hvanish : VanishesOnOddDimensions coeff) :
    ¬ ExtractionStateRouteWitness P 15 coeff := by
  exact
    DeterminedByExtractionState.not_fifteen_of_not_fourteen_on_oddVanishingSurface
      (R := ExtractionStateRouteWitness P)
      (extractionStateRouteWitness_determinedByExtractionState P)
      h14 hvanish

end YangMills
end QuantumTheory
end Mettapedia
