import Mettapedia.Computability.PNP.ResidualSideInformationObstruction
import Mettapedia.Computability.PNP.ResolutionDemandObstruction

/-!
# P vs NP crux: source-determined residual side information has no resolving mass

The functional residual-side-information obstruction blocks source-only
recoding across same-source collisions.  This file connects that obstruction to
the orbit-resolution budget: if the residual side information is decoded from a
base feature that is invariant under the manuscript involution, then the side
channel itself is invariant, has zero resolving mass, and cannot supply positive
advantage.  Conversely, any positive advantage over such an invariant base must
expose a positive-weight same-base pair where the residual side information
actually changes.
-/

namespace Mettapedia.Computability.PNP

section

variable {α Base Side : Type*} [Fintype α]

omit [Fintype α] in
/-- Source-determined side information cannot change across an involution pair
when the base feature does not change. -/
theorem side_eq_under_involution_of_determinedBy_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (hbase : ∀ x, base (τ x) = base x)
    (hdet : SideInfoDeterminedBy base side) :
    ∀ x, side (τ x) = side x := by
  rcases hdet with ⟨decode, hdecode⟩
  intro x
  calc
    side (τ x) = decode (base (τ x)) := (hdecode (τ x)).symm
    _ = decode (base x) := by rw [hbase x]
    _ = side x := hdecode x

/-- A residual side channel decoded from an invariant base has zero
orbit-resolving mass. -/
theorem resolvedMass_eq_zero_of_determinedBy_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side) (w : α → ℕ)
    (hbase : ∀ x, base (τ x) = base x)
    (hdet : SideInfoDeterminedBy base side) :
    resolvedMass τ side w = 0 :=
  resolvedMass_eq_zero_of_unresolved τ side w
    (side_eq_under_involution_of_determinedBy_invariant_base
      τ base side hbase hdet)

/-- A source-determined residual side channel over an invariant base cannot
give positive doubled advantage to a classifier on `(base, side)`. -/
theorem not_pos_doubledAdvantage_pair_of_determinedBy_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hdet : SideInfoDeterminedBy base side)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x) :
    ¬ 0 < doubledAdvantage (fun x => (base x, side x)) y w h :=
  not_pos_doubledAdvantage_pair_of_supportwise_unresolved
    τ base side y w h hτ hbase hy hw
    (fun x _ => side_eq_under_involution_of_determinedBy_invariant_base
      τ base side hbase hdet x)

/-- In the half-accuracy formulation, a classifier on `(base, side)` with
source-determined invariant side information cannot beat chance. -/
theorem not_total_lt_two_mul_weightedCorrectMass_pair_of_determinedBy_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hdet : SideInfoDeterminedBy base side)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x) :
    ¬ weightedTotalMass w <
      2 * weightedCorrectMass (fun x => (base x, side x)) y w h := by
  have hbound :
      2 * weightedCorrectMass (fun x => (base x, side x)) y w h
        ≤ weightedTotalMass w + resolvedMass τ side w :=
    two_mul_weightedCorrectMass_pair_le_total_plus_resolvedMass
      τ base side y w h hτ hbase hy hw
  have hzero : resolvedMass τ side w = 0 :=
    resolvedMass_eq_zero_of_determinedBy_invariant_base
      τ base side w hbase hdet
  omega

/-- Positive orbit-resolving mass for an invariant-base residual side channel
already exposes a positive-weight residual collision over the base. -/
theorem positiveWeightSideInfoCollisionOverBase_of_pos_resolvedMass_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side) (w : α → ℕ)
    (hbase : ∀ x, base (τ x) = base x)
    (hmass : 0 < resolvedMass τ side w) :
    PositiveWeightSideInfoCollisionOverBase base side w := by
  rcases exists_resolving_point_of_pos_resolvedMass τ side w hmass with
    ⟨x, hxw, hside⟩
  exact ⟨x, τ x, hxw, (hbase x).symm, fun hside' => hside hside'.symm⟩

/-- Positive orbit-resolving mass for an invariant-base residual side channel
already rules out source-only residual decoding. -/
theorem not_sideInfoDeterminedBy_of_pos_resolvedMass_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side) (w : α → ℕ)
    (hbase : ∀ x, base (τ x) = base x)
    (hmass : 0 < resolvedMass τ side w) :
    ¬ SideInfoDeterminedBy base side :=
  not_sideInfoDeterminedBy_of_positiveWeight_collision
    (positiveWeightSideInfoCollisionOverBase_of_pos_resolvedMass_invariant_base
      τ base side w hbase hmass)

/-- Positive orbit-resolving mass for an invariant-base residual side channel
already exposes a supported residual value whose equality predicate is not
source-only. -/
theorem exists_positive_not_sourceOnlyPredicateCapturesSideEq_of_pos_resolvedMass_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side) (w : α → ℕ)
    (hbase : ∀ x, base (τ x) = base x)
    (hmass : 0 < resolvedMass τ side w) :
    ∃ x, 0 < w x ∧
      ¬ SourceOnlyPredicateCapturesSideEq base side (side x) :=
  exists_positive_not_sourceOnlyPredicateCapturesSideEq_of_positiveWeight_collision
    (positiveWeightSideInfoCollisionOverBase_of_pos_resolvedMass_invariant_base
      τ base side w hbase hmass)

/-- Positive orbit-resolving mass is already a classifier-free residual-side
obstruction over an invariant base.  It simultaneously rules out source-only
residual decoding, exhibits a supported same-base residual collision, and
exposes a supported residual equality test that is not source-only. -/
theorem pos_resolvedMass_obstruction_package_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side) (w : α → ℕ)
    (hbase : ∀ x, base (τ x) = base x)
    (hmass : 0 < resolvedMass τ side w) :
    ¬ SideInfoDeterminedBy base side ∧
      PositiveWeightSideInfoCollisionOverBase base side w ∧
      (∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
      (∃ x, 0 < w x ∧
        ¬ SourceOnlyPredicateCapturesSideEq base side (side x)) := by
  have hcollision :
      PositiveWeightSideInfoCollisionOverBase base side w :=
    positiveWeightSideInfoCollisionOverBase_of_pos_resolvedMass_invariant_base
      τ base side w hbase hmass
  rcases exists_resolving_point_of_pos_resolvedMass τ side w hmass with
    ⟨x, hxw, hside⟩
  refine ⟨?_, hcollision, ?_, ?_⟩
  · exact not_sideInfoDeterminedBy_of_positiveWeight_collision hcollision
  · exact ⟨x, hxw, hbase x, hside⟩
  · exact
      exists_positive_not_sourceOnlyPredicateCapturesSideEq_of_positiveWeight_collision
        hcollision

/-- Positive doubled advantage from `(base, side)` over an invariant base proves
that the residual side information is not source-determined. -/
theorem not_sideInfoDeterminedBy_of_pos_doubledAdvantage_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv : 0 < doubledAdvantage (fun x => (base x, side x)) y w h) :
    ¬ SideInfoDeterminedBy base side := by
  intro hdet
  exact
    (not_pos_doubledAdvantage_pair_of_determinedBy_invariant_base
      τ base side y w h hτ hbase hdet hy hw) hadv

/-- Strict half-accuracy advantage from `(base, side)` over an invariant base
also proves that the residual side information is not source-determined. -/
theorem not_sideInfoDeterminedBy_of_total_lt_two_mul_weightedCorrectMass_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv :
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h) :
    ¬ SideInfoDeterminedBy base side := by
  intro hdet
  exact
    (not_total_lt_two_mul_weightedCorrectMass_pair_of_determinedBy_invariant_base
      τ base side y w h hτ hbase hdet hy hw) hadv

/-- Positive doubled advantage from `(base, side)` over an invariant base
exposes a positive-weight same-base point where the residual side information
changes across the involution. -/
theorem exists_positive_same_base_ne_side_of_pos_doubledAdvantage_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv : 0 < doubledAdvantage (fun x => (base x, side x)) y w h) :
    ∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x := by
  rcases
    exists_resolving_point_of_pos_doubledAdvantage_pair
      τ base side y w h hτ hbase hy hw hadv with
    ⟨x, hxw, hside⟩
  exact ⟨x, hxw, hbase x, hside⟩

/-- Positive doubled advantage from `(base, side)` over an invariant base
exposes a positive-weight residual collision over the base. -/
theorem positiveWeightSideInfoCollisionOverBase_of_pos_doubledAdvantage_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv : 0 < doubledAdvantage (fun x => (base x, side x)) y w h) :
    PositiveWeightSideInfoCollisionOverBase base side w := by
  rcases
    exists_positive_same_base_ne_side_of_pos_doubledAdvantage_invariant_base
      τ base side y w h hτ hbase hy hw hadv with
    ⟨x, hxw, hbase_x, hside_x⟩
  exact ⟨x, τ x, hxw, hbase_x.symm, fun hside => hside_x hside.symm⟩

/-- Positive doubled advantage from `(base, side)` over an invariant base
exposes a positive-weight residual value whose equality test is not
source-only. -/
theorem exists_positive_not_sourceOnlyPredicateCapturesSideEq_of_pos_doubledAdvantage_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv : 0 < doubledAdvantage (fun x => (base x, side x)) y w h) :
    ∃ x, 0 < w x ∧
      ¬ SourceOnlyPredicateCapturesSideEq base side (side x) :=
  exists_positive_not_sourceOnlyPredicateCapturesSideEq_of_positiveWeight_collision
    (positiveWeightSideInfoCollisionOverBase_of_pos_doubledAdvantage_invariant_base
      τ base side y w h hτ hbase hy hw hadv)

/-- If every positive-weight residual equality test is source-only, then
`(base, side)` cannot have positive doubled advantage over an invariant base. -/
theorem not_pos_doubledAdvantage_pair_of_supported_sourceOnlyPredicateCapturesSideEq_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hsource :
      ∀ x, 0 < w x → SourceOnlyPredicateCapturesSideEq base side (side x)) :
    ¬ 0 < doubledAdvantage (fun x => (base x, side x)) y w h := by
  intro hadv
  rcases
    exists_positive_not_sourceOnlyPredicateCapturesSideEq_of_pos_doubledAdvantage_invariant_base
      τ base side y w h hτ hbase hy hw hadv with
    ⟨x, hxw, hnot⟩
  exact hnot (hsource x hxw)

/-- Strict half-accuracy advantage from `(base, side)` over an invariant base
also exposes a positive-weight same-base point where the residual side
information changes across the involution. -/
theorem exists_positive_same_base_ne_side_of_total_lt_two_mul_weightedCorrectMass_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv :
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h) :
    ∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x := by
  rcases
    exists_resolving_point_of_total_lt_two_mul_weightedCorrectMass_pair
      τ base side y w h hτ hbase hy hw hadv with
    ⟨x, hxw, hside⟩
  exact ⟨x, hxw, hbase x, hside⟩

/-- Strict half-accuracy advantage from `(base, side)` over an invariant base
exposes a positive-weight residual collision over the base. -/
theorem positiveWeightSideInfoCollisionOverBase_of_total_lt_two_mul_weightedCorrectMass_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv :
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h) :
    PositiveWeightSideInfoCollisionOverBase base side w := by
  rcases
    exists_positive_same_base_ne_side_of_total_lt_two_mul_weightedCorrectMass_invariant_base
      τ base side y w h hτ hbase hy hw hadv with
    ⟨x, hxw, hbase_x, hside_x⟩
  exact ⟨x, τ x, hxw, hbase_x.symm, fun hside => hside_x hside.symm⟩

/-- Strict half-accuracy advantage from `(base, side)` over an invariant base
exposes a positive-weight residual value whose equality test is not
source-only. -/
theorem exists_positive_not_sourceOnlyPredicateCapturesSideEq_of_total_lt_two_mul_weightedCorrectMass_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv :
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h) :
    ∃ x, 0 < w x ∧
      ¬ SourceOnlyPredicateCapturesSideEq base side (side x) :=
  exists_positive_not_sourceOnlyPredicateCapturesSideEq_of_positiveWeight_collision
    (positiveWeightSideInfoCollisionOverBase_of_total_lt_two_mul_weightedCorrectMass_invariant_base
      τ base side y w h hτ hbase hy hw hadv)

/-- If every positive-weight residual equality test is source-only, then
`(base, side)` cannot beat half accuracy over an invariant base. -/
theorem not_total_lt_two_mul_weightedCorrectMass_pair_of_supported_sourceOnlyPredicateCapturesSideEq_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hsource :
      ∀ x, 0 < w x → SourceOnlyPredicateCapturesSideEq base side (side x)) :
    ¬ weightedTotalMass w <
      2 * weightedCorrectMass (fun x => (base x, side x)) y w h := by
  intro hadv
  rcases
    exists_positive_not_sourceOnlyPredicateCapturesSideEq_of_total_lt_two_mul_weightedCorrectMass_invariant_base
      τ base side y w h hτ hbase hy hw hadv with
    ⟨x, hxw, hnot⟩
  exact hnot (hsource x hxw)

omit [Fintype α] in
/-- A source-only pair classifier on positive support has the same prediction
on every positive-weight involution pair when the base is invariant. -/
theorem prediction_eq_under_involution_of_supportwiseSourceOnlyPairClassifier_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (w : α → ℕ) (h : Base × Side → Bool)
    (hbase : ∀ x, base (τ x) = base x)
    (hw : ∀ x, w (τ x) = w x)
    (hsource : SupportwiseSourceOnlyPairClassifier base side w h) :
    ∀ x, 0 < w x →
      h (base (τ x), side (τ x)) = h (base x, side x) := by
  rcases hsource with ⟨classifier, hclassifier⟩
  intro x hx
  have hxτ : 0 < w (τ x) := by
    simpa [hw x] using hx
  calc
    h (base (τ x), side (τ x)) = classifier (base (τ x)) :=
      (hclassifier (τ x) hxτ).symm
    _ = classifier (base x) := by rw [hbase x]
    _ = h (base x, side x) := hclassifier x hx

/-- If the classifier's realized positive-support predictions are already
source-only over the invariant base, then `(base, side)` cannot have positive
doubled advantage. -/
theorem not_pos_doubledAdvantage_pair_of_supportwiseSourceOnlyPairClassifier_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hsource : SupportwiseSourceOnlyPairClassifier base side w h) :
    ¬ 0 < doubledAdvantage (fun x => (base x, side x)) y w h :=
  not_pos_doubledAdvantage_of_supportwise_prediction_invariant
    τ (fun x => (base x, side x)) y w h hτ hy hw
    (prediction_eq_under_involution_of_supportwiseSourceOnlyPairClassifier_invariant_base
      τ base side w h hbase hw hsource)

/-- In the strict half-accuracy formulation, source-only realized predictions
on positive support cannot beat chance over an invariant base. -/
theorem not_total_lt_two_mul_weightedCorrectMass_pair_of_supportwiseSourceOnlyPairClassifier_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hsource : SupportwiseSourceOnlyPairClassifier base side w h) :
    ¬ weightedTotalMass w <
      2 * weightedCorrectMass (fun x => (base x, side x)) y w h :=
  not_total_lt_two_mul_weightedCorrectMass_of_supportwise_prediction_invariant
    τ (fun x => (base x, side x)) y w h hτ hy hw
    (prediction_eq_under_involution_of_supportwiseSourceOnlyPairClassifier_invariant_base
      τ base side w h hbase hw hsource)

/-- Any positive doubled advantage from `(base, side)` over an invariant base
forces a positive-weight involution pair where the final classifier's
prediction changes. -/
theorem exists_positive_prediction_ne_of_pos_doubledAdvantage_pair_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv : 0 < doubledAdvantage (fun x => (base x, side x)) y w h) :
    ∃ x, 0 < w x ∧
      h (base (τ x), side (τ x)) ≠ h (base x, side x) := by
  let _ := hbase
  exact
    exists_positive_prediction_ne_of_pos_doubledAdvantage
      τ (fun x => (base x, side x)) y w h hτ hy hw hadv

/-- Strict half-accuracy advantage from `(base, side)` over an invariant base
forces the same supported prediction-separation witness. -/
theorem exists_positive_prediction_ne_of_total_lt_two_mul_weightedCorrectMass_pair_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv :
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h) :
    ∃ x, 0 < w x ∧
      h (base (τ x), side (τ x)) ≠ h (base x, side x) := by
  let _ := hbase
  exact
    exists_positive_prediction_ne_of_total_lt_two_mul_weightedCorrectMass
      τ (fun x => (base x, side x)) y w h hτ hy hw hadv

end

end Mettapedia.Computability.PNP
