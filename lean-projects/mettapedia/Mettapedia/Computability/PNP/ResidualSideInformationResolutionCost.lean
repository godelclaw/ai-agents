import Mettapedia.Computability.PNP.ResidualSideInformationObstruction
import Mettapedia.Computability.PNP.ResolutionDemandObstruction
import Mettapedia.Computability.PNP.WeightedFeatureFiberMarginObstruction

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

/-- Over an invariant base, positive orbit-resolving mass is exactly the same
as a positive-support same-base involution pair where the residual side
information changes. -/
theorem pos_resolvedMass_iff_exists_positive_same_base_ne_side_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side) (w : α → ℕ)
    (hbase : ∀ x, base (τ x) = base x) :
    0 < resolvedMass τ side w ↔
      ∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x := by
  constructor
  · intro hmass
    rcases exists_resolving_point_of_pos_resolvedMass τ side w hmass with
      ⟨x, hxw, hside⟩
    exact ⟨x, hxw, hbase x, hside⟩
  · rintro ⟨x, hxw, _hbase, hside⟩
    exact resolvedMass_pos_of_resolving_point τ side w hxw hside

/-- Over an invariant base, full orbit-resolving mass is exactly the same as
supportwise separation of the visible `(base, side)` pair on positive
support. -/
theorem resolvedMass_eq_weightedTotalMass_iff_supportwise_visiblePair_separated_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side) (w : α → ℕ)
    (hbase : ∀ x, base (τ x) = base x) :
    resolvedMass τ side w = weightedTotalMass w ↔
      ∀ x, 0 < w x → (base (τ x), side (τ x)) ≠ (base x, side x) := by
  constructor
  · intro hmass x hxw hpair
    have hsep :=
      (resolvedMass_eq_weightedTotalMass_iff_supportwise_resolving τ side w).1
        hmass x hxw
    exact hsep (congrArg Prod.snd hpair)
  · intro hsep
    exact
      (resolvedMass_eq_weightedTotalMass_iff_supportwise_resolving τ side w).2
        (fun x hxw hside => hsep x hxw (Prod.ext (hbase x) hside))

/-- If a classifier on `(base, side)` is correct on every positive-weight point
and the target flips across every positive-weight involution pair, then the
visible pair must separate every supported involution pair. -/
theorem supportwise_visiblePair_separated_of_supportwise_correct_pair
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hy : ∀ x, 0 < w x → y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hcorrect : ∀ x, 0 < w x →
      Correct (fun x => (base x, side x)) y h x) :
    ∀ x, 0 < w x → (base (τ x), side (τ x)) ≠ (base x, side x) := by
  intro x hxw hpair
  have hxwτ : 0 < w (τ x) := by
    simpa [hw x] using hxw
  have hcorr : h (base x, side x) = y x := hcorrect x hxw
  have hcorrτ : h (base (τ x), side (τ x)) = y (τ x) := hcorrect (τ x) hxwτ
  have hsame : y (τ x) = y x := by
    calc
      y (τ x) = h (base (τ x), side (τ x)) := hcorrτ.symm
      _ = h (base x, side x) := by simpa [hpair]
      _ = y x := hcorr
  have hflip : y (τ x) = !(y x) := hy x hxw
  rw [hsame] at hflip
  simp at hflip

/-- Under the same supportwise-correctness hypothesis, an invariant-base
residual repair already uses the full support budget as orbit-resolving
mass. -/
theorem resolvedMass_eq_weightedTotalMass_of_supportwise_correct_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, 0 < w x → y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hcorrect : ∀ x, 0 < w x →
      Correct (fun x => (base x, side x)) y h x) :
    resolvedMass τ side w = weightedTotalMass w := by
  exact
    (resolvedMass_eq_weightedTotalMass_iff_supportwise_visiblePair_separated_invariant_base
      τ base side w hbase).2
      (supportwise_visiblePair_separated_of_supportwise_correct_pair
        τ base side y w h hy hw hcorrect)

/-- Under the same supportwise-correctness hypothesis, the doubled advantage of
the visible-pair classifier is exactly the orbit-resolving mass. -/
theorem doubledAdvantage_eq_resolvedMass_of_supportwise_correct_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, 0 < w x → y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hcorrect : ∀ x, 0 < w x →
      Correct (fun x => (base x, side x)) y h x) :
    doubledAdvantage (fun x => (base x, side x)) y w h =
      resolvedMass τ side w := by
  rw [doubledAdvantage_eq_weightedTotalMass_of_supportwise_correct
    (fun x => (base x, side x)) y w h hcorrect]
  exact
    (resolvedMass_eq_weightedTotalMass_of_supportwise_correct_invariant_base
      τ base side y w h hbase hy hw hcorrect).symm

/-- Over an invariant base, zero orbit-resolving mass is exactly the same as
supportwise invariance of the visible `(base, side)` pair. -/
theorem resolvedMass_eq_zero_iff_supportwise_visiblePair_invariant_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side) (w : α → ℕ)
    (hbase : ∀ x, base (τ x) = base x) :
    resolvedMass τ side w = 0 ↔
      ∀ x, 0 < w x → (base (τ x), side (τ x)) = (base x, side x) := by
  constructor
  · intro hzero x hxw
    refine Prod.ext (hbase x) ?_
    by_contra hside
    have hmass : 0 < resolvedMass τ side w :=
      resolvedMass_pos_of_resolving_point τ side w hxw hside
    have hnot : ¬ 0 < resolvedMass τ side w := by
      simp [hzero]
    exact (hnot hmass).elim
  · intro hpair
    refine resolvedMass_eq_zero_of_supportwise_unresolved τ side w ?_
    intro x hxw
    exact congrArg Prod.snd (hpair x hxw)

/-- Over an invariant base, positive orbit-resolving mass is exactly the same
as failure of supportwise visible-pair invariance on positive support. -/
theorem pos_resolvedMass_iff_not_supportwise_visiblePair_invariant_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side) (w : α → ℕ)
    (hbase : ∀ x, base (τ x) = base x) :
    0 < resolvedMass τ side w ↔
      ¬ ∀ x, 0 < w x → (base (τ x), side (τ x)) = (base x, side x) := by
  constructor
  · intro hmass hpair
    have hzero :
        resolvedMass τ side w = 0 :=
      (resolvedMass_eq_zero_iff_supportwise_visiblePair_invariant_invariant_base
        τ base side w hbase).2 hpair
    have hnot : ¬ 0 < resolvedMass τ side w := by
      simp [hzero]
    exact (hnot hmass).elim
  · intro hnot
    by_contra hmass
    have hzero : resolvedMass τ side w = 0 := Nat.eq_zero_of_not_pos hmass
    exact hnot
      ((resolvedMass_eq_zero_iff_supportwise_visiblePair_invariant_invariant_base
        τ base side w hbase).1 hzero)

/-- If a classifier on `(base, side)` is correct on every positive-weight
point over an invariant base, then all supported mass is orbit-resolving
mass. -/
theorem resolvedMass_eq_weightedTotalMass_of_weightedCorrectMass_eq_weightedTotalMass_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hperfect :
      weightedCorrectMass (fun x => (base x, side x)) y w h =
        weightedTotalMass w) :
    resolvedMass τ side w = weightedTotalMass w :=
  resolvedMass_eq_weightedTotalMass_of_weightedCorrectMass_eq_weightedTotalMass_pair
    τ base side y w h hτ hbase hy hw hperfect

/-- Perfect supported correctness on `(base, side)` over an invariant base
forces supportwise separation of the visible pair on every positive-weight
involution pair. -/
theorem supportwise_visiblePair_separated_of_weightedCorrectMass_eq_weightedTotalMass_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hperfect :
      weightedCorrectMass (fun x => (base x, side x)) y w h =
        weightedTotalMass w) :
    ∀ x, 0 < w x → (base (τ x), side (τ x)) ≠ (base x, side x) := by
  exact
    (resolvedMass_eq_weightedTotalMass_iff_supportwise_visiblePair_separated_invariant_base
      τ base side w hbase).1
      (resolvedMass_eq_weightedTotalMass_of_weightedCorrectMass_eq_weightedTotalMass_invariant_base
        τ base side y w h hτ hbase hy hw hperfect)

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

/-- If a weight-preserving involution flips the target while keeping the
visible `(base, side)` feature pair fixed on positive support, then no
classifier on `(base, side)` can have positive doubled advantage. -/
theorem not_pos_doubledAdvantage_pair_of_supportwise_visiblePair_invariant
    (σ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hσ : Function.Involutive σ)
    (hy : ∀ x, y (σ x) = !(y x))
    (hw : ∀ x, w (σ x) = w x)
    (hpair : ∀ x, 0 < w x → (base (σ x), side (σ x)) = (base x, side x)) :
    ¬ 0 < doubledAdvantage (fun x => (base x, side x)) y w h := by
  have hpred :
      ∀ x, 0 < w x →
        h (base (σ x), side (σ x)) = h (base x, side x) := by
    intro x hx
    exact congrArg h (hpair x hx)
  exact
    not_pos_doubledAdvantage_of_supportwise_prediction_invariant
      σ (fun x => (base x, side x)) y w h hσ hy hw hpred

/-- The same supportwise visible-pair balancing symmetry also blocks strict
half-accuracy advantage on `(base, side)`. -/
theorem not_total_lt_two_mul_weightedCorrectMass_pair_of_supportwise_visiblePair_invariant
    (σ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hσ : Function.Involutive σ)
    (hy : ∀ x, y (σ x) = !(y x))
    (hw : ∀ x, w (σ x) = w x)
    (hpair : ∀ x, 0 < w x → (base (σ x), side (σ x)) = (base x, side x)) :
    ¬ weightedTotalMass w <
      2 * weightedCorrectMass (fun x => (base x, side x)) y w h := by
  have hpred :
      ∀ x, 0 < w x →
        h (base (σ x), side (σ x)) = h (base x, side x) := by
    intro x hx
    exact congrArg h (hpair x hx)
  exact
    not_total_lt_two_mul_weightedCorrectMass_of_supportwise_prediction_invariant
      σ (fun x => (base x, side x)) y w h hσ hy hw hpred

/-- A supportwise visible-pair balancing involution flips the target, preserves
weights, and keeps the visible `(base, side)` pair fixed on positive support. -/
def SupportwiseVisiblePairBalancing
    (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) : Prop :=
  ∃ σ : α → α,
    Function.Involutive σ ∧
    (∀ x, y (σ x) = !(y x)) ∧
    (∀ x, w (σ x) = w x) ∧
    (∀ x, 0 < w x → (base (σ x), side (σ x)) = (base x, side x))

/-- A successful classifier on `(base, side)` rules out every supportwise
visible-pair balancing involution on that visible surface. -/
theorem not_supportwiseVisiblePairBalancing_of_pos_doubledAdvantage_pair
    (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hadv : 0 < doubledAdvantage (fun x => (base x, side x)) y w h) :
    ¬ SupportwiseVisiblePairBalancing base side y w := by
  rintro ⟨σ, hσ, hy, hw, hpair⟩
  exact
    (not_pos_doubledAdvantage_pair_of_supportwise_visiblePair_invariant
      σ base side y w h hσ hy hw hpair) hadv

/-- The same visible-pair balancing obstruction blocks any strict half-accuracy
success on `(base, side)`. -/
theorem not_supportwiseVisiblePairBalancing_of_total_lt_two_mul_weightedCorrectMass_pair
    (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hadv :
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h) :
    ¬ SupportwiseVisiblePairBalancing base side y w := by
  rintro ⟨σ, hσ, hy, hw, hpair⟩
  exact
    (not_total_lt_two_mul_weightedCorrectMass_pair_of_supportwise_visiblePair_invariant
      σ base side y w h hσ hy hw hpair) hadv

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

/-- On a finite visible `(base, side)` surface, any positive doubled advantage
must already break true/false mass balance on at least one visible fiber. -/
theorem exists_visiblePair_fiber_imbalance_of_pos_doubledAdvantage
    [Fintype Base] [Fintype Side] [DecidableEq Base] [DecidableEq Side]
    (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hadv : 0 < doubledAdvantage (fun x => (base x, side x)) y w h) :
    ∃ bs : Base × Side,
      weightedFeatureFiberTrueMass (fun x => (base x, side x)) y w bs ≠
        weightedFeatureFiberFalseMass (fun x => (base x, side x)) y w bs := by
  exact
    exists_weightedFeatureFiber_imbalance_of_pos_doubledAdvantage
      (fun x => (base x, side x)) y w h hadv

/-- The same visible-fiber imbalance is already forced by any strict half
accuracy claim on a finite visible `(base, side)` surface. -/
theorem exists_visiblePair_fiber_imbalance_of_total_lt_two_mul_weightedCorrectMass
    [Fintype Base] [Fintype Side] [DecidableEq Base] [DecidableEq Side]
    (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hadv :
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h) :
    ∃ bs : Base × Side,
      weightedFeatureFiberTrueMass (fun x => (base x, side x)) y w bs ≠
        weightedFeatureFiberFalseMass (fun x => (base x, side x)) y w bs := by
  exact
    exists_weightedFeatureFiber_imbalance_of_total_lt_two_mul_weightedCorrectMass
      (fun x => (base x, side x)) y w h hadv

/-- If every visible `(base, side)` fiber is already weight-balanced, then no
classifier on that visible surface can achieve positive doubled advantage. -/
theorem not_pos_doubledAdvantage_pair_of_visiblePair_fiber_balanced
    [Fintype Base] [Fintype Side] [DecidableEq Base] [DecidableEq Side]
    (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hbal :
      ∀ bs : Base × Side,
        weightedFeatureFiberTrueMass (fun x => (base x, side x)) y w bs =
          weightedFeatureFiberFalseMass (fun x => (base x, side x)) y w bs) :
    ¬ 0 < doubledAdvantage (fun x => (base x, side x)) y w h := by
  exact
    not_pos_doubledAdvantage_of_weightedFeatureFiberBalanced
      (fun x => (base x, side x)) y w h hbal

/-- The same visible-pair fiber balance blocks every strict-half weighted
success claim on that residual-side visible surface. -/
theorem not_total_lt_two_mul_weightedCorrectMass_pair_of_visiblePair_fiber_balanced
    [Fintype Base] [Fintype Side] [DecidableEq Base] [DecidableEq Side]
    (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hbal :
      ∀ bs : Base × Side,
        weightedFeatureFiberTrueMass (fun x => (base x, side x)) y w bs =
          weightedFeatureFiberFalseMass (fun x => (base x, side x)) y w bs) :
    ¬ weightedTotalMass w <
      2 * weightedCorrectMass (fun x => (base x, side x)) y w h := by
  exact
    not_total_lt_two_mul_weightedCorrectMass_of_weightedFeatureFiberBalanced
      (fun x => (base x, side x)) y w h hbal

/-- If every visible `(base, side)` fiber is weight-balanced, then there is no
successful classifier anywhere on that visible surface. -/
theorem not_exists_pos_doubledAdvantage_pair_of_visiblePair_fiber_balanced
    [Fintype Base] [Fintype Side] [DecidableEq Base] [DecidableEq Side]
    (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ)
    (hbal :
      ∀ bs : Base × Side,
        weightedFeatureFiberTrueMass (fun x => (base x, side x)) y w bs =
          weightedFeatureFiberFalseMass (fun x => (base x, side x)) y w bs) :
    ¬ ∃ h : Base × Side → Bool,
      0 < doubledAdvantage (fun x => (base x, side x)) y w h := by
  rintro ⟨h, hadv⟩
  exact
    (not_pos_doubledAdvantage_pair_of_visiblePair_fiber_balanced
      base side y w h hbal) hadv

/-- The same visible-pair balance obstruction rules out every strict-half
weighted-success classifier on that visible surface. -/
theorem not_exists_total_lt_two_mul_weightedCorrectMass_pair_of_visiblePair_fiber_balanced
    [Fintype Base] [Fintype Side] [DecidableEq Base] [DecidableEq Side]
    (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ)
    (hbal :
      ∀ bs : Base × Side,
        weightedFeatureFiberTrueMass (fun x => (base x, side x)) y w bs =
          weightedFeatureFiberFalseMass (fun x => (base x, side x)) y w bs) :
    ¬ ∃ h : Base × Side → Bool,
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h := by
  rintro ⟨h, hadv⟩
  exact
    (not_total_lt_two_mul_weightedCorrectMass_pair_of_visiblePair_fiber_balanced
      base side y w h hbal) hadv

/-- On a finite visible `(base, side)` surface, positive doubled advantage
exists exactly when some visible pair fiber has unequal retained `true` and
`false` mass. -/
theorem exists_pos_doubledAdvantage_pair_iff_exists_visiblePair_fiber_imbalance
    [Fintype Base] [Fintype Side] [DecidableEq Base] [DecidableEq Side]
    (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) :
    (∃ h : Base × Side → Bool,
      0 < doubledAdvantage (fun x => (base x, side x)) y w h) ↔
      ∃ bs : Base × Side,
        weightedFeatureFiberTrueMass (fun x => (base x, side x)) y w bs ≠
          weightedFeatureFiberFalseMass (fun x => (base x, side x)) y w bs := by
  exact
    exists_pos_doubledAdvantage_iff_exists_weightedFeatureFiber_imbalance
      (fun x => (base x, side x)) y w

/-- The strict-half weighted-success formulation has the same exact visible
pair-fiber criterion. -/
theorem exists_total_lt_two_mul_weightedCorrectMass_pair_iff_exists_visiblePair_fiber_imbalance
    [Fintype Base] [Fintype Side] [DecidableEq Base] [DecidableEq Side]
    (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) :
    (∃ h : Base × Side → Bool,
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h) ↔
      ∃ bs : Base × Side,
        weightedFeatureFiberTrueMass (fun x => (base x, side x)) y w bs ≠
          weightedFeatureFiberFalseMass (fun x => (base x, side x)) y w bs := by
  exact
    exists_total_lt_two_mul_weightedCorrectMass_iff_exists_weightedFeatureFiber_imbalance
      (fun x => (base x, side x)) y w

/-- Any existential positive-advantage residual repair over an invariant base
already collapses to classifier-free data: positive resolved mass together
with a concrete imbalanced visible `(base, side)` fiber. -/
theorem pos_resolvedMass_and_exists_visiblePair_fiber_imbalance_of_exists_pos_doubledAdvantage_invariant_base
    [Fintype Base] [Fintype Side] [DecidableEq Base] [DecidableEq Side]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hsuccess : ∃ h : Base × Side → Bool,
      0 < doubledAdvantage (fun x => (base x, side x)) y w h) :
    0 < resolvedMass τ side w ∧
      ∃ bs : Base × Side,
        weightedFeatureFiberTrueMass (fun x => (base x, side x)) y w bs ≠
          weightedFeatureFiberFalseMass (fun x => (base x, side x)) y w bs := by
  rcases hsuccess with ⟨h, hadv⟩
  refine ⟨?_, ?_⟩
  · exact
      resolvedMass_pos_of_pos_doubledAdvantage_pair
        τ base side y w h hτ hbase hy hw hadv
  · exact
      exists_visiblePair_fiber_imbalance_of_pos_doubledAdvantage
        base side y w h hadv

/-- The same classifier-free collapse holds for existential strict-half
weighted success. -/
theorem pos_resolvedMass_and_exists_visiblePair_fiber_imbalance_of_exists_total_lt_two_mul_weightedCorrectMass_invariant_base
    [Fintype Base] [Fintype Side] [DecidableEq Base] [DecidableEq Side]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hsuccess : ∃ h : Base × Side → Bool,
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h) :
    0 < resolvedMass τ side w ∧
      ∃ bs : Base × Side,
        weightedFeatureFiberTrueMass (fun x => (base x, side x)) y w bs ≠
          weightedFeatureFiberFalseMass (fun x => (base x, side x)) y w bs := by
  rcases hsuccess with ⟨h, hadv⟩
  refine ⟨?_, ?_⟩
  · exact
      resolvedMass_pos_of_total_lt_two_mul_weightedCorrectMass_pair
        τ base side y w h hτ hbase hy hw hadv
  · exact
      exists_visiblePair_fiber_imbalance_of_total_lt_two_mul_weightedCorrectMass
        base side y w h hadv

/-- Any existential positive-advantage residual repair over an invariant base
is already proof-relevant: Lean extracts a witness classifier together with
positive resolved mass and a supported same-base residual change. -/
theorem exists_classifier_and_same_base_residual_witness_of_exists_pos_doubledAdvantage_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hsuccess : ∃ h : Base × Side → Bool,
      0 < doubledAdvantage (fun x => (base x, side x)) y w h) :
    ∃ h : Base × Side → Bool,
      0 < doubledAdvantage (fun x => (base x, side x)) y w h ∧
      0 < resolvedMass τ side w ∧
      ∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x := by
  rcases hsuccess with ⟨h, hadv⟩
  refine ⟨h, hadv, ?_, ?_⟩
  · exact
      resolvedMass_pos_of_pos_doubledAdvantage_pair
        τ base side y w h hτ hbase hy hw hadv
  · exact
      exists_positive_same_base_ne_side_of_pos_doubledAdvantage_invariant_base
        τ base side y w h hτ hbase hy hw hadv

/-- The same proof-relevant extraction works for an existential strict
half-accuracy residual repair claim. -/
theorem exists_classifier_and_same_base_residual_witness_of_exists_total_lt_two_mul_weightedCorrectMass_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hsuccess : ∃ h : Base × Side → Bool,
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h) :
    ∃ h : Base × Side → Bool,
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h ∧
      0 < resolvedMass τ side w ∧
      ∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x := by
  rcases hsuccess with ⟨h, hadv⟩
  refine ⟨h, hadv, ?_, ?_⟩
  · exact
      resolvedMass_pos_of_total_lt_two_mul_weightedCorrectMass_pair
        τ base side y w h hτ hbase hy hw hadv
  · exact
      exists_positive_same_base_ne_side_of_total_lt_two_mul_weightedCorrectMass_invariant_base
        τ base side y w h hτ hbase hy hw hadv

/-- Exact minimal proof-relevant boundary: over an invariant base, claiming
that some classifier on `(base, side)` has positive doubled advantage is
equivalent to claiming that some classifier succeeds and thereby exposes a
positive-support same-base residual witness together with positive resolved
mass. -/
theorem exists_pos_doubledAdvantage_iff_exists_classifier_and_same_base_residual_witness_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x) :
    (∃ h : Base × Side → Bool,
      0 < doubledAdvantage (fun x => (base x, side x)) y w h) ↔
    ∃ h : Base × Side → Bool,
      0 < doubledAdvantage (fun x => (base x, side x)) y w h ∧
      0 < resolvedMass τ side w ∧
      ∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x := by
  constructor
  · exact
      exists_classifier_and_same_base_residual_witness_of_exists_pos_doubledAdvantage_invariant_base
        τ base side y w hτ hbase hy hw
  · intro hwitness
    rcases hwitness with ⟨h, hadv, _⟩
    exact ⟨h, hadv⟩

/-- Exact minimal proof-relevant boundary for the strict half-accuracy
formulation. -/
theorem exists_total_lt_two_mul_weightedCorrectMass_iff_exists_classifier_and_same_base_residual_witness_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x) :
    (∃ h : Base × Side → Bool,
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h) ↔
    ∃ h : Base × Side → Bool,
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h ∧
      0 < resolvedMass τ side w ∧
      ∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x := by
  constructor
  · exact
      exists_classifier_and_same_base_residual_witness_of_exists_total_lt_two_mul_weightedCorrectMass_invariant_base
        τ base side y w hτ hbase hy hw
  · intro hwitness
    rcases hwitness with ⟨h, hadv, _⟩
    exact ⟨h, hadv⟩

/-- Any existential positive-advantage residual repair over an invariant base
already exposes the minimal resolving witness and also rules out any
supportwise visible-pair balancing involution on the same visible surface. -/
theorem exists_classifier_and_same_base_residual_witness_and_no_visiblePairBalancing_of_exists_pos_doubledAdvantage_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hsuccess : ∃ h : Base × Side → Bool,
      0 < doubledAdvantage (fun x => (base x, side x)) y w h) :
    ∃ h : Base × Side → Bool,
      0 < doubledAdvantage (fun x => (base x, side x)) y w h ∧
      0 < resolvedMass τ side w ∧
      (∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
      ¬ SupportwiseVisiblePairBalancing base side y w := by
  rcases hsuccess with ⟨h, hadv⟩
  refine ⟨h, hadv, ?_, ?_, ?_⟩
  · exact
      resolvedMass_pos_of_pos_doubledAdvantage_pair
        τ base side y w h hτ hbase hy hw hadv
  · exact
      exists_positive_same_base_ne_side_of_pos_doubledAdvantage_invariant_base
        τ base side y w h hτ hbase hy hw hadv
  · exact
      not_supportwiseVisiblePairBalancing_of_pos_doubledAdvantage_pair
        base side y w h hadv

/-- The same sharpening holds for existential strict half-accuracy residual
repair claims. -/
theorem exists_classifier_and_same_base_residual_witness_and_no_visiblePairBalancing_of_exists_total_lt_two_mul_weightedCorrectMass_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hsuccess : ∃ h : Base × Side → Bool,
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h) :
    ∃ h : Base × Side → Bool,
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h ∧
      0 < resolvedMass τ side w ∧
      (∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
      ¬ SupportwiseVisiblePairBalancing base side y w := by
  rcases hsuccess with ⟨h, hadv⟩
  refine ⟨h, hadv, ?_, ?_, ?_⟩
  · exact
      resolvedMass_pos_of_total_lt_two_mul_weightedCorrectMass_pair
        τ base side y w h hτ hbase hy hw hadv
  · exact
      exists_positive_same_base_ne_side_of_total_lt_two_mul_weightedCorrectMass_invariant_base
        τ base side y w h hτ hbase hy hw hadv
  · exact
      not_supportwiseVisiblePairBalancing_of_total_lt_two_mul_weightedCorrectMass_pair
        base side y w h hadv

/-- Exact minimal boundary sharpened by the balancing obstruction: over an
invariant base, existential positive-advantage repair is equivalent to the
same claim plus a resolving witness and absence of supportwise visible-pair
balancing. -/
theorem exists_pos_doubledAdvantage_iff_exists_classifier_and_same_base_residual_witness_and_no_visiblePairBalancing_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x) :
    (∃ h : Base × Side → Bool,
      0 < doubledAdvantage (fun x => (base x, side x)) y w h) ↔
    ∃ h : Base × Side → Bool,
      0 < doubledAdvantage (fun x => (base x, side x)) y w h ∧
      0 < resolvedMass τ side w ∧
      (∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
      ¬ SupportwiseVisiblePairBalancing base side y w := by
  constructor
  · exact
      exists_classifier_and_same_base_residual_witness_and_no_visiblePairBalancing_of_exists_pos_doubledAdvantage_invariant_base
        τ base side y w hτ hbase hy hw
  · intro hwitness
    rcases hwitness with ⟨h, hadv, _⟩
    exact ⟨h, hadv⟩

/-- Exact minimal boundary sharpened by the same balancing obstruction for the
strict half-accuracy formulation. -/
theorem exists_total_lt_two_mul_weightedCorrectMass_iff_exists_classifier_and_same_base_residual_witness_and_no_visiblePairBalancing_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x) :
    (∃ h : Base × Side → Bool,
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h) ↔
    ∃ h : Base × Side → Bool,
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h ∧
      0 < resolvedMass τ side w ∧
      (∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
      ¬ SupportwiseVisiblePairBalancing base side y w := by
  constructor
  · exact
      exists_classifier_and_same_base_residual_witness_and_no_visiblePairBalancing_of_exists_total_lt_two_mul_weightedCorrectMass_invariant_base
        τ base side y w hτ hbase hy hw
  · intro hwitness
    rcases hwitness with ⟨h, hadv, _⟩
    exact ⟨h, hadv⟩

/-- Any existential positive-advantage residual repair over an invariant base
already collapses to the classifier-free positive-resolving-mass obstruction
package. -/
theorem pos_resolvedMass_obstruction_package_of_exists_pos_doubledAdvantage_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hsuccess : ∃ h : Base × Side → Bool,
      0 < doubledAdvantage (fun x => (base x, side x)) y w h) :
    0 < resolvedMass τ side w ∧
      ¬ SideInfoDeterminedBy base side ∧
      PositiveWeightSideInfoCollisionOverBase base side w ∧
      (∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
      (∃ x, 0 < w x ∧
        ¬ SourceOnlyPredicateCapturesSideEq base side (side x)) := by
  rcases hsuccess with ⟨h, hadv⟩
  have hmass :
      0 < resolvedMass τ side w :=
    resolvedMass_pos_of_pos_doubledAdvantage_pair
      τ base side y w h hτ hbase hy hw hadv
  rcases
    pos_resolvedMass_obstruction_package_invariant_base
      τ base side w hbase hmass with
    ⟨hnot, hcollision, hwitness, hpred⟩
  exact ⟨hmass, hnot, hcollision, hwitness, hpred⟩

/-- The same classifier-free positive-resolving-mass reduction holds for
existential strict half-accuracy residual repair claims. -/
theorem pos_resolvedMass_obstruction_package_of_exists_total_lt_two_mul_weightedCorrectMass_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hsuccess : ∃ h : Base × Side → Bool,
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h) :
    0 < resolvedMass τ side w ∧
      ¬ SideInfoDeterminedBy base side ∧
      PositiveWeightSideInfoCollisionOverBase base side w ∧
      (∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
      (∃ x, 0 < w x ∧
        ¬ SourceOnlyPredicateCapturesSideEq base side (side x)) := by
  rcases hsuccess with ⟨h, hadv⟩
  have hmass :
      0 < resolvedMass τ side w :=
    resolvedMass_pos_of_total_lt_two_mul_weightedCorrectMass_pair
      τ base side y w h hτ hbase hy hw hadv
  rcases
    pos_resolvedMass_obstruction_package_invariant_base
      τ base side w hbase hmass with
    ⟨hnot, hcollision, hwitness, hpred⟩
  exact ⟨hmass, hnot, hcollision, hwitness, hpred⟩

/-- Any existential positive-advantage residual repair over an invariant base
already yields the full supported obstruction package with an actual witness
classifier. -/
theorem exists_classifier_and_supported_obstruction_package_of_exists_pos_doubledAdvantage_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hsuccess : ∃ h : Base × Side → Bool,
      0 < doubledAdvantage (fun x => (base x, side x)) y w h) :
    ∃ h : Base × Side → Bool,
      0 < doubledAdvantage (fun x => (base x, side x)) y w h ∧
      0 < resolvedMass τ side w ∧
      ¬ SideInfoDeterminedBy base side ∧
      ¬ SupportwiseSourceOnlyPairClassifier base side w h ∧
      (∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
      (∃ x, 0 < w x ∧
        ¬ SourceOnlyPredicateCapturesSideEq base side (side x)) ∧
      (∃ x, 0 < w x ∧
        h (base (τ x), side (τ x)) ≠ h (base x, side x)) := by
  rcases hsuccess with ⟨h, hadv⟩
  refine ⟨h, hadv, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact
      resolvedMass_pos_of_pos_doubledAdvantage_pair
        τ base side y w h hτ hbase hy hw hadv
  · exact
      not_sideInfoDeterminedBy_of_pos_doubledAdvantage_invariant_base
        τ base side y w h hτ hbase hy hw hadv
  · intro hsource
    exact
      (not_pos_doubledAdvantage_pair_of_supportwiseSourceOnlyPairClassifier_invariant_base
        τ base side y w h hτ hbase hy hw hsource) hadv
  · exact
      exists_positive_same_base_ne_side_of_pos_doubledAdvantage_invariant_base
        τ base side y w h hτ hbase hy hw hadv
  · exact
      exists_positive_not_sourceOnlyPredicateCapturesSideEq_of_pos_doubledAdvantage_invariant_base
        τ base side y w h hτ hbase hy hw hadv
  · exact
      exists_positive_prediction_ne_of_pos_doubledAdvantage_pair_invariant_base
        τ base side y w h hτ hbase hy hw hadv

/-- The same existential proof-relevant package holds for strict half-accuracy
residual repair claims over an invariant base. -/
theorem exists_classifier_and_supported_obstruction_package_of_exists_total_lt_two_mul_weightedCorrectMass_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hsuccess : ∃ h : Base × Side → Bool,
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h) :
    ∃ h : Base × Side → Bool,
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h ∧
      0 < resolvedMass τ side w ∧
      ¬ SideInfoDeterminedBy base side ∧
      ¬ SupportwiseSourceOnlyPairClassifier base side w h ∧
      (∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
      (∃ x, 0 < w x ∧
        ¬ SourceOnlyPredicateCapturesSideEq base side (side x)) ∧
      (∃ x, 0 < w x ∧
        h (base (τ x), side (τ x)) ≠ h (base x, side x)) := by
  rcases hsuccess with ⟨h, hadv⟩
  refine ⟨h, hadv, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact
      resolvedMass_pos_of_total_lt_two_mul_weightedCorrectMass_pair
        τ base side y w h hτ hbase hy hw hadv
  · exact
      not_sideInfoDeterminedBy_of_total_lt_two_mul_weightedCorrectMass_invariant_base
        τ base side y w h hτ hbase hy hw hadv
  · intro hsource
    exact
      (not_total_lt_two_mul_weightedCorrectMass_pair_of_supportwiseSourceOnlyPairClassifier_invariant_base
        τ base side y w h hτ hbase hy hw hsource) hadv
  · exact
      exists_positive_same_base_ne_side_of_total_lt_two_mul_weightedCorrectMass_invariant_base
        τ base side y w h hτ hbase hy hw hadv
  · exact
      exists_positive_not_sourceOnlyPredicateCapturesSideEq_of_total_lt_two_mul_weightedCorrectMass_invariant_base
        τ base side y w h hτ hbase hy hw hadv
  · exact
      exists_positive_prediction_ne_of_total_lt_two_mul_weightedCorrectMass_pair_invariant_base
        τ base side y w h hτ hbase hy hw hadv

/-- Exact existential boundary: over an invariant base, claiming that some
classifier on `(base, side)` has positive doubled advantage is equivalent to
claiming that some classifier realizes the full supported obstruction package. -/
theorem exists_pos_doubledAdvantage_iff_exists_supported_obstruction_package_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x) :
    (∃ h : Base × Side → Bool,
      0 < doubledAdvantage (fun x => (base x, side x)) y w h) ↔
    ∃ h : Base × Side → Bool,
      0 < doubledAdvantage (fun x => (base x, side x)) y w h ∧
      0 < resolvedMass τ side w ∧
      ¬ SideInfoDeterminedBy base side ∧
      ¬ SupportwiseSourceOnlyPairClassifier base side w h ∧
      (∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
      (∃ x, 0 < w x ∧
        ¬ SourceOnlyPredicateCapturesSideEq base side (side x)) ∧
      (∃ x, 0 < w x ∧
        h (base (τ x), side (τ x)) ≠ h (base x, side x)) := by
  constructor
  · exact
      exists_classifier_and_supported_obstruction_package_of_exists_pos_doubledAdvantage_invariant_base
        τ base side y w hτ hbase hy hw
  · intro hpackage
    rcases hpackage with ⟨h, hadv, _⟩
    exact ⟨h, hadv⟩

/-- Exact existential boundary for the strict half-accuracy formulation. -/
theorem exists_total_lt_two_mul_weightedCorrectMass_iff_exists_supported_obstruction_package_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x) :
    (∃ h : Base × Side → Bool,
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h) ↔
    ∃ h : Base × Side → Bool,
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h ∧
      0 < resolvedMass τ side w ∧
      ¬ SideInfoDeterminedBy base side ∧
      ¬ SupportwiseSourceOnlyPairClassifier base side w h ∧
      (∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
      (∃ x, 0 < w x ∧
        ¬ SourceOnlyPredicateCapturesSideEq base side (side x)) ∧
      (∃ x, 0 < w x ∧
        h (base (τ x), side (τ x)) ≠ h (base x, side x)) := by
  constructor
  · exact
      exists_classifier_and_supported_obstruction_package_of_exists_total_lt_two_mul_weightedCorrectMass_invariant_base
        τ base side y w hτ hbase hy hw
  · intro hpackage
    rcases hpackage with ⟨h, hadv, _⟩
    exact ⟨h, hadv⟩

/-- The full supported obstruction package can be sharpened by the generic
visible-pair balancing burden: any existential positive-advantage residual
repair over an invariant base already carries a witness classifier with the
entire supported proof-relevant package and no supportwise visible-pair
balancing involution on the same visible surface. -/
theorem exists_classifier_and_supported_obstruction_package_and_no_visiblePairBalancing_of_exists_pos_doubledAdvantage_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hsuccess : ∃ h : Base × Side → Bool,
      0 < doubledAdvantage (fun x => (base x, side x)) y w h) :
    ∃ h : Base × Side → Bool,
      0 < doubledAdvantage (fun x => (base x, side x)) y w h ∧
      0 < resolvedMass τ side w ∧
      ¬ SideInfoDeterminedBy base side ∧
      ¬ SupportwiseSourceOnlyPairClassifier base side w h ∧
      (∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
      (∃ x, 0 < w x ∧
        ¬ SourceOnlyPredicateCapturesSideEq base side (side x)) ∧
      (∃ x, 0 < w x ∧
        h (base (τ x), side (τ x)) ≠ h (base x, side x)) ∧
      ¬ SupportwiseVisiblePairBalancing base side y w := by
  rcases
    exists_classifier_and_supported_obstruction_package_of_exists_pos_doubledAdvantage_invariant_base
      τ base side y w hτ hbase hy hw hsuccess with
    ⟨h, hadv, hmass, hnot, hsource, hwitness, hpred, hsep⟩
  refine ⟨h, hadv, hmass, hnot, hsource, hwitness, hpred, hsep, ?_⟩
  exact
    not_supportwiseVisiblePairBalancing_of_pos_doubledAdvantage_pair
      base side y w h hadv

/-- The same sharpening holds for existential strict half-accuracy residual
repair claims. -/
theorem exists_classifier_and_supported_obstruction_package_and_no_visiblePairBalancing_of_exists_total_lt_two_mul_weightedCorrectMass_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hsuccess : ∃ h : Base × Side → Bool,
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h) :
    ∃ h : Base × Side → Bool,
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h ∧
      0 < resolvedMass τ side w ∧
      ¬ SideInfoDeterminedBy base side ∧
      ¬ SupportwiseSourceOnlyPairClassifier base side w h ∧
      (∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
      (∃ x, 0 < w x ∧
        ¬ SourceOnlyPredicateCapturesSideEq base side (side x)) ∧
      (∃ x, 0 < w x ∧
        h (base (τ x), side (τ x)) ≠ h (base x, side x)) ∧
      ¬ SupportwiseVisiblePairBalancing base side y w := by
  rcases
    exists_classifier_and_supported_obstruction_package_of_exists_total_lt_two_mul_weightedCorrectMass_invariant_base
      τ base side y w hτ hbase hy hw hsuccess with
    ⟨h, hadv, hmass, hnot, hsource, hwitness, hpred, hsep⟩
  refine ⟨h, hadv, hmass, hnot, hsource, hwitness, hpred, hsep, ?_⟩
  exact
    not_supportwiseVisiblePairBalancing_of_total_lt_two_mul_weightedCorrectMass_pair
      base side y w h hadv

/-- Exact existential boundary sharpened all the way to the full supported
proof-relevant package: over an invariant base, positive-advantage residual
repair is exactly the same claim plus the supported obstruction package and
absence of supportwise visible-pair balancing. -/
theorem exists_pos_doubledAdvantage_iff_exists_supported_obstruction_package_and_no_visiblePairBalancing_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x) :
    (∃ h : Base × Side → Bool,
      0 < doubledAdvantage (fun x => (base x, side x)) y w h) ↔
    ∃ h : Base × Side → Bool,
      0 < doubledAdvantage (fun x => (base x, side x)) y w h ∧
      0 < resolvedMass τ side w ∧
      ¬ SideInfoDeterminedBy base side ∧
      ¬ SupportwiseSourceOnlyPairClassifier base side w h ∧
      (∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
      (∃ x, 0 < w x ∧
        ¬ SourceOnlyPredicateCapturesSideEq base side (side x)) ∧
      (∃ x, 0 < w x ∧
        h (base (τ x), side (τ x)) ≠ h (base x, side x)) ∧
      ¬ SupportwiseVisiblePairBalancing base side y w := by
  constructor
  · exact
      exists_classifier_and_supported_obstruction_package_and_no_visiblePairBalancing_of_exists_pos_doubledAdvantage_invariant_base
        τ base side y w hτ hbase hy hw
  · intro hpackage
    rcases hpackage with ⟨h, hadv, _⟩
    exact ⟨h, hadv⟩

/-- Exact existential boundary sharpened in the same way for strict
half-accuracy residual repair. -/
theorem exists_total_lt_two_mul_weightedCorrectMass_iff_exists_supported_obstruction_package_and_no_visiblePairBalancing_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x) :
    (∃ h : Base × Side → Bool,
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h) ↔
    ∃ h : Base × Side → Bool,
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h ∧
      0 < resolvedMass τ side w ∧
      ¬ SideInfoDeterminedBy base side ∧
      ¬ SupportwiseSourceOnlyPairClassifier base side w h ∧
      (∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
      (∃ x, 0 < w x ∧
        ¬ SourceOnlyPredicateCapturesSideEq base side (side x)) ∧
      (∃ x, 0 < w x ∧
        h (base (τ x), side (τ x)) ≠ h (base x, side x)) ∧
      ¬ SupportwiseVisiblePairBalancing base side y w := by
  constructor
  · exact
      exists_classifier_and_supported_obstruction_package_and_no_visiblePairBalancing_of_exists_total_lt_two_mul_weightedCorrectMass_invariant_base
        τ base side y w hτ hbase hy hw
  · intro hpackage
    rcases hpackage with ⟨h, hadv, _⟩
    exact ⟨h, hadv⟩

/-- Positive-support exact success on `(base, side)` over an invariant base
already carries the full supported obstruction package, saturates the whole
resolution budget, and rules out any supportwise visible-pair balancing
involution on the same visible surface. -/
theorem exact_supported_obstruction_package_and_no_visiblePairBalancing_of_weightedCorrectMass_eq_weightedTotalMass_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hperfect :
      weightedCorrectMass (fun x => (base x, side x)) y w h =
        weightedTotalMass w)
    (htotal : 0 < weightedTotalMass w) :
    weightedCorrectMass (fun x => (base x, side x)) y w h =
        weightedTotalMass w ∧
      0 < doubledAdvantage (fun x => (base x, side x)) y w h ∧
      doubledAdvantage (fun x => (base x, side x)) y w h =
        resolvedMass τ side w ∧
      0 < resolvedMass τ side w ∧
      ¬ SideInfoDeterminedBy base side ∧
      ¬ SupportwiseSourceOnlyPairClassifier base side w h ∧
      (∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
      (∃ x, 0 < w x ∧
        ¬ SourceOnlyPredicateCapturesSideEq base side (side x)) ∧
      (∃ x, 0 < w x ∧
        h (base (τ x), side (τ x)) ≠ h (base x, side x)) ∧
      ¬ SupportwiseVisiblePairBalancing base side y w := by
  have hadv :
      0 < doubledAdvantage (fun x => (base x, side x)) y w h := by
    rw [doubledAdvantage_eq_weightedTotalMass_of_weightedCorrectMass_eq_weightedTotalMass
      (fun x => (base x, side x)) y w h hperfect]
    exact htotal
  have hbudget :
      doubledAdvantage (fun x => (base x, side x)) y w h =
        resolvedMass τ side w :=
    doubledAdvantage_eq_resolvedMass_of_weightedCorrectMass_eq_weightedTotalMass_pair
      τ base side y w h hτ hbase hy hw hperfect
  have hmass :
      0 < resolvedMass τ side w := by
    rw [← hbudget]
    exact hadv
  have hnot :
      ¬ SideInfoDeterminedBy base side :=
    not_sideInfoDeterminedBy_of_pos_doubledAdvantage_invariant_base
      τ base side y w h hτ hbase hy hw hadv
  have hsource :
      ¬ SupportwiseSourceOnlyPairClassifier base side w h := by
    intro hsource
    exact
      (not_pos_doubledAdvantage_pair_of_supportwiseSourceOnlyPairClassifier_invariant_base
        τ base side y w h hτ hbase hy hw hsource) hadv
  refine ⟨hperfect, hadv, hbudget, hmass, hnot, hsource, ?_, ?_, ?_, ?_⟩
  · exact
      exists_positive_same_base_ne_side_of_pos_doubledAdvantage_invariant_base
        τ base side y w h hτ hbase hy hw hadv
  · exact
      exists_positive_not_sourceOnlyPredicateCapturesSideEq_of_pos_doubledAdvantage_invariant_base
        τ base side y w h hτ hbase hy hw hadv
  · exact
      exists_positive_prediction_ne_of_pos_doubledAdvantage_pair_invariant_base
        τ base side y w h hτ hbase hy hw hadv
  · exact
      not_supportwiseVisiblePairBalancing_of_pos_doubledAdvantage_pair
        base side y w h hadv

/-- The same exact-success hypothesis can be repackaged purely in terms of the
full resolving budget it forces, together with the supported obstruction data
on the visible surface. -/
theorem full_resolution_budget_and_supported_obstruction_package_and_no_visiblePairBalancing_of_weightedCorrectMass_eq_weightedTotalMass_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hperfect :
      weightedCorrectMass (fun x => (base x, side x)) y w h =
        weightedTotalMass w)
    (htotal : 0 < weightedTotalMass w) :
    doubledAdvantage (fun x => (base x, side x)) y w h =
        resolvedMass τ side w ∧
      resolvedMass τ side w = weightedTotalMass w ∧
      0 < resolvedMass τ side w ∧
      ¬ SideInfoDeterminedBy base side ∧
      ¬ SupportwiseSourceOnlyPairClassifier base side w h ∧
      (∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
      (∃ x, 0 < w x ∧
        ¬ SourceOnlyPredicateCapturesSideEq base side (side x)) ∧
      (∃ x, 0 < w x ∧
        h (base (τ x), side (τ x)) ≠ h (base x, side x)) ∧
      ¬ SupportwiseVisiblePairBalancing base side y w := by
  rcases
    exact_supported_obstruction_package_and_no_visiblePairBalancing_of_weightedCorrectMass_eq_weightedTotalMass_invariant_base
      τ base side y w h hτ hbase hy hw hperfect htotal with
    ⟨_hperfect, _hadv, hbudget, hmass, hnot, hsource, hwitness, hpred, hsep,
      hbalancing⟩
  have hfull :
      resolvedMass τ side w = weightedTotalMass w :=
    resolvedMass_eq_weightedTotalMass_of_weightedCorrectMass_eq_weightedTotalMass_invariant_base
      τ base side y w h hτ hbase hy hw hperfect
  exact ⟨hbudget, hfull, hmass, hnot, hsource, hwitness, hpred, hsep, hbalancing⟩

/-- The exact-success boundary also has a minimal proof-relevant reading: exact
supported success forces the full resolving budget together with a supported
same-base residual witness. -/
theorem full_resolution_budget_and_same_base_residual_witness_of_weightedCorrectMass_eq_weightedTotalMass_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hperfect :
      weightedCorrectMass (fun x => (base x, side x)) y w h =
        weightedTotalMass w)
    (htotal : 0 < weightedTotalMass w) :
    doubledAdvantage (fun x => (base x, side x)) y w h =
        resolvedMass τ side w ∧
      resolvedMass τ side w = weightedTotalMass w ∧
      0 < resolvedMass τ side w ∧
      (∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x) := by
  rcases
    full_resolution_budget_and_supported_obstruction_package_and_no_visiblePairBalancing_of_weightedCorrectMass_eq_weightedTotalMass_invariant_base
      τ base side y w h hτ hbase hy hw hperfect htotal with
    ⟨hbudget, hfull, hmass, _hnot, _hsource, hwitness, _hpred, _hsep,
      _hbalancing⟩
  exact ⟨hbudget, hfull, hmass, hwitness⟩

/-- Positive-support exact supported success on an invariant-base residual
surface is exactly equivalent to existence of a witness classifier carrying the
full supported obstruction package, a saturated resolution budget, and the
generic no-visible-pair-balancing burden. -/
theorem exists_weightedCorrectMass_eq_weightedTotalMass_and_pos_totalMass_iff_exists_exact_supported_obstruction_package_and_no_visiblePairBalancing_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x) :
    ((∃ h : Base × Side → Bool,
      weightedCorrectMass (fun x => (base x, side x)) y w h =
        weightedTotalMass w) ∧
      0 < weightedTotalMass w) ↔
    ∃ h : Base × Side → Bool,
      weightedCorrectMass (fun x => (base x, side x)) y w h =
          weightedTotalMass w ∧
        0 < doubledAdvantage (fun x => (base x, side x)) y w h ∧
        doubledAdvantage (fun x => (base x, side x)) y w h =
          resolvedMass τ side w ∧
        0 < resolvedMass τ side w ∧
        ¬ SideInfoDeterminedBy base side ∧
        ¬ SupportwiseSourceOnlyPairClassifier base side w h ∧
        (∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
        (∃ x, 0 < w x ∧
          ¬ SourceOnlyPredicateCapturesSideEq base side (side x)) ∧
        (∃ x, 0 < w x ∧
          h (base (τ x), side (τ x)) ≠ h (base x, side x)) ∧
        ¬ SupportwiseVisiblePairBalancing base side y w := by
  constructor
  · rintro ⟨⟨h, hperfect⟩, htotal⟩
    refine ⟨h, ?_⟩
    exact
      exact_supported_obstruction_package_and_no_visiblePairBalancing_of_weightedCorrectMass_eq_weightedTotalMass_invariant_base
        τ base side y w h hτ hbase hy hw hperfect htotal
  · intro hpackage
    rcases hpackage with
      ⟨h, hperfect, _hadv, _hbudget, hmass, _hnot, _hsource, _hwitness, _hpred,
        _hsep, _hbalancing⟩
    refine ⟨⟨h, hperfect⟩, ?_⟩
    exact lt_of_lt_of_le hmass (resolvedMass_le_weightedTotalMass τ side w)

/-- Positive-support exact supported success on an invariant-base residual
surface is exactly equivalent to existence of a witness classifier whose
doubled advantage saturates the full orbit-resolving budget, together with the
same supported obstruction package and no-visible-pair-balancing burden. -/
theorem exists_weightedCorrectMass_eq_weightedTotalMass_and_pos_totalMass_iff_exists_full_resolution_budget_and_supported_obstruction_package_and_no_visiblePairBalancing_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x) :
    ((∃ h : Base × Side → Bool,
      weightedCorrectMass (fun x => (base x, side x)) y w h =
        weightedTotalMass w) ∧
      0 < weightedTotalMass w) ↔
    ∃ h : Base × Side → Bool,
      doubledAdvantage (fun x => (base x, side x)) y w h =
          resolvedMass τ side w ∧
        resolvedMass τ side w = weightedTotalMass w ∧
        0 < resolvedMass τ side w ∧
        ¬ SideInfoDeterminedBy base side ∧
        ¬ SupportwiseSourceOnlyPairClassifier base side w h ∧
        (∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
        (∃ x, 0 < w x ∧
          ¬ SourceOnlyPredicateCapturesSideEq base side (side x)) ∧
        (∃ x, 0 < w x ∧
          h (base (τ x), side (τ x)) ≠ h (base x, side x)) ∧
        ¬ SupportwiseVisiblePairBalancing base side y w := by
  constructor
  · rintro ⟨⟨h, hperfect⟩, htotal⟩
    refine ⟨h, ?_⟩
    exact
      full_resolution_budget_and_supported_obstruction_package_and_no_visiblePairBalancing_of_weightedCorrectMass_eq_weightedTotalMass_invariant_base
        τ base side y w h hτ hbase hy hw hperfect htotal
  · intro hpackage
    rcases hpackage with
      ⟨h, hbudget, hfull, hmass, _hnot, _hsource, _hwitness, _hpred, _hsep,
        _hbalancing⟩
    have hperfect :
        weightedCorrectMass (fun x => (base x, side x)) y w h =
          weightedTotalMass w :=
      weightedCorrectMass_eq_weightedTotalMass_of_doubledAdvantage_eq_weightedTotalMass
        (fun x => (base x, side x)) y w h (hbudget.trans hfull)
    refine ⟨⟨h, hperfect⟩, ?_⟩
    exact lt_of_lt_of_le hmass (resolvedMass_le_weightedTotalMass τ side w)

/-- Exact minimal proof-relevant boundary: over an invariant base, nonempty
exact supported success is exactly equivalent to existence of a classifier that
spends the full orbit-resolving budget and thereby exposes a supported
same-base residual witness. -/
theorem exists_weightedCorrectMass_eq_weightedTotalMass_and_pos_totalMass_iff_exists_full_resolution_budget_and_same_base_residual_witness_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x) :
    ((∃ h : Base × Side → Bool,
      weightedCorrectMass (fun x => (base x, side x)) y w h =
        weightedTotalMass w) ∧
      0 < weightedTotalMass w) ↔
    ∃ h : Base × Side → Bool,
      doubledAdvantage (fun x => (base x, side x)) y w h =
          resolvedMass τ side w ∧
        resolvedMass τ side w = weightedTotalMass w ∧
        0 < resolvedMass τ side w ∧
        (∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x) := by
  constructor
  · rintro ⟨⟨h, hperfect⟩, htotal⟩
    refine ⟨h, ?_⟩
    exact
      full_resolution_budget_and_same_base_residual_witness_of_weightedCorrectMass_eq_weightedTotalMass_invariant_base
        τ base side y w h hτ hbase hy hw hperfect htotal
  · intro hwitness
    rcases hwitness with ⟨h, hbudget, hfull, hmass, _hwitness⟩
    have hperfect :
        weightedCorrectMass (fun x => (base x, side x)) y w h =
          weightedTotalMass w :=
      weightedCorrectMass_eq_weightedTotalMass_of_doubledAdvantage_eq_weightedTotalMass
        (fun x => (base x, side x)) y w h (hbudget.trans hfull)
    refine ⟨⟨h, hperfect⟩, ?_⟩
    exact lt_of_lt_of_le hmass (resolvedMass_le_weightedTotalMass τ side w)

end

end Mettapedia.Computability.PNP
