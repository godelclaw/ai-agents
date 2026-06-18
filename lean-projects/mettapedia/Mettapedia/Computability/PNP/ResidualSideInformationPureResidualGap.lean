import Mettapedia.Computability.PNP.ResidualSideInformationResolutionCost

/-!
# P vs NP crux: pure residual obstruction does not imply classifier success

The invariant-base residual-side lane now has a classifier-free core:
positive `resolvedMass` is equivalent to a positive-support same-base residual
change witness, and every successful residual repair collapses to that pure
obstruction package.

This file records the converse failure on a concrete four-point surface.  The
surface carries positive resolved mass and the full pure residual obstruction
package, but every classifier on `(base, side)` still stays exactly at chance.
So the pure residual package is necessary for success, not sufficient.
-/

namespace Mettapedia.Computability.PNP

namespace BalancedResidualCounterexample

/-- Four-point surface with a hidden balancing bit and a visible residual bit. -/
abbrev Ω : Type := Bool × Bool

/-- The manuscript involution candidate that flips the residual bit. -/
def resolveSwap : Ω → Ω := fun x => (x.1, !x.2)

/-- Auxiliary involution showing that the visible `(base, side)` feature pair
is still balanced at chance. -/
def neutralSwap : Ω → Ω := fun x => (!x.1, x.2)

/-- The base feature is completely collapsed in this counterexample. -/
def base : Ω → Unit := fun _ => ()

/-- The residual side information is the second bit. -/
def side : Ω → Bool := fun x => x.2

/-- The target depends on both bits, so the residual bit alone is insufficient. -/
def target : Ω → Bool := fun x => Bool.xor x.1 x.2

/-- Uniform positive support. -/
def weight : Ω → ℕ := fun _ => 1

/-- Concrete classifier that reads the visible residual bit directly. -/
def separatingClassifier : Unit × Bool → Bool := fun u => u.2

theorem resolveSwap_involutive : Function.Involutive resolveSwap := by
  intro x
  cases x with
  | mk a b =>
      simp [resolveSwap]

theorem neutralSwap_involutive : Function.Involutive neutralSwap := by
  intro x
  cases x with
  | mk a b =>
      simp [neutralSwap]

theorem base_invariant_under_resolveSwap : ∀ x, base (resolveSwap x) = base x := by
  intro x
  cases x with
  | mk a b =>
      rfl

theorem target_flips_under_resolveSwap : ∀ x, target (resolveSwap x) = !(target x) := by
  intro x
  cases x with
  | mk a b =>
      cases a <;> cases b <;> simp [target, resolveSwap, Bool.xor]

theorem target_flips_under_neutralSwap : ∀ x, target (neutralSwap x) = !(target x) := by
  intro x
  cases x with
  | mk a b =>
      cases a <;> cases b <;> simp [target, neutralSwap, Bool.xor]

theorem weight_invariant_under_resolveSwap : ∀ x, weight (resolveSwap x) = weight x := by
  intro x
  cases x with
  | mk a b =>
      rfl

theorem weight_invariant_under_neutralSwap : ∀ x, weight (neutralSwap x) = weight x := by
  intro x
  cases x with
  | mk a b =>
      rfl

theorem features_invariant_under_neutralSwap :
    ∀ x, (base (neutralSwap x), side (neutralSwap x)) = (base x, side x) := by
  intro x
  cases x with
  | mk a b =>
      rfl

theorem pos_resolvedMass :
    0 < resolvedMass resolveSwap side weight := by
  refine
    resolvedMass_pos_of_resolving_point
      resolveSwap side weight (x := (false, false)) ?_ ?_
  · simp [weight]
  · simp [resolveSwap, side]

theorem pure_residual_obstruction_package :
    ¬ SideInfoDeterminedBy base side ∧
      PositiveWeightSideInfoCollisionOverBase base side weight ∧
      (∃ x, 0 < weight x ∧ base (resolveSwap x) = base x ∧ side (resolveSwap x) ≠ side x) ∧
      (∃ x, 0 < weight x ∧
        ¬ SourceOnlyPredicateCapturesSideEq base side (side x)) := by
  exact
    pos_resolvedMass_obstruction_package_invariant_base
      resolveSwap base side weight base_invariant_under_resolveSwap pos_resolvedMass

theorem no_pos_doubledAdvantage :
    ∀ h : Unit × Bool → Bool,
      ¬ 0 < doubledAdvantage (fun x => (base x, side x)) target weight h := by
  intro h
  exact
    not_pos_doubledAdvantage_pair_of_supportwise_visiblePair_invariant
      neutralSwap
      base
      side
      target
      weight
      h
      neutralSwap_involutive
      target_flips_under_neutralSwap
      weight_invariant_under_neutralSwap
      (fun x _hx => features_invariant_under_neutralSwap x)

theorem no_strict_half_advantage :
    ∀ h : Unit × Bool → Bool,
      ¬ weightedTotalMass weight <
        2 * weightedCorrectMass (fun x => (base x, side x)) target weight h := by
  intro h
  exact
    not_total_lt_two_mul_weightedCorrectMass_pair_of_supportwise_visiblePair_invariant
      neutralSwap
      base
      side
      target
      weight
      h
      neutralSwap_involutive
      target_flips_under_neutralSwap
      weight_invariant_under_neutralSwap
      (fun x _hx => features_invariant_under_neutralSwap x)

theorem separatingClassifier_not_supportwiseSourceOnly :
    ¬ SupportwiseSourceOnlyPairClassifier base side weight separatingClassifier := by
  rintro ⟨classifier, hclassifier⟩
  have hfalse : classifier () = false := by
    simpa [base, side, separatingClassifier] using
      hclassifier (false, false) (by simp [weight])
  have htrue : classifier () = true := by
    simpa [base, side, separatingClassifier] using
      hclassifier (false, true) (by simp [weight])
  exact Bool.false_ne_true (hfalse.symm.trans htrue)

theorem separatingClassifier_prediction_separation :
    ∃ x, 0 < weight x ∧
      separatingClassifier (base (resolveSwap x), side (resolveSwap x)) ≠
        separatingClassifier (base x, side x) := by
  refine ⟨(false, false), ?_, ?_⟩
  · simp [weight]
  · simp [separatingClassifier, side, resolveSwap]

theorem separatingClassifier_no_pos_doubledAdvantage :
    ¬ 0 < doubledAdvantage
      (fun x => (base x, side x))
      target
      weight
      separatingClassifier :=
  no_pos_doubledAdvantage separatingClassifier

theorem separatingClassifier_no_strict_half_advantage :
    ¬ weightedTotalMass weight <
        2 * weightedCorrectMass
          (fun x => (base x, side x))
          target
          weight
          separatingClassifier :=
  no_strict_half_advantage separatingClassifier

/-- Concrete proof-relevant blocker: even an explicit classifier on `(base,
side)` that genuinely depends on the residual bit and separates a
positive-support involution pair still cannot beat chance on the balanced
four-point surface. -/
theorem prediction_witness_not_sufficient_package :
    ¬ SupportwiseSourceOnlyPairClassifier
      base
      side
      weight
      separatingClassifier ∧
      (∃ x, 0 < weight x ∧
        separatingClassifier (base (resolveSwap x), side (resolveSwap x)) ≠
          separatingClassifier (base x, side x)) ∧
      ¬ 0 < doubledAdvantage
        (fun x => (base x, side x))
        target
        weight
        separatingClassifier ∧
      ¬ weightedTotalMass weight <
        2 * weightedCorrectMass
          (fun x => (base x, side x))
          target
          weight
          separatingClassifier := by
  exact
    ⟨separatingClassifier_not_supportwiseSourceOnly,
      separatingClassifier_prediction_separation,
      separatingClassifier_no_pos_doubledAdvantage,
      separatingClassifier_no_strict_half_advantage⟩

/-- Concrete supported-obstruction blocker: even the full supported residual
obstruction package for a concrete classifier on `(base, side)` still does not
imply success on the balanced four-point surface. -/
theorem supported_obstruction_package_not_sufficient_package :
    ∃ h : Unit × Bool → Bool,
      0 < resolvedMass resolveSwap side weight ∧
      ¬ SideInfoDeterminedBy base side ∧
      ¬ SupportwiseSourceOnlyPairClassifier base side weight h ∧
      (∃ x, 0 < weight x ∧
        base (resolveSwap x) = base x ∧
        side (resolveSwap x) ≠ side x) ∧
      (∃ x, 0 < weight x ∧
        ¬ SourceOnlyPredicateCapturesSideEq base side (side x)) ∧
      (∃ x, 0 < weight x ∧
        h (base (resolveSwap x), side (resolveSwap x)) ≠ h (base x, side x)) ∧
      ¬ 0 < doubledAdvantage (fun x => (base x, side x)) target weight h ∧
      ¬ weightedTotalMass weight <
        2 * weightedCorrectMass (fun x => (base x, side x)) target weight h := by
  rcases pure_residual_obstruction_package with ⟨hnot, _hcollision, hwitness, hpred⟩
  exact
    ⟨separatingClassifier,
      pos_resolvedMass,
      hnot,
      separatingClassifier_not_supportwiseSourceOnly,
      hwitness,
      hpred,
      separatingClassifier_prediction_separation,
      separatingClassifier_no_pos_doubledAdvantage,
      separatingClassifier_no_strict_half_advantage⟩

/-- Stronger proof-relevant blocker: on the balanced four-point surface a
concrete classifier realizes the full supported residual obstruction package,
yet no classifier on the same visible `(base, side)` surface can succeed at
all.  So the proof-relevant package is not merely insufficient for that witness
classifier; it is insufficient for the existence of any successful repair on
that surface. -/
theorem supported_obstruction_package_not_sufficient_for_any_success_package :
    ∃ h : Unit × Bool → Bool,
      0 < resolvedMass resolveSwap side weight ∧
      ¬ SideInfoDeterminedBy base side ∧
      ¬ SupportwiseSourceOnlyPairClassifier base side weight h ∧
      (∃ x, 0 < weight x ∧
        base (resolveSwap x) = base x ∧
        side (resolveSwap x) ≠ side x) ∧
      (∃ x, 0 < weight x ∧
        ¬ SourceOnlyPredicateCapturesSideEq base side (side x)) ∧
      (∃ x, 0 < weight x ∧
        h (base (resolveSwap x), side (resolveSwap x)) ≠ h (base x, side x)) ∧
      (∀ h' : Unit × Bool → Bool,
        ¬ 0 < doubledAdvantage (fun x => (base x, side x)) target weight h') ∧
      (∀ h' : Unit × Bool → Bool,
        ¬ weightedTotalMass weight <
          2 * weightedCorrectMass (fun x => (base x, side x)) target weight h') := by
  rcases supported_obstruction_package_not_sufficient_package with
    ⟨h, hmass, hnot, hsource, hwitness, hpred, hsep, _hfail, _hhalf⟩
  exact
    ⟨h,
      hmass,
      hnot,
      hsource,
      hwitness,
      hpred,
      hsep,
      no_pos_doubledAdvantage,
      no_strict_half_advantage⟩

/-- Strongest concrete blocker on the balanced four-point surface: the same
visible surface simultaneously carries a witness classifier with the full
supported obstruction package for `resolveSwap` and a second involution
`neutralSwap` that fixes the visible `(base, side)` pair on positive support
while flipping the target.  Hence every classifier on `(base, side)` still
fails. -/
theorem supported_obstruction_package_with_visiblePair_balancing_blocks_any_success_package :
    ∃ h : Unit × Bool → Bool,
      0 < resolvedMass resolveSwap side weight ∧
      ¬ SideInfoDeterminedBy base side ∧
      ¬ SupportwiseSourceOnlyPairClassifier base side weight h ∧
      (∃ x, 0 < weight x ∧
        base (resolveSwap x) = base x ∧
        side (resolveSwap x) ≠ side x) ∧
      (∃ x, 0 < weight x ∧
        ¬ SourceOnlyPredicateCapturesSideEq base side (side x)) ∧
      (∃ x, 0 < weight x ∧
        h (base (resolveSwap x), side (resolveSwap x)) ≠ h (base x, side x)) ∧
      Function.Involutive neutralSwap ∧
      (∀ x, target (neutralSwap x) = !(target x)) ∧
      (∀ x, weight (neutralSwap x) = weight x) ∧
      (∀ x, 0 < weight x →
        (base (neutralSwap x), side (neutralSwap x)) = (base x, side x)) ∧
      (∀ h' : Unit × Bool → Bool,
        ¬ 0 < doubledAdvantage (fun x => (base x, side x)) target weight h') ∧
      (∀ h' : Unit × Bool → Bool,
        ¬ weightedTotalMass weight <
          2 * weightedCorrectMass (fun x => (base x, side x)) target weight h') := by
  rcases supported_obstruction_package_not_sufficient_for_any_success_package with
    ⟨h, hmass, hnot, hsource, hwitness, hpred, hsep, hfail, hhalf⟩
  exact
    ⟨h,
      hmass,
      hnot,
      hsource,
      hwitness,
      hpred,
      hsep,
      neutralSwap_involutive,
      target_flips_under_neutralSwap,
      weight_invariant_under_neutralSwap,
      (fun x _hx => features_invariant_under_neutralSwap x),
      hfail,
      hhalf⟩

/-- Concrete blocker package: positive invariant-base resolved mass and the
pure residual obstruction package do not imply any classifier success on
`(base, side)`. -/
theorem route_package :
    Function.Involutive resolveSwap ∧
      (∀ x, base (resolveSwap x) = base x) ∧
      (∀ x, target (resolveSwap x) = !(target x)) ∧
      (∀ x, weight (resolveSwap x) = weight x) ∧
      0 < resolvedMass resolveSwap side weight ∧
      ¬ SideInfoDeterminedBy base side ∧
      PositiveWeightSideInfoCollisionOverBase base side weight ∧
      (∃ x, 0 < weight x ∧ base (resolveSwap x) = base x ∧ side (resolveSwap x) ≠ side x) ∧
      (∃ x, 0 < weight x ∧
        ¬ SourceOnlyPredicateCapturesSideEq base side (side x)) ∧
      (∀ h : Unit × Bool → Bool,
        ¬ 0 < doubledAdvantage (fun x => (base x, side x)) target weight h) ∧
      (∀ h : Unit × Bool → Bool,
        ¬ weightedTotalMass weight <
          2 * weightedCorrectMass (fun x => (base x, side x)) target weight h) := by
  rcases pure_residual_obstruction_package with ⟨hnot, hcollision, hwitness, hpred⟩
  exact
    ⟨resolveSwap_involutive,
      base_invariant_under_resolveSwap,
      target_flips_under_resolveSwap,
      weight_invariant_under_resolveSwap,
      pos_resolvedMass,
      hnot,
      hcollision,
      hwitness,
      hpred,
      no_pos_doubledAdvantage,
      no_strict_half_advantage⟩

end BalancedResidualCounterexample

end Mettapedia.Computability.PNP
