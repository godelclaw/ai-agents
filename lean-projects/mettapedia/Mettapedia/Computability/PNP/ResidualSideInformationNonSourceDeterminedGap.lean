import Mettapedia.Computability.PNP.ResidualSideInformationResolutionCost

/-!
# P vs NP crux: supported non-source-determined residual data need not resolve orbits

The residual-side lane now proves that any successful invariant-base repair
must expose positive orbit-resolving mass and, from there, a proof-relevant
same-base residual-change witness.

This file records the converse failure at the broader non-source-determined
surface.  A residual side channel can vary on positive support inside one base
fiber and therefore fail source-determination, while still staying completely
invariant along the manuscript involution.  In that case the resolved mass is
zero and every classifier on `(base, side)` remains exactly at chance.
-/

namespace Mettapedia.Computability.PNP

namespace OrbitInvisibleResidualCounterexample

/-- Four-point surface with a hidden orbit bit and a visible residual bit. -/
abbrev Ω : Type := Bool × Bool

/-- The manuscript involution candidate flips only the hidden orbit bit. -/
def orbitSwap : Ω → Ω := fun x => (!x.1, x.2)

/-- The base feature is completely collapsed in this counterexample. -/
def base : Ω → Unit := fun _ => ()

/-- The residual side information is the visible second bit. -/
def side : Ω → Bool := fun x => x.2

/-- The target is the hidden orbit bit, so the residual bit alone is useless. -/
def target : Ω → Bool := fun x => x.1

/-- Uniform positive support. -/
def weight : Ω → ℕ := fun _ => 1

/-- Concrete classifier that reads the visible residual bit directly. -/
def separatingClassifier : Unit × Bool → Bool := fun u => u.2

theorem orbitSwap_involutive : Function.Involutive orbitSwap := by
  intro x
  cases x with
  | mk a b =>
      simp [orbitSwap]

theorem base_invariant_under_orbitSwap : ∀ x, base (orbitSwap x) = base x := by
  intro x
  cases x with
  | mk a b =>
      rfl

theorem side_invariant_under_orbitSwap : ∀ x, side (orbitSwap x) = side x := by
  intro x
  cases x with
  | mk a b =>
      rfl

theorem target_flips_under_orbitSwap : ∀ x, target (orbitSwap x) = !(target x) := by
  intro x
  cases x with
  | mk a b =>
      cases a <;> cases b <;> simp [target, orbitSwap]

theorem weight_invariant_under_orbitSwap : ∀ x, weight (orbitSwap x) = weight x := by
  intro x
  cases x with
  | mk a b =>
      rfl

theorem features_invariant_under_orbitSwap :
    ∀ x, (base (orbitSwap x), side (orbitSwap x)) = (base x, side x) := by
  intro x
  cases x with
  | mk a b =>
      rfl

theorem supported_collision :
    PositiveWeightSideInfoCollisionOverBase base side weight := by
  exact
    ⟨(false, false), (false, true), by simp [weight], rfl, by simp [side]⟩

theorem not_determined :
    ¬ SideInfoDeterminedBy base side := by
  exact not_sideInfoDeterminedBy_of_positiveWeight_collision supported_collision

theorem supported_non_sourceOnlyPredicate :
    ∃ x, 0 < weight x ∧
      ¬ SourceOnlyPredicateCapturesSideEq base side (side x) := by
  exact
    exists_positive_not_sourceOnlyPredicateCapturesSideEq_of_positiveWeight_collision
      supported_collision

theorem resolvedMass_eq_zero :
    resolvedMass orbitSwap side weight = 0 := by
  exact
    resolvedMass_eq_zero_of_unresolved
      orbitSwap side weight side_invariant_under_orbitSwap

theorem no_pos_doubledAdvantage :
    ∀ h : Unit × Bool → Bool,
      ¬ 0 < doubledAdvantage (fun x => (base x, side x)) target weight h := by
  intro h
  exact
    not_pos_doubledAdvantage_pair_of_resolvedMass_eq_zero
      orbitSwap
      base
      side
      target
      weight
      h
      orbitSwap_involutive
      base_invariant_under_orbitSwap
      target_flips_under_orbitSwap
      weight_invariant_under_orbitSwap
      resolvedMass_eq_zero

theorem no_strict_half_advantage :
    ∀ h : Unit × Bool → Bool,
      ¬ weightedTotalMass weight <
        2 * weightedCorrectMass (fun x => (base x, side x)) target weight h := by
  intro h
  exact
    not_total_lt_two_mul_weightedCorrectMass_pair_of_supportwise_visiblePair_invariant
      orbitSwap
      base
      side
      target
      weight
      h
      orbitSwap_involutive
      target_flips_under_orbitSwap
      weight_invariant_under_orbitSwap
      (fun x _hx => features_invariant_under_orbitSwap x)

theorem separatingClassifier_not_supportwiseSourceOnly :
    ¬ SupportwiseSourceOnlyPairClassifier base side weight separatingClassifier := by
  rintro ⟨classifier, hclassifier⟩
  have hfalse : classifier () = false := by
    simpa [base, side, weight, separatingClassifier] using
      hclassifier (false, false) (by simp [weight])
  have htrue : classifier () = true := by
    simpa [base, side, weight, separatingClassifier] using
      hclassifier (false, true) (by simp [weight])
  exact Bool.false_ne_true (hfalse.symm.trans htrue)

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
side)` that genuinely depends on the residual bit can still fail completely
when the involution never exposes that bit.  The orbit-invisible four-point
surface has zero resolved mass, and this residual-reading classifier remains at
chance despite not being supportwise source-only. -/
theorem proof_relevant_classifier_not_sufficient_package :
    ∃ h : Unit × Bool → Bool,
      ¬ SupportwiseSourceOnlyPairClassifier base side weight h ∧
      ¬ 0 < doubledAdvantage (fun x => (base x, side x)) target weight h ∧
      ¬ weightedTotalMass weight <
        2 * weightedCorrectMass (fun x => (base x, side x)) target weight h := by
  exact
    ⟨separatingClassifier,
      separatingClassifier_not_supportwiseSourceOnly,
      separatingClassifier_no_pos_doubledAdvantage,
      separatingClassifier_no_strict_half_advantage⟩

/-- Concrete blocker package: supported non-source-determined residual
variation is still too weak for the route.  It need not produce any
orbit-resolving mass, and therefore need not support any successful classifier
on `(base, side)`. -/
theorem route_package :
    Function.Involutive orbitSwap ∧
      (∀ x, base (orbitSwap x) = base x) ∧
      (∀ x, side (orbitSwap x) = side x) ∧
      (∀ x, target (orbitSwap x) = !(target x)) ∧
      (∀ x, weight (orbitSwap x) = weight x) ∧
      ¬ SideInfoDeterminedBy base side ∧
      PositiveWeightSideInfoCollisionOverBase base side weight ∧
      (∃ x, 0 < weight x ∧
        ¬ SourceOnlyPredicateCapturesSideEq base side (side x)) ∧
      resolvedMass orbitSwap side weight = 0 ∧
      (∃ h : Unit × Bool → Bool,
        ¬ SupportwiseSourceOnlyPairClassifier base side weight h ∧
        ¬ 0 < doubledAdvantage (fun x => (base x, side x)) target weight h ∧
        ¬ weightedTotalMass weight <
          2 * weightedCorrectMass (fun x => (base x, side x)) target weight h) ∧
      (∀ h : Unit × Bool → Bool,
        ¬ 0 < doubledAdvantage (fun x => (base x, side x)) target weight h) ∧
      (∀ h : Unit × Bool → Bool,
        ¬ weightedTotalMass weight <
          2 * weightedCorrectMass (fun x => (base x, side x)) target weight h) := by
  exact
    ⟨orbitSwap_involutive,
      base_invariant_under_orbitSwap,
      side_invariant_under_orbitSwap,
      target_flips_under_orbitSwap,
      weight_invariant_under_orbitSwap,
      not_determined,
      supported_collision,
      supported_non_sourceOnlyPredicate,
      resolvedMass_eq_zero,
      proof_relevant_classifier_not_sufficient_package,
      no_pos_doubledAdvantage,
      no_strict_half_advantage⟩

end OrbitInvisibleResidualCounterexample

end Mettapedia.Computability.PNP
