import Mettapedia.Computability.PNP.ResidualSideInformationResolutionCost

/-!
# P vs NP crux: no visible-pair balancing still need not imply residual success

The residual-side lane already shows that any successful invariant-base repair
must expose positive resolved mass and rule out supportwise visible-pair
balancing.  This file records the converse failure of that last condition on a
concrete finite surface.

The counterexample has positive resolved mass and a concrete proof-relevant
classifier witness, and it even rules out every supportwise visible-pair
balancing involution.  Nevertheless every classifier on `(base, side)` stays at
chance because each visible fiber is balanced only in aggregate: one heavy point
on one label is split across two light points on the opposite label.
-/

namespace Mettapedia.Computability.PNP

namespace WeightSplitResidualCounterexample

/-- Three hidden orbit slots crossed with one visible residual bit. -/
abbrev Ω : Type := Fin 3 × Bool

/-- The manuscript involution candidate flips only the visible residual bit. -/
def resolveSwap : Ω → Ω := fun x => (x.1, !x.2)

/-- The base feature is completely collapsed in this counterexample. -/
def base : Ω → Unit := fun _ => ()

/-- The residual side information is the visible second bit. -/
def side : Ω → Bool := fun x => x.2

/-- The hidden index `0` carries the heavy point; the other two indices are
the light points. -/
def weight : Ω → ℕ := fun x => if x.1 = 0 then 2 else 1

/-- The heavy slot carries the opposite target pattern from the two light
slots, so each visible side fiber balances only in aggregate. -/
def target : Ω → Bool := fun x => if x.1 = 0 then !x.2 else x.2

/-- The visible classifier surface seen by every residual-side repair. -/
def visible : Ω → Unit × Bool := fun x => (base x, side x)

/-- Concrete classifier that reads only the visible residual bit. -/
def separatingClassifier : Unit × Bool → Bool := fun u => u.2

/-- Constant-`false` classifier on the visible surface. -/
def constantFalseClassifier : Unit × Bool → Bool := fun _ => false

/-- Constant-`true` classifier on the visible surface. -/
def constantTrueClassifier : Unit × Bool → Bool := fun _ => true

/-- Classifier that predicts the negation of the visible residual bit. -/
def negatingClassifier : Unit × Bool → Bool := fun u => !u.2

theorem resolveSwap_involutive : Function.Involutive resolveSwap := by
  intro x
  cases x with
  | mk i b =>
      simp [resolveSwap]

theorem base_invariant_under_resolveSwap : ∀ x, base (resolveSwap x) = base x := by
  intro x
  cases x with
  | mk i b =>
      rfl

theorem side_changes_under_resolveSwap : ∀ x, side (resolveSwap x) ≠ side x := by
  intro x
  cases x with
  | mk i b =>
      simp [resolveSwap, side]

theorem target_flips_under_resolveSwap : ∀ x, target (resolveSwap x) = !(target x) := by
  intro x
  cases x with
  | mk i b =>
      fin_cases i <;> cases b <;> simp [resolveSwap, target]

theorem weight_invariant_under_resolveSwap : ∀ x, weight (resolveSwap x) = weight x := by
  intro x
  cases x with
  | mk i b =>
      simp [resolveSwap, weight]

theorem target_eq_true_of_side_false_weight_two
    (x : Ω) (hside : side x = false) (hweight : weight x = 2) :
    target x = true := by
  cases x with
  | mk i b =>
      fin_cases i <;> cases b <;> simp [side, weight, target] at hside hweight ⊢

theorem pos_resolvedMass :
    0 < resolvedMass resolveSwap side weight := by
  refine
    resolvedMass_pos_of_resolving_point
      resolveSwap side weight (x := (0, false)) ?_ ?_
  · simp [weight]
  · simp [resolveSwap, side]

theorem pure_residual_obstruction_package :
    ¬ SideInfoDeterminedBy base side ∧
      PositiveWeightSideInfoCollisionOverBase base side weight ∧
      (∃ x, 0 < weight x ∧
        base (resolveSwap x) = base x ∧ side (resolveSwap x) ≠ side x) ∧
      (∃ x, 0 < weight x ∧
        ¬ SourceOnlyPredicateCapturesSideEq base side (side x)) := by
  exact
    pos_resolvedMass_obstruction_package_invariant_base
      resolveSwap base side weight base_invariant_under_resolveSwap pos_resolvedMass

theorem not_supportwiseVisiblePairBalancing :
    ¬ SupportwiseVisiblePairBalancing base side target weight := by
  rintro ⟨σ, _hσ, htarget, hweight, hpair⟩
  let x : Ω := (0, false)
  have hxw : 0 < weight x := by
    simp [x, weight]
  have hside :
      side (σ x) = false := by
    have hpairx := hpair x hxw
    exact congrArg Prod.snd hpairx
  have hweightx : weight (σ x) = 2 := by
    simpa [x, weight] using hweight x
  have htrue : target (σ x) = true :=
    target_eq_true_of_side_false_weight_two (σ x) hside hweightx
  have hfalse : target (σ x) = false := by
    simpa [x, target] using htarget x
  rw [htrue] at hfalse
  simp at hfalse

theorem visiblePair_fiber_balanced :
    ∀ bs : Unit × Bool,
      weightedFeatureFiberTrueMass visible target weight bs =
        weightedFeatureFiberFalseMass visible target weight bs := by
  rintro ⟨u, b⟩
  cases u
  cases b <;> decide

theorem constantFalse_no_pos_doubledAdvantage :
    ¬ 0 < doubledAdvantage
      visible
      target
      weight
      constantFalseClassifier := by
  decide

theorem constantTrue_no_pos_doubledAdvantage :
    ¬ 0 < doubledAdvantage
      visible
      target
      weight
      constantTrueClassifier := by
  decide

theorem separatingClassifier_no_pos_doubledAdvantage :
    ¬ 0 < doubledAdvantage
      visible
      target
      weight
      separatingClassifier := by
  decide

theorem negatingClassifier_no_pos_doubledAdvantage :
    ¬ 0 < doubledAdvantage
      visible
      target
      weight
      negatingClassifier := by
  decide

theorem constantFalse_no_strict_half_advantage :
    ¬ weightedTotalMass weight <
        2 * weightedCorrectMass
          visible
          target
          weight
          constantFalseClassifier := by
  decide

theorem constantTrue_no_strict_half_advantage :
    ¬ weightedTotalMass weight <
        2 * weightedCorrectMass
          visible
          target
          weight
          constantTrueClassifier := by
  decide

theorem separatingClassifier_no_strict_half_advantage :
    ¬ weightedTotalMass weight <
        2 * weightedCorrectMass
          visible
          target
          weight
          separatingClassifier := by
  decide

theorem negatingClassifier_no_strict_half_advantage :
    ¬ weightedTotalMass weight <
        2 * weightedCorrectMass
          visible
          target
          weight
          negatingClassifier := by
  decide

theorem classifier_cases (h : Unit × Bool → Bool) :
    h = constantFalseClassifier ∨
      h = constantTrueClassifier ∨
      h = separatingClassifier ∨
      h = negatingClassifier := by
  cases hfalse : h ((), false) <;> cases htrue : h ((), true)
  · left
    funext u
    cases u with
    | mk _ b =>
        cases b <;> simp [constantFalseClassifier, hfalse, htrue]
  · right
    right
    left
    funext u
    cases u with
    | mk _ b =>
        cases b <;> simp [separatingClassifier, hfalse, htrue]
  · right
    right
    right
    funext u
    cases u with
    | mk _ b =>
        cases b <;> simp [negatingClassifier, hfalse, htrue]
  · right
    left
    funext u
    cases u with
    | mk _ b =>
        cases b <;> simp [constantTrueClassifier, hfalse, htrue]

theorem no_pos_doubledAdvantage :
    ∀ h : Unit × Bool → Bool,
      ¬ 0 < doubledAdvantage visible target weight h := by
  intro h
  exact
    not_pos_doubledAdvantage_pair_of_visiblePair_fiber_balanced
      base side target weight h visiblePair_fiber_balanced

theorem no_strict_half_advantage :
    ∀ h : Unit × Bool → Bool,
      ¬ weightedTotalMass weight <
        2 * weightedCorrectMass visible target weight h := by
  intro h
  exact
    not_total_lt_two_mul_weightedCorrectMass_pair_of_visiblePair_fiber_balanced
      base side target weight h visiblePair_fiber_balanced

theorem separatingClassifier_not_supportwiseSourceOnly :
    ¬ SupportwiseSourceOnlyPairClassifier base side weight separatingClassifier := by
  rintro ⟨classifier, hclassifier⟩
  have hfalse : classifier () = false := by
    simpa [base, side, separatingClassifier] using
      hclassifier (0, false) (by simp [weight])
  have htrue : classifier () = true := by
    simpa [base, side, separatingClassifier] using
      hclassifier (0, true) (by simp [weight])
  exact Bool.false_ne_true (hfalse.symm.trans htrue)

theorem separatingClassifier_prediction_separation :
    ∃ x, 0 < weight x ∧
      separatingClassifier (base (resolveSwap x), side (resolveSwap x)) ≠
        separatingClassifier (base x, side x) := by
  refine ⟨(0, false), ?_, ?_⟩
  · simp [weight]
  · simp [separatingClassifier, side, resolveSwap]

/-- The full proof-relevant obstruction bundle from the weight-splitting
surface, together with the failure of every visible-pair classifier. -/
def SupportedGapPackage : Prop :=
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
    ¬ SupportwiseVisiblePairBalancing base side target weight ∧
    (∀ g : Unit × Bool → Bool,
      ¬ 0 < doubledAdvantage visible target weight g) ∧
    (∀ g : Unit × Bool → Bool,
      ¬ weightedTotalMass weight <
        2 * weightedCorrectMass visible target weight g)

/-- The compact route bundle used to re-export the stronger counterexample on
the synthesis surface. -/
def RoutePackage : Prop :=
  Function.Involutive resolveSwap ∧
    (∀ x, base (resolveSwap x) = base x) ∧
    (∀ x, target (resolveSwap x) = !(target x)) ∧
    (∀ x, weight (resolveSwap x) = weight x) ∧
    0 < resolvedMass resolveSwap side weight ∧
    ¬ SideInfoDeterminedBy base side ∧
    ¬ SupportwiseVisiblePairBalancing base side target weight ∧
    (∃ h : Unit × Bool → Bool,
      ¬ SupportwiseSourceOnlyPairClassifier base side weight h ∧
      (∃ x, 0 < weight x ∧
        base (resolveSwap x) = base x ∧
        side (resolveSwap x) ≠ side x) ∧
      (∃ x, 0 < weight x ∧
        ¬ SourceOnlyPredicateCapturesSideEq base side (side x)) ∧
      (∃ x, 0 < weight x ∧
        h (base (resolveSwap x), side (resolveSwap x)) ≠ h (base x, side x))) ∧
    (∀ h : Unit × Bool → Bool,
      ¬ 0 < doubledAdvantage visible target weight h) ∧
    (∀ h : Unit × Bool → Bool,
      ¬ weightedTotalMass weight <
        2 * weightedCorrectMass visible target weight h)

/-- Stronger proof-relevant blocker: the visible side channel can carry
positive resolved mass and a concrete prediction-separating classifier, and it
can even refute every supportwise visible-pair balancing involution, while
still leaving every classifier on `(base, side)` exactly at chance. -/
theorem supported_obstruction_package_and_no_visiblePairBalancing_not_sufficient_for_any_success_package :
    SupportedGapPackage := by
  rcases pure_residual_obstruction_package with ⟨hnot, _hcollision, hwitness, hpred⟩
  exact
    ⟨separatingClassifier,
      pos_resolvedMass,
      hnot,
      separatingClassifier_not_supportwiseSourceOnly,
      hwitness,
      hpred,
      separatingClassifier_prediction_separation,
      not_supportwiseVisiblePairBalancing,
      no_pos_doubledAdvantage,
      no_strict_half_advantage⟩

/-- Full route package for the stronger weight-splitting blocker. -/
theorem route_package :
    RoutePackage := by
  rcases pure_residual_obstruction_package with ⟨hnot, _hcollision, hwitness, hpred⟩
  exact
    ⟨resolveSwap_involutive,
      base_invariant_under_resolveSwap,
      target_flips_under_resolveSwap,
      weight_invariant_under_resolveSwap,
      pos_resolvedMass,
      hnot,
      not_supportwiseVisiblePairBalancing,
      ⟨separatingClassifier,
        separatingClassifier_not_supportwiseSourceOnly,
        hwitness,
        hpred,
        separatingClassifier_prediction_separation⟩,
      no_pos_doubledAdvantage,
      no_strict_half_advantage⟩

end WeightSplitResidualCounterexample

end Mettapedia.Computability.PNP
