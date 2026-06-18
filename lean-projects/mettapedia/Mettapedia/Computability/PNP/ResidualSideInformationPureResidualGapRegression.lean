import Mettapedia.Computability.PNP.ResidualSideInformationPureResidualGap

/-!
# Regression checks for the pure residual-side gap

These checks pin the stronger balanced counterexample showing that positive
resolved mass and the full pure residual obstruction package still do not force
any visible `(base, side)` classifier success.
-/

namespace Mettapedia.Computability.PNP.BalancedResidualCounterexampleRegression

open Mettapedia.Computability.PNP
open Mettapedia.Computability.PNP.BalancedResidualCounterexample

theorem pos_resolvedMass_regression :
    0 < resolvedMass resolveSwap side weight := by
  exact pos_resolvedMass

theorem pure_residual_obstruction_package_regression :
    ¬ SideInfoDeterminedBy base side ∧
      PositiveWeightSideInfoCollisionOverBase base side weight ∧
      (∃ x, 0 < weight x ∧
        base (resolveSwap x) = base x ∧
        side (resolveSwap x) ≠ side x) ∧
      (∃ x, 0 < weight x ∧
        ¬ SourceOnlyPredicateCapturesSideEq base side (side x)) := by
  exact pure_residual_obstruction_package

theorem supported_obstruction_package_not_sufficient_for_any_success_regression :
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
  exact supported_obstruction_package_not_sufficient_for_any_success_package

theorem supported_obstruction_package_with_visiblePair_balancing_blocks_any_success_regression :
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
  exact supported_obstruction_package_with_visiblePair_balancing_blocks_any_success_package

end Mettapedia.Computability.PNP.BalancedResidualCounterexampleRegression
