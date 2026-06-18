import Mettapedia.Computability.PNP.WeightedFeatureFiberMarginObstruction
import Mettapedia.Computability.PNP.ResidualSideInformationResolutionCost
import Mettapedia.Computability.PNP.ResidualSideInformationWeightSplitGap

/-!
# Regression checks for the weighted feature-fiber margin obstruction

These checks pin the new generic obstruction to the residual-side route: the
weight-splitting counterexample is fiber-balanced on the visible surface, so the
generic theorem must recover its global no-success conclusion.
-/

namespace Mettapedia.Computability.PNP.WeightedFeatureFiberMarginObstructionRegression

open Mettapedia.Computability.PNP
open Mettapedia.Computability.PNP.WeightSplitResidualCounterexample

abbrev boolVisible : Bool → Bool := id

abbrev boolTarget : Bool → Bool := id

def boolWeight : Bool → ℕ := fun _ => 1

theorem bool_visibleFiberImbalance :
    ∃ v : Bool,
      weightedFeatureFiberTrueMass boolVisible boolTarget boolWeight v ≠
        weightedFeatureFiberFalseMass boolVisible boolTarget boolWeight v := by
  refine ⟨true, ?_⟩
  decide

theorem bool_majority_classifier_has_pos_doubledAdvantage :
    0 < doubledAdvantage
      boolVisible
      boolTarget
      boolWeight
      (weightedFeatureFiberMajorityClassifier boolVisible boolTarget boolWeight) := by
  exact
    pos_doubledAdvantage_of_exists_weightedFeatureFiber_imbalance
      boolVisible boolTarget boolWeight bool_visibleFiberImbalance

theorem bool_exists_pos_doubledAdvantage_iff_visibleFiberImbalance_regression :
    (∃ h : Bool → Bool, 0 < doubledAdvantage boolVisible boolTarget boolWeight h) ↔
      ∃ v : Bool,
        weightedFeatureFiberTrueMass boolVisible boolTarget boolWeight v ≠
          weightedFeatureFiberFalseMass boolVisible boolTarget boolWeight v := by
  exact
    exists_pos_doubledAdvantage_iff_exists_weightedFeatureFiber_imbalance
      boolVisible boolTarget boolWeight

theorem weightSplit_visibleFiberBalanced :
    ∀ v : Unit × Bool,
      weightedFeatureFiberTrueMass visible target weight v =
        weightedFeatureFiberFalseMass visible target weight v := by
  rintro ⟨u, b⟩
  cases u
  cases b <;> decide

theorem weightSplit_no_pos_doubledAdvantage_via_visibleFiberBalance
    (h : Unit × Bool → Bool) :
    ¬ 0 < doubledAdvantage visible target weight h := by
  exact
    not_pos_doubledAdvantage_of_weightedFeatureFiberBalanced
      visible target weight h weightSplit_visibleFiberBalanced

theorem weightSplit_no_pos_doubledAdvantage_via_required_visibleFiberImbalance
    (h : Unit × Bool → Bool) :
    ¬ 0 < doubledAdvantage visible target weight h := by
  intro hadv
  rcases
    exists_weightedFeatureFiber_imbalance_of_pos_doubledAdvantage
      visible target weight h hadv with ⟨v, hneq⟩
  exact hneq (weightSplit_visibleFiberBalanced v)

theorem weightSplit_no_strict_half_advantage_via_visibleFiberBalance
    (h : Unit × Bool → Bool) :
    ¬ weightedTotalMass weight <
      2 * weightedCorrectMass visible target weight h := by
  exact
    not_total_lt_two_mul_weightedCorrectMass_of_weightedFeatureFiberBalanced
      visible target weight h weightSplit_visibleFiberBalanced

theorem weightSplit_no_strict_half_advantage_via_required_visibleFiberImbalance
    (h : Unit × Bool → Bool) :
    ¬ weightedTotalMass weight <
      2 * weightedCorrectMass visible target weight h := by
  intro hadv
  rcases
    exists_weightedFeatureFiber_imbalance_of_total_lt_two_mul_weightedCorrectMass
      visible target weight h hadv with ⟨v, hneq⟩
  exact hneq (weightSplit_visibleFiberBalanced v)

theorem weightSplit_no_pos_doubledAdvantage_via_visiblePairFiberImbalance
    (h : Unit × Bool → Bool) :
    ¬ 0 < doubledAdvantage visible target weight h := by
  intro hadv
  rcases
    exists_visiblePair_fiber_imbalance_of_pos_doubledAdvantage
      base side target weight h hadv with ⟨v, hneq⟩
  exact hneq (weightSplit_visibleFiberBalanced v)

theorem weightSplit_no_strict_half_advantage_via_visiblePairFiberImbalance
    (h : Unit × Bool → Bool) :
    ¬ weightedTotalMass weight <
      2 * weightedCorrectMass visible target weight h := by
  intro hadv
  rcases
    exists_visiblePair_fiber_imbalance_of_total_lt_two_mul_weightedCorrectMass
      base side target weight h hadv with ⟨v, hneq⟩
  exact hneq (weightSplit_visibleFiberBalanced v)

theorem weightSplit_separatingClassifier_no_pos_doubledAdvantage_via_visibleFiberBalance :
    ¬ 0 < doubledAdvantage visible target weight separatingClassifier := by
  exact
    weightSplit_no_pos_doubledAdvantage_via_visibleFiberBalance separatingClassifier

theorem weightSplit_separatingClassifier_no_strict_half_advantage_via_visibleFiberBalance :
    ¬ weightedTotalMass weight <
      2 * weightedCorrectMass visible target weight separatingClassifier := by
  exact
    weightSplit_no_strict_half_advantage_via_visibleFiberBalance separatingClassifier

end Mettapedia.Computability.PNP.WeightedFeatureFiberMarginObstructionRegression
