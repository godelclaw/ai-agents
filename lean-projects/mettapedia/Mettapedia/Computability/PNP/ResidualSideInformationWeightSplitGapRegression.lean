import Mettapedia.Computability.PNP.ResidualSideInformationWeightSplitGap

/-!
# Regression checks for the residual-side weight-splitting blocker

These checks keep the stronger no-visible-pair-balancing counterexample tied to
its intended route meaning: positive resolved mass and a concrete
proof-relevant residual witness still do not imply any success on the visible
`(base, side)` surface.
-/

namespace Mettapedia.Computability.PNP.WeightSplitResidualCounterexampleRegression

open Mettapedia.Computability.PNP
open Mettapedia.Computability.PNP.WeightSplitResidualCounterexample

theorem supported_obstruction_package_and_no_visiblePairBalancing_not_sufficient_for_any_success_regression :
    WeightSplitResidualCounterexample.SupportedGapPackage := by
  exact
    Mettapedia.Computability.PNP.WeightSplitResidualCounterexample.supported_obstruction_package_and_no_visiblePairBalancing_not_sufficient_for_any_success_package

theorem route_package_regression :
    WeightSplitResidualCounterexample.RoutePackage := by
  exact
    Mettapedia.Computability.PNP.WeightSplitResidualCounterexample.route_package

theorem visiblePair_fiber_balance_blocks_existential_positive_advantage_regression :
    ¬ ∃ h : Unit × Bool → Bool,
      0 < doubledAdvantage visible target weight h := by
  exact
    not_exists_pos_doubledAdvantage_pair_of_visiblePair_fiber_balanced
      base side target weight visiblePair_fiber_balanced

theorem visiblePair_fiber_balance_blocks_existential_strict_half_advantage_regression :
    ¬ ∃ h : Unit × Bool → Bool,
      weightedTotalMass weight <
        2 * weightedCorrectMass visible target weight h := by
  exact
    not_exists_total_lt_two_mul_weightedCorrectMass_pair_of_visiblePair_fiber_balanced
      base side target weight visiblePair_fiber_balanced

theorem any_existential_positive_advantage_would_force_visiblePair_imbalance_regression :
    ¬ ∃ h : Unit × Bool → Bool,
      0 < doubledAdvantage visible target weight h := by
  intro hsuccess
  rcases
    pos_resolvedMass_and_exists_visiblePair_fiber_imbalance_of_exists_pos_doubledAdvantage_invariant_base
      resolveSwap base side target weight
      resolveSwap_involutive
      base_invariant_under_resolveSwap
      target_flips_under_resolveSwap
      weight_invariant_under_resolveSwap
      hsuccess with ⟨_hmass, ⟨bs, hneq⟩⟩
  exact hneq (visiblePair_fiber_balanced bs)

theorem any_existential_strict_half_advantage_would_force_visiblePair_imbalance_regression :
    ¬ ∃ h : Unit × Bool → Bool,
      weightedTotalMass weight <
        2 * weightedCorrectMass visible target weight h := by
  intro hsuccess
  rcases
    pos_resolvedMass_and_exists_visiblePair_fiber_imbalance_of_exists_total_lt_two_mul_weightedCorrectMass_invariant_base
      resolveSwap base side target weight
      resolveSwap_involutive
      base_invariant_under_resolveSwap
      target_flips_under_resolveSwap
      weight_invariant_under_resolveSwap
      hsuccess with ⟨_hmass, ⟨bs, hneq⟩⟩
  exact hneq (visiblePair_fiber_balanced bs)

theorem no_existential_positive_advantage_via_visiblePair_fiber_imbalance_iff_regression :
    ¬ ∃ h : Unit × Bool → Bool,
      0 < doubledAdvantage visible target weight h := by
  intro hsuccess
  rcases
    (exists_pos_doubledAdvantage_pair_iff_exists_visiblePair_fiber_imbalance
      base side target weight).1 hsuccess with ⟨bs, hneq⟩
  exact hneq (visiblePair_fiber_balanced bs)

theorem no_existential_strict_half_advantage_via_visiblePair_fiber_imbalance_iff_regression :
    ¬ ∃ h : Unit × Bool → Bool,
      weightedTotalMass weight <
        2 * weightedCorrectMass visible target weight h := by
  intro hsuccess
  rcases
    (exists_total_lt_two_mul_weightedCorrectMass_pair_iff_exists_visiblePair_fiber_imbalance
      base side target weight).1 hsuccess with ⟨bs, hneq⟩
  exact hneq (visiblePair_fiber_balanced bs)

end Mettapedia.Computability.PNP.WeightSplitResidualCounterexampleRegression
