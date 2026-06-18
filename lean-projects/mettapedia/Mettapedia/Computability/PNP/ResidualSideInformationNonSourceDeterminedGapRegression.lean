import Mettapedia.Computability.PNP.ResidualSideInformationNonSourceDeterminedGap

/-!
# Regression checks for the non-source-determined residual-side gap

These checks pin the concrete orbit-invisible counterexample showing that
supported non-source-determined residual variation can still carry zero
resolving mass and no visible `(base, side)` classifier success.
-/

namespace Mettapedia.Computability.PNP.OrbitInvisibleResidualCounterexampleRegression

open Mettapedia.Computability.PNP
open Mettapedia.Computability.PNP.OrbitInvisibleResidualCounterexample

theorem supported_collision_regression :
    PositiveWeightSideInfoCollisionOverBase base side weight := by
  exact supported_collision

theorem not_determined_regression :
    ¬ SideInfoDeterminedBy base side := by
  exact not_determined

theorem resolvedMass_eq_zero_regression :
    resolvedMass orbitSwap side weight = 0 := by
  exact resolvedMass_eq_zero

theorem proof_relevant_classifier_not_sufficient_package_regression :
    ∃ h : Unit × Bool → Bool,
      ¬ SupportwiseSourceOnlyPairClassifier base side weight h ∧
      ¬ 0 < doubledAdvantage (fun x => (base x, side x)) target weight h ∧
      ¬ weightedTotalMass weight <
        2 * weightedCorrectMass (fun x => (base x, side x)) target weight h := by
  exact proof_relevant_classifier_not_sufficient_package

theorem no_existential_positive_advantage_regression :
    ¬ ∃ h : Unit × Bool → Bool,
      0 < doubledAdvantage (fun x => (base x, side x)) target weight h := by
  rintro ⟨h, hadv⟩
  exact (no_pos_doubledAdvantage h) hadv

theorem no_existential_strict_half_advantage_regression :
    ¬ ∃ h : Unit × Bool → Bool,
      weightedTotalMass weight <
        2 * weightedCorrectMass (fun x => (base x, side x)) target weight h := by
  rintro ⟨h, hadv⟩
  exact (no_strict_half_advantage h) hadv

end Mettapedia.Computability.PNP.OrbitInvisibleResidualCounterexampleRegression
