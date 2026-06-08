import Mettapedia.Computability.PNP.PostSwitchResidualWitness

/-!
# Regression checks for the exact post-switch residual witness

These wrappers pin the concrete active-orbit witness on the manuscript's exact
post-switch surface.  The retained side bit already has positive resolving
mass, and that positive resolving mass already forces the pure residual
obstruction package before any classifier-level prediction-separation argument
is used.
-/

namespace Mettapedia.Computability.PNP.PostSwitchResidualWitnessRegression

open Mettapedia.Computability.PNP

theorem active_orbit_pos_resolved_mass_bool_regression :
    0 < resolvedMass tiInputMap
      (fun u : ExactVisiblePostSwitchSurface Bool 1 => u.b)
      (activeOrbitWeight false) := by
  exact pos_resolvedMass_activeOrbit (Z := Bool) false

theorem active_orbit_strict_half_advantage_bool_regression :
    weightedTotalMass (activeOrbitWeight false) <
      2 * weightedCorrectMass
        activeOrbitFeatures
        activeOrbitTarget
        (activeOrbitWeight false)
        activeOrbitClassifier := by
  exact total_lt_two_mul_weightedCorrectMass_activeOrbit (Z := Bool) false

theorem active_orbit_positive_nonzero_column_mass_bool_regression :
    0 <
      sliceMass
        (fun u : ExactVisiblePostSwitchSurface Bool 1 => nonzeroColumn u.a)
        (activeOrbitWeight false) := by
  exact pos_nonzeroColumnMass_activeOrbit (Z := Bool) false

theorem active_orbit_refutes_exact_input_invariant_support_bool_regression :
    ¬ exactInputInvariantWeightedSupport (activeOrbitWeight false) := by
  exact not_exactInputInvariantWeightedSupport_activeOrbit (Z := Bool) false

theorem active_orbit_forces_fork_obstruction_bool_regression :
    weightedTotalMass (activeOrbitWeight false) <
        2 * weightedCorrectMass
          activeOrbitFeatures
          activeOrbitTarget
          (activeOrbitWeight false)
          activeOrbitClassifier ∧
      0 <
        sliceMass
          (fun u : ExactVisiblePostSwitchSurface Bool 1 => nonzeroColumn u.a)
          (activeOrbitWeight false) ∧
      ¬ exactInputInvariantWeightedSupport (activeOrbitWeight false) := by
  exact exactPostSwitch_activeOrbit_forces_fork_obstruction (Z := Bool) false

theorem active_orbit_pos_resolved_mass_forces_pure_residual_obstruction_package_bool_regression :
    ¬ SideInfoDeterminedBy invariantVisibleData
        (fun u : ExactVisiblePostSwitchSurface Bool 1 => u.b) ∧
      PositiveWeightSideInfoCollisionOverBase invariantVisibleData
        (fun u : ExactVisiblePostSwitchSurface Bool 1 => u.b)
        (activeOrbitWeight false) ∧
      (∃ u : ExactVisiblePostSwitchSurface Bool 1,
        0 < activeOrbitWeight false u ∧
          invariantVisibleData (tiInputMap u) = invariantVisibleData u ∧
          (tiInputMap u).b ≠ u.b) ∧
      (∃ u : ExactVisiblePostSwitchSurface Bool 1,
        0 < activeOrbitWeight false u ∧
          ¬ SourceOnlyPredicateCapturesSideEq invariantVisibleData
            (fun u : ExactVisiblePostSwitchSurface Bool 1 => u.b) (u.b)) := by
  exact
    exactPostSwitch_pos_resolvedMass_forces_pure_residual_obstruction_package
      (Z := Bool)
      (w := activeOrbitWeight false)
      active_orbit_pos_resolved_mass_bool_regression

theorem active_orbit_realizes_pure_residual_obstruction_package_bool_regression :
    0 < resolvedMass tiInputMap
        (fun u : ExactVisiblePostSwitchSurface Bool 1 => u.b)
        (activeOrbitWeight false) ∧
      ¬ SideInfoDeterminedBy invariantVisibleData
          (fun u : ExactVisiblePostSwitchSurface Bool 1 => u.b) ∧
      PositiveWeightSideInfoCollisionOverBase invariantVisibleData
        (fun u : ExactVisiblePostSwitchSurface Bool 1 => u.b)
        (activeOrbitWeight false) ∧
      (∃ u : ExactVisiblePostSwitchSurface Bool 1,
        0 < activeOrbitWeight false u ∧
          invariantVisibleData (tiInputMap u) = invariantVisibleData u ∧
          (tiInputMap u).b ≠ u.b) ∧
      (∃ u : ExactVisiblePostSwitchSurface Bool 1,
        0 < activeOrbitWeight false u ∧
          ¬ SourceOnlyPredicateCapturesSideEq invariantVisibleData
            (fun u : ExactVisiblePostSwitchSurface Bool 1 => u.b) (u.b)) := by
  exact
    exactPostSwitch_activeOrbit_realizes_pure_residual_obstruction_package
      (Z := Bool) false

end Mettapedia.Computability.PNP.PostSwitchResidualWitnessRegression
