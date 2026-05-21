import Mettapedia.FluidDynamics.NavierStokes.NavierStokesLinearShearFiniteEnergyObstruction

/-!
# Navier-Stokes linear-shear finite-energy obstruction regression

Focused theorem-level checks for the manuscript-facing affine linear-shear
finite-energy obstruction file.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace NavierStokesLinearShearFiniteEnergyObstructionRegression

theorem not_finiteInitialKineticEnergy_linearShearInitialVelocity_regression :
    ¬ finiteInitialKineticEnergy (linearShearInitialVelocity 1) := by
  exact not_finiteInitialKineticEnergy_linearShearInitialVelocity_of_shear_ne_zero one_ne_zero

theorem not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_linearShearVerticalDrift_regression :
    ¬ Nonempty { P : FiniteEnergyAdmissibleNavierStokesProblemData //
        P.initialVelocity = linearShearVerticalDriftInitialVelocity 1 1 } := by
  exact
    not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_linearShearVerticalDriftInitialVelocity_of_shear_ne_zero_or_verticalDrift_ne_zero
      (a := 1) (c := 1) (Or.inl one_ne_zero)

theorem not_finiteInitialKineticEnergy_linearShearHorizontalDrift_regression :
    ¬ finiteInitialKineticEnergy (linearShearHorizontalDriftInitialVelocity 1 1) := by
  exact
    not_finiteInitialKineticEnergy_linearShearHorizontalDriftInitialVelocity_of_shear_ne_zero_or_horizontalDrift_ne_zero
      (a := 1) (b := 1) (Or.inl one_ne_zero)

theorem not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_linearShearFullDrift_regression :
    ¬ Nonempty { P : FiniteEnergyAdmissibleNavierStokesProblemData //
        P.initialVelocity = linearShearFullDriftInitialVelocity 1 1 1 } := by
  exact
    not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_linearShearFullDriftInitialVelocity_of_parameter_ne_zero
      (a := 1) (b := 1) (c := 1) (Or.inl one_ne_zero)

end NavierStokesLinearShearFiniteEnergyObstructionRegression
end NavierStokes
end FluidDynamics
end Mettapedia
