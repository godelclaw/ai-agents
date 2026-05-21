import Mettapedia.FluidDynamics.NavierStokes.NavierStokesHeatShearFiniteEnergyObstruction

/-!
# Navier-Stokes heat-shear finite-energy obstruction regression

Focused theorem-level checks for the manuscript-facing heat-shear finite-energy
obstruction file.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace NavierStokesHeatShearFiniteEnergyObstructionRegression

theorem not_finiteInitialKineticEnergy_heatShearInitialVelocity_regression :
    ¬ finiteInitialKineticEnergy (heatShearInitialVelocity 1 1) := by
  exact
    not_finiteInitialKineticEnergy_heatShearInitialVelocity_of_amplitude_mul_wavenumber_ne_zero
      (a := 1) (k := 1) (by norm_num)

theorem not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_heatShearFullDrift_regression :
    ¬ Nonempty { P : FiniteEnergyAdmissibleNavierStokesProblemData //
        P.initialVelocity = heatShearFullDriftInitialVelocity 1 1 1 1 } := by
  exact
    not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_heatShearFullDriftInitialVelocity_of_streamwiseDrift_ne_zero_or_verticalDrift_ne_zero_or_amplitude_mul_wavenumber_ne_zero
      (a := 1) (k := 1) (d := 1) (c := 1) (Or.inl one_ne_zero)

theorem not_finiteInitialKineticEnergy_heatShearTransportInitialVelocity_regression :
    ¬ finiteInitialKineticEnergy (heatShearTransportInitialVelocity 1 1 1) := by
  exact
    not_finiteInitialKineticEnergy_heatShearTransportInitialVelocity_of_transport_ne_zero_or_amplitude_mul_wavenumber_ne_zero
      (a := 1) (k := 1) (b := 1) (Or.inl one_ne_zero)

theorem not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_heatShearTransportFullDrift_regression :
    ¬ Nonempty { P : FiniteEnergyAdmissibleNavierStokesProblemData //
        P.initialVelocity = heatShearTransportFullDriftInitialVelocity 1 1 1 1 1 } := by
  exact
    not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_heatShearTransportFullDriftInitialVelocity_of_transport_ne_zero_or_streamwiseDrift_ne_zero_or_verticalDrift_ne_zero_or_amplitude_mul_wavenumber_ne_zero
      (a := 1) (k := 1) (b := 1) (d := 1) (c := 1) (Or.inl one_ne_zero)

end NavierStokesHeatShearFiniteEnergyObstructionRegression
end NavierStokes
end FluidDynamics
end Mettapedia
