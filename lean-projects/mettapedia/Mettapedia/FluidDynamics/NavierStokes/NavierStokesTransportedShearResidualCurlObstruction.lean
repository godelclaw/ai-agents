import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMContinuationTarget

/-!
# Transported shear residual-curl obstructions

This file composes the concrete residual-curl computation for transported
arbitrary-amplitude shear with the explicit finite-time, BKM, and global-output
Navier--Stokes target surfaces.

The obstruction is not tied to a pressure ansatz.  If the sampled scalar
amplitude fails the heat ODE, the exact pressure residual has nonzero curl at
the transported phase point, so no smooth pressure field can make that velocity
occupy any of these exact target slots.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section TransportedShearResidualCurlObstruction

/-- A transported arbitrary-amplitude shear field whose scalar amplitude misses
the heat ODE at a point of the certified slab cannot be the exact velocity of a
finite-time witness on that slab. -/
theorem not_exists_ExplicitFiniteTimeRegularityWitness_velocity_amplitudeShearTransportVelocityField_of_heatODE_mismatch_at
    {A : NSTime → ℝ} {A' ν k b T : ℝ} {t : NSTime} {u₀ : NSInitialVelocity}
    (hA : HasDerivAt A A' t)
    (hode : A' + ν * k ^ (2 : ℕ) * A t ≠ 0) (hk : k ≠ 0)
    (ht0 : 0 ≤ t) (htT : t ≤ T) :
    ¬ ∃ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
      W.velocity = amplitudeShearTransportVelocityField A k b := by
  exact
    not_exists_ExplicitFiniteTimeRegularityWitness_velocity_of_momentumPressureResidual_vorticity_ne_zero_on
      (ν := ν) (T := T) (u₀ := u₀)
      (u := amplitudeShearTransportVelocityField A k b)
      ⟨t, EuclideanSpace.single nsCoord1 (b * t), ht0, htT,
        spatialVorticity_momentumPressureResidual_amplitudeShearTransportVelocityField_phasePoint_ne_zero
          hA hode hk⟩

/-- The BKM envelope layer cannot hide the same transported-shear residual-curl
obstruction: once the exact finite-time velocity is impossible, adding a
time-integrable vorticity envelope adds no repair route. -/
theorem not_exists_BKMData_velocity_amplitudeShearTransportVelocityField_of_heatODE_mismatch_at
    {A : NSTime → ℝ} {A' ν k b T : ℝ} {t : NSTime} {u₀ : NSInitialVelocity}
    (hA : HasDerivAt A A' t)
    (hode : A' + ν * k ^ (2 : ℕ) * A t ≠ 0) (hk : k ≠ 0)
    (ht0 : 0 ≤ t) (htT : t ≤ T) :
    ¬ ∃ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
      W.velocity = amplitudeShearTransportVelocityField A k b ∧
        ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
          vorticityEnvelopeOn W.velocity T Ω ∧
            integrableVorticityEnvelopeOn Ω T B := by
  exact
    not_exists_BKMData_velocity_of_momentumPressureResidual_vorticity_ne_zero_on
      (ν := ν) (T := T) (u₀ := u₀)
      (u := amplitudeShearTransportVelocityField A k b)
      ⟨t, EuclideanSpace.single nsCoord1 (b * t), ht0, htT,
        spatialVorticity_momentumPressureResidual_amplitudeShearTransportVelocityField_phasePoint_ne_zero
          hA hode hk⟩

/-- A transported arbitrary-amplitude shear field with a sampled heat-ODE defect
cannot be the prescribed velocity of a whole-space global output at the same
viscosity. -/
theorem not_ExplicitConcreteNavierStokesGlobalOutputWithVelocity_amplitudeShearTransportVelocityField_of_heatODE_mismatch_at
    {A : NSTime → ℝ} {A' ν k b : ℝ} {t : NSTime} {u₀ : NSInitialVelocity}
    (hA : HasDerivAt A A' t)
    (hode : A' + ν * k ^ (2 : ℕ) * A t ≠ 0) (hk : k ≠ 0) :
    ¬ ExplicitConcreteNavierStokesGlobalOutputWithVelocity ν u₀
      (amplitudeShearTransportVelocityField A k b) := by
  exact
    not_ExplicitConcreteNavierStokesGlobalOutputWithVelocity_of_momentumPressureResidual_vorticity_ne_zero
      (ν := ν) (u₀ := u₀)
      (u := amplitudeShearTransportVelocityField A k b)
      ⟨t, EuclideanSpace.single nsCoord1 (b * t),
        spatialVorticity_momentumPressureResidual_amplitudeShearTransportVelocityField_phasePoint_ne_zero
          hA hode hk⟩

end TransportedShearResidualCurlObstruction

end NavierStokes
end FluidDynamics
end Mettapedia
