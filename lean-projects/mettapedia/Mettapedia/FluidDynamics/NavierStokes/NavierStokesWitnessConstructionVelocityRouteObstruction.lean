import Mettapedia.FluidDynamics.NavierStokes.NavierStokesTransportedShearResidualCurlObstruction
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesWitnessConstructionGlobalOutputObstruction

/-!
# Witness-Construction Velocity-Route Obstruction

This file packages the currently formalized pressure-agnostic repair surfaces
for a prescribed velocity field:

* an exact finite-time witness with that velocity,
* the same witness plus a uniform vorticity bound,
* the same witness plus BKM envelope data, and
* the prescribed-velocity exact whole-space output surface.

Because all four branches still rely on the same exact finite-time witness
velocity, the bundle is conservative.  Consequently, a nonzero curl in the
exact pressure residual blocks the whole velocity route at once, independent of
any pressure ansatz.

As a concrete bottom-up instance, the file specializes the route obstruction to
transported arbitrary-amplitude shear fields whose scalar amplitude misses the
heat ODE at a sampled slab point.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

/-- The currently formalized pressure-agnostic witness-construction repair
surfaces for a prescribed velocity field on a slab and the corresponding
prescribed-velocity exact whole-space output surface. -/
def VelocityWitnessConstructionRoute
    (ν T : ℝ) (u₀ : NSInitialVelocity) (u : NSVelocityField) : Prop :=
  (∃ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
      W.velocity = u) ∨
    (∃ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
      W.velocity = u ∧
        ∃ B : ℝ, uniformVorticityBoundUpTo W.velocity T B) ∨
    (∃ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
      W.velocity = u ∧
        ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
          vorticityEnvelopeOn W.velocity T Ω ∧
            integrableVorticityEnvelopeOn Ω T B) ∨
    ExplicitConcreteNavierStokesGlobalOutputWithVelocity ν u₀ u

/-- The older uniform-vorticity packaging layer cannot hide a non-curl-free
exact pressure residual either: once the same velocity is impossible as an
exact witness, adding a slab vorticity bound does not repair it. -/
theorem not_exists_uniformVorticityData_velocity_of_momentumPressureResidual_vorticity_ne_zero_on
    {ν T : ℝ} {u₀ : NSInitialVelocity} {u : NSVelocityField}
    (hcurl : ∃ t : NSTime, ∃ x : NSSpace,
      0 ≤ t ∧ t ≤ T ∧
        spatialVorticity (momentumPressureResidual ν u) t x ≠ 0) :
    ¬ ∃ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
      W.velocity = u ∧
        ∃ B : ℝ, uniformVorticityBoundUpTo W.velocity T B := by
  intro hW
  apply
    not_exists_ExplicitFiniteTimeRegularityWitness_velocity_of_momentumPressureResidual_vorticity_ne_zero_on
      (ν := ν) (T := T) (u₀ := u₀) (u := u) hcurl
  rcases hW with ⟨W, hWvel, _B, _hω⟩
  exact ⟨W, hWvel⟩

/-- The bundled pressure-agnostic witness-construction route is conservative:
it exists exactly when the prescribed velocity already exists as an exact
finite-time witness on the slab.  The extra uniform-vorticity, BKM, and
prescribed-global wrappers add no new velocity inhabitants. -/
theorem VelocityWitnessConstructionRoute_iff_exists_finiteTimeWitness_velocity
    {ν T : ℝ} {u₀ : NSInitialVelocity} {u : NSVelocityField} :
    VelocityWitnessConstructionRoute ν T u₀ u ↔
      ∃ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
        W.velocity = u := by
  constructor
  · intro hRoute
    rcases hRoute with hExact | hRoute
    · exact hExact
    rcases hRoute with hUniform | hRoute
    · rcases hUniform with ⟨W, hWvel, _B, _hω⟩
      exact ⟨W, hWvel⟩
    rcases hRoute with hBKM | hGlobal
    · rcases hBKM with ⟨W, hWvel, _Ω, _B, _hEnv, _hInt⟩
      exact ⟨W, hWvel⟩
    · rw [ExplicitConcreteNavierStokesGlobalOutputWithVelocity_iff_exists_pressure] at hGlobal
      rcases hGlobal with ⟨p, hGlobal⟩
      rcases
          ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure.implies_finiteTimeWitness
            (T := T) hGlobal with
        ⟨W, hWvel, _hWpress⟩
      exact ⟨W, hWvel⟩
  · intro hW
    exact Or.inl hW

/-- A slabwise exact-witness obstruction already blocks every currently
formalized pressure-agnostic witness-construction repair surface for the same
velocity. -/
theorem not_VelocityWitnessConstructionRoute_of_not_exists_finiteTimeWitness_velocity
    {ν T : ℝ} {u₀ : NSInitialVelocity} {u : NSVelocityField}
    (hW :
      ¬ ∃ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
          W.velocity = u) :
    ¬ VelocityWitnessConstructionRoute ν T u₀ u := by
  intro hRoute
  rw [VelocityWitnessConstructionRoute_iff_exists_finiteTimeWitness_velocity] at hRoute
  exact hW hRoute

/-- A nonzero curl in the exact pressure residual blocks the whole bundled
pressure-agnostic witness-construction route for that velocity. -/
theorem not_VelocityWitnessConstructionRoute_of_momentumPressureResidual_vorticity_ne_zero_on
    {ν T : ℝ} {u₀ : NSInitialVelocity} {u : NSVelocityField}
    (hcurl : ∃ t : NSTime, ∃ x : NSSpace,
      0 ≤ t ∧ t ≤ T ∧
        spatialVorticity (momentumPressureResidual ν u) t x ≠ 0) :
    ¬ VelocityWitnessConstructionRoute ν T u₀ u := by
  exact
    not_VelocityWitnessConstructionRoute_of_not_exists_finiteTimeWitness_velocity
      (not_exists_ExplicitFiniteTimeRegularityWitness_velocity_of_momentumPressureResidual_vorticity_ne_zero_on
        (ν := ν) (T := T) (u₀ := u₀) (u := u) hcurl)

/-- Concrete transported-shear specialization: if the sampled scalar amplitude
misses the heat ODE at one certified slab point, then no pressure choice can
promote that velocity to any currently formalized witness-construction repair
surface. -/
theorem not_VelocityWitnessConstructionRoute_amplitudeShearTransportVelocityField_of_heatODE_mismatch_at
    {A : NSTime → ℝ} {A' ν k b T : ℝ} {t : NSTime} {u₀ : NSInitialVelocity}
    (hA : HasDerivAt A A' t)
    (hode : A' + ν * k ^ (2 : ℕ) * A t ≠ 0) (hk : k ≠ 0)
    (ht0 : 0 ≤ t) (htT : t ≤ T) :
    ¬ VelocityWitnessConstructionRoute ν T u₀
      (amplitudeShearTransportVelocityField A k b) := by
  refine
    not_VelocityWitnessConstructionRoute_of_momentumPressureResidual_vorticity_ne_zero_on
      (ν := ν) (T := T) (u₀ := u₀)
      (u := amplitudeShearTransportVelocityField A k b) ?_
  refine ⟨t, EuclideanSpace.single nsCoord1 (b * t), ht0, htT, ?_⟩
  exact
    spatialVorticity_momentumPressureResidual_amplitudeShearTransportVelocityField_phasePoint_ne_zero
      hA hode hk

end NavierStokes
end FluidDynamics
end Mettapedia
