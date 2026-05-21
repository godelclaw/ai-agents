import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeSchwartzBKMBridge
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesWitnessConstructionGlobalOutputObstruction

/-!
# Finite-Mode Affine-Pressure Exact Obstructions

This file pushes the constant-one two-mode affine-plus-localized pressure
obstruction onto the exact finite-time witness and exact whole-space output
surfaces.

The key point is that this bounded velocity already carries its own BKM
envelope. Therefore the existing BKM no-go theorem does not merely block one
packaged continuation route; it also blocks the underlying exact witness and,
via slab restriction, the exact global output with the same pressure family.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff RealInnerProductSpace SchwartzMap

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

/-- The finite two-pair affine-plus-localized pressure obstruction for the
constant-one two-mode branch already rules out exact finite-time witnesses.
The branch is uniformly bounded in vorticity, so any exact witness would
automatically extend to BKM data and contradict the existing no-go theorem. -/
theorem
    not_exists_ExplicitFiniteTimeRegularityWitness_oneOneTwoModeSchwartzVelocity_affineAddScalarSchwartzPressure_of_same_pressureGradient_pair_lapSum_pair_ne_on
    {ν T : ℝ} (hν : 0 < ν) (f g : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0)
    (hbad : ∃ t x₁ y₁ x₂ y₂,
        0 ≤ t ∧ t ≤ T ∧
          (spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x₁ -
              spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y₁) =
            (spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x₂ -
              spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y₂) ∧
          ((spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x₁ +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x₁) -
              (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y₁ +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y₁)) ≠
            ((spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x₂ +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x₂) -
              (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y₂ +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y₂))) :
    ¬ ∃ c : NSTime → NSSpace, ∃ π : NSTime → ℝ, ∃ ρ : NSTime → ℝ,
      ∃ W : ExplicitFiniteTimeRegularityWitness
          ν (twoModeSchwartzInitialVelocity 1 1 f g) T,
        W.velocity =
            twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q := by
  intro hW
  rcases hW with ⟨c, π, ρ, W, hWvel, hWpress⟩
  rcases
      twoModeSchwartzVelocity_exhibits_BKMEnvelope_of_abs_le
        (a := fun _ : NSTime => 1)
        (b := fun _ : NSTime => 1)
        (f := f)
        (g := g)
        (A := 1)
        (B := 1)
        (T := T)
        (by intro t; norm_num)
        (by intro t; norm_num) with
    ⟨Ω, Bint, hEnv, hInt⟩
  exact
    not_exists_BKMData_oneOneTwoMode_affineAddScalarSchwartzPressure_of_same_pressureGradient_pair_lapSum_pair_ne_on
      hν f g q hclosure hbad
      ⟨c, π, ρ, W, hWvel, hWpress, Ω, Bint, by simpa [hWvel] using hEnv, hInt⟩

/-- The same finite two-pair affine-plus-localized pressure obstruction also
rules out exact whole-space outputs with that pressure family. Any exact global
output would restrict to an exact finite-time witness on the certified slab,
which is already impossible. -/
theorem
    not_exists_ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure_oneOneTwoModeSchwartzVelocity_affineAddScalarSchwartzPressure_of_same_pressureGradient_pair_lapSum_pair_ne_on
    {ν T : ℝ} (hν : 0 < ν) (f g : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0)
    (hbad : ∃ t x₁ y₁ x₂ y₂,
        0 ≤ t ∧ t ≤ T ∧
          (spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x₁ -
              spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y₁) =
            (spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x₂ -
              spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y₂) ∧
          ((spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x₁ +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x₁) -
              (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y₁ +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y₁)) ≠
            ((spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x₂ +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x₂) -
              (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y₂ +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y₂))) :
    ¬ ∃ c : NSTime → NSSpace, ∃ π : NSTime → ℝ, ∃ ρ : NSTime → ℝ,
      ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure
        ν
        (twoModeSchwartzInitialVelocity 1 1 f g)
        (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g)
        (affineAddScalarSchwartzPressure c π ρ q) := by
  intro hGlobal
  rcases hGlobal with ⟨c, π, ρ, hPair⟩
  have hW :
      ¬ ∃ W : ExplicitFiniteTimeRegularityWitness ν (twoModeSchwartzInitialVelocity 1 1 f g) T,
          W.velocity =
              twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g ∧
            W.pressure = affineAddScalarSchwartzPressure c π ρ q := by
    intro hWitness
    rcases hWitness with ⟨W, hWvel, hWpress⟩
    exact
      not_exists_ExplicitFiniteTimeRegularityWitness_oneOneTwoModeSchwartzVelocity_affineAddScalarSchwartzPressure_of_same_pressureGradient_pair_lapSum_pair_ne_on
        hν f g q hclosure hbad
        ⟨c, π, ρ, W, hWvel, hWpress⟩
  exact
    (not_ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure_of_not_exists_finiteTimeWitness
      (ν := ν)
      (T := T)
      (u₀ := twoModeSchwartzInitialVelocity 1 1 f g)
      (u := twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g)
      (p := affineAddScalarSchwartzPressure c π ρ q)
      hW) hPair

/-- Route-level exact-surface separation for the non-cancelling constant-one
two-mode branch. The branch has a nonzero inviscid exact witness, but the same
velocity cannot be promoted to positive-viscosity exact witness or exact
whole-space output through the affine-plus-localized Schwartz pressure family
once the finite two-pair mismatch is present on the slab. -/
theorem oneOneTwoModeSchwartzVelocity_exactSurfaceSeparation_of_same_pressureGradient_pair_lapSum_pair_ne_on
    {ν T : ℝ} (hν : 0 < ν) (f g : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hfg : ∃ x : NSSpace, f x + g x ≠ 0)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0)
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0)
    (hbad : ∃ t x₁ y₁ x₂ y₂,
        0 ≤ t ∧ t ≤ T ∧
          (spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x₁ -
              spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y₁) =
            (spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x₂ -
              spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y₂) ∧
          ((spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x₁ +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x₁) -
              (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y₁ +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y₁)) ≠
            ((spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x₂ +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x₂) -
              (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y₂ +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y₂))) :
    (((∃ t x,
        twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g t x ≠
          (0 : NSSpace)) ∧
        ∃ W :
            ExplicitFiniteTimeRegularityWitness 0
              (twoModeSchwartzInitialVelocity 1 1 f g) T,
          W.velocity =
              twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g ∧
            W.pressure = (0 : NSPressureField)) ∧
      ¬ ∃ c : NSTime → NSSpace, ∃ π : NSTime → ℝ, ∃ ρ : NSTime → ℝ,
          ∃ W : ExplicitFiniteTimeRegularityWitness
              ν (twoModeSchwartzInitialVelocity 1 1 f g) T,
            W.velocity =
                twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g ∧
              W.pressure = affineAddScalarSchwartzPressure c π ρ q) ∧
      ¬ ∃ c : NSTime → NSSpace, ∃ π : NSTime → ℝ, ∃ ρ : NSTime → ℝ,
          ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure
            ν
            (twoModeSchwartzInitialVelocity 1 1 f g)
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g)
            (affineAddScalarSchwartzPressure c π ρ q) := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · exact oneOneTwoModeSchwartzVelocity_nonzero_of_exists_profile_sum_ne_zero f g hfg
      · let W :=
            ExplicitFiniteTimeRegularityWitness.of_oneOneTwoModeSchwartzVelocity_inviscidZeroPressure
              f g hfDiv hgDiv hclosure (T := T)
        have hWvel :
            W.velocity =
              twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g := by
          rfl
        have hWpressure : W.pressure = (0 : NSPressureField) := by
          have hWpressureAffine :
              W.pressure =
                affineAddScalarSchwartzPressure (fun _ : NSTime => 0) (fun _ : NSTime => 0)
                  (fun _ : NSTime => 0) (0 : 𝓢(NSSpace, ℝ)) := by
            rfl
          have hAffineZero :
              affineAddScalarSchwartzPressure (fun _ : NSTime => 0) (fun _ : NSTime => 0)
                  (fun _ : NSTime => 0) (0 : 𝓢(NSSpace, ℝ)) =
                (0 : NSPressureField) := by
            funext t x
            simp [affineAddScalarSchwartzPressure]
          exact hWpressureAffine.trans hAffineZero
        exact ⟨W, hWvel, hWpressure⟩
    · exact
        not_exists_ExplicitFiniteTimeRegularityWitness_oneOneTwoModeSchwartzVelocity_affineAddScalarSchwartzPressure_of_same_pressureGradient_pair_lapSum_pair_ne_on
          hν f g q hclosure hbad
  · exact
      not_exists_ExplicitConcreteNavierStokesGlobalOutputWithVelocityPressure_oneOneTwoModeSchwartzVelocity_affineAddScalarSchwartzPressure_of_same_pressureGradient_pair_lapSum_pair_ne_on
        hν f g q hclosure hbad

end NavierStokes
end FluidDynamics
end Mettapedia
