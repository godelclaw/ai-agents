import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSchwartzDirectionalRigidity
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3

/-!
# Schwartz Obstruction for the Concrete Heat-Shear Datum

This file turns the abstract directional-rigidity theorem for Schwartz profiles
into a concrete obstruction for the explicit heat-shear initial datum
`x ↦ (a * sin (k * x₁), 0, 0)` on `ℝ^3`.

The datum is translation invariant along the `x₀` direction.  Therefore any
Schwartz initial velocity equal to it must vanish identically.  For nonzero
amplitude and wavenumber, a one-point evaluation shows that the heat-shear
datum is not zero, so no such Schwartz realization can exist.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

/-- The streamwise basis direction `e₀` in `ℝ^3`. -/
def heatShearStreamwiseDirection : NSSpace :=
  EuclideanSpace.single nsCoord0 (1 : ℝ)

theorem heatShearStreamwiseDirection_ne_zero :
    heatShearStreamwiseDirection ≠ 0 := by
  intro h
  have hcoord := congrArg (fun x : NSSpace => x nsCoord0) h
  simp [heatShearStreamwiseDirection, nsCoord0] at hcoord

/-- The concrete heat-shear initial datum depends only on the transverse
coordinate `x₁`, so it is invariant under streamwise translation. -/
theorem translationInvariantAlong_heatShearInitialVelocity_streamwise
    (a k : ℝ) :
    TranslationInvariantAlong heatShearStreamwiseDirection
      (heatShearInitialVelocity a k) := by
  intro x s
  rw [heatShearInitialVelocity_apply, heatShearInitialVelocity_apply]
  ext i
  fin_cases i <;>
    simp [heatShearStreamwiseDirection, nsCoord0, nsCoord1]

/-- A nondegenerate heat-shear initial datum is not the zero velocity field. -/
theorem heatShearInitialVelocity_ne_zero_of_amplitude_ne_zero_of_wavenumber_ne_zero
    {a k : ℝ} (ha : a ≠ 0) (hk : k ≠ 0) :
    heatShearInitialVelocity a k ≠ (0 : NSInitialVelocity) := by
  intro hzero
  let x1 : NSSpace := EuclideanSpace.single nsCoord1 ((Real.pi / 2) / k)
  have hzeroAt : heatShearInitialVelocity a k x1 = 0 := by
    simpa using congrArg (fun u : NSInitialVelocity => u x1) hzero
  have hx1coord : x1 nsCoord1 = (Real.pi / 2) / k := by
    simp [x1, nsCoord1]
  have hkpi : k * ((Real.pi / 2) / k) = Real.pi / 2 := by
    field_simp [hk]
  have hvalue : heatShearInitialVelocity a k x1 = EuclideanSpace.single nsCoord0 a := by
    rw [heatShearInitialVelocity_apply, hx1coord, hkpi, Real.sin_pi_div_two]
    simp
  rw [hvalue] at hzeroAt
  have hcoord := congrArg (fun v : NSSpace => v nsCoord0) hzeroAt
  simp [nsCoord0] at hcoord
  exact ha hcoord

/-- No nondegenerate heat-shear initial datum can lie in the Schwartz initial
data lane, because its streamwise translation invariance would force it to
vanish. -/
theorem not_exists_schwartzInitialVelocity_eq_heatShearInitialVelocity_of_amplitude_ne_zero_of_wavenumber_ne_zero
    {a k : ℝ} (ha : a ≠ 0) (hk : k ≠ 0) :
    ¬ ∃ u₀ : NSSchwartzInitialVelocity,
        (u₀ : NSInitialVelocity) = heatShearInitialVelocity a k := by
  intro h
  rcases h with ⟨u₀, hu₀⟩
  have hinv :
      TranslationInvariantAlong heatShearStreamwiseDirection
        (u₀ : NSInitialVelocity) := by
    simpa [hu₀] using
      translationInvariantAlong_heatShearInitialVelocity_streamwise a k
  have huzero : (u₀ : NSInitialVelocity) = 0 := by
    exact
      schwartzInitialVelocity_eq_zero_of_translationInvariantAlong u₀
        heatShearStreamwiseDirection_ne_zero hinv
  have hheatzero : heatShearInitialVelocity a k = (0 : NSInitialVelocity) := by
    simpa [hu₀] using huzero
  exact
    heatShearInitialVelocity_ne_zero_of_amplitude_ne_zero_of_wavenumber_ne_zero
      ha hk hheatzero

end NavierStokes
end FluidDynamics
end Mettapedia
