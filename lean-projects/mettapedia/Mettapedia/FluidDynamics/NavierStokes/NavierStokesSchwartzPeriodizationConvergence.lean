import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSchwartzPeriodizationBoxes

/-!
# Navier-Stokes Schwartz Periodization Convergence Interface

This file packages the first explicit local convergence interface sitting above
the finite box exhaustion family from `NavierStokesSchwartzPeriodizationBoxes`.
Instead of proving the Schwartz periodization limit outright, we isolate the
exact theorem surface that Appendix H.4 uses on fixed cubes `Q_R`: if the boxed
partial periodizations converge locally, then the shell increments must vanish
locally as well.
-/

set_option autoImplicit false

noncomputable section

open Filter

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

/-- The centered spatial cube `Q_R = [-R, R]^3 ⊂ ℝ^3`. -/
def spatialCube (R : ℝ) : Set NSSpace :=
  { x | ∀ i : Fin 3, |x i| ≤ R }

/-- Membership in `Q_R` is the expected coordinatewise bound. -/
theorem mem_spatialCube_iff {R : ℝ} {x : NSSpace} :
    x ∈ spatialCube R ↔ ∀ i : Fin 3, |x i| ≤ R :=
  Iff.rfl

/-- Larger radii contain smaller centered cubes. -/
theorem spatialCube_mono {R S : ℝ} (hRS : R ≤ S) :
    spatialCube R ⊆ spatialCube S := by
  intro x hx
  rw [mem_spatialCube_iff] at hx ⊢
  intro i
  exact (hx i).trans hRS

/-- The shell contribution added when enlarging the boxed partial periodization
from radius `N` to radius `N + 1`. -/
def boxedPeriodizationShellInitialVelocity
    (N : ℕ) (L : ℝ) (u₀ : NSInitialVelocity) :
    NSInitialVelocity :=
  finitePartialPeriodizedInitialVelocity (centeredLatticeShell N) L u₀

/-- The shell contribution is exactly the one-step difference of boxed partial
periodizations. -/
theorem boxedPeriodizationShellInitialVelocity_eq_sub
    (N : ℕ) (L : ℝ) (u₀ : NSInitialVelocity) :
    boxedPeriodizationShellInitialVelocity N L u₀ =
      boxedPartialPeriodizedInitialVelocity (N + 1) L u₀ -
        boxedPartialPeriodizedInitialVelocity N L u₀ := by
  funext x
  apply eq_sub_iff_add_eq.mpr
  simpa [boxedPeriodizationShellInitialVelocity, add_comm, add_left_comm, add_assoc] using
    (congrFun (boxedPartialPeriodizedInitialVelocity_succ N L u₀) x).symm

/-- Local convergence of the boxed partial periodizations on a set `s`. -/
def BoxedPartialPeriodizationConvergesOn
    (s : Set NSSpace) (L : ℝ) (u₀ u : NSInitialVelocity) : Prop :=
  ∀ x ∈ s, Tendsto (fun N => boxedPartialPeriodizedInitialVelocity N L u₀ x)
    Filter.atTop (nhds (u x))

/-- Local convergence of the boxed partial periodizations on the centered cube
`Q_R`. -/
def BoxedPartialPeriodizationConvergesOnCube
    (R L : ℝ) (u₀ u : NSInitialVelocity) : Prop :=
  BoxedPartialPeriodizationConvergesOn (spatialCube R) L u₀ u

theorem BoxedPartialPeriodizationConvergesOn.mono
    {s t : Set NSSpace} {L : ℝ} {u₀ u : NSInitialVelocity}
    (hconv : BoxedPartialPeriodizationConvergesOn t L u₀ u)
    (hst : s ⊆ t) :
    BoxedPartialPeriodizationConvergesOn s L u₀ u := by
  intro x hx
  exact hconv x (hst hx)

theorem BoxedPartialPeriodizationConvergesOnCube.mono
    {R S L : ℝ} {u₀ u : NSInitialVelocity}
    (hconv : BoxedPartialPeriodizationConvergesOnCube S L u₀ u)
    (hRS : R ≤ S) :
    BoxedPartialPeriodizationConvergesOnCube R L u₀ u := by
  exact BoxedPartialPeriodizationConvergesOn.mono hconv (spatialCube_mono hRS)

/-- If the boxed partial periodizations converge locally, the added shell
contributions vanish locally. -/
theorem boxedPeriodizationShellInitialVelocity_tendsto_zero_on_of_convergesOn
    {s : Set NSSpace} {L : ℝ} {u₀ u : NSInitialVelocity}
    (hconv : BoxedPartialPeriodizationConvergesOn s L u₀ u) :
    ∀ x ∈ s, Tendsto (fun N => boxedPeriodizationShellInitialVelocity N L u₀ x)
      Filter.atTop (nhds 0) := by
  intro x hx
  have hconv_x := hconv x hx
  have hsucc_x :
      Tendsto (fun N => boxedPartialPeriodizedInitialVelocity (N + 1) L u₀ x)
        Filter.atTop (nhds (u x)) := by
    exact hconv_x.comp (tendsto_add_atTop_nat 1)
  have hdiff :
      Tendsto
        (fun N =>
          boxedPartialPeriodizedInitialVelocity (N + 1) L u₀ x -
            boxedPartialPeriodizedInitialVelocity N L u₀ x)
        Filter.atTop (nhds (u x - u x)) :=
    hsucc_x.sub hconv_x
  simpa [boxedPeriodizationShellInitialVelocity_eq_sub] using hdiff

/-- Cube-local convergence implies vanishing shell increments on the same cube. -/
theorem boxedPeriodizationShellInitialVelocity_tendsto_zero_onCube_of_convergesOnCube
    {R L : ℝ} {u₀ u : NSInitialVelocity}
    (hconv : BoxedPartialPeriodizationConvergesOnCube R L u₀ u) :
    ∀ x ∈ spatialCube R,
      Tendsto (fun N => boxedPeriodizationShellInitialVelocity N L u₀ x)
        Filter.atTop (nhds 0) :=
  boxedPeriodizationShellInitialVelocity_tendsto_zero_on_of_convergesOn hconv

end NavierStokes
end FluidDynamics
end Mettapedia
