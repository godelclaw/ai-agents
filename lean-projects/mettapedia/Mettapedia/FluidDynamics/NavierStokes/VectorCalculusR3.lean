import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEquationTarget
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Vector Calculus on `ℝ^3` for the Concrete NS Surface

This file starts the bottom-up NS tranche. It keeps the literal
`ℝ × ℝ^3` theorem surface from `NavierStokesEquationTarget.lean`, but extracts a
reusable vector-calculus layer on top of it:

- coordinate derivatives and curl/vorticity on `ℝ^3`;
- linearity and zero lemmas for the concrete first-order operators;
- linearity lemmas for the concrete pressure gradient and Laplacian.

The goal is lasting value: these are concrete theorems about actual Mathlib
operators on `ℝ^3`, not more abstract interface shells.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open scoped Gradient
open scoped Laplacian
open scoped BigOperators
open scoped ContDiff

section VectorCalculusR3

/-- The coordinate `0` in `Fin 3`. -/
def nsCoord0 : Fin 3 := ⟨0, by decide⟩

/-- The coordinate `1` in `Fin 3`. -/
def nsCoord1 : Fin 3 := ⟨1, by decide⟩

/-- The coordinate `2` in `Fin 3`. -/
def nsCoord2 : Fin 3 := ⟨2, by decide⟩

/-- Constant velocity field on `ℝ × ℝ^3`. -/
def constantVelocityField (c : NSSpace) : NSVelocityField :=
  fun _ : NSTime => fun _ : NSSpace => c

/-- Constant initial velocity data on `ℝ^3`. -/
def constantInitialVelocity (c : NSSpace) : NSInitialVelocity :=
  fun _ : NSSpace => c

/-- Addition of constant initial data is again constant initial data. -/
theorem constantInitialVelocity_add
    (u v : NSSpace) :
    constantInitialVelocity u + constantInitialVelocity v =
      constantInitialVelocity (u + v) := by
  funext x
  simp [constantInitialVelocity]

/-- Linear shear map `x ↦ (a * x₁, 0, 0)` on `ℝ^3`. -/
def linearShearMap (a : ℝ) : NSSpace →L[ℝ] NSSpace :=
  ((EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ)).smulRight
    (EuclideanSpace.single nsCoord0 a)

/-- Linear shear initial velocity data `x ↦ (a * x₁, 0, 0)` on `ℝ^3`. -/
def linearShearInitialVelocity (a : ℝ) : NSInitialVelocity :=
  linearShearMap a

/-- Steady linear shear velocity field `u(t,x) = (a * x₁, 0, 0)` on
`ℝ × ℝ^3`. -/
def linearShearVelocityField (a : ℝ) : NSVelocityField :=
  fun _ : NSTime => linearShearInitialVelocity a

/-- Initial velocity data `x ↦ (a * x₁, 0, b)` on `ℝ^3`. -/
def linearShearVerticalDriftInitialVelocity (a b : ℝ) : NSInitialVelocity :=
  linearShearInitialVelocity a +
    constantInitialVelocity (EuclideanSpace.single nsCoord2 b)

/-- Steady velocity field `u(t,x) = (a * x₁, 0, b)` on `ℝ × ℝ^3`. -/
def linearShearVerticalDriftVelocityField (a b : ℝ) : NSVelocityField :=
  linearShearVelocityField a +
    constantVelocityField (EuclideanSpace.single nsCoord2 b)

/-- Initial velocity data `x ↦ (a * x₁, b, 0)` on `ℝ^3`. -/
def linearShearHorizontalDriftInitialVelocity (a b : ℝ) : NSInitialVelocity :=
  linearShearInitialVelocity a +
    constantInitialVelocity (EuclideanSpace.single nsCoord1 b)

/-- Steady velocity field `u(t,x) = (a * x₁, b, 0)` on `ℝ × ℝ^3`. -/
def linearShearHorizontalDriftVelocityField (a b : ℝ) : NSVelocityField :=
  linearShearVelocityField a +
    constantVelocityField (EuclideanSpace.single nsCoord1 b)

/-- Initial velocity data `x ↦ (a * x₁, b, c)` on `ℝ^3`. -/
def linearShearFullDriftInitialVelocity (a b c : ℝ) : NSInitialVelocity :=
  linearShearHorizontalDriftInitialVelocity a b +
    constantInitialVelocity (EuclideanSpace.single nsCoord2 c)

/-- Steady velocity field `u(t,x) = (a * x₁, b, c)` on `ℝ × ℝ^3`. -/
def linearShearFullDriftVelocityField (a b c : ℝ) : NSVelocityField :=
  linearShearHorizontalDriftVelocityField a b +
    constantVelocityField (EuclideanSpace.single nsCoord2 c)

/-- Pressure field `p(t,x) = -(a * b) * x₀` balancing the horizontal-drift
shear convection on `ℝ × ℝ^3`. -/
def linearShearHorizontalDriftPressureField (a b : ℝ) : NSPressureField :=
  fun _ : NSTime => fun x : NSSpace => -(a * b * x nsCoord0)

/-- Continuous linear embedding of scalar profiles into the first velocity
component. -/
def coord0Embedding : ℝ →L[ℝ] NSSpace :=
  (1 : ℝ →L[ℝ] ℝ).smulRight (EuclideanSpace.single nsCoord0 (1 : ℝ))

/-- Scalar initial profile `x ↦ a * sin (k * x₁)` for the non-affine heat-shear
branch. -/
def heatShearInitialScalar (a k : ℝ) : NSSpace → ℝ :=
  fun x => a * Real.sin (k * x nsCoord1)

/-- Scalar space-time profile `a * exp (-(ν * k²) * t) * sin (k * x₁)` solving
the one-dimensional heat equation along the `x₁` direction. -/
def heatShearScalar (ν a k : ℝ) : NSTime → NSSpace → ℝ :=
  fun t x => a * (Real.exp (-(ν * k ^ (2 : ℕ)) * t) * Real.sin (k * x nsCoord1))

/-- Initial velocity data for the damped sinusoidal heat-shear family,
`x ↦ (a * sin (k * x₁), 0, 0)`. -/
def heatShearInitialVelocity (a k : ℝ) : NSInitialVelocity :=
  fun x => coord0Embedding (heatShearInitialScalar a k x)

/-- Non-affine heat-shear velocity field
`u(t,x) = (a * exp (-(ν * k²) * t) * sin (k * x₁), 0, 0)`. -/
def heatShearVelocityField (ν a k : ℝ) : NSVelocityField :=
  fun t x => coord0Embedding (heatShearScalar ν a k t x)

/-- General time-amplitude shear ansatz
`u(t,x) = (A t * sin (k * x₁), 0, 0)`.  This isolates the ODE burden on the
amplitude from the spatial vector-calculus calculation. -/
def amplitudeShearVelocityField (A : NSTime → ℝ) (k : ℝ) : NSVelocityField :=
  fun t x => coord0Embedding (A t * Real.sin (k * x nsCoord1))

/-- Initial velocity data for the heat-shear family with constant streamwise
drift, `x ↦ (d + a * sin (k * x₁), 0, 0)`. -/
def heatShearStreamwiseDriftInitialVelocity (a k d : ℝ) : NSInitialVelocity :=
  heatShearInitialVelocity a k +
    constantInitialVelocity (EuclideanSpace.single nsCoord0 d)

/-- Space-time heat-shear family with constant streamwise drift,
`u(t,x) = (d + a * exp (-(ν * k²) * t) * sin (k * x₁), 0, 0)`. -/
def heatShearStreamwiseDriftVelocityField (ν a k d : ℝ) : NSVelocityField :=
  heatShearVelocityField ν a k +
    constantVelocityField (EuclideanSpace.single nsCoord0 d)

/-- Initial velocity data for the heat-shear family with constant drift in the
third component, `x ↦ (a * sin (k * x₁), 0, c)`. -/
def heatShearVerticalDriftInitialVelocity (a k c : ℝ) : NSInitialVelocity :=
  heatShearInitialVelocity a k +
    constantInitialVelocity (EuclideanSpace.single nsCoord2 c)

/-- Space-time heat-shear family with constant drift in the third component,
`u(t,x) = (a * exp (-(ν * k²) * t) * sin (k * x₁), 0, c)`. -/
def heatShearVerticalDriftVelocityField (ν a k c : ℝ) : NSVelocityField :=
  heatShearVelocityField ν a k +
    constantVelocityField (EuclideanSpace.single nsCoord2 c)

/-- Initial velocity data for the heat-shear family with both constant
streamwise and vertical drifts, `x ↦ (d + a * sin (k * x₁), 0, c)`. -/
def heatShearFullDriftInitialVelocity (a k d c : ℝ) : NSInitialVelocity :=
  heatShearStreamwiseDriftInitialVelocity a k d +
    constantInitialVelocity (EuclideanSpace.single nsCoord2 c)

/-- Space-time heat-shear family with both constant streamwise and vertical
drifts, `u(t,x) = (d + a * exp (-(ν * k²) * t) * sin (k * x₁), 0, c)`. -/
def heatShearFullDriftVelocityField (ν a k d c : ℝ) : NSVelocityField :=
  heatShearStreamwiseDriftVelocityField ν a k d +
    constantVelocityField (EuclideanSpace.single nsCoord2 c)

/-- Initial velocity data for the transported heat-shear family,
`x ↦ (a * sin (k * x₁), b, 0)`. -/
def heatShearTransportInitialVelocity (a k b : ℝ) : NSInitialVelocity :=
  heatShearInitialVelocity a k +
    constantInitialVelocity (EuclideanSpace.single nsCoord1 b)

/-- Scalar space-time profile
`a * exp (-(ν * k²) * t) * sin (k * (x₁ - b * t))` solving the one-dimensional
advection-diffusion equation along the `x₁` direction with transport speed
`b`. -/
def heatShearTransportScalar (ν a k b : ℝ) : NSTime → NSSpace → ℝ :=
  fun t x => a * (Real.exp (-(ν * k ^ (2 : ℕ)) * t) * Real.sin (k * (x nsCoord1 - b * t)))

/-- Transported non-affine heat-shear velocity field
`u(t,x) = (a * exp (-(ν * k²) * t) * sin (k * (x₁ - b * t)), b, 0)`. -/
def heatShearTransportVelocityField (ν a k b : ℝ) : NSVelocityField :=
  (fun t x => coord0Embedding (heatShearTransportScalar ν a k b t x)) +
    constantVelocityField (EuclideanSpace.single nsCoord1 b)

/-- Transported shear with an arbitrary time amplitude,
`u(t,x) = (A t * sin (k * (x₁ - b * t)), b, 0)`. -/
def amplitudeShearTransportVelocityField
    (A : NSTime → ℝ) (k b : ℝ) : NSVelocityField :=
  (fun t x => coord0Embedding (A t * Real.sin (k * (x nsCoord1 - b * t)))) +
    constantVelocityField (EuclideanSpace.single nsCoord1 b)

/-- Initial velocity data for the transported heat-shear family with additional
constant streamwise and vertical drifts,
`x ↦ (d + a * sin (k * x₁), b, c)`. -/
def heatShearTransportFullDriftInitialVelocity (a k b d c : ℝ) : NSInitialVelocity :=
  heatShearTransportInitialVelocity a k b +
    constantInitialVelocity
      (EuclideanSpace.single nsCoord0 d + EuclideanSpace.single nsCoord2 c)

/-- Transported non-affine heat-shear velocity field with additional constant
streamwise and vertical drifts,
`u(t,x) = (d + a * exp (-(ν * k²) * t) * sin (k * (x₁ - b * t)), b, c)`. -/
def heatShearTransportFullDriftVelocityField (ν a k b d c : ℝ) : NSVelocityField :=
  heatShearTransportVelocityField ν a k b +
    constantVelocityField
      (EuclideanSpace.single nsCoord0 d + EuclideanSpace.single nsCoord2 c)

/-- Directional derivative of the `comp` component of a velocity field in the
spatial coordinate direction `coord`. -/
def spatialDerivativeComponent
    (u : NSVelocityField) (t : NSTime) (x : NSSpace)
    (coord comp : Fin 3) : ℝ :=
  (spatialFDeriv u t x (EuclideanSpace.single coord (1 : ℝ))) comp

/-- Concrete vorticity / curl operator on `ℝ^3`. -/
def spatialVorticity (u : NSVelocityField) (t : NSTime) (x : NSSpace) : NSSpace :=
  EuclideanSpace.single nsCoord0
      (spatialDerivativeComponent u t x nsCoord1 nsCoord2 -
        spatialDerivativeComponent u t x nsCoord2 nsCoord1) +
    EuclideanSpace.single nsCoord1
      (spatialDerivativeComponent u t x nsCoord2 nsCoord0 -
        spatialDerivativeComponent u t x nsCoord0 nsCoord2) +
    EuclideanSpace.single nsCoord2
      (spatialDerivativeComponent u t x nsCoord0 nsCoord1 -
        spatialDerivativeComponent u t x nsCoord1 nsCoord0)

/-- Spatial coordinate derivatives only depend on the velocity field on the
fixed time slice. -/
theorem spatialDerivativeComponent_congr_at
    {u v : NSVelocityField} {t : NSTime} {x : NSSpace}
    (h : ∀ y : NSSpace, u t y = v t y) (coord comp : Fin 3) :
    spatialDerivativeComponent u t x coord comp =
      spatialDerivativeComponent v t x coord comp := by
  unfold spatialDerivativeComponent spatialFDeriv
  have hf : (fun y : NSSpace => u t y) = fun y : NSSpace => v t y := funext h
  rw [hf]

/-- The concrete vorticity at a point only depends on the velocity field on
the fixed time slice. -/
theorem spatialVorticity_congr_at
    {u v : NSVelocityField} {t : NSTime} {x : NSSpace}
    (h : ∀ y : NSSpace, u t y = v t y) :
    spatialVorticity u t x = spatialVorticity v t x := by
  have hderiv :
      ∀ coord comp : Fin 3,
        spatialDerivativeComponent u t x coord comp =
          spatialDerivativeComponent v t x coord comp := by
    intro coord comp
    exact spatialDerivativeComponent_congr_at h coord comp
  ext i
  fin_cases i <;>
    simp [spatialVorticity, hderiv]

/-- The spatial Fréchet derivative only depends on the velocity field on the
fixed time slice. -/
theorem spatialFDeriv_congr_at
    {u v : NSVelocityField} {t : NSTime} {x : NSSpace}
    (h : ∀ y : NSSpace, u t y = v t y) :
    spatialFDeriv u t x = spatialFDeriv v t x := by
  unfold spatialFDeriv
  have hf : (fun y : NSSpace => u t y) = fun y : NSSpace => v t y := funext h
  rw [hf]

/-- Spatial divergence only depends on the velocity field on the fixed time
slice. -/
theorem spatialDivergence_congr_at
    {u v : NSVelocityField} {t : NSTime} {x : NSSpace}
    (h : ∀ y : NSSpace, u t y = v t y) :
    spatialDivergence u t x = spatialDivergence v t x := by
  unfold spatialDivergence
  rw [spatialFDeriv_congr_at h]

/-- The convection term only depends on the velocity field on the fixed time
slice. -/
theorem spatialConvection_congr_at
    {u v : NSVelocityField} {t : NSTime} {x : NSSpace}
    (h : ∀ y : NSSpace, u t y = v t y) :
    spatialConvection u t x = spatialConvection v t x := by
  unfold spatialConvection
  rw [spatialFDeriv_congr_at h, h x]

/-- Spatial Laplacian only depends on the velocity field on the fixed time
slice. -/
theorem spatialLaplacian_congr_at
    {u v : NSVelocityField} {t : NSTime} {x : NSSpace}
    (h : ∀ y : NSSpace, u t y = v t y) :
    spatialLaplacian u t x = spatialLaplacian v t x := by
  unfold spatialLaplacian
  have hf : (fun y : NSSpace => u t y) = fun y : NSSpace => v t y := funext h
  rw [hf]

/-- Pointwise norm control for the concrete vorticity vector by the six
coordinate derivatives that enter the curl formula. -/
theorem norm_spatialVorticity_le_sum_abs_spatialDerivativeComponent
    (u : NSVelocityField) (t : NSTime) (x : NSSpace) :
    ‖spatialVorticity u t x‖ ≤
      |spatialDerivativeComponent u t x nsCoord1 nsCoord2| +
        |spatialDerivativeComponent u t x nsCoord2 nsCoord1| +
        |spatialDerivativeComponent u t x nsCoord2 nsCoord0| +
        |spatialDerivativeComponent u t x nsCoord0 nsCoord2| +
        |spatialDerivativeComponent u t x nsCoord0 nsCoord1| +
        |spatialDerivativeComponent u t x nsCoord1 nsCoord0| := by
  let d12 := spatialDerivativeComponent u t x nsCoord1 nsCoord2
  let d21 := spatialDerivativeComponent u t x nsCoord2 nsCoord1
  let d20 := spatialDerivativeComponent u t x nsCoord2 nsCoord0
  let d02 := spatialDerivativeComponent u t x nsCoord0 nsCoord2
  let d01 := spatialDerivativeComponent u t x nsCoord0 nsCoord1
  let d10 := spatialDerivativeComponent u t x nsCoord1 nsCoord0
  change
    ‖EuclideanSpace.single nsCoord0 (d12 - d21) +
        EuclideanSpace.single nsCoord1 (d20 - d02) +
        EuclideanSpace.single nsCoord2 (d01 - d10)‖ ≤
      |d12| + |d21| + |d20| + |d02| + |d01| + |d10|
  have hnorm :
      ‖EuclideanSpace.single nsCoord0 (d12 - d21) +
          EuclideanSpace.single nsCoord1 (d20 - d02) +
          EuclideanSpace.single nsCoord2 (d01 - d10)‖ ≤
        |d12 - d21| + |d20 - d02| + |d01 - d10| := by
    calc
      ‖EuclideanSpace.single nsCoord0 (d12 - d21) +
          EuclideanSpace.single nsCoord1 (d20 - d02) +
          EuclideanSpace.single nsCoord2 (d01 - d10)‖
        ≤
          ‖EuclideanSpace.single nsCoord0 (d12 - d21) +
            EuclideanSpace.single nsCoord1 (d20 - d02)‖ +
            ‖EuclideanSpace.single nsCoord2 (d01 - d10)‖ := by
            exact norm_add_le _ _
      _ ≤
          (‖EuclideanSpace.single nsCoord0 (d12 - d21)‖ +
            ‖EuclideanSpace.single nsCoord1 (d20 - d02)‖) +
            ‖EuclideanSpace.single nsCoord2 (d01 - d10)‖ := by
            gcongr
            exact norm_add_le _ _
      _ = |d12 - d21| + |d20 - d02| + |d01 - d10| := by
            simp [EuclideanSpace.norm_single, add_assoc]
  have h12 : |d12 - d21| ≤ |d12| + |d21| := by
    simpa [sub_eq_add_neg, abs_neg] using abs_add_le d12 (-d21)
  have h20 : |d20 - d02| ≤ |d20| + |d02| := by
    simpa [sub_eq_add_neg, abs_neg] using abs_add_le d20 (-d02)
  have h01 : |d01 - d10| ≤ |d01| + |d10| := by
    simpa [sub_eq_add_neg, abs_neg] using abs_add_le d01 (-d10)
  calc
    ‖EuclideanSpace.single nsCoord0 (d12 - d21) +
        EuclideanSpace.single nsCoord1 (d20 - d02) +
        EuclideanSpace.single nsCoord2 (d01 - d10)‖
      ≤ |d12 - d21| + |d20 - d02| + |d01 - d10| := hnorm
    _ ≤ (|d12| + |d21|) + (|d20| + |d02|) + (|d01| + |d10|) := by
      gcongr
    _ = |d12| + |d21| + |d20| + |d02| + |d01| + |d10| := by
      ring

/-- If every coordinate derivative entering the concrete curl is bounded by a
common constant, then the vorticity norm is bounded by six times that
constant. -/
theorem norm_spatialVorticity_le_of_abs_spatialDerivativeComponent_le
    {u : NSVelocityField} {t : NSTime} {x : NSSpace} {K : ℝ}
    (hK : ∀ coord comp : Fin 3,
      |spatialDerivativeComponent u t x coord comp| ≤ K) :
    ‖spatialVorticity u t x‖ ≤ 6 * K := by
  have hsum := norm_spatialVorticity_le_sum_abs_spatialDerivativeComponent u t x
  have h12 := hK nsCoord1 nsCoord2
  have h21 := hK nsCoord2 nsCoord1
  have h20 := hK nsCoord2 nsCoord0
  have h02 := hK nsCoord0 nsCoord2
  have h01 := hK nsCoord0 nsCoord1
  have h10 := hK nsCoord1 nsCoord0
  nlinarith

/-- A smooth space-time velocity field restricts to a smooth spatial slice at
any fixed time. -/
theorem smoothSpaceTimeVelocity_contDiff_spatialSlice
    {u : NSVelocityField}
    (hu : smoothSpaceTimeVelocity u)
    (t : NSTime) :
    ContDiff ℝ ∞ (fun y : NSSpace => u t y) := by
  simpa [smoothSpaceTimeVelocity, spaceTimeVelocityMap] using
    hu.comp (contDiff_prodMk_right (𝕜 := ℝ) t)

/-- A smooth space-time velocity field restricts to a differentiable spatial
slice at every point of every fixed time. -/
theorem smoothSpaceTimeVelocity_differentiableAt_spatialSlice
    {u : NSVelocityField}
    (hu : smoothSpaceTimeVelocity u)
    (t : NSTime) (x : NSSpace) :
    DifferentiableAt ℝ (fun y : NSSpace => u t y) x := by
  exact (smoothSpaceTimeVelocity_contDiff_spatialSlice hu t).differentiable (by simp) x

/-- A smooth space-time velocity field restricts to a smooth time slice at any
fixed spatial point. -/
theorem smoothSpaceTimeVelocity_contDiff_timeSlice
    {u : NSVelocityField}
    (hu : smoothSpaceTimeVelocity u)
    (x : NSSpace) :
    ContDiff ℝ ∞ (fun s : NSTime => u s x) := by
  simpa [smoothSpaceTimeVelocity, spaceTimeVelocityMap] using
    hu.comp (contDiff_prodMk_left (𝕜 := ℝ) x)

/-- A smooth space-time velocity field restricts to a differentiable time
slice at every fixed spatial point. -/
theorem smoothSpaceTimeVelocity_differentiableAt_timeSlice
    {u : NSVelocityField}
    (hu : smoothSpaceTimeVelocity u)
    (t : NSTime) (x : NSSpace) :
    DifferentiableAt ℝ (fun s : NSTime => u s x) t := by
  exact (smoothSpaceTimeVelocity_contDiff_timeSlice hu x).differentiable (by simp) t

/-- Constant velocity fields are smooth on `ℝ × ℝ^3`. -/
theorem smoothSpaceTimeVelocity_constantVelocityField
    (c : NSSpace) :
    smoothSpaceTimeVelocity (constantVelocityField c) := by
  simpa [smoothSpaceTimeVelocity, spaceTimeVelocityMap, constantVelocityField] using
    (contDiff_const : ContDiff ℝ ∞ (fun _ : NSSpacetime => c))

/-- The time-independent space-time velocity field generated by initial data.
This is the smallest concrete seed object attached to an initial datum; it is
not a Navier-Stokes solution unless the momentum residual also vanishes. -/
def timeIndependentVelocity (u₀ : NSInitialVelocity) : NSVelocityField :=
  fun _ : NSTime => u₀

@[simp]
theorem timeIndependentVelocity_apply
    (u₀ : NSInitialVelocity) (t : NSTime) (x : NSSpace) :
    timeIndependentVelocity u₀ t x = u₀ x :=
  rfl

/-- A smooth initial datum gives a smooth time-independent space-time seed. -/
theorem smoothSpaceTimeVelocity_timeIndependentVelocity
    {u₀ : NSInitialVelocity}
    (hu₀ : smoothInitialVelocityData u₀) :
    smoothSpaceTimeVelocity (timeIndependentVelocity u₀) := by
  simpa [smoothSpaceTimeVelocity, spaceTimeVelocityMap, timeIndependentVelocity,
    smoothInitialVelocityData] using hu₀.snd'

/-- The time-independent seed matches its prescribed initial datum. -/
theorem MatchesInitialVelocity_timeIndependentVelocity
    (u₀ : NSInitialVelocity) :
    MatchesInitialVelocity u₀ (timeIndependentVelocity u₀) := by
  intro x
  rfl

/-- The kinetic-energy density of the time-independent seed is the initial
kinetic-energy density on every time slice. -/
theorem kineticEnergyDensity_timeIndependentVelocity
    (u₀ : NSInitialVelocity) (t : NSTime) :
    kineticEnergyDensity (timeIndependentVelocity u₀) t =
      initialKineticEnergyDensity u₀ :=
  rfl

/-- The kinetic energy of the time-independent seed is the initial kinetic
energy on every time slice. -/
theorem kineticEnergyAt_timeIndependentVelocity
    (u₀ : NSInitialVelocity) (t : NSTime) :
    kineticEnergyAt (timeIndependentVelocity u₀) t =
      ∫ x, initialKineticEnergyDensity u₀ x
        ∂(MeasureTheory.volume : MeasureTheory.Measure NSSpace) :=
  rfl

/-- Smooth space-time velocity fields are stable under constant scalar
rescaling. -/
theorem smoothSpaceTimeVelocity_const_smul
    {u : NSVelocityField}
    (a : ℝ)
    (hu : smoothSpaceTimeVelocity u) :
    smoothSpaceTimeVelocity (a • u) := by
  simpa [smoothSpaceTimeVelocity, spaceTimeVelocityMap] using hu.const_smul a

/-- Smooth space-time velocity fields are stable under addition. -/
theorem smoothSpaceTimeVelocity_add
    {u v : NSVelocityField}
    (hu : smoothSpaceTimeVelocity u)
    (hv : smoothSpaceTimeVelocity v) :
    smoothSpaceTimeVelocity (u + v) := by
  simpa [smoothSpaceTimeVelocity, spaceTimeVelocityMap] using hu.add hv

/-- Smooth space-time velocity fields are stable under sign flip. -/
theorem smoothSpaceTimeVelocity_neg
    {u : NSVelocityField}
    (hu : smoothSpaceTimeVelocity u) :
    smoothSpaceTimeVelocity (-u) := by
  simpa using smoothSpaceTimeVelocity_const_smul (-1 : ℝ) hu

/-- Smooth space-time velocity fields are stable under subtraction. -/
theorem smoothSpaceTimeVelocity_sub
    {u v : NSVelocityField}
    (hu : smoothSpaceTimeVelocity u)
    (hv : smoothSpaceTimeVelocity v) :
    smoothSpaceTimeVelocity (u - v) := by
  simpa [sub_eq_add_neg] using
    smoothSpaceTimeVelocity_add hu (smoothSpaceTimeVelocity_neg hv)

/-- Smooth space-time velocity fields are stable under real linear
combinations. -/
theorem smoothSpaceTimeVelocity_linearCombination
    {u v : NSVelocityField}
    (a b : ℝ)
    (hu : smoothSpaceTimeVelocity u)
    (hv : smoothSpaceTimeVelocity v) :
    smoothSpaceTimeVelocity (a • u + b • v) := by
  exact
    smoothSpaceTimeVelocity_add
      (smoothSpaceTimeVelocity_const_smul a hu)
      (smoothSpaceTimeVelocity_const_smul b hv)

/-- A smooth space-time pressure field restricts to a smooth spatial slice at
any fixed time. -/
theorem smoothSpaceTimePressure_contDiff_spatialSlice
    {p : NSPressureField}
    (hp : smoothSpaceTimePressure p)
    (t : NSTime) :
    ContDiff ℝ ∞ (fun y : NSSpace => p t y) := by
  simpa [smoothSpaceTimePressure, spaceTimePressureMap] using
    hp.comp (contDiff_prodMk_right (𝕜 := ℝ) t)

/-- A smooth space-time pressure field restricts to a differentiable spatial
slice at every point of every fixed time. -/
theorem smoothSpaceTimePressure_differentiableAt_spatialSlice
    {p : NSPressureField}
    (hp : smoothSpaceTimePressure p)
    (t : NSTime) (x : NSSpace) :
    DifferentiableAt ℝ (fun y : NSSpace => p t y) x := by
  exact (smoothSpaceTimePressure_contDiff_spatialSlice hp t).differentiable (by simp) x

/-- Smooth space-time pressure fields are stable under addition. -/
theorem smoothSpaceTimePressure_add
    {p q : NSPressureField}
    (hp : smoothSpaceTimePressure p)
    (hq : smoothSpaceTimePressure q) :
    smoothSpaceTimePressure (p + q) := by
  simpa [smoothSpaceTimePressure, spaceTimePressureMap] using hp.add hq

/-- Constant pressure fields are smooth on `ℝ × ℝ^3`. -/
theorem smoothSpaceTimePressure_const
    (c : ℝ) :
    smoothSpaceTimePressure (fun _ : NSTime => fun _ : NSSpace => c) := by
  simpa [smoothSpaceTimePressure, spaceTimePressureMap] using
    (contDiff_const : ContDiff ℝ ∞ (fun _ : NSSpacetime => c))

/-- Smooth space-time pressure fields are stable under constant scalar
rescaling. -/
theorem smoothSpaceTimePressure_const_smul
    {p : NSPressureField}
    (a : ℝ)
    (hp : smoothSpaceTimePressure p) :
    smoothSpaceTimePressure (a • p) := by
  simpa [smoothSpaceTimePressure, spaceTimePressureMap] using hp.const_smul a

/-- Smooth space-time pressure fields are stable under sign flip. -/
theorem smoothSpaceTimePressure_neg
    {p : NSPressureField}
    (hp : smoothSpaceTimePressure p) :
    smoothSpaceTimePressure (-p) := by
  simpa using smoothSpaceTimePressure_const_smul (-1 : ℝ) hp

/-- Smooth space-time pressure fields are stable under subtraction. -/
theorem smoothSpaceTimePressure_sub
    {p q : NSPressureField}
    (hp : smoothSpaceTimePressure p)
    (hq : smoothSpaceTimePressure q) :
    smoothSpaceTimePressure (p - q) := by
  simpa [sub_eq_add_neg] using
    smoothSpaceTimePressure_add hp (smoothSpaceTimePressure_neg hq)

/-- Smooth space-time pressure fields are stable under real linear
combinations. -/
theorem smoothSpaceTimePressure_linearCombination
    {p q : NSPressureField}
    (a b : ℝ)
    (hp : smoothSpaceTimePressure p)
    (hq : smoothSpaceTimePressure q) :
    smoothSpaceTimePressure (a • p + b • q) := by
  exact
    smoothSpaceTimePressure_add
      (smoothSpaceTimePressure_const_smul a hp)
      (smoothSpaceTimePressure_const_smul b hq)

/-- Any smooth scalar function of time alone induces a smooth space-time
pressure field that is constant across each spatial slice. -/
theorem smoothSpaceTimePressure_timeOnly
    {π : NSTime → ℝ}
    (hπ : ContDiff ℝ ∞ π) :
    smoothSpaceTimePressure (fun t : NSTime => fun _ : NSSpace => π t) := by
  simpa [smoothSpaceTimePressure, spaceTimePressureMap] using hπ.fst'

/-- A coordinate-linear pressure field `p(t,x) = c * x₀` is smooth on
`ℝ × ℝ^3`. -/
theorem smoothSpaceTimePressure_coord0Linear
    (c : ℝ) :
    smoothSpaceTimePressure (fun _ : NSTime => fun x : NSSpace => c * x nsCoord0) := by
  let L : NSSpace →L[ℝ] ℝ := c • (EuclideanSpace.proj nsCoord0 : NSSpace →L[ℝ] ℝ)
  have hL : ContDiff ℝ ∞ fun tx : NSSpacetime => L tx.2 := by
    simpa using L.contDiff.comp (contDiff_snd : ContDiff ℝ ∞ fun tx : NSSpacetime => tx.2)
  simpa [smoothSpaceTimePressure, spaceTimePressureMap, L, nsCoord0] using hL

/-- Constant initial velocity data are smooth on `ℝ^3`. -/
theorem smoothInitialVelocityData_constantInitialVelocity
    (c : NSSpace) :
    smoothInitialVelocityData (constantInitialVelocity c) := by
  simpa [smoothInitialVelocityData, constantInitialVelocity] using
    (contDiff_const : ContDiff ℝ ∞ (fun _ : NSSpace => c))

/-- The concrete linear shear initial data are given coordinatewise by
`x ↦ (a * x₁, 0, 0)`. -/
theorem linearShearInitialVelocity_apply
    (a : ℝ) (x : NSSpace) :
    linearShearInitialVelocity a x = EuclideanSpace.single nsCoord0 (a * x nsCoord1) := by
  ext i
  fin_cases i <;>
    simp [linearShearInitialVelocity, linearShearMap, nsCoord0, nsCoord1,
      ContinuousLinearMap.smulRight_apply, mul_comm]

/-- The concrete affine shear initial data are given coordinatewise by
`x ↦ (a * x₁, 0, b)`. -/
theorem linearShearVerticalDriftInitialVelocity_apply
    (a b : ℝ) (x : NSSpace) :
    linearShearVerticalDriftInitialVelocity a b x =
      EuclideanSpace.single nsCoord0 (a * x nsCoord1) +
        EuclideanSpace.single nsCoord2 b := by
  simp [linearShearVerticalDriftInitialVelocity, constantInitialVelocity,
    linearShearInitialVelocity_apply]

/-- The steady affine shear field is given coordinatewise on every time slice by
`x ↦ (a * x₁, 0, b)`. -/
theorem linearShearVerticalDriftVelocityField_apply
    (a b : ℝ) (t : NSTime) (x : NSSpace) :
    linearShearVerticalDriftVelocityField a b t x =
      EuclideanSpace.single nsCoord0 (a * x nsCoord1) +
        EuclideanSpace.single nsCoord2 b := by
  simp [linearShearVerticalDriftVelocityField, constantVelocityField,
    linearShearVelocityField, linearShearInitialVelocity_apply]

/-- The concrete affine shear-with-horizontal-drift initial data are given
coordinatewise by `x ↦ (a * x₁, b, 0)`. -/
theorem linearShearHorizontalDriftInitialVelocity_apply
    (a b : ℝ) (x : NSSpace) :
    linearShearHorizontalDriftInitialVelocity a b x =
      EuclideanSpace.single nsCoord0 (a * x nsCoord1) +
        EuclideanSpace.single nsCoord1 b := by
  simp [linearShearHorizontalDriftInitialVelocity, constantInitialVelocity,
    linearShearInitialVelocity_apply]

/-- The steady affine shear-with-horizontal-drift field is given coordinatewise
on every time slice by `x ↦ (a * x₁, b, 0)`. -/
theorem linearShearHorizontalDriftVelocityField_apply
    (a b : ℝ) (t : NSTime) (x : NSSpace) :
    linearShearHorizontalDriftVelocityField a b t x =
      EuclideanSpace.single nsCoord0 (a * x nsCoord1) +
        EuclideanSpace.single nsCoord1 b := by
  simp [linearShearHorizontalDriftVelocityField, constantVelocityField,
    linearShearVelocityField, linearShearInitialVelocity_apply]

/-- The concrete full-drift affine shear initial data are given coordinatewise
by `x ↦ (a * x₁, b, c)`. -/
theorem linearShearFullDriftInitialVelocity_apply
    (a b c : ℝ) (x : NSSpace) :
    linearShearFullDriftInitialVelocity a b c x =
      EuclideanSpace.single nsCoord0 (a * x nsCoord1) +
        EuclideanSpace.single nsCoord1 b +
        EuclideanSpace.single nsCoord2 c := by
  simp [linearShearFullDriftInitialVelocity, linearShearHorizontalDriftInitialVelocity,
    constantInitialVelocity, linearShearInitialVelocity_apply, add_assoc]

/-- Vanishing horizontal drift reduces full-drift linear shear to the
vertical-drift subfamily. -/
theorem linearShearFullDriftInitialVelocity_zero_horizontalDrift
    (a c : ℝ) :
    linearShearFullDriftInitialVelocity a 0 c =
      linearShearVerticalDriftInitialVelocity a c := by
  funext x
  ext i
  fin_cases i <;>
    simp [linearShearFullDriftInitialVelocity_apply,
      linearShearVerticalDriftInitialVelocity_apply, nsCoord0, nsCoord1, nsCoord2]

/-- Vanishing vertical drift reduces full-drift linear shear to the
horizontal-drift subfamily. -/
theorem linearShearFullDriftInitialVelocity_zero_verticalDrift
    (a b : ℝ) :
    linearShearFullDriftInitialVelocity a b 0 =
      linearShearHorizontalDriftInitialVelocity a b := by
  funext x
  ext i
  fin_cases i <;>
    simp [linearShearFullDriftInitialVelocity_apply,
      linearShearHorizontalDriftInitialVelocity_apply, nsCoord0, nsCoord1, nsCoord2]

/-- Vanishing both extra drifts reduces full-drift linear shear to the base
linear-shear family. -/
theorem linearShearFullDriftInitialVelocity_zero_drifts
    (a : ℝ) :
    linearShearFullDriftInitialVelocity a 0 0 =
      linearShearInitialVelocity a := by
  funext x
  ext i
  fin_cases i <;>
    simp [linearShearFullDriftInitialVelocity_apply,
      linearShearInitialVelocity_apply, nsCoord0, nsCoord1, nsCoord2]

/-- The steady full-drift affine shear field is given coordinatewise on every
time slice by `x ↦ (a * x₁, b, c)`. -/
theorem linearShearFullDriftVelocityField_apply
    (a b c : ℝ) (t : NSTime) (x : NSSpace) :
    linearShearFullDriftVelocityField a b c t x =
      EuclideanSpace.single nsCoord0 (a * x nsCoord1) +
        EuclideanSpace.single nsCoord1 b +
        EuclideanSpace.single nsCoord2 c := by
  simp [linearShearFullDriftVelocityField, linearShearHorizontalDriftVelocityField,
    constantVelocityField, linearShearVelocityField, linearShearInitialVelocity_apply, add_assoc]

/-- The scalar embedding into the first velocity component is given by the
standard basis vector `e₀`. -/
theorem coord0Embedding_apply
    (z : ℝ) :
    coord0Embedding z = EuclideanSpace.single nsCoord0 z := by
  ext i
  fin_cases i <;>
    simp [coord0Embedding, nsCoord0, ContinuousLinearMap.smulRight_apply]

/-- The damped sinusoidal initial datum is given coordinatewise by
`x ↦ (a * sin (k * x₁), 0, 0)`. -/
theorem heatShearInitialVelocity_apply
    (a k : ℝ) (x : NSSpace) :
    heatShearInitialVelocity a k x =
      EuclideanSpace.single nsCoord0 (a * Real.sin (k * x nsCoord1)) := by
  simp [heatShearInitialVelocity, heatShearInitialScalar, coord0Embedding_apply]

/-- Zero amplitude collapses the heat-shear initial datum to the zero field. -/
theorem heatShearInitialVelocity_zero_of_amplitude_zero
    (k : ℝ) :
    heatShearInitialVelocity 0 k = (0 : NSInitialVelocity) := by
  funext x
  simp [heatShearInitialVelocity, heatShearInitialScalar, coord0Embedding_apply]

/-- Zero wave number collapses the heat-shear initial datum to the zero field. -/
theorem heatShearInitialVelocity_zero_of_wavenumber_zero
    (a : ℝ) :
    heatShearInitialVelocity a 0 = (0 : NSInitialVelocity) := by
  funext x
  simp [heatShearInitialVelocity, heatShearInitialScalar, coord0Embedding_apply]

/-- The damped sinusoidal heat-shear field is given coordinatewise on every time
slice by
`x ↦ (a * exp (-(ν * k²) * t) * sin (k * x₁), 0, 0)`. -/
theorem heatShearVelocityField_apply
    (ν a k : ℝ) (t : NSTime) (x : NSSpace) :
    heatShearVelocityField ν a k t x =
      EuclideanSpace.single nsCoord0
        (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * Real.sin (k * x nsCoord1)) := by
  simp [heatShearVelocityField, heatShearScalar, coord0Embedding_apply, mul_assoc]

/-- The general time-amplitude shear ansatz is given coordinatewise on every
time slice by `x ↦ (A t * sin (k * x₁), 0, 0)`. -/
theorem amplitudeShearVelocityField_apply
    (A : NSTime → ℝ) (k : ℝ) (t : NSTime) (x : NSSpace) :
    amplitudeShearVelocityField A k t x =
      EuclideanSpace.single nsCoord0 (A t * Real.sin (k * x nsCoord1)) := by
  simp [amplitudeShearVelocityField, coord0Embedding_apply]

/-- The heat-shear datum with streamwise drift is given coordinatewise by
`x ↦ (d + a * sin (k * x₁), 0, 0)`. -/
theorem heatShearStreamwiseDriftInitialVelocity_apply
    (a k d : ℝ) (x : NSSpace) :
    heatShearStreamwiseDriftInitialVelocity a k d x =
      EuclideanSpace.single nsCoord0 (d + a * Real.sin (k * x nsCoord1)) := by
  ext i
  fin_cases i <;>
    simp [heatShearStreamwiseDriftInitialVelocity, constantInitialVelocity,
      heatShearInitialVelocity_apply, nsCoord0, add_comm]

/-- The heat-shear family with streamwise drift is given coordinatewise on
every time slice by `x ↦ (d + a * exp (-(ν * k²) * t) * sin (k * x₁), 0, 0)`.
-/
theorem heatShearStreamwiseDriftVelocityField_apply
    (ν a k d : ℝ) (t : NSTime) (x : NSSpace) :
    heatShearStreamwiseDriftVelocityField ν a k d t x =
      EuclideanSpace.single nsCoord0
        (d + a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * Real.sin (k * x nsCoord1)) := by
  ext i
  fin_cases i <;>
    simp [heatShearStreamwiseDriftVelocityField, constantVelocityField,
      heatShearVelocityField_apply, nsCoord0, add_comm]

/-- The heat-shear datum with vertical drift is given coordinatewise by
`x ↦ (a * sin (k * x₁), 0, c)`. -/
theorem heatShearVerticalDriftInitialVelocity_apply
    (a k c : ℝ) (x : NSSpace) :
    heatShearVerticalDriftInitialVelocity a k c x =
      EuclideanSpace.single nsCoord0 (a * Real.sin (k * x nsCoord1)) +
        EuclideanSpace.single nsCoord2 c := by
  simp [heatShearVerticalDriftInitialVelocity, constantInitialVelocity,
    heatShearInitialVelocity_apply]

/-- The heat-shear family with vertical drift is given coordinatewise on every
time slice by `x ↦ (a * exp (-(ν * k²) * t) * sin (k * x₁), 0, c)`. -/
theorem heatShearVerticalDriftVelocityField_apply
    (ν a k c : ℝ) (t : NSTime) (x : NSSpace) :
    heatShearVerticalDriftVelocityField ν a k c t x =
      EuclideanSpace.single nsCoord0
          (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * Real.sin (k * x nsCoord1)) +
        EuclideanSpace.single nsCoord2 c := by
  simp [heatShearVerticalDriftVelocityField, constantVelocityField,
    heatShearVelocityField_apply]

/-- The heat-shear datum with full drift is given coordinatewise by
`x ↦ (d + a * sin (k * x₁), 0, c)`. -/
theorem heatShearFullDriftInitialVelocity_apply
    (a k d c : ℝ) (x : NSSpace) :
    heatShearFullDriftInitialVelocity a k d c x =
      EuclideanSpace.single nsCoord0 (d + a * Real.sin (k * x nsCoord1)) +
        EuclideanSpace.single nsCoord2 c := by
  simp [heatShearFullDriftInitialVelocity, constantInitialVelocity,
    heatShearStreamwiseDriftInitialVelocity_apply]

/-- Vanishing streamwise drift reduces full-drift heat shear to the vertical-drift
subfamily. -/
theorem heatShearFullDriftInitialVelocity_zero_streamwiseDrift
    (a k c : ℝ) :
    heatShearFullDriftInitialVelocity a k 0 c =
      heatShearVerticalDriftInitialVelocity a k c := by
  funext x
  simp [heatShearFullDriftInitialVelocity, heatShearStreamwiseDriftInitialVelocity,
    heatShearVerticalDriftInitialVelocity, constantInitialVelocity]

/-- Vanishing vertical drift reduces full-drift heat shear to the streamwise-drift
subfamily. -/
theorem heatShearFullDriftInitialVelocity_zero_verticalDrift
    (a k d : ℝ) :
    heatShearFullDriftInitialVelocity a k d 0 =
      heatShearStreamwiseDriftInitialVelocity a k d := by
  funext x
  simp [heatShearFullDriftInitialVelocity, heatShearStreamwiseDriftInitialVelocity,
    constantInitialVelocity]

/-- Vanishing both extra drifts reduces full-drift heat shear to the base
heat-shear family. -/
theorem heatShearFullDriftInitialVelocity_zero_drifts
    (a k : ℝ) :
    heatShearFullDriftInitialVelocity a k 0 0 =
      heatShearInitialVelocity a k := by
  funext x
  ext i
  fin_cases i <;>
    simp [heatShearFullDriftInitialVelocity_apply,
      heatShearInitialVelocity_apply, nsCoord0, nsCoord1, nsCoord2]

/-- The heat-shear family with full drift is given coordinatewise on every
time slice by `x ↦ (d + a * exp (-(ν * k²) * t) * sin (k * x₁), 0, c)`. -/
theorem heatShearFullDriftVelocityField_apply
    (ν a k d c : ℝ) (t : NSTime) (x : NSSpace) :
    heatShearFullDriftVelocityField ν a k d c t x =
      EuclideanSpace.single nsCoord0
          (d + a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * Real.sin (k * x nsCoord1)) +
        EuclideanSpace.single nsCoord2 c := by
  simp [heatShearFullDriftVelocityField, constantVelocityField,
    heatShearStreamwiseDriftVelocityField_apply]

/-- Linear shear initial velocity data are smooth on `ℝ^3`. -/
theorem smoothInitialVelocityData_linearShearInitialVelocity
    (a : ℝ) :
    smoothInitialVelocityData (linearShearInitialVelocity a) := by
  simpa [smoothInitialVelocityData, linearShearInitialVelocity] using
    (linearShearMap a).contDiff

/-- Initial velocity data `x ↦ (a * x₁, 0, b)` are smooth on `ℝ^3`. -/
theorem smoothInitialVelocityData_linearShearVerticalDriftInitialVelocity
    (a b : ℝ) :
    smoothInitialVelocityData (linearShearVerticalDriftInitialVelocity a b) := by
  simpa [linearShearVerticalDriftInitialVelocity] using
    (smoothInitialVelocityData_linearShearInitialVelocity a).add
      (smoothInitialVelocityData_constantInitialVelocity
        (EuclideanSpace.single nsCoord2 b))

/-- Initial velocity data `x ↦ (a * x₁, b, 0)` are smooth on `ℝ^3`. -/
theorem smoothInitialVelocityData_linearShearHorizontalDriftInitialVelocity
    (a b : ℝ) :
    smoothInitialVelocityData (linearShearHorizontalDriftInitialVelocity a b) := by
  simpa [linearShearHorizontalDriftInitialVelocity] using
    (smoothInitialVelocityData_linearShearInitialVelocity a).add
      (smoothInitialVelocityData_constantInitialVelocity
        (EuclideanSpace.single nsCoord1 b))

/-- Initial velocity data `x ↦ (a * x₁, b, c)` are smooth on `ℝ^3`. -/
theorem smoothInitialVelocityData_linearShearFullDriftInitialVelocity
    (a b c : ℝ) :
    smoothInitialVelocityData (linearShearFullDriftInitialVelocity a b c) := by
  simpa [linearShearFullDriftInitialVelocity] using
    (smoothInitialVelocityData_linearShearHorizontalDriftInitialVelocity a b).add
      (smoothInitialVelocityData_constantInitialVelocity
        (EuclideanSpace.single nsCoord2 c))

/-- The damped sinusoidal initial datum is smooth on `ℝ^3`. -/
theorem smoothInitialVelocityData_heatShearInitialVelocity
    (a k : ℝ) :
    smoothInitialVelocityData (heatShearInitialVelocity a k) := by
  have hscalar : ContDiff ℝ ∞ (heatShearInitialScalar a k) := by
    simpa [heatShearInitialScalar, smul_eq_mul, mul_assoc] using
      ((Real.contDiff_sin.comp
        ((EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ).contDiff.const_smul k)).const_smul a)
  simpa [smoothInitialVelocityData, heatShearInitialVelocity] using
    coord0Embedding.contDiff.comp hscalar

/-- Initial velocity data `x ↦ (d + a * sin (k * x₁), 0, 0)` are smooth on
`ℝ^3`. -/
theorem smoothInitialVelocityData_heatShearStreamwiseDriftInitialVelocity
    (a k d : ℝ) :
    smoothInitialVelocityData (heatShearStreamwiseDriftInitialVelocity a k d) := by
  simpa [heatShearStreamwiseDriftInitialVelocity] using
    (smoothInitialVelocityData_heatShearInitialVelocity a k).add
      (smoothInitialVelocityData_constantInitialVelocity
        (EuclideanSpace.single nsCoord0 d))

/-- Initial velocity data `x ↦ (a * sin (k * x₁), 0, c)` are smooth on
`ℝ^3`. -/
theorem smoothInitialVelocityData_heatShearVerticalDriftInitialVelocity
    (a k c : ℝ) :
    smoothInitialVelocityData (heatShearVerticalDriftInitialVelocity a k c) := by
  simpa [heatShearVerticalDriftInitialVelocity] using
    (smoothInitialVelocityData_heatShearInitialVelocity a k).add
      (smoothInitialVelocityData_constantInitialVelocity
        (EuclideanSpace.single nsCoord2 c))

/-- Initial velocity data `x ↦ (d + a * sin (k * x₁), 0, c)` are smooth on
`ℝ^3`. -/
theorem smoothInitialVelocityData_heatShearFullDriftInitialVelocity
    (a k d c : ℝ) :
    smoothInitialVelocityData (heatShearFullDriftInitialVelocity a k d c) := by
  simpa [heatShearFullDriftInitialVelocity] using
    (smoothInitialVelocityData_heatShearStreamwiseDriftInitialVelocity a k d).add
      (smoothInitialVelocityData_constantInitialVelocity
        (EuclideanSpace.single nsCoord2 c))

/-- The steady linear shear field is smooth on `ℝ × ℝ^3`. -/
theorem smoothSpaceTimeVelocity_linearShearVelocityField
    (a : ℝ) :
    smoothSpaceTimeVelocity (linearShearVelocityField a) := by
  simpa [smoothSpaceTimeVelocity, spaceTimeVelocityMap, linearShearVelocityField] using
    ((linearShearMap a).contDiff.comp contDiff_snd)

/-- The steady field `u(t,x) = (a * x₁, 0, b)` is smooth on `ℝ × ℝ^3`. -/
theorem smoothSpaceTimeVelocity_linearShearVerticalDriftVelocityField
    (a b : ℝ) :
    smoothSpaceTimeVelocity (linearShearVerticalDriftVelocityField a b) := by
  simpa [linearShearVerticalDriftVelocityField] using
    (smoothSpaceTimeVelocity_linearShearVelocityField a).add
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord2 b))

/-- The steady field `u(t,x) = (a * x₁, b, 0)` is smooth on `ℝ × ℝ^3`. -/
theorem smoothSpaceTimeVelocity_linearShearHorizontalDriftVelocityField
    (a b : ℝ) :
    smoothSpaceTimeVelocity (linearShearHorizontalDriftVelocityField a b) := by
  simpa [linearShearHorizontalDriftVelocityField] using
    (smoothSpaceTimeVelocity_linearShearVelocityField a).add
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord1 b))

/-- The steady field `u(t,x) = (a * x₁, b, c)` is smooth on `ℝ × ℝ^3`. -/
theorem smoothSpaceTimeVelocity_linearShearFullDriftVelocityField
    (a b c : ℝ) :
    smoothSpaceTimeVelocity (linearShearFullDriftVelocityField a b c) := by
  simpa [linearShearFullDriftVelocityField] using
    (smoothSpaceTimeVelocity_linearShearHorizontalDriftVelocityField a b).add
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord2 c))

/-- The damped sinusoidal heat-shear field is smooth on `ℝ × ℝ^3`. -/
theorem smoothSpaceTimeVelocity_heatShearVelocityField
    (ν a k : ℝ) :
    smoothSpaceTimeVelocity (heatShearVelocityField ν a k) := by
  have htime : ContDiff ℝ ∞
      (fun tx : NSSpacetime => Real.exp (-(ν * k ^ (2 : ℕ)) * tx.1)) := by
    simpa [smul_eq_mul, mul_assoc] using
      (Real.contDiff_exp.comp (contDiff_fst.const_smul (-(ν * k ^ (2 : ℕ)))))
  have hspace : ContDiff ℝ ∞
      (fun tx : NSSpacetime => Real.sin (k * tx.2 nsCoord1)) := by
    have hcoord : ContDiff ℝ ∞ (fun tx : NSSpacetime => tx.2 nsCoord1) := by
      simpa using
        (EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ).contDiff.comp contDiff_snd
    simpa [smul_eq_mul, mul_assoc] using
      (Real.contDiff_sin.comp (hcoord.const_smul k))
  have hscalar : ContDiff ℝ ∞ (fun tx : NSSpacetime =>
      a * Real.exp (-(ν * k ^ (2 : ℕ)) * tx.1) * Real.sin (k * tx.2 nsCoord1)) := by
    simpa [smul_eq_mul, mul_assoc, mul_left_comm] using
      ((htime.mul hspace).const_smul a)
  have hmap :
      spaceTimeVelocityMap (heatShearVelocityField ν a k) =
        fun tx : NSSpacetime =>
          coord0Embedding
            (a * Real.exp (-(ν * k ^ (2 : ℕ)) * tx.1) * Real.sin (k * tx.2 nsCoord1)) := by
    funext tx
    simp [spaceTimeVelocityMap, heatShearVelocityField, heatShearScalar, mul_assoc]
  rw [smoothSpaceTimeVelocity, hmap]
  exact coord0Embedding.contDiff.comp hscalar

/-- The heat-shear family with streamwise drift is smooth on `ℝ × ℝ^3`. -/
theorem smoothSpaceTimeVelocity_heatShearStreamwiseDriftVelocityField
    (ν a k d : ℝ) :
    smoothSpaceTimeVelocity (heatShearStreamwiseDriftVelocityField ν a k d) := by
  simpa [heatShearStreamwiseDriftVelocityField] using
    (smoothSpaceTimeVelocity_heatShearVelocityField ν a k).add
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord0 d))

/-- The heat-shear family with vertical drift is smooth on `ℝ × ℝ^3`. -/
theorem smoothSpaceTimeVelocity_heatShearVerticalDriftVelocityField
    (ν a k c : ℝ) :
    smoothSpaceTimeVelocity (heatShearVerticalDriftVelocityField ν a k c) := by
  simpa [heatShearVerticalDriftVelocityField] using
    (smoothSpaceTimeVelocity_heatShearVelocityField ν a k).add
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord2 c))

/-- The heat-shear family with full drift is smooth on `ℝ × ℝ^3`. -/
theorem smoothSpaceTimeVelocity_heatShearFullDriftVelocityField
    (ν a k d c : ℝ) :
    smoothSpaceTimeVelocity (heatShearFullDriftVelocityField ν a k d c) := by
  simpa [heatShearFullDriftVelocityField] using
    (smoothSpaceTimeVelocity_heatShearStreamwiseDriftVelocityField ν a k d).add
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord2 c))

/-- The compensating pressure field `p(t,x) = -(a * b) * x₀` is smooth on
`ℝ × ℝ^3`. -/
theorem smoothSpaceTimePressure_linearShearHorizontalDriftPressureField
    (a b : ℝ) :
    smoothSpaceTimePressure (linearShearHorizontalDriftPressureField a b) := by
  simpa [linearShearHorizontalDriftPressureField] using
    smoothSpaceTimePressure_coord0Linear (-(a * b))

/-- The spatial Fréchet derivative commutes with constant scalar multiplication. -/
theorem spatialFDeriv_const_smul
    (a : ℝ) (u : NSVelocityField) (t : NSTime) (x : NSSpace) :
    spatialFDeriv (a • u) t x = a • spatialFDeriv u t x := by
  rw [spatialFDeriv, spatialFDeriv]
  change fderiv ℝ (a • fun y : NSSpace => u t y) x = a • fderiv ℝ (fun y : NSSpace => u t y) x
  rw [fderiv_const_smul_field]
  rfl

/-- The spatial Fréchet derivative commutes with addition. -/
theorem spatialFDeriv_add
    {u v : NSVelocityField} {t : NSTime} {x : NSSpace}
    (hu : DifferentiableAt ℝ (fun y : NSSpace => u t y) x)
    (hv : DifferentiableAt ℝ (fun y : NSSpace => v t y) x) :
    spatialFDeriv (u + v) t x = spatialFDeriv u t x + spatialFDeriv v t x := by
  rw [spatialFDeriv, spatialFDeriv, spatialFDeriv]
  change fderiv ℝ ((fun y : NSSpace => u t y) + fun y : NSSpace => v t y) x = _
  rw [fderiv_add hu hv]

/-- The spatial Fréchet derivative of the zero field is zero. -/
theorem spatialFDeriv_zero (t : NSTime) (x : NSSpace) :
    spatialFDeriv (0 : NSVelocityField) t x = 0 := by
  simp [spatialFDeriv]

/-- The spatial Fréchet derivative of a constant velocity field is zero. -/
theorem spatialFDeriv_constantVelocityField
    (c : NSSpace) (t : NSTime) (x : NSSpace) :
    spatialFDeriv (constantVelocityField c) t x = 0 := by
  simp [spatialFDeriv, constantVelocityField]

/-- The spatial Fréchet derivative of the steady linear shear field is the
same linear shear map at every space-time point. -/
theorem spatialFDeriv_linearShearVelocityField
    (a : ℝ) (t : NSTime) (x : NSSpace) :
    spatialFDeriv (linearShearVelocityField a) t x = linearShearMap a := by
  unfold spatialFDeriv linearShearVelocityField
  change fderiv ℝ (linearShearInitialVelocity a) x = linearShearMap a
  rw [linearShearInitialVelocity]
  exact (linearShearMap a).fderiv (x := x)

/-- The spatial Fréchet derivative of the steady field `u(t,x) = (a * x₁, 0, b)`
is the same linear shear map at every space-time point. -/
theorem spatialFDeriv_linearShearVerticalDriftVelocityField
    (a b : ℝ) (t : NSTime) (x : NSSpace) :
    spatialFDeriv (linearShearVerticalDriftVelocityField a b) t x = linearShearMap a := by
  rw [linearShearVerticalDriftVelocityField]
  rw [spatialFDeriv_add
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_linearShearVelocityField a) t x)
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
      (EuclideanSpace.single nsCoord2 b)) t x)]
  simp [spatialFDeriv_linearShearVelocityField, spatialFDeriv_constantVelocityField]

/-- The spatial Fréchet derivative of the steady field `u(t,x) = (a * x₁, b, 0)`
is the same linear shear map at every space-time point. -/
theorem spatialFDeriv_linearShearHorizontalDriftVelocityField
    (a b : ℝ) (t : NSTime) (x : NSSpace) :
    spatialFDeriv (linearShearHorizontalDriftVelocityField a b) t x = linearShearMap a := by
  rw [linearShearHorizontalDriftVelocityField]
  rw [spatialFDeriv_add
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_linearShearVelocityField a) t x)
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord1 b)) t x)]
  simp [spatialFDeriv_linearShearVelocityField, spatialFDeriv_constantVelocityField]

/-- The spatial Fréchet derivative of the damped sinusoidal heat-shear field is
supported on the `x₁` direction and the first velocity component. -/
theorem spatialFDeriv_heatShearVelocityField
    (ν a k : ℝ) (t : NSTime) (x : NSSpace) :
    spatialFDeriv (heatShearVelocityField ν a k) t x =
      coord0Embedding.comp
        (((a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) : ℝ) •
          (Real.cos (k * x nsCoord1) •
            ((k : ℝ) • (EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ))))) := by
  let A : ℝ := a * Real.exp (-(ν * k ^ (2 : ℕ)) * t)
  have hcoord : HasFDerivAt (fun y : NSSpace => k * y nsCoord1)
      ((k : ℝ) • (EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ)) x := by
    simpa [smul_eq_mul] using
      ((EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ).hasFDerivAt.const_smul k)
  have hsin : HasFDerivAt (fun y : NSSpace => Real.sin (k * y nsCoord1))
      (Real.cos (k * x nsCoord1) •
        ((k : ℝ) • (EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ))) x := by
    simpa using hcoord.sin
  have hscalar : HasFDerivAt
      (fun y : NSSpace => A * Real.sin (k * y nsCoord1))
      ((A : ℝ) •
        (Real.cos (k * x nsCoord1) •
          ((k : ℝ) • (EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ)))) x := by
    simpa [A, smul_eq_mul] using
      hsin.const_smul A
  have hvec : HasFDerivAt
      (fun y : NSSpace => coord0Embedding (A * Real.sin (k * y nsCoord1)))
      (coord0Embedding.comp
        ((A : ℝ) •
          (Real.cos (k * x nsCoord1) •
            ((k : ℝ) • (EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ))))) x := by
    exact coord0Embedding.hasFDerivAt.comp x hscalar
  unfold spatialFDeriv
  simpa [heatShearVelocityField, heatShearScalar, A, mul_assoc] using hvec.fderiv

/-- The spatial Fréchet derivative of the general time-amplitude shear ansatz
has the same slice formula as heat shear, with the sampled amplitude `A t`. -/
theorem spatialFDeriv_amplitudeShearVelocityField
    (A : NSTime → ℝ) (k : ℝ) (t : NSTime) (x : NSSpace) :
    spatialFDeriv (amplitudeShearVelocityField A k) t x =
      coord0Embedding.comp
        (((A t : ℝ) •
          (Real.cos (k * x nsCoord1) •
            ((k : ℝ) • (EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ))))) := by
  have hslice :
      ∀ y : NSSpace,
        amplitudeShearVelocityField A k t y = heatShearVelocityField 0 (A t) k t y := by
    intro y
    simp [amplitudeShearVelocityField, heatShearVelocityField, heatShearScalar]
  rw [spatialFDeriv_congr_at hslice]
  simpa [heatShearScalar]
    using spatialFDeriv_heatShearVelocityField 0 (A t) k t x

/-- The heat-shear family with streamwise drift has the same spatial Fréchet
derivative as pure heat shear. -/
theorem spatialFDeriv_heatShearStreamwiseDriftVelocityField
    (ν a k d : ℝ) (t : NSTime) (x : NSSpace) :
    spatialFDeriv (heatShearStreamwiseDriftVelocityField ν a k d) t x =
      coord0Embedding.comp
        (((a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) : ℝ) •
          (Real.cos (k * x nsCoord1) •
            ((k : ℝ) • (EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ))))) := by
  rw [heatShearStreamwiseDriftVelocityField]
  rw [spatialFDeriv_add
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_heatShearVelocityField ν a k) t x)
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord0 d)) t x)]
  simp [spatialFDeriv_heatShearVelocityField, spatialFDeriv_constantVelocityField]

/-- The time derivative commutes with constant scalar multiplication. -/
theorem timeVelocityDerivative_const_smul
    (a : ℝ) (u : NSVelocityField) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (a • u) t x = a • timeVelocityDerivative u t x := by
  rw [timeVelocityDerivative, timeVelocityDerivative, timeFDeriv, timeFDeriv]
  change fderiv ℝ (a • fun s : NSTime => u s x) t (1 : ℝ) =
      a • fderiv ℝ (fun s : NSTime => u s x) t (1 : ℝ)
  rw [fderiv_const_smul_field]
  rfl

/-- The time derivative commutes with addition. -/
theorem timeVelocityDerivative_add
    {u v : NSVelocityField} {t : NSTime} {x : NSSpace}
    (hu : DifferentiableAt ℝ (fun s : NSTime => u s x) t)
    (hv : DifferentiableAt ℝ (fun s : NSTime => v s x) t) :
    timeVelocityDerivative (u + v) t x =
      timeVelocityDerivative u t x + timeVelocityDerivative v t x := by
  rw [timeVelocityDerivative, timeVelocityDerivative, timeVelocityDerivative, timeFDeriv, timeFDeriv,
    timeFDeriv]
  change fderiv ℝ ((fun s : NSTime => u s x) + fun s : NSTime => v s x) t (1 : ℝ) = _
  rw [fderiv_add hu hv]
  simp [ContinuousLinearMap.add_apply]

/-- The time derivative of the zero field is zero. -/
theorem timeVelocityDerivative_zero (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (0 : NSVelocityField) t x = 0 := by
  simp [timeVelocityDerivative, timeFDeriv]

/-- The time derivative of a constant velocity field is zero. -/
theorem timeVelocityDerivative_constantVelocityField
    (c : NSSpace) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (constantVelocityField c) t x = 0 := by
  simp [timeVelocityDerivative, timeFDeriv, constantVelocityField]

/-- The time-independent seed has zero time derivative. -/
theorem timeVelocityDerivative_timeIndependentVelocity
    (u₀ : NSInitialVelocity) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (timeIndependentVelocity u₀) t x = 0 := by
  simp [timeVelocityDerivative, timeFDeriv, timeIndependentVelocity]

/-- The steady linear shear field has zero time derivative. -/
theorem timeVelocityDerivative_linearShearVelocityField
    (a : ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (linearShearVelocityField a) t x = 0 := by
  simp [linearShearVelocityField, timeVelocityDerivative, timeFDeriv]

/-- The steady field `u(t,x) = (a * x₁, 0, b)` has zero time derivative. -/
theorem timeVelocityDerivative_linearShearVerticalDriftVelocityField
    (a b : ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (linearShearVerticalDriftVelocityField a b) t x = 0 := by
  rw [linearShearVerticalDriftVelocityField]
  rw [timeVelocityDerivative_add]
  · simp [timeVelocityDerivative_linearShearVelocityField,
      timeVelocityDerivative_constantVelocityField]
  · dsimp [linearShearVelocityField]
    exact differentiableAt_const ((linearShearInitialVelocity a) x)
  · dsimp [constantVelocityField]
    exact differentiableAt_const (EuclideanSpace.single nsCoord2 b : NSSpace)

/-- The steady field `u(t,x) = (a * x₁, b, 0)` has zero time derivative. -/
theorem timeVelocityDerivative_linearShearHorizontalDriftVelocityField
    (a b : ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (linearShearHorizontalDriftVelocityField a b) t x = 0 := by
  rw [linearShearHorizontalDriftVelocityField]
  rw [timeVelocityDerivative_add]
  · simp [timeVelocityDerivative_linearShearVelocityField,
      timeVelocityDerivative_constantVelocityField]
  · dsimp [linearShearVelocityField]
    exact differentiableAt_const ((linearShearInitialVelocity a) x)
  · dsimp [constantVelocityField]
    exact differentiableAt_const (EuclideanSpace.single nsCoord1 b : NSSpace)

/-- The steady field `u(t,x) = (a * x₁, b, c)` has zero time derivative. -/
theorem timeVelocityDerivative_linearShearFullDriftVelocityField
    (a b c : ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (linearShearFullDriftVelocityField a b c) t x = 0 := by
  rw [linearShearFullDriftVelocityField]
  rw [timeVelocityDerivative_add]
  · simp [timeVelocityDerivative_linearShearHorizontalDriftVelocityField,
      timeVelocityDerivative_constantVelocityField]
  · dsimp [linearShearHorizontalDriftVelocityField]
    exact differentiableAt_const ((linearShearHorizontalDriftInitialVelocity a b) x)
  · dsimp [constantVelocityField]
    exact differentiableAt_const (EuclideanSpace.single nsCoord2 c : NSSpace)

/-- The damped sinusoidal heat-shear field has the expected heat-decay time
derivative. -/
theorem timeVelocityDerivative_heatShearVelocityField
    (ν a k : ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (heatShearVelocityField ν a k) t x =
      coord0Embedding
        (-(ν * k ^ (2 : ℕ)) *
          (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * Real.sin (k * x nsCoord1))) := by
  let S : ℝ := Real.sin (k * x nsCoord1)
  have hexp : HasDerivAt
      (fun s : ℝ => Real.exp (-(ν * k ^ (2 : ℕ)) * s))
      (Real.exp (-(ν * k ^ (2 : ℕ)) * t) * (-(ν * k ^ (2 : ℕ)))) t := by
    simpa [smul_eq_mul, mul_assoc] using
      (((hasDerivAt_id' t).const_mul (-(ν * k ^ (2 : ℕ)))).exp)
  have hscalar : HasDerivAt
      (fun s : ℝ => a * Real.exp (-(ν * k ^ (2 : ℕ)) * s) * S)
      (-(ν * k ^ (2 : ℕ)) *
        (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * S)) t := by
    simpa [S, mul_assoc, mul_left_comm, mul_comm] using
      hexp.mul_const (a * S)
  have hvec := coord0Embedding.hasFDerivAt.comp t hscalar.hasFDerivAt
  have happly :=
    congrArg (fun L : ℝ →L[ℝ] NSSpace => L (1 : ℝ)) hvec.fderiv
  simpa [timeVelocityDerivative, timeFDeriv, heatShearVelocityField, heatShearScalar,
    S, ContinuousLinearMap.comp_apply, mul_assoc, mul_left_comm, mul_comm] using happly

/-- The time derivative of the general time-amplitude shear ansatz is exactly
the sampled scalar amplitude derivative times the fixed sine mode. -/
theorem timeVelocityDerivative_amplitudeShearVelocityField
    {A : NSTime → ℝ} {A' : ℝ} {t : NSTime}
    (hA : HasDerivAt A A' t) (k : ℝ) (x : NSSpace) :
    timeVelocityDerivative (amplitudeShearVelocityField A k) t x =
      coord0Embedding (A' * Real.sin (k * x nsCoord1)) := by
  let S : ℝ := Real.sin (k * x nsCoord1)
  have hscalar : HasDerivAt (fun s : ℝ => A s * S) (A' * S) t := by
    simpa [S, mul_assoc, mul_left_comm, mul_comm] using hA.mul_const S
  have hvec := coord0Embedding.hasFDerivAt.comp t hscalar.hasFDerivAt
  have happly :=
    congrArg (fun L : ℝ →L[ℝ] NSSpace => L (1 : ℝ)) hvec.fderiv
  simpa [timeVelocityDerivative, timeFDeriv, amplitudeShearVelocityField,
    S, ContinuousLinearMap.comp_apply, mul_assoc, mul_left_comm, mul_comm] using happly

/-- The heat-shear family with streamwise drift has the same time derivative as
pure heat shear. -/
theorem timeVelocityDerivative_heatShearStreamwiseDriftVelocityField
    (ν a k d : ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (heatShearStreamwiseDriftVelocityField ν a k d) t x =
      coord0Embedding
        (-(ν * k ^ (2 : ℕ)) *
          (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * Real.sin (k * x nsCoord1))) := by
  rw [heatShearStreamwiseDriftVelocityField]
  rw [timeVelocityDerivative_add]
  · simp [timeVelocityDerivative_heatShearVelocityField,
      timeVelocityDerivative_constantVelocityField]
  · exact smoothSpaceTimeVelocity_differentiableAt_timeSlice
      (smoothSpaceTimeVelocity_heatShearVelocityField ν a k) t x
  · dsimp [constantVelocityField]
    exact differentiableAt_const (EuclideanSpace.single nsCoord0 d : NSSpace)

/-- The heat-shear family with vertical drift has the same time derivative as
pure heat shear. -/
theorem timeVelocityDerivative_heatShearVerticalDriftVelocityField
    (ν a k c : ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (heatShearVerticalDriftVelocityField ν a k c) t x =
      coord0Embedding
        (-(ν * k ^ (2 : ℕ)) *
          (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * Real.sin (k * x nsCoord1))) := by
  rw [heatShearVerticalDriftVelocityField]
  rw [timeVelocityDerivative_add]
  · simp [timeVelocityDerivative_heatShearVelocityField,
      timeVelocityDerivative_constantVelocityField]
  · exact smoothSpaceTimeVelocity_differentiableAt_timeSlice
      (smoothSpaceTimeVelocity_heatShearVelocityField ν a k) t x
  · dsimp [constantVelocityField]
    exact differentiableAt_const (EuclideanSpace.single nsCoord2 c : NSSpace)

/-- The heat-shear family with full drift has the same time derivative as pure
heat shear. -/
theorem timeVelocityDerivative_heatShearFullDriftVelocityField
    (ν a k d c : ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (heatShearFullDriftVelocityField ν a k d c) t x =
      coord0Embedding
        (-(ν * k ^ (2 : ℕ)) *
          (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * Real.sin (k * x nsCoord1))) := by
  rw [heatShearFullDriftVelocityField]
  rw [timeVelocityDerivative_add]
  · simp [timeVelocityDerivative_heatShearStreamwiseDriftVelocityField,
      timeVelocityDerivative_constantVelocityField]
  · exact smoothSpaceTimeVelocity_differentiableAt_timeSlice
      (smoothSpaceTimeVelocity_heatShearStreamwiseDriftVelocityField ν a k d) t x
  · dsimp [constantVelocityField]
    exact differentiableAt_const (EuclideanSpace.single nsCoord2 c : NSSpace)

/-- Spatial divergence commutes with constant scalar multiplication. -/
theorem spatialDivergence_const_smul
    (a : ℝ) (u : NSVelocityField) (t : NSTime) (x : NSSpace) :
    spatialDivergence (a • u) t x = a * spatialDivergence u t x := by
  rw [spatialDivergence, spatialFDeriv]
  change ∑ i : Fin 3,
      (fderiv ℝ (a • fun y : NSSpace => u t y) x (EuclideanSpace.single i (1 : ℝ))) i = _
  rw [fderiv_const_smul_field]
  simp
  rw [← Finset.mul_sum]
  rfl

/-- Spatial divergence commutes with addition. -/
theorem spatialDivergence_add
    {u v : NSVelocityField} {t : NSTime} {x : NSSpace}
    (hu : DifferentiableAt ℝ (fun y : NSSpace => u t y) x)
    (hv : DifferentiableAt ℝ (fun y : NSSpace => v t y) x) :
    spatialDivergence (u + v) t x =
      spatialDivergence u t x + spatialDivergence v t x := by
  rw [spatialDivergence, spatialDivergence, spatialDivergence, spatialFDeriv, spatialFDeriv, spatialFDeriv]
  change ∑ i : Fin 3,
      (fderiv ℝ ((fun y : NSSpace => u t y) + fun y : NSSpace => v t y) x
        (EuclideanSpace.single i (1 : ℝ))) i = _
  rw [fderiv_add hu hv]
  simp [Finset.sum_add_distrib]

/-- Spatial divergence of the zero field is zero. -/
theorem spatialDivergence_zero (t : NSTime) (x : NSSpace) :
    spatialDivergence (0 : NSVelocityField) t x = 0 := by
  simp [spatialDivergence, spatialFDeriv]

/-- Spatial divergence of a constant velocity field is zero. -/
theorem spatialDivergence_constantVelocityField
    (c : NSSpace) (t : NSTime) (x : NSSpace) :
    spatialDivergence (constantVelocityField c) t x = 0 := by
  simp [spatialDivergence, spatialFDeriv, constantVelocityField]

/-- Spatial divergence of the time-independent seed is exactly the divergence
of the initial datum. -/
theorem spatialDivergence_timeIndependentVelocity
    (u₀ : NSInitialVelocity) (t : NSTime) (x : NSSpace) :
    spatialDivergence (timeIndependentVelocity u₀) t x =
      initialSpatialDivergence u₀ x :=
  rfl

/-- Spatial divergence of the steady linear shear field is zero. -/
theorem spatialDivergence_linearShearVelocityField
    (a : ℝ) (t : NSTime) (x : NSSpace) :
    spatialDivergence (linearShearVelocityField a) t x = 0 := by
  rw [spatialDivergence, spatialFDeriv_linearShearVelocityField, Fin.sum_univ_three]
  simp [linearShearMap, nsCoord0, nsCoord1, ContinuousLinearMap.smulRight_apply]

/-- The steady field `u(t,x) = (a * x₁, 0, b)` is divergence free. -/
theorem spatialDivergence_linearShearVerticalDriftVelocityField
    (a b : ℝ) (t : NSTime) (x : NSSpace) :
    spatialDivergence (linearShearVerticalDriftVelocityField a b) t x = 0 := by
  rw [linearShearVerticalDriftVelocityField]
  rw [spatialDivergence_add]
  · simp [spatialDivergence_linearShearVelocityField,
      spatialDivergence_constantVelocityField]
  · exact smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_linearShearVelocityField a) t x
  · exact smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord2 b)) t x

/-- The steady field `u(t,x) = (a * x₁, b, 0)` is divergence free. -/
theorem spatialDivergence_linearShearHorizontalDriftVelocityField
    (a b : ℝ) (t : NSTime) (x : NSSpace) :
    spatialDivergence (linearShearHorizontalDriftVelocityField a b) t x = 0 := by
  rw [linearShearHorizontalDriftVelocityField]
  rw [spatialDivergence_add]
  · simp [spatialDivergence_linearShearVelocityField,
      spatialDivergence_constantVelocityField]
  · exact smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_linearShearVelocityField a) t x
  · exact smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord1 b)) t x

/-- The steady field `u(t,x) = (a * x₁, b, c)` is divergence free. -/
theorem spatialDivergence_linearShearFullDriftVelocityField
    (a b c : ℝ) (t : NSTime) (x : NSSpace) :
    spatialDivergence (linearShearFullDriftVelocityField a b c) t x = 0 := by
  rw [linearShearFullDriftVelocityField]
  rw [spatialDivergence_add]
  · simp [spatialDivergence_linearShearHorizontalDriftVelocityField,
      spatialDivergence_constantVelocityField]
  · exact smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_linearShearHorizontalDriftVelocityField a b) t x
  · exact smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord2 c)) t x

/-- The damped sinusoidal heat-shear field is divergence free. -/
theorem spatialDivergence_heatShearVelocityField
    (ν a k : ℝ) (t : NSTime) (x : NSSpace) :
    spatialDivergence (heatShearVelocityField ν a k) t x = 0 := by
  rw [spatialDivergence, spatialFDeriv_heatShearVelocityField, Fin.sum_univ_three]
  simp [coord0Embedding_apply, nsCoord0, nsCoord1]

/-- The general time-amplitude shear ansatz is divergence free on each time
slice. -/
theorem spatialDivergence_amplitudeShearVelocityField
    (A : NSTime → ℝ) (k : ℝ) (t : NSTime) (x : NSSpace) :
    spatialDivergence (amplitudeShearVelocityField A k) t x = 0 := by
  have hslice :
      ∀ y : NSSpace,
        amplitudeShearVelocityField A k t y = heatShearVelocityField 0 (A t) k t y := by
    intro y
    simp [amplitudeShearVelocityField, heatShearVelocityField, heatShearScalar]
  rw [spatialDivergence_congr_at hslice]
  simpa
    using spatialDivergence_heatShearVelocityField 0 (A t) k t x

/-- The heat-shear family with streamwise drift is divergence free. -/
theorem spatialDivergence_heatShearStreamwiseDriftVelocityField
    (ν a k d : ℝ) (t : NSTime) (x : NSSpace) :
    spatialDivergence (heatShearStreamwiseDriftVelocityField ν a k d) t x = 0 := by
  rw [heatShearStreamwiseDriftVelocityField]
  rw [spatialDivergence_add]
  · simp [spatialDivergence_heatShearVelocityField,
      spatialDivergence_constantVelocityField]
  · exact smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_heatShearVelocityField ν a k) t x
  · exact smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord0 d)) t x

/-- The heat-shear family with vertical drift is divergence free. -/
theorem spatialDivergence_heatShearVerticalDriftVelocityField
    (ν a k c : ℝ) (t : NSTime) (x : NSSpace) :
    spatialDivergence (heatShearVerticalDriftVelocityField ν a k c) t x = 0 := by
  rw [heatShearVerticalDriftVelocityField]
  rw [spatialDivergence_add]
  · simp [spatialDivergence_heatShearVelocityField,
      spatialDivergence_constantVelocityField]
  · exact smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_heatShearVelocityField ν a k) t x
  · exact smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord2 c)) t x

/-- The heat-shear family with full drift is spatially divergence free. -/
theorem spatialDivergence_heatShearFullDriftVelocityField
    (ν a k d c : ℝ) (t : NSTime) (x : NSSpace) :
    spatialDivergence (heatShearFullDriftVelocityField ν a k d c) t x = 0 := by
  rw [heatShearFullDriftVelocityField]
  rw [spatialDivergence_add]
  · simp [spatialDivergence_heatShearStreamwiseDriftVelocityField,
      spatialDivergence_constantVelocityField]
  · exact smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_heatShearStreamwiseDriftVelocityField ν a k d) t x
  · exact smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord2 c)) t x

/-- Divergence of initial data commutes with constant scalar multiplication. -/
theorem initialSpatialDivergence_const_smul
    (a : ℝ) (u₀ : NSInitialVelocity) (x : NSSpace) :
    initialSpatialDivergence (a • u₀) x = a * initialSpatialDivergence u₀ x := by
  rw [initialSpatialDivergence]
  rw [fderiv_const_smul_field]
  simp
  rw [← Finset.mul_sum]
  rfl

/-- Divergence of initial data commutes with addition. -/
theorem initialSpatialDivergence_add
    {u₀ v₀ : NSInitialVelocity} {x : NSSpace}
    (hu : DifferentiableAt ℝ u₀ x) (hv : DifferentiableAt ℝ v₀ x) :
    initialSpatialDivergence (u₀ + v₀) x =
      initialSpatialDivergence u₀ x + initialSpatialDivergence v₀ x := by
  rw [initialSpatialDivergence, initialSpatialDivergence, initialSpatialDivergence]
  rw [fderiv_add hu hv]
  simp [Finset.sum_add_distrib]

/-- Divergence of zero initial data is zero. -/
theorem initialSpatialDivergence_zero (x : NSSpace) :
    initialSpatialDivergence (0 : NSInitialVelocity) x = 0 := by
  simp [initialSpatialDivergence]

/-- Divergence of constant initial velocity data is zero. -/
theorem initialSpatialDivergence_constantInitialVelocity
    (c : NSSpace) (x : NSSpace) :
    initialSpatialDivergence (constantInitialVelocity c) x = 0 := by
  unfold initialSpatialDivergence constantInitialVelocity
  simp [fderiv_const_apply]

/-- Divergence of the concrete linear shear initial data is zero. -/
theorem initialSpatialDivergence_linearShearInitialVelocity
    (a : ℝ) (x : NSSpace) :
    initialSpatialDivergence (linearShearInitialVelocity a) x = 0 := by
  have hf :
      fderiv ℝ (linearShearInitialVelocity a) x = linearShearMap a := by
    simp [linearShearInitialVelocity, linearShearMap]
  rw [initialSpatialDivergence, hf, Fin.sum_univ_three]
  simp [linearShearMap, nsCoord0, nsCoord1, ContinuousLinearMap.smulRight_apply]

/-- Divergence of the initial data `x ↦ (a * x₁, 0, b)` is zero. -/
theorem initialSpatialDivergence_linearShearVerticalDriftInitialVelocity
    (a b : ℝ) (x : NSSpace) :
    initialSpatialDivergence (linearShearVerticalDriftInitialVelocity a b) x = 0 := by
  rw [linearShearVerticalDriftInitialVelocity]
  rw [initialSpatialDivergence_add]
  · simp [initialSpatialDivergence_linearShearInitialVelocity,
      initialSpatialDivergence_constantInitialVelocity]
  · exact ((smoothInitialVelocityData_linearShearInitialVelocity a).contDiffAt
      (x := x)).differentiableAt (by simp)
  · exact ((smoothInitialVelocityData_constantInitialVelocity
      (EuclideanSpace.single nsCoord2 b)).contDiffAt (x := x)).differentiableAt (by simp)

/-- Divergence of the initial data `x ↦ (a * x₁, b, 0)` is zero. -/
theorem initialSpatialDivergence_linearShearHorizontalDriftInitialVelocity
    (a b : ℝ) (x : NSSpace) :
    initialSpatialDivergence (linearShearHorizontalDriftInitialVelocity a b) x = 0 := by
  rw [linearShearHorizontalDriftInitialVelocity]
  rw [initialSpatialDivergence_add]
  · simp [initialSpatialDivergence_linearShearInitialVelocity,
      initialSpatialDivergence_constantInitialVelocity]
  · exact ((smoothInitialVelocityData_linearShearInitialVelocity a).contDiffAt
      (x := x)).differentiableAt (by simp)
  · exact ((smoothInitialVelocityData_constantInitialVelocity
      (EuclideanSpace.single nsCoord1 b)).contDiffAt (x := x)).differentiableAt (by simp)

/-- Divergence of the initial data `x ↦ (a * x₁, b, c)` is zero. -/
theorem initialSpatialDivergence_linearShearFullDriftInitialVelocity
    (a b c : ℝ) (x : NSSpace) :
    initialSpatialDivergence (linearShearFullDriftInitialVelocity a b c) x = 0 := by
  rw [linearShearFullDriftInitialVelocity]
  rw [initialSpatialDivergence_add]
  · simp [initialSpatialDivergence_linearShearHorizontalDriftInitialVelocity,
      initialSpatialDivergence_constantInitialVelocity]
  · exact ((smoothInitialVelocityData_linearShearHorizontalDriftInitialVelocity a b).contDiffAt
      (x := x)).differentiableAt (by simp)
  · exact ((smoothInitialVelocityData_constantInitialVelocity
      (EuclideanSpace.single nsCoord2 c)).contDiffAt (x := x)).differentiableAt (by simp)

/-- The damped sinusoidal initial datum is divergence free. -/
theorem initialSpatialDivergence_heatShearInitialVelocity
    (a k : ℝ) (x : NSSpace) :
    initialSpatialDivergence (heatShearInitialVelocity a k) x = 0 := by
  have hslice :
      (fun y : NSSpace => heatShearInitialVelocity a k y) =
        fun y : NSSpace => heatShearVelocityField 0 a k 0 y := by
    funext y
    simp [heatShearVelocityField, heatShearInitialVelocity, heatShearScalar,
      heatShearInitialScalar]
  simpa [initialSpatialDivergence, spatialDivergence, spatialFDeriv, hslice] using
    (spatialDivergence_heatShearVelocityField (ν := 0) a k 0 x : _)

/-- The heat-shear datum with streamwise drift is divergence free. -/
theorem initialSpatialDivergence_heatShearStreamwiseDriftInitialVelocity
    (a k d : ℝ) (x : NSSpace) :
    initialSpatialDivergence (heatShearStreamwiseDriftInitialVelocity a k d) x = 0 := by
  rw [heatShearStreamwiseDriftInitialVelocity]
  rw [initialSpatialDivergence_add]
  · simp [initialSpatialDivergence_heatShearInitialVelocity,
      initialSpatialDivergence_constantInitialVelocity]
  · exact ((smoothInitialVelocityData_heatShearInitialVelocity a k).contDiffAt
      (x := x)).differentiableAt (by simp)
  · exact ((smoothInitialVelocityData_constantInitialVelocity
      (EuclideanSpace.single nsCoord0 d)).contDiffAt (x := x)).differentiableAt (by simp)

/-- The heat-shear datum with vertical drift is divergence free. -/
theorem initialSpatialDivergence_heatShearVerticalDriftInitialVelocity
    (a k c : ℝ) (x : NSSpace) :
    initialSpatialDivergence (heatShearVerticalDriftInitialVelocity a k c) x = 0 := by
  rw [heatShearVerticalDriftInitialVelocity]
  rw [initialSpatialDivergence_add]
  · simp [initialSpatialDivergence_heatShearInitialVelocity,
      initialSpatialDivergence_constantInitialVelocity]
  · exact ((smoothInitialVelocityData_heatShearInitialVelocity a k).contDiffAt
      (x := x)).differentiableAt (by simp)
  · exact ((smoothInitialVelocityData_constantInitialVelocity
      (EuclideanSpace.single nsCoord2 c)).contDiffAt (x := x)).differentiableAt (by simp)

/-- The heat-shear datum with full drift is divergence free. -/
theorem initialSpatialDivergence_heatShearFullDriftInitialVelocity
    (a k d c : ℝ) (x : NSSpace) :
    initialSpatialDivergence (heatShearFullDriftInitialVelocity a k d c) x = 0 := by
  rw [heatShearFullDriftInitialVelocity]
  rw [initialSpatialDivergence_add]
  · simp [initialSpatialDivergence_heatShearStreamwiseDriftInitialVelocity,
      initialSpatialDivergence_constantInitialVelocity]
  · exact ((smoothInitialVelocityData_heatShearStreamwiseDriftInitialVelocity a k d).contDiffAt
      (x := x)).differentiableAt (by simp)
  · exact ((smoothInitialVelocityData_constantInitialVelocity
      (EuclideanSpace.single nsCoord2 c)).contDiffAt (x := x)).differentiableAt (by simp)

/-- Pressure gradient commutes with addition. -/
theorem spatialPressureGradient_add
    {p q : NSPressureField} {t : NSTime} {x : NSSpace}
    (hp : DifferentiableAt ℝ (fun y : NSSpace => p t y) x)
    (hq : DifferentiableAt ℝ (fun y : NSSpace => q t y) x) :
    spatialPressureGradient (p + q) t x =
      spatialPressureGradient p t x + spatialPressureGradient q t x := by
  unfold spatialPressureGradient
  change gradient ((fun y : NSSpace => p t y) + fun y : NSSpace => q t y) x = _
  rw [gradient, fderiv_add hp hq]
  simp [gradient]

/-- Pressure gradient commutes with constant scalar multiplication. -/
theorem spatialPressureGradient_const_smul
    (a : ℝ) (p : NSPressureField) (t : NSTime) (x : NSSpace) :
    spatialPressureGradient (a • p) t x = a • spatialPressureGradient p t x := by
  unfold spatialPressureGradient
  change gradient (a • fun y : NSSpace => p t y) x = _
  rw [gradient, fderiv_const_smul_field]
  simp [gradient]

/-- Pressure gradient commutes with sign flip. -/
theorem spatialPressureGradient_neg
    (p : NSPressureField) (t : NSTime) (x : NSSpace) :
    spatialPressureGradient (-p) t x = -spatialPressureGradient p t x := by
  simpa using spatialPressureGradient_const_smul (-1 : ℝ) p t x

/-- Pressure gradient commutes with subtraction. -/
theorem spatialPressureGradient_sub
    {p q : NSPressureField} {t : NSTime} {x : NSSpace}
    (hp : DifferentiableAt ℝ (fun y : NSSpace => p t y) x)
    (hq : DifferentiableAt ℝ (fun y : NSSpace => q t y) x) :
    spatialPressureGradient (p - q) t x =
      spatialPressureGradient p t x - spatialPressureGradient q t x := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  rw [spatialPressureGradient_add (p := p) (q := -q) hp hq.neg]
  rw [spatialPressureGradient_neg]

/-- Pressure gradient commutes with real linear combinations. -/
theorem spatialPressureGradient_linearCombination
    {p q : NSPressureField} {t : NSTime} {x : NSSpace}
    (a b : ℝ)
    (hp : DifferentiableAt ℝ (fun y : NSSpace => p t y) x)
    (hq : DifferentiableAt ℝ (fun y : NSSpace => q t y) x) :
    spatialPressureGradient (a • p + b • q) t x =
      a • spatialPressureGradient p t x + b • spatialPressureGradient q t x := by
  rw [spatialPressureGradient_add (hp.const_smul a) (hq.const_smul b)]
  rw [spatialPressureGradient_const_smul, spatialPressureGradient_const_smul]

/-- Pressure gradient of the zero field is zero. -/
theorem spatialPressureGradient_zero (t : NSTime) (x : NSSpace) :
    spatialPressureGradient (0 : NSPressureField) t x = 0 := by
  simp [spatialPressureGradient]

/-- Pressure gradient of a spatially constant pressure field is zero. -/
theorem spatialPressureGradient_const
    (c : ℝ) (t : NSTime) (x : NSSpace) :
    spatialPressureGradient (fun _ : NSTime => fun _ : NSSpace => c) t x = 0 := by
  unfold spatialPressureGradient
  simp

/-- Pressure gradient of a time-only pressure field is zero on every spatial
slice. -/
theorem spatialPressureGradient_timeOnly
    (π : NSTime → ℝ) (t : NSTime) (x : NSSpace) :
    spatialPressureGradient (fun s : NSTime => fun _ : NSSpace => π s) t x = 0 := by
  unfold spatialPressureGradient
  simp

/-- Any affine combination of a spatially constant pressure and a time-only
pressure is still time-only, hence has zero spatial gradient on every slice. -/
theorem spatialPressureGradient_affineConstantTimeOnly
    (a b c : ℝ) (π : NSTime → ℝ) (t : NSTime) (x : NSSpace) :
    spatialPressureGradient
      (a • (fun _ : NSTime => fun _ : NSSpace => c) +
        b • (fun s : NSTime => fun _ : NSSpace => π s)) t x = 0 := by
  change
    spatialPressureGradient
      (fun s : NSTime => fun _ : NSSpace => a • c + b • π s) t x = 0
  simpa [smul_eq_mul] using
    spatialPressureGradient_timeOnly (fun s : NSTime => a • c + b • π s) t x

/-- The spatial gradient of the coordinate-linear pressure field
`p(t,x) = c * x₀` is the constant vector `c e₀`. -/
theorem spatialPressureGradient_coord0Linear
    (c : ℝ) (t : NSTime) (x : NSSpace) :
    spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => c * y nsCoord0) t x =
      EuclideanSpace.single nsCoord0 c := by
  have hdual :
      (InnerProductSpace.toDual ℝ NSSpace) (EuclideanSpace.single nsCoord0 c) =
        c • (EuclideanSpace.proj nsCoord0 : NSSpace →L[ℝ] ℝ) := by
    ext y
    rw [InnerProductSpace.toDual_apply_apply]
    simp [EuclideanSpace.inner_single_left, nsCoord0]
  unfold spatialPressureGradient
  apply HasGradientAt.gradient
  rw [hasGradientAt_iff_hasFDerivAt]
  rw [hdual]
  convert ((c : ℝ) • (EuclideanSpace.proj nsCoord0 : NSSpace →L[ℝ] ℝ)).hasFDerivAt using 1

/-- The compensating pressure field `p(t,x) = -(a * b) * x₀` has constant
spatial gradient `-(a * b) e₀`. -/
theorem spatialPressureGradient_linearShearHorizontalDriftPressureField
    (a b : ℝ) (t : NSTime) (x : NSSpace) :
    spatialPressureGradient (linearShearHorizontalDriftPressureField a b) t x =
      EuclideanSpace.single nsCoord0 (-(a * b)) := by
  simpa [linearShearHorizontalDriftPressureField] using
    spatialPressureGradient_coord0Linear (-(a * b)) t x

/-- The smoothness order `C^∞` used for concrete NS fields is at least `C²`. -/
theorem two_le_contDiff_infty : (2 : WithTop ℕ∞) ≤ ∞ := by
  exact WithTop.coe_le_coe.2 (show (2 : ℕ∞) ≤ ⊤ from le_top)

/-- Over the real field, the minimal smoothness needed for symmetric second
derivatives is also available from `C^∞`. -/
theorem minSmoothness_two_le_contDiff_infty : minSmoothness ℝ 2 ≤ ∞ := by
  simpa using two_le_contDiff_infty

/-- View the spatial pressure gradient as a velocity field on `ℝ × ℝ^3`. -/
def pressureGradientVelocityField (p : NSPressureField) : NSVelocityField :=
  fun t x => spatialPressureGradient p t x

/-- The vector field that a pressure gradient must equal in the concrete
momentum equation:
\[
  \nabla p = \nu \Delta u - \partial_t u - (u\cdot\nabla)u.
\]
This isolates the exact-gradient compatibility burden from the rest of the
momentum identity. -/
def momentumPressureResidual (ν : ℝ) (u : NSVelocityField) : NSVelocityField :=
  fun t x =>
    ν • spatialLaplacian u t x - timeVelocityDerivative u t x -
      spatialConvection u t x

/-- A coordinate derivative of the gradient of a smooth scalar field is the
corresponding second Fréchet derivative. -/
theorem fderiv_gradient_component_eq_second_fderiv
    {f : NSSpace → ℝ}
    (hf : ContDiff ℝ ∞ f)
    (x : NSSpace) (coord comp : Fin 3) :
    (fderiv ℝ (fun y : NSSpace => gradient f y) x
        (EuclideanSpace.single coord (1 : ℝ))) comp =
      fderiv ℝ (fun y : NSSpace => fderiv ℝ f y) x
        (EuclideanSpace.single coord (1 : ℝ))
        (EuclideanSpace.single comp (1 : ℝ)) := by
  let ecoord : NSSpace := EuclideanSpace.single coord (1 : ℝ)
  let ecomp : NSSpace := EuclideanSpace.single comp (1 : ℝ)
  have hfdiff : DifferentiableAt ℝ (fun y : NSSpace => fderiv ℝ f y) x := by
    exact ((hf.contDiffAt (x := x)).fderiv_right (m := 1)
      two_le_contDiff_infty).differentiableAt one_ne_zero
  have hgrad_diff : DifferentiableAt ℝ (fun y : NSSpace => gradient f y) x := by
    unfold gradient
    exact (InnerProductSpace.toDual ℝ NSSpace).symm.differentiableAt.comp x hfdiff
  have hproj :
      fderiv ℝ (fun y : NSSpace => (gradient f y) comp) x =
        (EuclideanSpace.proj comp : NSSpace →L[ℝ] ℝ).comp
          (fderiv ℝ (fun y : NSSpace => gradient f y) x) := by
    simpa [Function.comp] using
      fderiv_comp x (EuclideanSpace.proj comp : NSSpace →L[ℝ] ℝ).differentiableAt hgrad_diff
  have hvec_scalar :
      (fderiv ℝ (fun y : NSSpace => gradient f y) x ecoord) comp =
        fderiv ℝ (fun y : NSSpace => (gradient f y) comp) x ecoord := by
    simpa [ContinuousLinearMap.comp_apply, ecoord] using
      (congrArg (fun L : NSSpace →L[ℝ] ℝ => L ecoord) hproj).symm
  have hcomp_eq :
      (fun y : NSSpace => (gradient f y) comp) =
        fun y : NSSpace => fderiv ℝ f y ecomp := by
    funext y
    have hdy : DifferentiableAt ℝ f y := (hf.differentiable (by simp)) y
    have hinner : inner ℝ ecomp (gradient f y) = fderiv ℝ f y ecomp := by
      simpa [ecomp] using inner_gradient_right (x := ecomp) (y := y) hdy
    calc
      (gradient f y) comp = inner ℝ ecomp (gradient f y) := by
        simp [ecomp, EuclideanSpace.inner_single_left]
      _ = fderiv ℝ f y ecomp := hinner
  have hscalar :
      fderiv ℝ (fun y : NSSpace => (gradient f y) comp) x ecoord =
        fderiv ℝ (fun y : NSSpace => fderiv ℝ f y ecomp) x ecoord := by
    rw [hcomp_eq]
  have happly :
      fderiv ℝ (fun y : NSSpace => fderiv ℝ f y ecomp) x ecoord =
        fderiv ℝ (fun y : NSSpace => fderiv ℝ f y) x ecoord ecomp := by
    have h := fderiv_comp x (ContinuousLinearMap.apply ℝ ℝ ecomp).differentiableAt hfdiff
    simpa [ContinuousLinearMap.comp_apply, ecoord] using
      congrArg (fun L : NSSpace →L[ℝ] ℝ => L ecoord) h
  calc
    (fderiv ℝ (fun y : NSSpace => gradient f y) x
        (EuclideanSpace.single coord (1 : ℝ))) comp
        = (fderiv ℝ (fun y : NSSpace => gradient f y) x ecoord) comp := by rfl
    _ = fderiv ℝ (fun y : NSSpace => (gradient f y) comp) x ecoord := hvec_scalar
    _ = fderiv ℝ (fun y : NSSpace => fderiv ℝ f y ecomp) x ecoord := hscalar
    _ = fderiv ℝ (fun y : NSSpace => fderiv ℝ f y) x ecoord ecomp := happly
    _ = fderiv ℝ (fun y : NSSpace => fderiv ℝ f y) x
        (EuclideanSpace.single coord (1 : ℝ))
        (EuclideanSpace.single comp (1 : ℝ)) := by rfl

/-- A coordinate derivative of an arbitrary smooth pressure-gradient field is
the corresponding mixed second derivative of the pressure slice. -/
theorem spatialDerivativeComponent_pressureGradientVelocityField
    {p : NSPressureField}
    (hp : smoothSpaceTimePressure p)
    (t : NSTime) (x : NSSpace) (coord comp : Fin 3) :
    spatialDerivativeComponent (pressureGradientVelocityField p) t x coord comp =
      fderiv ℝ (fun y : NSSpace => fderiv ℝ (fun z : NSSpace => p t z) y) x
        (EuclideanSpace.single coord (1 : ℝ))
        (EuclideanSpace.single comp (1 : ℝ)) := by
  let f : NSSpace → ℝ := fun z => p t z
  change (fderiv ℝ (fun y : NSSpace => gradient f y) x
        (EuclideanSpace.single coord (1 : ℝ))) comp = _
  exact fderiv_gradient_component_eq_second_fderiv
    (f := f) (smoothSpaceTimePressure_contDiff_spatialSlice hp t) x coord comp

/-- The spatial curl/vorticity of an arbitrary smooth pressure-gradient field
vanishes. This is a structural integrability obstruction, not a property of a
particular pressure ansatz. -/
theorem spatialVorticity_pressureGradientVelocityField
    {p : NSPressureField}
    (hp : smoothSpaceTimePressure p)
    (t : NSTime) (x : NSSpace) :
    spatialVorticity (pressureGradientVelocityField p) t x = 0 := by
  let f : NSSpace → ℝ := fun z => p t z
  have hf : ContDiff ℝ ∞ f := smoothSpaceTimePressure_contDiff_spatialSlice hp t
  have hsymm : IsSymmSndFDerivAt ℝ f x := by
    exact (hf.contDiffAt (x := x)).isSymmSndFDerivAt minSmoothness_two_le_contDiff_infty
  ext i
  fin_cases i
  · simp [spatialVorticity, spatialDerivativeComponent_pressureGradientVelocityField hp,
      nsCoord0, nsCoord1, nsCoord2]
    exact sub_eq_zero.mpr (hsymm.eq (EuclideanSpace.single nsCoord1 (1 : ℝ))
      (EuclideanSpace.single nsCoord2 (1 : ℝ)))
  · simp [spatialVorticity, spatialDerivativeComponent_pressureGradientVelocityField hp,
      nsCoord0, nsCoord1, nsCoord2]
    exact sub_eq_zero.mpr (hsymm.eq (EuclideanSpace.single nsCoord2 (1 : ℝ))
      (EuclideanSpace.single nsCoord0 (1 : ℝ)))
  · simp [spatialVorticity, spatialDerivativeComponent_pressureGradientVelocityField hp,
      nsCoord0, nsCoord1, nsCoord2]
    exact sub_eq_zero.mpr (hsymm.eq (EuclideanSpace.single nsCoord0 (1 : ℝ))
      (EuclideanSpace.single nsCoord1 (1 : ℝ)))

/-- A velocity field with nonzero vorticity somewhere cannot be represented as
the spatial gradient of any smooth pressure field. -/
theorem not_exists_smoothPressure_pressureGradientVelocityField_eq_of_spatialVorticity_ne_zero
    {u : NSVelocityField}
    (hcurl : ∃ t : NSTime, ∃ x : NSSpace, spatialVorticity u t x ≠ 0) :
    ¬ ∃ p : NSPressureField,
      smoothSpaceTimePressure p ∧ pressureGradientVelocityField p = u := by
  rintro ⟨p, hp, hpu⟩
  rcases hcurl with ⟨t, x, hne⟩
  apply hne
  rw [← hpu]
  exact spatialVorticity_pressureGradientVelocityField hp t x

/-- Any pressure satisfying the concrete momentum equation has gradient equal
to the exact pressure residual `ν Δu - ∂ₜu - (u · ∇)u`. -/
theorem pressureGradientVelocityField_eq_momentumPressureResidual_of_momentumEquation
    {ν : ℝ} {u : NSVelocityField} {p : NSPressureField}
    (hmom : ∀ t x,
      timeVelocityDerivative u t x + spatialConvection u t x +
          spatialPressureGradient p t x =
        ν • spatialLaplacian u t x) :
    pressureGradientVelocityField p = momentumPressureResidual ν u := by
  funext t x
  have h := hmom t x
  unfold pressureGradientVelocityField momentumPressureResidual
  calc
    spatialPressureGradient p t x =
        (timeVelocityDerivative u t x + spatialConvection u t x +
          spatialPressureGradient p t x) -
            timeVelocityDerivative u t x - spatialConvection u t x := by
      abel
    _ = ν • spatialLaplacian u t x -
          timeVelocityDerivative u t x - spatialConvection u t x := by
      rw [h]

/-- Therefore the exact pressure residual of any smooth-pressure momentum
solution is curl-free. -/
theorem spatialVorticity_momentumPressureResidual_of_momentumEquation
    {ν : ℝ} {u : NSVelocityField} {p : NSPressureField}
    (hp : smoothSpaceTimePressure p)
    (hmom : ∀ t x,
      timeVelocityDerivative u t x + spatialConvection u t x +
          spatialPressureGradient p t x =
        ν • spatialLaplacian u t x)
    (t : NSTime) (x : NSSpace) :
    spatialVorticity (momentumPressureResidual ν u) t x = 0 := by
  rw [← pressureGradientVelocityField_eq_momentumPressureResidual_of_momentumEquation hmom]
  exact spatialVorticity_pressureGradientVelocityField hp t x

/-- If the concrete pressure residual has nonzero curl somewhere, no smooth
pressure can repair the momentum equation for that velocity field. -/
theorem not_exists_smoothPressure_momentumEquation_of_momentumPressureResidual_vorticity_ne_zero
    {ν : ℝ} {u : NSVelocityField}
    (hcurl : ∃ t : NSTime, ∃ x : NSSpace,
      spatialVorticity (momentumPressureResidual ν u) t x ≠ 0) :
    ¬ ∃ p : NSPressureField,
      smoothSpaceTimePressure p ∧
        ∀ t x,
          timeVelocityDerivative u t x + spatialConvection u t x +
              spatialPressureGradient p t x =
            ν • spatialLaplacian u t x := by
  rintro ⟨p, hp, hmom⟩
  rcases hcurl with ⟨t, x, hne⟩
  exact hne (spatialVorticity_momentumPressureResidual_of_momentumEquation hp hmom t x)

/-- The explicit constant velocity field matches the corresponding constant
initial data at time `0`. -/
theorem matchesInitialVelocity_constantVelocityField
    (c : NSSpace) :
    MatchesInitialVelocity (constantInitialVelocity c) (constantVelocityField c) := by
  intro x
  rfl

/-- The steady linear shear field matches the corresponding linear shear
initial data at time `0`. -/
theorem matchesInitialVelocity_linearShearVelocityField
    (a : ℝ) :
    MatchesInitialVelocity (linearShearInitialVelocity a) (linearShearVelocityField a) := by
  intro x
  rfl

/-- The steady field `u(t,x) = (a * x₁, 0, b)` matches the corresponding
initial data at time `0`. -/
theorem matchesInitialVelocity_linearShearVerticalDriftVelocityField
    (a b : ℝ) :
    MatchesInitialVelocity
      (linearShearVerticalDriftInitialVelocity a b)
      (linearShearVerticalDriftVelocityField a b) := by
  intro x
  rfl

/-- The steady field `u(t,x) = (a * x₁, b, 0)` matches the corresponding
initial data at time `0`. -/
theorem matchesInitialVelocity_linearShearHorizontalDriftVelocityField
    (a b : ℝ) :
    MatchesInitialVelocity
      (linearShearHorizontalDriftInitialVelocity a b)
      (linearShearHorizontalDriftVelocityField a b) := by
  intro x
  rfl

/-- The steady field `u(t,x) = (a * x₁, b, c)` matches the corresponding
initial data at time `0`. -/
theorem matchesInitialVelocity_linearShearFullDriftVelocityField
    (a b c : ℝ) :
    MatchesInitialVelocity
      (linearShearFullDriftInitialVelocity a b c)
      (linearShearFullDriftVelocityField a b c) := by
  intro x
  rfl

/-- The damped sinusoidal heat-shear field matches the corresponding initial
datum at time `0`. -/
theorem matchesInitialVelocity_heatShearVelocityField
    (ν a k : ℝ) :
    MatchesInitialVelocity
      (heatShearInitialVelocity a k)
      (heatShearVelocityField ν a k) := by
  intro x
  simp [heatShearVelocityField, heatShearInitialVelocity, heatShearScalar, heatShearInitialScalar]

/-- The heat-shear family with streamwise drift matches its declared initial
data at time `0`. -/
theorem matchesInitialVelocity_heatShearStreamwiseDriftVelocityField
    (ν a k d : ℝ) :
    MatchesInitialVelocity
      (heatShearStreamwiseDriftInitialVelocity a k d)
      (heatShearStreamwiseDriftVelocityField ν a k d) := by
  intro x
  simp [heatShearStreamwiseDriftVelocityField, heatShearStreamwiseDriftInitialVelocity,
    heatShearVelocityField, heatShearInitialVelocity, heatShearScalar, heatShearInitialScalar,
    constantVelocityField, constantInitialVelocity, nsCoord0]

/-- The heat-shear family with vertical drift matches its declared initial
data at time `0`. -/
theorem matchesInitialVelocity_heatShearVerticalDriftVelocityField
    (ν a k c : ℝ) :
    MatchesInitialVelocity
      (heatShearVerticalDriftInitialVelocity a k c)
      (heatShearVerticalDriftVelocityField ν a k c) := by
  intro x
  simp [heatShearVerticalDriftVelocityField, heatShearVerticalDriftInitialVelocity,
    heatShearVelocityField, heatShearInitialVelocity, heatShearScalar, heatShearInitialScalar,
    constantVelocityField, constantInitialVelocity]

/-- The heat-shear family with full drift matches its declared initial data at
time `0`. -/
theorem matchesInitialVelocity_heatShearFullDriftVelocityField
    (ν a k d c : ℝ) :
    MatchesInitialVelocity
      (heatShearFullDriftInitialVelocity a k d c)
      (heatShearFullDriftVelocityField ν a k d c) := by
  intro x
  simp [heatShearFullDriftVelocityField, heatShearFullDriftInitialVelocity,
    heatShearStreamwiseDriftVelocityField, heatShearStreamwiseDriftInitialVelocity,
    heatShearVelocityField, heatShearInitialVelocity, heatShearScalar, heatShearInitialScalar,
    constantVelocityField, constantInitialVelocity, nsCoord0]

/-- The spatial Laplacian commutes with addition on twice continuously
differentiable slices. -/
theorem spatialLaplacian_add
    {u v : NSVelocityField} {t : NSTime} {x : NSSpace}
    (hu : ContDiffAt ℝ 2 (fun y : NSSpace => u t y) x)
    (hv : ContDiffAt ℝ 2 (fun y : NSSpace => v t y) x) :
    spatialLaplacian (u + v) t x =
      spatialLaplacian u t x + spatialLaplacian v t x := by
  unfold spatialLaplacian
  change Δ ((fun y : NSSpace => u t y) + fun y : NSSpace => v t y) x = _
  simpa using hu.laplacian_add hv

/-- The spatial Laplacian commutes with constant scalar multiplication on twice
continuously differentiable slices. -/
theorem spatialLaplacian_const_smul
    (a : ℝ) {u : NSVelocityField} {t : NSTime} {x : NSSpace}
    (hu : ContDiffAt ℝ 2 (fun y : NSSpace => u t y) x) :
    spatialLaplacian (a • u) t x = a • spatialLaplacian u t x := by
  unfold spatialLaplacian
  change Δ (a • fun y : NSSpace => u t y) x = a • Δ (fun y : NSSpace => u t y) x
  simpa using InnerProductSpace.laplacian_smul a hu

/-- The spatial Laplacian of a constant velocity field is zero. -/
theorem spatialLaplacian_constantVelocityField
    (c : NSSpace) (t : NSTime) (x : NSSpace) :
    spatialLaplacian (constantVelocityField c) t x = 0 := by
  unfold spatialLaplacian constantVelocityField
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  rw [iteratedFDeriv_const_of_ne (𝕜 := ℝ) (E := NSSpace) (F := NSSpace) (n := 2)
    (by simp) c]
  simp

/-- Any continuous linear map on `ℝ^3` has zero Laplacian. -/
theorem laplacian_continuousLinearMap_zero
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (l : NSSpace →L[ℝ] F) (x : NSSpace) :
    Δ (fun y : NSSpace => l y) x = 0 := by
  let m : NSSpace →L[ℝ] (ContinuousMultilinearMap ℝ (fun _ : Fin 0 => NSSpace) F) :=
    ((continuousMultilinearCurryFin0 ℝ NSSpace F).symm : F ≃L[ℝ] _).toContinuousLinearMap.comp l
  have h1 : iteratedFDeriv ℝ 1 (fun y : NSSpace => l y) = fun _ =>
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 1 => NSSpace) F).symm m := by
    funext z
    rw [iteratedFDeriv_succ_eq_comp_left]
    change ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 1 => NSSpace) F).symm)
        (fderiv ℝ (((continuousMultilinearCurryFin0 ℝ NSSpace F).symm : F ≃L[ℝ] _) ∘
          fun y : NSSpace => l y) z) = _
    congr 1
    simpa [m] using m.fderiv (x := z)
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  rw [iteratedFDeriv_succ_eq_comp_left]
  simp [h1]

/-- The steady linear shear field has zero spatial Laplacian. -/
theorem spatialLaplacian_linearShearVelocityField
    (a : ℝ) (t : NSTime) (x : NSSpace) :
    spatialLaplacian (linearShearVelocityField a) t x = 0 := by
  simpa [spatialLaplacian, linearShearVelocityField, linearShearInitialVelocity] using
    (laplacian_continuousLinearMap_zero (F := NSSpace) (linearShearMap a) x)

/-- The steady field `u(t,x) = (a * x₁, 0, b)` has zero spatial Laplacian. -/
theorem spatialLaplacian_linearShearVerticalDriftVelocityField
    (a b : ℝ) (t : NSTime) (x : NSSpace) :
    spatialLaplacian (linearShearVerticalDriftVelocityField a b) t x = 0 := by
  rw [linearShearVerticalDriftVelocityField]
  rw [spatialLaplacian_add]
  · simp [spatialLaplacian_linearShearVelocityField,
      spatialLaplacian_constantVelocityField]
  · exact ((smoothSpaceTimeVelocity_contDiff_spatialSlice
      (smoothSpaceTimeVelocity_linearShearVelocityField a) t).contDiffAt
      (x := x)).of_le (by
        exact ENat.natCast_le_of_coe_top_le_withTop
          (N := (∞ : WithTop ℕ∞)) (by rfl) 2)
  · exact ((smoothSpaceTimeVelocity_contDiff_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord2 b)) t).contDiffAt
      (x := x)).of_le (by
        exact ENat.natCast_le_of_coe_top_le_withTop
          (N := (∞ : WithTop ℕ∞)) (by rfl) 2)

/-- The steady field `u(t,x) = (a * x₁, b, 0)` has zero spatial Laplacian. -/
theorem spatialLaplacian_linearShearHorizontalDriftVelocityField
    (a b : ℝ) (t : NSTime) (x : NSSpace) :
    spatialLaplacian (linearShearHorizontalDriftVelocityField a b) t x = 0 := by
  rw [linearShearHorizontalDriftVelocityField]
  rw [spatialLaplacian_add]
  · simp [spatialLaplacian_linearShearVelocityField,
      spatialLaplacian_constantVelocityField]
  · exact ((smoothSpaceTimeVelocity_contDiff_spatialSlice
      (smoothSpaceTimeVelocity_linearShearVelocityField a) t).contDiffAt
      (x := x)).of_le (by
        exact ENat.natCast_le_of_coe_top_le_withTop
          (N := (∞ : WithTop ℕ∞)) (by rfl) 2)
  · exact ((smoothSpaceTimeVelocity_contDiff_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord1 b)) t).contDiffAt
      (x := x)).of_le (by
        exact ENat.natCast_le_of_coe_top_le_withTop
          (N := (∞ : WithTop ℕ∞)) (by rfl) 2)

/-- The steady field `u(t,x) = (a * x₁, b, c)` has zero spatial Laplacian. -/
theorem spatialLaplacian_linearShearFullDriftVelocityField
    (a b c : ℝ) (t : NSTime) (x : NSSpace) :
    spatialLaplacian (linearShearFullDriftVelocityField a b c) t x = 0 := by
  rw [linearShearFullDriftVelocityField]
  rw [spatialLaplacian_add]
  · simp [spatialLaplacian_linearShearHorizontalDriftVelocityField,
      spatialLaplacian_constantVelocityField]
  · exact ((smoothSpaceTimeVelocity_contDiff_spatialSlice
      (smoothSpaceTimeVelocity_linearShearHorizontalDriftVelocityField a b) t).contDiffAt
      (x := x)).of_le (by
        exact ENat.natCast_le_of_coe_top_le_withTop
          (N := (∞ : WithTop ℕ∞)) (by rfl) 2)
  · exact ((smoothSpaceTimeVelocity_contDiff_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord2 c)) t).contDiffAt
      (x := x)).of_le (by
        exact ENat.natCast_le_of_coe_top_le_withTop
          (N := (∞ : WithTop ℕ∞)) (by rfl) 2)

/-- The scalar Laplacian of the damped sinusoidal heat-shear profile is the
expected one-dimensional second derivative in the `x₁` direction. -/
theorem laplacian_heatShearScalar
    (ν a k : ℝ) (t : NSTime) (x : NSSpace) :
    Δ (fun y : NSSpace => heatShearScalar ν a k t y) x =
      -(k ^ (2 : ℕ)) *
        (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * Real.sin (k * x nsCoord1)) := by
  let A : ℝ := a * Real.exp (-(ν * k ^ (2 : ℕ)) * t)
  let g : ℝ → ℝ := fun s => A * Real.sin (k * s)
  have hg : ContDiff ℝ 2 g := by
    simpa [g, A, smul_eq_mul, mul_assoc] using
      (Real.contDiff_sin.comp ((contDiff_id).const_smul k)).const_smul A
  have hlapx :
      Δ (fun y : NSSpace => heatShearScalar ν a k t y) x =
        ∑ i : Fin 3,
          (iteratedFDeriv ℝ 2 (fun y : NSSpace => heatShearScalar ν a k t y) x)
            ![(EuclideanSpace.basisFun (Fin 3) ℝ) i, (EuclideanSpace.basisFun (Fin 3) ℝ) i] := by
    simpa using congrArg (fun h : NSSpace → ℝ => h x)
      (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
        (f := fun y : NSSpace => heatShearScalar ν a k t y)
        (v := EuclideanSpace.basisFun (Fin 3) ℝ))
  rw [hlapx]
  rw [Fin.sum_univ_three]
  have hcoord :
      iteratedFDeriv ℝ 2 (fun y : NSSpace => heatShearScalar ν a k t y) x =
        (iteratedFDeriv ℝ 2 g (x nsCoord1)).compContinuousLinearMap
          (fun _ => (EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ)) := by
    simpa [heatShearScalar, g, A, Function.comp, mul_assoc] using
      (ContinuousLinearMap.iteratedFDeriv_comp_right
        (EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ) hg x (i := 2) (by norm_num))
  rw [hcoord]
  have h0 :
      (fun i => (![(EuclideanSpace.single (0 : Fin 3) (1 : ℝ)),
        EuclideanSpace.single (0 : Fin 3) (1 : ℝ)] i).ofLp nsCoord1) = 0 := by
    funext i
    fin_cases i <;> simp [nsCoord1]
  have h1 :
      (fun i => (![(EuclideanSpace.single (1 : Fin 3) (1 : ℝ)),
        EuclideanSpace.single (1 : Fin 3) (1 : ℝ)] i).ofLp nsCoord1) = fun _ => (1 : ℝ) := by
    funext i
    fin_cases i <;> simp [nsCoord1]
  have h2 :
      (fun i => (![(EuclideanSpace.single (2 : Fin 3) (1 : ℝ)),
        EuclideanSpace.single (2 : Fin 3) (1 : ℝ)] i).ofLp nsCoord1) = 0 := by
    funext i
    fin_cases i <;> simp [nsCoord1]
  have hz0 :
      ((iteratedFDeriv ℝ 2 g (x nsCoord1)).compContinuousLinearMap
        (fun _ => (EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ)))
        ![(EuclideanSpace.basisFun (Fin 3) ℝ) 0, (EuclideanSpace.basisFun (Fin 3) ℝ) 0] = 0 := by
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    simp [EuclideanSpace.basisFun_apply]
    rw [h0]
    simp
  have h1eval :
      ((iteratedFDeriv ℝ 2 g (x nsCoord1)).compContinuousLinearMap
        (fun _ => (EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ)))
        ![(EuclideanSpace.basisFun (Fin 3) ℝ) 1, (EuclideanSpace.basisFun (Fin 3) ℝ) 1] =
        iteratedDeriv 2 g (x nsCoord1) := by
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    simp [EuclideanSpace.basisFun_apply]
    rw [h1]
    simp [iteratedDeriv_eq_iteratedFDeriv]
  have hz2 :
      ((iteratedFDeriv ℝ 2 g (x nsCoord1)).compContinuousLinearMap
        (fun _ => (EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ)))
        ![(EuclideanSpace.basisFun (Fin 3) ℝ) 2, (EuclideanSpace.basisFun (Fin 3) ℝ) 2] = 0 := by
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    simp [EuclideanSpace.basisFun_apply]
    rw [h2]
    simp
  rw [hz0, h1eval, hz2]
  simp [g, A, iteratedDeriv_const_mul_field, iteratedDeriv_comp_const_mul, Real.contDiff_sin]
  ring

/-- The damped sinusoidal heat-shear velocity field has the expected heat
Laplacian in the first velocity component. -/
theorem spatialLaplacian_heatShearVelocityField
    (ν a k : ℝ) (t : NSTime) (x : NSSpace) :
    spatialLaplacian (heatShearVelocityField ν a k) t x =
      coord0Embedding
        (-(k ^ (2 : ℕ)) *
          (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * Real.sin (k * x nsCoord1))) := by
  let A : ℝ := a * Real.exp (-(ν * k ^ (2 : ℕ)) * t)
  let g : ℝ → ℝ := fun s => A * Real.sin (k * s)
  have hg : ContDiff ℝ 2 g := by
    simpa [g, A, smul_eq_mul, mul_assoc] using
      (Real.contDiff_sin.comp ((contDiff_id).const_smul k)).const_smul A
  have hscalar : ContDiffAt ℝ 2 (fun y : NSSpace => heatShearScalar ν a k t y) x := by
    have hcont : ContDiff ℝ 2 (fun y : NSSpace => heatShearScalar ν a k t y) := by
      simpa [heatShearScalar, g, A, Function.comp, mul_assoc] using
        hg.comp ((EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ).contDiff)
    exact hcont.contDiffAt
  unfold spatialLaplacian
  rw [show (fun y : NSSpace => heatShearVelocityField ν a k t y) =
      coord0Embedding ∘ fun y : NSSpace => heatShearScalar ν a k t y by
      funext y
      rfl]
  rw [hscalar.laplacian_CLM_comp_left (l := coord0Embedding)]
  simp [laplacian_heatShearScalar]

/-- The spatial Laplacian of the general time-amplitude shear ansatz is the
same sine-mode Laplacian, with the sampled amplitude `A t`. -/
theorem spatialLaplacian_amplitudeShearVelocityField
    (A : NSTime → ℝ) (k : ℝ) (t : NSTime) (x : NSSpace) :
    spatialLaplacian (amplitudeShearVelocityField A k) t x =
      coord0Embedding
        (-(k ^ (2 : ℕ)) * (A t * Real.sin (k * x nsCoord1))) := by
  have hslice :
      ∀ y : NSSpace,
        amplitudeShearVelocityField A k t y = heatShearVelocityField 0 (A t) k t y := by
    intro y
    simp [amplitudeShearVelocityField, heatShearVelocityField, heatShearScalar]
  rw [spatialLaplacian_congr_at hslice]
  simpa [heatShearScalar]
    using spatialLaplacian_heatShearVelocityField 0 (A t) k t x

/-- The heat-shear family with streamwise drift has the same spatial Laplacian
as pure heat shear. -/
theorem spatialLaplacian_heatShearStreamwiseDriftVelocityField
    (ν a k d : ℝ) (t : NSTime) (x : NSSpace) :
    spatialLaplacian (heatShearStreamwiseDriftVelocityField ν a k d) t x =
      coord0Embedding
        (-(k ^ (2 : ℕ)) *
          (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * Real.sin (k * x nsCoord1))) := by
  rw [heatShearStreamwiseDriftVelocityField]
  rw [spatialLaplacian_add]
  · simp [spatialLaplacian_heatShearVelocityField,
      spatialLaplacian_constantVelocityField]
  · exact ((smoothSpaceTimeVelocity_contDiff_spatialSlice
      (smoothSpaceTimeVelocity_heatShearVelocityField ν a k) t).contDiffAt
        (x := x)).of_le (by
          exact ENat.natCast_le_of_coe_top_le_withTop
            (N := (∞ : WithTop ℕ∞)) (by rfl) 2)
  · exact ((smoothSpaceTimeVelocity_contDiff_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord0 d)) t).contDiffAt
          (x := x)).of_le (by
            exact ENat.natCast_le_of_coe_top_le_withTop
              (N := (∞ : WithTop ℕ∞)) (by rfl) 2)

/-- The heat-shear family with vertical drift has the same spatial Laplacian
as pure heat shear. -/
theorem spatialLaplacian_heatShearVerticalDriftVelocityField
    (ν a k c : ℝ) (t : NSTime) (x : NSSpace) :
    spatialLaplacian (heatShearVerticalDriftVelocityField ν a k c) t x =
      coord0Embedding
        (-(k ^ (2 : ℕ)) *
          (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * Real.sin (k * x nsCoord1))) := by
  rw [heatShearVerticalDriftVelocityField]
  rw [spatialLaplacian_add]
  · simp [spatialLaplacian_heatShearVelocityField,
      spatialLaplacian_constantVelocityField]
  · exact ((smoothSpaceTimeVelocity_contDiff_spatialSlice
      (smoothSpaceTimeVelocity_heatShearVelocityField ν a k) t).contDiffAt
        (x := x)).of_le (by
          exact ENat.natCast_le_of_coe_top_le_withTop
            (N := (∞ : WithTop ℕ∞)) (by rfl) 2)
  · exact ((smoothSpaceTimeVelocity_contDiff_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord2 c)) t).contDiffAt
          (x := x)).of_le (by
            exact ENat.natCast_le_of_coe_top_le_withTop
              (N := (∞ : WithTop ℕ∞)) (by rfl) 2)

/-- The heat-shear family with full drift has the same spatial Laplacian as
pure heat shear. -/
theorem spatialLaplacian_heatShearFullDriftVelocityField
    (ν a k d c : ℝ) (t : NSTime) (x : NSSpace) :
    spatialLaplacian (heatShearFullDriftVelocityField ν a k d c) t x =
      coord0Embedding
        (-(k ^ (2 : ℕ)) *
          (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * Real.sin (k * x nsCoord1))) := by
  rw [heatShearFullDriftVelocityField]
  rw [spatialLaplacian_add]
  · simp [spatialLaplacian_heatShearStreamwiseDriftVelocityField,
      spatialLaplacian_constantVelocityField]
  · exact ((smoothSpaceTimeVelocity_contDiff_spatialSlice
      (smoothSpaceTimeVelocity_heatShearStreamwiseDriftVelocityField ν a k d) t).contDiffAt
        (x := x)).of_le (by
          exact ENat.natCast_le_of_coe_top_le_withTop
            (N := (∞ : WithTop ℕ∞)) (by rfl) 2)
  · exact ((smoothSpaceTimeVelocity_contDiff_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord2 c)) t).contDiffAt
          (x := x)).of_le (by
            exact ENat.natCast_le_of_coe_top_le_withTop
              (N := (∞ : WithTop ℕ∞)) (by rfl) 2)

/-- A coordinate derivative commutes with constant scalar multiplication. -/
theorem spatialDerivativeComponent_const_smul
    (a : ℝ) (u : NSVelocityField) (t : NSTime) (x : NSSpace)
    (coord comp : Fin 3) :
    spatialDerivativeComponent (a • u) t x coord comp =
      a * spatialDerivativeComponent u t x coord comp := by
  rw [spatialDerivativeComponent, spatialFDeriv]
  change (fderiv ℝ (a • fun y : NSSpace => u t y) x (EuclideanSpace.single coord (1 : ℝ))) comp = _
  rw [fderiv_const_smul_field]
  rfl

/-- A coordinate derivative commutes with addition. -/
theorem spatialDerivativeComponent_add
    {u v : NSVelocityField} {t : NSTime} {x : NSSpace}
    (hu : DifferentiableAt ℝ (fun y : NSSpace => u t y) x)
    (hv : DifferentiableAt ℝ (fun y : NSSpace => v t y) x)
    (coord comp : Fin 3) :
    spatialDerivativeComponent (u + v) t x coord comp =
      spatialDerivativeComponent u t x coord comp +
        spatialDerivativeComponent v t x coord comp := by
  rw [spatialDerivativeComponent, spatialDerivativeComponent, spatialDerivativeComponent,
    spatialFDeriv, spatialFDeriv, spatialFDeriv]
  change (fderiv ℝ ((fun y : NSSpace => u t y) + fun y : NSSpace => v t y) x
      (EuclideanSpace.single coord (1 : ℝ))) comp = _
  rw [fderiv_add hu hv]
  rfl

/-- A coordinate derivative of the zero field is zero. -/
theorem spatialDerivativeComponent_zero
    (t : NSTime) (x : NSSpace) (coord comp : Fin 3) :
    spatialDerivativeComponent (0 : NSVelocityField) t x coord comp = 0 := by
  simp [spatialDerivativeComponent, spatialFDeriv]

/-- Every coordinate derivative of a constant velocity field is zero. -/
theorem spatialDerivativeComponent_constantVelocityField
    (c : NSSpace) (t : NSTime) (x : NSSpace) (coord comp : Fin 3) :
    spatialDerivativeComponent (constantVelocityField c) t x coord comp = 0 := by
  simp [spatialDerivativeComponent, spatialFDeriv, constantVelocityField]

/-- The convection term of the zero field is zero. -/
theorem spatialConvection_zero
    (t : NSTime) (x : NSSpace) :
    spatialConvection (0 : NSVelocityField) t x = 0 := by
  rw [spatialConvection, spatialFDeriv_zero]
  simp

/-- The convection term is quadratic under constant velocity rescaling. -/
theorem spatialConvection_const_smul
    (a : ℝ) (u : NSVelocityField) (t : NSTime) (x : NSSpace) :
    spatialConvection (a • u) t x = (a ^ (2 : ℕ)) • spatialConvection u t x := by
  rw [spatialConvection, spatialFDeriv_const_smul]
  calc
    (a • spatialFDeriv u t x) (a • u t x) = a • (spatialFDeriv u t x (a • u t x)) := by
      simp
    _ = a • (a • spatialFDeriv u t x (u t x)) := by
      simp
    _ = (a ^ (2 : ℕ)) • spatialConvection u t x := by
      simp [spatialConvection, pow_two, smul_smul]

/-- The convection term expands over addition into the two self-terms plus the
two mixed directional-derivative terms. -/
theorem spatialConvection_add
    {u v : NSVelocityField} {t : NSTime} {x : NSSpace}
    (hu : DifferentiableAt ℝ (fun y : NSSpace => u t y) x)
    (hv : DifferentiableAt ℝ (fun y : NSSpace => v t y) x) :
    spatialConvection (u + v) t x =
      spatialConvection u t x + spatialFDeriv u t x (v t x) +
        spatialFDeriv v t x (u t x) + spatialConvection v t x := by
  rw [spatialConvection, spatialFDeriv_add hu hv]
  calc
    (spatialFDeriv u t x + spatialFDeriv v t x) (u t x + v t x) =
        spatialFDeriv u t x (u t x + v t x) +
          spatialFDeriv v t x (u t x + v t x) := by
      simp
    _ =
        (spatialFDeriv u t x (u t x) + spatialFDeriv u t x (v t x)) +
          (spatialFDeriv v t x (u t x) + spatialFDeriv v t x (v t x)) := by
      simp
    _ =
        spatialConvection u t x + spatialFDeriv u t x (v t x) +
          spatialFDeriv v t x (u t x) + spatialConvection v t x := by
      simp [spatialConvection]
      ac_rfl

/-- The convection term is unchanged under sign flip. -/
theorem spatialConvection_neg
    (u : NSVelocityField) (t : NSTime) (x : NSSpace) :
    spatialConvection (-u) t x = spatialConvection u t x := by
  simpa using spatialConvection_const_smul (-1 : ℝ) u t x

/-- The convection term expands over subtraction into the two self-terms minus
the two mixed directional-derivative terms. -/
theorem spatialConvection_sub
    {u v : NSVelocityField} {t : NSTime} {x : NSSpace}
    (hu : DifferentiableAt ℝ (fun y : NSSpace => u t y) x)
    (hv : DifferentiableAt ℝ (fun y : NSSpace => v t y) x) :
    spatialConvection (u - v) t x =
      spatialConvection u t x - spatialFDeriv u t x (v t x) -
        spatialFDeriv v t x (u t x) + spatialConvection v t x := by
  rw [sub_eq_add_neg]
  rw [spatialConvection_add hu hv.neg]
  rw [spatialConvection_neg]
  rw [show spatialFDeriv (-v) t x = (-1 : ℝ) • spatialFDeriv v t x by
    simpa using spatialFDeriv_const_smul (-1 : ℝ) v t x]
  simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

/-- The convection term of a linear combination expands into the two quadratic
self-terms plus the mixed directional-derivative terms. -/
theorem spatialConvection_linearCombination
    {u v : NSVelocityField} {t : NSTime} {x : NSSpace}
    (a b : ℝ)
    (hu : DifferentiableAt ℝ (fun y : NSSpace => u t y) x)
    (hv : DifferentiableAt ℝ (fun y : NSSpace => v t y) x) :
    spatialConvection (a • u + b • v) t x =
      (a ^ (2 : ℕ)) • spatialConvection u t x +
        (a * b) • spatialFDeriv u t x (v t x) +
        (a * b) • spatialFDeriv v t x (u t x) +
        (b ^ (2 : ℕ)) • spatialConvection v t x := by
  rw [spatialConvection_add (hu.const_smul a) (hv.const_smul b)]
  rw [spatialConvection_const_smul, spatialConvection_const_smul]
  simp [spatialFDeriv_const_smul, pow_two, smul_smul]
  ac_rfl

/-- The convection term of a constant velocity field is zero. -/
theorem spatialConvection_constantVelocityField
    (c : NSSpace) (t : NSTime) (x : NSSpace) :
    spatialConvection (constantVelocityField c) t x = 0 := by
  rw [spatialConvection, spatialFDeriv_constantVelocityField]
  simp

/-- Constant velocity fields satisfy the exact zero-pressure momentum identity
for every viscosity. -/
theorem momentumEquation_constantVelocityField_zeroPressure
    (ν : ℝ) (c : NSSpace) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (constantVelocityField c) t x +
        spatialConvection (constantVelocityField c) t x +
        spatialPressureGradient (0 : NSPressureField) t x =
      ν • spatialLaplacian (constantVelocityField c) t x := by
  rw [timeVelocityDerivative_constantVelocityField,
    spatialConvection_constantVelocityField,
    spatialPressureGradient_zero,
    spatialLaplacian_constantVelocityField]
  simp

/-- Constant velocity fields remain exact pointwise solutions after adding any
time-only pressure gauge, since such gauges have zero spatial gradient. -/
theorem momentumEquation_constantVelocityField_timeOnlyPressure
    (ν : ℝ) (c : NSSpace) (π : NSTime → ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (constantVelocityField c) t x +
        spatialConvection (constantVelocityField c) t x +
        spatialPressureGradient (fun s : NSTime => fun _ : NSSpace => π s) t x =
      ν • spatialLaplacian (constantVelocityField c) t x := by
  rw [timeVelocityDerivative_constantVelocityField,
    spatialConvection_constantVelocityField,
    spatialPressureGradient_timeOnly,
    spatialLaplacian_constantVelocityField]
  simp

/-- The zero velocity field is the degenerate constant-field baseline for the
exact zero-pressure momentum identity. -/
theorem momentumEquation_zeroVelocityField_zeroPressure
    (ν : ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (0 : NSVelocityField) t x +
        spatialConvection (0 : NSVelocityField) t x +
        spatialPressureGradient (0 : NSPressureField) t x =
      ν • spatialLaplacian (0 : NSVelocityField) t x := by
  simpa [constantVelocityField] using
    momentumEquation_constantVelocityField_zeroPressure ν (0 : NSSpace) t x

/-- The zero velocity field likewise remains an exact pointwise solution after
adding any time-only pressure gauge. -/
theorem momentumEquation_zeroVelocityField_timeOnlyPressure
    (ν : ℝ) (π : NSTime → ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (0 : NSVelocityField) t x +
        spatialConvection (0 : NSVelocityField) t x +
        spatialPressureGradient (fun s : NSTime => fun _ : NSSpace => π s) t x =
      ν • spatialLaplacian (0 : NSVelocityField) t x := by
  simpa [constantVelocityField] using
    momentumEquation_constantVelocityField_timeOnlyPressure ν (0 : NSSpace) π t x

/-- Pointwise momentum identities are stable under adding any extra pressure
field whose spatial gradient vanishes at the point in question. -/
theorem momentumEquation_addPressureOfZeroSpatialGradient
    {u : NSVelocityField} {p q : NSPressureField} {ν : ℝ} {t : NSTime} {x : NSSpace}
    (hp : DifferentiableAt ℝ (fun y : NSSpace => p t y) x)
    (hq : DifferentiableAt ℝ (fun y : NSSpace => q t y) x)
    (hq_zero : spatialPressureGradient q t x = 0)
    (h :
      timeVelocityDerivative u t x + spatialConvection u t x +
          spatialPressureGradient p t x =
        ν • spatialLaplacian u t x) :
    timeVelocityDerivative u t x + spatialConvection u t x +
        spatialPressureGradient (p + q) t x =
      ν • spatialLaplacian u t x := by
  rw [spatialPressureGradient_add hp hq, hq_zero, add_zero]
  exact h

/-- Pointwise momentum identities are in particular stable under adding an
arbitrary time-only pressure gauge. -/
theorem momentumEquation_addTimeOnlyPressure
    {u : NSVelocityField} {p : NSPressureField} {ν : ℝ} {t : NSTime} {x : NSSpace}
    (π : NSTime → ℝ)
    (hp : DifferentiableAt ℝ (fun y : NSSpace => p t y) x)
    (h :
      timeVelocityDerivative u t x + spatialConvection u t x +
          spatialPressureGradient p t x =
        ν • spatialLaplacian u t x) :
    timeVelocityDerivative u t x + spatialConvection u t x +
        spatialPressureGradient (p + fun s : NSTime => fun _ : NSSpace => π s) t x =
      ν • spatialLaplacian u t x := by
  have hq : DifferentiableAt ℝ (fun y : NSSpace => (fun _ : NSSpace => π t) y) x := by
    simp
  exact momentumEquation_addPressureOfZeroSpatialGradient hp hq
    (spatialPressureGradient_timeOnly π t x) h

/-- The steady linear shear field has zero convection term. -/
theorem spatialConvection_linearShearVelocityField
    (a : ℝ) (t : NSTime) (x : NSSpace) :
    spatialConvection (linearShearVelocityField a) t x = 0 := by
  rw [spatialConvection, spatialFDeriv_linearShearVelocityField, linearShearVelocityField,
    linearShearInitialVelocity_apply]
  ext i
  fin_cases i <;> simp [linearShearMap, nsCoord0, nsCoord1, ContinuousLinearMap.smulRight_apply]

/-- The steady field `u(t,x) = (a * x₁, 0, b)` has zero convection term. -/
theorem spatialConvection_linearShearVerticalDriftVelocityField
    (a b : ℝ) (t : NSTime) (x : NSSpace) :
    spatialConvection (linearShearVerticalDriftVelocityField a b) t x = 0 := by
  rw [linearShearVerticalDriftVelocityField]
  rw [spatialConvection_add
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_linearShearVelocityField a) t x)
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord2 b)) t x)]
  rw [spatialConvection_linearShearVelocityField,
    spatialConvection_constantVelocityField,
    spatialFDeriv_linearShearVelocityField,
    spatialFDeriv_constantVelocityField]
  have hmap : linearShearMap a (EuclideanSpace.single nsCoord2 b) = 0 := by
    ext i
    fin_cases i <;>
      simp [linearShearMap, nsCoord0, nsCoord1, nsCoord2,
        ContinuousLinearMap.smulRight_apply]
  simpa [hmap]

/-- The steady field `u(t,x) = (a * x₁, b, 0)` has constant convection term
`(a * b, 0, 0)`. -/
theorem spatialConvection_linearShearHorizontalDriftVelocityField
    (a b : ℝ) (t : NSTime) (x : NSSpace) :
    spatialConvection (linearShearHorizontalDriftVelocityField a b) t x =
      EuclideanSpace.single nsCoord0 (a * b) := by
  rw [linearShearHorizontalDriftVelocityField]
  rw [spatialConvection_add
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_linearShearVelocityField a) t x)
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord1 b)) t x)]
  rw [spatialConvection_linearShearVelocityField,
    spatialConvection_constantVelocityField,
    spatialFDeriv_linearShearVelocityField,
    spatialFDeriv_constantVelocityField]
  have hmap :
      linearShearMap a (EuclideanSpace.single nsCoord1 b) =
        EuclideanSpace.single nsCoord0 (a * b) := by
    ext i
    fin_cases i <;>
      simp [linearShearMap, nsCoord0, nsCoord1,
        ContinuousLinearMap.smulRight_apply, mul_comm]
  simpa [hmap]

/-- The steady field `u(t,x) = (a * x₁, b, c)` has the same constant
convection term `(a * b, 0, 0)` as the horizontal-drift branch. -/
theorem spatialConvection_linearShearFullDriftVelocityField
    (a b c : ℝ) (t : NSTime) (x : NSSpace) :
    spatialConvection (linearShearFullDriftVelocityField a b c) t x =
      EuclideanSpace.single nsCoord0 (a * b) := by
  rw [linearShearFullDriftVelocityField]
  rw [spatialConvection_add
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_linearShearHorizontalDriftVelocityField a b) t x)
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord2 c)) t x)]
  rw [spatialConvection_linearShearHorizontalDriftVelocityField,
    spatialConvection_constantVelocityField,
    spatialFDeriv_linearShearHorizontalDriftVelocityField,
    spatialFDeriv_constantVelocityField]
  have hmap : linearShearMap a (EuclideanSpace.single nsCoord2 c) = 0 := by
    ext i
    fin_cases i <;>
      simp [linearShearMap, nsCoord0, nsCoord1, nsCoord2,
        ContinuousLinearMap.smulRight_apply]
  simpa [hmap]

/-- The steady linear shear field satisfies the exact zero-pressure momentum
identity for every viscosity. -/
theorem momentumEquation_linearShearVelocityField_zeroPressure
    (ν a : ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (linearShearVelocityField a) t x +
        spatialConvection (linearShearVelocityField a) t x +
        spatialPressureGradient (0 : NSPressureField) t x =
      ν • spatialLaplacian (linearShearVelocityField a) t x := by
  rw [timeVelocityDerivative_linearShearVelocityField,
    spatialConvection_linearShearVelocityField,
    spatialPressureGradient_zero,
    spatialLaplacian_linearShearVelocityField]
  simp

/-- The steady field `u(t,x) = (a * x₁, 0, b)` satisfies the same exact
zero-pressure momentum identity for every viscosity. -/
theorem momentumEquation_linearShearVerticalDriftVelocityField_zeroPressure
    (ν a b : ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (linearShearVerticalDriftVelocityField a b) t x +
        spatialConvection (linearShearVerticalDriftVelocityField a b) t x +
        spatialPressureGradient (0 : NSPressureField) t x =
      ν • spatialLaplacian (linearShearVerticalDriftVelocityField a b) t x := by
  rw [timeVelocityDerivative_linearShearVerticalDriftVelocityField,
    spatialConvection_linearShearVerticalDriftVelocityField,
    spatialPressureGradient_zero,
    spatialLaplacian_linearShearVerticalDriftVelocityField]
  simp

/-- The steady field `u(t,x) = (a * x₁, b, 0)` satisfies the exact momentum
identity with compensating affine pressure `p(t,x) = -(a * b) * x₀`. -/
theorem momentumEquation_linearShearHorizontalDriftVelocityField
    (ν a b : ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (linearShearHorizontalDriftVelocityField a b) t x +
        spatialConvection (linearShearHorizontalDriftVelocityField a b) t x +
        spatialPressureGradient (linearShearHorizontalDriftPressureField a b) t x =
      ν • spatialLaplacian (linearShearHorizontalDriftVelocityField a b) t x := by
  rw [timeVelocityDerivative_linearShearHorizontalDriftVelocityField,
    spatialConvection_linearShearHorizontalDriftVelocityField,
    spatialPressureGradient_linearShearHorizontalDriftPressureField,
    spatialLaplacian_linearShearHorizontalDriftVelocityField]
  ext i
  fin_cases i <;>
    simp [nsCoord0]

/-- The steady field `u(t,x) = (a * x₁, b, c)` satisfies the same exact
momentum identity with affine pressure `p(t,x) = -(a * b) * x₀`. -/
theorem momentumEquation_linearShearFullDriftVelocityField
    (ν a b c : ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (linearShearFullDriftVelocityField a b c) t x +
        spatialConvection (linearShearFullDriftVelocityField a b c) t x +
        spatialPressureGradient (linearShearHorizontalDriftPressureField a b) t x =
      ν • spatialLaplacian (linearShearFullDriftVelocityField a b c) t x := by
  rw [timeVelocityDerivative_linearShearFullDriftVelocityField,
    spatialConvection_linearShearFullDriftVelocityField,
    spatialPressureGradient_linearShearHorizontalDriftPressureField,
    spatialLaplacian_linearShearFullDriftVelocityField]
  ext i
  fin_cases i <;>
    simp [nsCoord0]

/-- The damped sinusoidal heat-shear field has zero convection term. -/
theorem spatialConvection_heatShearVelocityField
    (ν a k : ℝ) (t : NSTime) (x : NSSpace) :
    spatialConvection (heatShearVelocityField ν a k) t x = 0 := by
  rw [spatialConvection, spatialFDeriv_heatShearVelocityField, heatShearVelocityField_apply]
  simp [coord0Embedding_apply, nsCoord0, nsCoord1, mul_assoc]

/-- The general time-amplitude shear ansatz has zero convection term: the
velocity is in the `x₀` direction and the profile is independent of `x₀`. -/
theorem spatialConvection_amplitudeShearVelocityField
    (A : NSTime → ℝ) (k : ℝ) (t : NSTime) (x : NSSpace) :
    spatialConvection (amplitudeShearVelocityField A k) t x = 0 := by
  have hslice :
      ∀ y : NSSpace,
        amplitudeShearVelocityField A k t y = heatShearVelocityField 0 (A t) k t y := by
    intro y
    simp [amplitudeShearVelocityField, heatShearVelocityField, heatShearScalar]
  rw [spatialConvection_congr_at hslice]
  simpa
    using spatialConvection_heatShearVelocityField 0 (A t) k t x

/-- The heat-shear family with streamwise drift also has zero convection term,
because the oscillatory part depends only on `x₁` while the added drift is in
the flow direction `x₀` and the field remains independent of `x₀`. -/
theorem spatialConvection_heatShearStreamwiseDriftVelocityField
    (ν a k d : ℝ) (t : NSTime) (x : NSSpace) :
    spatialConvection (heatShearStreamwiseDriftVelocityField ν a k d) t x = 0 := by
  rw [heatShearStreamwiseDriftVelocityField]
  rw [spatialConvection_add
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_heatShearVelocityField ν a k) t x)
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord0 d)) t x)]
  rw [spatialConvection_heatShearVelocityField,
    spatialConvection_constantVelocityField,
    spatialFDeriv_heatShearVelocityField,
    spatialFDeriv_constantVelocityField]
  ext i
  fin_cases i <;>
    simp [coord0Embedding_apply, constantVelocityField, nsCoord0, nsCoord1,
      mul_left_comm, mul_comm]

/-- The heat-shear family with vertical drift also has zero convection term,
because the oscillatory part depends only on `x₁` while the drift is purely in
the `x₂` direction. -/
theorem spatialConvection_heatShearVerticalDriftVelocityField
    (ν a k c : ℝ) (t : NSTime) (x : NSSpace) :
    spatialConvection (heatShearVerticalDriftVelocityField ν a k c) t x = 0 := by
  rw [heatShearVerticalDriftVelocityField]
  rw [spatialConvection_add
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_heatShearVelocityField ν a k) t x)
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord2 c)) t x)]
  rw [spatialConvection_heatShearVelocityField,
    spatialConvection_constantVelocityField,
    spatialFDeriv_heatShearVelocityField,
    spatialFDeriv_constantVelocityField]
  ext i
  fin_cases i <;>
    simp [coord0Embedding_apply, constantVelocityField, nsCoord0, nsCoord1, nsCoord2,
      mul_left_comm, mul_comm]

/-- The heat-shear family with full drift also has zero convection term,
because the oscillatory part depends only on `x₁` while both added drifts are
constant and point along directions of independence. -/
theorem spatialConvection_heatShearFullDriftVelocityField
    (ν a k d c : ℝ) (t : NSTime) (x : NSSpace) :
    spatialConvection (heatShearFullDriftVelocityField ν a k d c) t x = 0 := by
  rw [heatShearFullDriftVelocityField]
  rw [spatialConvection_add
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_heatShearStreamwiseDriftVelocityField ν a k d) t x)
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord2 c)) t x)]
  rw [spatialConvection_heatShearStreamwiseDriftVelocityField,
    spatialConvection_constantVelocityField,
    spatialFDeriv_heatShearStreamwiseDriftVelocityField,
    spatialFDeriv_constantVelocityField]
  ext i
  fin_cases i <;>
    simp [coord0Embedding_apply, constantVelocityField, nsCoord0, nsCoord1, nsCoord2,
      mul_left_comm, mul_comm]

/-- The damped sinusoidal heat-shear velocity field satisfies the exact
zero-pressure momentum identity. -/
theorem momentumEquation_heatShearVelocityField_zeroPressure
    (ν a k : ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (heatShearVelocityField ν a k) t x +
        spatialConvection (heatShearVelocityField ν a k) t x +
        spatialPressureGradient (0 : NSPressureField) t x =
      ν • spatialLaplacian (heatShearVelocityField ν a k) t x := by
  rw [timeVelocityDerivative_heatShearVelocityField,
    spatialConvection_heatShearVelocityField,
    spatialPressureGradient_zero,
    spatialLaplacian_heatShearVelocityField]
  ext i
  fin_cases i <;>
    simp [coord0Embedding_apply, nsCoord0, nsCoord1,
      mul_assoc, mul_left_comm, mul_comm]

/-- If a heat-shear field is evolved with viscosity `ν` but tested against a
momentum equation with viscosity `μ`, the required pressure residual is exactly
the viscosity mismatch times the heat profile. -/
theorem momentumPressureResidual_heatShearVelocityField
    (μ ν a k : ℝ) :
    momentumPressureResidual μ (heatShearVelocityField ν a k) =
      ((ν - μ) * k ^ (2 : ℕ)) • heatShearVelocityField ν a k := by
  funext t x
  ext i
  fin_cases i <;>
    simp [momentumPressureResidual, timeVelocityDerivative_heatShearVelocityField,
      spatialConvection_heatShearVelocityField, spatialLaplacian_heatShearVelocityField,
      heatShearVelocityField_apply, coord0Embedding_apply, nsCoord0, nsCoord1,
      mul_assoc, mul_left_comm, mul_comm]
  ring

/-- On a fixed time slice, the pressure residual of a general amplitude shear
is exactly the sine shear with amplitude equal to the scalar heat-ODE defect
`-(A' + μ k² A(t))`. -/
theorem momentumPressureResidual_amplitudeShearVelocityField_slice
    {A : NSTime → ℝ} {A' μ k : ℝ} {t : NSTime}
    (hA : HasDerivAt A A' t) :
    ∀ y : NSSpace,
      momentumPressureResidual μ (amplitudeShearVelocityField A k) t y =
        heatShearVelocityField 0 (-(A' + μ * k ^ (2 : ℕ) * A t)) k t y := by
  intro y
  ext i
  fin_cases i <;>
    simp [momentumPressureResidual,
      timeVelocityDerivative_amplitudeShearVelocityField hA,
      spatialConvection_amplitudeShearVelocityField,
      spatialLaplacian_amplitudeShearVelocityField,
      heatShearVelocityField_apply, coord0Embedding_apply, nsCoord0, nsCoord1,
      mul_left_comm, mul_comm]
  ring

/-- At unit viscosity, the undamped unit heat-shear profile leaves exactly the
negative profile as the pressure residual.  This is the minimal concrete
positive-viscosity mismatch: the velocity is smooth and divergence-free, but it
has not been given the heat decay required by the viscous term. -/
theorem momentumPressureResidual_undampedUnitHeatShearVelocityField :
    momentumPressureResidual 1 (heatShearVelocityField 0 1 1) =
      -heatShearVelocityField 0 1 1 := by
  funext t x
  ext i
  fin_cases i <;>
    simp [momentumPressureResidual, timeVelocityDerivative_heatShearVelocityField,
      spatialConvection_heatShearVelocityField, spatialLaplacian_heatShearVelocityField,
      heatShearVelocityField_apply, coord0Embedding_apply, nsCoord0, nsCoord1]

/-- The heat-shear family with streamwise drift satisfies the same exact
zero-pressure momentum identity. -/
theorem momentumEquation_heatShearStreamwiseDriftVelocityField_zeroPressure
    (ν a k d : ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (heatShearStreamwiseDriftVelocityField ν a k d) t x +
        spatialConvection (heatShearStreamwiseDriftVelocityField ν a k d) t x +
        spatialPressureGradient (0 : NSPressureField) t x =
      ν • spatialLaplacian (heatShearStreamwiseDriftVelocityField ν a k d) t x := by
  rw [timeVelocityDerivative_heatShearStreamwiseDriftVelocityField,
    spatialConvection_heatShearStreamwiseDriftVelocityField,
    spatialPressureGradient_zero,
    spatialLaplacian_heatShearStreamwiseDriftVelocityField]
  ext i
  fin_cases i <;>
    simp [coord0Embedding_apply, nsCoord0, nsCoord1,
      mul_assoc, mul_left_comm, mul_comm]

/-- The heat-shear family with vertical drift satisfies the same exact
zero-pressure momentum identity. -/
theorem momentumEquation_heatShearVerticalDriftVelocityField_zeroPressure
    (ν a k c : ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (heatShearVerticalDriftVelocityField ν a k c) t x +
        spatialConvection (heatShearVerticalDriftVelocityField ν a k c) t x +
        spatialPressureGradient (0 : NSPressureField) t x =
      ν • spatialLaplacian (heatShearVerticalDriftVelocityField ν a k c) t x := by
  rw [timeVelocityDerivative_heatShearVerticalDriftVelocityField,
    spatialConvection_heatShearVerticalDriftVelocityField,
    spatialPressureGradient_zero,
    spatialLaplacian_heatShearVerticalDriftVelocityField]
  ext i
  fin_cases i <;>
    simp [coord0Embedding_apply, nsCoord0, nsCoord1,
      mul_assoc, mul_left_comm, mul_comm]

/-- The heat-shear family with full drift satisfies the same exact
zero-pressure momentum identity. -/
theorem momentumEquation_heatShearFullDriftVelocityField_zeroPressure
    (ν a k d c : ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (heatShearFullDriftVelocityField ν a k d c) t x +
        spatialConvection (heatShearFullDriftVelocityField ν a k d c) t x +
        spatialPressureGradient (0 : NSPressureField) t x =
      ν • spatialLaplacian (heatShearFullDriftVelocityField ν a k d c) t x := by
  rw [timeVelocityDerivative_heatShearFullDriftVelocityField,
    spatialConvection_heatShearFullDriftVelocityField,
    spatialPressureGradient_zero,
    spatialLaplacian_heatShearFullDriftVelocityField]
  ext i
  fin_cases i <;>
    simp [coord0Embedding_apply, nsCoord0, nsCoord1,
      mul_assoc, mul_left_comm, mul_comm]

/-- Vorticity commutes with constant scalar multiplication. -/
theorem spatialVorticity_const_smul
    (a : ℝ) (u : NSVelocityField) (t : NSTime) (x : NSSpace) :
    spatialVorticity (a • u) t x = a • spatialVorticity u t x := by
  ext i
  fin_cases i <;>
    simp [spatialVorticity, spatialDerivativeComponent_const_smul, mul_sub]

/-- Vorticity commutes with addition. -/
theorem spatialVorticity_add
    {u v : NSVelocityField} {t : NSTime} {x : NSSpace}
    (hu : DifferentiableAt ℝ (fun y : NSSpace => u t y) x)
    (hv : DifferentiableAt ℝ (fun y : NSSpace => v t y) x) :
    spatialVorticity (u + v) t x = spatialVorticity u t x + spatialVorticity v t x := by
  ext i
  fin_cases i
  · simp [spatialVorticity, nsCoord0, nsCoord1, nsCoord2, EuclideanSpace.single_apply]
    have h12 :
        spatialDerivativeComponent (u + v) t x 1 2 =
          spatialDerivativeComponent u t x 1 2 + spatialDerivativeComponent v t x 1 2 := by
      simpa [nsCoord1, nsCoord2] using
        (spatialDerivativeComponent_add hu hv (coord := nsCoord1) (comp := nsCoord2))
    have h21 :
        spatialDerivativeComponent (u + v) t x 2 1 =
          spatialDerivativeComponent u t x 2 1 + spatialDerivativeComponent v t x 2 1 := by
      simpa [nsCoord1, nsCoord2] using
        (spatialDerivativeComponent_add hu hv (coord := nsCoord2) (comp := nsCoord1))
    rw [h12, h21]
    ring
  · simp [spatialVorticity, nsCoord0, nsCoord1, nsCoord2, EuclideanSpace.single_apply]
    have h20 :
        spatialDerivativeComponent (u + v) t x 2 0 =
          spatialDerivativeComponent u t x 2 0 + spatialDerivativeComponent v t x 2 0 := by
      simpa [nsCoord0, nsCoord2] using
        (spatialDerivativeComponent_add hu hv (coord := nsCoord2) (comp := nsCoord0))
    have h02 :
        spatialDerivativeComponent (u + v) t x 0 2 =
          spatialDerivativeComponent u t x 0 2 + spatialDerivativeComponent v t x 0 2 := by
      simpa [nsCoord0, nsCoord2] using
        (spatialDerivativeComponent_add hu hv (coord := nsCoord0) (comp := nsCoord2))
    rw [h20, h02]
    ring
  · simp [spatialVorticity, nsCoord0, nsCoord1, nsCoord2, EuclideanSpace.single_apply]
    have h01 :
        spatialDerivativeComponent (u + v) t x 0 1 =
          spatialDerivativeComponent u t x 0 1 + spatialDerivativeComponent v t x 0 1 := by
      simpa [nsCoord0, nsCoord1] using
        (spatialDerivativeComponent_add hu hv (coord := nsCoord0) (comp := nsCoord1))
    have h10 :
        spatialDerivativeComponent (u + v) t x 1 0 =
          spatialDerivativeComponent u t x 1 0 + spatialDerivativeComponent v t x 1 0 := by
      simpa [nsCoord0, nsCoord1] using
        (spatialDerivativeComponent_add hu hv (coord := nsCoord1) (comp := nsCoord0))
    rw [h01, h10]
    ring

/-- Vorticity is unchanged up to sign under velocity negation. -/
theorem spatialVorticity_neg
    (u : NSVelocityField) (t : NSTime) (x : NSSpace) :
    spatialVorticity (-u) t x = -spatialVorticity u t x := by
  simpa using spatialVorticity_const_smul (-1 : ℝ) u t x

/-- Vorticity commutes with subtraction. -/
theorem spatialVorticity_sub
    {u v : NSVelocityField} {t : NSTime} {x : NSSpace}
    (hu : DifferentiableAt ℝ (fun y : NSSpace => u t y) x)
    (hv : DifferentiableAt ℝ (fun y : NSSpace => v t y) x) :
    spatialVorticity (u - v) t x = spatialVorticity u t x - spatialVorticity v t x := by
  rw [sub_eq_add_neg]
  rw [spatialVorticity_add hu hv.neg]
  rw [spatialVorticity_neg]
  abel

/-- Vorticity commutes with linear combinations. -/
theorem spatialVorticity_linearCombination
    {u v : NSVelocityField} {t : NSTime} {x : NSSpace}
    (a b : ℝ)
    (hu : DifferentiableAt ℝ (fun y : NSSpace => u t y) x)
    (hv : DifferentiableAt ℝ (fun y : NSSpace => v t y) x) :
    spatialVorticity (a • u + b • v) t x =
      a • spatialVorticity u t x + b • spatialVorticity v t x := by
  rw [spatialVorticity_add (hu.const_smul a) (hv.const_smul b)]
  rw [spatialVorticity_const_smul, spatialVorticity_const_smul]

/-- The vorticity of the zero field is zero. -/
theorem spatialVorticity_zero (t : NSTime) (x : NSSpace) :
    spatialVorticity (0 : NSVelocityField) t x = 0 := by
  ext i
  fin_cases i <;> simp [spatialVorticity, spatialDerivativeComponent_zero]

/-- The vorticity of a constant velocity field is zero. -/
theorem spatialVorticity_constantVelocityField
    (c : NSSpace) (t : NSTime) (x : NSSpace) :
    spatialVorticity (constantVelocityField c) t x = 0 := by
  ext i
  fin_cases i <;>
    simp [spatialVorticity, spatialDerivativeComponent_constantVelocityField]

/-- The steady linear shear field has constant vorticity `(0, 0, -a)`. -/
theorem spatialVorticity_linearShearVelocityField
    (a : ℝ) (t : NSTime) (x : NSSpace) :
    spatialVorticity (linearShearVelocityField a) t x = EuclideanSpace.single nsCoord2 (-a) := by
  ext i
  fin_cases i
  · simp [spatialVorticity, spatialDerivativeComponent, spatialFDeriv_linearShearVelocityField,
      linearShearMap, nsCoord0, nsCoord1, nsCoord2, ContinuousLinearMap.smulRight_apply]
  · simp [spatialVorticity, spatialDerivativeComponent, spatialFDeriv_linearShearVelocityField,
      linearShearMap, nsCoord0, nsCoord1, nsCoord2, ContinuousLinearMap.smulRight_apply]
  · simp [spatialVorticity, spatialDerivativeComponent, spatialFDeriv_linearShearVelocityField,
      linearShearMap, nsCoord0, nsCoord1, nsCoord2, ContinuousLinearMap.smulRight_apply]

/-- The steady field `u(t,x) = (a * x₁, 0, b)` has the same constant vorticity
`(0, 0, -a)` as pure linear shear. -/
theorem spatialVorticity_linearShearVerticalDriftVelocityField
    (a b : ℝ) (t : NSTime) (x : NSSpace) :
    spatialVorticity (linearShearVerticalDriftVelocityField a b) t x =
      EuclideanSpace.single nsCoord2 (-a) := by
  rw [linearShearVerticalDriftVelocityField]
  rw [spatialVorticity_add
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_linearShearVelocityField a) t x)
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord2 b)) t x)]
  simp [spatialVorticity_linearShearVelocityField,
    spatialVorticity_constantVelocityField]

/-- The steady field `u(t,x) = (a * x₁, b, 0)` has the same constant vorticity
`(0, 0, -a)` as pure linear shear. -/
theorem spatialVorticity_linearShearHorizontalDriftVelocityField
    (a b : ℝ) (t : NSTime) (x : NSSpace) :
    spatialVorticity (linearShearHorizontalDriftVelocityField a b) t x =
      EuclideanSpace.single nsCoord2 (-a) := by
  rw [linearShearHorizontalDriftVelocityField]
  rw [spatialVorticity_add
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_linearShearVelocityField a) t x)
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
      (EuclideanSpace.single nsCoord1 b)) t x)]
  simp [spatialVorticity_linearShearVelocityField,
    spatialVorticity_constantVelocityField]

/-- The steady field `u(t,x) = (a * x₁, b, c)` has the same constant vorticity
`(0, 0, -a)` as pure linear shear. -/
theorem spatialVorticity_linearShearFullDriftVelocityField
    (a b c : ℝ) (t : NSTime) (x : NSSpace) :
    spatialVorticity (linearShearFullDriftVelocityField a b c) t x =
      EuclideanSpace.single nsCoord2 (-a) := by
  rw [linearShearFullDriftVelocityField]
  rw [spatialVorticity_add
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_linearShearHorizontalDriftVelocityField a b) t x)
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord2 c)) t x)]
  simp [spatialVorticity_linearShearHorizontalDriftVelocityField,
    spatialVorticity_constantVelocityField]

/-- The damped sinusoidal heat-shear field has vorticity in the third
component only. -/
theorem spatialVorticity_heatShearVelocityField
    (ν a k : ℝ) (t : NSTime) (x : NSSpace) :
    spatialVorticity (heatShearVelocityField ν a k) t x =
      EuclideanSpace.single nsCoord2
        (-(a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * Real.cos (k * x nsCoord1) * k)) := by
  ext i
  fin_cases i <;>
  simp [spatialVorticity, spatialDerivativeComponent, spatialFDeriv_heatShearVelocityField,
      coord0Embedding_apply, nsCoord0, nsCoord1, nsCoord2,
      mul_assoc, mul_left_comm, mul_comm]

/-- The general time-amplitude shear ansatz has the same vorticity formula as
heat shear, with the sampled amplitude `A t`. -/
theorem spatialVorticity_amplitudeShearVelocityField
    (A : NSTime → ℝ) (k : ℝ) (t : NSTime) (x : NSSpace) :
    spatialVorticity (amplitudeShearVelocityField A k) t x =
      EuclideanSpace.single nsCoord2
        (-(A t * Real.cos (k * x nsCoord1) * k)) := by
  have hslice :
      ∀ y : NSSpace,
        amplitudeShearVelocityField A k t y = heatShearVelocityField 0 (A t) k t y := by
    intro y
    simp [amplitudeShearVelocityField, heatShearVelocityField, heatShearScalar]
  rw [spatialVorticity_congr_at hslice]
  simpa [heatShearScalar]
    using spatialVorticity_heatShearVelocityField 0 (A t) k t x

/-- The wrong-viscosity pressure residual for heat shear has curl equal to the
same viscosity mismatch times the heat-shear vorticity. -/
theorem spatialVorticity_momentumPressureResidual_heatShearVelocityField
    (μ ν a k : ℝ) (t : NSTime) (x : NSSpace) :
    spatialVorticity (momentumPressureResidual μ (heatShearVelocityField ν a k)) t x =
      ((ν - μ) * k ^ (2 : ℕ)) •
        spatialVorticity (heatShearVelocityField ν a k) t x := by
  rw [momentumPressureResidual_heatShearVelocityField,
    spatialVorticity_const_smul]

/-- At the spacetime origin, the wrong-viscosity pressure residual has a
concrete nonzero curl component whenever the viscosity mismatch, amplitude, and
frequency are all nonzero. -/
theorem spatialVorticity_momentumPressureResidual_heatShearVelocityField_origin
    (μ ν a k : ℝ) :
    spatialVorticity (momentumPressureResidual μ (heatShearVelocityField ν a k)) 0 0 =
      EuclideanSpace.single nsCoord2 ((μ - ν) * a * k ^ (3 : ℕ)) := by
  rw [spatialVorticity_momentumPressureResidual_heatShearVelocityField,
    spatialVorticity_heatShearVelocityField]
  ext i
  fin_cases i <;>
    simp [nsCoord1, nsCoord2, mul_assoc, mul_left_comm, mul_comm]
  ring

/-- The wrong-viscosity heat-shear residual has nonzero curl at the origin under
the nondegeneracy assumptions `μ ≠ ν`, `a ≠ 0`, and `k ≠ 0`. -/
theorem spatialVorticity_momentumPressureResidual_heatShearVelocityField_origin_ne_zero
    {μ ν a k : ℝ} (hμν : μ ≠ ν) (ha : a ≠ 0) (hk : k ≠ 0) :
    spatialVorticity (momentumPressureResidual μ (heatShearVelocityField ν a k)) 0 0 ≠ 0 := by
  rw [spatialVorticity_momentumPressureResidual_heatShearVelocityField_origin]
  intro h
  have hcoord := congrArg (fun v : NSSpace => v nsCoord2) h
  have hprod : (μ - ν) * a * k ^ (3 : ℕ) = 0 := by
    simpa [nsCoord2] using hcoord
  exact
    (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hμν) ha)
      (pow_ne_zero (3 : ℕ) hk)) hprod

/-- No smooth pressure can repair a nondegenerate heat-shear profile into a
momentum equation at the wrong viscosity.  The obstruction is the curl of the
required pressure residual, so it is independent of any pressure ansatz. -/
theorem not_exists_smoothPressure_momentumEquation_heatShearVelocityField_wrongViscosity
    {μ ν a k : ℝ} (hμν : μ ≠ ν) (ha : a ≠ 0) (hk : k ≠ 0) :
    ¬ ∃ p : NSPressureField,
      smoothSpaceTimePressure p ∧
        ∀ t x,
          timeVelocityDerivative (heatShearVelocityField ν a k) t x +
              spatialConvection (heatShearVelocityField ν a k) t x +
              spatialPressureGradient p t x =
            μ • spatialLaplacian (heatShearVelocityField ν a k) t x := by
  exact
    not_exists_smoothPressure_momentumEquation_of_momentumPressureResidual_vorticity_ne_zero
      (ν := μ) (u := heatShearVelocityField ν a k)
      ⟨0, 0,
        spatialVorticity_momentumPressureResidual_heatShearVelocityField_origin_ne_zero
          hμν ha hk⟩

/-- If the scalar amplitude misses the heat ODE at a sampled time, then the
pressure residual of the general shear ansatz has a concrete nonzero curl
component at that time. -/
theorem spatialVorticity_momentumPressureResidual_amplitudeShearVelocityField_origin
    {A : NSTime → ℝ} {A' μ k : ℝ} {t : NSTime}
    (hA : HasDerivAt A A' t) :
    spatialVorticity (momentumPressureResidual μ (amplitudeShearVelocityField A k)) t 0 =
      EuclideanSpace.single nsCoord2 ((A' + μ * k ^ (2 : ℕ) * A t) * k) := by
  rw [spatialVorticity_congr_at
    (u := momentumPressureResidual μ (amplitudeShearVelocityField A k))
    (v := heatShearVelocityField 0 (-(A' + μ * k ^ (2 : ℕ) * A t)) k)
    (t := t) (x := 0)
    (momentumPressureResidual_amplitudeShearVelocityField_slice
      (A := A) (A' := A') (μ := μ) (k := k) (t := t) hA)]
  rw [spatialVorticity_heatShearVelocityField]
  ext i
  fin_cases i <;>
    simp [nsCoord1, nsCoord2, mul_left_comm, mul_comm]
  ring

/-- A nonzero sampled heat-ODE defect and nonzero wave number make the
general-amplitude pressure residual visibly non-gradient by curl. -/
theorem spatialVorticity_momentumPressureResidual_amplitudeShearVelocityField_origin_ne_zero
    {A : NSTime → ℝ} {A' μ k : ℝ} {t : NSTime}
    (hA : HasDerivAt A A' t)
    (hode : A' + μ * k ^ (2 : ℕ) * A t ≠ 0) (hk : k ≠ 0) :
    spatialVorticity (momentumPressureResidual μ (amplitudeShearVelocityField A k)) t 0 ≠ 0 := by
  rw [spatialVorticity_momentumPressureResidual_amplitudeShearVelocityField_origin hA]
  intro h
  have hcoord := congrArg (fun v : NSSpace => v nsCoord2) h
  have hprod : (A' + μ * k ^ (2 : ℕ) * A t) * k = 0 := by
    simpa [nsCoord2] using hcoord
  exact (mul_ne_zero hode hk) hprod

/-- No smooth pressure can repair a general time-amplitude shear ansatz at a
time where its scalar amplitude violates the heat ODE `A' + μ k² A = 0`.
The obstruction is the curl of the pressure residual, not a restriction to a
special pressure family. -/
theorem not_exists_smoothPressure_momentumEquation_amplitudeShearVelocityField_of_heatODE_mismatch_at
    {A : NSTime → ℝ} {A' μ k : ℝ} {t : NSTime}
    (hA : HasDerivAt A A' t)
    (hode : A' + μ * k ^ (2 : ℕ) * A t ≠ 0) (hk : k ≠ 0) :
    ¬ ∃ p : NSPressureField,
      smoothSpaceTimePressure p ∧
        ∀ s x,
          timeVelocityDerivative (amplitudeShearVelocityField A k) s x +
              spatialConvection (amplitudeShearVelocityField A k) s x +
              spatialPressureGradient p s x =
            μ • spatialLaplacian (amplitudeShearVelocityField A k) s x := by
  exact
    not_exists_smoothPressure_momentumEquation_of_momentumPressureResidual_vorticity_ne_zero
      (ν := μ) (u := amplitudeShearVelocityField A k)
      ⟨t, 0,
        spatialVorticity_momentumPressureResidual_amplitudeShearVelocityField_origin_ne_zero
          hA hode hk⟩

/-- The pressure residual of the undamped unit heat-shear profile has nonzero
curl at the origin, so it is not a smooth pressure gradient. -/
theorem spatialVorticity_momentumPressureResidual_undampedUnitHeatShearVelocityField_origin_ne_zero :
    spatialVorticity (momentumPressureResidual 1 (heatShearVelocityField 0 1 1)) 0 0 ≠ 0 := by
  rw [momentumPressureResidual_undampedUnitHeatShearVelocityField,
    spatialVorticity_neg, spatialVorticity_heatShearVelocityField]
  intro h
  have hcoord := congrArg (fun v : NSSpace => v nsCoord2) h
  simp [nsCoord2] at hcoord

/-- No smooth pressure can repair the undamped unit heat-shear profile into the
unit-viscosity momentum equation.  The obstruction is the nonzero curl of the
required pressure residual, not a restriction to a special pressure ansatz. -/
theorem not_exists_smoothPressure_momentumEquation_undampedUnitHeatShearVelocityField_unitViscosity :
    ¬ ∃ p : NSPressureField,
      smoothSpaceTimePressure p ∧
        ∀ t x,
          timeVelocityDerivative (heatShearVelocityField 0 1 1) t x +
              spatialConvection (heatShearVelocityField 0 1 1) t x +
              spatialPressureGradient p t x =
            (1 : ℝ) • spatialLaplacian (heatShearVelocityField 0 1 1) t x := by
  exact
    not_exists_smoothPressure_momentumEquation_of_momentumPressureResidual_vorticity_ne_zero
      (ν := 1) (u := heatShearVelocityField 0 1 1)
      ⟨0, 0,
        spatialVorticity_momentumPressureResidual_undampedUnitHeatShearVelocityField_origin_ne_zero⟩

/-- The heat-shear family with streamwise drift has the same vorticity as pure
heat shear. -/
theorem spatialVorticity_heatShearStreamwiseDriftVelocityField
    (ν a k d : ℝ) (t : NSTime) (x : NSSpace) :
    spatialVorticity (heatShearStreamwiseDriftVelocityField ν a k d) t x =
      EuclideanSpace.single nsCoord2
        (-(a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * Real.cos (k * x nsCoord1) * k)) := by
  rw [heatShearStreamwiseDriftVelocityField]
  rw [spatialVorticity_add
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_heatShearVelocityField ν a k) t x)
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord0 d)) t x)]
  simp [spatialVorticity_heatShearVelocityField,
    spatialVorticity_constantVelocityField]

/-- The heat-shear family with vertical drift has the same vorticity as pure
heat shear. -/
theorem spatialVorticity_heatShearVerticalDriftVelocityField
    (ν a k c : ℝ) (t : NSTime) (x : NSSpace) :
    spatialVorticity (heatShearVerticalDriftVelocityField ν a k c) t x =
      EuclideanSpace.single nsCoord2
        (-(a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * Real.cos (k * x nsCoord1) * k)) := by
  rw [heatShearVerticalDriftVelocityField]
  rw [spatialVorticity_add
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_heatShearVelocityField ν a k) t x)
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord2 c)) t x)]
  simp [spatialVorticity_heatShearVelocityField,
    spatialVorticity_constantVelocityField]

/-- The heat-shear family with full drift has the same vorticity as pure heat
shear. -/
theorem spatialVorticity_heatShearFullDriftVelocityField
    (ν a k d c : ℝ) (t : NSTime) (x : NSSpace) :
    spatialVorticity (heatShearFullDriftVelocityField ν a k d c) t x =
      EuclideanSpace.single nsCoord2
        (-(a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * Real.cos (k * x nsCoord1) * k)) := by
  rw [heatShearFullDriftVelocityField]
  rw [spatialVorticity_add
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_heatShearStreamwiseDriftVelocityField ν a k d) t x)
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord2 c)) t x)]
  simp [spatialVorticity_heatShearStreamwiseDriftVelocityField,
    spatialVorticity_constantVelocityField]

/-- Initial data `x ↦ (a * sin (k * x₁), b, 0)` for the transported
heat-shear branch. -/
theorem heatShearTransportInitialVelocity_apply
    (a k b : ℝ) (x : NSSpace) :
    heatShearTransportInitialVelocity a k b x =
      EuclideanSpace.single nsCoord0 (a * Real.sin (k * x nsCoord1)) +
        EuclideanSpace.single nsCoord1 b := by
  simp [heatShearTransportInitialVelocity, heatShearInitialVelocity,
    heatShearInitialScalar, constantInitialVelocity, coord0Embedding_apply]

/-- The transported heat-shear field has the explicit coordinate formula
`u(t,x) = (a * exp (-(ν * k²) * t) * sin (k * (x₁ - b * t)), b, 0)`. -/
theorem heatShearTransportVelocityField_apply
    (ν a k b : ℝ) (t : NSTime) (x : NSSpace) :
    heatShearTransportVelocityField ν a k b t x =
      EuclideanSpace.single nsCoord0
          (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * Real.sin (k * (x nsCoord1 - b * t))) +
        EuclideanSpace.single nsCoord1 b := by
  simp [heatShearTransportVelocityField, heatShearTransportScalar,
    constantVelocityField, coord0Embedding_apply, mul_assoc]

/-- The transported arbitrary-amplitude shear field has the explicit coordinate
formula `u(t,x) = (A t * sin (k * (x₁ - b * t)), b, 0)`. -/
theorem amplitudeShearTransportVelocityField_apply
    (A : NSTime → ℝ) (k b : ℝ) (t : NSTime) (x : NSSpace) :
    amplitudeShearTransportVelocityField A k b t x =
      EuclideanSpace.single nsCoord0 (A t * Real.sin (k * (x nsCoord1 - b * t))) +
        EuclideanSpace.single nsCoord1 b := by
  simp [amplitudeShearTransportVelocityField, constantVelocityField,
    coord0Embedding_apply]

/-- Initial data `x ↦ (d + a * sin (k * x₁), b, c)` for the transported
full-drift heat-shear branch. -/
theorem heatShearTransportFullDriftInitialVelocity_apply
    (a k b d c : ℝ) (x : NSSpace) :
    heatShearTransportFullDriftInitialVelocity a k b d c x =
      EuclideanSpace.single nsCoord0 (d + a * Real.sin (k * x nsCoord1)) +
        EuclideanSpace.single nsCoord1 b +
        EuclideanSpace.single nsCoord2 c := by
  ext i
  fin_cases i <;>
    simp [heatShearTransportFullDriftInitialVelocity, heatShearTransportInitialVelocity,
      heatShearInitialVelocity, heatShearInitialScalar, constantInitialVelocity,
      coord0Embedding_apply, nsCoord0, nsCoord1, nsCoord2, add_left_comm, add_comm]

/-- Vanishing transport speed reduces transported full-drift heat shear to the
non-transport full-drift subfamily. -/
theorem heatShearTransportFullDriftInitialVelocity_zero_transport
    (a k d c : ℝ) :
    heatShearTransportFullDriftInitialVelocity a k 0 d c =
      heatShearFullDriftInitialVelocity a k d c := by
  funext x
  ext i
  fin_cases i <;>
    simp [heatShearTransportFullDriftInitialVelocity_apply,
      heatShearFullDriftInitialVelocity_apply, nsCoord0, nsCoord1, nsCoord2]

/-- Vanishing extra streamwise and vertical drifts reduces transported
full-drift heat shear to the transported heat-shear subfamily. -/
theorem heatShearTransportFullDriftInitialVelocity_zero_drifts
    (a k b : ℝ) :
    heatShearTransportFullDriftInitialVelocity a k b 0 0 =
      heatShearTransportInitialVelocity a k b := by
  funext x
  ext i
  fin_cases i <;>
    simp [heatShearTransportFullDriftInitialVelocity_apply,
      heatShearTransportInitialVelocity_apply, nsCoord0, nsCoord1, nsCoord2]

/-- The transported full-drift heat-shear field has the explicit coordinate
formula
`u(t,x) = (d + a * exp (-(ν * k²) * t) * sin (k * (x₁ - b * t)), b, c)`. -/
theorem heatShearTransportFullDriftVelocityField_apply
    (ν a k b d c : ℝ) (t : NSTime) (x : NSSpace) :
    heatShearTransportFullDriftVelocityField ν a k b d c t x =
      EuclideanSpace.single nsCoord0
          (d + a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * Real.sin (k * (x nsCoord1 - b * t))) +
        EuclideanSpace.single nsCoord1 b +
        EuclideanSpace.single nsCoord2 c := by
  ext i
  fin_cases i <;>
    simp [heatShearTransportFullDriftVelocityField, heatShearTransportVelocityField,
      heatShearTransportScalar, constantVelocityField, coord0Embedding_apply,
      nsCoord0, nsCoord1, nsCoord2, add_left_comm, add_comm, mul_assoc]

/-- Initial velocity data `x ↦ (a * sin (k * x₁), b, 0)` are smooth on
`ℝ^3`. -/
theorem smoothInitialVelocityData_heatShearTransportInitialVelocity
    (a k b : ℝ) :
    smoothInitialVelocityData (heatShearTransportInitialVelocity a k b) := by
  simpa [heatShearTransportInitialVelocity] using
    (smoothInitialVelocityData_heatShearInitialVelocity a k).add
      (smoothInitialVelocityData_constantInitialVelocity
        (EuclideanSpace.single nsCoord1 b))

/-- The transported heat-shear field is smooth on `ℝ × ℝ^3`. -/
theorem smoothSpaceTimeVelocity_heatShearTransportVelocityField
    (ν a k b : ℝ) :
    smoothSpaceTimeVelocity (heatShearTransportVelocityField ν a k b) := by
  have htime : ContDiff ℝ ∞
      (fun tx : NSSpacetime => Real.exp (-(ν * k ^ (2 : ℕ)) * tx.1)) := by
    simpa [smul_eq_mul, mul_assoc] using
      (Real.contDiff_exp.comp (contDiff_fst.const_smul (-(ν * k ^ (2 : ℕ)))))
  have hphase : ContDiff ℝ ∞
      (fun tx : NSSpacetime => tx.2 nsCoord1 - b * tx.1) := by
    have hcoord : ContDiff ℝ ∞ (fun tx : NSSpacetime => tx.2 nsCoord1) := by
      simpa using
        (EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ).contDiff.comp contDiff_snd
    exact hcoord.sub (contDiff_fst.const_smul b)
  have hspace : ContDiff ℝ ∞
      (fun tx : NSSpacetime => Real.sin (k * (tx.2 nsCoord1 - b * tx.1))) := by
    simpa [smul_eq_mul, mul_assoc] using
      (Real.contDiff_sin.comp (hphase.const_smul k))
  have hscalar : ContDiff ℝ ∞ (fun tx : NSSpacetime =>
      a * Real.exp (-(ν * k ^ (2 : ℕ)) * tx.1) *
        Real.sin (k * (tx.2 nsCoord1 - b * tx.1))) := by
    simpa [smul_eq_mul, mul_assoc, mul_left_comm] using
      ((htime.mul hspace).const_smul a)
  have hosc :
      smoothSpaceTimeVelocity
        (fun t x => coord0Embedding (heatShearTransportScalar ν a k b t x)) := by
    simpa [smoothSpaceTimeVelocity, spaceTimeVelocityMap, heatShearTransportScalar, mul_assoc] using
      coord0Embedding.contDiff.comp hscalar
  simpa [heatShearTransportVelocityField] using
    hosc.add (smoothSpaceTimeVelocity_constantVelocityField
      (EuclideanSpace.single nsCoord1 b))

/-- Initial velocity data `x ↦ (d + a * sin (k * x₁), b, c)` are smooth on
`ℝ^3`. -/
theorem smoothInitialVelocityData_heatShearTransportFullDriftInitialVelocity
    (a k b d c : ℝ) :
    smoothInitialVelocityData (heatShearTransportFullDriftInitialVelocity a k b d c) := by
  simpa [heatShearTransportFullDriftInitialVelocity] using
    (smoothInitialVelocityData_heatShearTransportInitialVelocity a k b).add
      (smoothInitialVelocityData_constantInitialVelocity
        (EuclideanSpace.single nsCoord0 d + EuclideanSpace.single nsCoord2 c))

/-- The transported full-drift heat-shear field is smooth on `ℝ × ℝ^3`. -/
theorem smoothSpaceTimeVelocity_heatShearTransportFullDriftVelocityField
    (ν a k b d c : ℝ) :
    smoothSpaceTimeVelocity (heatShearTransportFullDriftVelocityField ν a k b d c) := by
  simpa [heatShearTransportFullDriftVelocityField] using
    (smoothSpaceTimeVelocity_heatShearTransportVelocityField ν a k b).add
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord0 d + EuclideanSpace.single nsCoord2 c))

/-- The transported heat-shear field has the expected spatial Fréchet
derivative in the first velocity component. -/
theorem spatialFDeriv_heatShearTransportVelocityField
    (ν a k b : ℝ) (t : NSTime) (x : NSSpace) :
    spatialFDeriv (heatShearTransportVelocityField ν a k b) t x =
      coord0Embedding.comp
        (((a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) : ℝ) •
          (Real.cos (k * (x nsCoord1 - b * t)) •
            ((k : ℝ) • (EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ))))) := by
  let A : ℝ := a * Real.exp (-(ν * k ^ (2 : ℕ)) * t)
  have hcoord : HasFDerivAt (fun y : NSSpace => k * (y nsCoord1 - b * t))
      ((k : ℝ) • (EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ)) x := by
    simpa [smul_eq_mul, sub_eq_add_neg, mul_assoc] using
      (((EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ).hasFDerivAt.sub_const (b * t)).const_smul k)
  have hsin : HasFDerivAt (fun y : NSSpace => Real.sin (k * (y nsCoord1 - b * t)))
      (Real.cos (k * (x nsCoord1 - b * t)) •
        ((k : ℝ) • (EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ))) x := by
    simpa using hcoord.sin
  have hscalar : HasFDerivAt
      (fun y : NSSpace => A * Real.sin (k * (y nsCoord1 - b * t)))
      ((A : ℝ) •
        (Real.cos (k * (x nsCoord1 - b * t)) •
          ((k : ℝ) • (EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ)))) x := by
    simpa [A, smul_eq_mul] using hsin.const_smul A
  have hvec : HasFDerivAt
      (fun y : NSSpace => coord0Embedding (A * Real.sin (k * (y nsCoord1 - b * t))))
      (coord0Embedding.comp
        ((A : ℝ) •
          (Real.cos (k * (x nsCoord1 - b * t)) •
            ((k : ℝ) • (EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ))))) x := by
    exact coord0Embedding.hasFDerivAt.comp x hscalar
  have hcore :
      spatialFDeriv
        (fun t x => coord0Embedding (heatShearTransportScalar ν a k b t x)) t x =
      coord0Embedding.comp
        (((a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) : ℝ) •
          (Real.cos (k * (x nsCoord1 - b * t)) •
            ((k : ℝ) • (EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ))))) := by
    unfold spatialFDeriv
    simpa [heatShearTransportScalar, A, mul_assoc] using hvec.fderiv
  have hdiff :
      DifferentiableAt ℝ (fun y : NSSpace => coord0Embedding (heatShearTransportScalar ν a k b t y)) x := by
    simpa [heatShearTransportScalar, A, mul_assoc] using hvec.differentiableAt
  rw [heatShearTransportVelocityField]
  rw [spatialFDeriv_add
    hdiff
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord1 b)) t x)]
  simp [hcore, spatialFDeriv_constantVelocityField]

/-- The spatial Fréchet derivative of transported arbitrary-amplitude shear is
the transported heat-shear slice formula with sampled amplitude `A t`. -/
theorem spatialFDeriv_amplitudeShearTransportVelocityField
    (A : NSTime → ℝ) (k b : ℝ) (t : NSTime) (x : NSSpace) :
    spatialFDeriv (amplitudeShearTransportVelocityField A k b) t x =
      coord0Embedding.comp
        (((A t : ℝ) •
          (Real.cos (k * (x nsCoord1 - b * t)) •
            ((k : ℝ) • (EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ))))) := by
  have hslice :
      ∀ y : NSSpace,
        amplitudeShearTransportVelocityField A k b t y =
          heatShearTransportVelocityField 0 (A t) k b t y := by
    intro y
    simp [amplitudeShearTransportVelocityField, heatShearTransportVelocityField,
      heatShearTransportScalar, constantVelocityField]
  rw [spatialFDeriv_congr_at hslice]
  simpa [heatShearTransportScalar]
    using spatialFDeriv_heatShearTransportVelocityField 0 (A t) k b t x

/-- The transported heat-shear field has the expected advection-diffusion time
derivative. -/
theorem timeVelocityDerivative_heatShearTransportVelocityField
    (ν a k b : ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (heatShearTransportVelocityField ν a k b) t x =
      coord0Embedding
        (-(ν * k ^ (2 : ℕ)) *
            (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
              Real.sin (k * (x nsCoord1 - b * t))) -
          a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
            (b * k * Real.cos (k * (x nsCoord1 - b * t)))) := by
  let E : ℝ := Real.exp (-(ν * k ^ (2 : ℕ)) * t)
  let S : ℝ := Real.sin (k * (x nsCoord1 - b * t))
  let C : ℝ := Real.cos (k * (x nsCoord1 - b * t))
  have hexp : HasDerivAt
      (fun s : ℝ => Real.exp (-(ν * k ^ (2 : ℕ)) * s))
      (Real.exp (-(ν * k ^ (2 : ℕ)) * t) * (-(ν * k ^ (2 : ℕ)))) t := by
    simpa [smul_eq_mul, mul_assoc] using
      (((hasDerivAt_id' t).const_mul (-(ν * k ^ (2 : ℕ)))).exp)
  have hphase : HasDerivAt
      (fun s : ℝ => k * (x nsCoord1 - b * s))
      (-(b * k)) t := by
    have hbase : HasDerivAt (fun s : ℝ => x nsCoord1 - b * s) (-b) t := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (((hasDerivAt_id' t).const_mul b).const_sub (x nsCoord1))
    simpa [mul_comm, mul_left_comm, mul_assoc] using hbase.const_mul k
  have hsin : HasDerivAt
      (fun s : ℝ => Real.sin (k * (x nsCoord1 - b * s)))
      (Real.cos (k * (x nsCoord1 - b * t)) * (-(b * k))) t := by
    simpa using hphase.sin
  have hscalar : HasDerivAt
      (fun s : ℝ =>
        a * Real.exp (-(ν * k ^ (2 : ℕ)) * s) *
          Real.sin (k * (x nsCoord1 - b * s)))
      (-(ν * k ^ (2 : ℕ)) * (a * E * S) - a * E * (b * k * C)) t := by
    convert (hexp.mul hsin).const_mul a using 1
    · simp [mul_assoc]
    · simp [E, S, C, mul_assoc, mul_left_comm, mul_comm]
      ring
  have hvec := coord0Embedding.hasFDerivAt.comp t hscalar.hasFDerivAt
  have happly :=
    congrArg (fun L : ℝ →L[ℝ] NSSpace => L (1 : ℝ)) hvec.fderiv
  have hcore :
      timeVelocityDerivative
          (fun t x => coord0Embedding (heatShearTransportScalar ν a k b t x)) t x =
        coord0Embedding
          (-(ν * k ^ (2 : ℕ)) * (a * E * S) - a * E * (b * k * C)) := by
    simpa [timeVelocityDerivative, timeFDeriv, heatShearTransportScalar,
      E, S, C, ContinuousLinearMap.comp_apply, mul_assoc, mul_left_comm, mul_comm] using happly
  have htdiff :
      DifferentiableAt ℝ (fun s : ℝ => coord0Embedding (heatShearTransportScalar ν a k b s x)) t := by
    simpa [heatShearTransportScalar, mul_assoc] using hvec.differentiableAt
  rw [heatShearTransportVelocityField]
  rw [timeVelocityDerivative_add]
  · simpa [hcore, E, S, C] using timeVelocityDerivative_constantVelocityField
      (EuclideanSpace.single nsCoord1 b) t x
  · exact htdiff
  · dsimp [constantVelocityField]
    exact differentiableAt_const (EuclideanSpace.single nsCoord1 b : NSSpace)

/-- The time derivative of transported arbitrary-amplitude shear contains the
sampled amplitude derivative and the phase-transport term. -/
theorem timeVelocityDerivative_amplitudeShearTransportVelocityField
    {A : NSTime → ℝ} {A' : ℝ} {t : NSTime}
    (hA : HasDerivAt A A' t) (k b : ℝ) (x : NSSpace) :
    timeVelocityDerivative (amplitudeShearTransportVelocityField A k b) t x =
      coord0Embedding
        (A' * Real.sin (k * (x nsCoord1 - b * t)) -
          A t * (b * k * Real.cos (k * (x nsCoord1 - b * t)))) := by
  let S : ℝ := Real.sin (k * (x nsCoord1 - b * t))
  let C : ℝ := Real.cos (k * (x nsCoord1 - b * t))
  have hphase : HasDerivAt
      (fun s : ℝ => k * (x nsCoord1 - b * s))
      (-(b * k)) t := by
    have hbase : HasDerivAt (fun s : ℝ => x nsCoord1 - b * s) (-b) t := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (((hasDerivAt_id' t).const_mul b).const_sub (x nsCoord1))
    simpa [mul_comm, mul_left_comm, mul_assoc] using hbase.const_mul k
  have hsin : HasDerivAt
      (fun s : ℝ => Real.sin (k * (x nsCoord1 - b * s)))
      (C * (-(b * k))) t := by
    simpa [C] using hphase.sin
  have hscalar : HasDerivAt
      (fun s : ℝ => A s * Real.sin (k * (x nsCoord1 - b * s)))
      (A' * S - A t * (b * k * C)) t := by
    convert hA.mul hsin using 1
    simp [S, C, mul_assoc, mul_left_comm, mul_comm]
    ring
  have hvec := coord0Embedding.hasFDerivAt.comp t hscalar.hasFDerivAt
  have happly :=
    congrArg (fun L : ℝ →L[ℝ] NSSpace => L (1 : ℝ)) hvec.fderiv
  have hcore :
      timeVelocityDerivative
          (fun t x => coord0Embedding
            (A t * Real.sin (k * (x nsCoord1 - b * t)))) t x =
        coord0Embedding (A' * S - A t * (b * k * C)) := by
    simpa [timeVelocityDerivative, timeFDeriv, S, C,
      ContinuousLinearMap.comp_apply, mul_assoc, mul_left_comm, mul_comm] using happly
  have htdiff :
      DifferentiableAt ℝ
        (fun s : ℝ => coord0Embedding (A s * Real.sin (k * (x nsCoord1 - b * s)))) t := by
    simpa using hvec.differentiableAt
  rw [amplitudeShearTransportVelocityField]
  rw [timeVelocityDerivative_add]
  · simp [hcore, timeVelocityDerivative_constantVelocityField, S, C]
  · exact htdiff
  · dsimp [constantVelocityField]
    exact differentiableAt_const (EuclideanSpace.single nsCoord1 b : NSSpace)

/-- The transported full-drift heat-shear family has the same time derivative
as the transported branch without the additional constant drifts. -/
theorem timeVelocityDerivative_heatShearTransportFullDriftVelocityField
    (ν a k b d c : ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (heatShearTransportFullDriftVelocityField ν a k b d c) t x =
      coord0Embedding
        (-(ν * k ^ (2 : ℕ)) *
            (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
              Real.sin (k * (x nsCoord1 - b * t))) -
          a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
            (b * k * Real.cos (k * (x nsCoord1 - b * t)))) := by
  rw [heatShearTransportFullDriftVelocityField]
  rw [timeVelocityDerivative_add]
  · simp [timeVelocityDerivative_heatShearTransportVelocityField,
      timeVelocityDerivative_constantVelocityField]
  · exact smoothSpaceTimeVelocity_differentiableAt_timeSlice
      (smoothSpaceTimeVelocity_heatShearTransportVelocityField ν a k b) t x
  · dsimp [constantVelocityField]
    exact differentiableAt_const
      (EuclideanSpace.single nsCoord0 d + EuclideanSpace.single nsCoord2 c : NSSpace)

/-- The transported heat-shear field is divergence free. -/
theorem spatialDivergence_heatShearTransportVelocityField
    (ν a k b : ℝ) (t : NSTime) (x : NSSpace) :
    spatialDivergence (heatShearTransportVelocityField ν a k b) t x = 0 := by
  rw [spatialDivergence, spatialFDeriv_heatShearTransportVelocityField, Fin.sum_univ_three]
  simp [coord0Embedding_apply, nsCoord0, nsCoord1]

/-- Transported arbitrary-amplitude shear is divergence free on each time
slice. -/
theorem spatialDivergence_amplitudeShearTransportVelocityField
    (A : NSTime → ℝ) (k b : ℝ) (t : NSTime) (x : NSSpace) :
    spatialDivergence (amplitudeShearTransportVelocityField A k b) t x = 0 := by
  have hslice :
      ∀ y : NSSpace,
        amplitudeShearTransportVelocityField A k b t y =
          heatShearTransportVelocityField 0 (A t) k b t y := by
    intro y
    simp [amplitudeShearTransportVelocityField, heatShearTransportVelocityField,
      heatShearTransportScalar, constantVelocityField]
  rw [spatialDivergence_congr_at hslice]
  simpa using spatialDivergence_heatShearTransportVelocityField 0 (A t) k b t x

/-- The transported heat-shear initial datum is divergence free. -/
theorem initialSpatialDivergence_heatShearTransportInitialVelocity
    (a k b : ℝ) (x : NSSpace) :
    initialSpatialDivergence (heatShearTransportInitialVelocity a k b) x = 0 := by
  rw [heatShearTransportInitialVelocity]
  rw [initialSpatialDivergence_add]
  · simp [initialSpatialDivergence_heatShearInitialVelocity,
      initialSpatialDivergence_constantInitialVelocity]
  · exact ((smoothInitialVelocityData_heatShearInitialVelocity a k).contDiffAt
      (x := x)).differentiableAt (by simp)
  · exact ((smoothInitialVelocityData_constantInitialVelocity
      (EuclideanSpace.single nsCoord1 b)).contDiffAt (x := x)).differentiableAt (by simp)

/-- The transported full-drift heat-shear field is divergence free. -/
theorem spatialDivergence_heatShearTransportFullDriftVelocityField
    (ν a k b d c : ℝ) (t : NSTime) (x : NSSpace) :
    spatialDivergence (heatShearTransportFullDriftVelocityField ν a k b d c) t x = 0 := by
  rw [heatShearTransportFullDriftVelocityField]
  rw [spatialDivergence_add
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_heatShearTransportVelocityField ν a k b) t x)
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord0 d + EuclideanSpace.single nsCoord2 c)) t x)]
  simp [spatialDivergence_heatShearTransportVelocityField,
    spatialDivergence_constantVelocityField]

/-- The transported full-drift heat-shear initial datum is divergence free. -/
theorem initialSpatialDivergence_heatShearTransportFullDriftInitialVelocity
    (a k b d c : ℝ) (x : NSSpace) :
    initialSpatialDivergence (heatShearTransportFullDriftInitialVelocity a k b d c) x = 0 := by
  rw [heatShearTransportFullDriftInitialVelocity]
  rw [initialSpatialDivergence_add]
  · simp [initialSpatialDivergence_heatShearTransportInitialVelocity,
      initialSpatialDivergence_constantInitialVelocity]
  · exact ((smoothInitialVelocityData_heatShearTransportInitialVelocity a k b).contDiffAt
      (x := x)).differentiableAt (by simp)
  · exact ((smoothInitialVelocityData_constantInitialVelocity
      (EuclideanSpace.single nsCoord0 d + EuclideanSpace.single nsCoord2 c)).contDiffAt
        (x := x)).differentiableAt (by simp)

/-- The transported heat-shear field matches its declared initial data at time
`0`. -/
theorem matchesInitialVelocity_heatShearTransportVelocityField
    (ν a k b : ℝ) :
    MatchesInitialVelocity
      (heatShearTransportInitialVelocity a k b)
      (heatShearTransportVelocityField ν a k b) := by
  intro x
  simp [heatShearTransportVelocityField, heatShearTransportInitialVelocity,
    heatShearTransportScalar, heatShearInitialVelocity, heatShearInitialScalar,
    constantVelocityField, constantInitialVelocity, nsCoord1, mul_assoc]

/-- The transported full-drift heat-shear field matches its declared initial
data at time `0`. -/
theorem matchesInitialVelocity_heatShearTransportFullDriftVelocityField
    (ν a k b d c : ℝ) :
    MatchesInitialVelocity
      (heatShearTransportFullDriftInitialVelocity a k b d c)
      (heatShearTransportFullDriftVelocityField ν a k b d c) := by
  intro x
  simp [heatShearTransportFullDriftVelocityField, heatShearTransportFullDriftInitialVelocity,
    heatShearTransportVelocityField, heatShearTransportInitialVelocity,
    heatShearTransportScalar, heatShearInitialVelocity, heatShearInitialScalar,
    constantVelocityField, constantInitialVelocity, nsCoord1, mul_assoc]

/-- The scalar Laplacian of the transported heat-shear profile is the expected
one-dimensional second derivative in the `x₁` direction. -/
theorem laplacian_heatShearTransportScalar
    (ν a k b : ℝ) (t : NSTime) (x : NSSpace) :
    Δ (fun y : NSSpace => heatShearTransportScalar ν a k b t y) x =
      -(k ^ (2 : ℕ)) *
        (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * Real.sin (k * (x nsCoord1 - b * t))) := by
  let A : ℝ := a * Real.exp (-(ν * k ^ (2 : ℕ)) * t)
  let g : ℝ → ℝ := fun s => A * Real.sin (k * (s - b * t))
  have hg : ContDiff ℝ 2 g := by
    simpa [g, A, smul_eq_mul, mul_assoc] using
      (Real.contDiff_sin.comp ((contDiff_id.sub contDiff_const).const_smul k)).const_smul A
  have hlapx :
      Δ (fun y : NSSpace => heatShearTransportScalar ν a k b t y) x =
        ∑ i : Fin 3,
          (iteratedFDeriv ℝ 2 (fun y : NSSpace => heatShearTransportScalar ν a k b t y) x)
            ![(EuclideanSpace.basisFun (Fin 3) ℝ) i, (EuclideanSpace.basisFun (Fin 3) ℝ) i] := by
    simpa using congrArg (fun h : NSSpace → ℝ => h x)
      (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
        (f := fun y : NSSpace => heatShearTransportScalar ν a k b t y)
        (v := EuclideanSpace.basisFun (Fin 3) ℝ))
  rw [hlapx]
  rw [Fin.sum_univ_three]
  have hcoord :
      iteratedFDeriv ℝ 2 (fun y : NSSpace => heatShearTransportScalar ν a k b t y) x =
        (iteratedFDeriv ℝ 2 g (x nsCoord1)).compContinuousLinearMap
          (fun _ => (EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ)) := by
    simpa [heatShearTransportScalar, g, A, Function.comp, mul_assoc] using
      (ContinuousLinearMap.iteratedFDeriv_comp_right
        (EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ) hg x (i := 2) (by norm_num))
  rw [hcoord]
  have h0 :
      (fun i => (![(EuclideanSpace.single (0 : Fin 3) (1 : ℝ)),
        EuclideanSpace.single (0 : Fin 3) (1 : ℝ)] i).ofLp nsCoord1) = 0 := by
    funext i
    fin_cases i <;> simp [nsCoord1]
  have h1 :
      (fun i => (![(EuclideanSpace.single (1 : Fin 3) (1 : ℝ)),
        EuclideanSpace.single (1 : Fin 3) (1 : ℝ)] i).ofLp nsCoord1) = fun _ => (1 : ℝ) := by
    funext i
    fin_cases i <;> simp [nsCoord1]
  have h2 :
      (fun i => (![(EuclideanSpace.single (2 : Fin 3) (1 : ℝ)),
        EuclideanSpace.single (2 : Fin 3) (1 : ℝ)] i).ofLp nsCoord1) = 0 := by
    funext i
    fin_cases i <;> simp [nsCoord1]
  have hz0 :
      ((iteratedFDeriv ℝ 2 g (x nsCoord1)).compContinuousLinearMap
        (fun _ => (EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ)))
        ![(EuclideanSpace.basisFun (Fin 3) ℝ) 0, (EuclideanSpace.basisFun (Fin 3) ℝ) 0] = 0 := by
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    simp [EuclideanSpace.basisFun_apply]
    rw [h0]
    simp
  have h1eval :
      ((iteratedFDeriv ℝ 2 g (x nsCoord1)).compContinuousLinearMap
        (fun _ => (EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ)))
        ![(EuclideanSpace.basisFun (Fin 3) ℝ) 1, (EuclideanSpace.basisFun (Fin 3) ℝ) 1] =
        iteratedDeriv 2 g (x nsCoord1) := by
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    simp [EuclideanSpace.basisFun_apply]
    rw [h1]
    simp [iteratedDeriv_eq_iteratedFDeriv]
  have hz2 :
      ((iteratedFDeriv ℝ 2 g (x nsCoord1)).compContinuousLinearMap
        (fun _ => (EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ)))
        ![(EuclideanSpace.basisFun (Fin 3) ℝ) 2, (EuclideanSpace.basisFun (Fin 3) ℝ) 2] = 0 := by
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    simp [EuclideanSpace.basisFun_apply]
    rw [h2]
    simp
  have hshift :
      iteratedDeriv 2 (fun z : ℝ => Real.sin (k * (z - b * t))) (x nsCoord1) =
        iteratedDeriv 2 (fun z : ℝ => Real.sin (k * z)) (x nsCoord1 - b * t) := by
    simpa using congrArg (fun h : ℝ → ℝ => h (x nsCoord1))
      (iteratedDeriv_comp_sub_const (n := 2) (f := fun z : ℝ => Real.sin (k * z)) (s := b * t))
  have hsinBase :
      iteratedDeriv 2 Real.sin (k * (x nsCoord1 - b * t)) =
        -Real.sin (k * (x nsCoord1 - b * t)) := by
    have hs := congrArg (fun h : ℝ → ℝ => h (k * (x nsCoord1 - b * t)))
      (Real.iteratedDeriv_even_sin (n := 1))
    rw [pow_one, neg_one_mul] at hs
    exact hs
  have hsin2 :
      iteratedDeriv 2 (fun z : ℝ => Real.sin (k * z)) (x nsCoord1 - b * t) =
        -(k ^ (2 : ℕ)) * Real.sin (k * (x nsCoord1 - b * t)) := by
    have hcomp := congrArg (fun h : ℝ → ℝ => h (x nsCoord1 - b * t))
      (iteratedDeriv_comp_const_mul (n := 2) (f := Real.sin) Real.contDiff_sin k)
    have hcomp' :
        iteratedDeriv 2 (fun z : ℝ => Real.sin (k * z)) (x nsCoord1 - b * t) =
          k ^ (2 : ℕ) * iteratedDeriv 2 Real.sin (k * (x nsCoord1 - b * t)) := by
      simpa using hcomp
    rw [hsinBase] at hcomp'
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hcomp'
  have hsecond :
      iteratedDeriv 2 g (x nsCoord1) =
        -(k ^ (2 : ℕ)) *
          (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * Real.sin (k * (x nsCoord1 - b * t))) := by
    have hconst :
        iteratedDeriv 2 g (x nsCoord1) =
          A * iteratedDeriv 2 (fun z : ℝ => Real.sin (k * (z - b * t))) (x nsCoord1) := by
      simp [g, iteratedDeriv_const_mul_field]
    rw [hconst, hshift, hsin2]
    ring
  rw [hz0, h1eval, hz2, hsecond]
  simp

/-- The transported heat-shear velocity field has the expected advection-heat
Laplacian in the first velocity component. -/
theorem spatialLaplacian_heatShearTransportVelocityField
    (ν a k b : ℝ) (t : NSTime) (x : NSSpace) :
    spatialLaplacian (heatShearTransportVelocityField ν a k b) t x =
      coord0Embedding
        (-(k ^ (2 : ℕ)) *
          (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * Real.sin (k * (x nsCoord1 - b * t)))) := by
  let A : ℝ := a * Real.exp (-(ν * k ^ (2 : ℕ)) * t)
  let g : ℝ → ℝ := fun s => A * Real.sin (k * (s - b * t))
  have hg : ContDiff ℝ 2 g := by
    simpa [g, A, smul_eq_mul, mul_assoc] using
      (Real.contDiff_sin.comp ((contDiff_id.sub contDiff_const).const_smul k)).const_smul A
  have hscalar : ContDiffAt ℝ 2 (fun y : NSSpace => heatShearTransportScalar ν a k b t y) x := by
    have hcont : ContDiff ℝ 2 (fun y : NSSpace => heatShearTransportScalar ν a k b t y) := by
      simpa [heatShearTransportScalar, g, A, Function.comp, mul_assoc] using
        hg.comp ((EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ).contDiff)
    exact hcont.contDiffAt
  have hosc : ContDiffAt ℝ 2
      (fun y : NSSpace => coord0Embedding (heatShearTransportScalar ν a k b t y)) x := by
    have hcont : ContDiff ℝ 2
        (fun y : NSSpace => coord0Embedding (heatShearTransportScalar ν a k b t y)) := by
      simpa [heatShearTransportScalar, g, A, Function.comp, mul_assoc] using
        coord0Embedding.contDiff.comp
          (hg.comp ((EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ).contDiff))
    exact hcont.contDiffAt
  have hcore :
      spatialLaplacian (fun t x => coord0Embedding (heatShearTransportScalar ν a k b t x)) t x =
      coord0Embedding
        (-(k ^ (2 : ℕ)) *
          (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * Real.sin (k * (x nsCoord1 - b * t)))) := by
    unfold spatialLaplacian
    rw [show (fun y : NSSpace => coord0Embedding (heatShearTransportScalar ν a k b t y)) =
        coord0Embedding ∘ fun y : NSSpace => heatShearTransportScalar ν a k b t y by
        funext y
        rfl]
    rw [hscalar.laplacian_CLM_comp_left (l := coord0Embedding)]
    simp [laplacian_heatShearTransportScalar]
  rw [heatShearTransportVelocityField]
  rw [spatialLaplacian_add]
  · simp [hcore, spatialLaplacian_constantVelocityField]
  · exact hosc.of_le (by
      exact (show (2 : WithTop ℕ∞) ≤ 2 from le_rfl))
  · exact ((smoothSpaceTimeVelocity_contDiff_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord1 b)) t).contDiffAt
          (x := x)).of_le (by
            exact ENat.natCast_le_of_coe_top_le_withTop
              (N := (∞ : WithTop ℕ∞)) (by rfl) 2)

/-- The spatial Laplacian of transported arbitrary-amplitude shear is the
transported sine-mode Laplacian with sampled amplitude `A t`. -/
theorem spatialLaplacian_amplitudeShearTransportVelocityField
    (A : NSTime → ℝ) (k b : ℝ) (t : NSTime) (x : NSSpace) :
    spatialLaplacian (amplitudeShearTransportVelocityField A k b) t x =
      coord0Embedding
        (-(k ^ (2 : ℕ)) *
          (A t * Real.sin (k * (x nsCoord1 - b * t)))) := by
  have hslice :
      ∀ y : NSSpace,
        amplitudeShearTransportVelocityField A k b t y =
          heatShearTransportVelocityField 0 (A t) k b t y := by
    intro y
    simp [amplitudeShearTransportVelocityField, heatShearTransportVelocityField,
      heatShearTransportScalar, constantVelocityField]
  rw [spatialLaplacian_congr_at hslice]
  simpa [heatShearTransportScalar]
    using spatialLaplacian_heatShearTransportVelocityField 0 (A t) k b t x

/-- The transported full-drift heat-shear family has the same spatial
Laplacian as the transported branch without the additional constant drifts. -/
theorem spatialLaplacian_heatShearTransportFullDriftVelocityField
    (ν a k b d c : ℝ) (t : NSTime) (x : NSSpace) :
    spatialLaplacian (heatShearTransportFullDriftVelocityField ν a k b d c) t x =
      coord0Embedding
        (-(k ^ (2 : ℕ)) *
          (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * Real.sin (k * (x nsCoord1 - b * t)))) := by
  rw [heatShearTransportFullDriftVelocityField]
  rw [spatialLaplacian_add]
  · simp [spatialLaplacian_heatShearTransportVelocityField,
      spatialLaplacian_constantVelocityField]
  · exact ((smoothSpaceTimeVelocity_contDiff_spatialSlice
      (smoothSpaceTimeVelocity_heatShearTransportVelocityField ν a k b) t).contDiffAt
        (x := x)).of_le (by
          exact ENat.natCast_le_of_coe_top_le_withTop
            (N := (∞ : WithTop ℕ∞)) (by rfl) 2)
  · exact ((smoothSpaceTimeVelocity_contDiff_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord0 d + EuclideanSpace.single nsCoord2 c)) t).contDiffAt
          (x := x)).of_le (by
            exact ENat.natCast_le_of_coe_top_le_withTop
              (N := (∞ : WithTop ℕ∞)) (by rfl) 2)

/-- The transported heat-shear field has the exact convection term generated
by the constant transport speed `b` along `x₁`. -/
theorem spatialConvection_heatShearTransportVelocityField
    (ν a k b : ℝ) (t : NSTime) (x : NSSpace) :
    spatialConvection (heatShearTransportVelocityField ν a k b) t x =
      coord0Embedding
        (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
          (b * k * Real.cos (k * (x nsCoord1 - b * t)))) := by
  rw [spatialConvection, spatialFDeriv_heatShearTransportVelocityField,
    heatShearTransportVelocityField_apply]
  ext i
  fin_cases i <;>
    simp [coord0Embedding_apply, nsCoord0, nsCoord1,
      mul_assoc, mul_left_comm, mul_comm]

/-- Transported arbitrary-amplitude shear has the same transport convection
term as the transported heat-shear slice with sampled amplitude `A t`. -/
theorem spatialConvection_amplitudeShearTransportVelocityField
    (A : NSTime → ℝ) (k b : ℝ) (t : NSTime) (x : NSSpace) :
    spatialConvection (amplitudeShearTransportVelocityField A k b) t x =
      coord0Embedding
        (A t * (b * k * Real.cos (k * (x nsCoord1 - b * t)))) := by
  have hslice :
      ∀ y : NSSpace,
        amplitudeShearTransportVelocityField A k b t y =
          heatShearTransportVelocityField 0 (A t) k b t y := by
    intro y
    simp [amplitudeShearTransportVelocityField, heatShearTransportVelocityField,
      heatShearTransportScalar, constantVelocityField]
  rw [spatialConvection_congr_at hslice]
  simpa [heatShearTransportScalar, mul_assoc, mul_left_comm, mul_comm]
    using spatialConvection_heatShearTransportVelocityField 0 (A t) k b t x

/-- The transported full-drift heat-shear family has the same convection term
as the transported branch without the additional constant drifts, because the
added constant field has zero `x₁` component. -/
theorem spatialConvection_heatShearTransportFullDriftVelocityField
    (ν a k b d c : ℝ) (t : NSTime) (x : NSSpace) :
    spatialConvection (heatShearTransportFullDriftVelocityField ν a k b d c) t x =
      coord0Embedding
        (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
          (b * k * Real.cos (k * (x nsCoord1 - b * t)))) := by
  rw [heatShearTransportFullDriftVelocityField]
  rw [spatialConvection_add
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_heatShearTransportVelocityField ν a k b) t x)
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord0 d + EuclideanSpace.single nsCoord2 c)) t x)]
  rw [spatialConvection_heatShearTransportVelocityField,
    spatialConvection_constantVelocityField,
    spatialFDeriv_heatShearTransportVelocityField,
    spatialFDeriv_constantVelocityField]
  ext i
  fin_cases i <;>
    simp [coord0Embedding_apply, constantVelocityField, nsCoord0, nsCoord1, nsCoord2,
      mul_assoc, mul_left_comm, mul_comm]

/-- The transported heat-shear field satisfies the exact zero-pressure momentum
identity. -/
theorem momentumEquation_heatShearTransportVelocityField_zeroPressure
    (ν a k b : ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (heatShearTransportVelocityField ν a k b) t x +
        spatialConvection (heatShearTransportVelocityField ν a k b) t x +
        spatialPressureGradient (0 : NSPressureField) t x =
      ν • spatialLaplacian (heatShearTransportVelocityField ν a k b) t x := by
  rw [timeVelocityDerivative_heatShearTransportVelocityField,
    spatialConvection_heatShearTransportVelocityField,
    spatialPressureGradient_zero,
    spatialLaplacian_heatShearTransportVelocityField]
  ext i
  fin_cases i <;>
    simp [coord0Embedding_apply, nsCoord0, nsCoord1,
      mul_assoc, mul_left_comm, mul_comm]

/-- On a fixed time slice, the pressure residual of transported
arbitrary-amplitude shear is the transported sine profile with amplitude equal
to the scalar heat-ODE defect; the constant transport drift itself cancels out.
-/
theorem momentumPressureResidual_amplitudeShearTransportVelocityField_slice
    {A : NSTime → ℝ} {A' μ k b : ℝ} {t : NSTime}
    (hA : HasDerivAt A A' t) :
    ∀ y : NSSpace,
      momentumPressureResidual μ (amplitudeShearTransportVelocityField A k b) t y =
        heatShearTransportVelocityField 0 (-(A' + μ * k ^ (2 : ℕ) * A t)) k b t y -
          constantVelocityField (EuclideanSpace.single nsCoord1 b) t y := by
  intro y
  ext i
  fin_cases i <;>
    simp [momentumPressureResidual,
      timeVelocityDerivative_amplitudeShearTransportVelocityField hA,
      spatialConvection_amplitudeShearTransportVelocityField,
      spatialLaplacian_amplitudeShearTransportVelocityField,
      heatShearTransportVelocityField_apply, constantVelocityField,
      coord0Embedding_apply, nsCoord0, nsCoord1,
      mul_assoc, mul_left_comm, mul_comm]
  ring

/-- The transported full-drift heat-shear family satisfies the same exact
zero-pressure momentum identity. -/
theorem momentumEquation_heatShearTransportFullDriftVelocityField_zeroPressure
    (ν a k b d c : ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (heatShearTransportFullDriftVelocityField ν a k b d c) t x +
        spatialConvection (heatShearTransportFullDriftVelocityField ν a k b d c) t x +
        spatialPressureGradient (0 : NSPressureField) t x =
      ν • spatialLaplacian (heatShearTransportFullDriftVelocityField ν a k b d c) t x := by
  rw [timeVelocityDerivative_heatShearTransportFullDriftVelocityField,
    spatialConvection_heatShearTransportFullDriftVelocityField,
    spatialPressureGradient_zero,
    spatialLaplacian_heatShearTransportFullDriftVelocityField]
  ext i
  fin_cases i <;>
    simp [coord0Embedding_apply, nsCoord0, nsCoord1,
      mul_assoc, mul_left_comm, mul_comm]

/-- The transported heat-shear field has the same vorticity magnitude as pure
heat shear, but evaluated at the transported phase `x₁ - b * t`. -/
theorem spatialVorticity_heatShearTransportVelocityField
    (ν a k b : ℝ) (t : NSTime) (x : NSSpace) :
    spatialVorticity (heatShearTransportVelocityField ν a k b) t x =
      EuclideanSpace.single nsCoord2
        (-(a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
          Real.cos (k * (x nsCoord1 - b * t)) * k)) := by
  ext i
  fin_cases i <;>
  simp [spatialVorticity, spatialDerivativeComponent,
    spatialFDeriv_heatShearTransportVelocityField, coord0Embedding_apply,
    nsCoord0, nsCoord1, nsCoord2, mul_assoc, mul_left_comm, mul_comm]

/-- Transported arbitrary-amplitude shear has the transported heat-shear
vorticity formula with sampled amplitude `A t`. -/
theorem spatialVorticity_amplitudeShearTransportVelocityField
    (A : NSTime → ℝ) (k b : ℝ) (t : NSTime) (x : NSSpace) :
    spatialVorticity (amplitudeShearTransportVelocityField A k b) t x =
      EuclideanSpace.single nsCoord2
        (-(A t * Real.cos (k * (x nsCoord1 - b * t)) * k)) := by
  have hslice :
      ∀ y : NSSpace,
        amplitudeShearTransportVelocityField A k b t y =
          heatShearTransportVelocityField 0 (A t) k b t y := by
    intro y
    simp [amplitudeShearTransportVelocityField, heatShearTransportVelocityField,
      heatShearTransportScalar, constantVelocityField]
  rw [spatialVorticity_congr_at hslice]
  simpa [heatShearTransportScalar]
    using spatialVorticity_heatShearTransportVelocityField 0 (A t) k b t x

/-- At the phase-aligned point `x₁ = b * t`, a transported
arbitrary-amplitude shear residual has curl equal to the sampled scalar heat
ODE defect times `k`. -/
theorem spatialVorticity_momentumPressureResidual_amplitudeShearTransportVelocityField_phasePoint
    {A : NSTime → ℝ} {A' μ k b : ℝ} {t : NSTime}
    (hA : HasDerivAt A A' t) :
    spatialVorticity
        (momentumPressureResidual μ (amplitudeShearTransportVelocityField A k b))
        t (EuclideanSpace.single nsCoord1 (b * t)) =
      EuclideanSpace.single nsCoord2 ((A' + μ * k ^ (2 : ℕ) * A t) * k) := by
  let B : ℝ := -(A' + μ * k ^ (2 : ℕ) * A t)
  rw [spatialVorticity_congr_at
    (u := momentumPressureResidual μ (amplitudeShearTransportVelocityField A k b))
    (v := heatShearTransportVelocityField 0 B k b -
      constantVelocityField (EuclideanSpace.single nsCoord1 b))
    (t := t) (x := EuclideanSpace.single nsCoord1 (b * t))
    (by
      intro y
      simpa [B] using
        momentumPressureResidual_amplitudeShearTransportVelocityField_slice
          (A := A) (A' := A') (μ := μ) (k := k) (b := b) (t := t) hA y)]
  rw [spatialVorticity_sub
    (u := heatShearTransportVelocityField 0 B k b)
    (v := constantVelocityField (EuclideanSpace.single nsCoord1 b))
    (t := t) (x := EuclideanSpace.single nsCoord1 (b * t))]
  · rw [spatialVorticity_heatShearTransportVelocityField,
      spatialVorticity_constantVelocityField]
    ext i
    fin_cases i <;>
      simp [B, nsCoord1, nsCoord2, mul_left_comm, mul_comm]
    ring
  · exact smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_heatShearTransportVelocityField 0 B k b)
      t (EuclideanSpace.single nsCoord1 (b * t))
  · exact smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField (EuclideanSpace.single nsCoord1 b))
      t (EuclideanSpace.single nsCoord1 (b * t))

/-- A nonzero sampled heat-ODE defect and nonzero wave number make the
transported arbitrary-amplitude pressure residual non-gradient by curl. -/
theorem spatialVorticity_momentumPressureResidual_amplitudeShearTransportVelocityField_phasePoint_ne_zero
    {A : NSTime → ℝ} {A' μ k b : ℝ} {t : NSTime}
    (hA : HasDerivAt A A' t)
    (hode : A' + μ * k ^ (2 : ℕ) * A t ≠ 0) (hk : k ≠ 0) :
    spatialVorticity
        (momentumPressureResidual μ (amplitudeShearTransportVelocityField A k b))
        t (EuclideanSpace.single nsCoord1 (b * t)) ≠ 0 := by
  rw [spatialVorticity_momentumPressureResidual_amplitudeShearTransportVelocityField_phasePoint hA]
  intro h
  have hcoord := congrArg (fun v : NSSpace => v nsCoord2) h
  have hprod : (A' + μ * k ^ (2 : ℕ) * A t) * k = 0 := by
    simpa [nsCoord2] using hcoord
  exact (mul_ne_zero hode hk) hprod

/-- No smooth pressure can repair a transported arbitrary-amplitude shear ansatz
at a time where its scalar amplitude violates the heat ODE.  The constant
transport drift cancels with the phase transport term, leaving the same scalar
ODE burden as for pure shear. -/
theorem not_exists_smoothPressure_momentumEquation_amplitudeShearTransportVelocityField_of_heatODE_mismatch_at
    {A : NSTime → ℝ} {A' μ k b : ℝ} {t : NSTime}
    (hA : HasDerivAt A A' t)
    (hode : A' + μ * k ^ (2 : ℕ) * A t ≠ 0) (hk : k ≠ 0) :
    ¬ ∃ p : NSPressureField,
      smoothSpaceTimePressure p ∧
        ∀ s x,
          timeVelocityDerivative (amplitudeShearTransportVelocityField A k b) s x +
              spatialConvection (amplitudeShearTransportVelocityField A k b) s x +
              spatialPressureGradient p s x =
            μ • spatialLaplacian (amplitudeShearTransportVelocityField A k b) s x := by
  exact
    not_exists_smoothPressure_momentumEquation_of_momentumPressureResidual_vorticity_ne_zero
      (ν := μ) (u := amplitudeShearTransportVelocityField A k b)
      ⟨t, EuclideanSpace.single nsCoord1 (b * t),
        spatialVorticity_momentumPressureResidual_amplitudeShearTransportVelocityField_phasePoint_ne_zero
          hA hode hk⟩

/-- The transported full-drift heat-shear family has the same vorticity as the
transported branch without the additional constant drifts. -/
theorem spatialVorticity_heatShearTransportFullDriftVelocityField
    (ν a k b d c : ℝ) (t : NSTime) (x : NSSpace) :
    spatialVorticity (heatShearTransportFullDriftVelocityField ν a k b d c) t x =
      EuclideanSpace.single nsCoord2
        (-(a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
          Real.cos (k * (x nsCoord1 - b * t)) * k)) := by
  rw [heatShearTransportFullDriftVelocityField]
  rw [spatialVorticity_add
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_heatShearTransportVelocityField ν a k b) t x)
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord0 d + EuclideanSpace.single nsCoord2 c)) t x)]
  simp [spatialVorticity_heatShearTransportVelocityField,
    spatialVorticity_constantVelocityField]

/-- The steady linear shear field has vorticity norm exactly `|a|`. -/
theorem norm_spatialVorticity_linearShearVelocityField
    (a : ℝ) (t : NSTime) (x : NSSpace) :
    ‖spatialVorticity (linearShearVelocityField a) t x‖ = |a| := by
  rw [spatialVorticity_linearShearVelocityField]
  simp [EuclideanSpace.norm_single]

/-- Adding constant drifts to steady linear shear does not change the vorticity
norm. -/
theorem norm_spatialVorticity_linearShearFullDriftVelocityField
    (a b c : ℝ) (t : NSTime) (x : NSSpace) :
    ‖spatialVorticity (linearShearFullDriftVelocityField a b c) t x‖ = |a| := by
  rw [spatialVorticity_linearShearFullDriftVelocityField]
  simp [EuclideanSpace.norm_single]

/-- Exact pointwise vorticity norm for the damped sinusoidal heat-shear field. -/
theorem norm_spatialVorticity_heatShearVelocityField
    (ν a k : ℝ) (t : NSTime) (x : NSSpace) :
    ‖spatialVorticity (heatShearVelocityField ν a k) t x‖ =
      |a| * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
        |Real.cos (k * x nsCoord1)| * |k| := by
  rw [spatialVorticity_heatShearVelocityField]
  simp [EuclideanSpace.norm_single, mul_assoc, mul_left_comm, mul_comm]

/-- The heat-shear vorticity norm is bounded by its damped amplitude envelope,
uniformly in the oscillatory phase. -/
theorem norm_spatialVorticity_heatShearVelocityField_le_exp_abs
    (ν a k : ℝ) (t : NSTime) (x : NSSpace) :
    ‖spatialVorticity (heatShearVelocityField ν a k) t x‖ ≤
      |a| * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * |k| := by
  rw [norm_spatialVorticity_heatShearVelocityField]
  calc
    |a| * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
          |Real.cos (k * x nsCoord1)| * |k|
        ≤ |a| * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * 1 * |k| := by
          gcongr
          simpa using Real.abs_cos_le_one (k * x nsCoord1)
    _ = |a| * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * |k| := by
          ring

/-- Exact pointwise vorticity norm for transported heat shear.  The transport
speed only shifts the phase. -/
theorem norm_spatialVorticity_heatShearTransportVelocityField
    (ν a k b : ℝ) (t : NSTime) (x : NSSpace) :
    ‖spatialVorticity (heatShearTransportVelocityField ν a k b) t x‖ =
      |a| * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
        |Real.cos (k * (x nsCoord1 - b * t))| * |k| := by
  rw [spatialVorticity_heatShearTransportVelocityField]
  simp [EuclideanSpace.norm_single, mul_assoc, mul_left_comm, mul_comm]

/-- Transported heat-shear vorticity has the same damped amplitude envelope as
the untransported heat-shear field. -/
theorem norm_spatialVorticity_heatShearTransportVelocityField_le_exp_abs
    (ν a k b : ℝ) (t : NSTime) (x : NSSpace) :
    ‖spatialVorticity (heatShearTransportVelocityField ν a k b) t x‖ ≤
      |a| * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * |k| := by
  rw [norm_spatialVorticity_heatShearTransportVelocityField]
  calc
    |a| * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
          |Real.cos (k * (x nsCoord1 - b * t))| * |k|
        ≤ |a| * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * 1 * |k| := by
          gcongr
          simpa using Real.abs_cos_le_one (k * (x nsCoord1 - b * t))
    _ = |a| * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * |k| := by
          ring

/-- Exact pointwise vorticity norm for transported full-drift heat shear. -/
theorem norm_spatialVorticity_heatShearTransportFullDriftVelocityField
    (ν a k b d c : ℝ) (t : NSTime) (x : NSSpace) :
    ‖spatialVorticity (heatShearTransportFullDriftVelocityField ν a k b d c) t x‖ =
      |a| * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
        |Real.cos (k * (x nsCoord1 - b * t))| * |k| := by
  rw [spatialVorticity_heatShearTransportFullDriftVelocityField]
  simp [EuclideanSpace.norm_single, mul_assoc, mul_left_comm, mul_comm]

/-- Full-drift transported heat shear has the same damped vorticity envelope as
the drift-free transported branch. -/
theorem norm_spatialVorticity_heatShearTransportFullDriftVelocityField_le_exp_abs
    (ν a k b d c : ℝ) (t : NSTime) (x : NSSpace) :
    ‖spatialVorticity (heatShearTransportFullDriftVelocityField ν a k b d c) t x‖ ≤
      |a| * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * |k| := by
  rw [norm_spatialVorticity_heatShearTransportFullDriftVelocityField]
  calc
    |a| * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
          |Real.cos (k * (x nsCoord1 - b * t))| * |k|
        ≤ |a| * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * 1 * |k| := by
          gcongr
          simpa using Real.abs_cos_le_one (k * (x nsCoord1 - b * t))
    _ = |a| * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * |k| := by
          ring

end VectorCalculusR3

end NavierStokes
end FluidDynamics
end Mettapedia
