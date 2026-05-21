import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Energy Identity Reductions for Concrete Navier-Stokes

This file starts the Navier-Stokes energy-inequality lane on the concrete
`ℝ × ℝ^3` theorem surface.

At the current stage, two genuine analytic burdens are still separate from the
concrete PDE algebra:

* differentiating `t ↦ (1 / 2) ∫ |u(t,x)|² dx` through the spatial integral;
* the viscous integration-by-parts identity
  `∫ u(t,x) · Δu(t,x) dx = - ∫ ‖∇u(t,x)‖² dx`.

Instead of masking those steps, this file makes them explicit hypotheses and
proves the honest reduction from the Navier-Stokes momentum equation to the
energy dissipation identity. It also records the correction that the viscous
integration-by-parts identity naturally matches the sum of squared coordinate
derivatives, not the operator norm of the full spatial Fréchet derivative, and
checks the resulting interface on the concrete zero solution.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open MeasureTheory
open scoped ContDiff Laplacian RealInnerProductSpace LineDeriv SchwartzMap

/-- Index type of the canonical orthonormal basis of the concrete NS space
`ℝ^3`. -/
abbrev NSStdBasisIndex := Fin (Module.finrank ℝ NSSpace)

/-- Canonical orthonormal basis of the concrete NS space `ℝ^3`. -/
abbrev nsStdBasis : OrthonormalBasis NSStdBasisIndex ℝ NSSpace :=
  stdOrthonormalBasis ℝ NSSpace

/-- Spatial enstrophy density: squared norm of the spatial velocity derivative.
This is the concrete dissipation density used in the energy identity. -/
def enstrophyDensity (u : NSVelocityField) (t : NSTime) : NSSpace → ℝ :=
  fun x => ‖spatialFDeriv u t x‖ ^ (2 : ℕ)

/-- Total enstrophy of a time slice. -/
def enstrophyAt (u : NSVelocityField) (t : NSTime) : ℝ :=
  ∫ x, enstrophyDensity u t x ∂volume

/-- Coordinatewise enstrophy density using the standard orthonormal basis of
`ℝ^3`. This is the dissipation density that matches the Laplacian
integration-by-parts identity on Schwartz slices. -/
def coordinateEnstrophyDensity (u : NSVelocityField) (t : NSTime) : NSSpace → ℝ :=
  fun x =>
    ∑ i : NSStdBasisIndex,
      ‖spatialFDeriv u t x (nsStdBasis i)‖ ^ (2 : ℕ)

/-- Total coordinatewise enstrophy of a time slice. -/
def coordinateEnstrophyAt (u : NSVelocityField) (t : NSTime) : ℝ :=
  ∫ x, coordinateEnstrophyDensity u t x ∂volume

/-- Viscous energy dissipation rate `ν ∫ ‖∇u‖²`. -/
def energyDissipationRate (u : NSVelocityField) (ν : ℝ) (t : NSTime) : ℝ :=
  ν * enstrophyAt u t

/-- Corrected viscous energy dissipation rate
`ν ∫ Σᵢ |∂ᵢu|²`. This is the concrete rate matching the Laplacian
integration-by-parts identity on `ℝ^3`. -/
def coordinateEnergyDissipationRate (u : NSVelocityField) (ν : ℝ) (t : NSTime) : ℝ :=
  ν * coordinateEnstrophyAt u t

/-- The conventional `1 / 2`-normalized kinetic energy. -/
def normalizedKineticEnergy (u : NSVelocityField) (t : NSTime) : ℝ :=
  (1 / 2 : ℝ) * kineticEnergyAt u t

/-- Kinetic-energy density is pointwise nonnegative. -/
theorem kineticEnergyDensity_nonneg
    (u : NSVelocityField) (t : NSTime) (x : NSSpace) :
    0 ≤ kineticEnergyDensity u t x := by
  simp [kineticEnergyDensity]

/-- The unguarded spatial kinetic-energy integral is nonnegative.  This uses
mathlib's convention that the Bochner integral of a nonintegrable nonnegative
function is still `0`, so finite-energy statements still need an explicit
integrability guard. -/
theorem kineticEnergyAt_nonneg
    (u : NSVelocityField) (t : NSTime) :
    0 ≤ kineticEnergyAt u t := by
  rw [kineticEnergyAt]
  exact integral_nonneg_of_ae
    (Filter.Eventually.of_forall fun x => kineticEnergyDensity_nonneg u t x)

/-- Normalized kinetic energy is nonnegative. -/
theorem normalizedKineticEnergy_nonneg
    (u : NSVelocityField) (t : NSTime) :
    0 ≤ normalizedKineticEnergy u t := by
  exact mul_nonneg (by norm_num) (kineticEnergyAt_nonneg u t)

/-- Enstrophy density is pointwise nonnegative. -/
theorem enstrophyDensity_nonneg
    (u : NSVelocityField) (t : NSTime) (x : NSSpace) :
    0 ≤ enstrophyDensity u t x := by
  simp [enstrophyDensity]

/-- Coordinatewise enstrophy density is pointwise nonnegative. -/
theorem coordinateEnstrophyDensity_nonneg
    (u : NSVelocityField) (t : NSTime) (x : NSSpace) :
    0 ≤ coordinateEnstrophyDensity u t x := by
  unfold coordinateEnstrophyDensity
  exact Finset.sum_nonneg fun i _ => by positivity

/-- Total enstrophy is nonnegative on the unguarded integral surface. -/
theorem enstrophyAt_nonneg
    (u : NSVelocityField) (t : NSTime) :
    0 ≤ enstrophyAt u t := by
  rw [enstrophyAt]
  exact integral_nonneg_of_ae
    (Filter.Eventually.of_forall fun x => enstrophyDensity_nonneg u t x)

/-- Total coordinatewise enstrophy is nonnegative on the unguarded integral
surface. -/
theorem coordinateEnstrophyAt_nonneg
    (u : NSVelocityField) (t : NSTime) :
    0 ≤ coordinateEnstrophyAt u t := by
  rw [coordinateEnstrophyAt]
  exact integral_nonneg_of_ae
    (Filter.Eventually.of_forall fun x => coordinateEnstrophyDensity_nonneg u t x)

/-- Nonnegative viscosity gives nonnegative conventional dissipation rate. -/
theorem energyDissipationRate_nonneg
    (u : NSVelocityField) {ν : ℝ} (hν : 0 ≤ ν) (t : NSTime) :
    0 ≤ energyDissipationRate u ν t := by
  exact mul_nonneg hν (enstrophyAt_nonneg u t)

/-- Nonnegative viscosity gives nonnegative corrected coordinatewise
dissipation rate. -/
theorem coordinateEnergyDissipationRate_nonneg
    (u : NSVelocityField) {ν : ℝ} (hν : 0 ≤ ν) (t : NSTime) :
    0 ≤ coordinateEnergyDissipationRate u ν t := by
  exact mul_nonneg hν (coordinateEnstrophyAt_nonneg u t)

/-- The corrected energy identity has a nonpositive right-hand side for
nonnegative viscosity. -/
theorem neg_coordinateEnergyDissipationRate_nonpos
    (u : NSVelocityField) {ν : ℝ} (hν : 0 ≤ ν) (t : NSTime) :
    -(coordinateEnergyDissipationRate u ν t) ≤ 0 := by
  exact neg_nonpos.mpr (coordinateEnergyDissipationRate_nonneg u hν t)

/-- The space integrand `u · ∂ₜu` appearing in the energy identity. -/
def timeEnergyPairing (u : NSVelocityField) (t : NSTime) : NSSpace → ℝ :=
  fun x => ⟪u t x, timeVelocityDerivative u t x⟫

/-- The space integrand `u · (u · ∇)u` from the nonlinear transport term. -/
def convectionEnergyPairing (u : NSVelocityField) (t : NSTime) : NSSpace → ℝ :=
  fun x => ⟪u t x, spatialConvection u t x⟫

/-- The space integrand `u · ∇p` from the pressure term. -/
def pressureEnergyPairing
    (u : NSVelocityField) (p : NSPressureField) (t : NSTime) : NSSpace → ℝ :=
  fun x => ⟪u t x, spatialPressureGradient p t x⟫

/-- The pressure energy pairing is additive in the pressure field whenever both
spatial pressure slices are differentiable at every point of the time slice. -/
theorem pressureEnergyPairing_add
    (u : NSVelocityField) {p q : NSPressureField} (t : NSTime)
    (hp : ∀ x, DifferentiableAt ℝ (fun y : NSSpace => p t y) x)
    (hq : ∀ x, DifferentiableAt ℝ (fun y : NSSpace => q t y) x) :
    pressureEnergyPairing u (p + q) t =
      fun x : NSSpace => pressureEnergyPairing u p t x + pressureEnergyPairing u q t x := by
  funext x
  rw [pressureEnergyPairing, pressureEnergyPairing, pressureEnergyPairing]
  rw [spatialPressureGradient_add (p := p) (q := q) (hp x) (hq x)]
  simp [inner_add_right]

/-- The pressure energy pairing against zero pressure vanishes identically. -/
theorem pressureEnergyPairing_zero_right
    (u : NSVelocityField) (t : NSTime) :
    pressureEnergyPairing u (0 : NSPressureField) t = fun _ : NSSpace => 0 := by
  funext x
  simp [pressureEnergyPairing, spatialPressureGradient_zero]

/-- The pressure energy pairing against a time-only pressure gauge vanishes
identically. -/
theorem pressureEnergyPairing_timeOnly
    (u : NSVelocityField) (π : NSTime → ℝ) (t : NSTime) :
    pressureEnergyPairing u (fun s : NSTime => fun _ : NSSpace => π s) t =
      fun _ : NSSpace => 0 := by
  funext x
  simp [pressureEnergyPairing, spatialPressureGradient_timeOnly]

/-- Against the coordinate-linear pressure field `p(t,x) = c * x₀`, the
pressure energy pairing is exactly `c` times the `x₀`-component of the
velocity. -/
theorem pressureEnergyPairing_coord0Linear
    (u : NSVelocityField) (c : ℝ) (t : NSTime) :
    pressureEnergyPairing
        u (fun _ : NSTime => fun y : NSSpace => c * y nsCoord0) t =
      fun x : NSSpace => c * (u t x) nsCoord0 := by
  funext x
  rw [pressureEnergyPairing, spatialPressureGradient_coord0Linear]
  simp [EuclideanSpace.inner_single_right, nsCoord0]

/-- The pressure energy pairing against a linear pressure field
`p(t,x) = ⟪c, x⟫` is exactly `u · c`. -/
theorem pressureEnergyPairing_linear
    (u : NSVelocityField) (c : NSSpace) (t : NSTime) :
    pressureEnergyPairing u (fun _ : NSTime => fun y : NSSpace => ⟪c, y⟫) t =
      fun x : NSSpace => ⟪u t x, c⟫ := by
  funext x
  rw [pressureEnergyPairing]
  have hgrad :
      spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => ⟪c, y⟫) t x = c := by
    unfold spatialPressureGradient
    apply HasGradientAt.gradient
    rw [hasGradientAt_iff_hasFDerivAt]
    simpa [InnerProductSpace.toDual_apply_apply, real_inner_comm] using
      (((InnerProductSpace.toDual ℝ NSSpace) c)).hasFDerivAt
  rw [hgrad]

/-- The pressure energy pairing against an affine-in-space pressure gauge
`p(t,x) = ⟪c(t), x⟫ + π(t)` depends only on the linear part, hence is exactly
`u · c(t)`. -/
theorem pressureEnergyPairing_affine
    (u : NSVelocityField) (c : NSTime → NSSpace) (π : NSTime → ℝ) (t : NSTime) :
    pressureEnergyPairing u (fun s : NSTime => fun y : NSSpace => ⟪c s, y⟫ + π s) t =
      fun x : NSSpace => ⟪u t x, c t⟫ := by
  funext x
  rw [pressureEnergyPairing]
  have hgrad :
      spatialPressureGradient (fun s : NSTime => fun y : NSSpace => ⟪c s, y⟫ + π s) t x = c t := by
    unfold spatialPressureGradient
    apply HasGradientAt.gradient
    rw [hasGradientAt_iff_hasFDerivAt]
    simpa [InnerProductSpace.toDual_apply_apply, real_inner_comm] using
      ((((InnerProductSpace.toDual ℝ NSSpace) (c t))).hasFDerivAt).add_const (π t)
  rw [hgrad]

/-- Concrete coordinate expansion of the Euclidean inner product on the
Navier-Stokes space `ℝ^3`. -/
theorem real_inner_eq_coord_sum (u c : NSSpace) :
    ⟪u, c⟫ = u nsCoord0 * c nsCoord0 +
      (u nsCoord1 * c nsCoord1 + u nsCoord2 * c nsCoord2) := by
  calc
    ⟪u, c⟫ = ∑ i : Fin 3, u i * c i := by
      simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]
    _ = u nsCoord0 * c nsCoord0 +
          (u nsCoord1 * c nsCoord1 + u nsCoord2 * c nsCoord2) := by
      simpa [nsCoord0, nsCoord1, nsCoord2, add_assoc] using
        (Fin.sum_univ_three (f := fun i : Fin 3 => u i * c i))

/-- A divergence-free Schwartz time slice has zero spatial mean in its `x₀`
component. This is the precise slice lemma needed to close the first explicit
nontrivial pressure class `p(t,x)=c*x₀`. -/
theorem integral_coord0_zero_of_schwartzSlice_of_spatialDivergence_zero
    (u : NSVelocityField) (t : NSTime) (f : 𝓢(NSSpace, NSSpace))
    (hslice : ∀ x, u t x = f x)
    (hdiv : ∀ x, spatialDivergence u t x = 0) :
    ∫ x, (u t x) nsCoord0 ∂volume = 0 := by
  let coord : Fin 3 → 𝓢(NSSpace, ℝ) := fun i =>
    SchwartzMap.bilinLeftCLM
      (ContinuousLinearMap.apply ℝ ℝ)
      (g := fun _ : NSSpace => (EuclideanSpace.proj i : NSSpace →L[ℝ] ℝ))
      (by fun_prop) f
  let x0 : NSSpace → ℝ := fun x => x nsCoord0
  let e0 : NSSpace := EuclideanSpace.single nsCoord0 (1 : ℝ)
  let e1 : NSSpace := EuclideanSpace.single nsCoord1 (1 : ℝ)
  let e2 : NSSpace := EuclideanSpace.single nsCoord2 (1 : ℝ)
  have hsliceFun : (fun x : NSSpace => u t x) = (f : NSSpace → NSSpace) := funext hslice
  have hCoordEq (i : Fin 3) (x : NSSpace) : coord i x = (f x) i := by
    simp [coord, SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.apply_apply]
  have hCoordFDeriv (i j : Fin 3) (x : NSSpace) :
      fderiv ℝ (coord i) x (EuclideanSpace.single j (1 : ℝ)) =
        fderiv ℝ f x (EuclideanSpace.single j (1 : ℝ)) i := by
    have hproj :=
      congrArg
        (fun L : NSSpace →L[ℝ] ℝ => L (EuclideanSpace.single j (1 : ℝ)))
        (((EuclideanSpace.proj i : NSSpace →L[ℝ] ℝ).hasFDerivAt.comp x
          (f.hasFDerivAt x)).fderiv)
    simpa [coord, SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.apply_apply,
      ContinuousLinearMap.comp_apply] using hproj
  have hx0_hasFDeriv (x : NSSpace) :
      HasFDerivAt x0 (EuclideanSpace.proj nsCoord0 : NSSpace →L[ℝ] ℝ) x := by
    simpa [x0] using
      ((EuclideanSpace.proj nsCoord0 : NSSpace →L[ℝ] ℝ).hasFDerivAt (x := x))
  have hx0_diff : Differentiable ℝ x0 := by
    intro x
    exact (hx0_hasFDeriv x).differentiableAt
  have hIntWeighted (i : Fin 3) :
      Integrable (fun x : NSSpace => x0 x * coord i x) := by
    let weighted : 𝓢(NSSpace, ℝ) :=
      SchwartzMap.bilinLeftCLM
        (ContinuousLinearMap.mul ℝ ℝ)
        (g := (EuclideanSpace.proj nsCoord0 : NSSpace →L[ℝ] ℝ))
        (by fun_prop)
        (coord i)
    have hWeighted :
        (weighted : NSSpace → ℝ) = fun x : NSSpace => x0 x * coord i x := by
      funext x
      simp [weighted, x0, coord, SchwartzMap.bilinLeftCLM_apply]
      rw [mul_comm]
    rw [← hWeighted]
    exact weighted.integrable
  have hIntWeightedDeriv (i : Fin 3) (v : NSSpace) :
      Integrable (fun x : NSSpace => x0 x * fderiv ℝ (coord i) x v) := by
    have hEq :
        (fun x : NSSpace => x0 x * fderiv ℝ (coord i) x v) =
          fun x : NSSpace => x0 x * (∂_{v} (coord i)) x := by
      funext x
      rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    let weighted : 𝓢(NSSpace, ℝ) :=
      SchwartzMap.bilinLeftCLM
        (ContinuousLinearMap.mul ℝ ℝ)
        (g := (EuclideanSpace.proj nsCoord0 : NSSpace →L[ℝ] ℝ))
        (by fun_prop)
        (∂_{v} (coord i))
    have hWeighted :
        (weighted : NSSpace → ℝ) = fun x : NSSpace => x0 x * (∂_{v} (coord i)) x := by
      funext x
      simp [weighted, x0, coord, SchwartzMap.bilinLeftCLM_apply]
      rw [mul_comm]
    rw [hEq, ← hWeighted]
    exact weighted.integrable
  have hx0_e0 (x : NSSpace) : fderiv ℝ x0 x e0 = 1 := by
    rw [(hx0_hasFDeriv x).fderiv]
    simp [e0, nsCoord0]
  have hx0_e1 (x : NSSpace) : fderiv ℝ x0 x e1 = 0 := by
    rw [(hx0_hasFDeriv x).fderiv]
    simp [e1, nsCoord0, nsCoord1]
  have hx0_e2 (x : NSSpace) : fderiv ℝ x0 x e2 = 0 := by
    rw [(hx0_hasFDeriv x).fderiv]
    simp [e2, nsCoord0, nsCoord2]
  have hDivEq (x : NSSpace) :
      fderiv ℝ (coord nsCoord0) x e0 =
        -(fderiv ℝ (coord nsCoord1) x e1 + fderiv ℝ (coord nsCoord2) x e2) := by
    have hx : spatialDivergence u t x = 0 := hdiv x
    rw [spatialDivergence, spatialFDeriv, hsliceFun, Fin.sum_univ_three] at hx
    have hx' :
        fderiv ℝ (coord nsCoord0) x e0 +
            (fderiv ℝ (coord nsCoord1) x e1 + fderiv ℝ (coord nsCoord2) x e2) = 0 := by
      rw [hCoordFDeriv nsCoord0 nsCoord0 x, hCoordFDeriv nsCoord1 nsCoord1 x,
        hCoordFDeriv nsCoord2 nsCoord2 x]
      simpa [e0, e1, e2, add_assoc] using hx
    exact eq_neg_of_add_eq_zero_left hx'
  have hIBP0 :
      ∫ x, x0 x * fderiv ℝ (coord nsCoord0) x e0 ∂volume =
        - ∫ x, coord nsCoord0 x ∂volume := by
    have hIBP0raw :
        ∫ x, x0 x * fderiv ℝ (coord nsCoord0) x e0 ∂volume =
          - ∫ x, fderiv ℝ x0 x e0 * coord nsCoord0 x ∂volume := by
      exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
        (by
          have hEq :
              (fun x : NSSpace => fderiv ℝ x0 x e0 * coord nsCoord0 x) =
                fun x : NSSpace => coord nsCoord0 x := by
            funext x
            rw [hx0_e0 x]
            ring
          rw [hEq]
          exact (coord nsCoord0).integrable)
        (hIntWeightedDeriv nsCoord0 e0)
        (hIntWeighted nsCoord0)
        hx0_diff
        (fun x => (coord nsCoord0).differentiableAt)
    simpa [hx0_e0] using hIBP0raw
  have hIBP1 :
      ∫ x, x0 x * fderiv ℝ (coord nsCoord1) x e1 ∂volume = 0 := by
    have hIBP1raw :
        ∫ x, x0 x * fderiv ℝ (coord nsCoord1) x e1 ∂volume =
          - ∫ x, fderiv ℝ x0 x e1 * coord nsCoord1 x ∂volume := by
      exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
        (by
          have hEq :
              (fun x : NSSpace => fderiv ℝ x0 x e1 * coord nsCoord1 x) =
                fun _ : NSSpace => 0 := by
            funext x
            rw [hx0_e1 x]
            simp
          rw [hEq]
          exact integrable_zero NSSpace ℝ (volume : Measure NSSpace))
        (hIntWeightedDeriv nsCoord1 e1)
        (hIntWeighted nsCoord1)
        hx0_diff
        (fun x => (coord nsCoord1).differentiableAt)
    simpa [hx0_e1] using hIBP1raw
  have hIBP2 :
      ∫ x, x0 x * fderiv ℝ (coord nsCoord2) x e2 ∂volume = 0 := by
    have hIBP2raw :
        ∫ x, x0 x * fderiv ℝ (coord nsCoord2) x e2 ∂volume =
          - ∫ x, fderiv ℝ x0 x e2 * coord nsCoord2 x ∂volume := by
      exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
        (by
          have hEq :
              (fun x : NSSpace => fderiv ℝ x0 x e2 * coord nsCoord2 x) =
                fun _ : NSSpace => 0 := by
            funext x
            rw [hx0_e2 x]
            simp
          rw [hEq]
          exact integrable_zero NSSpace ℝ (volume : Measure NSSpace))
        (hIntWeightedDeriv nsCoord2 e2)
        (hIntWeighted nsCoord2)
        hx0_diff
        (fun x => (coord nsCoord2).differentiableAt)
    simpa [hx0_e2] using hIBP2raw
  have hCoord0Eq :
      (fun x : NSSpace => (u t x) nsCoord0) = coord nsCoord0 := by
    funext x
    rw [hslice x]
    exact hCoordEq nsCoord0 x
  have hIBP0' :
      ∫ x, coord nsCoord0 x ∂volume =
        - ∫ x, x0 x * fderiv ℝ (coord nsCoord0) x e0 ∂volume := by
    have hneg := congrArg Neg.neg hIBP0
    simpa [neg_neg] using hneg.symm
  calc
    ∫ x, (u t x) nsCoord0 ∂volume = ∫ x, coord nsCoord0 x ∂volume := by
      rw [hCoord0Eq]
    _ = - ∫ x, x0 x * fderiv ℝ (coord nsCoord0) x e0 ∂volume := hIBP0'
    _ = ∫ x, -(x0 x * fderiv ℝ (coord nsCoord0) x e0) ∂volume := by
      rw [← integral_neg]
    _ = ∫ x, x0 x * (fderiv ℝ (coord nsCoord1) x e1 + fderiv ℝ (coord nsCoord2) x e2) ∂volume := by
      congr 1
      funext x
      rw [hDivEq x]
      ring
    _ = ∫ x, x0 x * fderiv ℝ (coord nsCoord1) x e1 ∂volume +
          ∫ x, x0 x * fderiv ℝ (coord nsCoord2) x e2 ∂volume := by
      have hSplit :
          (fun x : NSSpace =>
            x0 x * (fderiv ℝ (coord nsCoord1) x e1 + fderiv ℝ (coord nsCoord2) x e2)) =
            (fun x : NSSpace => x0 x * fderiv ℝ (coord nsCoord1) x e1) +
              (fun x : NSSpace => x0 x * fderiv ℝ (coord nsCoord2) x e2) := by
        funext x
        simp [mul_add]
      rw [hSplit]
      simpa using
        integral_add
          (hIntWeightedDeriv nsCoord1 e1)
          (hIntWeightedDeriv nsCoord2 e2)
    _ = 0 := by rw [hIBP1, hIBP2]; ring

/-- A divergence-free Schwartz time slice has zero spatial mean in every
coordinate component. This is the correct pressure-side mean-zero theorem for
linear pressure classes on `ℝ^3`. -/
theorem integral_coord_zero_of_schwartzSlice_of_spatialDivergence_zero
    (u : NSVelocityField) (t : NSTime) (f : 𝓢(NSSpace, NSSpace))
    (hslice : ∀ x, u t x = f x)
    (hdiv : ∀ x, spatialDivergence u t x = 0)
    (k : Fin 3) :
    ∫ x, (u t x) k ∂volume = 0 := by
  let coord : Fin 3 → 𝓢(NSSpace, ℝ) := fun i =>
    SchwartzMap.bilinLeftCLM
      (ContinuousLinearMap.apply ℝ ℝ)
      (g := fun _ : NSSpace => (EuclideanSpace.proj i : NSSpace →L[ℝ] ℝ))
      (by fun_prop) f
  let xk : NSSpace → ℝ := fun x => x k
  let ek : NSSpace := EuclideanSpace.single k (1 : ℝ)
  let remainder : NSSpace → ℝ := fun x =>
    (Finset.univ.erase k).sum
      (fun i => fderiv ℝ (coord i) x (EuclideanSpace.single i (1 : ℝ)))
  have hsliceFun : (fun x : NSSpace => u t x) = (f : NSSpace → NSSpace) := funext hslice
  have hCoordEq (i : Fin 3) (x : NSSpace) : coord i x = (f x) i := by
    simp [coord, SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.apply_apply]
  have hCoordFDeriv (i j : Fin 3) (x : NSSpace) :
      fderiv ℝ (coord i) x (EuclideanSpace.single j (1 : ℝ)) =
        fderiv ℝ f x (EuclideanSpace.single j (1 : ℝ)) i := by
    have hproj :=
      congrArg
        (fun L : NSSpace →L[ℝ] ℝ => L (EuclideanSpace.single j (1 : ℝ)))
        (((EuclideanSpace.proj i : NSSpace →L[ℝ] ℝ).hasFDerivAt.comp x
          (f.hasFDerivAt x)).fderiv)
    simpa [coord, SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.apply_apply,
      ContinuousLinearMap.comp_apply] using hproj
  have hxk_hasFDeriv (x : NSSpace) :
      HasFDerivAt xk (EuclideanSpace.proj k : NSSpace →L[ℝ] ℝ) x := by
    simpa [xk] using
      ((EuclideanSpace.proj k : NSSpace →L[ℝ] ℝ).hasFDerivAt (x := x))
  have hxk_diff : Differentiable ℝ xk := by
    intro x
    exact (hxk_hasFDeriv x).differentiableAt
  have hIntWeighted (i : Fin 3) :
      Integrable (fun x : NSSpace => xk x * coord i x) := by
    let weighted : 𝓢(NSSpace, ℝ) :=
      SchwartzMap.bilinLeftCLM
        (ContinuousLinearMap.mul ℝ ℝ)
        (g := (EuclideanSpace.proj k : NSSpace →L[ℝ] ℝ))
        (by fun_prop)
        (coord i)
    have hWeighted :
        (weighted : NSSpace → ℝ) = fun x : NSSpace => xk x * coord i x := by
      funext x
      simp [weighted, xk, coord, SchwartzMap.bilinLeftCLM_apply]
      rw [mul_comm]
    rw [← hWeighted]
    exact weighted.integrable
  have hIntWeightedDeriv (i : Fin 3) (v : NSSpace) :
      Integrable (fun x : NSSpace => xk x * fderiv ℝ (coord i) x v) := by
    have hEq :
        (fun x : NSSpace => xk x * fderiv ℝ (coord i) x v) =
          fun x : NSSpace => xk x * (∂_{v} (coord i)) x := by
      funext x
      rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    let weighted : 𝓢(NSSpace, ℝ) :=
      SchwartzMap.bilinLeftCLM
        (ContinuousLinearMap.mul ℝ ℝ)
        (g := (EuclideanSpace.proj k : NSSpace →L[ℝ] ℝ))
        (by fun_prop)
        (∂_{v} (coord i))
    have hWeighted :
        (weighted : NSSpace → ℝ) = fun x : NSSpace => xk x * (∂_{v} (coord i)) x := by
      funext x
      simp [weighted, xk, coord, SchwartzMap.bilinLeftCLM_apply]
      rw [mul_comm]
    rw [hEq, ← hWeighted]
    exact weighted.integrable
  have hxk_ek (x : NSSpace) : fderiv ℝ xk x ek = 1 := by
    rw [(hxk_hasFDeriv x).fderiv]
    simp [ek]
  have hxk_ei_zero (i : Fin 3) (hik : i ≠ k) (x : NSSpace) :
      fderiv ℝ xk x (EuclideanSpace.single i (1 : ℝ)) = 0 := by
    rw [(hxk_hasFDeriv x).fderiv]
    simpa [eq_comm] using hik
  have hDivEq (x : NSSpace) :
      fderiv ℝ (coord k) x ek = - remainder x := by
    have hx : spatialDivergence u t x = 0 := hdiv x
    rw [spatialDivergence, spatialFDeriv, hsliceFun] at hx
    have hx' :
        (∑ i : Fin 3, fderiv ℝ (coord i) x (EuclideanSpace.single i (1 : ℝ))) = 0 := by
      convert hx using 1
      refine Finset.sum_congr rfl ?_
      intro i hi
      exact hCoordFDeriv i i x
    have hsplit' :
        remainder x + fderiv ℝ (coord k) x ek = 0 := by
      have hsplit'' :
          (Finset.univ.erase k).sum
              (fun i => fderiv ℝ (coord i) x (EuclideanSpace.single i (1 : ℝ))) +
            fderiv ℝ (coord k) x (EuclideanSpace.single k (1 : ℝ)) = 0 := by
        rw [Finset.sum_erase_add (s := Finset.univ)
          (f := fun i : Fin 3 => fderiv ℝ (coord i) x (EuclideanSpace.single i (1 : ℝ)))
          (a := k) (by simp)]
        exact hx'
      simpa [remainder, ek] using hsplit''
    have hsplit :
        fderiv ℝ (coord k) x ek + remainder x = 0 := by
      simpa [add_comm] using hsplit'
    exact eq_neg_of_add_eq_zero_left hsplit
  have hIBPk :
      ∫ x, xk x * fderiv ℝ (coord k) x ek ∂volume =
        - ∫ x, coord k x ∂volume := by
    have hIBPkRaw :
        ∫ x, xk x * fderiv ℝ (coord k) x ek ∂volume =
          - ∫ x, fderiv ℝ xk x ek * coord k x ∂volume := by
      exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
        (by
          have hEq :
              (fun x : NSSpace => fderiv ℝ xk x ek * coord k x) =
                fun x : NSSpace => coord k x := by
            funext x
            rw [hxk_ek x]
            ring
          rw [hEq]
          exact (coord k).integrable)
        (hIntWeightedDeriv k ek)
        (hIntWeighted k)
        hxk_diff
        (fun x => (coord k).differentiableAt)
    simpa [hxk_ek] using hIBPkRaw
  have hIBPzero (i : Fin 3) (hik : i ≠ k) :
      ∫ x, xk x * fderiv ℝ (coord i) x (EuclideanSpace.single i (1 : ℝ)) ∂volume = 0 := by
    have hIBPRaw :
        ∫ x, xk x * fderiv ℝ (coord i) x (EuclideanSpace.single i (1 : ℝ)) ∂volume =
          - ∫ x, fderiv ℝ xk x (EuclideanSpace.single i (1 : ℝ)) * coord i x ∂volume := by
      exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
        (by
          have hEq :
              (fun x : NSSpace =>
                fderiv ℝ xk x (EuclideanSpace.single i (1 : ℝ)) * coord i x) =
                fun _ : NSSpace => 0 := by
            funext x
            rw [hxk_ei_zero i hik x]
            simp
          rw [hEq]
          exact integrable_zero NSSpace ℝ (volume : Measure NSSpace))
        (hIntWeightedDeriv i (EuclideanSpace.single i (1 : ℝ)))
        (hIntWeighted i)
        hxk_diff
        (fun x => (coord i).differentiableAt)
    simpa [hxk_ei_zero i hik] using hIBPRaw
  have hCoordkEq :
      (fun x : NSSpace => (u t x) k) = coord k := by
    funext x
    rw [hslice x]
    exact hCoordEq k x
  have hIBPk' :
      ∫ x, coord k x ∂volume =
        - ∫ x, xk x * fderiv ℝ (coord k) x ek ∂volume := by
    have hneg := congrArg Neg.neg hIBPk
    simpa [neg_neg] using hneg.symm
  calc
    ∫ x, (u t x) k ∂volume = ∫ x, coord k x ∂volume := by
      rw [hCoordkEq]
    _ = - ∫ x, xk x * fderiv ℝ (coord k) x ek ∂volume := hIBPk'
    _ = ∫ x, -(xk x * fderiv ℝ (coord k) x ek) ∂volume := by
      rw [← integral_neg]
    _ = ∫ x,
          xk x * remainder x ∂volume := by
      congr 1
      funext x
      rw [hDivEq x]
      ring
    _ = (Finset.univ.erase k).sum
          (fun i => ∫ x, xk x * fderiv ℝ (coord i) x (EuclideanSpace.single i (1 : ℝ)) ∂volume) := by
      have hSplit :
          (fun x : NSSpace => xk x * remainder x) =
            (fun x : NSSpace =>
              (Finset.univ.erase k).sum
                (fun i => xk x * fderiv ℝ (coord i) x (EuclideanSpace.single i (1 : ℝ)))) := by
        have hSplit' :
            (fun x : NSSpace =>
              xk x *
                (Finset.univ.erase k).sum
                  (fun i => fderiv ℝ (coord i) x (EuclideanSpace.single i (1 : ℝ)))) =
              (fun x : NSSpace =>
                (Finset.univ.erase k).sum
                  (fun i => xk x * fderiv ℝ (coord i) x (EuclideanSpace.single i (1 : ℝ)))) := by
          funext x
          rw [Finset.mul_sum]
        simpa [remainder] using hSplit'
      rw [hSplit, integral_finset_sum]
      intro i hi
      exact hIntWeightedDeriv i (EuclideanSpace.single i (1 : ℝ))
    _ = 0 := by
      refine Finset.sum_eq_zero ?_
      intro i hi
      exact hIBPzero i (Finset.mem_erase.mp hi).1

/-- A Schwartz time slice has integrable pressure energy pairing against the
linear pressure field `p(t,x) = ⟪c, x⟫`. -/
theorem integrable_pressureEnergyPairing_linear_of_schwartzSlice
    (u : NSVelocityField) (t : NSTime) (f : 𝓢(NSSpace, NSSpace))
    (c : NSSpace) (hslice : ∀ x, u t x = f x) :
    Integrable (pressureEnergyPairing u (fun _ : NSTime => fun y : NSSpace => ⟪c, y⟫) t) := by
  let coord : Fin 3 → 𝓢(NSSpace, ℝ) := fun i =>
    SchwartzMap.bilinLeftCLM
      (ContinuousLinearMap.apply ℝ ℝ)
      (g := fun _ : NSSpace => (EuclideanSpace.proj i : NSSpace →L[ℝ] ℝ))
      (by fun_prop) f
  have hCoordEq (i : Fin 3) (x : NSSpace) : coord i x = (f x) i := by
    simp [coord, SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.apply_apply]
  have hPair :
      pressureEnergyPairing u (fun _ : NSTime => fun y : NSSpace => ⟪c, y⟫) t =
        fun x : NSSpace =>
          coord nsCoord0 x * c nsCoord0 +
            (coord nsCoord1 x * c nsCoord1 + coord nsCoord2 x * c nsCoord2) := by
    funext x
    rw [pressureEnergyPairing_linear]
    change ⟪u t x, c⟫ =
      coord nsCoord0 x * c nsCoord0 +
        (coord nsCoord1 x * c nsCoord1 + coord nsCoord2 x * c nsCoord2)
    rw [hslice x, real_inner_eq_coord_sum]
    rw [hCoordEq nsCoord0 x, hCoordEq nsCoord1 x, hCoordEq nsCoord2 x]
  rw [hPair]
  have h0 : Integrable (fun x : NSSpace => coord nsCoord0 x * c nsCoord0) := by
    simpa [mul_comm] using (coord nsCoord0).integrable.const_mul (c nsCoord0)
  have h1 : Integrable (fun x : NSSpace => coord nsCoord1 x * c nsCoord1) := by
    simpa [mul_comm] using (coord nsCoord1).integrable.const_mul (c nsCoord1)
  have h2 : Integrable (fun x : NSSpace => coord nsCoord2 x * c nsCoord2) := by
    simpa [mul_comm] using (coord nsCoord2).integrable.const_mul (c nsCoord2)
  exact h0.add (h1.add h2)

/-- A divergence-free Schwartz time slice has vanishing pressure energy
integral against any linear pressure field `p(t,x) = ⟪c, x⟫`. -/
theorem integral_pressureEnergyPairing_linear_of_schwartzSlice_of_spatialDivergence_zero
    (u : NSVelocityField) (t : NSTime) (f : 𝓢(NSSpace, NSSpace))
    (c : NSSpace) (hslice : ∀ x, u t x = f x)
    (hdiv : ∀ x, spatialDivergence u t x = 0) :
    ∫ x, pressureEnergyPairing u (fun _ : NSTime => fun y : NSSpace => ⟪c, y⟫) t x ∂volume = 0 := by
  let coord : Fin 3 → 𝓢(NSSpace, ℝ) := fun i =>
    SchwartzMap.bilinLeftCLM
      (ContinuousLinearMap.apply ℝ ℝ)
      (g := fun _ : NSSpace => (EuclideanSpace.proj i : NSSpace →L[ℝ] ℝ))
      (by fun_prop) f
  have hCoordEq (i : Fin 3) (x : NSSpace) : coord i x = (f x) i := by
    simp [coord, SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.apply_apply]
  have hPair :
      pressureEnergyPairing u (fun _ : NSTime => fun y : NSSpace => ⟪c, y⟫) t =
        fun x : NSSpace =>
          coord nsCoord0 x * c nsCoord0 +
            (coord nsCoord1 x * c nsCoord1 + coord nsCoord2 x * c nsCoord2) := by
    funext x
    rw [pressureEnergyPairing_linear]
    change ⟪u t x, c⟫ =
      coord nsCoord0 x * c nsCoord0 +
        (coord nsCoord1 x * c nsCoord1 + coord nsCoord2 x * c nsCoord2)
    rw [hslice x, real_inner_eq_coord_sum]
    rw [hCoordEq nsCoord0 x, hCoordEq nsCoord1 x, hCoordEq nsCoord2 x]
  have h0 : Integrable (fun x : NSSpace => coord nsCoord0 x * c nsCoord0) := by
    simpa [mul_comm] using (coord nsCoord0).integrable.const_mul (c nsCoord0)
  have h1 : Integrable (fun x : NSSpace => coord nsCoord1 x * c nsCoord1) := by
    simpa [mul_comm] using (coord nsCoord1).integrable.const_mul (c nsCoord1)
  have h2 : Integrable (fun x : NSSpace => coord nsCoord2 x * c nsCoord2) := by
    simpa [mul_comm] using (coord nsCoord2).integrable.const_mul (c nsCoord2)
  have hCoordU (k : Fin 3) :
      (fun x : NSSpace => coord k x) = fun x : NSSpace => (u t x) k := by
    funext x
    rw [hCoordEq k x, ← hslice x]
  have hIntCoordZero (k : Fin 3) : ∫ x, coord k x ∂volume = 0 := by
    rw [hCoordU k]
    exact integral_coord_zero_of_schwartzSlice_of_spatialDivergence_zero
      (u := u) (t := t) (f := f) (hslice := hslice) (hdiv := hdiv) (k := k)
  have hAdd03 :
      ∫ x, coord nsCoord0 x * c nsCoord0 +
          ((coord nsCoord1 x * c nsCoord1) + coord nsCoord2 x * c nsCoord2) ∂volume =
        ∫ x, coord nsCoord0 x * c nsCoord0 ∂volume +
          ∫ x, (coord nsCoord1 x * c nsCoord1) + coord nsCoord2 x * c nsCoord2 ∂volume := by
    simpa using integral_add h0 (h1.add h2)
  have hAdd12 :
      ∫ x, (coord nsCoord1 x * c nsCoord1) + coord nsCoord2 x * c nsCoord2 ∂volume =
        ∫ x, coord nsCoord1 x * c nsCoord1 ∂volume +
          ∫ x, coord nsCoord2 x * c nsCoord2 ∂volume := by
    simpa using integral_add h1 h2
  have hConst0 :
      ∫ x, coord nsCoord0 x * c nsCoord0 ∂volume =
        c nsCoord0 * ∫ x, coord nsCoord0 x ∂volume := by
    simpa [mul_comm] using
      integral_const_mul (c nsCoord0) (fun x : NSSpace => coord nsCoord0 x)
  have hConst1 :
      ∫ x, coord nsCoord1 x * c nsCoord1 ∂volume =
        c nsCoord1 * ∫ x, coord nsCoord1 x ∂volume := by
    simpa [mul_comm] using
      integral_const_mul (c nsCoord1) (fun x : NSSpace => coord nsCoord1 x)
  have hConst2 :
      ∫ x, coord nsCoord2 x * c nsCoord2 ∂volume =
        c nsCoord2 * ∫ x, coord nsCoord2 x ∂volume := by
    simpa [mul_comm] using
      integral_const_mul (c nsCoord2) (fun x : NSSpace => coord nsCoord2 x)
  rw [hPair]
  calc
    ∫ x, coord nsCoord0 x * c nsCoord0 +
        ((coord nsCoord1 x * c nsCoord1) + coord nsCoord2 x * c nsCoord2) ∂volume =
      ∫ x, coord nsCoord0 x * c nsCoord0 ∂volume +
        (∫ x, coord nsCoord1 x * c nsCoord1 ∂volume +
          ∫ x, coord nsCoord2 x * c nsCoord2 ∂volume) := by
        rw [hAdd03, hAdd12]
    _ = c nsCoord0 * ∫ x, coord nsCoord0 x ∂volume +
        (c nsCoord1 * ∫ x, coord nsCoord1 x ∂volume +
          c nsCoord2 * ∫ x, coord nsCoord2 x ∂volume) := by
        rw [hConst0, hConst1, hConst2]
    _ = 0 := by
        rw [hIntCoordZero nsCoord0, hIntCoordZero nsCoord1, hIntCoordZero nsCoord2]
        simp

/-- A smooth time coefficient multiplying a Schwartz spatial profile gives a
smooth concrete space-time pressure field. -/
theorem smoothSpaceTimePressure_scalar_smul_schwartzPressure
    {ρ : NSTime → ℝ} (hρ : ContDiff ℝ ∞ ρ) (q : 𝓢(NSSpace, ℝ)) :
    smoothSpaceTimePressure (fun t : NSTime => fun x : NSSpace => ρ t * q x) := by
  have hρTime : ContDiff ℝ ∞ (fun tx : NSSpacetime => ρ tx.1) :=
    hρ.comp (contDiff_fst : ContDiff ℝ ∞ fun tx : NSSpacetime => tx.1)
  have hqSpace : ContDiff ℝ ∞ (fun tx : NSSpacetime => q tx.2) :=
    q.smooth'.comp (contDiff_snd : ContDiff ℝ ∞ fun tx : NSSpacetime => tx.2)
  simpa [smoothSpaceTimePressure, spaceTimePressureMap] using hρTime.mul hqSpace

/-- A smooth time-dependent affine spatial pressure profile
`p(t,x) = ⟪c(t), x⟫ + π(t)` is a smooth concrete space-time pressure field. -/
theorem smoothSpaceTimePressure_affinePressure
    {c : NSTime → NSSpace} {π : NSTime → ℝ}
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) :
    smoothSpaceTimePressure (fun t : NSTime => fun x : NSSpace => ⟪c t, x⟫ + π t) := by
  have hcTime : ContDiff ℝ ∞ (fun tx : NSSpacetime => c tx.1) :=
    hc.comp (contDiff_fst : ContDiff ℝ ∞ fun tx : NSSpacetime => tx.1)
  have hxSpace : ContDiff ℝ ∞ (fun tx : NSSpacetime => tx.2) :=
    contDiff_snd
  have hCoord (i : Fin 3) :
      ContDiff ℝ ∞ (fun tx : NSSpacetime => (c tx.1) i * tx.2 i) :=
    ((EuclideanSpace.proj i : NSSpace →L[ℝ] ℝ).contDiff.comp hcTime).mul
      ((EuclideanSpace.proj i : NSSpace →L[ℝ] ℝ).contDiff.comp hxSpace)
  have hInnerSum :
      ContDiff ℝ ∞ (fun tx : NSSpacetime => ∑ i : Fin 3, (c tx.1) i * tx.2 i) := by
    simpa using
      (ContDiff.sum (s := (Finset.univ : Finset (Fin 3)))
        (fun i _ => hCoord i))
  have hπTime : ContDiff ℝ ∞ (fun tx : NSSpacetime => π tx.1) :=
    hπ.comp (contDiff_fst : ContDiff ℝ ∞ fun tx : NSSpacetime => tx.1)
  simpa [smoothSpaceTimePressure, spaceTimePressureMap,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm] using
      hInnerSum.add hπTime

/-- Smooth affine pressures remain smooth after adding a smooth time
coefficient times a Schwartz spatial profile. -/
theorem smoothSpaceTimePressure_affine_add_scalar_smul_schwartzPressure
    {c : NSTime → NSSpace} {π ρ : NSTime → ℝ}
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ)
    (q : 𝓢(NSSpace, ℝ)) :
    smoothSpaceTimePressure
      ((fun t : NSTime => fun x : NSSpace => ⟪c t, x⟫ + π t) +
        fun t : NSTime => fun x : NSSpace => ρ t * q x) := by
  exact
    smoothSpaceTimePressure_add
      (smoothSpaceTimePressure_affinePressure hc hπ)
      (smoothSpaceTimePressure_scalar_smul_schwartzPressure hρ q)

/-- Against a scalar-multiple Schwartz pressure profile `p(t,x) = ρ(t) * q(x)`,
the pressure energy pairing is the coordinatewise velocity-pressure pairing with
the spatial derivatives of `q`. -/
theorem pressureEnergyPairing_scalar_smul_schwartzPressure
    (u : NSVelocityField) (ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ)) (t : NSTime) :
    pressureEnergyPairing u (fun s : NSTime => fun y : NSSpace => ρ s * q y) t =
      fun x : NSSpace =>
        ρ t *
          ∑ i : Fin 3,
            (u t x) i * (∂_{EuclideanSpace.single i (1 : ℝ)} q) x := by
  funext x
  have hdiff : DifferentiableAt ℝ (fun y : NSSpace => q y) x := q.differentiableAt
  have hgradq :
      HasGradientAt (fun y : NSSpace => q y) (gradient (fun y : NSSpace => q y) x) x :=
    hdiff.hasGradientAt
  have hgrad :
      spatialPressureGradient (fun s : NSTime => fun y : NSSpace => ρ s * q y) t x =
        (ρ t) • gradient (fun y : NSSpace => q y) x := by
    unfold spatialPressureGradient
    apply HasGradientAt.gradient
    rw [hasGradientAt_iff_hasFDerivAt]
    simpa [smul_eq_mul] using (hgradq.hasFDerivAt.const_mul (ρ t))
  have hGradCoord (i : Fin 3) :
      (gradient (fun y : NSSpace => q y) x) i =
        (∂_{EuclideanSpace.single i (1 : ℝ)} q) x := by
    have h :=
      hgradq.fderiv_apply (𝕜 := ℝ) (y := EuclideanSpace.single i (1 : ℝ))
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    simpa [EuclideanSpace.inner_single_right] using h.symm
  have hInnerRaw :
      ⟪u t x, gradient (fun y : NSSpace => q y) x⟫ =
        ∑ i : Fin 3, (u t x) i * (gradient (fun y : NSSpace => q y) x) i := by
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]
  have hInner :
      ⟪u t x, gradient (fun y : NSSpace => q y) x⟫ =
        ∑ i : Fin 3, (u t x) i * (∂_{EuclideanSpace.single i (1 : ℝ)} q) x := by
    rw [hInnerRaw]
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact congrArg (fun z : ℝ => (u t x) i * z) (hGradCoord i)
  rw [pressureEnergyPairing, hgrad, real_inner_smul_right, hInner]

/-- A Schwartz time slice has integrable pressure energy pairing against a
scalar-multiple Schwartz pressure profile `p(t,x) = ρ(t) * q(x)`. -/
theorem integrable_pressureEnergyPairing_of_schwartzSlice_scalarSchwartzPressure
    (u : NSVelocityField) (t : NSTime) (f : 𝓢(NSSpace, NSSpace))
    (ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (hslice : ∀ x, u t x = f x) :
    Integrable (pressureEnergyPairing u (fun s : NSTime => fun y : NSSpace => ρ s * q y) t) := by
  let coord : Fin 3 → 𝓢(NSSpace, ℝ) := fun i =>
    SchwartzMap.bilinLeftCLM
      (ContinuousLinearMap.apply ℝ ℝ)
      (g := fun _ : NSSpace => (EuclideanSpace.proj i : NSSpace →L[ℝ] ℝ))
      (by fun_prop) f
  have hCoordEq (i : Fin 3) (x : NSSpace) : coord i x = (f x) i := by
    simp [coord, SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.apply_apply]
  have hPair :
      pressureEnergyPairing u (fun s : NSTime => fun y : NSSpace => ρ s * q y) t =
        fun x : NSSpace =>
          ρ t *
            ∑ i : Fin 3,
              coord i x * (∂_{EuclideanSpace.single i (1 : ℝ)} q) x := by
    funext x
    rw [pressureEnergyPairing_scalar_smul_schwartzPressure]
    apply congrArg (fun z : ℝ => ρ t * z)
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [hslice x]
    simp [hCoordEq i x]
  have hTermIntegrable (i : Fin 3) :
      Integrable
        (fun x : NSSpace =>
          coord i x * (∂_{EuclideanSpace.single i (1 : ℝ)} q) x) := by
    simpa [coord, SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.apply_apply] using
      (SchwartzMap.pairing
        (ContinuousLinearMap.mul ℝ ℝ)
        (coord i)
        (∂_{EuclideanSpace.single i (1 : ℝ)} q)).integrable
  rw [hPair]
  have hSum :
      Integrable
        (fun x : NSSpace =>
          ∑ i : Fin 3, coord i x * (∂_{EuclideanSpace.single i (1 : ℝ)} q) x) := by
    simpa using
      integrable_finset_sum (Finset.univ : Finset (Fin 3)) (fun i _ => hTermIntegrable i)
  exact hSum.const_mul (ρ t)

/-- A divergence-free Schwartz velocity slice has vanishing pressure energy
integral against a scalar-multiple Schwartz pressure profile
`p(t,x) = ρ(t) * q(x)`. -/
theorem integral_pressureEnergyPairing_of_schwartzSlice_scalarSchwartzPressure_of_spatialDivergence_zero
    (u : NSVelocityField) (t : NSTime) (f : 𝓢(NSSpace, NSSpace))
    (ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (hslice : ∀ x, u t x = f x)
    (hdiv : ∀ x, spatialDivergence u t x = 0) :
    ∫ x, pressureEnergyPairing u (fun s : NSTime => fun y : NSSpace => ρ s * q y) t x ∂volume = 0 := by
  let coord : Fin 3 → 𝓢(NSSpace, ℝ) := fun i =>
    SchwartzMap.bilinLeftCLM
      (ContinuousLinearMap.apply ℝ ℝ)
      (g := fun _ : NSSpace => (EuclideanSpace.proj i : NSSpace →L[ℝ] ℝ))
      (by fun_prop) f
  have hsliceFun : (fun x : NSSpace => u t x) = (f : NSSpace → NSSpace) := funext hslice
  have hCoordEq (i : Fin 3) (x : NSSpace) : coord i x = (f x) i := by
    simp [coord, SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.apply_apply]
  have hCoordDeriv (i : Fin 3) (x : NSSpace) :
      (∂_{EuclideanSpace.single i (1 : ℝ)} (coord i)) x =
        (∂_{EuclideanSpace.single i (1 : ℝ)} f x) i := by
    have hproj :=
      congrArg
        (fun L : NSSpace →L[ℝ] ℝ => L (EuclideanSpace.single i (1 : ℝ)))
        (((EuclideanSpace.proj i : NSSpace →L[ℝ] ℝ).hasFDerivAt.comp x
          (f.hasFDerivAt x)).fderiv)
    simpa [coord, SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.apply_apply,
      ContinuousLinearMap.comp_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv] using hproj
  have hPair :
      pressureEnergyPairing u (fun s : NSTime => fun y : NSSpace => ρ s * q y) t =
        fun x : NSSpace =>
          ρ t *
            ∑ i : Fin 3,
              coord i x * (∂_{EuclideanSpace.single i (1 : ℝ)} q) x := by
    funext x
    rw [pressureEnergyPairing_scalar_smul_schwartzPressure]
    apply congrArg (fun z : ℝ => ρ t * z)
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [hslice x]
    simp [hCoordEq i x]
  have hTermIntegrable (i : Fin 3) :
      Integrable
        (fun x : NSSpace =>
          coord i x * (∂_{EuclideanSpace.single i (1 : ℝ)} q) x) := by
    simpa [coord, SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.apply_apply] using
      (SchwartzMap.pairing
        (ContinuousLinearMap.mul ℝ ℝ)
        (coord i)
        (∂_{EuclideanSpace.single i (1 : ℝ)} q)).integrable
  have hDivTermIntegrable (i : Fin 3) :
      Integrable
        (fun x : NSSpace =>
          (∂_{EuclideanSpace.single i (1 : ℝ)} (coord i)) x * q x) := by
    simpa [coord, SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.apply_apply] using
      (SchwartzMap.pairing
        (ContinuousLinearMap.mul ℝ ℝ)
        (∂_{EuclideanSpace.single i (1 : ℝ)} (coord i))
        q).integrable
  have hDivEq (x : NSSpace) :
      ∑ i : Fin 3, (∂_{EuclideanSpace.single i (1 : ℝ)} (coord i)) x = 0 := by
    have hx : spatialDivergence u t x = 0 := hdiv x
    rw [spatialDivergence, spatialFDeriv, hsliceFun] at hx
    convert hx using 1
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact hCoordDeriv i x
  rw [hPair]
  calc
    ∫ x, ρ t * ∑ i : Fin 3, coord i x * (∂_{EuclideanSpace.single i (1 : ℝ)} q) x ∂volume
        = ρ t *
            ∫ x, ∑ i : Fin 3, coord i x * (∂_{EuclideanSpace.single i (1 : ℝ)} q) x ∂volume := by
          rw [integral_const_mul]
    _ = ρ t *
          ∑ i : Fin 3,
            ∫ x, coord i x * (∂_{EuclideanSpace.single i (1 : ℝ)} q) x ∂volume := by
          congr 1
          rw [integral_finset_sum]
          intro i hi
          exact hTermIntegrable i
    _ = ρ t *
          ∑ i : Fin 3,
            (-∫ x, (∂_{EuclideanSpace.single i (1 : ℝ)} (coord i)) x * q x ∂volume) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [SchwartzMap.integral_mul_lineDerivOp_right_eq_neg_left
            (coord i) q (EuclideanSpace.single i (1 : ℝ))]
    _ = -(ρ t) *
          ∑ i : Fin 3,
            ∫ x, (∂_{EuclideanSpace.single i (1 : ℝ)} (coord i)) x * q x ∂volume := by
          rw [Finset.sum_neg_distrib]
          ring
    _ = -(ρ t) *
          ∫ x,
            ∑ i : Fin 3, (∂_{EuclideanSpace.single i (1 : ℝ)} (coord i)) x * q x ∂volume := by
          congr 2
          rw [integral_finset_sum]
          intro i hi
          exact hDivTermIntegrable i
    _ = -(ρ t) * ∫ x, (0 : ℝ) ∂volume := by
          congr 2
          funext x
          rw [← Finset.sum_mul, hDivEq x]
          simp
    _ = 0 := by simp

/-- If each fixed-time pressure slice is Schwartz, then the pressure energy
pairing has the expected coordinate expansion against the spatial derivatives
of that slice. -/
theorem pressureEnergyPairing_schwartzPressureSlice
    (u : NSVelocityField) (q : NSTime → 𝓢(NSSpace, ℝ)) (t : NSTime) :
    pressureEnergyPairing u (fun s : NSTime => fun y : NSSpace => q s y) t =
      fun x : NSSpace =>
        ∑ i : Fin 3, (u t x) i * (∂_{EuclideanSpace.single i (1 : ℝ)} (q t)) x := by
  funext x
  have hdiff : DifferentiableAt ℝ (fun y : NSSpace => q t y) x := (q t).differentiableAt
  have hgradq :
      HasGradientAt (fun y : NSSpace => q t y) (gradient (fun y : NSSpace => q t y) x) x :=
    hdiff.hasGradientAt
  have hgrad :
      spatialPressureGradient (fun s : NSTime => fun y : NSSpace => q s y) t x =
        gradient (fun y : NSSpace => q t y) x := by
    rfl
  have hGradCoord (i : Fin 3) :
      (gradient (fun y : NSSpace => q t y) x) i =
        (∂_{EuclideanSpace.single i (1 : ℝ)} (q t)) x := by
    have h :=
      hgradq.fderiv_apply (𝕜 := ℝ) (y := EuclideanSpace.single i (1 : ℝ))
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    simpa [EuclideanSpace.inner_single_right] using h.symm
  have hInnerRaw :
      ⟪u t x, gradient (fun y : NSSpace => q t y) x⟫ =
        ∑ i : Fin 3, (u t x) i * (gradient (fun y : NSSpace => q t y) x) i := by
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]
  have hInner :
      ⟪u t x, gradient (fun y : NSSpace => q t y) x⟫ =
        ∑ i : Fin 3, (u t x) i * (∂_{EuclideanSpace.single i (1 : ℝ)} (q t)) x := by
    rw [hInnerRaw]
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact congrArg (fun z : ℝ => (u t x) i * z) (hGradCoord i)
  rw [pressureEnergyPairing, hgrad, hInner]

/-- A Schwartz velocity time slice has integrable pressure energy pairing
against any time-indexed Schwartz pressure slice. -/
theorem integrable_pressureEnergyPairing_of_schwartzSlice_schwartzPressureSlice
    (u : NSVelocityField) (t : NSTime) (f : 𝓢(NSSpace, NSSpace))
    (q : NSTime → 𝓢(NSSpace, ℝ))
    (hslice : ∀ x, u t x = f x) :
    Integrable (pressureEnergyPairing u (fun s : NSTime => fun y : NSSpace => q s y) t) := by
  let coord : Fin 3 → 𝓢(NSSpace, ℝ) := fun i =>
    SchwartzMap.bilinLeftCLM
      (ContinuousLinearMap.apply ℝ ℝ)
      (g := fun _ : NSSpace => (EuclideanSpace.proj i : NSSpace →L[ℝ] ℝ))
      (by fun_prop) f
  have hCoordEq (i : Fin 3) (x : NSSpace) : coord i x = (f x) i := by
    simp [coord, SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.apply_apply]
  have hPair :
      pressureEnergyPairing u (fun s : NSTime => fun y : NSSpace => q s y) t =
        fun x : NSSpace =>
          ∑ i : Fin 3, coord i x * (∂_{EuclideanSpace.single i (1 : ℝ)} (q t)) x := by
    rw [pressureEnergyPairing_schwartzPressureSlice]
    funext x
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [hslice x]
    simp [hCoordEq i x]
  have hTermIntegrable (i : Fin 3) :
      Integrable
        (fun x : NSSpace =>
          coord i x * (∂_{EuclideanSpace.single i (1 : ℝ)} (q t)) x) := by
    simpa [coord, SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.apply_apply] using
      (SchwartzMap.pairing
        (ContinuousLinearMap.mul ℝ ℝ)
        (coord i)
        (∂_{EuclideanSpace.single i (1 : ℝ)} (q t))).integrable
  rw [hPair]
  exact integrable_finset_sum (Finset.univ : Finset (Fin 3)) (fun i _ => hTermIntegrable i)

/-- A divergence-free Schwartz velocity time slice has zero pressure work
against any time-indexed Schwartz pressure slice. -/
theorem integral_pressureEnergyPairing_of_schwartzSlice_schwartzPressureSlice_of_spatialDivergence_zero
    (u : NSVelocityField) (t : NSTime) (f : 𝓢(NSSpace, NSSpace))
    (q : NSTime → 𝓢(NSSpace, ℝ))
    (hslice : ∀ x, u t x = f x)
    (hdiv : ∀ x, spatialDivergence u t x = 0) :
    ∫ x, pressureEnergyPairing u (fun s : NSTime => fun y : NSSpace => q s y) t x ∂volume = 0 := by
  let coord : Fin 3 → 𝓢(NSSpace, ℝ) := fun i =>
    SchwartzMap.bilinLeftCLM
      (ContinuousLinearMap.apply ℝ ℝ)
      (g := fun _ : NSSpace => (EuclideanSpace.proj i : NSSpace →L[ℝ] ℝ))
      (by fun_prop) f
  have hsliceFun : (fun x : NSSpace => u t x) = (f : NSSpace → NSSpace) := funext hslice
  have hCoordEq (i : Fin 3) (x : NSSpace) : coord i x = (f x) i := by
    simp [coord, SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.apply_apply]
  have hCoordDeriv (i : Fin 3) (x : NSSpace) :
      (∂_{EuclideanSpace.single i (1 : ℝ)} (coord i)) x =
        (∂_{EuclideanSpace.single i (1 : ℝ)} f x) i := by
    have hproj :=
      congrArg
        (fun L : NSSpace →L[ℝ] ℝ => L (EuclideanSpace.single i (1 : ℝ)))
        (((EuclideanSpace.proj i : NSSpace →L[ℝ] ℝ).hasFDerivAt.comp x
          (f.hasFDerivAt x)).fderiv)
    simpa [coord, SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.apply_apply,
      ContinuousLinearMap.comp_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv] using hproj
  have hPair :
      pressureEnergyPairing u (fun s : NSTime => fun y : NSSpace => q s y) t =
        fun x : NSSpace =>
          ∑ i : Fin 3, coord i x * (∂_{EuclideanSpace.single i (1 : ℝ)} (q t)) x := by
    rw [pressureEnergyPairing_schwartzPressureSlice]
    funext x
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [hslice x]
    simp [hCoordEq i x]
  have hTermIntegrable (i : Fin 3) :
      Integrable
        (fun x : NSSpace =>
          coord i x * (∂_{EuclideanSpace.single i (1 : ℝ)} (q t)) x) := by
    simpa [coord, SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.apply_apply] using
      (SchwartzMap.pairing
        (ContinuousLinearMap.mul ℝ ℝ)
        (coord i)
        (∂_{EuclideanSpace.single i (1 : ℝ)} (q t))).integrable
  have hDivTermIntegrable (i : Fin 3) :
      Integrable
        (fun x : NSSpace =>
          (∂_{EuclideanSpace.single i (1 : ℝ)} (coord i)) x * q t x) := by
    simpa [coord, SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.apply_apply] using
      (SchwartzMap.pairing
        (ContinuousLinearMap.mul ℝ ℝ)
        (∂_{EuclideanSpace.single i (1 : ℝ)} (coord i))
        (q t)).integrable
  have hDivEq (x : NSSpace) :
      ∑ i : Fin 3, (∂_{EuclideanSpace.single i (1 : ℝ)} (coord i)) x = 0 := by
    have hx : spatialDivergence u t x = 0 := hdiv x
    rw [spatialDivergence, spatialFDeriv, hsliceFun] at hx
    convert hx using 1
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact hCoordDeriv i x
  rw [hPair]
  calc
    ∫ x, ∑ i : Fin 3, coord i x * (∂_{EuclideanSpace.single i (1 : ℝ)} (q t)) x ∂volume
        = ∑ i : Fin 3,
            ∫ x, coord i x * (∂_{EuclideanSpace.single i (1 : ℝ)} (q t)) x ∂volume := by
          rw [integral_finset_sum]
          intro i hi
          exact hTermIntegrable i
    _ = ∑ i : Fin 3,
          (-∫ x, (∂_{EuclideanSpace.single i (1 : ℝ)} (coord i)) x * q t x ∂volume) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [SchwartzMap.integral_mul_lineDerivOp_right_eq_neg_left
            (coord i) (q t) (EuclideanSpace.single i (1 : ℝ))]
    _ = -∑ i : Fin 3,
          ∫ x, (∂_{EuclideanSpace.single i (1 : ℝ)} (coord i)) x * q t x ∂volume := by
          rw [Finset.sum_neg_distrib]
    _ = -∫ x,
          ∑ i : Fin 3, (∂_{EuclideanSpace.single i (1 : ℝ)} (coord i)) x * q t x ∂volume := by
          congr 1
          rw [integral_finset_sum]
          intro i hi
          exact hDivTermIntegrable i
    _ = -∫ x, (0 : ℝ) ∂volume := by
          congr 1
          have hFun :
              (fun x : NSSpace =>
                ∑ i : Fin 3, (∂_{EuclideanSpace.single i (1 : ℝ)} (coord i)) x * q t x) =
                fun _ : NSSpace => 0 := by
            funext x
            rw [← Finset.sum_mul, hDivEq x]
            simp
          rw [hFun]
    _ = 0 := by simp

/-- The space integrand `u · Δu` from the viscous term. -/
def laplacianEnergyPairing (u : NSVelocityField) (t : NSTime) : NSSpace → ℝ :=
  fun x => ⟪u t x, spatialLaplacian u t x⟫

/-- The derivative-under-the-integral seam for the normalized kinetic energy.
This is the first genuinely analytic missing lemma on the current concrete NS
surface. -/
def EnergyDerivativeFormula (u : NSVelocityField) : Prop :=
  ∀ t,
    HasDerivAt (normalizedKineticEnergy u)
      (∫ x, timeEnergyPairing u t x ∂volume) t

/-- The viscous integration-by-parts seam
`∫ u · Δu = - ∫ ‖∇u‖²`. This is the second genuinely analytic missing lemma on
the current concrete NS surface. -/
def ViscousEnergyPairingFormula (u : NSVelocityField) : Prop :=
  ∀ t, ∫ x, laplacianEnergyPairing u t x ∂volume = -enstrophyAt u t

/-- Corrected viscous pairing seam using the coordinatewise dissipation density
coming from the standard orthonormal basis of `ℝ^3`. -/
def CoordinateViscousEnergyPairingFormula (u : NSVelocityField) : Prop :=
  ∀ t, ∫ x, laplacianEnergyPairing u t x ∂volume = -coordinateEnstrophyAt u t

/-- Integrability of the three space pairings used in the energy reduction. -/
def EnergyPairingIntegrable (u : NSVelocityField) (p : NSPressureField) : Prop :=
  ∀ t,
    Integrable (laplacianEnergyPairing u t) ∧
      Integrable (convectionEnergyPairing u t) ∧
      Integrable (pressureEnergyPairing u p t)

/-- A Schwartz profile on `ℝ^3` has integrable squared norm against Lebesgue
measure. This is the concrete `L²` input needed for the kinetic-energy
computations below. -/
theorem integrable_norm_sq_of_schwartz
    (f : 𝓢(NSSpace, NSSpace)) :
    Integrable (fun x : NSSpace => ‖f x‖ ^ (2 : ℕ)) := by
  simpa using
    (MeasureTheory.memLp_two_iff_integrable_sq_norm
      (μ := (volume : Measure NSSpace))
      f.continuous.aestronglyMeasurable).mp
      (f.memLp 2 (μ := (volume : Measure NSSpace)))

/-- Time derivative of a scalar-modulated spatial profile `u(t,x)=a(t)•f(x)`.
-/
theorem timeVelocityDerivative_scalar_smul
    (a a' : ℝ → ℝ) (f : NSSpace → NSSpace)
    (ha : ∀ t, HasDerivAt a (a' t) t) :
    ∀ t x, timeVelocityDerivative (fun s y => a s • f y) t x = a' t • f x := by
  intro t x
  unfold timeVelocityDerivative timeFDeriv
  have hDeriv : HasDerivAt (fun s : NSTime => a s • f x) (a' t • f x) t := by
    exact (ha t).smul_const (f x)
  rw [hDeriv.hasFDerivAt.fderiv]
  simp

/-- Kinetic energy of a scalar-modulated Schwartz profile
`u(t,x)=a(t)•f(x)`. -/
theorem kineticEnergyAt_scalar_smul_schwartz
    (a : ℝ → ℝ) (f : 𝓢(NSSpace, NSSpace)) :
    kineticEnergyAt (fun t x => a t • f x) =
      fun t => (a t) ^ (2 : ℕ) * ∫ x, ‖f x‖ ^ (2 : ℕ) ∂volume := by
  funext t
  rw [kineticEnergyAt]
  have hDensity :
      kineticEnergyDensity (fun s y => a s • f y) t =
        fun x : NSSpace => (a t) ^ (2 : ℕ) * ‖f x‖ ^ (2 : ℕ) := by
    funext x
    simp [kineticEnergyDensity, norm_smul, mul_pow, sq_abs]
  rw [hDensity]
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    integral_const_mul ((a t) ^ (2 : ℕ)) (fun x : NSSpace => ‖f x‖ ^ (2 : ℕ))

/-- Integral of the time-energy pairing for a scalar-modulated Schwartz profile
`u(t,x)=a(t)•f(x)`. -/
theorem integral_timeEnergyPairing_scalar_smul_schwartz
    (a a' : ℝ → ℝ) (f : 𝓢(NSSpace, NSSpace))
    (ha : ∀ t, HasDerivAt a (a' t) t) :
    ∀ t,
      ∫ x, timeEnergyPairing (fun s y => a s • f y) t x ∂volume =
        (a t * a' t) * ∫ x, ‖f x‖ ^ (2 : ℕ) ∂volume := by
  intro t
  have hPair :
      timeEnergyPairing (fun s y => a s • f y) t =
        fun x : NSSpace => (a t * a' t) * ‖f x‖ ^ (2 : ℕ) := by
    funext x
    rw [timeEnergyPairing, timeVelocityDerivative_scalar_smul a a' f ha t x]
    simp [real_inner_smul_left, real_inner_smul_right, mul_assoc, mul_left_comm]
  rw [hPair]
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    integral_const_mul (a t * a' t) (fun x : NSSpace => ‖f x‖ ^ (2 : ℕ))

/-- The derivative-under-the-integral seam holds for scalar-modulated
Schwartz profiles `u(t,x)=a(t)•f(x)`. This is a genuine nontrivial finite-energy
class on the concrete `ℝ × ℝ^3` surface. -/
theorem EnergyDerivativeFormula_of_scalar_smul_schwartz
    (a a' : ℝ → ℝ) (f : 𝓢(NSSpace, NSSpace))
    (ha : ∀ t, HasDerivAt a (a' t) t) :
    EnergyDerivativeFormula (fun s y => a s • f y) := by
  intro t
  let E : ℝ := ∫ x, ‖f x‖ ^ (2 : ℕ) ∂volume
  have hEnergy :
      normalizedKineticEnergy (fun s y => a s • f y) =
        fun s => ((1 / 2 : ℝ) * E) * (a s) ^ (2 : ℕ) := by
    funext s
    rw [normalizedKineticEnergy, kineticEnergyAt_scalar_smul_schwartz]
    simp [E]
    ring
  have hPair :
      ∫ x, timeEnergyPairing (fun s y => a s • f y) t x ∂volume =
        (a t * a' t) * E := by
    simpa [E] using integral_timeEnergyPairing_scalar_smul_schwartz a a' f ha t
  rw [hEnergy, hPair]
  have hPow :
      HasDerivAt (fun s : ℝ => (a s) ^ (2 : ℕ)) (2 * a t * a' t) t := by
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using (ha t).pow 2
  have hDeriv :
      HasDerivAt (fun s : ℝ => ((1 / 2 : ℝ) * E) * (a s) ^ (2 : ℕ))
        (((1 / 2 : ℝ) * E) * (2 * a t * a' t)) t := by
    exact hPow.const_mul (((1 / 2 : ℝ) * E))
  convert hDeriv using 1
  ring

/-- The pointwise inner product of two Schwartz profiles on `ℝ^3` is
integrable against Lebesgue measure. -/
theorem integrable_inner_schwartz
    (f g : 𝓢(NSSpace, NSSpace)) :
    Integrable (fun x : NSSpace => ⟪f x, g x⟫) := by
  simpa [SchwartzMap.pairing_apply_apply] using
    (SchwartzMap.pairing (innerSL ℝ) f g).integrable

/-- Time derivative of a two-profile scalar superposition
`u(t,x)=a(t)•f(x)+b(t)•g(x)`. -/
theorem timeVelocityDerivative_add_scalar_smul
    (a a' b b' : ℝ → ℝ) (f g : NSSpace → NSSpace)
    (ha : ∀ t, HasDerivAt a (a' t) t)
    (hb : ∀ t, HasDerivAt b (b' t) t) :
    ∀ t x,
      timeVelocityDerivative (fun s y => a s • f y + b s • g y) t x =
        a' t • f x + b' t • g x := by
  intro t x
  unfold timeVelocityDerivative timeFDeriv
  have hDeriv :
      HasDerivAt (fun s : NSTime => a s • f x + b s • g x)
        (a' t • f x + b' t • g x) t := by
    exact (ha t).smul_const (f x) |>.add ((hb t).smul_const (g x))
  rw [hDeriv.hasFDerivAt.fderiv]
  simp

/-- Kinetic energy of a two-profile scalar Schwartz superposition
`u(t,x)=a(t)•f(x)+b(t)•g(x)`. -/
theorem kineticEnergyAt_add_scalar_smul_schwartz
    (a b : ℝ → ℝ) (f g : 𝓢(NSSpace, NSSpace)) :
    kineticEnergyAt (fun t x => a t • f x + b t • g x) =
      fun t =>
        (a t) ^ (2 : ℕ) * ∫ x, ‖f x‖ ^ (2 : ℕ) ∂volume +
          (2 * (a t * b t)) * ∫ x, ⟪f x, g x⟫ ∂volume +
            (b t) ^ (2 : ℕ) * ∫ x, ‖g x‖ ^ (2 : ℕ) ∂volume := by
  funext t
  rw [kineticEnergyAt]
  have hDensity :
      kineticEnergyDensity (fun s y => a s • f y + b s • g y) t =
        fun x : NSSpace =>
          (a t) ^ (2 : ℕ) * ‖f x‖ ^ (2 : ℕ) +
            (2 * (a t * b t)) * ⟪f x, g x⟫ +
              (b t) ^ (2 : ℕ) * ‖g x‖ ^ (2 : ℕ) := by
    funext x
    rw [kineticEnergyDensity]
    simpa [real_inner_smul_left, real_inner_smul_right, real_inner_comm,
      norm_smul, sq_abs, mul_pow, mul_assoc, mul_left_comm, mul_comm] using
      (norm_add_sq_real (a t • f x) (b t • g x))
  have hIntF :
      Integrable (fun x : NSSpace => (a t) ^ (2 : ℕ) * ‖f x‖ ^ (2 : ℕ)) := by
    exact (integrable_norm_sq_of_schwartz f).const_mul ((a t) ^ (2 : ℕ))
  have hIntFG :
      Integrable (fun x : NSSpace => (2 * (a t * b t)) * ⟪f x, g x⟫) := by
    exact (integrable_inner_schwartz f g).const_mul (2 * (a t * b t))
  have hIntG :
      Integrable (fun x : NSSpace => (b t) ^ (2 : ℕ) * ‖g x‖ ^ (2 : ℕ)) := by
    exact (integrable_norm_sq_of_schwartz g).const_mul ((b t) ^ (2 : ℕ))
  rw [hDensity]
  calc
    ∫ x,
        ((a t) ^ (2 : ℕ) * ‖f x‖ ^ (2 : ℕ) +
          (2 * (a t * b t)) * ⟪f x, g x⟫ +
            (b t) ^ (2 : ℕ) * ‖g x‖ ^ (2 : ℕ)) ∂volume
      = ∫ x,
          ((a t) ^ (2 : ℕ) * ‖f x‖ ^ (2 : ℕ) +
            (2 * (a t * b t)) * ⟪f x, g x⟫) ∂volume
            + ∫ x, (b t) ^ (2 : ℕ) * ‖g x‖ ^ (2 : ℕ) ∂volume := by
          simpa [add_assoc] using integral_add (hIntF.add hIntFG) hIntG
    _ = (∫ x, (a t) ^ (2 : ℕ) * ‖f x‖ ^ (2 : ℕ) ∂volume
          + ∫ x, (2 * (a t * b t)) * ⟪f x, g x⟫ ∂volume)
          + ∫ x, (b t) ^ (2 : ℕ) * ‖g x‖ ^ (2 : ℕ) ∂volume := by
          rw [integral_add hIntF hIntFG]
    _ = (a t) ^ (2 : ℕ) * ∫ x, ‖f x‖ ^ (2 : ℕ) ∂volume +
          (2 * (a t * b t)) * ∫ x, ⟪f x, g x⟫ ∂volume +
            (b t) ^ (2 : ℕ) * ∫ x, ‖g x‖ ^ (2 : ℕ) ∂volume := by
          rw [integral_const_mul, integral_const_mul, integral_const_mul]

/-- Integral of the time-energy pairing for a two-profile scalar Schwartz
superposition. -/
theorem integral_timeEnergyPairing_add_scalar_smul_schwartz
    (a a' b b' : ℝ → ℝ) (f g : 𝓢(NSSpace, NSSpace))
    (ha : ∀ t, HasDerivAt a (a' t) t)
    (hb : ∀ t, HasDerivAt b (b' t) t) :
    ∀ t,
      ∫ x, timeEnergyPairing (fun s y => a s • f y + b s • g y) t x ∂volume =
        (a t * a' t) * ∫ x, ‖f x‖ ^ (2 : ℕ) ∂volume +
          (a t * b' t + b t * a' t) * ∫ x, ⟪f x, g x⟫ ∂volume +
            (b t * b' t) * ∫ x, ‖g x‖ ^ (2 : ℕ) ∂volume := by
  intro t
  have hPair :
      timeEnergyPairing (fun s y => a s • f y + b s • g y) t =
        fun x : NSSpace =>
          (a t * a' t) * ‖f x‖ ^ (2 : ℕ) +
            (a t * b' t + b t * a' t) * ⟪f x, g x⟫ +
              (b t * b' t) * ‖g x‖ ^ (2 : ℕ) := by
    funext x
    rw [timeEnergyPairing, timeVelocityDerivative_add_scalar_smul a a' b b' f g ha hb t x]
    simp [inner_add_left, inner_add_right, real_inner_smul_right, real_inner_comm,
      add_mul, mul_assoc, mul_left_comm, mul_comm]
    ring
  have hIntF :
      Integrable (fun x : NSSpace => (a t * a' t) * ‖f x‖ ^ (2 : ℕ)) := by
    exact (integrable_norm_sq_of_schwartz f).const_mul (a t * a' t)
  have hIntFG :
      Integrable (fun x : NSSpace => (a t * b' t + b t * a' t) * ⟪f x, g x⟫) := by
    exact (integrable_inner_schwartz f g).const_mul (a t * b' t + b t * a' t)
  have hIntG :
      Integrable (fun x : NSSpace => (b t * b' t) * ‖g x‖ ^ (2 : ℕ)) := by
    exact (integrable_norm_sq_of_schwartz g).const_mul (b t * b' t)
  rw [hPair]
  calc
    ∫ x,
        ((a t * a' t) * ‖f x‖ ^ (2 : ℕ) +
          (a t * b' t + b t * a' t) * ⟪f x, g x⟫ +
            (b t * b' t) * ‖g x‖ ^ (2 : ℕ)) ∂volume
      = ∫ x,
          ((a t * a' t) * ‖f x‖ ^ (2 : ℕ) +
            (a t * b' t + b t * a' t) * ⟪f x, g x⟫) ∂volume
            + ∫ x, (b t * b' t) * ‖g x‖ ^ (2 : ℕ) ∂volume := by
          simpa [add_assoc] using integral_add (hIntF.add hIntFG) hIntG
    _ = (∫ x, (a t * a' t) * ‖f x‖ ^ (2 : ℕ) ∂volume
          + ∫ x, (a t * b' t + b t * a' t) * ⟪f x, g x⟫ ∂volume)
          + ∫ x, (b t * b' t) * ‖g x‖ ^ (2 : ℕ) ∂volume := by
          rw [integral_add hIntF hIntFG]
    _ = (a t * a' t) * ∫ x, ‖f x‖ ^ (2 : ℕ) ∂volume +
          (a t * b' t + b t * a' t) * ∫ x, ⟪f x, g x⟫ ∂volume +
            (b t * b' t) * ∫ x, ‖g x‖ ^ (2 : ℕ) ∂volume := by
          rw [integral_const_mul, integral_const_mul, integral_const_mul]

/-- The derivative-under-the-integral seam holds for two-profile scalar
Schwartz superpositions `u(t,x)=a(t)•f(x)+b(t)•g(x)`. This is the first class
where nontrivial cross terms enter the energy identity on the concrete whole
space. -/
theorem EnergyDerivativeFormula_of_add_scalar_smul_schwartz
    (a a' b b' : ℝ → ℝ) (f g : 𝓢(NSSpace, NSSpace))
    (ha : ∀ t, HasDerivAt a (a' t) t)
    (hb : ∀ t, HasDerivAt b (b' t) t) :
    EnergyDerivativeFormula (fun s y => a s • f y + b s • g y) := by
  intro t
  let F : ℝ := ∫ x, ‖f x‖ ^ (2 : ℕ) ∂volume
  let FG : ℝ := ∫ x, ⟪f x, g x⟫ ∂volume
  let G : ℝ := ∫ x, ‖g x‖ ^ (2 : ℕ) ∂volume
  have hEnergy :
      normalizedKineticEnergy (fun s y => a s • f y + b s • g y) =
        fun s =>
          ((1 / 2 : ℝ) * F) * (a s) ^ (2 : ℕ) +
            FG * (a s * b s) +
              ((1 / 2 : ℝ) * G) * (b s) ^ (2 : ℕ) := by
    funext s
    rw [normalizedKineticEnergy, kineticEnergyAt_add_scalar_smul_schwartz]
    simp [F, FG, G]
    ring
  have hPair :
      ∫ x, timeEnergyPairing (fun s y => a s • f y + b s • g y) t x ∂volume =
        F * (a t * a' t) + FG * (a t * b' t + b t * a' t) + G * (b t * b' t) := by
    simpa [F, FG, G, mul_comm, mul_left_comm, mul_assoc] using
      integral_timeEnergyPairing_add_scalar_smul_schwartz a a' b b' f g ha hb t
  rw [hEnergy, hPair]
  have hA2 :
      HasDerivAt (fun s : ℝ => (a s) ^ (2 : ℕ)) (2 * a t * a' t) t := by
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using (ha t).pow 2
  have hAB :
      HasDerivAt (fun s : ℝ => a s * b s) (a' t * b t + a t * b' t) t := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using (ha t).mul (hb t)
  have hB2 :
      HasDerivAt (fun s : ℝ => (b s) ^ (2 : ℕ)) (2 * b t * b' t) t := by
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using (hb t).pow 2
  have hDeriv :
      HasDerivAt
        (fun s : ℝ =>
          ((1 / 2 : ℝ) * F) * (a s) ^ (2 : ℕ) +
            FG * (a s * b s) +
              ((1 / 2 : ℝ) * G) * (b s) ^ (2 : ℕ))
        ((((1 / 2 : ℝ) * F) * (2 * a t * a' t)) +
          (FG * (a' t * b t + a t * b' t)) +
            (((1 / 2 : ℝ) * G) * (2 * b t * b' t))) t := by
    simpa [add_assoc] using
      (hA2.const_mul (((1 / 2 : ℝ) * F))).add
        ((hAB.const_mul FG).add (hB2.const_mul (((1 / 2 : ℝ) * G))))
  convert hDeriv using 1
  ring

/-- Honest energy-identity reduction for smooth Navier-Stokes: once the two
analytic seams are supplied as explicit hypotheses, the concrete momentum
equation implies the dissipation law

`d/dt ((1/2) ∫ |u|²) = -ν ∫ ‖∇u‖²`.

This theorem proves the PDE-to-energy algebra directly on the current concrete
`ℝ × ℝ^3` surface and isolates the exact remaining analytic obligations rather
than hiding them behind placeholders. -/
theorem energyDissipationIdentity_smooth
    (u : NSVelocityField) (p : NSPressureField) (ν : ℝ)
    (hderiv : EnergyDerivativeFormula u)
    (heq : ∀ t x,
      timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
        (ν : ℝ) • spatialLaplacian u t x)
    (hintegrable : EnergyPairingIntegrable u p)
    (hviscous : ViscousEnergyPairingFormula u)
    (hboundary : ∀ t, ∫ x, pressureEnergyPairing u p t x ∂volume = 0)
    (hnonlinear : ∀ t, ∫ x, convectionEnergyPairing u t x ∂volume = 0) :
    ∀ t, HasDerivAt (normalizedKineticEnergy u) (-(energyDissipationRate u ν t)) t := by
  intro t
  let viscousContribution : NSSpace → ℝ :=
    fun x => ⟪u t x, (ν : ℝ) • spatialLaplacian u t x⟫
  have hIntL : Integrable (laplacianEnergyPairing u t) := (hintegrable t).1
  have hIntN : Integrable (convectionEnergyPairing u t) := (hintegrable t).2.1
  have hIntP : Integrable (pressureEnergyPairing u p t) := (hintegrable t).2.2
  have hViscousContribution :
      viscousContribution = fun x => (ν : ℝ) * laplacianEnergyPairing u t x := by
    funext x
    simpa [viscousContribution, laplacianEnergyPairing] using
      (real_inner_smul_right (u t x) (spatialLaplacian u t x) (ν : ℝ))
  have hIntViscous : Integrable viscousContribution := by
    rw [hViscousContribution]
    exact hIntL.const_mul ν
  have hPointwise :
      timeEnergyPairing u t =
        viscousContribution - convectionEnergyPairing u t - pressureEnergyPairing u p t := by
    funext x
    have hInnerEq :
        ⟪u t x, timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x⟫ =
          ⟪u t x, (ν : ℝ) • spatialLaplacian u t x⟫ := by
      exact congrArg (fun v : NSSpace => ⟪u t x, v⟫) (heq t x)
    have hExpanded :
        ⟪u t x, timeVelocityDerivative u t x⟫ +
            ⟪u t x, spatialConvection u t x⟫ +
              ⟪u t x, spatialPressureGradient p t x⟫ =
          ⟪u t x, (ν : ℝ) • spatialLaplacian u t x⟫ := by
      simpa [inner_add_right, add_assoc] using hInnerEq
    calc
      timeEnergyPairing u t x
          = ⟪u t x, timeVelocityDerivative u t x⟫ := by rfl
      _ = ⟪u t x, (ν : ℝ) • spatialLaplacian u t x⟫ -
            ⟪u t x, spatialConvection u t x⟫ -
              ⟪u t x, spatialPressureGradient p t x⟫ := by
            linarith
      _ = viscousContribution x - convectionEnergyPairing u t x - pressureEnergyPairing u p t x := by
            rfl
  have hMomentumIntegral :
      ∫ x, timeEnergyPairing u t x ∂volume =
        ∫ x, viscousContribution x ∂volume -
          ∫ x, convectionEnergyPairing u t x ∂volume -
            ∫ x, pressureEnergyPairing u p t x ∂volume := by
    rw [hPointwise]
    have hOuter :
        ∫ x, ((viscousContribution - convectionEnergyPairing u t) - pressureEnergyPairing u p t) x ∂volume =
          ∫ x, (viscousContribution - convectionEnergyPairing u t) x ∂volume -
            ∫ x, pressureEnergyPairing u p t x ∂volume := by
      simpa [Pi.sub_apply] using integral_sub (hIntViscous.sub hIntN) hIntP
    have hInner :
        ∫ x, (viscousContribution - convectionEnergyPairing u t) x ∂volume =
          ∫ x, viscousContribution x ∂volume - ∫ x, convectionEnergyPairing u t x ∂volume := by
      simpa [Pi.sub_apply] using integral_sub hIntViscous hIntN
    rw [hOuter, hInner]
  have hViscousIntegral :
      ∫ x, viscousContribution x ∂volume =
        (ν : ℝ) * ∫ x, laplacianEnergyPairing u t x ∂volume := by
    rw [hViscousContribution]
    simpa using integral_const_mul (ν : ℝ) (fun x => laplacianEnergyPairing u t x)
  have hEnergySlope :
      ∫ x, timeEnergyPairing u t x ∂volume = -(energyDissipationRate u ν t) := by
    calc
      ∫ x, timeEnergyPairing u t x ∂volume
          = ∫ x, viscousContribution x ∂volume -
              ∫ x, convectionEnergyPairing u t x ∂volume -
                ∫ x, pressureEnergyPairing u p t x ∂volume := hMomentumIntegral
      _ = (ν : ℝ) * ∫ x, laplacianEnergyPairing u t x ∂volume -
            ∫ x, convectionEnergyPairing u t x ∂volume -
              ∫ x, pressureEnergyPairing u p t x ∂volume := by
            rw [hViscousIntegral]
      _ = (ν : ℝ) * ∫ x, laplacianEnergyPairing u t x ∂volume - 0 - 0 := by
            rw [hnonlinear t, hboundary t]
      _ = (ν : ℝ) * ∫ x, laplacianEnergyPairing u t x ∂volume := by ring
      _ = (ν : ℝ) * (-enstrophyAt u t) := by rw [hviscous t]
      _ = -(energyDissipationRate u ν t) := by
            unfold energyDissipationRate
            ring
  have hd := hderiv t
  rw [hEnergySlope] at hd
  exact hd

/-- Honest corrected energy-identity reduction for smooth Navier-Stokes: once
the derivative-under-the-integral seam and the coordinatewise viscous pairing
formula are supplied, the concrete momentum equation implies the corrected
dissipation law

`d/dt ((1/2) ∫ |u|²) = -ν ∫ Σᵢ |∂ᵢu|²`. -/
theorem coordinateEnergyDissipationIdentity_smooth
    (u : NSVelocityField) (p : NSPressureField) (ν : ℝ)
    (hderiv : EnergyDerivativeFormula u)
    (heq : ∀ t x,
      timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
        (ν : ℝ) • spatialLaplacian u t x)
    (hintegrable : EnergyPairingIntegrable u p)
    (hviscous : CoordinateViscousEnergyPairingFormula u)
    (hboundary : ∀ t, ∫ x, pressureEnergyPairing u p t x ∂volume = 0)
    (hnonlinear : ∀ t, ∫ x, convectionEnergyPairing u t x ∂volume = 0) :
    ∀ t, HasDerivAt (normalizedKineticEnergy u)
      (-(coordinateEnergyDissipationRate u ν t)) t := by
  intro t
  let viscousContribution : NSSpace → ℝ :=
    fun x => ⟪u t x, (ν : ℝ) • spatialLaplacian u t x⟫
  have hIntL : Integrable (laplacianEnergyPairing u t) := (hintegrable t).1
  have hIntN : Integrable (convectionEnergyPairing u t) := (hintegrable t).2.1
  have hIntP : Integrable (pressureEnergyPairing u p t) := (hintegrable t).2.2
  have hViscousContribution :
      viscousContribution = fun x => (ν : ℝ) * laplacianEnergyPairing u t x := by
    funext x
    simpa [viscousContribution, laplacianEnergyPairing] using
      (real_inner_smul_right (u t x) (spatialLaplacian u t x) (ν : ℝ))
  have hIntViscous : Integrable viscousContribution := by
    rw [hViscousContribution]
    exact hIntL.const_mul ν
  have hPointwise :
      timeEnergyPairing u t =
        viscousContribution - convectionEnergyPairing u t - pressureEnergyPairing u p t := by
    funext x
    have hInnerEq :
        ⟪u t x, timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x⟫ =
          ⟪u t x, (ν : ℝ) • spatialLaplacian u t x⟫ := by
      exact congrArg (fun v : NSSpace => ⟪u t x, v⟫) (heq t x)
    have hExpanded :
        ⟪u t x, timeVelocityDerivative u t x⟫ +
            ⟪u t x, spatialConvection u t x⟫ +
              ⟪u t x, spatialPressureGradient p t x⟫ =
          ⟪u t x, (ν : ℝ) • spatialLaplacian u t x⟫ := by
      simpa [inner_add_right, add_assoc] using hInnerEq
    calc
      timeEnergyPairing u t x
          = ⟪u t x, timeVelocityDerivative u t x⟫ := by rfl
      _ = ⟪u t x, (ν : ℝ) • spatialLaplacian u t x⟫ -
            ⟪u t x, spatialConvection u t x⟫ -
              ⟪u t x, spatialPressureGradient p t x⟫ := by
            linarith
      _ = viscousContribution x - convectionEnergyPairing u t x - pressureEnergyPairing u p t x := by
            rfl
  have hMomentumIntegral :
      ∫ x, timeEnergyPairing u t x ∂volume =
        ∫ x, viscousContribution x ∂volume -
          ∫ x, convectionEnergyPairing u t x ∂volume -
            ∫ x, pressureEnergyPairing u p t x ∂volume := by
    rw [hPointwise]
    have hOuter :
        ∫ x, ((viscousContribution - convectionEnergyPairing u t) - pressureEnergyPairing u p t) x ∂volume =
          ∫ x, (viscousContribution - convectionEnergyPairing u t) x ∂volume -
            ∫ x, pressureEnergyPairing u p t x ∂volume := by
      simpa [Pi.sub_apply] using integral_sub (hIntViscous.sub hIntN) hIntP
    have hInner :
        ∫ x, (viscousContribution - convectionEnergyPairing u t) x ∂volume =
          ∫ x, viscousContribution x ∂volume - ∫ x, convectionEnergyPairing u t x ∂volume := by
      simpa [Pi.sub_apply] using integral_sub hIntViscous hIntN
    rw [hOuter, hInner]
  have hViscousIntegral :
      ∫ x, viscousContribution x ∂volume =
        (ν : ℝ) * ∫ x, laplacianEnergyPairing u t x ∂volume := by
    rw [hViscousContribution]
    simpa using integral_const_mul (ν : ℝ) (fun x => laplacianEnergyPairing u t x)
  have hEnergySlope :
      ∫ x, timeEnergyPairing u t x ∂volume = -(coordinateEnergyDissipationRate u ν t) := by
    calc
      ∫ x, timeEnergyPairing u t x ∂volume
          = ∫ x, viscousContribution x ∂volume -
              ∫ x, convectionEnergyPairing u t x ∂volume -
                ∫ x, pressureEnergyPairing u p t x ∂volume := hMomentumIntegral
      _ = (ν : ℝ) * ∫ x, laplacianEnergyPairing u t x ∂volume -
            ∫ x, convectionEnergyPairing u t x ∂volume -
              ∫ x, pressureEnergyPairing u p t x ∂volume := by
            rw [hViscousIntegral]
      _ = (ν : ℝ) * ∫ x, laplacianEnergyPairing u t x ∂volume - 0 - 0 := by
            rw [hnonlinear t, hboundary t]
      _ = (ν : ℝ) * ∫ x, laplacianEnergyPairing u t x ∂volume := by ring
      _ = (ν : ℝ) * (-coordinateEnstrophyAt u t) := by rw [hviscous t]
      _ = -(coordinateEnergyDissipationRate u ν t) := by
            unfold coordinateEnergyDissipationRate
            ring
  have hd := hderiv t
  rw [hEnergySlope] at hd
  exact hd

/-- The corrected coordinatewise energy identity gives monotone decay of the
normalized kinetic energy whenever the viscosity is nonnegative.  This is the
calculus bridge from the exact dissipation identity to the energy-inequality
shape. -/
theorem coordinateEnergyDissipationIdentity_smooth_antitone_normalizedKineticEnergy
    (u : NSVelocityField) (p : NSPressureField) {ν : ℝ}
    (hν : 0 ≤ ν)
    (hderiv : EnergyDerivativeFormula u)
    (heq : ∀ t x,
      timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
        (ν : ℝ) • spatialLaplacian u t x)
    (hintegrable : EnergyPairingIntegrable u p)
    (hviscous : CoordinateViscousEnergyPairingFormula u)
    (hboundary : ∀ t, ∫ x, pressureEnergyPairing u p t x ∂volume = 0)
    (hnonlinear : ∀ t, ∫ x, convectionEnergyPairing u t x ∂volume = 0) :
    Antitone (normalizedKineticEnergy u) := by
  refine
    antitone_of_hasDerivAt_nonpos
      (f' := fun t => -(coordinateEnergyDissipationRate u ν t))
      ?_ ?_
  · exact
      coordinateEnergyDissipationIdentity_smooth
        (u := u)
        (p := p)
        (ν := ν)
        hderiv
        heq
        hintegrable
        hviscous
        hboundary
        hnonlinear
  · intro t
    exact neg_coordinateEnergyDissipationRate_nonpos u hν t

/-- Two-time energy inequality extracted from the corrected coordinatewise
energy identity: later normalized kinetic energy is bounded by earlier
normalized kinetic energy. -/
theorem coordinateEnergyDissipationIdentity_smooth_normalizedKineticEnergy_le_of_le
    (u : NSVelocityField) (p : NSPressureField) {ν : ℝ}
    (hν : 0 ≤ ν)
    (hderiv : EnergyDerivativeFormula u)
    (heq : ∀ t x,
      timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
        (ν : ℝ) • spatialLaplacian u t x)
    (hintegrable : EnergyPairingIntegrable u p)
    (hviscous : CoordinateViscousEnergyPairingFormula u)
    (hboundary : ∀ t, ∫ x, pressureEnergyPairing u p t x ∂volume = 0)
    (hnonlinear : ∀ t, ∫ x, convectionEnergyPairing u t x ∂volume = 0)
    {t₀ t₁ : NSTime} (ht : t₀ ≤ t₁) :
    normalizedKineticEnergy u t₁ ≤ normalizedKineticEnergy u t₀ := by
  exact
    (coordinateEnergyDissipationIdentity_smooth_antitone_normalizedKineticEnergy
      (u := u)
      (p := p)
      (ν := ν)
      hν
      hderiv
      heq
      hintegrable
      hviscous
      hboundary
      hnonlinear) ht

/-- The corrected coordinatewise energy identity places every later normalized
kinetic energy between zero and its earlier value. -/
theorem coordinateEnergyDissipationIdentity_smooth_normalizedKineticEnergy_between_zero_and_initial
    (u : NSVelocityField) (p : NSPressureField) {ν : ℝ}
    (hν : 0 ≤ ν)
    (hderiv : EnergyDerivativeFormula u)
    (heq : ∀ t x,
      timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
        (ν : ℝ) • spatialLaplacian u t x)
    (hintegrable : EnergyPairingIntegrable u p)
    (hviscous : CoordinateViscousEnergyPairingFormula u)
    (hboundary : ∀ t, ∫ x, pressureEnergyPairing u p t x ∂volume = 0)
    (hnonlinear : ∀ t, ∫ x, convectionEnergyPairing u t x ∂volume = 0)
    {t₀ t₁ : NSTime} (ht : t₀ ≤ t₁) :
    0 ≤ normalizedKineticEnergy u t₁ ∧
      normalizedKineticEnergy u t₁ ≤ normalizedKineticEnergy u t₀ := by
  exact
    ⟨normalizedKineticEnergy_nonneg u t₁,
      coordinateEnergyDissipationIdentity_smooth_normalizedKineticEnergy_le_of_le
        (u := u)
        (p := p)
        (ν := ν)
        hν
        hderiv
        heq
        hintegrable
        hviscous
        hboundary
        hnonlinear
        ht⟩

/-- Standard kinetic-energy form of the corrected two-time energy inequality:
the unnormalized spatial kinetic energy at a later time is bounded by the
earlier one. -/
theorem coordinateEnergyDissipationIdentity_smooth_kineticEnergyAt_le_of_le
    (u : NSVelocityField) (p : NSPressureField) {ν : ℝ}
    (hν : 0 ≤ ν)
    (hderiv : EnergyDerivativeFormula u)
    (heq : ∀ t x,
      timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
        (ν : ℝ) • spatialLaplacian u t x)
    (hintegrable : EnergyPairingIntegrable u p)
    (hviscous : CoordinateViscousEnergyPairingFormula u)
    (hboundary : ∀ t, ∫ x, pressureEnergyPairing u p t x ∂volume = 0)
    (hnonlinear : ∀ t, ∫ x, convectionEnergyPairing u t x ∂volume = 0)
    {t₀ t₁ : NSTime} (ht : t₀ ≤ t₁) :
    kineticEnergyAt u t₁ ≤ kineticEnergyAt u t₀ := by
  have hnorm :
      normalizedKineticEnergy u t₁ ≤ normalizedKineticEnergy u t₀ :=
    coordinateEnergyDissipationIdentity_smooth_normalizedKineticEnergy_le_of_le
      (u := u)
      (p := p)
      (ν := ν)
      hν
      hderiv
      heq
      hintegrable
      hviscous
      hboundary
      hnonlinear
      ht
  unfold normalizedKineticEnergy at hnorm
  nlinarith

/-- Standard kinetic-energy estimate extracted from the corrected coordinatewise
energy identity: later kinetic energy lies between zero and the earlier kinetic
energy. -/
theorem coordinateEnergyDissipationIdentity_smooth_kineticEnergyAt_between_zero_and_initial
    (u : NSVelocityField) (p : NSPressureField) {ν : ℝ}
    (hν : 0 ≤ ν)
    (hderiv : EnergyDerivativeFormula u)
    (heq : ∀ t x,
      timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
        (ν : ℝ) • spatialLaplacian u t x)
    (hintegrable : EnergyPairingIntegrable u p)
    (hviscous : CoordinateViscousEnergyPairingFormula u)
    (hboundary : ∀ t, ∫ x, pressureEnergyPairing u p t x ∂volume = 0)
    (hnonlinear : ∀ t, ∫ x, convectionEnergyPairing u t x ∂volume = 0)
    {t₀ t₁ : NSTime} (ht : t₀ ≤ t₁) :
    0 ≤ kineticEnergyAt u t₁ ∧
      kineticEnergyAt u t₁ ≤ kineticEnergyAt u t₀ := by
  exact
    ⟨kineticEnergyAt_nonneg u t₁,
      coordinateEnergyDissipationIdentity_smooth_kineticEnergyAt_le_of_le
        (u := u)
        (p := p)
        (ν := ν)
        hν
        hderiv
        heq
        hintegrable
        hviscous
        hboundary
        hnonlinear
        ht⟩

/-- Repaired coordinatewise energy identity on the concrete finite-energy
surface: if the velocity field already satisfies the global bounded-energy
predicate used elsewhere in the concrete NS route, then every time slice has
honest integrable kinetic-energy density and the corrected dissipation identity
holds on that meaningful domain. -/
theorem meaningfulCoordinateEnergyDissipationIdentity_smooth_of_boundedKineticEnergy
    (u : NSVelocityField) (p : NSPressureField) (ν : ℝ)
    (henergy : boundedKineticEnergy u)
    (hderiv : EnergyDerivativeFormula u)
    (heq : ∀ t x,
      timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
        (ν : ℝ) • spatialLaplacian u t x)
    (hintegrable : EnergyPairingIntegrable u p)
    (hviscous : CoordinateViscousEnergyPairingFormula u)
    (hboundary : ∀ t, ∫ x, pressureEnergyPairing u p t x ∂volume = 0)
    (hnonlinear : ∀ t, ∫ x, convectionEnergyPairing u t x ∂volume = 0) :
    ∀ t,
      MeasureTheory.Integrable (kineticEnergyDensity u t) ∧
        HasDerivAt (normalizedKineticEnergy u)
          (-(coordinateEnergyDissipationRate u ν t)) t := by
  rcases henergy with ⟨C, hC, hbound⟩
  intro t
  refine ⟨(hbound t).1, ?_⟩
  exact
    coordinateEnergyDissipationIdentity_smooth
      (u := u)
      (p := p)
      (ν := ν)
      hderiv
      heq
      hintegrable
      hviscous
      hboundary
      hnonlinear
      t

/-- Corrected Schwartz-slice viscous pairing identity:

`∫ u · Δu = - ∫ Σᵢ |∂ᵢ u|²`.

This is the exact integration-by-parts statement produced by mathlib's
Schwartz-space Laplacian machinery on `ℝ^3`, and it targets the coordinatewise
gradient square rather than the operator norm of the full derivative. -/
theorem schwartz_integral_laplacianEnergyPairing_eq_neg_coordinateEnstrophy
    (f : 𝓢(NSSpace, NSSpace)) :
    ∫ x, ⟪f x, Δ f x⟫ ∂volume =
      - ∫ x, ∑ i : NSStdBasisIndex, ‖∂_{nsStdBasis i} f x‖ ^ (2 : ℕ) ∂volume := by
  let b : OrthonormalBasis NSStdBasisIndex ℝ NSSpace := nsStdBasis
  have hIntSecond :
      ∀ i : NSStdBasisIndex, Integrable (fun x : NSSpace => ⟪f x, ∂_{b i} (∂_{b i} f) x⟫) := by
    intro i
    simpa [SchwartzMap.pairing_apply_apply] using
      (SchwartzMap.pairing (innerSL ℝ) f (∂_{b i} (∂_{b i} f))).integrable
  have hIntDiag :
      ∀ i : NSStdBasisIndex, Integrable (fun x : NSSpace => ‖(∂_{b i} f) x‖ ^ (2 : ℕ)) := by
    intro i
    have hPair :
        Integrable
          (⇑(((SchwartzMap.pairing (innerSL ℝ)) (∂_{b i} f)) (∂_{b i} f)))
          (volume : Measure NSSpace) := by
      exact
        ((SchwartzMap.pairing (innerSL ℝ) (∂_{b i} f) (∂_{b i} f)).integrable
          (μ := (volume : Measure NSSpace)))
    have hEq :
        (⇑(((SchwartzMap.pairing (innerSL ℝ)) (∂_{b i} f)) (∂_{b i} f))) =
          fun x : NSSpace => ‖(∂_{b i} f) x‖ ^ (2 : ℕ) := by
      funext x
      rw [SchwartzMap.pairing_apply_apply, innerSL_apply_apply, real_inner_self_eq_norm_sq]
    rw [← hEq]
    exact hPair
  have hIBP :
      ∀ i : NSStdBasisIndex,
        ∫ x, ⟪f x, (∂_{b i} (∂_{b i} f)) x⟫ ∂volume =
          - ∫ x, ‖(∂_{b i} f) x‖ ^ (2 : ℕ) ∂volume := by
    intro i
    have hRaw :
        ∫ x, ((innerSL ℝ) (f x)) ((∂_{b i} (∂_{b i} f)) x) ∂volume =
          - ∫ x, ((innerSL ℝ) ((∂_{b i} f) x)) ((∂_{b i} f) x) ∂volume := by
      exact
        (SchwartzMap.integral_bilinear_lineDerivOp_right_eq_neg_left
        (μ := (volume : Measure NSSpace))
        f (∂_{b i} f) (innerSL ℝ) (b i))
    have hLeft :
        (fun x : NSSpace => ((innerSL ℝ) (f x)) ((∂_{b i} (∂_{b i} f)) x)) =
          fun x : NSSpace => ⟪f x, (∂_{b i} (∂_{b i} f)) x⟫ := by
      funext x
      simp [innerSL_apply_apply]
    have hRight :
        (fun x : NSSpace => ((innerSL ℝ) ((∂_{b i} f) x)) ((∂_{b i} f) x)) =
          fun x : NSSpace => ‖(∂_{b i} f) x‖ ^ (2 : ℕ) := by
      funext x
      rw [innerSL_apply_apply, real_inner_self_eq_norm_sq]
    rw [hLeft, hRight] at hRaw
    exact hRaw
  have hLapExpand :
      ∫ x, ⟪f x, Δ f x⟫ ∂volume =
        ∫ x, ∑ i : NSStdBasisIndex, ⟪f x, ∂_{b i} (∂_{b i} f) x⟫ ∂volume := by
    rw [SchwartzMap.laplacian_eq_sum b f]
    simp [inner_sum]
  calc
    ∫ x, ⟪f x, Δ f x⟫ ∂volume
        = ∫ x, ∑ i : NSStdBasisIndex, ⟪f x, ∂_{b i} (∂_{b i} f) x⟫ ∂volume := hLapExpand
    _ = ∑ i : NSStdBasisIndex, ∫ x, ⟪f x, ∂_{b i} (∂_{b i} f) x⟫ ∂volume := by
          rw [integral_finset_sum]
          intro i hi
          exact hIntSecond i
    _ = ∑ i : NSStdBasisIndex, - ∫ x, ‖(∂_{b i} f) x‖ ^ (2 : ℕ) ∂volume := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          exact hIBP i
    _ = - ∑ i : NSStdBasisIndex, ∫ x, ‖(∂_{b i} f) x‖ ^ (2 : ℕ) ∂volume := by
          rw [Finset.sum_neg_distrib]
    _ = - ∫ x, ∑ i : NSStdBasisIndex, ‖(∂_{b i} f) x‖ ^ (2 : ℕ) ∂volume := by
          congr 1
          rw [integral_finset_sum]
          intro i hi
          exact hIntDiag i
    _ = - ∫ x, ∑ i : NSStdBasisIndex, ‖∂_{b i} f x‖ ^ (2 : ℕ) ∂volume := by
          rfl

/-- A concrete Navier-Stokes time slice that agrees pointwise with a Schwartz
function satisfies the corrected viscous pairing identity. -/
theorem coordinateViscousEnergyPairingFormula_of_schwartzSlice
    (u : NSVelocityField) (t : NSTime) (f : 𝓢(NSSpace, NSSpace))
    (hslice : ∀ x, u t x = f x) :
    ∫ x, laplacianEnergyPairing u t x ∂volume = -coordinateEnstrophyAt u t := by
  let b : OrthonormalBasis NSStdBasisIndex ℝ NSSpace := nsStdBasis
  have hsliceFun : (fun x : NSSpace => u t x) = (f : NSSpace → NSSpace) := funext hslice
  have hLhs :
      laplacianEnergyPairing u t = fun x : NSSpace => ⟪f x, Δ f x⟫ := by
    funext x
    have hLap : spatialLaplacian u t x = Δ f x := by
      rw [spatialLaplacian, hsliceFun]
      exact (SchwartzMap.laplacian_apply f x).symm
    rw [laplacianEnergyPairing, hslice x, hLap]
  have hRhs :
      coordinateEnstrophyDensity u t =
        fun x : NSSpace => ∑ i : NSStdBasisIndex, ‖∂_{b i} f x‖ ^ (2 : ℕ) := by
    funext x
    simp only [coordinateEnstrophyDensity]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [spatialFDeriv, hsliceFun]
    rw [← SchwartzMap.lineDerivOp_apply_eq_fderiv]
  rw [hLhs, coordinateEnstrophyAt, hRhs]
  exact schwartz_integral_laplacianEnergyPairing_eq_neg_coordinateEnstrophy f

/-- The corrected viscous pairing seam holds for two-profile scalar Schwartz
superpositions `u(t,x)=a(t)•f(x)+b(t)•g(x)`. This matches the same nontrivial
finite-energy class where the derivative-under-the-integral seam has already
been proved. -/
theorem CoordinateViscousEnergyPairingFormula_of_add_scalar_smul_schwartz
    (a b : ℝ → ℝ) (f g : 𝓢(NSSpace, NSSpace)) :
    CoordinateViscousEnergyPairingFormula (fun s y => a s • f y + b s • g y) := by
  intro t
  exact
    coordinateViscousEnergyPairingFormula_of_schwartzSlice
      (u := fun s y => a s • f y + b s • g y)
      (t := t)
      (f := (a t) • f + (b t) • g)
      (hslice := by
        intro x
        rfl)

/-- A concrete Navier-Stokes time slice that agrees pointwise with a Schwartz
function has integrable viscous energy pairing. -/
theorem integrable_laplacianEnergyPairing_of_schwartzSlice
    (u : NSVelocityField) (t : NSTime) (f : 𝓢(NSSpace, NSSpace))
    (hslice : ∀ x, u t x = f x) :
    Integrable (laplacianEnergyPairing u t) := by
  have hsliceFun : (fun x : NSSpace => u t x) = (f : NSSpace → NSSpace) := funext hslice
  have hPair :
      laplacianEnergyPairing u t = fun x : NSSpace => ⟪f x, Δ f x⟫ := by
    funext x
    have hLap : spatialLaplacian u t x = Δ f x := by
      rw [spatialLaplacian, hsliceFun]
      exact (SchwartzMap.laplacian_apply f x).symm
    rw [laplacianEnergyPairing, hslice x, hLap]
  rw [hPair]
  simpa [SchwartzMap.pairing_apply_apply] using integrable_inner_schwartz f (Δ f)

/-- A concrete Navier-Stokes time slice that agrees pointwise with a Schwartz
function has integrable convection energy pairing. -/
theorem integrable_convectionEnergyPairing_of_schwartzSlice
    (u : NSVelocityField) (t : NSTime) (f : 𝓢(NSSpace, NSSpace))
    (hslice : ∀ x, u t x = f x) :
    Integrable (convectionEnergyPairing u t) := by
  let coord : Fin 3 → 𝓢(NSSpace, ℝ) := fun i =>
    SchwartzMap.bilinLeftCLM
      (ContinuousLinearMap.apply ℝ ℝ)
      (g := fun _ : NSSpace => (EuclideanSpace.proj i : NSSpace →L[ℝ] ℝ))
      (by fun_prop) f
  have hsliceFun : (fun x : NSSpace => u t x) = (f : NSSpace → NSSpace) := funext hslice
  have hCoordEq (i : Fin 3) (x : NSSpace) : coord i x = (f x) i := by
    simp [coord, SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.apply_apply]
  have hConvectionEq :
      convectionEnergyPairing u t =
        fun x : NSSpace =>
          ∑ i : Fin 3, coord i x * ⟪f x, ∂_{EuclideanSpace.single i (1 : ℝ)} f x⟫ := by
    funext x
    have hVec :
        f x = ∑ i : Fin 3, coord i x • EuclideanSpace.single i (1 : ℝ) := by
      ext j
      change (f x).ofLp j =
        (∑ i : Fin 3, coord i x • EuclideanSpace.single i (1 : ℝ)).ofLp j
      fin_cases j <;> rw [Fin.sum_univ_three] <;> simp [hCoordEq]
    rw [convectionEnergyPairing, spatialConvection, hslice x, spatialFDeriv, hsliceFun]
    rw [hVec, map_sum, inner_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [ContinuousLinearMap.map_smul, real_inner_smul_right]
    simp [SchwartzMap.lineDerivOp_apply_eq_fderiv, mul_comm]
  have hTermIntegrable (i : Fin 3) :
      Integrable
        (fun x : NSSpace =>
          coord i x * ⟪f x, ∂_{EuclideanSpace.single i (1 : ℝ)} f x⟫) := by
    simpa [coord, SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.apply_apply,
      SchwartzMap.pairing_apply_apply] using
      (SchwartzMap.pairing
        (ContinuousLinearMap.mul ℝ ℝ)
        (coord i)
        (SchwartzMap.pairing (innerSL ℝ) f (∂_{EuclideanSpace.single i (1 : ℝ)} f))).integrable
  rw [hConvectionEq]
  simpa using integrable_finset_sum (Finset.univ : Finset (Fin 3)) (fun i hi => hTermIntegrable i)

/-- A concrete Navier-Stokes time slice that agrees pointwise with a
divergence-free Schwartz function has vanishing convection energy integral. -/
theorem integral_convectionEnergyPairing_of_schwartzSlice_of_spatialDivergence_zero
    (u : NSVelocityField) (t : NSTime) (f : 𝓢(NSSpace, NSSpace))
    (hslice : ∀ x, u t x = f x)
    (hdiv : ∀ x, spatialDivergence u t x = 0) :
    ∫ x, convectionEnergyPairing u t x ∂volume = 0 := by
  let coord : Fin 3 → 𝓢(NSSpace, ℝ) := fun i =>
    SchwartzMap.bilinLeftCLM
      (ContinuousLinearMap.apply ℝ ℝ)
      (g := fun _ : NSSpace => (EuclideanSpace.proj i : NSSpace →L[ℝ] ℝ))
      (by fun_prop) f
  let normSq : 𝓢(NSSpace, ℝ) := SchwartzMap.pairing (innerSL ℝ) f f
  have hsliceFun : (fun x : NSSpace => u t x) = (f : NSSpace → NSSpace) := funext hslice
  have hCoordEq (i : Fin 3) (x : NSSpace) : coord i x = (f x) i := by
    simp [coord, SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.apply_apply]
  have hCoordDeriv (i : Fin 3) (x : NSSpace) :
      (∂_{EuclideanSpace.single i (1 : ℝ)} (coord i)) x =
        (∂_{EuclideanSpace.single i (1 : ℝ)} f x) i := by
    have hproj :=
      congrArg
        (fun L : NSSpace →L[ℝ] ℝ => L (EuclideanSpace.single i (1 : ℝ)))
        (((EuclideanSpace.proj i : NSSpace →L[ℝ] ℝ).hasFDerivAt.comp x
          (f.hasFDerivAt x)).fderiv)
    simpa [coord, SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.apply_apply,
      ContinuousLinearMap.comp_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv] using hproj
  have hNormSqDeriv (i : Fin 3) (x : NSSpace) :
      ∂_{EuclideanSpace.single i (1 : ℝ)} normSq x =
        2 * ⟪f x, ∂_{EuclideanSpace.single i (1 : ℝ)} f x⟫ := by
    have hNormSqEq :
        (normSq : NSSpace → ℝ) = fun y : NSSpace => ‖f y‖ ^ (2 : ℕ) := by
      funext y
      simp [normSq, SchwartzMap.pairing_apply_apply]
      rw [innerSL_apply_apply, real_inner_self_eq_norm_sq]
    have hnorm :=
      congrArg
        (fun L : NSSpace →L[ℝ] ℝ => L (EuclideanSpace.single i (1 : ℝ)))
        ((f.hasFDerivAt x).norm_sq.fderiv)
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, hNormSqEq]
    simpa [ContinuousLinearMap.comp_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv] using hnorm
  have hConvectionEq :
      convectionEnergyPairing u t =
        fun x : NSSpace =>
          ∑ i : Fin 3, coord i x * ⟪f x, ∂_{EuclideanSpace.single i (1 : ℝ)} f x⟫ := by
    funext x
    have hVec :
        f x = ∑ i : Fin 3, coord i x • EuclideanSpace.single i (1 : ℝ) := by
      ext j
      change (f x).ofLp j =
        (∑ i : Fin 3, coord i x • EuclideanSpace.single i (1 : ℝ)).ofLp j
      fin_cases j <;> rw [Fin.sum_univ_three] <;> simp [hCoordEq]
    rw [convectionEnergyPairing, spatialConvection, hslice x, spatialFDeriv, hsliceFun]
    rw [hVec, map_sum, inner_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [ContinuousLinearMap.map_smul, real_inner_smul_right]
    simp [SchwartzMap.lineDerivOp_apply_eq_fderiv, mul_comm]
  have hTermIntegrable (i : Fin 3) :
      Integrable
        (fun x : NSSpace =>
          coord i x * ⟪f x, ∂_{EuclideanSpace.single i (1 : ℝ)} f x⟫) := by
    simpa [coord, SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.apply_apply,
      SchwartzMap.pairing_apply_apply] using
      (SchwartzMap.pairing
        (ContinuousLinearMap.mul ℝ ℝ)
        (coord i)
        (SchwartzMap.pairing (innerSL ℝ) f (∂_{EuclideanSpace.single i (1 : ℝ)} f))).integrable
  have hDivTermIntegrable (i : Fin 3) :
      Integrable
        (fun x : NSSpace =>
          (∂_{EuclideanSpace.single i (1 : ℝ)} (coord i)) x * normSq x) := by
    simpa [normSq, SchwartzMap.pairing_apply_apply] using
      (SchwartzMap.pairing
        (ContinuousLinearMap.mul ℝ ℝ)
        (∂_{EuclideanSpace.single i (1 : ℝ)} (coord i))
        normSq).integrable
  have hDivEq (x : NSSpace) :
      ∑ i : Fin 3, (∂_{EuclideanSpace.single i (1 : ℝ)} (coord i)) x = 0 := by
    have hx : spatialDivergence u t x = 0 := hdiv x
    rw [spatialDivergence, spatialFDeriv, hsliceFun] at hx
    convert hx using 1
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact hCoordDeriv i x
  calc
    ∫ x, convectionEnergyPairing u t x ∂volume
        = ∫ x,
            ∑ i : Fin 3,
              coord i x * ⟪f x, ∂_{EuclideanSpace.single i (1 : ℝ)} f x⟫ ∂volume := by
            rw [hConvectionEq]
    _ = ∑ i : Fin 3,
          ∫ x, coord i x * ⟪f x, ∂_{EuclideanSpace.single i (1 : ℝ)} f x⟫ ∂volume := by
          rw [integral_finset_sum]
          intro i hi
          exact hTermIntegrable i
    _ = ∑ i : Fin 3,
          (1 / 2 : ℝ) *
            ∫ x, coord i x * ∂_{EuclideanSpace.single i (1 : ℝ)} normSq x ∂volume := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hEq :
              (fun x : NSSpace =>
                coord i x * ⟪f x, ∂_{EuclideanSpace.single i (1 : ℝ)} f x⟫) =
                fun x : NSSpace =>
                  (1 / 2 : ℝ) *
                    (coord i x * ∂_{EuclideanSpace.single i (1 : ℝ)} normSq x) := by
            funext x
            rw [hNormSqDeriv i x]
            ring
          rw [hEq, integral_const_mul]
    _ = ∑ i : Fin 3,
          (-(1 / 2 : ℝ)) *
            ∫ x, (∂_{EuclideanSpace.single i (1 : ℝ)} (coord i)) x * normSq x ∂volume := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [SchwartzMap.integral_mul_lineDerivOp_right_eq_neg_left
            (coord i) normSq (EuclideanSpace.single i (1 : ℝ))]
          ring
    _ = (-(1 / 2 : ℝ)) *
          ∑ i : Fin 3,
            ∫ x, (∂_{EuclideanSpace.single i (1 : ℝ)} (coord i)) x * normSq x ∂volume := by
          rw [← Finset.mul_sum]
    _ = (-(1 / 2 : ℝ)) *
          ∫ x,
            ∑ i : Fin 3, (∂_{EuclideanSpace.single i (1 : ℝ)} (coord i)) x * normSq x ∂volume := by
          congr 2
          rw [integral_finset_sum]
          intro i hi
          exact hDivTermIntegrable i
    _ = (-(1 / 2 : ℝ)) * ∫ x, (0 : ℝ) ∂volume := by
          congr 2
          funext x
          rw [← Finset.sum_mul, hDivEq x]
          simp
    _ = 0 := by simp

/-- The nonlinear transport energy integral vanishes for a two-profile Schwartz
superposition whenever the combined velocity field is divergence-free on every
time slice. -/
theorem integral_convectionEnergyPairing_of_add_scalar_smul_schwartz_of_spatialDivergence_zero
    (a b : ℝ → ℝ) (f g : 𝓢(NSSpace, NSSpace))
    (hdiv :
      ∀ t x,
        spatialDivergence (fun s y => a s • f y + b s • g y) t x = 0) :
    ∀ t,
      ∫ x, convectionEnergyPairing (fun s y => a s • f y + b s • g y) t x ∂volume = 0 := by
  intro t
  apply integral_convectionEnergyPairing_of_schwartzSlice_of_spatialDivergence_zero
    (u := fun s y => a s • f y + b s • g y)
    (t := t)
    (f := (a t) • f + (b t) • g)
  · intro x
    rfl
  · intro x
    exact hdiv t x

/-- The nonlinear transport energy integral vanishes for a two-profile Schwartz
superposition once both spatial profiles are divergence-free in the standard
coordinate basis of `ℝ^3`. -/
theorem integral_convectionEnergyPairing_of_add_scalar_smul_schwartz_of_divergenceFree
    (a b : ℝ → ℝ) (f g : 𝓢(NSSpace, NSSpace))
    (hfdiv : ∀ x,
      ∑ i : Fin 3, (∂_{EuclideanSpace.single i (1 : ℝ)} f x) i = 0)
    (hgdiv : ∀ x,
      ∑ i : Fin 3, (∂_{EuclideanSpace.single i (1 : ℝ)} g x) i = 0) :
    ∀ t,
      ∫ x, convectionEnergyPairing (fun s y => a s • f y + b s • g y) t x ∂volume = 0 := by
  apply integral_convectionEnergyPairing_of_add_scalar_smul_schwartz_of_spatialDivergence_zero
    (a := a) (b := b) (f := f) (g := g)
  intro t x
  let uf : NSVelocityField := fun _ y => f y
  let ug : NSVelocityField := fun _ y => g y
  have huf : spatialDivergence uf t x = 0 := by
    simpa [uf, spatialDivergence, spatialFDeriv, SchwartzMap.lineDerivOp_apply_eq_fderiv] using
      hfdiv x
  have hug : spatialDivergence ug t x = 0 := by
    simpa [ug, spatialDivergence, spatialFDeriv, SchwartzMap.lineDerivOp_apply_eq_fderiv] using
      hgdiv x
  have hsum :
      spatialDivergence ((a t) • uf + (b t) • ug) t x =
        spatialDivergence ((a t) • uf) t x + spatialDivergence ((b t) • ug) t x := by
    apply spatialDivergence_add
    · simpa [uf] using (show DifferentiableAt ℝ (fun y : NSSpace => a t • f y) x by fun_prop)
    · simpa [ug] using (show DifferentiableAt ℝ (fun y : NSSpace => b t • g y) x by fun_prop)
  change spatialDivergence ((a t) • uf + (b t) • ug) t x = 0
  rw [hsum, spatialDivergence_const_smul, spatialDivergence_const_smul, huf, hug]
  simp

/-- Uniformly bounded scalar coefficients keep a two-profile Schwartz
superposition in the concrete bounded-energy class. -/
theorem boundedKineticEnergy_of_add_scalar_smul_schwartz_of_abs_le
    (a b : ℝ → ℝ) (f g : 𝓢(NSSpace, NSSpace)) (A B : ℝ)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B) :
    boundedKineticEnergy (fun s y => a s • f y + b s • g y) := by
  let u : NSVelocityField := fun s y => a s • f y + b s • g y
  have hA : 0 ≤ A := by
    nlinarith [abs_nonneg (a 0), haBound 0]
  have hB : 0 ≤ B := by
    nlinarith [abs_nonneg (b 0), hbBound 0]
  let C : ℝ :=
    (2 * A ^ (2 : ℕ)) * ∫ x, ‖f x‖ ^ (2 : ℕ) ∂volume +
      (2 * B ^ (2 : ℕ)) * ∫ x, ‖g x‖ ^ (2 : ℕ) ∂volume
  have hIntF :
      Integrable (fun x : NSSpace => (2 * A ^ (2 : ℕ)) * ‖f x‖ ^ (2 : ℕ)) := by
    exact (integrable_norm_sq_of_schwartz f).const_mul (2 * A ^ (2 : ℕ))
  have hIntG :
      Integrable (fun x : NSSpace => (2 * B ^ (2 : ℕ)) * ‖g x‖ ^ (2 : ℕ)) := by
    exact (integrable_norm_sq_of_schwartz g).const_mul (2 * B ^ (2 : ℕ))
  have hIntF_nonneg : 0 ≤ ∫ x, ‖f x‖ ^ (2 : ℕ) ∂volume := by
    refine integral_nonneg_of_ae ?_
    filter_upwards with x
    positivity
  have hIntG_nonneg : 0 ≤ ∫ x, ‖g x‖ ^ (2 : ℕ) ∂volume := by
    refine integral_nonneg_of_ae ?_
    filter_upwards with x
    positivity
  have hC : 0 ≤ C := by
    dsimp [C]
    nlinarith [hIntF_nonneg, hIntG_nonneg]
  refine ⟨C, hC, ?_⟩
  intro t
  have hPointwise :
      ∀ x : NSSpace,
        kineticEnergyDensity u t x ≤
          (2 * A ^ (2 : ℕ)) * ‖f x‖ ^ (2 : ℕ) +
            (2 * B ^ (2 : ℕ)) * ‖g x‖ ^ (2 : ℕ) := by
    intro x
    have hMulF : |a t| * ‖f x‖ ≤ A * ‖f x‖ := by
      nlinarith [haBound t, norm_nonneg (f x)]
    have hMulG : |b t| * ‖g x‖ ≤ B * ‖g x‖ := by
      nlinarith [hbBound t, norm_nonneg (g x)]
    have hNorm :
        ‖a t • f x + b t • g x‖ ≤ A * ‖f x‖ + B * ‖g x‖ := by
      calc
        ‖a t • f x + b t • g x‖ ≤ ‖a t • f x‖ + ‖b t • g x‖ := norm_add_le _ _
        _ = |a t| * ‖f x‖ + |b t| * ‖g x‖ := by simp [norm_smul]
        _ ≤ A * ‖f x‖ + B * ‖g x‖ := by linarith
    have hX_nonneg : 0 ≤ A * ‖f x‖ := by positivity
    have hY_nonneg : 0 ≤ B * ‖g x‖ := by positivity
    have hSq :
        ‖a t • f x + b t • g x‖ ^ (2 : ℕ) ≤
          (A * ‖f x‖ + B * ‖g x‖) ^ (2 : ℕ) := by
      nlinarith [hNorm, norm_nonneg (a t • f x + b t • g x), hX_nonneg, hY_nonneg]
    have hSumSq :
        (A * ‖f x‖ + B * ‖g x‖) ^ (2 : ℕ) ≤
          2 * (A * ‖f x‖) ^ (2 : ℕ) + 2 * (B * ‖g x‖) ^ (2 : ℕ) := by
      nlinarith [two_mul_le_add_sq (A * ‖f x‖) (B * ‖g x‖)]
    calc
      kineticEnergyDensity u t x = ‖a t • f x + b t • g x‖ ^ (2 : ℕ) := by rfl
      _ ≤ (A * ‖f x‖ + B * ‖g x‖) ^ (2 : ℕ) := hSq
      _ ≤ 2 * (A * ‖f x‖) ^ (2 : ℕ) + 2 * (B * ‖g x‖) ^ (2 : ℕ) := hSumSq
      _ = (2 * A ^ (2 : ℕ)) * ‖f x‖ ^ (2 : ℕ) +
            (2 * B ^ (2 : ℕ)) * ‖g x‖ ^ (2 : ℕ) := by
            ring
  have hMeas :
      AEStronglyMeasurable (kineticEnergyDensity u t) (volume : Measure NSSpace) := by
    have hCont :
        Continuous (fun x : NSSpace => kineticEnergyDensity u t x) := by
      simpa [u, kineticEnergyDensity] using
        (((f.continuous.const_smul (a t)).add (g.continuous.const_smul (b t))).norm.pow 2)
    exact hCont.aestronglyMeasurable
  have hIntDensity : Integrable (kineticEnergyDensity u t) := by
    refine Integrable.mono' (hIntF.add hIntG) hMeas ?_
    filter_upwards with x
    have hDensity_nonneg : 0 ≤ kineticEnergyDensity u t x := by
      simp [u, kineticEnergyDensity]
    simpa [Real.norm_eq_abs, abs_of_nonneg hDensity_nonneg] using hPointwise x
  refine ⟨hIntDensity, ?_⟩
  calc
    kineticEnergyAt u t = ∫ x, kineticEnergyDensity u t x ∂volume := by rfl
    _ ≤ ∫ x,
          ((2 * A ^ (2 : ℕ)) * ‖f x‖ ^ (2 : ℕ) +
            (2 * B ^ (2 : ℕ)) * ‖g x‖ ^ (2 : ℕ)) ∂volume := by
          exact integral_mono hIntDensity (hIntF.add hIntG) hPointwise
    _ = C := by
          dsimp [C]
          rw [integral_add hIntF hIntG, integral_const_mul, integral_const_mul]

/-- The repaired bounded-energy guarded coordinate energy identity holds for a
two-profile Schwartz superposition once the scalar coefficients are uniformly
bounded and the concrete PDE hypotheses are supplied. -/
theorem meaningfulCoordinateEnergyDissipationIdentity_smooth_of_add_scalar_smul_schwartz_of_abs_le
    (a a' b b' : ℝ → ℝ) (f g : 𝓢(NSSpace, NSSpace)) (A B : ℝ)
    (p : NSPressureField) (ν : ℝ)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (ha : ∀ t, HasDerivAt a (a' t) t)
    (hb : ∀ t, HasDerivAt b (b' t) t)
    (heq : ∀ t x,
      timeVelocityDerivative (fun s y => a s • f y + b s • g y) t x +
          spatialConvection (fun s y => a s • f y + b s • g y) t x +
          spatialPressureGradient p t x =
        (ν : ℝ) • spatialLaplacian (fun s y => a s • f y + b s • g y) t x)
    (hintegrable :
      EnergyPairingIntegrable (fun s y => a s • f y + b s • g y) p)
    (hboundary :
      ∀ t,
        ∫ x, pressureEnergyPairing (fun s y => a s • f y + b s • g y) p t x ∂volume = 0)
    (hnonlinear :
      ∀ t,
        ∫ x, convectionEnergyPairing (fun s y => a s • f y + b s • g y) t x ∂volume = 0) :
    ∀ t,
      MeasureTheory.Integrable
          (kineticEnergyDensity (fun s y => a s • f y + b s • g y) t) ∧
        HasDerivAt
          (normalizedKineticEnergy (fun s y => a s • f y + b s • g y))
          (-(coordinateEnergyDissipationRate (fun s y => a s • f y + b s • g y) ν t)) t := by
  exact
    meaningfulCoordinateEnergyDissipationIdentity_smooth_of_boundedKineticEnergy
      (u := fun s y => a s • f y + b s • g y)
      (p := p)
      (ν := ν)
      (boundedKineticEnergy_of_add_scalar_smul_schwartz_of_abs_le a b f g A B haBound hbBound)
      (EnergyDerivativeFormula_of_add_scalar_smul_schwartz a a' b b' f g ha hb)
      heq
      hintegrable
      (CoordinateViscousEnergyPairingFormula_of_add_scalar_smul_schwartz a b f g)
      hboundary
      hnonlinear

/-- The repaired bounded-energy coordinate energy identity for a two-profile
Schwartz superposition no longer needs a separate nonlinear-cancellation
hypothesis once both profiles are divergence-free in the standard coordinates
of `ℝ^3`. -/
theorem meaningfulCoordinateEnergyDissipationIdentity_smooth_of_add_scalar_smul_schwartz_of_abs_le_of_divergenceFree
    (a a' b b' : ℝ → ℝ) (f g : 𝓢(NSSpace, NSSpace)) (A B : ℝ)
    (p : NSPressureField) (ν : ℝ)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (ha : ∀ t, HasDerivAt a (a' t) t)
    (hb : ∀ t, HasDerivAt b (b' t) t)
    (heq : ∀ t x,
      timeVelocityDerivative (fun s y => a s • f y + b s • g y) t x +
          spatialConvection (fun s y => a s • f y + b s • g y) t x +
          spatialPressureGradient p t x =
        (ν : ℝ) • spatialLaplacian (fun s y => a s • f y + b s • g y) t x)
    (hintegrable :
      EnergyPairingIntegrable (fun s y => a s • f y + b s • g y) p)
    (hboundary :
      ∀ t,
        ∫ x, pressureEnergyPairing (fun s y => a s • f y + b s • g y) p t x ∂volume = 0)
    (hfdiv : ∀ x,
      ∑ i : Fin 3, (∂_{EuclideanSpace.single i (1 : ℝ)} f x) i = 0)
    (hgdiv : ∀ x,
      ∑ i : Fin 3, (∂_{EuclideanSpace.single i (1 : ℝ)} g x) i = 0) :
    ∀ t,
      MeasureTheory.Integrable
          (kineticEnergyDensity (fun s y => a s • f y + b s • g y) t) ∧
        HasDerivAt
          (normalizedKineticEnergy (fun s y => a s • f y + b s • g y))
          (-(coordinateEnergyDissipationRate (fun s y => a s • f y + b s • g y) ν t)) t := by
  exact
    meaningfulCoordinateEnergyDissipationIdentity_smooth_of_add_scalar_smul_schwartz_of_abs_le
      a a' b b' f g A B p ν haBound hbBound ha hb heq hintegrable hboundary
      (integral_convectionEnergyPairing_of_add_scalar_smul_schwartz_of_divergenceFree
        a b f g hfdiv hgdiv)

/-- The two-profile Schwartz energy theorem needs only pressure-pairing
integrability as an extra hypothesis: the viscous and convection pairings are
automatically integrable on this concrete class. -/
theorem meaningfulCoordinateEnergyDissipationIdentity_smooth_of_add_scalar_smul_schwartz_of_abs_le_of_divergenceFree_of_pressureIntegrable
    (a a' b b' : ℝ → ℝ) (f g : 𝓢(NSSpace, NSSpace)) (A B : ℝ)
    (p : NSPressureField) (ν : ℝ)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (ha : ∀ t, HasDerivAt a (a' t) t)
    (hb : ∀ t, HasDerivAt b (b' t) t)
    (heq : ∀ t x,
      timeVelocityDerivative (fun s y => a s • f y + b s • g y) t x +
          spatialConvection (fun s y => a s • f y + b s • g y) t x +
          spatialPressureGradient p t x =
        (ν : ℝ) • spatialLaplacian (fun s y => a s • f y + b s • g y) t x)
    (hpressureIntegrable :
      ∀ t,
        Integrable (pressureEnergyPairing (fun s y => a s • f y + b s • g y) p t))
    (hboundary :
      ∀ t,
        ∫ x, pressureEnergyPairing (fun s y => a s • f y + b s • g y) p t x ∂volume = 0)
    (hfdiv : ∀ x,
      ∑ i : Fin 3, (∂_{EuclideanSpace.single i (1 : ℝ)} f x) i = 0)
    (hgdiv : ∀ x,
      ∑ i : Fin 3, (∂_{EuclideanSpace.single i (1 : ℝ)} g x) i = 0) :
    ∀ t,
      MeasureTheory.Integrable
          (kineticEnergyDensity (fun s y => a s • f y + b s • g y) t) ∧
        HasDerivAt
          (normalizedKineticEnergy (fun s y => a s • f y + b s • g y))
          (-(coordinateEnergyDissipationRate (fun s y => a s • f y + b s • g y) ν t)) t := by
  have hintegrable :
      EnergyPairingIntegrable (fun s y => a s • f y + b s • g y) p := by
    intro t
    refine ⟨?_, ?_, hpressureIntegrable t⟩
    · exact
        integrable_laplacianEnergyPairing_of_schwartzSlice
          (u := fun s y => a s • f y + b s • g y)
          (t := t)
          (f := (a t) • f + (b t) • g)
          (hslice := by intro x; rfl)
    · exact
        integrable_convectionEnergyPairing_of_schwartzSlice
          (u := fun s y => a s • f y + b s • g y)
          (t := t)
          (f := (a t) • f + (b t) • g)
          (hslice := by intro x; rfl)
  exact
    meaningfulCoordinateEnergyDissipationIdentity_smooth_of_add_scalar_smul_schwartz_of_abs_le_of_divergenceFree
      a a' b b' f g A B p ν haBound hbBound ha hb heq hintegrable hboundary hfdiv hgdiv

/-- The two-profile Schwartz energy theorem only needs the combined velocity
field to be divergence-free on each time slice; it does not require separate
profilewise divergence hypotheses. -/
theorem meaningfulCoordinateEnergyDissipationIdentity_smooth_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_of_pressureIntegrable
    (a a' b b' : ℝ → ℝ) (f g : 𝓢(NSSpace, NSSpace)) (A B : ℝ)
    (p : NSPressureField) (ν : ℝ)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (ha : ∀ t, HasDerivAt a (a' t) t)
    (hb : ∀ t, HasDerivAt b (b' t) t)
    (heq : ∀ t x,
      timeVelocityDerivative (fun s y => a s • f y + b s • g y) t x +
          spatialConvection (fun s y => a s • f y + b s • g y) t x +
          spatialPressureGradient p t x =
        (ν : ℝ) • spatialLaplacian (fun s y => a s • f y + b s • g y) t x)
    (hpressureIntegrable :
      ∀ t,
        Integrable (pressureEnergyPairing (fun s y => a s • f y + b s • g y) p t))
    (hboundary :
      ∀ t,
        ∫ x, pressureEnergyPairing (fun s y => a s • f y + b s • g y) p t x ∂volume = 0)
    (hdiv :
      ∀ t x,
        spatialDivergence (fun s y => a s • f y + b s • g y) t x = 0) :
    ∀ t,
      MeasureTheory.Integrable
          (kineticEnergyDensity (fun s y => a s • f y + b s • g y) t) ∧
        HasDerivAt
          (normalizedKineticEnergy (fun s y => a s • f y + b s • g y))
          (-(coordinateEnergyDissipationRate (fun s y => a s • f y + b s • g y) ν t)) t := by
  have hintegrable :
      EnergyPairingIntegrable (fun s y => a s • f y + b s • g y) p := by
    intro t
    refine ⟨?_, ?_, hpressureIntegrable t⟩
    · exact
        integrable_laplacianEnergyPairing_of_schwartzSlice
          (u := fun s y => a s • f y + b s • g y)
          (t := t)
          (f := (a t) • f + (b t) • g)
          (hslice := by intro x; rfl)
    · exact
        integrable_convectionEnergyPairing_of_schwartzSlice
          (u := fun s y => a s • f y + b s • g y)
          (t := t)
          (f := (a t) • f + (b t) • g)
          (hslice := by intro x; rfl)
  exact
    meaningfulCoordinateEnergyDissipationIdentity_smooth_of_add_scalar_smul_schwartz_of_abs_le
      a a' b b' f g A B p ν haBound hbBound ha hb heq hintegrable hboundary
      (integral_convectionEnergyPairing_of_add_scalar_smul_schwartz_of_spatialDivergence_zero
        a b f g hdiv)

/-- The corrected two-profile coordinate energy identity closes completely for
the concrete class with slice-wise divergence-free flow and a time-only
pressure gauge. -/
theorem meaningfulCoordinateEnergyDissipationIdentity_smooth_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_timeOnlyPressure
    (a a' b b' : ℝ → ℝ) (f g : 𝓢(NSSpace, NSSpace)) (A B : ℝ)
    (π : NSTime → ℝ) (ν : ℝ)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (ha : ∀ t, HasDerivAt a (a' t) t)
    (hb : ∀ t, HasDerivAt b (b' t) t)
    (heq : ∀ t x,
      timeVelocityDerivative (fun s y => a s • f y + b s • g y) t x +
          spatialConvection (fun s y => a s • f y + b s • g y) t x +
          spatialPressureGradient (fun s : NSTime => fun _ : NSSpace => π s) t x =
        (ν : ℝ) • spatialLaplacian (fun s y => a s • f y + b s • g y) t x)
    (hdiv :
      ∀ t x,
        spatialDivergence (fun s y => a s • f y + b s • g y) t x = 0) :
    ∀ t,
      MeasureTheory.Integrable
          (kineticEnergyDensity (fun s y => a s • f y + b s • g y) t) ∧
        HasDerivAt
          (normalizedKineticEnergy (fun s y => a s • f y + b s • g y))
          (-(coordinateEnergyDissipationRate (fun s y => a s • f y + b s • g y) ν t)) t := by
  exact
    meaningfulCoordinateEnergyDissipationIdentity_smooth_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_of_pressureIntegrable
      a a' b b' f g A B (fun s : NSTime => fun _ : NSSpace => π s) ν
      haBound hbBound ha hb heq
      (by
        intro t
        rw [pressureEnergyPairing_timeOnly]
        exact integrable_zero NSSpace ℝ (volume : Measure NSSpace))
      (by
        intro t
        rw [pressureEnergyPairing_timeOnly]
        simp)
      hdiv

/-- The corrected two-profile coordinate energy identity also closes for the
coordinate-linear pressure gauge `p(t,x) = c * x₀` under slice-wise
divergence-free flow. On this Schwartz class, the needed zero-mean condition on
the pressured component is derived internally from the divergence-free
hypothesis. -/
theorem meaningfulCoordinateEnergyDissipationIdentity_smooth_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_coord0LinearPressure
    (a a' b b' : ℝ → ℝ) (f g : 𝓢(NSSpace, NSSpace)) (A B c : ℝ)
    (ν : ℝ)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (ha : ∀ t, HasDerivAt a (a' t) t)
    (hb : ∀ t, HasDerivAt b (b' t) t)
    (heq : ∀ t x,
      timeVelocityDerivative (fun s y => a s • f y + b s • g y) t x +
          spatialConvection (fun s y => a s • f y + b s • g y) t x +
          spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => c * y nsCoord0) t x =
        (ν : ℝ) • spatialLaplacian (fun s y => a s • f y + b s • g y) t x)
    (hdiv :
      ∀ t x,
        spatialDivergence (fun s y => a s • f y + b s • g y) t x = 0) :
    ∀ t,
      MeasureTheory.Integrable
          (kineticEnergyDensity (fun s y => a s • f y + b s • g y) t) ∧
        HasDerivAt
          (normalizedKineticEnergy (fun s y => a s • f y + b s • g y))
          (-(coordinateEnergyDissipationRate (fun s y => a s • f y + b s • g y) ν t)) t := by
  exact
    meaningfulCoordinateEnergyDissipationIdentity_smooth_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_of_pressureIntegrable
      a a' b b' f g A B (fun _ : NSTime => fun y : NSSpace => c * y nsCoord0) ν
      haBound hbBound ha hb heq
      (by
        intro t
        let coord0 :
            𝓢(NSSpace, ℝ) :=
          SchwartzMap.bilinLeftCLM
            (ContinuousLinearMap.apply ℝ ℝ)
            (g := fun _ : NSSpace => (EuclideanSpace.proj nsCoord0 : NSSpace →L[ℝ] ℝ))
            (by fun_prop)
            ((a t) • f + (b t) • g)
        have hcoord :
            (fun x : NSSpace => c * ((a t) • f x + (b t) • g x) nsCoord0) =
              fun x : NSSpace => c * coord0 x := by
          funext x
          simp [coord0, SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.apply_apply]
        have hpair :
            pressureEnergyPairing
                (fun s y => a s • f y + b s • g y)
                (fun _ : NSTime => fun y : NSSpace => c * y nsCoord0) t =
              fun x : NSSpace => c * coord0 x := by
          rw [pressureEnergyPairing_coord0Linear]
          exact hcoord
        rw [hpair]
        exact coord0.integrable.const_mul c)
      (by
        intro t
        rw [pressureEnergyPairing_coord0Linear]
        rw [integral_const_mul]
        rw [integral_coord0_zero_of_schwartzSlice_of_spatialDivergence_zero
          (u := fun s y => a s • f y + b s • g y)
          (t := t)
          (f := (a t) • f + (b t) • g)
          (hslice := by intro x; rfl)
          (hdiv := by intro x; exact hdiv t x)]
        simp)
      hdiv

/-- The corrected two-profile coordinate energy identity closes for every
time-independent linear pressure gauge `p(t,x) = ⟪c, x⟫` under slice-wise
divergence-free flow. The needed boundary cancellation is discharged
coordinatewise from the divergence-free Schwartz slice theorem. -/
theorem meaningfulCoordinateEnergyDissipationIdentity_smooth_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_linearPressure
    (a a' b b' : ℝ → ℝ) (f g : 𝓢(NSSpace, NSSpace)) (A B : ℝ)
    (c : NSSpace) (ν : ℝ)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (ha : ∀ t, HasDerivAt a (a' t) t)
    (hb : ∀ t, HasDerivAt b (b' t) t)
    (heq : ∀ t x,
      timeVelocityDerivative (fun s y => a s • f y + b s • g y) t x +
          spatialConvection (fun s y => a s • f y + b s • g y) t x +
          spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => ⟪c, y⟫) t x =
        (ν : ℝ) • spatialLaplacian (fun s y => a s • f y + b s • g y) t x)
    (hdiv :
      ∀ t x,
        spatialDivergence (fun s y => a s • f y + b s • g y) t x = 0) :
    ∀ t,
      MeasureTheory.Integrable
          (kineticEnergyDensity (fun s y => a s • f y + b s • g y) t) ∧
        HasDerivAt
          (normalizedKineticEnergy (fun s y => a s • f y + b s • g y))
          (-(coordinateEnergyDissipationRate (fun s y => a s • f y + b s • g y) ν t)) t := by
  exact
    meaningfulCoordinateEnergyDissipationIdentity_smooth_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_of_pressureIntegrable
      a a' b b' f g A B (fun _ : NSTime => fun y : NSSpace => ⟪c, y⟫) ν
      haBound hbBound ha hb heq
      (by
        intro t
        exact
          integrable_pressureEnergyPairing_linear_of_schwartzSlice
            (u := fun s y => a s • f y + b s • g y)
            (t := t)
            (f := (a t) • f + (b t) • g)
            (c := c)
            (hslice := by intro x; rfl))
      (by
        intro t
        exact
          integral_pressureEnergyPairing_linear_of_schwartzSlice_of_spatialDivergence_zero
            (u := fun s y => a s • f y + b s • g y)
            (t := t)
            (f := (a t) • f + (b t) • g)
            (c := c)
            (hslice := by intro x; rfl)
            (hdiv := by intro x; exact hdiv t x))
      hdiv

/-- The corrected two-profile coordinate energy identity closes for the full
affine pressure gauge class `p(t,x) = ⟪c(t), x⟫ + π(t)` under slice-wise
divergence-free flow. The time-only part contributes no spatial gradient, and
the linear part cancels coordinatewise from the divergence-free Schwartz slice
theorem. -/
theorem meaningfulCoordinateEnergyDissipationIdentity_smooth_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_affinePressure
    (a a' b b' : ℝ → ℝ) (f g : 𝓢(NSSpace, NSSpace)) (A B : ℝ)
    (c : NSTime → NSSpace) (π : NSTime → ℝ) (ν : ℝ)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (ha : ∀ t, HasDerivAt a (a' t) t)
    (hb : ∀ t, HasDerivAt b (b' t) t)
    (heq : ∀ t x,
      timeVelocityDerivative (fun s y => a s • f y + b s • g y) t x +
          spatialConvection (fun s y => a s • f y + b s • g y) t x +
          spatialPressureGradient (fun s : NSTime => fun y : NSSpace => ⟪c s, y⟫ + π s) t x =
        (ν : ℝ) • spatialLaplacian (fun s y => a s • f y + b s • g y) t x)
    (hdiv :
      ∀ t x,
        spatialDivergence (fun s y => a s • f y + b s • g y) t x = 0) :
    ∀ t,
      MeasureTheory.Integrable
          (kineticEnergyDensity (fun s y => a s • f y + b s • g y) t) ∧
        HasDerivAt
          (normalizedKineticEnergy (fun s y => a s • f y + b s • g y))
          (-(coordinateEnergyDissipationRate (fun s y => a s • f y + b s • g y) ν t)) t := by
  exact
    meaningfulCoordinateEnergyDissipationIdentity_smooth_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_of_pressureIntegrable
      a a' b b' f g A B (fun s : NSTime => fun y : NSSpace => ⟪c s, y⟫ + π s) ν
      haBound hbBound ha hb heq
      (by
        intro t
        rw [pressureEnergyPairing_affine]
        simpa [pressureEnergyPairing_linear] using
          integrable_pressureEnergyPairing_linear_of_schwartzSlice
            (u := fun s y => a s • f y + b s • g y)
            (t := t)
            (f := (a t) • f + (b t) • g)
            (c := c t)
            (hslice := by intro x; rfl))
      (by
        intro t
        rw [pressureEnergyPairing_affine]
        simpa [pressureEnergyPairing_linear] using
          integral_pressureEnergyPairing_linear_of_schwartzSlice_of_spatialDivergence_zero
            (u := fun s y => a s • f y + b s • g y)
            (t := t)
            (f := (a t) • f + (b t) • g)
            (c := c t)
            (hslice := by intro x; rfl)
            (hdiv := by intro x; exact hdiv t x))
      hdiv

/-- The corrected two-profile coordinate energy identity closes for the genuine
non-affine Schwartz pressure class `p(t,x) = ρ(t) * q(x)` under slice-wise
divergence-free flow. The pressure term cancels by coordinatewise integration by
parts against the fixed Schwartz scalar profile `q`. -/
theorem meaningfulCoordinateEnergyDissipationIdentity_smooth_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_scalarSchwartzPressure
    (a a' b b' : ℝ → ℝ) (f g : 𝓢(NSSpace, NSSpace)) (A B : ℝ)
    (ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ)) (ν : ℝ)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (ha : ∀ t, HasDerivAt a (a' t) t)
    (hb : ∀ t, HasDerivAt b (b' t) t)
    (heq : ∀ t x,
      timeVelocityDerivative (fun s y => a s • f y + b s • g y) t x +
          spatialConvection (fun s y => a s • f y + b s • g y) t x +
          spatialPressureGradient (fun s : NSTime => fun y : NSSpace => ρ s * q y) t x =
        (ν : ℝ) • spatialLaplacian (fun s y => a s • f y + b s • g y) t x)
    (hdiv :
      ∀ t x,
        spatialDivergence (fun s y => a s • f y + b s • g y) t x = 0) :
    ∀ t,
      MeasureTheory.Integrable
          (kineticEnergyDensity (fun s y => a s • f y + b s • g y) t) ∧
        HasDerivAt
          (normalizedKineticEnergy (fun s y => a s • f y + b s • g y))
          (-(coordinateEnergyDissipationRate (fun s y => a s • f y + b s • g y) ν t)) t := by
  exact
    meaningfulCoordinateEnergyDissipationIdentity_smooth_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_of_pressureIntegrable
      a a' b b' f g A B (fun s : NSTime => fun y : NSSpace => ρ s * q y) ν
      haBound hbBound ha hb heq
      (by
        intro t
        exact
          integrable_pressureEnergyPairing_of_schwartzSlice_scalarSchwartzPressure
            (u := fun s y => a s • f y + b s • g y)
            (t := t)
            (f := (a t) • f + (b t) • g)
            (ρ := ρ)
            (q := q)
            (hslice := by intro x; rfl))
      (by
        intro t
        exact
          integral_pressureEnergyPairing_of_schwartzSlice_scalarSchwartzPressure_of_spatialDivergence_zero
            (u := fun s y => a s • f y + b s • g y)
            (t := t)
            (f := (a t) • f + (b t) • g)
            (ρ := ρ)
            (q := q)
            (hslice := by intro x; rfl)
            (hdiv := by intro x; exact hdiv t x))
      hdiv

/-- The corrected two-profile coordinate energy identity closes for the
combined pressure class consisting of an affine gauge plus a localized Schwartz
pressure profile. This packages the affine cancellation and the Schwartz
integration-by-parts cancellation on the same concrete `ℝ × ℝ^3` surface. -/
theorem meaningfulCoordinateEnergyDissipationIdentity_smooth_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_affine_add_scalarSchwartzPressure
    (a a' b b' : ℝ → ℝ) (f g : 𝓢(NSSpace, NSSpace)) (A B : ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ)) (ν : ℝ)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (ha : ∀ t, HasDerivAt a (a' t) t)
    (hb : ∀ t, HasDerivAt b (b' t) t)
    (heq : ∀ t x,
      timeVelocityDerivative (fun s y => a s • f y + b s • g y) t x +
          spatialConvection (fun s y => a s • f y + b s • g y) t x +
          spatialPressureGradient
            ((fun s : NSTime => fun y : NSSpace => ⟪c s, y⟫ + π s) +
              fun s : NSTime => fun y : NSSpace => ρ s * q y) t x =
        (ν : ℝ) • spatialLaplacian (fun s y => a s • f y + b s • g y) t x)
    (hdiv :
      ∀ t x,
        spatialDivergence (fun s y => a s • f y + b s • g y) t x = 0) :
    ∀ t,
      MeasureTheory.Integrable
          (kineticEnergyDensity (fun s y => a s • f y + b s • g y) t) ∧
        HasDerivAt
          (normalizedKineticEnergy (fun s y => a s • f y + b s • g y))
          (-(coordinateEnergyDissipationRate (fun s y => a s • f y + b s • g y) ν t)) t := by
  let u : NSVelocityField := fun s y => a s • f y + b s • g y
  let pAffine : NSPressureField := fun s : NSTime => fun y : NSSpace => ⟪c s, y⟫ + π s
  let pSchwartz : NSPressureField := fun s : NSTime => fun y : NSSpace => ρ s * q y
  have hpAffineDiff (t : NSTime) :
      ∀ x, DifferentiableAt ℝ (fun y : NSSpace => pAffine t y) x := by
    intro x
    have hderiv :
        HasFDerivAt (fun y : NSSpace => ⟪c t, y⟫ + π t)
          ((InnerProductSpace.toDual ℝ NSSpace) (c t)) x := by
      simpa [InnerProductSpace.toDual_apply_apply, real_inner_comm] using
        ((((InnerProductSpace.toDual ℝ NSSpace) (c t))).hasFDerivAt).add_const (π t)
    exact hderiv.differentiableAt
  have hpSchwartzDiff (t : NSTime) :
      ∀ x, DifferentiableAt ℝ (fun y : NSSpace => pSchwartz t y) x := by
    intro x
    exact (q.differentiableAt.const_mul (ρ t))
  exact
    meaningfulCoordinateEnergyDissipationIdentity_smooth_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_of_pressureIntegrable
      a a' b b' f g A B (pAffine + pSchwartz) ν
      haBound hbBound ha hb
      (by
        intro t x
        simpa [u, pAffine, pSchwartz] using heq t x)
      (by
        intro t
        have hPairAdd :
            pressureEnergyPairing u (pAffine + pSchwartz) t =
              fun x : NSSpace =>
                pressureEnergyPairing u pAffine t x +
                  pressureEnergyPairing u pSchwartz t x :=
          pressureEnergyPairing_add u t (hpAffineDiff t) (hpSchwartzDiff t)
        have hAffineInt :
            Integrable (pressureEnergyPairing u pAffine t) := by
          rw [pressureEnergyPairing_affine]
          simpa [pressureEnergyPairing_linear, u, pAffine] using
            integrable_pressureEnergyPairing_linear_of_schwartzSlice
              (u := u)
              (t := t)
              (f := (a t) • f + (b t) • g)
              (c := c t)
              (hslice := by intro x; rfl)
        have hSchwartzInt :
            Integrable (pressureEnergyPairing u pSchwartz t) :=
          integrable_pressureEnergyPairing_of_schwartzSlice_scalarSchwartzPressure
            (u := u)
            (t := t)
            (f := (a t) • f + (b t) • g)
            (ρ := ρ)
            (q := q)
            (hslice := by intro x; rfl)
        rw [hPairAdd]
        exact hAffineInt.add hSchwartzInt)
      (by
        intro t
        have hPairAdd :
            pressureEnergyPairing u (pAffine + pSchwartz) t =
              fun x : NSSpace =>
                pressureEnergyPairing u pAffine t x +
                  pressureEnergyPairing u pSchwartz t x :=
          pressureEnergyPairing_add u t (hpAffineDiff t) (hpSchwartzDiff t)
        have hAffineInt :
            Integrable (pressureEnergyPairing u pAffine t) := by
          rw [pressureEnergyPairing_affine]
          simpa [pressureEnergyPairing_linear, u, pAffine] using
            integrable_pressureEnergyPairing_linear_of_schwartzSlice
              (u := u)
              (t := t)
              (f := (a t) • f + (b t) • g)
              (c := c t)
              (hslice := by intro x; rfl)
        have hSchwartzInt :
            Integrable (pressureEnergyPairing u pSchwartz t) :=
          integrable_pressureEnergyPairing_of_schwartzSlice_scalarSchwartzPressure
            (u := u)
            (t := t)
            (f := (a t) • f + (b t) • g)
            (ρ := ρ)
            (q := q)
            (hslice := by intro x; rfl)
        have hAffineIntegral :
            ∫ x, pressureEnergyPairing u pAffine t x ∂volume = 0 := by
          rw [pressureEnergyPairing_affine]
          simpa [pressureEnergyPairing_linear, u, pAffine] using
            integral_pressureEnergyPairing_linear_of_schwartzSlice_of_spatialDivergence_zero
              (u := u)
              (t := t)
              (f := (a t) • f + (b t) • g)
              (c := c t)
              (hslice := by intro x; rfl)
              (hdiv := by intro x; exact hdiv t x)
        have hSchwartzIntegral :
            ∫ x, pressureEnergyPairing u pSchwartz t x ∂volume = 0 :=
          integral_pressureEnergyPairing_of_schwartzSlice_scalarSchwartzPressure_of_spatialDivergence_zero
            (u := u)
            (t := t)
            (f := (a t) • f + (b t) • g)
            (ρ := ρ)
            (q := q)
            (hslice := by intro x; rfl)
            (hdiv := by intro x; exact hdiv t x)
        rw [hPairAdd]
        rw [integral_add hAffineInt hSchwartzInt, hAffineIntegral, hSchwartzIntegral]
        simp)
      (by
        intro t x
        simpa [u] using hdiv t x)

/-- Energy-inequality form for the concrete bounded two-profile Schwartz class
with affine plus localized Schwartz pressure: under nonnegative viscosity, the
normalized kinetic energy is antitone in time. -/
theorem normalizedKineticEnergy_antitone_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_affine_add_scalarSchwartzPressure
    (a a' b b' : ℝ → ℝ) (f g : 𝓢(NSSpace, NSSpace)) (A B : ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ)) {ν : ℝ}
    (hν : 0 ≤ ν)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (ha : ∀ t, HasDerivAt a (a' t) t)
    (hb : ∀ t, HasDerivAt b (b' t) t)
    (heq : ∀ t x,
      timeVelocityDerivative (fun s y => a s • f y + b s • g y) t x +
          spatialConvection (fun s y => a s • f y + b s • g y) t x +
          spatialPressureGradient
            ((fun s : NSTime => fun y : NSSpace => ⟪c s, y⟫ + π s) +
              fun s : NSTime => fun y : NSSpace => ρ s * q y) t x =
        (ν : ℝ) • spatialLaplacian (fun s y => a s • f y + b s • g y) t x)
    (hdiv :
      ∀ t x,
        spatialDivergence (fun s y => a s • f y + b s • g y) t x = 0) :
    Antitone (normalizedKineticEnergy (fun s y => a s • f y + b s • g y)) := by
  refine
    antitone_of_hasDerivAt_nonpos
      (f' := fun t =>
        -(coordinateEnergyDissipationRate (fun s y => a s • f y + b s • g y) ν t))
      ?_ ?_
  · intro t
    exact
      (meaningfulCoordinateEnergyDissipationIdentity_smooth_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_affine_add_scalarSchwartzPressure
        a a' b b' f g A B c π ρ q ν haBound hbBound ha hb heq hdiv t).2
  · intro t
    exact
      neg_coordinateEnergyDissipationRate_nonpos
        (fun s y => a s • f y + b s • g y) hν t

/-- Two-time energy inequality for the concrete bounded two-profile Schwartz
class with affine plus localized Schwartz pressure. -/
theorem normalizedKineticEnergy_between_zero_and_initial_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_affine_add_scalarSchwartzPressure
    (a a' b b' : ℝ → ℝ) (f g : 𝓢(NSSpace, NSSpace)) (A B : ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ)) {ν : ℝ}
    (hν : 0 ≤ ν)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (ha : ∀ t, HasDerivAt a (a' t) t)
    (hb : ∀ t, HasDerivAt b (b' t) t)
    (heq : ∀ t x,
      timeVelocityDerivative (fun s y => a s • f y + b s • g y) t x +
          spatialConvection (fun s y => a s • f y + b s • g y) t x +
          spatialPressureGradient
            ((fun s : NSTime => fun y : NSSpace => ⟪c s, y⟫ + π s) +
              fun s : NSTime => fun y : NSSpace => ρ s * q y) t x =
        (ν : ℝ) • spatialLaplacian (fun s y => a s • f y + b s • g y) t x)
    (hdiv :
      ∀ t x,
        spatialDivergence (fun s y => a s • f y + b s • g y) t x = 0)
    {t₀ t₁ : NSTime} (ht : t₀ ≤ t₁) :
    0 ≤ normalizedKineticEnergy (fun s y => a s • f y + b s • g y) t₁ ∧
      normalizedKineticEnergy (fun s y => a s • f y + b s • g y) t₁ ≤
        normalizedKineticEnergy (fun s y => a s • f y + b s • g y) t₀ := by
  refine ⟨normalizedKineticEnergy_nonneg _ t₁, ?_⟩
  exact
    (normalizedKineticEnergy_antitone_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_affine_add_scalarSchwartzPressure
      a a' b b' f g A B c π ρ q hν haBound hbBound ha hb heq hdiv) ht

/-- Standard kinetic-energy two-time bound for the concrete bounded
two-profile Schwartz class with affine plus localized Schwartz pressure. -/
theorem kineticEnergyAt_between_zero_and_initial_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_affine_add_scalarSchwartzPressure
    (a a' b b' : ℝ → ℝ) (f g : 𝓢(NSSpace, NSSpace)) (A B : ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ)) {ν : ℝ}
    (hν : 0 ≤ ν)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (ha : ∀ t, HasDerivAt a (a' t) t)
    (hb : ∀ t, HasDerivAt b (b' t) t)
    (heq : ∀ t x,
      timeVelocityDerivative (fun s y => a s • f y + b s • g y) t x +
          spatialConvection (fun s y => a s • f y + b s • g y) t x +
          spatialPressureGradient
            ((fun s : NSTime => fun y : NSSpace => ⟪c s, y⟫ + π s) +
              fun s : NSTime => fun y : NSSpace => ρ s * q y) t x =
        (ν : ℝ) • spatialLaplacian (fun s y => a s • f y + b s • g y) t x)
    (hdiv :
      ∀ t x,
        spatialDivergence (fun s y => a s • f y + b s • g y) t x = 0)
    {t₀ t₁ : NSTime} (ht : t₀ ≤ t₁) :
    0 ≤ kineticEnergyAt (fun s y => a s • f y + b s • g y) t₁ ∧
      kineticEnergyAt (fun s y => a s • f y + b s • g y) t₁ ≤
        kineticEnergyAt (fun s y => a s • f y + b s • g y) t₀ := by
  refine ⟨kineticEnergyAt_nonneg _ t₁, ?_⟩
  have hnorm :
      normalizedKineticEnergy (fun s y => a s • f y + b s • g y) t₁ ≤
        normalizedKineticEnergy (fun s y => a s • f y + b s • g y) t₀ :=
    (normalizedKineticEnergy_antitone_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_affine_add_scalarSchwartzPressure
      a a' b b' f g A B c π ρ q hν haBound hbBound ha hb heq hdiv) ht
  unfold normalizedKineticEnergy at hnorm
  nlinarith

/-- The two-profile Schwartz energy theorem closes completely on the concrete
zero-pressure lane once the profiles are divergence-free. -/
theorem meaningfulCoordinateEnergyDissipationIdentity_smooth_of_add_scalar_smul_schwartz_of_abs_le_of_divergenceFree_zeroPressure
    (a a' b b' : ℝ → ℝ) (f g : 𝓢(NSSpace, NSSpace)) (A B : ℝ)
    (ν : ℝ)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (ha : ∀ t, HasDerivAt a (a' t) t)
    (hb : ∀ t, HasDerivAt b (b' t) t)
    (heq : ∀ t x,
      timeVelocityDerivative (fun s y => a s • f y + b s • g y) t x +
          spatialConvection (fun s y => a s • f y + b s • g y) t x +
          spatialPressureGradient (0 : NSPressureField) t x =
        (ν : ℝ) • spatialLaplacian (fun s y => a s • f y + b s • g y) t x)
    (hfdiv : ∀ x,
      ∑ i : Fin 3, (∂_{EuclideanSpace.single i (1 : ℝ)} f x) i = 0)
    (hgdiv : ∀ x,
      ∑ i : Fin 3, (∂_{EuclideanSpace.single i (1 : ℝ)} g x) i = 0) :
    ∀ t,
      MeasureTheory.Integrable
          (kineticEnergyDensity (fun s y => a s • f y + b s • g y) t) ∧
        HasDerivAt
          (normalizedKineticEnergy (fun s y => a s • f y + b s • g y))
          (-(coordinateEnergyDissipationRate (fun s y => a s • f y + b s • g y) ν t)) t := by
  exact
    meaningfulCoordinateEnergyDissipationIdentity_smooth_of_add_scalar_smul_schwartz_of_abs_le_of_divergenceFree_of_pressureIntegrable
      a a' b b' f g A B (0 : NSPressureField) ν haBound hbBound ha hb heq
      (by
        intro t
        rw [pressureEnergyPairing_zero_right]
        exact integrable_zero NSSpace ℝ (volume : Measure NSSpace))
      (by
        intro t
        rw [pressureEnergyPairing_zero_right]
        simp)
      hfdiv hgdiv

/-- The two-profile Schwartz energy theorem also closes on the standard
time-only pressure gauge class once the profiles are divergence-free. -/
theorem meaningfulCoordinateEnergyDissipationIdentity_smooth_of_add_scalar_smul_schwartz_of_abs_le_of_divergenceFree_timeOnlyPressure
    (a a' b b' : ℝ → ℝ) (f g : 𝓢(NSSpace, NSSpace)) (A B : ℝ)
    (π : NSTime → ℝ) (ν : ℝ)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (ha : ∀ t, HasDerivAt a (a' t) t)
    (hb : ∀ t, HasDerivAt b (b' t) t)
    (heq : ∀ t x,
      timeVelocityDerivative (fun s y => a s • f y + b s • g y) t x +
          spatialConvection (fun s y => a s • f y + b s • g y) t x +
          spatialPressureGradient (fun s : NSTime => fun _ : NSSpace => π s) t x =
        (ν : ℝ) • spatialLaplacian (fun s y => a s • f y + b s • g y) t x)
    (hfdiv : ∀ x,
      ∑ i : Fin 3, (∂_{EuclideanSpace.single i (1 : ℝ)} f x) i = 0)
    (hgdiv : ∀ x,
      ∑ i : Fin 3, (∂_{EuclideanSpace.single i (1 : ℝ)} g x) i = 0) :
    ∀ t,
      MeasureTheory.Integrable
          (kineticEnergyDensity (fun s y => a s • f y + b s • g y) t) ∧
        HasDerivAt
          (normalizedKineticEnergy (fun s y => a s • f y + b s • g y))
          (-(coordinateEnergyDissipationRate (fun s y => a s • f y + b s • g y) ν t)) t := by
  exact
    meaningfulCoordinateEnergyDissipationIdentity_smooth_of_add_scalar_smul_schwartz_of_abs_le_of_divergenceFree_of_pressureIntegrable
      a a' b b' f g A B (fun s : NSTime => fun _ : NSSpace => π s) ν
      haBound hbBound ha hb heq
      (by
        intro t
        rw [pressureEnergyPairing_timeOnly]
        exact integrable_zero NSSpace ℝ (volume : Measure NSSpace))
      (by
        intro t
        rw [pressureEnergyPairing_timeOnly]
        simp)
      hfdiv hgdiv

/-- The zero field has zero normalized kinetic energy on every time slice. -/
theorem normalizedKineticEnergy_zero :
    normalizedKineticEnergy (0 : NSVelocityField) = fun _ : NSTime => 0 := by
  funext t
  simp [normalizedKineticEnergy, kineticEnergyAt, kineticEnergyDensity]

/-- The zero field has zero enstrophy density on every time slice. -/
theorem enstrophyDensity_zero (t : NSTime) :
    enstrophyDensity (0 : NSVelocityField) t = fun _ : NSSpace => 0 := by
  funext x
  rw [enstrophyDensity]
  simp [spatialFDeriv_zero]

/-- The zero field has zero total enstrophy on every time slice. -/
theorem enstrophyAt_zero :
    enstrophyAt (0 : NSVelocityField) = fun _ : NSTime => 0 := by
  funext t
  rw [enstrophyAt, enstrophyDensity_zero]
  simp

/-- The zero field has zero coordinatewise enstrophy density on every time
slice. -/
theorem coordinateEnstrophyDensity_zero (t : NSTime) :
    coordinateEnstrophyDensity (0 : NSVelocityField) t = fun _ : NSSpace => 0 := by
  funext x
  simp [coordinateEnstrophyDensity, spatialFDeriv_zero]

/-- The zero field has zero total coordinatewise enstrophy on every time
slice. -/
theorem coordinateEnstrophyAt_zero :
    coordinateEnstrophyAt (0 : NSVelocityField) = fun _ : NSTime => 0 := by
  funext t
  rw [coordinateEnstrophyAt, coordinateEnstrophyDensity_zero]
  simp

/-- The zero field has zero dissipation rate for every viscosity. -/
theorem energyDissipationRate_zero (ν : ℝ) :
    energyDissipationRate (0 : NSVelocityField) ν = fun _ : NSTime => 0 := by
  funext t
  rw [energyDissipationRate, enstrophyAt_zero]
  simp

/-- The zero field has zero corrected dissipation rate for every viscosity. -/
theorem coordinateEnergyDissipationRate_zero (ν : ℝ) :
    coordinateEnergyDissipationRate (0 : NSVelocityField) ν = fun _ : NSTime => 0 := by
  funext t
  rw [coordinateEnergyDissipationRate, coordinateEnstrophyAt_zero]
  simp

/-- The zero field has zero `u · ∂ₜu` pairing. -/
theorem timeEnergyPairing_zero (t : NSTime) :
    timeEnergyPairing (0 : NSVelocityField) t = fun _ : NSSpace => 0 := by
  funext x
  simp [timeEnergyPairing]

/-- The zero field has zero nonlinear energy pairing. -/
theorem convectionEnergyPairing_zero (t : NSTime) :
    convectionEnergyPairing (0 : NSVelocityField) t = fun _ : NSSpace => 0 := by
  funext x
  simp [convectionEnergyPairing]

/-- The zero field has zero pressure pairing against any pressure field. -/
theorem pressureEnergyPairing_zero_left (p : NSPressureField) (t : NSTime) :
    pressureEnergyPairing (0 : NSVelocityField) p t = fun _ : NSSpace => 0 := by
  funext x
  simp [pressureEnergyPairing]

/-- The zero field has zero viscous energy pairing. -/
theorem laplacianEnergyPairing_zero (t : NSTime) :
    laplacianEnergyPairing (0 : NSVelocityField) t = fun _ : NSSpace => 0 := by
  funext x
  have hLaplacian :
      spatialLaplacian (0 : NSVelocityField) t x = 0 := by
    simpa [constantVelocityField] using
      spatialLaplacian_constantVelocityField (0 : NSSpace) t x
  simp [laplacianEnergyPairing, hLaplacian]

/-- The derivative-under-the-integral seam holds on the concrete zero solution. -/
theorem EnergyDerivativeFormula_zero :
    EnergyDerivativeFormula (0 : NSVelocityField) := by
  intro t
  rw [normalizedKineticEnergy_zero]
  have hPairIntegral : ∫ x, timeEnergyPairing (0 : NSVelocityField) t x ∂volume = 0 := by
    rw [timeEnergyPairing_zero]
    simp
  rw [hPairIntegral]
  simpa using (hasDerivAt_const t (0 : ℝ))

/-- The viscous integration-by-parts seam holds trivially on the zero solution.
-/
theorem ViscousEnergyPairingFormula_zero :
    ViscousEnergyPairingFormula (0 : NSVelocityField) := by
  intro t
  rw [laplacianEnergyPairing_zero, enstrophyAt_zero]
  simp

/-- The corrected viscous integration-by-parts seam holds trivially on the zero
solution. -/
theorem CoordinateViscousEnergyPairingFormula_zero :
    CoordinateViscousEnergyPairingFormula (0 : NSVelocityField) := by
  intro t
  rw [laplacianEnergyPairing_zero, coordinateEnstrophyAt_zero]
  simp

/-- All three space pairings are integrable on the zero velocity / zero pressure
baseline. -/
theorem EnergyPairingIntegrable_zero :
    EnergyPairingIntegrable (0 : NSVelocityField) (0 : NSPressureField) := by
  intro t
  constructor
  · rw [laplacianEnergyPairing_zero]
    exact integrable_zero NSSpace ℝ (volume : Measure NSSpace)
  constructor
  · rw [convectionEnergyPairing_zero]
    exact integrable_zero NSSpace ℝ (volume : Measure NSSpace)
  · rw [pressureEnergyPairing_zero_left (0 : NSPressureField)]
    exact integrable_zero NSSpace ℝ (volume : Measure NSSpace)

/-- Concrete baseline: the smooth zero solution satisfies the energy
dissipation identity for every viscosity. This pairs the theorem-level energy
reduction with an actual bottom-up Navier-Stokes solution on `ℝ × ℝ^3`. -/
theorem energyDissipationIdentity_smooth_zero (ν : ℝ) :
    ∀ t,
      HasDerivAt (normalizedKineticEnergy (0 : NSVelocityField))
        (-(energyDissipationRate (0 : NSVelocityField) ν t)) t := by
  exact
    energyDissipationIdentity_smooth
      (u := (0 : NSVelocityField))
      (p := (0 : NSPressureField))
      (ν := ν)
      EnergyDerivativeFormula_zero
      (fun t x => momentumEquation_zeroVelocityField_zeroPressure ν t x)
      EnergyPairingIntegrable_zero
      (by
        intro t
        rw [laplacianEnergyPairing_zero, enstrophyAt_zero]
        simp)
      (by
        intro t
        rw [pressureEnergyPairing_zero_left (0 : NSPressureField)]
        simp)
      (by
        intro t
        rw [convectionEnergyPairing_zero]
        simp)

/-- Concrete corrected baseline: the smooth zero solution satisfies the
coordinatewise energy dissipation identity for every viscosity. -/
theorem coordinateEnergyDissipationIdentity_smooth_zero (ν : ℝ) :
    ∀ t,
      HasDerivAt (normalizedKineticEnergy (0 : NSVelocityField))
        (-(coordinateEnergyDissipationRate (0 : NSVelocityField) ν t)) t := by
  exact
    coordinateEnergyDissipationIdentity_smooth
      (u := (0 : NSVelocityField))
      (p := (0 : NSPressureField))
      (ν := ν)
      EnergyDerivativeFormula_zero
      (fun t x => momentumEquation_zeroVelocityField_zeroPressure ν t x)
      EnergyPairingIntegrable_zero
      CoordinateViscousEnergyPairingFormula_zero
      (by
        intro t
        rw [pressureEnergyPairing_zero_left (0 : NSPressureField)]
        simp)
      (by
        intro t
        rw [convectionEnergyPairing_zero]
        simp)

/-- The zero solution satisfies the repaired bounded-energy guarded coordinate
energy identity. -/
theorem meaningfulCoordinateEnergyDissipationIdentity_smooth_zero (ν : ℝ) :
    ∀ t,
      MeasureTheory.Integrable (kineticEnergyDensity (0 : NSVelocityField) t) ∧
        HasDerivAt (normalizedKineticEnergy (0 : NSVelocityField))
          (-(coordinateEnergyDissipationRate (0 : NSVelocityField) ν t)) t := by
  have henergy : boundedKineticEnergy (0 : NSVelocityField) := by
    refine ⟨0, le_rfl, ?_⟩
    intro t
    constructor
    · have hzeroDensity : kineticEnergyDensity (0 : NSVelocityField) t = fun _ : NSSpace => 0 := by
        funext x
        simp [kineticEnergyDensity]
      rw [hzeroDensity]
      exact integrable_zero NSSpace ℝ (volume : Measure NSSpace)
    · simp [kineticEnergyAt, kineticEnergyDensity]
  exact
    meaningfulCoordinateEnergyDissipationIdentity_smooth_of_boundedKineticEnergy
      (u := (0 : NSVelocityField))
      (p := (0 : NSPressureField))
      (ν := ν)
      henergy
      EnergyDerivativeFormula_zero
      (fun t x => momentumEquation_zeroVelocityField_zeroPressure ν t x)
      EnergyPairingIntegrable_zero
      CoordinateViscousEnergyPairingFormula_zero
      (by
        intro t
        rw [pressureEnergyPairing_zero_left (0 : NSPressureField)]
        simp)
      (by
        intro t
        rw [convectionEnergyPairing_zero]
        simp)

/-- A nonzero constant velocity field is not spatially integrable on `ℝ^3`
with respect to the kinetic-energy density. This is the concrete obstruction
behind the vacuous energy identity phenomenon for unguarded `∫`-based
statements. -/
theorem not_integrable_kineticEnergyDensity_constantVelocityField_of_ne_zero
    {c : NSSpace} (hc : c ≠ 0) (t : NSTime) :
    ¬ MeasureTheory.Integrable (kineticEnergyDensity (constantVelocityField c) t) := by
  have hconst : (‖c‖ ^ (2 : ℕ) : ℝ) ≠ 0 := by
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hc)
  have hnotfinite :
      ¬ MeasureTheory.IsFiniteMeasure (MeasureTheory.volume : MeasureTheory.Measure NSSpace) := by
    rw [MeasureTheory.not_isFiniteMeasure_iff]
    exact MeasureTheory.measure_univ_of_isAddLeftInvariant
      (μ := (MeasureTheory.volume : MeasureTheory.Measure NSSpace))
  intro hInt
  have hfinite :
      MeasureTheory.IsFiniteMeasure (MeasureTheory.volume : MeasureTheory.Measure NSSpace) := by
    have hEq :
        kineticEnergyDensity (constantVelocityField c) t = fun _ : NSSpace => ‖c‖ ^ (2 : ℕ) := by
      funext x
      simp [kineticEnergyDensity, constantVelocityField]
    rw [hEq] at hInt
    exact (MeasureTheory.integrable_const_iff_isFiniteMeasure hconst).mp hInt
  exact hnotfinite hfinite

/-- The concrete spatial kinetic energy of a constant velocity field collapses
to `0` because the integral is undefined on nonintegrable nonzero slices and
therefore evaluates to `0` in mathlib's Bochner integral. -/
theorem kineticEnergyAt_constantVelocityField
    (c : NSSpace) :
    kineticEnergyAt (constantVelocityField c) = fun _ : NSTime => 0 := by
  funext t
  by_cases hc : c = 0
  · subst hc
    simp [kineticEnergyAt, kineticEnergyDensity, constantVelocityField]
  · rw [kineticEnergyAt]
    exact MeasureTheory.integral_undef
      (not_integrable_kineticEnergyDensity_constantVelocityField_of_ne_zero hc t)

/-- The normalized kinetic energy of any constant velocity field is identically
zero on the current unguarded concrete NS surface. -/
theorem normalizedKineticEnergy_constantVelocityField
    (c : NSSpace) :
    normalizedKineticEnergy (constantVelocityField c) = fun _ : NSTime => 0 := by
  funext t
  rw [normalizedKineticEnergy, kineticEnergyAt_constantVelocityField]
  simp

/-- The coordinatewise enstrophy density of a constant velocity field is zero on
every time slice. -/
theorem coordinateEnstrophyDensity_constantVelocityField_zero
    (c : NSSpace) (t : NSTime) :
    coordinateEnstrophyDensity (constantVelocityField c) t = fun _ : NSSpace => 0 := by
  funext x
  simp [coordinateEnstrophyDensity, spatialFDeriv_constantVelocityField]

/-- Constant velocity fields have zero total coordinatewise enstrophy. -/
theorem coordinateEnstrophyAt_constantVelocityField_zero
    (c : NSSpace) :
    coordinateEnstrophyAt (constantVelocityField c) = fun _ : NSTime => 0 := by
  funext t
  rw [coordinateEnstrophyAt, coordinateEnstrophyDensity_constantVelocityField_zero]
  simp

/-- Constant velocity fields have zero corrected dissipation rate. -/
theorem coordinateEnergyDissipationRate_constantVelocityField_zero
    (c : NSSpace) (ν : ℝ) :
    coordinateEnergyDissipationRate (constantVelocityField c) ν = fun _ : NSTime => 0 := by
  funext t
  rw [coordinateEnergyDissipationRate, coordinateEnstrophyAt_constantVelocityField_zero]
  simp

/-- The time energy pairing of a constant velocity field vanishes. -/
theorem timeEnergyPairing_constantVelocityField_zero
    (c : NSSpace) (t : NSTime) :
    timeEnergyPairing (constantVelocityField c) t = fun _ : NSSpace => 0 := by
  funext x
  simp [timeEnergyPairing, timeVelocityDerivative_constantVelocityField]

/-- The convection energy pairing of a constant velocity field vanishes. -/
theorem convectionEnergyPairing_constantVelocityField_zero
    (c : NSSpace) (t : NSTime) :
    convectionEnergyPairing (constantVelocityField c) t = fun _ : NSSpace => 0 := by
  funext x
  simp [convectionEnergyPairing, spatialConvection_constantVelocityField]

/-- The pressure energy pairing of a constant velocity field against zero
pressure vanishes. -/
theorem pressureEnergyPairing_constantVelocityField_zeroPressure
    (c : NSSpace) (t : NSTime) :
    pressureEnergyPairing (constantVelocityField c) (0 : NSPressureField) t =
      fun _ : NSSpace => 0 := by
  funext x
  simp [pressureEnergyPairing, spatialPressureGradient_zero]

/-- The viscous energy pairing of a constant velocity field vanishes. -/
theorem laplacianEnergyPairing_constantVelocityField_zero
    (c : NSSpace) (t : NSTime) :
    laplacianEnergyPairing (constantVelocityField c) t = fun _ : NSSpace => 0 := by
  funext x
  simp [laplacianEnergyPairing, spatialLaplacian_constantVelocityField]

/-- The derivative-under-the-integral seam holds for constant velocity fields,
but only because the unguarded kinetic-energy integral itself collapses to
zero. -/
theorem EnergyDerivativeFormula_constantVelocityField
    (c : NSSpace) :
    EnergyDerivativeFormula (constantVelocityField c) := by
  intro t
  rw [normalizedKineticEnergy_constantVelocityField]
  have hPairIntegral :
      ∫ x, timeEnergyPairing (constantVelocityField c) t x ∂volume = 0 := by
    rw [timeEnergyPairing_constantVelocityField_zero]
    simp
  rw [hPairIntegral]
  simpa using (hasDerivAt_const t (0 : ℝ))

/-- The corrected viscous pairing seam holds for constant velocity fields. -/
theorem CoordinateViscousEnergyPairingFormula_constantVelocityField
    (c : NSSpace) :
    CoordinateViscousEnergyPairingFormula (constantVelocityField c) := by
  intro t
  rw [laplacianEnergyPairing_constantVelocityField_zero,
    coordinateEnstrophyAt_constantVelocityField_zero]
  simp

/-- All three space pairings are integrable for a constant velocity field with
zero pressure because each pairing vanishes identically. -/
theorem EnergyPairingIntegrable_constantVelocityField_zeroPressure
    (c : NSSpace) :
    EnergyPairingIntegrable (constantVelocityField c) (0 : NSPressureField) := by
  intro t
  constructor
  · rw [laplacianEnergyPairing_constantVelocityField_zero]
    exact integrable_zero NSSpace ℝ (volume : Measure NSSpace)
  constructor
  · rw [convectionEnergyPairing_constantVelocityField_zero]
    exact integrable_zero NSSpace ℝ (volume : Measure NSSpace)
  · rw [pressureEnergyPairing_constantVelocityField_zeroPressure]
    exact integrable_zero NSSpace ℝ (volume : Measure NSSpace)

/-- Every constant velocity field satisfies the current corrected energy
identity surface, even when the spatial kinetic energy is not integrable. -/
theorem coordinateEnergyDissipationIdentity_smooth_constantVelocityField
    (ν : ℝ) (c : NSSpace) :
    ∀ t,
      HasDerivAt (normalizedKineticEnergy (constantVelocityField c))
        (-(coordinateEnergyDissipationRate (constantVelocityField c) ν t)) t := by
  exact
    coordinateEnergyDissipationIdentity_smooth
      (u := constantVelocityField c)
      (p := (0 : NSPressureField))
      (ν := ν)
      (EnergyDerivativeFormula_constantVelocityField c)
      (fun t x => momentumEquation_constantVelocityField_zeroPressure ν c t x)
      (EnergyPairingIntegrable_constantVelocityField_zeroPressure c)
      (CoordinateViscousEnergyPairingFormula_constantVelocityField c)
      (by
        intro t
        rw [pressureEnergyPairing_constantVelocityField_zeroPressure]
        simp)
      (by
        intro t
        rw [convectionEnergyPairing_constantVelocityField_zero]
        simp)

/-- A nonzero constant velocity field still fails the bounded-energy predicate,
so the current unguarded energy identity surface is underpowered as a
finite-energy theorem target. -/
theorem not_boundedKineticEnergy_constantVelocityField_of_ne_zero
    {c : NSSpace} (hc : c ≠ 0) :
    ¬ boundedKineticEnergy (constantVelocityField c) := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  exact not_integrable_kineticEnergyDensity_constantVelocityField_of_ne_zero hc 0 (hbound 0).1

/-- Checked obstruction: the current coordinatewise energy identity does not by
itself encode finite-energy control, because a nonzero constant velocity field
satisfies the identity while failing `boundedKineticEnergy`. -/
theorem exists_nonzero_constantVelocityField_coordinateEnergyIdentity_without_boundedEnergy
    (ν : ℝ) :
    ∃ c : NSSpace,
      c ≠ 0 ∧
      (∀ t,
        HasDerivAt (normalizedKineticEnergy (constantVelocityField c))
          (-(coordinateEnergyDissipationRate (constantVelocityField c) ν t)) t) ∧
      ¬ boundedKineticEnergy (constantVelocityField c) := by
  let c : NSSpace := EuclideanSpace.single nsCoord0 (1 : ℝ)
  have hc : c ≠ 0 := by
    intro hzero
    have hcoord := congrArg (fun v : NSSpace => v nsCoord0) hzero
    simp [c, nsCoord0] at hcoord
  refine ⟨c, hc, coordinateEnergyDissipationIdentity_smooth_constantVelocityField ν c, ?_⟩
  exact not_boundedKineticEnergy_constantVelocityField_of_ne_zero hc

end NavierStokes
end FluidDynamics
end Mettapedia
