import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeGalerkinToy
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEquationTarget
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
# Finite-Mode Spatial Reconstruction

This file turns a finite-mode coefficient solution into an actual spatial
velocity field on `ℝ × ℝ^3`.  It reconstructs both velocity and finite pressure
ansatz fields, and isolates the pointwise momentum residual whose vanishing is
the exact remaining PDE obligation before this finite-dimensional object can be
read as an actual Navier-Stokes momentum solution.

The explicit coordinate and polynomial pressure modes below are used only for
pointwise PDE algebra.  They are not finite-energy pressure witnesses on
`ℝ^3`, and no theorem in this file claims Clay-admissible global regularity.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open Set
open scoped BigOperators
open scoped ContDiff
open scoped Laplacian

/-- The continuous linear map sending a vector of mode coefficients to the
spatial finite-mode sum at a fixed point `x`. -/
def finiteModeReconstructionCLM
    {ι : Type*} [Fintype ι]
    (mode : ι → NSSpace → NSSpace) (x : NSSpace) :
    FiniteModeState ι →L[ℝ] NSSpace :=
  ∑ i : ι, (ContinuousLinearMap.proj i).smulRight (mode i x)

@[simp]
theorem finiteModeReconstructionCLM_apply
    {ι : Type*} [Fintype ι]
    (mode : ι → NSSpace → NSSpace) (x : NSSpace)
    (a : FiniteModeState ι) :
    finiteModeReconstructionCLM mode x a =
      ∑ i : ι, a i • mode i x := by
  simp [finiteModeReconstructionCLM]

/-- Reconstruct a concrete velocity field from mode coefficients. -/
def finiteModeReconstructedVelocity
    {ι : Type*} [Fintype ι]
    (mode : ι → NSSpace → NSSpace) (a : ℝ → FiniteModeState ι) :
    NSVelocityField :=
  fun t x => finiteModeReconstructionCLM mode x (a t)

@[simp]
theorem finiteModeReconstructedVelocity_apply
    {ι : Type*} [Fintype ι]
    (mode : ι → NSSpace → NSSpace) (a : ℝ → FiniteModeState ι)
    (t : NSTime) (x : NSSpace) :
    finiteModeReconstructedVelocity mode a t x =
      ∑ i : ι, a t i • mode i x := by
  simp [finiteModeReconstructedVelocity]

/-- The reconstructed initial velocity associated to a coefficient vector. -/
def finiteModeReconstructedInitialVelocity
    {ι : Type*} [Fintype ι]
    (mode : ι → NSSpace → NSSpace) (a₀ : FiniteModeState ι) :
    NSInitialVelocity :=
  fun x => finiteModeReconstructionCLM mode x a₀

@[simp]
theorem finiteModeReconstructedInitialVelocity_apply
    {ι : Type*} [Fintype ι]
    (mode : ι → NSSpace → NSSpace) (a₀ : FiniteModeState ι)
    (x : NSSpace) :
    finiteModeReconstructedInitialVelocity mode a₀ x =
      ∑ i : ι, a₀ i • mode i x := by
  simp [finiteModeReconstructedInitialVelocity]

/-- Reconstruct the projected acceleration field from the coefficient RHS. -/
def finiteModeReconstructedAcceleration
    {ι : Type*} [Fintype ι]
    (mode : ι → NSSpace → NSSpace)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι) :
    NSVelocityField :=
  finiteModeReconstructedVelocity mode (fun t => finiteModeProjectedNSRHS C (a t))

@[simp]
theorem finiteModeReconstructedAcceleration_apply
    {ι : Type*} [Fintype ι]
    (mode : ι → NSSpace → NSSpace)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (t : NSTime) (x : NSSpace) :
    finiteModeReconstructedAcceleration mode C a t x =
      ∑ i : ι, finiteModeProjectedNSRHS C (a t) i • mode i x := by
  simp [finiteModeReconstructedAcceleration]

/-- Reconstruct a concrete pressure field from finite pressure-mode
coefficients. -/
def finiteModeReconstructedPressure
    {κ : Type*} [Fintype κ]
    (pressureMode : κ → NSSpace → ℝ) (b : ℝ → FiniteModeState κ) :
    NSPressureField :=
  fun t x => ∑ k : κ, b t k * pressureMode k x

@[simp]
theorem finiteModeReconstructedPressure_apply
    {κ : Type*} [Fintype κ]
    (pressureMode : κ → NSSpace → ℝ) (b : ℝ → FiniteModeState κ)
    (t : NSTime) (x : NSSpace) :
    finiteModeReconstructedPressure pressureMode b t x =
      ∑ k : κ, b t k * pressureMode k x := by
  rfl

/-- The spatial pressure gradient of the reconstructed pressure is the finite
sum of modal pressure gradients weighted by the current pressure coefficients. -/
theorem finiteModeReconstructedPressure_spatialPressureGradient
    {κ : Type*} [Fintype κ]
    (pressureMode : κ → NSSpace → ℝ) (b : ℝ → FiniteModeState κ)
    (t : NSTime) (x : NSSpace)
    (hmode : ∀ k, DifferentiableAt ℝ (pressureMode k) x) :
    spatialPressureGradient (finiteModeReconstructedPressure pressureMode b) t x =
      ∑ k : κ, b t k • gradient (pressureMode k) x := by
  unfold spatialPressureGradient gradient
  have hdiff :
      ∀ k ∈ (Finset.univ : Finset κ),
        DifferentiableAt ℝ (fun y : NSSpace => b t k * pressureMode k y) x := by
    intro k _hk
    simpa [smul_eq_mul] using (hmode k).const_smul (b t k)
  have hfderiv :
      fderiv ℝ (fun y : NSSpace => finiteModeReconstructedPressure pressureMode b t y) x =
        ∑ k : κ, fderiv ℝ (fun y : NSSpace => b t k * pressureMode k y) x := by
    simpa [finiteModeReconstructedPressure] using fderiv_fun_sum hdiff
  rw [hfderiv]
  calc
    (InnerProductSpace.toDual ℝ NSSpace).symm
        (∑ k : κ, fderiv ℝ (fun y : NSSpace => b t k * pressureMode k y) x) =
      ∑ k : κ,
        (InnerProductSpace.toDual ℝ NSSpace).symm
          (fderiv ℝ (fun y : NSSpace => b t k * pressureMode k y) x) := by
        simp
    _ =
      ∑ k : κ, b t k •
        (InnerProductSpace.toDual ℝ NSSpace).symm
          (fderiv ℝ (pressureMode k) x) := by
        apply Finset.sum_congr rfl
        intro k _hk
        have hf :
            fderiv ℝ (fun y : NSSpace => b t k * pressureMode k y) x =
              b t k • fderiv ℝ (pressureMode k) x := by
          simpa [smul_eq_mul] using
            fderiv_fun_const_smul (hmode k) (b t k)
        rw [hf]
        simp

/-- Smooth coefficient curves and smooth spatial modes reconstruct to a smooth
space-time velocity field. -/
theorem finiteModeReconstructedVelocity_smoothSpaceTime
    {ι : Type*} [Fintype ι]
    (mode : ι → NSSpace → NSSpace) (a : ℝ → FiniteModeState ι)
    (ha : ∀ i, ContDiff ℝ ∞ (fun t : NSTime => a t i))
    (hmode : ∀ i, ContDiff ℝ ∞ (mode i)) :
    smoothSpaceTimeVelocity (finiteModeReconstructedVelocity mode a) := by
  unfold smoothSpaceTimeVelocity spaceTimeVelocityMap
  unfold finiteModeReconstructedVelocity finiteModeReconstructionCLM
  simpa using
    (ContDiff.sum (s := (Finset.univ : Finset ι))
      (fun i _hi =>
        ((ha i).comp (contDiff_fst : ContDiff ℝ ∞ (fun tx : NSSpacetime => tx.1))).smul
          ((hmode i).comp
            (contDiff_snd : ContDiff ℝ ∞ (fun tx : NSSpacetime => tx.2)))))

/-- Smooth pressure coefficient curves and smooth pressure modes reconstruct to
a smooth space-time pressure field. -/
theorem finiteModeReconstructedPressure_smoothSpaceTime
    {κ : Type*} [Fintype κ]
    (pressureMode : κ → NSSpace → ℝ) (b : ℝ → FiniteModeState κ)
    (hb : ∀ k, ContDiff ℝ ∞ (fun t : NSTime => b t k))
    (hmode : ∀ k, ContDiff ℝ ∞ (pressureMode k)) :
    smoothSpaceTimePressure (finiteModeReconstructedPressure pressureMode b) := by
  unfold smoothSpaceTimePressure spaceTimePressureMap finiteModeReconstructedPressure
  simpa using
    (ContDiff.sum (s := (Finset.univ : Finset κ))
      (fun k _hk =>
        ((hb k).comp (contDiff_fst : ContDiff ℝ ∞ (fun tx : NSSpacetime => tx.1))).mul
          ((hmode k).comp
            (contDiff_snd : ContDiff ℝ ∞ (fun tx : NSSpacetime => tx.2)))))

/-- Coordinate-linear pressure modes on `ℝ^3`: the `j`th mode is
`x ↦ x_j`. -/
def finiteModeCoordinatePressureMode (j : Fin 3) : NSSpace → ℝ :=
  fun x => x j

/-- Coordinate-linear pressure modes are smooth. -/
theorem finiteModeCoordinatePressureMode_contDiff
    (j : Fin 3) :
    ContDiff ℝ ∞ (finiteModeCoordinatePressureMode j) := by
  change ContDiff ℝ ∞
    (fun y : NSSpace => (EuclideanSpace.proj j : NSSpace →L[ℝ] ℝ) y)
  exact (EuclideanSpace.proj j : NSSpace →L[ℝ] ℝ).contDiff

/-- The coordinate-linear pressure modes are differentiable. -/
theorem finiteModeCoordinatePressureMode_differentiableAt
    (j : Fin 3) (x : NSSpace) :
    DifferentiableAt ℝ (finiteModeCoordinatePressureMode j) x := by
  change
    DifferentiableAt ℝ
      (fun y : NSSpace => (EuclideanSpace.proj j : NSSpace →L[ℝ] ℝ) y) x
  exact (EuclideanSpace.proj j : NSSpace →L[ℝ] ℝ).differentiable.differentiableAt

/-- The gradient of the `j`th coordinate pressure mode is the `j`th coordinate
unit vector. -/
theorem finiteModeCoordinatePressureMode_gradient
    (j : Fin 3) (x : NSSpace) :
    gradient (finiteModeCoordinatePressureMode j) x =
      EuclideanSpace.single j (1 : ℝ) := by
  unfold finiteModeCoordinatePressureMode gradient
  apply HasGradientAt.gradient
  rw [hasGradientAt_iff_hasFDerivAt]
  have hdual :
      (InnerProductSpace.toDual ℝ NSSpace) (EuclideanSpace.single j (1 : ℝ)) =
        (EuclideanSpace.proj j : NSSpace →L[ℝ] ℝ) := by
    ext y
    rw [InnerProductSpace.toDual_apply_apply]
    simp [EuclideanSpace.inner_single_left]
  rw [hdual]
  exact (EuclideanSpace.proj j : NSSpace →L[ℝ] ℝ).hasFDerivAt

/-- The standard coordinate pressure gradients reconstruct any vector in
`ℝ^3`. -/
theorem finiteModeCoordinatePressureMode_gradient_sum
    (c : NSSpace) :
    (∑ j : Fin 3, c j • EuclideanSpace.single j (1 : ℝ)) = c := by
  ext j
  simp [Pi.single_apply]

/-- Coordinate pressure coefficients for a prescribed time-dependent constant
pressure gradient. -/
def finiteModeCoordinatePressureCoefficients
    (c : NSTime → NSSpace) : NSTime → FiniteModeState (Fin 3) :=
  fun t j => c t j

/-- The finite coordinate pressure ansatz has spatial gradient exactly `c(t)`. -/
theorem finiteModeCoordinatePressure_spatialPressureGradient
    (c : NSTime → NSSpace) (t : NSTime) (x : NSSpace) :
    spatialPressureGradient
        (finiteModeReconstructedPressure finiteModeCoordinatePressureMode
          (finiteModeCoordinatePressureCoefficients c)) t x =
      c t := by
  calc
    spatialPressureGradient
        (finiteModeReconstructedPressure finiteModeCoordinatePressureMode
          (finiteModeCoordinatePressureCoefficients c)) t x =
      ∑ j : Fin 3,
        finiteModeCoordinatePressureCoefficients c t j •
          gradient (finiteModeCoordinatePressureMode j) x := by
        rw [finiteModeReconstructedPressure_spatialPressureGradient]
        intro j
        exact finiteModeCoordinatePressureMode_differentiableAt j x
    _ = ∑ j : Fin 3, c t j • EuclideanSpace.single j (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro j _hj
        rw [finiteModeCoordinatePressureMode_gradient]
        rfl
    _ = c t := finiteModeCoordinatePressureMode_gradient_sum (c t)

/-- Diagonal quadratic pressure modes on `ℝ^3`: the `j`th mode is
`x ↦ (1 / 2) * x_j^2`. Their gradients are nonconstant, linear-in-space
coordinate vector fields. -/
def finiteModeDiagonalQuadraticPressureMode (j : Fin 3) : NSSpace → ℝ :=
  fun x => (1 / 2 : ℝ) * (x j) ^ (2 : ℕ)

/-- Diagonal quadratic pressure modes are smooth. -/
theorem finiteModeDiagonalQuadraticPressureMode_contDiff
    (j : Fin 3) :
    ContDiff ℝ ∞ (finiteModeDiagonalQuadraticPressureMode j) := by
  unfold finiteModeDiagonalQuadraticPressureMode
  have hcoord : ContDiff ℝ ∞ (fun x : NSSpace => x j) := by
    simpa using (EuclideanSpace.proj j : NSSpace →L[ℝ] ℝ).contDiff
  simpa using (contDiff_const.mul (hcoord.pow 2))

/-- The diagonal quadratic pressure modes are differentiable. -/
theorem finiteModeDiagonalQuadraticPressureMode_differentiableAt
    (j : Fin 3) (x : NSSpace) :
    DifferentiableAt ℝ (finiteModeDiagonalQuadraticPressureMode j) x := by
  unfold finiteModeDiagonalQuadraticPressureMode
  have hproj : HasFDerivAt (fun y : NSSpace => y j)
      (EuclideanSpace.proj j : NSSpace →L[ℝ] ℝ) x := by
    exact (EuclideanSpace.proj j : NSSpace →L[ℝ] ℝ).hasFDerivAt
  have hpow : HasFDerivAt (fun y : NSSpace => (y j) ^ (2 : ℕ))
      (((2 : ℝ) * x j) • (EuclideanSpace.proj j : NSSpace →L[ℝ] ℝ)) x := by
    simpa using hproj.pow 2
  exact (hpow.const_mul (1 / 2 : ℝ)).differentiableAt

/-- The gradient of `x ↦ (1 / 2) * x_j^2` is `x_j e_j`. -/
theorem finiteModeDiagonalQuadraticPressureMode_gradient
    (j : Fin 3) (x : NSSpace) :
    gradient (finiteModeDiagonalQuadraticPressureMode j) x =
      x j • EuclideanSpace.single j (1 : ℝ) := by
  unfold finiteModeDiagonalQuadraticPressureMode gradient
  apply HasGradientAt.gradient
  rw [hasGradientAt_iff_hasFDerivAt]
  have hdual :
      (InnerProductSpace.toDual ℝ NSSpace) (x j • EuclideanSpace.single j (1 : ℝ)) =
        (x j) • (EuclideanSpace.proj j : NSSpace →L[ℝ] ℝ) := by
    ext y
    rw [InnerProductSpace.toDual_apply_apply]
    rw [inner_smul_left]
    rw [EuclideanSpace.inner_single_left]
    simp
  rw [hdual]
  have hproj : HasFDerivAt (fun y : NSSpace => y j)
      (EuclideanSpace.proj j : NSSpace →L[ℝ] ℝ) x := by
    exact (EuclideanSpace.proj j : NSSpace →L[ℝ] ℝ).hasFDerivAt
  have hpow : HasFDerivAt (fun y : NSSpace => (y j) ^ (2 : ℕ))
      (((2 : ℝ) * x j) • (EuclideanSpace.proj j : NSSpace →L[ℝ] ℝ)) x := by
    simpa using hproj.pow 2
  have hconst := hpow.const_mul (1 / 2 : ℝ)
  convert hconst using 1
  · ext y
    simp [one_div, smul_smul]

/-- Coefficients for diagonal quadratic pressure modes. -/
def finiteModeDiagonalQuadraticPressureCoefficients
    (d : NSTime → FiniteModeState (Fin 3)) : NSTime → FiniteModeState (Fin 3) :=
  d

/-- The diagonal quadratic pressure ansatz has a nonconstant diagonal linear
spatial gradient. -/
theorem finiteModeDiagonalQuadraticPressure_spatialPressureGradient
    (d : NSTime → FiniteModeState (Fin 3)) (t : NSTime) (x : NSSpace) :
    spatialPressureGradient
        (finiteModeReconstructedPressure finiteModeDiagonalQuadraticPressureMode
          (finiteModeDiagonalQuadraticPressureCoefficients d)) t x =
      ∑ j : Fin 3, d t j • (x j • EuclideanSpace.single j (1 : ℝ)) := by
  calc
    spatialPressureGradient
        (finiteModeReconstructedPressure finiteModeDiagonalQuadraticPressureMode
          (finiteModeDiagonalQuadraticPressureCoefficients d)) t x =
      ∑ j : Fin 3,
        finiteModeDiagonalQuadraticPressureCoefficients d t j •
          gradient (finiteModeDiagonalQuadraticPressureMode j) x := by
        rw [finiteModeReconstructedPressure_spatialPressureGradient]
        intro j
        exact finiteModeDiagonalQuadraticPressureMode_differentiableAt j x
    _ = ∑ j : Fin 3, d t j • (x j • EuclideanSpace.single j (1 : ℝ)) := by
        apply Finset.sum_congr rfl
        intro j _hj
        rw [finiteModeDiagonalQuadraticPressureMode_gradient]
        rfl

/-- The finite-mode momentum residual after reconstructing velocity and
pressure.  Its vanishing is exactly the pressure/residual closure condition
that turns a projected coefficient trajectory into a pointwise momentum
equation for the reconstructed fields. -/
def finiteModeReconstructedMomentumResidual
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (ν : ℝ)
    (mode : ι → NSSpace → NSSpace)
    (pressureMode : κ → NSSpace → ℝ)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (b : ℝ → FiniteModeState κ) :
    NSVelocityField :=
  fun t x =>
    finiteModeReconstructedAcceleration mode C a t x +
        spatialConvection (finiteModeReconstructedVelocity mode a) t x +
          spatialPressureGradient (finiteModeReconstructedPressure pressureMode b) t x -
      ν • spatialLaplacian (finiteModeReconstructedVelocity mode a) t x

/-- Pointwise zero-residual condition for the reconstructed finite-mode
velocity-pressure ansatz. -/
def finiteModeReconstructedMomentumResidualZeroAt
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (ν : ℝ)
    (mode : ι → NSSpace → NSSpace)
    (pressureMode : κ → NSSpace → ℝ)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (b : ℝ → FiniteModeState κ)
    (t : NSTime) (x : NSSpace) : Prop :=
  finiteModeReconstructedMomentumResidual ν mode pressureMode C a b t x = 0

/-- Zero-residual condition on a time set. -/
def finiteModeReconstructedMomentumResidualZeroOn
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (I : Set NSTime)
    (ν : ℝ)
    (mode : ι → NSSpace → NSSpace)
    (pressureMode : κ → NSSpace → ℝ)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (b : ℝ → FiniteModeState κ) : Prop :=
  ∀ t ∈ I, ∀ x : NSSpace,
    finiteModeReconstructedMomentumResidualZeroAt
      ν mode pressureMode C a b t x

/-- The non-pressure part of the reconstructed momentum residual. -/
def finiteModeNonPressureMomentumDefect
    {ι : Type*} [Fintype ι]
    (ν : ℝ)
    (mode : ι → NSSpace → NSSpace)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι) :
    NSVelocityField :=
  fun t x =>
    finiteModeReconstructedAcceleration mode C a t x +
      spatialConvection (finiteModeReconstructedVelocity mode a) t x -
        ν • spatialLaplacian (finiteModeReconstructedVelocity mode a) t x

/-- The finite pressure-gradient synthesis map determined by selected pressure
modes. -/
def finiteModePressureGradientSynthesis
    {κ : Type*} [Fintype κ]
    (pressureMode : κ → NSSpace → ℝ) :
    FiniteModeState κ → NSSpace → NSSpace :=
  fun b x => ∑ k : κ, b k • gradient (pressureMode k) x

/-- Pointwise coercion of a finite linear combination in a subspace of vector
fields. -/
theorem finiteModeSubmodule_sum_apply
    {κ : Type*} [Fintype κ]
    (V : Submodule ℝ (NSSpace → NSSpace))
    (G : κ → V) (c : κ → ℝ) (x : NSSpace) :
    ((∑ k : κ, c k • G k : V) : NSSpace → NSSpace) x =
      ∑ k : κ, c k • ((G k : V) : NSSpace → NSSpace) x := by
  have hcoe :
      ((∑ k : κ, c k • G k : V) : NSSpace → NSSpace) =
        ∑ k : κ, ((c k • G k : V) : NSSpace → NSSpace) := by
    simp
  rw [hcoe]
  simp [Pi.smul_apply]

/-- If the modal pressure gradients are a basis for a finite-dimensional
subspace `V` of vector fields, the basis coordinates of any `F ∈ V` synthesize
exactly `F` as a pressure gradient. -/
theorem finiteModePressureGradientSynthesis_basis_repr
    {κ : Type*} [Fintype κ]
    (pressureMode : κ → NSSpace → ℝ)
    (V : Submodule ℝ (NSSpace → NSSpace))
    (B : Module.Basis κ ℝ V)
    (hgradientBasis : ∀ k,
      ((B k : V) : NSSpace → NSSpace) =
        fun x => gradient (pressureMode k) x)
    (F : V) :
    finiteModePressureGradientSynthesis pressureMode
        (fun k => B.repr F k) =
      (F : NSSpace → NSSpace) := by
  have hsum : (∑ k : κ, (B.repr F k) • B k : V) = F := by
    exact B.sum_repr F
  have hfun :
      ((∑ k : κ, (B.repr F k) • B k : V) : NSSpace → NSSpace) =
        (F : NSSpace → NSSpace) :=
    congrArg (fun G : V => (G : NSSpace → NSSpace)) hsum
  have hgradientBasis_apply :
      ∀ k x, ((B k : V) : NSSpace → NSSpace) x =
        gradient (pressureMode k) x := by
    intro k x
    exact congrFun (hgradientBasis k) x
  funext x
  have hx := congrFun hfun x
  calc
    finiteModePressureGradientSynthesis pressureMode
        (fun k => B.repr F k) x =
      ∑ k : κ, (B.repr F k) • (((B k : V) : NSSpace → NSSpace) x) := by
        simp [finiteModePressureGradientSynthesis, hgradientBasis_apply]
    _ = ((∑ k : κ, (B.repr F k) • B k : V) : NSSpace → NSSpace) x := by
        exact (finiteModeSubmodule_sum_apply V B (fun k => B.repr F k) x).symm
    _ = (F : NSSpace → NSSpace) x := hx

/-- The pressure coefficients obtained from a gradient-subspace basis witness
membership in the pressure-gradient range. -/
theorem finiteModePressureGradientSynthesis_mem_range_of_basis
    {κ : Type*} [Fintype κ]
    (pressureMode : κ → NSSpace → ℝ)
    (V : Submodule ℝ (NSSpace → NSSpace))
    (B : Module.Basis κ ℝ V)
    (hgradientBasis : ∀ k,
      ((B k : V) : NSSpace → NSSpace) =
        fun x => gradient (pressureMode k) x)
    (F : V) :
    (F : NSSpace → NSSpace) ∈
      range (finiteModePressureGradientSynthesis pressureMode) := by
  refine ⟨fun k => B.repr F k, ?_⟩
  exact finiteModePressureGradientSynthesis_basis_repr
    pressureMode V B hgradientBasis F

/-- A finite pressure basis realizes exactly its gradient subspace.  This is
the finite-dimensional Helmholtz algebra behind pressure reconstruction: once
the actual pressure primitives have been provided for a vector-field subspace,
pressure coefficients are just basis coordinates. -/
theorem finiteModePressureGradientSynthesis_range_eq_submodule
    {κ : Type*} [Fintype κ]
    (pressureMode : κ → NSSpace → ℝ)
    (V : Submodule ℝ (NSSpace → NSSpace))
    (B : Module.Basis κ ℝ V)
    (hgradientBasis : ∀ k,
      ((B k : V) : NSSpace → NSSpace) =
        fun x => gradient (pressureMode k) x) :
    range (finiteModePressureGradientSynthesis pressureMode) =
      (V : Set (NSSpace → NSSpace)) := by
  ext F
  constructor
  · rintro ⟨b, rfl⟩
    have hgradientBasis_apply :
        ∀ k x, ((B k : V) : NSSpace → NSSpace) x =
          gradient (pressureMode k) x := by
      intro k x
      exact congrFun (hgradientBasis k) x
    have hcoe :
        ((∑ k : κ, b k • B k : V) : NSSpace → NSSpace) =
          finiteModePressureGradientSynthesis pressureMode b := by
      funext x
      calc
        ((∑ k : κ, b k • B k : V) : NSSpace → NSSpace) x =
          ∑ k : κ, b k • (((B k : V) : NSSpace → NSSpace) x) := by
            exact finiteModeSubmodule_sum_apply V B b x
        _ = finiteModePressureGradientSynthesis pressureMode b x := by
            simp [finiteModePressureGradientSynthesis, hgradientBasis_apply]
    rw [← hcoe]
    exact (∑ k : κ, b k • B k : V).property
  · intro hF
    exact finiteModePressureGradientSynthesis_mem_range_of_basis
      pressureMode V B hgradientBasis ⟨F, hF⟩

/-- Polynomial pressure primitives for homogeneous curl-free vector fields.
For a homogeneous degree-`n` polynomial vector field `F`, Euler's identity
turns the radial antiderivative `(n + 1)⁻¹ ∑ i X_i F_i` into a genuine
pressure primitive whenever the mixed partials agree. -/
def finiteModeHomogeneousPolynomialPressurePrimitive
    (n : ℕ) (F : Fin 3 → MvPolynomial (Fin 3) ℝ) :
    MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.C (((n + 1 : ℕ) : ℝ)⁻¹) *
    ∑ i : Fin 3, MvPolynomial.X i * F i

/-- Degree-independent polynomial Poincare lemma for homogeneous curl-free
vector polynomials on `ℝ^3`: the radial primitive differentiates back to each
component.  This is the algebraic core needed before a finite-mode polynomial
pressure basis can solve the non-pressure residual instead of taking closure
as an input hypothesis. -/
theorem finiteModeHomogeneousPolynomialPressurePrimitive_pderiv
    (n : ℕ) (F : Fin 3 → MvPolynomial (Fin 3) ℝ)
    (hhom : ∀ j, (F j).IsHomogeneous n)
    (hcurl : ∀ i j, MvPolynomial.pderiv i (F j) =
      MvPolynomial.pderiv j (F i))
    (j : Fin 3) :
    MvPolynomial.pderiv j
        (finiteModeHomogeneousPolynomialPressurePrimitive n F) =
      F j := by
  classical
  have hdelta :
      (∑ i : Fin 3,
          MvPolynomial.pderiv j (MvPolynomial.X i : MvPolynomial (Fin 3) ℝ) *
            F i) =
        F j := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _hi hij
      rw [MvPolynomial.pderiv_X_of_ne hij]
      simp
    · intro hj
      exact False.elim (hj (Finset.mem_univ j))
  have hcurlsum :
      (∑ i : Fin 3,
          MvPolynomial.X i * MvPolynomial.pderiv j (F i)) =
        ∑ i : Fin 3, MvPolynomial.X i * MvPolynomial.pderiv i (F j) := by
    refine Finset.sum_congr rfl ?_
    intro i _hi
    rw [hcurl j i]
  have heuler :
      (∑ i : Fin 3, MvPolynomial.X i * MvPolynomial.pderiv i (F j)) =
        n • F j := by
    simpa using (hhom j).sum_X_mul_pderiv
  have hsum :
      MvPolynomial.pderiv j
          (∑ i : Fin 3, MvPolynomial.X i * F i) =
        (n + 1) • F j := by
    calc
      MvPolynomial.pderiv j
          (∑ i : Fin 3, MvPolynomial.X i * F i) =
        ∑ i : Fin 3,
          MvPolynomial.pderiv j (MvPolynomial.X i * F i) := by
          exact
            map_sum (MvPolynomial.pderiv j)
              (fun i : Fin 3 => MvPolynomial.X i * F i) Finset.univ
      _ = ∑ i : Fin 3,
          (MvPolynomial.pderiv j (MvPolynomial.X i) * F i +
            MvPolynomial.X i * MvPolynomial.pderiv j (F i)) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [MvPolynomial.pderiv_mul]
      _ =
        (∑ i : Fin 3,
          MvPolynomial.pderiv j (MvPolynomial.X i : MvPolynomial (Fin 3) ℝ) *
            F i) +
          ∑ i : Fin 3, MvPolynomial.X i * MvPolynomial.pderiv j (F i) := by
          rw [Finset.sum_add_distrib]
      _ = F j + ∑ i : Fin 3,
          MvPolynomial.X i * MvPolynomial.pderiv i (F j) := by
          rw [hdelta, hcurlsum]
      _ = F j + n • F j := by
          rw [heuler]
      _ = (n + 1) • F j := by
          simpa [Nat.succ_eq_add_one, add_comm] using
            ((succ_nsmul (F j) n).symm)
  unfold finiteModeHomogeneousPolynomialPressurePrimitive
  rw [MvPolynomial.pderiv_C_mul, hsum]
  have hnpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_pos n
  have hn : (((n + 1 : ℕ) : ℝ)) ≠ 0 := ne_of_gt hnpos
  rw [nsmul_eq_mul]
  change
    MvPolynomial.C (((n + 1 : ℕ) : ℝ)⁻¹) *
        (((n + 1 : ℕ) : MvPolynomial (Fin 3) ℝ) * F j) =
      F j
  rw [← mul_assoc]
  have hcast :
      ((n + 1 : ℕ) : MvPolynomial (Fin 3) ℝ) =
        MvPolynomial.C (((n + 1 : ℕ) : ℝ)) := by
    norm_num
  rw [hcast]
  have hscale :
      MvPolynomial.C (((n + 1 : ℕ) : ℝ)⁻¹) *
          MvPolynomial.C (((n + 1 : ℕ) : ℝ)) =
        (1 : MvPolynomial (Fin 3) ℝ) := by
    calc
      MvPolynomial.C (((n + 1 : ℕ) : ℝ)⁻¹) *
          MvPolynomial.C (((n + 1 : ℕ) : ℝ)) =
        MvPolynomial.C
          ((((n + 1 : ℕ) : ℝ)⁻¹) * (((n + 1 : ℕ) : ℝ))) := by
          rw [← MvPolynomial.C_mul]
      _ = (1 : MvPolynomial (Fin 3) ℝ) := by
          have hreal :
              (((n + 1 : ℕ) : ℝ)⁻¹ * (((n + 1 : ℕ) : ℝ))) = 1 :=
            inv_mul_cancel₀ hn
          rw [hreal]
          simp
  rw [hscale, one_mul]

/-- Finite sum of homogeneous polynomial pressure primitives. -/
def finiteModeFiniteHomogeneousPolynomialPressurePrimitive
    (s : Finset ℕ) (F : ℕ → Fin 3 → MvPolynomial (Fin 3) ℝ) :
    MvPolynomial (Fin 3) ℝ :=
  s.sum fun n => finiteModeHomogeneousPolynomialPressurePrimitive n (F n)

/-- A finite sum of homogeneous curl-free polynomial vector fields has a
polynomial pressure primitive obtained by summing the radial primitives of the
homogeneous pieces. -/
theorem finiteModeFiniteHomogeneousPolynomialPressurePrimitive_pderiv
    (s : Finset ℕ) (F : ℕ → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (hhom : ∀ n ∈ s, ∀ j, (F n j).IsHomogeneous n)
    (hcurl : ∀ n ∈ s, ∀ i j,
      MvPolynomial.pderiv i (F n j) =
        MvPolynomial.pderiv j (F n i))
    (j : Fin 3) :
    MvPolynomial.pderiv j
        (finiteModeFiniteHomogeneousPolynomialPressurePrimitive s F) =
      s.sum fun n => F n j := by
  unfold finiteModeFiniteHomogeneousPolynomialPressurePrimitive
  calc
    MvPolynomial.pderiv j
        (s.sum fun n => finiteModeHomogeneousPolynomialPressurePrimitive n (F n)) =
      s.sum fun n =>
        MvPolynomial.pderiv j
          (finiteModeHomogeneousPolynomialPressurePrimitive n (F n)) := by
        exact
          map_sum (MvPolynomial.pderiv j)
            (fun n => finiteModeHomogeneousPolynomialPressurePrimitive n (F n)) s
    _ = s.sum fun n => F n j := by
        refine Finset.sum_congr rfl ?_
        intro n hn
        exact finiteModeHomogeneousPolynomialPressurePrimitive_pderiv
          n (F n) (hhom n hn) (hcurl n hn) j

/-- Repackaged finite homogeneous pressure solve against a named target vector
polynomial.  The remaining general-polynomial task is to supply the homogeneous
decomposition and prove its pieces inherit curl-freeness. -/
theorem finiteModeFiniteHomogeneousPolynomialPressurePrimitive_pderiv_of_sum
    (s : Finset ℕ) (F : ℕ → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (G : Fin 3 → MvPolynomial (Fin 3) ℝ)
    (hhom : ∀ n ∈ s, ∀ j, (F n j).IsHomogeneous n)
    (hcurl : ∀ n ∈ s, ∀ i j,
      MvPolynomial.pderiv i (F n j) =
        MvPolynomial.pderiv j (F n i))
    (hsum : ∀ j, (s.sum fun n => F n j) = G j)
    (j : Fin 3) :
    MvPolynomial.pderiv j
        (finiteModeFiniteHomogeneousPolynomialPressurePrimitive s F) =
      G j := by
  rw [finiteModeFiniteHomogeneousPolynomialPressurePrimitive_pderiv
    s F hhom hcurl j, hsum j]

/-- Coefficient formula for formal partial derivatives on the polynomial ring
used for finite-mode pressure algebra. -/
theorem finiteModePolynomial_coeff_pderiv
    (i : Fin 3) (d : Fin 3 →₀ ℕ) (φ : MvPolynomial (Fin 3) ℝ) :
    MvPolynomial.coeff d (MvPolynomial.pderiv i φ) =
      MvPolynomial.coeff (d + Finsupp.single i 1) φ *
        ((d i + 1 : ℕ) : ℝ) := by
  induction φ using MvPolynomial.induction_on' with
  | monomial u a =>
      rw [MvPolynomial.pderiv_monomial]
      simp only [MvPolynomial.coeff_monomial]
      by_cases h : u = d + Finsupp.single i 1
      · subst u
        simp [add_comm]
      · simp [h]
        intro hsub
        have hui : u i = 0 := by
          by_contra hne
          have hadd : u = d + Finsupp.single i 1 := by
            rw [← hsub]
            exact (Finsupp.sub_add_single_one_cancel hne).symm
          exact h hadd
        simp [hui]
  | add p q hp hq =>
      rw [map_add]
      simp [MvPolynomial.coeff_add, hp, hq, add_mul]

/-- Formal partial derivatives commute with homogeneous projection, with the
expected degree shift. -/
theorem finiteModeHomogeneousComponent_pderiv_succ
    (n : ℕ) (i : Fin 3) (φ : MvPolynomial (Fin 3) ℝ) :
    MvPolynomial.pderiv i (MvPolynomial.homogeneousComponent (n + 1) φ) =
      MvPolynomial.homogeneousComponent n (MvPolynomial.pderiv i φ) := by
  ext d
  rw [finiteModePolynomial_coeff_pderiv]
  rw [MvPolynomial.coeff_homogeneousComponent]
  rw [MvPolynomial.coeff_homogeneousComponent]
  rw [finiteModePolynomial_coeff_pderiv]
  by_cases hd : d.degree = n <;> simp [hd]

/-- Curl-freeness passes to every homogeneous component of a polynomial vector
field. -/
theorem finiteModeHomogeneousComponent_curlFree
    (G : Fin 3 → MvPolynomial (Fin 3) ℝ)
    (hcurl : ∀ i j,
      MvPolynomial.pderiv i (G j) =
        MvPolynomial.pderiv j (G i))
    (n : ℕ) (i j : Fin 3) :
    MvPolynomial.pderiv i (MvPolynomial.homogeneousComponent n (G j)) =
      MvPolynomial.pderiv j (MvPolynomial.homogeneousComponent n (G i)) := by
  cases n with
  | zero =>
      simp [MvPolynomial.homogeneousComponent_zero]
  | succ n =>
      rw [finiteModeHomogeneousComponent_pderiv_succ n i (G j)]
      rw [finiteModeHomogeneousComponent_pderiv_succ n j (G i)]
      rw [hcurl i j]

/-- Homogeneous components up to any degree bound summing past the total degree
still reconstruct the original polynomial. -/
theorem finiteModePolynomial_sum_homogeneousComponent_of_totalDegree_le
    (φ : MvPolynomial (Fin 3) ℝ) {N : ℕ} (hN : φ.totalDegree ≤ N) :
    (Finset.range (N + 1)).sum
        (fun n => MvPolynomial.homogeneousComponent n φ) =
      φ := by
  calc
    (∑ n ∈ Finset.range (N + 1), MvPolynomial.homogeneousComponent n φ) =
        ∑ n ∈ Finset.range (φ.totalDegree + 1),
          MvPolynomial.homogeneousComponent n φ := by
      exact (Finset.sum_subset
        (s₁ := Finset.range (φ.totalDegree + 1))
        (s₂ := Finset.range (N + 1))
        (f := fun n => MvPolynomial.homogeneousComponent n φ)
        (by
          intro n hn
          rw [Finset.mem_range] at hn ⊢
          exact lt_of_lt_of_le hn (Nat.succ_le_succ hN))
        (by
          intro n _hnBig hnSmall
          rw [Finset.mem_range] at hnSmall
          have hlt : φ.totalDegree < n := Nat.le_of_not_gt hnSmall
          exact MvPolynomial.homogeneousComponent_eq_zero n φ hlt)).symm
    _ = φ := MvPolynomial.sum_homogeneousComponent (φ := φ)

/-- Uniform total-degree bound for a three-component polynomial vector field. -/
def finiteModePolynomialVectorTotalDegree
    (G : Fin 3 → MvPolynomial (Fin 3) ℝ) : ℕ :=
  Finset.univ.sup fun j : Fin 3 => (G j).totalDegree

/-- General polynomial pressure primitive for a curl-free polynomial vector
field, obtained by summing the radial primitives of its homogeneous
components. -/
def finiteModePolynomialPressurePrimitive
    (G : Fin 3 → MvPolynomial (Fin 3) ℝ) :
    MvPolynomial (Fin 3) ℝ :=
  finiteModeFiniteHomogeneousPolynomialPressurePrimitive
    (Finset.range (finiteModePolynomialVectorTotalDegree G + 1))
    (fun n j => MvPolynomial.homogeneousComponent n (G j))

/-- Polynomial Helmholtz/Poincare pressure solve on `ℝ^3`: every curl-free
polynomial vector field is the formal gradient of the explicit polynomial
pressure primitive above. -/
theorem finiteModePolynomialPressurePrimitive_pderiv
    (G : Fin 3 → MvPolynomial (Fin 3) ℝ)
    (hcurl : ∀ i j,
      MvPolynomial.pderiv i (G j) =
        MvPolynomial.pderiv j (G i))
    (j : Fin 3) :
    MvPolynomial.pderiv j (finiteModePolynomialPressurePrimitive G) =
      G j := by
  unfold finiteModePolynomialPressurePrimitive
  rw [finiteModeFiniteHomogeneousPolynomialPressurePrimitive_pderiv]
  · exact finiteModePolynomial_sum_homogeneousComponent_of_totalDegree_le
      (G j)
      (Finset.le_sup
        (f := fun k : Fin 3 => (G k).totalDegree) (Finset.mem_univ j))
  · intro n _hn k
    exact MvPolynomial.homogeneousComponent_isHomogeneous n (G k)
  · intro n _hn i k
    exact finiteModeHomogeneousComponent_curlFree G hcurl n i k

/-- Formal mixed partial derivatives commute for three-variable real
polynomials. -/
theorem finiteModePolynomial_pderiv_comm
    (i j : Fin 3) (p : MvPolynomial (Fin 3) ℝ) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j p) =
      MvPolynomial.pderiv j (MvPolynomial.pderiv i p) := by
  ext d
  repeat rw [finiteModePolynomial_coeff_pderiv]
  by_cases hij : i = j
  · subst j
    ring
  · have hji : j ≠ i := Ne.symm hij
    simp [Finsupp.single_eq_of_ne, hij, hji, Finsupp.add_apply,
      add_comm, add_left_comm, mul_assoc, mul_comm, mul_left_comm]

/-- Polynomial Helmholtz/Poincare exactness in coefficient form: a polynomial
vector field is a formal gradient exactly when its mixed partials commute. -/
theorem finiteModePolynomialPressurePrimitive_exists_iff_curlFree
    (G : Fin 3 → MvPolynomial (Fin 3) ℝ) :
    (∃ p : MvPolynomial (Fin 3) ℝ,
        ∀ j, MvPolynomial.pderiv j p = G j) ↔
      ∀ i j, MvPolynomial.pderiv i (G j) =
        MvPolynomial.pderiv j (G i) := by
  constructor
  · rintro ⟨p, hp⟩ i j
    rw [← hp j, ← hp i]
    exact finiteModePolynomial_pderiv_comm i j p
  · intro hcurl
    exact ⟨finiteModePolynomialPressurePrimitive G,
      finiteModePolynomialPressurePrimitive_pderiv G hcurl⟩

/-- The Fréchet derivative of evaluating a multivariate polynomial on
`NSSpace`, written as the coordinate sum of formal partial derivatives. -/
def finiteModePolynomialEvalFDeriv
    (p : MvPolynomial (Fin 3) ℝ) (x : NSSpace) : NSSpace →L[ℝ] ℝ :=
  ∑ j : Fin 3, (EuclideanSpace.proj j : NSSpace →L[ℝ] ℝ).smulRight
    (MvPolynomial.eval x (MvPolynomial.pderiv j p))

/-- The gradient vector associated to polynomial evaluation. -/
def finiteModePolynomialEvalGradient
    (p : MvPolynomial (Fin 3) ℝ) (x : NSSpace) : NSSpace :=
  ∑ j : Fin 3,
    MvPolynomial.eval x (MvPolynomial.pderiv j p) • EuclideanSpace.single j (1 : ℝ)

@[simp]
theorem finiteModePolynomialEvalGradient_apply
    (p : MvPolynomial (Fin 3) ℝ) (x : NSSpace) (j : Fin 3) :
    finiteModePolynomialEvalGradient p x j =
      MvPolynomial.eval x (MvPolynomial.pderiv j p) := by
  simp [finiteModePolynomialEvalGradient, Pi.single_apply]

@[simp]
theorem finiteModePolynomialEvalFDeriv_apply
    (p : MvPolynomial (Fin 3) ℝ) (x v : NSSpace) :
    finiteModePolynomialEvalFDeriv p x v =
      ∑ j : Fin 3, v j * MvPolynomial.eval x (MvPolynomial.pderiv j p) := by
  simp [finiteModePolynomialEvalFDeriv]

theorem finiteModePolynomialEvalFDeriv_C
    (a : ℝ) (x : NSSpace) :
    finiteModePolynomialEvalFDeriv (MvPolynomial.C a) x = 0 := by
  ext v
  simp [finiteModePolynomialEvalFDeriv]

theorem finiteModePolynomialEvalFDeriv_add
    (p q : MvPolynomial (Fin 3) ℝ) (x : NSSpace) :
    finiteModePolynomialEvalFDeriv (p + q) x =
      finiteModePolynomialEvalFDeriv p x + finiteModePolynomialEvalFDeriv q x := by
  ext v
  calc
    finiteModePolynomialEvalFDeriv (p + q) x v =
        ∑ j : Fin 3,
          (v j * MvPolynomial.eval x (MvPolynomial.pderiv j p) +
            v j * MvPolynomial.eval x (MvPolynomial.pderiv j q)) := by
        simp [finiteModePolynomialEvalFDeriv, mul_add]
    _ = finiteModePolynomialEvalFDeriv p x v +
        finiteModePolynomialEvalFDeriv q x v := by
        simp [finiteModePolynomialEvalFDeriv, Finset.sum_add_distrib]

set_option maxHeartbeats 800000 in
theorem finiteModePolynomialEvalFDeriv_mul_X
    (p : MvPolynomial (Fin 3) ℝ) (n : Fin 3) (x : NSSpace) :
    finiteModePolynomialEvalFDeriv (p * MvPolynomial.X n) x =
      (MvPolynomial.eval x p) • (EuclideanSpace.proj n : NSSpace →L[ℝ] ℝ) +
        (x n) • finiteModePolynomialEvalFDeriv p x := by
  ext v
  fin_cases n <;>
    simp [finiteModePolynomialEvalFDeriv, Fin.sum_univ_three, MvPolynomial.eval_add,
      MvPolynomial.eval_mul, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm] <;>
    ring

theorem finiteModePolynomialEval_hasFDerivAt
    (p : MvPolynomial (Fin 3) ℝ) (x : NSSpace) :
    HasFDerivAt (fun y : NSSpace => MvPolynomial.eval y p)
      (finiteModePolynomialEvalFDeriv p x) x := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      simpa [finiteModePolynomialEvalFDeriv_C] using
        (hasFDerivAt_const (x := x) (c := a))
  | add p q hp hq =>
      have hderiv := hp.add hq
      simpa [MvPolynomial.eval_add, finiteModePolynomialEvalFDeriv_add] using hderiv
  | mul_X p n hp =>
      have hcoord : HasFDerivAt (fun y : NSSpace => y n)
          (EuclideanSpace.proj n : NSSpace →L[ℝ] ℝ) x := by
        exact (EuclideanSpace.proj n : NSSpace →L[ℝ] ℝ).hasFDerivAt
      have hderiv := hp.mul hcoord
      have hmul := finiteModePolynomialEvalFDeriv_mul_X p n x
      simpa [MvPolynomial.eval_mul, MvPolynomial.eval_X, hmul] using hderiv

/-- The derivative, in the spatial base point, of the polynomial-evaluation
derivative. -/
def finiteModePolynomialEvalFDerivFDeriv
    (p : MvPolynomial (Fin 3) ℝ) (x : NSSpace) :
    NSSpace →L[ℝ] (NSSpace →L[ℝ] ℝ) :=
  ∑ j : Fin 3,
    (finiteModePolynomialEvalFDeriv (MvPolynomial.pderiv j p) x).smulRight
      (EuclideanSpace.proj j : NSSpace →L[ℝ] ℝ)

@[simp]
theorem finiteModePolynomialEvalFDerivFDeriv_apply
    (p : MvPolynomial (Fin 3) ℝ) (x w v : NSSpace) :
    finiteModePolynomialEvalFDerivFDeriv p x w v =
      ∑ j : Fin 3,
        (∑ r : Fin 3, w r *
          MvPolynomial.eval x (MvPolynomial.pderiv r (MvPolynomial.pderiv j p))) * v j := by
  simp [finiteModePolynomialEvalFDerivFDeriv, finiteModePolynomialEvalFDeriv_apply]

theorem finiteModePolynomialEvalFDeriv_hasFDerivAt
    (p : MvPolynomial (Fin 3) ℝ) (x : NSSpace) :
    HasFDerivAt (fun y : NSSpace => finiteModePolynomialEvalFDeriv p y)
      (finiteModePolynomialEvalFDerivFDeriv p x) x := by
  let g : NSSpace → (NSSpace →L[ℝ] ℝ) := fun y =>
    ∑ j : Fin 3, MvPolynomial.eval y (MvPolynomial.pderiv j p) •
      (EuclideanSpace.proj j : NSSpace →L[ℝ] ℝ)
  have hfg : (fun y : NSSpace => finiteModePolynomialEvalFDeriv p y) = g := by
    funext y
    ext v
    simp [g, finiteModePolynomialEvalFDeriv, ContinuousLinearMap.smulRight_apply, mul_comm]
  rw [hfg]
  simpa [g, finiteModePolynomialEvalFDerivFDeriv]
    using
      (HasFDerivAt.sum (u := (Finset.univ : Finset (Fin 3)))
        (fun j _hj =>
          (finiteModePolynomialEval_hasFDerivAt (MvPolynomial.pderiv j p) x).smul_const
            (EuclideanSpace.proj j : NSSpace →L[ℝ] ℝ)))

theorem finiteModePolynomialEval_iteratedFDeriv_two_basis
    (p : MvPolynomial (Fin 3) ℝ) (x : NSSpace) (i : Fin 3) :
    (iteratedFDeriv ℝ 2 (fun y : NSSpace => MvPolynomial.eval y p) x)
        ![(EuclideanSpace.basisFun (Fin 3) ℝ) i,
          (EuclideanSpace.basisFun (Fin 3) ℝ) i] =
      MvPolynomial.eval x (MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) := by
  rw [iteratedFDeriv_two_apply]
  have hf : (fun y : NSSpace => fderiv ℝ (fun z : NSSpace => MvPolynomial.eval z p) y) =
      fun y => finiteModePolynomialEvalFDeriv p y := by
    funext y
    exact (finiteModePolynomialEval_hasFDerivAt p y).fderiv
  change (fderiv ℝ (fun y : NSSpace =>
      fderiv ℝ (fun z : NSSpace => MvPolynomial.eval z p) y) x)
        (![(EuclideanSpace.basisFun (Fin 3) ℝ) i,
          (EuclideanSpace.basisFun (Fin 3) ℝ) i] 0)
        (![(EuclideanSpace.basisFun (Fin 3) ℝ) i,
          (EuclideanSpace.basisFun (Fin 3) ℝ) i] 1) =
      MvPolynomial.eval x (MvPolynomial.pderiv i (MvPolynomial.pderiv i p))
  rw [hf]
  rw [(finiteModePolynomialEvalFDeriv_hasFDerivAt p x).fderiv]
  simp [EuclideanSpace.basisFun_apply]

@[simp]
theorem finiteModePolynomialEval_iteratedFDeriv_two_single
    (p : MvPolynomial (Fin 3) ℝ) (x : NSSpace) (i : Fin 3) :
    (iteratedFDeriv ℝ 2 (fun y : NSSpace => MvPolynomial.eval y p) x)
        ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] =
      MvPolynomial.eval x (MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) := by
  simpa [EuclideanSpace.basisFun_apply] using
    finiteModePolynomialEval_iteratedFDeriv_two_basis p x i

/-- Formal scalar Laplacian of a polynomial in the spatial variables. -/
def finiteModePolynomialScalarLaplacian
    (p : MvPolynomial (Fin 3) ℝ) : MvPolynomial (Fin 3) ℝ :=
  ∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)

theorem finiteModePolynomialEval_laplacian
    (p : MvPolynomial (Fin 3) ℝ) (x : NSSpace) :
    Δ (fun y : NSSpace => MvPolynomial.eval y p) x =
      MvPolynomial.eval x (finiteModePolynomialScalarLaplacian p) := by
  rw [show Δ (fun y : NSSpace => MvPolynomial.eval y p) x =
      ∑ i : Fin 3,
        (iteratedFDeriv ℝ 2 (fun y : NSSpace => MvPolynomial.eval y p) x)
          ![(EuclideanSpace.basisFun (Fin 3) ℝ) i,
            (EuclideanSpace.basisFun (Fin 3) ℝ) i] by
    simpa using congrArg (fun h : NSSpace → ℝ => h x)
      (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
        (f := fun y : NSSpace => MvPolynomial.eval y p)
        (v := EuclideanSpace.basisFun (Fin 3) ℝ))]
  simp [finiteModePolynomialScalarLaplacian, EuclideanSpace.basisFun_apply]

theorem finiteModePolynomialEval_contDiff
    (p : MvPolynomial (Fin 3) ℝ) :
    ContDiff ℝ 2 (fun y : NSSpace => MvPolynomial.eval y p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      simpa using (contDiff_const : ContDiff ℝ 2 (fun _ : NSSpace => a))
  | add p q hp hq =>
      simpa [MvPolynomial.eval_add] using hp.add hq
  | mul_X p n hp =>
      have hcoord : ContDiff ℝ 2 (fun y : NSSpace => y n) := by
        simpa using (EuclideanSpace.proj n : NSSpace →L[ℝ] ℝ).contDiff
      simpa [MvPolynomial.eval_mul, MvPolynomial.eval_X] using hp.mul hcoord

/-- Polynomial evaluation on `NSSpace` is smooth.  The existing `C^2` version
feeds the Laplacian API; this `C^∞` variant is used by global regularity
interfaces. -/
theorem finiteModePolynomialEval_contDiff_top
    (p : MvPolynomial (Fin 3) ℝ) :
    ContDiff ℝ ∞ (fun y : NSSpace => MvPolynomial.eval y p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      simpa using (contDiff_const : ContDiff ℝ ∞ (fun _ : NSSpace => a))
  | add p q hp hq =>
      simpa [MvPolynomial.eval_add] using hp.add hq
  | mul_X p n hp =>
      have hcoord : ContDiff ℝ ∞ (fun y : NSSpace => y n) := by
        simpa using (EuclideanSpace.proj n : NSSpace →L[ℝ] ℝ).contDiff
      simpa [MvPolynomial.eval_mul, MvPolynomial.eval_X] using hp.mul hcoord

theorem finiteModePolynomialEval_hasGradientAt
    (p : MvPolynomial (Fin 3) ℝ) (x : NSSpace) :
    HasGradientAt (fun y : NSSpace => MvPolynomial.eval y p)
      (finiteModePolynomialEvalGradient p x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hdual :
      (InnerProductSpace.toDual ℝ NSSpace) (finiteModePolynomialEvalGradient p x) =
        finiteModePolynomialEvalFDeriv p x := by
    ext v
    simp [finiteModePolynomialEvalGradient, finiteModePolynomialEvalFDeriv,
      InnerProductSpace.toDual_apply_apply, EuclideanSpace.inner_single_left, mul_comm]
  rw [hdual]
  exact finiteModePolynomialEval_hasFDerivAt p x

theorem finiteModePolynomialEval_gradient
    (p : MvPolynomial (Fin 3) ℝ) (x : NSSpace) :
    gradient (fun y : NSSpace => MvPolynomial.eval y p) x =
      finiteModePolynomialEvalGradient p x := by
  apply HasGradientAt.gradient
  exact finiteModePolynomialEval_hasGradientAt p x

/-- Evaluate a polynomial vector field as an `NSSpace` vector. -/
def finiteModePolynomialVectorFieldEval
    (G : Fin 3 → MvPolynomial (Fin 3) ℝ) : NSSpace → NSSpace :=
  fun x => ∑ j : Fin 3, MvPolynomial.eval x (G j) • EuclideanSpace.single j (1 : ℝ)

@[simp]
theorem finiteModePolynomialVectorFieldEval_apply
    (G : Fin 3 → MvPolynomial (Fin 3) ℝ) (x : NSSpace) (j : Fin 3) :
    finiteModePolynomialVectorFieldEval G x j =
      MvPolynomial.eval x (G j) := by
  simp [finiteModePolynomialVectorFieldEval, Pi.single_apply]

/-- The Fréchet derivative of a polynomial vector field, assembled component by
component from the scalar polynomial derivative formula. -/
def finiteModePolynomialVectorFieldFDeriv
    (U : Fin 3 → MvPolynomial (Fin 3) ℝ) (x : NSSpace) :
    NSSpace →L[ℝ] NSSpace :=
  ∑ j : Fin 3,
    (finiteModePolynomialEvalFDeriv (U j) x).smulRight
      (EuclideanSpace.single j (1 : ℝ))

@[simp]
theorem finiteModePolynomialVectorFieldFDeriv_apply
    (U : Fin 3 → MvPolynomial (Fin 3) ℝ) (x v : NSSpace) (j : Fin 3) :
    finiteModePolynomialVectorFieldFDeriv U x v j =
      ∑ r : Fin 3, v r * MvPolynomial.eval x (MvPolynomial.pderiv r (U j)) := by
  simp [finiteModePolynomialVectorFieldFDeriv, finiteModePolynomialEvalFDeriv_apply,
    Pi.single_apply]

/-- A polynomial vector field has the expected componentwise Fréchet
derivative. -/
theorem finiteModePolynomialVectorFieldEval_hasFDerivAt
    (U : Fin 3 → MvPolynomial (Fin 3) ℝ) (x : NSSpace) :
    HasFDerivAt (finiteModePolynomialVectorFieldEval U)
      (finiteModePolynomialVectorFieldFDeriv U x) x := by
  simpa [finiteModePolynomialVectorFieldEval, finiteModePolynomialVectorFieldFDeriv]
    using
      (HasFDerivAt.sum (u := (Finset.univ : Finset (Fin 3)))
        (fun j _hj =>
          (finiteModePolynomialEval_hasFDerivAt (U j) x).smul_const
            (EuclideanSpace.single j (1 : ℝ))))

theorem finiteModePolynomialVectorFieldEval_contDiff
    (U : Fin 3 → MvPolynomial (Fin 3) ℝ) :
    ContDiff ℝ 2 (finiteModePolynomialVectorFieldEval U) := by
  simpa [finiteModePolynomialVectorFieldEval]
    using
      (ContDiff.sum (s := (Finset.univ : Finset (Fin 3)))
        (fun j _hj => (finiteModePolynomialEval_contDiff (U j)).smul_const
          (EuclideanSpace.single j (1 : ℝ))))

/-- Polynomial vector fields on `NSSpace` are smooth. -/
theorem finiteModePolynomialVectorFieldEval_contDiff_top
    (U : Fin 3 → MvPolynomial (Fin 3) ℝ) :
    ContDiff ℝ ∞ (finiteModePolynomialVectorFieldEval U) := by
  simpa [finiteModePolynomialVectorFieldEval]
    using
      (ContDiff.sum (s := (Finset.univ : Finset (Fin 3)))
        (fun j _hj => (finiteModePolynomialEval_contDiff_top (U j)).smul_const
          (EuclideanSpace.single j (1 : ℝ))))

/-- Polynomial vector field components for a finite-mode reconstructed velocity
when each selected spatial mode is represented by polynomial components. -/
def finiteModePolynomialReconstructedVelocityComponents
    {ι : Type*} [Fintype ι]
    (modePoly : ι → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (a : ℝ → FiniteModeState ι)
    (t : NSTime) : Fin 3 → MvPolynomial (Fin 3) ℝ :=
  fun j => ∑ i : ι, MvPolynomial.C (a t i) * modePoly i j

/-- The projected-RHS acceleration reconstructed from polynomial spatial modes
is again represented componentwise by an explicit polynomial vector field. -/
def finiteModePolynomialReconstructedAccelerationComponents
    {ι : Type*} [Fintype ι]
    (modePoly : ι → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (t : NSTime) : Fin 3 → MvPolynomial (Fin 3) ℝ :=
  fun j => ∑ i : ι,
    MvPolynomial.C (finiteModeProjectedNSRHS C (a t) i) * modePoly i j

/-- Polynomial components for the convection term `(u · ∇)u`. -/
def finiteModePolynomialConvectionComponents
    (U : Fin 3 → MvPolynomial (Fin 3) ℝ) :
    Fin 3 → MvPolynomial (Fin 3) ℝ :=
  fun j => ∑ r : Fin 3, U r * MvPolynomial.pderiv r (U j)

/-- Polynomial components for the spatial Laplacian `Δu`. -/
def finiteModePolynomialLaplacianComponents
    (U : Fin 3 → MvPolynomial (Fin 3) ℝ) :
    Fin 3 → MvPolynomial (Fin 3) ℝ :=
  fun j => finiteModePolynomialScalarLaplacian (U j)

/-- Formal polynomial components for the non-pressure finite-mode momentum
defect.  The acceleration and convection pieces are computed from the
polynomial mode data; `lapPoly` records the polynomial representation of the
actual spatial Laplacian slice. -/
def finiteModePolynomialNonPressureDefectComponents
    {ι : Type*} [Fintype ι]
    (ν : ℝ)
    (modePoly : ι → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (lapPoly : NSTime → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (t : NSTime) : Fin 3 → MvPolynomial (Fin 3) ℝ :=
  fun j =>
    finiteModePolynomialReconstructedAccelerationComponents modePoly C a t j +
      finiteModePolynomialConvectionComponents
        (finiteModePolynomialReconstructedVelocityComponents modePoly a t) j -
        MvPolynomial.C ν * lapPoly t j

/-- The polynomial vector field that a pressure gradient must equal in order to
close the non-pressure finite-mode defect. -/
def finiteModePolynomialClosingPressureGradientComponents
    {ι : Type*} [Fintype ι]
    (ν : ℝ)
    (modePoly : ι → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (lapPoly : NSTime → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (t : NSTime) : Fin 3 → MvPolynomial (Fin 3) ℝ :=
  fun j => -finiteModePolynomialNonPressureDefectComponents ν modePoly C a lapPoly t j

/-- If each selected finite mode is represented by polynomial components, then
the reconstructed velocity slice is represented by the corresponding polynomial
linear combination. -/
theorem finiteModePolynomialReconstructedVelocity_eq_eval
    {ι : Type*} [Fintype ι]
    (modePoly : ι → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (a : ℝ → FiniteModeState ι)
    (t : NSTime) (x : NSSpace) :
    finiteModeReconstructedVelocity
        (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y) a t x =
      finiteModePolynomialVectorFieldEval
        (finiteModePolynomialReconstructedVelocityComponents modePoly a t) x := by
  ext j
  simp [finiteModePolynomialReconstructedVelocityComponents,
    finiteModePolynomialVectorFieldEval_apply, MvPolynomial.eval_mul]

/-- If each selected finite mode is represented by polynomial components, then
the projected acceleration slice is represented by the corresponding polynomial
linear combination. -/
theorem finiteModePolynomialReconstructedAcceleration_eq_eval
    {ι : Type*} [Fintype ι]
    (modePoly : ι → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (t : NSTime) (x : NSSpace) :
    finiteModeReconstructedAcceleration
        (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y) C a t x =
      finiteModePolynomialVectorFieldEval
        (finiteModePolynomialReconstructedAccelerationComponents modePoly C a t) x := by
  ext j
  simp [finiteModePolynomialReconstructedAccelerationComponents,
    finiteModePolynomialVectorFieldEval_apply, MvPolynomial.eval_mul]

/-- Concrete convection of a polynomial vector field is the formal polynomial
vector field with components `Σ_r u_r ∂_r u_j`. -/
theorem finiteModePolynomialVectorField_spatialConvection
    (U : NSTime → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (t : NSTime) (x : NSSpace) :
    spatialConvection
        (fun s y => finiteModePolynomialVectorFieldEval (U s) y) t x =
      finiteModePolynomialVectorFieldEval
        (finiteModePolynomialConvectionComponents (U t)) x := by
  unfold spatialConvection spatialFDeriv
  rw [(finiteModePolynomialVectorFieldEval_hasFDerivAt (U t) x).fderiv]
  ext j
  simp [finiteModePolynomialConvectionComponents,
    finiteModePolynomialVectorFieldEval_apply, MvPolynomial.eval_mul]

/-- The concrete convection term for a finite-mode reconstruction from
polynomial spatial modes is represented by the formal polynomial convection of
the reconstructed polynomial velocity components. -/
theorem finiteModePolynomialReconstructedVelocity_spatialConvection
    {ι : Type*} [Fintype ι]
    (modePoly : ι → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (a : ℝ → FiniteModeState ι)
    (t : NSTime) (x : NSSpace) :
    spatialConvection
        (finiteModeReconstructedVelocity
          (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y) a) t x =
      finiteModePolynomialVectorFieldEval
        (finiteModePolynomialConvectionComponents
          (finiteModePolynomialReconstructedVelocityComponents modePoly a t)) x := by
  unfold spatialConvection spatialFDeriv
  have hslice :
      (fun y : NSSpace =>
        finiteModeReconstructedVelocity
          (fun i z => finiteModePolynomialVectorFieldEval (modePoly i) z) a t y) =
        finiteModePolynomialVectorFieldEval
          (finiteModePolynomialReconstructedVelocityComponents modePoly a t) := by
    funext y
    exact finiteModePolynomialReconstructedVelocity_eq_eval modePoly a t y
  rw [hslice]
  rw [finiteModePolynomialReconstructedVelocity_eq_eval modePoly a t x]
  rw [(finiteModePolynomialVectorFieldEval_hasFDerivAt
    (finiteModePolynomialReconstructedVelocityComponents modePoly a t) x).fderiv]
  ext j
  simp [finiteModePolynomialConvectionComponents,
    finiteModePolynomialVectorFieldEval_apply, MvPolynomial.eval_mul]

/-- Concrete spatial Laplacian of a polynomial vector field is the formal
componentwise polynomial Laplacian. -/
theorem finiteModePolynomialVectorField_spatialLaplacian
    (U : NSTime → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (t : NSTime) (x : NSSpace) :
    spatialLaplacian
        (fun s y => finiteModePolynomialVectorFieldEval (U s) y) t x =
      finiteModePolynomialVectorFieldEval
        (finiteModePolynomialLaplacianComponents (U t)) x := by
  unfold spatialLaplacian
  ext j
  have hproj :
      Δ ((EuclideanSpace.proj j : NSSpace →L[ℝ] ℝ) ∘
          finiteModePolynomialVectorFieldEval (U t)) x =
        (EuclideanSpace.proj j : NSSpace →L[ℝ] ℝ)
          (Δ (finiteModePolynomialVectorFieldEval (U t)) x) := by
    simpa [Function.comp] using
      ((finiteModePolynomialVectorFieldEval_contDiff (U t)).contDiffAt
        (x := x)).laplacian_CLM_comp_left
          (l := (EuclideanSpace.proj j : NSSpace →L[ℝ] ℝ))
  change (EuclideanSpace.proj j : NSSpace →L[ℝ] ℝ)
      (Δ (finiteModePolynomialVectorFieldEval (U t)) x) =
    (finiteModePolynomialVectorFieldEval
      (finiteModePolynomialLaplacianComponents (U t)) x) j
  rw [← hproj]
  rw [show ((EuclideanSpace.proj j : NSSpace →L[ℝ] ℝ) ∘
      finiteModePolynomialVectorFieldEval (U t)) =
        (fun y : NSSpace => MvPolynomial.eval y ((U t) j)) by
    funext y
    simp [Function.comp, finiteModePolynomialVectorFieldEval_apply]]
  simpa [finiteModePolynomialVectorFieldEval_apply,
    finiteModePolynomialLaplacianComponents] using
      finiteModePolynomialEval_laplacian ((U t) j) x

/-- The concrete spatial Laplacian of a finite-mode reconstruction from
polynomial spatial modes is represented by the formal componentwise polynomial
Laplacian of the reconstructed polynomial velocity components. -/
theorem finiteModePolynomialReconstructedVelocity_spatialLaplacian
    {ι : Type*} [Fintype ι]
    (modePoly : ι → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (a : ℝ → FiniteModeState ι)
    (t : NSTime) (x : NSSpace) :
    spatialLaplacian
        (finiteModeReconstructedVelocity
          (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y) a) t x =
      finiteModePolynomialVectorFieldEval
        (finiteModePolynomialLaplacianComponents
          (finiteModePolynomialReconstructedVelocityComponents modePoly a t)) x := by
  rw [show finiteModeReconstructedVelocity
        (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y) a =
      fun s y => finiteModePolynomialVectorFieldEval
        (finiteModePolynomialReconstructedVelocityComponents modePoly a s) y by
    funext s y
    exact finiteModePolynomialReconstructedVelocity_eq_eval modePoly a s y]
  exact finiteModePolynomialVectorField_spatialLaplacian
    (fun s => finiteModePolynomialReconstructedVelocityComponents modePoly a s) t x

/-- Once the Laplacian slice of a polynomial finite-mode reconstruction is
itself represented by polynomial components, the whole non-pressure momentum
defect is represented by the explicit polynomial expression above. -/
theorem finiteModePolynomialNonPressureDefect_eq_eval_of_laplacian
    {ι : Type*} [Fintype ι]
    (ν : ℝ)
    (modePoly : ι → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (lapPoly : NSTime → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (hLap : ∀ t x,
      spatialLaplacian
          (finiteModeReconstructedVelocity
            (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y) a) t x =
        finiteModePolynomialVectorFieldEval (lapPoly t) x)
    (t : NSTime) (x : NSSpace) :
    finiteModeNonPressureMomentumDefect ν
        (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y) C a t x =
      finiteModePolynomialVectorFieldEval
        (finiteModePolynomialNonPressureDefectComponents ν modePoly C a lapPoly t) x := by
  unfold finiteModeNonPressureMomentumDefect
  rw [finiteModePolynomialReconstructedAcceleration_eq_eval modePoly C a t x,
    finiteModePolynomialReconstructedVelocity_spatialConvection modePoly a t x,
    hLap t x]
  ext j
  simp [finiteModePolynomialNonPressureDefectComponents,
    finiteModePolynomialVectorFieldEval_apply, MvPolynomial.eval_mul]

/-- For polynomial spatial modes, the non-pressure finite-mode momentum defect
has an explicit polynomial representative with no external Laplacian
representation hypothesis. -/
theorem finiteModePolynomialNonPressureDefect_eq_eval
    {ι : Type*} [Fintype ι]
    (ν : ℝ)
    (modePoly : ι → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (t : NSTime) (x : NSSpace) :
    finiteModeNonPressureMomentumDefect ν
        (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y) C a t x =
      finiteModePolynomialVectorFieldEval
        (finiteModePolynomialNonPressureDefectComponents ν modePoly C a
          (fun s => finiteModePolynomialLaplacianComponents
            (finiteModePolynomialReconstructedVelocityComponents modePoly a s)) t) x := by
  exact finiteModePolynomialNonPressureDefect_eq_eval_of_laplacian
    ν modePoly C a
    (fun s => finiteModePolynomialLaplacianComponents
      (finiteModePolynomialReconstructedVelocityComponents modePoly a s))
    (fun s y => finiteModePolynomialReconstructedVelocity_spatialLaplacian modePoly a s y)
    t x

/-- The concrete scalar pressure mode associated to a curl-free polynomial
vector field. -/
def finiteModePolynomialPressureMode
    (G : Fin 3 → MvPolynomial (Fin 3) ℝ) : NSSpace → ℝ :=
  fun x => MvPolynomial.eval x (finiteModePolynomialPressurePrimitive G)

theorem finiteModePolynomialPressureMode_differentiableAt
    (G : Fin 3 → MvPolynomial (Fin 3) ℝ) (x : NSSpace) :
    DifferentiableAt ℝ (finiteModePolynomialPressureMode G) x :=
  (finiteModePolynomialEval_hasFDerivAt
    (finiteModePolynomialPressurePrimitive G) x).differentiableAt

/-- General polynomial pressure reconstruction: curl-free polynomial vector
fields are actual spatial gradients of the explicit polynomial primitive. -/
theorem finiteModePolynomialPressureMode_gradient
    (G : Fin 3 → MvPolynomial (Fin 3) ℝ)
    (hcurl : ∀ i j,
      MvPolynomial.pderiv i (G j) =
        MvPolynomial.pderiv j (G i))
    (x : NSSpace) :
    gradient (finiteModePolynomialPressureMode G) x =
      finiteModePolynomialVectorFieldEval G x := by
  unfold finiteModePolynomialPressureMode
  rw [finiteModePolynomialEval_gradient]
  ext j
  rw [finiteModePolynomialEvalGradient_apply, finiteModePolynomialVectorFieldEval_apply,
    finiteModePolynomialPressurePrimitive_pderiv G hcurl j]

theorem finiteModePolynomialPressureMode_spatialPressureGradient
    (G : Fin 3 → MvPolynomial (Fin 3) ℝ)
    (hcurl : ∀ i j,
      MvPolynomial.pderiv i (G j) =
        MvPolynomial.pderiv j (G i))
    (t : NSTime) (x : NSSpace) :
    spatialPressureGradient (fun _ y => finiteModePolynomialPressureMode G y) t x =
      finiteModePolynomialVectorFieldEval G x := by
  unfold spatialPressureGradient
  exact finiteModePolynomialPressureMode_gradient G hcurl x

/-- A pointwise equality between the actual spatial pressure gradient of a
polynomial pressure and a polynomial vector field is equivalent to coefficient
level derivative identities. -/
theorem finiteModePolynomialPressureGradient_eq_eval_iff_pderiv
    (p : MvPolynomial (Fin 3) ℝ)
    (G : Fin 3 → MvPolynomial (Fin 3) ℝ)
    (t : NSTime) :
    (∀ x : NSSpace,
      spatialPressureGradient (fun _ y => MvPolynomial.eval y p) t x =
        finiteModePolynomialVectorFieldEval G x) ↔
      ∀ j, MvPolynomial.pderiv j p = G j := by
  constructor
  · intro h j
    apply MvPolynomial.funext
    intro x
    have hcomp := congrArg (fun v : NSSpace => v j) (h (WithLp.toLp 2 x))
    simpa [spatialPressureGradient, finiteModePolynomialEval_gradient,
      finiteModePolynomialEvalGradient_apply, finiteModePolynomialVectorFieldEval_apply]
      using hcomp
  · intro hp x
    unfold spatialPressureGradient
    rw [finiteModePolynomialEval_gradient]
    ext j
    rw [finiteModePolynomialEvalGradient_apply, finiteModePolynomialVectorFieldEval_apply,
      hp j]

/-- Time-dependent version of
`finiteModePolynomialPressureGradient_eq_eval_iff_pderiv`. -/
theorem finiteModeTimePolynomialPressureGradient_eq_eval_iff_pderiv
    (P : NSTime → MvPolynomial (Fin 3) ℝ)
    (G : NSTime → Fin 3 → MvPolynomial (Fin 3) ℝ) :
    (∀ t x,
      spatialPressureGradient (fun s y => MvPolynomial.eval y (P s)) t x =
        finiteModePolynomialVectorFieldEval (G t) x) ↔
      ∀ t j, MvPolynomial.pderiv j (P t) = G t j := by
  constructor
  · intro h t
    exact (finiteModePolynomialPressureGradient_eq_eval_iff_pderiv
      (P t) (G t) t).mp (h t)
  · intro hp t
    exact (finiteModePolynomialPressureGradient_eq_eval_iff_pderiv
      (P t) (G t) t).mpr (hp t)

/-- Time-dependent polynomial pressure existence is exactly curl-freeness of
the polynomial vector field at every time slice.  This is the polynomial
Helmholtz/Poincare pressure theorem through the concrete
`spatialPressureGradient` API. -/
theorem finiteModeTimePolynomialPressureGradient_exists_iff_curlFree
    (G : NSTime → Fin 3 → MvPolynomial (Fin 3) ℝ) :
    (∃ P : NSTime → MvPolynomial (Fin 3) ℝ,
        ∀ t x,
          spatialPressureGradient (fun s y => MvPolynomial.eval y (P s)) t x =
            finiteModePolynomialVectorFieldEval (G t) x) ↔
      ∀ t i j, MvPolynomial.pderiv i (G t j) =
        MvPolynomial.pderiv j (G t i) := by
  constructor
  · rintro ⟨P, hP⟩ t
    have hp : ∀ t j, MvPolynomial.pderiv j (P t) = G t j :=
      (finiteModeTimePolynomialPressureGradient_eq_eval_iff_pderiv P G).mp hP
    exact (finiteModePolynomialPressurePrimitive_exists_iff_curlFree (G t)).mp
      ⟨P t, hp t⟩
  · intro hcurl
    refine ⟨fun t => finiteModePolynomialPressurePrimitive (G t), ?_⟩
    exact (finiteModeTimePolynomialPressureGradient_eq_eval_iff_pderiv
      (fun t => finiteModePolynomialPressurePrimitive (G t)) G).mpr
      (fun t j => finiteModePolynomialPressurePrimitive_pderiv (G t) (hcurl t) j)

/-- If the non-pressure finite-mode defect is represented by a polynomial
vector field on a time set, then polynomial pressure closure of that defect is
equivalent to curl-freeness of the representing polynomial vector field on the
same time set. -/
theorem finiteModePolynomialPressure_closes_nonPressureDefectOn_iff_curlFree_of_polynomialDefect
    {ι : Type*} [Fintype ι]
    (I : Set NSTime)
    (ν : ℝ)
    (mode : ι → NSSpace → NSSpace)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (G : NSTime → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (hdefect : ∀ t ∈ I,
      -finiteModeNonPressureMomentumDefect ν mode C a t =
        finiteModePolynomialVectorFieldEval (G t)) :
    (∃ P : NSTime → MvPolynomial (Fin 3) ℝ,
        ∀ t ∈ I, ∀ x : NSSpace,
          spatialPressureGradient (fun s y => MvPolynomial.eval y (P s)) t x =
            -finiteModeNonPressureMomentumDefect ν mode C a t x) ↔
      ∀ t ∈ I, ∀ i j, MvPolynomial.pderiv i (G t j) =
        MvPolynomial.pderiv j (G t i) := by
  constructor
  · rintro ⟨P, hP⟩ t ht
    have hgrad :
        ∀ x : NSSpace,
          spatialPressureGradient (fun s y => MvPolynomial.eval y (P s)) t x =
            finiteModePolynomialVectorFieldEval (G t) x := by
      intro x
      have hdefx :
          -finiteModeNonPressureMomentumDefect ν mode C a t x =
            finiteModePolynomialVectorFieldEval (G t) x := by
        simpa using congrFun (hdefect t ht) x
      rw [hP t ht x, hdefx]
    have hpderiv :
        ∀ j, MvPolynomial.pderiv j (P t) = G t j :=
      (finiteModePolynomialPressureGradient_eq_eval_iff_pderiv
        (P t) (G t) t).mp hgrad
    exact (finiteModePolynomialPressurePrimitive_exists_iff_curlFree (G t)).mp
      ⟨P t, hpderiv⟩
  · intro hcurl
    refine ⟨fun t => finiteModePolynomialPressurePrimitive (G t), ?_⟩
    intro t ht x
    have hgrad :
        spatialPressureGradient
            (fun s y => MvPolynomial.eval y
              (finiteModePolynomialPressurePrimitive (G s))) t x =
          finiteModePolynomialVectorFieldEval (G t) x := by
      unfold spatialPressureGradient
      rw [finiteModePolynomialEval_gradient]
      ext j
      rw [finiteModePolynomialEvalGradient_apply, finiteModePolynomialVectorFieldEval_apply,
        finiteModePolynomialPressurePrimitive_pderiv (G t) (hcurl t ht) j]
    have hdefx :
        -finiteModeNonPressureMomentumDefect ν mode C a t x =
          finiteModePolynomialVectorFieldEval (G t) x := by
      simpa using congrFun (hdefect t ht) x
    exact hgrad.trans hdefx.symm

/-- A one-mode spatial forcing direction shaped like the shear vector field
`x₁ e₀`.  It is used below as a concrete obstruction to the idea that the
abstract projected finite-mode RHS forces the full spatial residual to be a
gradient. -/
def finiteModeShearAccelerationMode (_ : PUnit) : NSSpace → NSSpace :=
  fun x => EuclideanSpace.single (0 : Fin 3) (x (1 : Fin 3))

/-- One-mode projected coefficients with unit forcing and no linear or
quadratic terms. -/
def finiteModeUnitForcingCoefficients : FiniteModeProjectedNSCoefficients PUnit where
  forcing := fun _ => 1
  linear := fun _ _ => 0
  quadratic := fun _ _ _ => 0

/-- The identically zero coefficient curve for a one-mode system. -/
def finiteModeZeroCoefficientCurve : ℝ → FiniteModeState PUnit :=
  fun _ _ => 0

/-- The identity coefficient curve for the one-mode unit-forcing system. -/
def finiteModeIdentityCoefficientCurve : ℝ → FiniteModeState PUnit :=
  fun t _ => t

/-- One-mode projected coefficients with constant scalar forcing and no linear
or quadratic terms. -/
def finiteModeScalarForcingCoefficients
    (c : ℝ) : FiniteModeProjectedNSCoefficients PUnit.{1} where
  forcing := fun _ => c
  linear := fun _ _ => 0
  quadratic := fun _ _ _ => 0

/-- A one-mode coefficient curve with arbitrary scalar amplitude `g(t)`. -/
def finiteModeScalarAmplitudeCoefficientCurve
    (g : NSTime → ℝ) : NSTime → FiniteModeState PUnit.{1} :=
  fun t _ => g t

/-- If the scalar amplitude has derivative `gdot t`, then the corresponding
one-mode coefficient curve solves the projected ODE with constant forcing
`gdot t` at that time. -/
theorem finiteModeScalarAmplitudeCoefficientCurve_hasDerivAt
    (g gdot : NSTime → ℝ) {t : NSTime}
    (hg : HasDerivAt g (gdot t) t) :
    HasDerivAt (finiteModeScalarAmplitudeCoefficientCurve g)
      (finiteModeProjectedNSRHS
        (finiteModeScalarForcingCoefficients (gdot t))
        (finiteModeScalarAmplitudeCoefficientCurve g t)) t := by
  rw [hasDerivAt_pi]
  intro i
  cases i
  simpa [finiteModeScalarAmplitudeCoefficientCurve, finiteModeProjectedNSRHS,
    finiteModeScalarForcingCoefficients] using hg

/-- The identity curve solves the abstract one-mode projected ODE with unit
forcing and no linear or quadratic terms. -/
theorem finiteModeIdentityCoefficientCurve_hasDerivAt
    (t : NSTime) :
    HasDerivAt finiteModeIdentityCoefficientCurve
      (finiteModeProjectedNSRHS finiteModeUnitForcingCoefficients
        (finiteModeIdentityCoefficientCurve t)) t := by
  rw [hasDerivAt_pi]
  intro i
  cases i
  simpa [finiteModeIdentityCoefficientCurve, finiteModeProjectedNSRHS,
    finiteModeUnitForcingCoefficients] using (hasDerivAt_id t)

/-- The polynomial vector field `(X₁, 0, 0)`, matching
`finiteModeShearAccelerationMode`. -/
def finiteModeShearAccelerationPolynomialVectorField :
    Fin 3 → MvPolynomial (Fin 3) ℝ :=
  fun j => if j = (0 : Fin 3) then MvPolynomial.X (1 : Fin 3) else 0

/-- With zero coefficient velocity, unit projected forcing into the shear mode,
and zero viscosity, the non-pressure finite-mode residual is the polynomial
vector field `(X₁, 0, 0)`. -/
theorem finiteModeShearAcceleration_nonPressureDefect_eq_polynomial
    (t : NSTime) (x : NSSpace) :
    finiteModeNonPressureMomentumDefect (0 : ℝ) finiteModeShearAccelerationMode
        finiteModeUnitForcingCoefficients finiteModeZeroCoefficientCurve t x =
      finiteModePolynomialVectorFieldEval
        finiteModeShearAccelerationPolynomialVectorField x := by
  ext j
  fin_cases j <;>
    simp [finiteModeNonPressureMomentumDefect, finiteModeReconstructedAcceleration,
      finiteModeReconstructedVelocity, finiteModeReconstructionCLM, finiteModeProjectedNSRHS,
      finiteModeUnitForcingCoefficients, finiteModeZeroCoefficientCurve,
      finiteModeShearAccelerationMode, spatialConvection, spatialLaplacian,
      finiteModeShearAccelerationPolynomialVectorField,
      finiteModePolynomialVectorFieldEval, Pi.single_apply]

/-- The identity coefficient reconstruction is the time-dependent linear shear
slice `x ↦ t x₁ e₀`. -/
theorem finiteModeShearAcceleration_identityVelocity_eq_linearShear
    (t : NSTime) (x : NSSpace) :
    finiteModeReconstructedVelocity finiteModeShearAccelerationMode
        finiteModeIdentityCoefficientCurve t x =
      linearShearVelocityField t t x := by
  ext j
  fin_cases j <;>
    simp [finiteModeReconstructedVelocity, finiteModeReconstructionCLM,
      finiteModeIdentityCoefficientCurve, finiteModeShearAccelerationMode,
      linearShearVelocityField, linearShearInitialVelocity,
      linearShearMap, nsCoord0, nsCoord1, ContinuousLinearMap.smulRight_apply,
      mul_comm]

/-- The identity-coefficient shear reconstruction has zero convection at every
point. -/
theorem finiteModeShearAcceleration_identity_spatialConvection_zero
    (t : NSTime) (x : NSSpace) :
    spatialConvection
        (finiteModeReconstructedVelocity finiteModeShearAccelerationMode
          finiteModeIdentityCoefficientCurve) t x = 0 := by
  unfold spatialConvection
  have hfderiv :
      spatialFDeriv
          (finiteModeReconstructedVelocity finiteModeShearAccelerationMode
            finiteModeIdentityCoefficientCurve) t x =
        spatialFDeriv (linearShearVelocityField t) t x := by
    unfold spatialFDeriv
    congr 1
    funext y
    exact finiteModeShearAcceleration_identityVelocity_eq_linearShear t y
  rw [hfderiv, finiteModeShearAcceleration_identityVelocity_eq_linearShear]
  exact spatialConvection_linearShearVelocityField t t x

/-- The identity-coefficient shear reconstruction has zero spatial Laplacian at
every point. -/
theorem finiteModeShearAcceleration_identity_spatialLaplacian_zero
    (t : NSTime) (x : NSSpace) :
    spatialLaplacian
        (finiteModeReconstructedVelocity finiteModeShearAccelerationMode
          finiteModeIdentityCoefficientCurve) t x = 0 := by
  unfold spatialLaplacian
  have hslice :
      (fun y : NSSpace =>
        finiteModeReconstructedVelocity finiteModeShearAccelerationMode
          finiteModeIdentityCoefficientCurve t y) =
      fun y : NSSpace => linearShearVelocityField t t y := by
    funext y
    exact finiteModeShearAcceleration_identityVelocity_eq_linearShear t y
  rw [hslice]
  exact spatialLaplacian_linearShearVelocityField t t x

/-- Even when the coefficient curve is an actual solution of the unit-forcing
projected ODE, the abstract finite-mode non-pressure defect can be the
non-gradient shear polynomial `(X₁, 0, 0)`. -/
theorem finiteModeShearAcceleration_solution_nonPressureDefect_eq_polynomial
    (t : NSTime) (x : NSSpace) :
    finiteModeNonPressureMomentumDefect (0 : ℝ) finiteModeShearAccelerationMode
        finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve t x =
      finiteModePolynomialVectorFieldEval
        finiteModeShearAccelerationPolynomialVectorField x := by
  unfold finiteModeNonPressureMomentumDefect
  rw [finiteModeShearAcceleration_identity_spatialConvection_zero t x,
    finiteModeShearAcceleration_identity_spatialLaplacian_zero t x]
  ext j
  fin_cases j <;>
    simp [finiteModeReconstructedAcceleration,
      finiteModeReconstructedVelocity, finiteModeReconstructionCLM, finiteModeProjectedNSRHS,
      finiteModeUnitForcingCoefficients, finiteModeIdentityCoefficientCurve,
      finiteModeShearAccelerationMode,
      finiteModeShearAccelerationPolynomialVectorField,
      finiteModePolynomialVectorFieldEval, Pi.single_apply]

/-- The shear acceleration polynomial vector field is not curl-free. -/
theorem finiteModeShearAccelerationPolynomialVectorField_not_curlFree :
    ¬ (∀ i j,
      MvPolynomial.pderiv i (finiteModeShearAccelerationPolynomialVectorField j) =
        MvPolynomial.pderiv j (finiteModeShearAccelerationPolynomialVectorField i)) := by
  intro h
  have h10 := h (1 : Fin 3) (0 : Fin 3)
  norm_num [finiteModeShearAccelerationPolynomialVectorField] at h10

/-- Consequently the concrete shear acceleration residual has no polynomial
pressure primitive in its natural polynomial representation. -/
theorem finiteModeShearAccelerationPolynomialVectorField_no_pressurePrimitive :
    ¬ ∃ p : MvPolynomial (Fin 3) ℝ, ∀ j,
      MvPolynomial.pderiv j p =
        finiteModeShearAccelerationPolynomialVectorField j := by
  intro hp
  exact finiteModeShearAccelerationPolynomialVectorField_not_curlFree
    ((finiteModePolynomialPressurePrimitive_exists_iff_curlFree
      finiteModeShearAccelerationPolynomialVectorField).mp hp)

/-- The sign required to close momentum also has no polynomial pressure
primitive: if `∇p = -(X₁ e₀)`, then `-p` would primitive `X₁ e₀`. -/
theorem finiteModeShearAccelerationPolynomialVectorField_no_negative_pressurePrimitive :
    ¬ ∃ p : MvPolynomial (Fin 3) ℝ, ∀ j,
      MvPolynomial.pderiv j p =
        -finiteModeShearAccelerationPolynomialVectorField j := by
  intro hp
  rcases hp with ⟨p, hp⟩
  exact finiteModeShearAccelerationPolynomialVectorField_no_pressurePrimitive
    ⟨-p, by
      intro j
      calc
        MvPolynomial.pderiv j (-p) =
            -MvPolynomial.pderiv j p := by
              simp
        _ = finiteModeShearAccelerationPolynomialVectorField j := by
              rw [hp j]
              simp⟩

/-- No time-dependent scalar polynomial pressure can satisfy the coefficient
obligation `∇p(t) = -(X₁ e₀)` required to close the identity-coefficient shear
residual. -/
theorem finiteModeShearAcceleration_solution_no_timeDependentPolynomialPressurePrimitive :
    ¬ ∃ P : NSTime → MvPolynomial (Fin 3) ℝ, ∀ t j,
      MvPolynomial.pderiv j (P t) =
        -finiteModeShearAccelerationPolynomialVectorField j := by
  intro hP
  rcases hP with ⟨P, hP⟩
  exact finiteModeShearAccelerationPolynomialVectorField_no_negative_pressurePrimitive
    ⟨P 0, hP 0⟩

/-- No time-dependent scalar polynomial pressure can close the identity-curve
shear residual through the actual pointwise `spatialPressureGradient` API.  The
proof reflects pointwise equality of polynomial gradients back to coefficient
equality by `MvPolynomial.funext`. -/
theorem finiteModeShearAcceleration_solution_no_pointwisePolynomialPressureGradient :
    ¬ ∃ P : NSTime → MvPolynomial (Fin 3) ℝ,
      ∀ t x,
        spatialPressureGradient (fun s y => MvPolynomial.eval y (P s)) t x =
          -finiteModeNonPressureMomentumDefect (0 : ℝ) finiteModeShearAccelerationMode
            finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve t x := by
  intro hP
  rcases hP with ⟨P, hP⟩
  exact finiteModeShearAccelerationPolynomialVectorField_no_negative_pressurePrimitive
    ⟨P 0, by
      intro j
      exact
        (finiteModeTimePolynomialPressureGradient_eq_eval_iff_pderiv P
          (fun _ j => -finiteModeShearAccelerationPolynomialVectorField j)).mp
          (by
            intro t x
            rw [hP t x,
              finiteModeShearAcceleration_solution_nonPressureDefect_eq_polynomial]
            ext k
            simp [finiteModePolynomialVectorFieldEval_apply])
          0 j⟩

/-- Obstruction to the universal residual-curl-free claim for the abstract
finite-mode API: the projected ODE can force the zero velocity curve in a
non-gradient shear direction.  Additional projection/Leray structure is needed
before the polynomial pressure theorem can close the residual. -/
theorem finiteModeProjectedNS_nonPressureDefect_curlFree_not_forced_obstruction :
    (∀ t : NSTime,
      finiteModeNonPressureMomentumDefect (0 : ℝ) finiteModeShearAccelerationMode
          finiteModeUnitForcingCoefficients finiteModeZeroCoefficientCurve t =
        finiteModePolynomialVectorFieldEval
          finiteModeShearAccelerationPolynomialVectorField) ∧
      ¬ ∃ p : MvPolynomial (Fin 3) ℝ, ∀ j,
        MvPolynomial.pderiv j p =
          finiteModeShearAccelerationPolynomialVectorField j := by
  constructor
  · intro t
    funext x
    exact finiteModeShearAcceleration_nonPressureDefect_eq_polynomial t x
  · exact finiteModeShearAccelerationPolynomialVectorField_no_pressurePrimitive

/-- Stronger obstruction to the universal residual-curl-free claim: the
counterexample can use an actual coefficient solution of the abstract projected
ODE.  Thus the missing pressure theorem needs an additional Helmholtz/Leray
compatibility hypothesis tying the coefficient ODE to the spatial residual. -/
theorem finiteModeProjectedNS_coefficientSolution_nonPressureDefect_curlFree_not_forced_obstruction :
    (∀ t : NSTime,
      HasDerivAt finiteModeIdentityCoefficientCurve
        (finiteModeProjectedNSRHS finiteModeUnitForcingCoefficients
          (finiteModeIdentityCoefficientCurve t)) t) ∧
      (∀ t : NSTime,
        finiteModeNonPressureMomentumDefect (0 : ℝ) finiteModeShearAccelerationMode
            finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve t =
          finiteModePolynomialVectorFieldEval
            finiteModeShearAccelerationPolynomialVectorField) ∧
      ¬ ∃ p : MvPolynomial (Fin 3) ℝ, ∀ j,
        MvPolynomial.pderiv j p =
          finiteModeShearAccelerationPolynomialVectorField j := by
  refine ⟨finiteModeIdentityCoefficientCurve_hasDerivAt, ?_, ?_⟩
  · intro t
    funext x
    exact finiteModeShearAcceleration_solution_nonPressureDefect_eq_polynomial t x
  · exact finiteModeShearAccelerationPolynomialVectorField_no_pressurePrimitive

/-- The coefficient-solution obstruction with the sign needed by the momentum
equation: even time-dependent polynomial pressures cannot close the shear
residual produced by the abstract projected ODE. -/
theorem finiteModeProjectedNS_coefficientSolution_no_polynomialPressurePrimitive_obstruction :
    (∀ t : NSTime,
      HasDerivAt finiteModeIdentityCoefficientCurve
        (finiteModeProjectedNSRHS finiteModeUnitForcingCoefficients
          (finiteModeIdentityCoefficientCurve t)) t) ∧
      (∀ t : NSTime,
        finiteModeNonPressureMomentumDefect (0 : ℝ) finiteModeShearAccelerationMode
            finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve t =
          finiteModePolynomialVectorFieldEval
            finiteModeShearAccelerationPolynomialVectorField) ∧
      ¬ ∃ P : NSTime → MvPolynomial (Fin 3) ℝ, ∀ t j,
        MvPolynomial.pderiv j (P t) =
          -finiteModeShearAccelerationPolynomialVectorField j := by
  refine ⟨finiteModeIdentityCoefficientCurve_hasDerivAt, ?_, ?_⟩
  · intro t
    funext x
    exact finiteModeShearAcceleration_solution_nonPressureDefect_eq_polynomial t x
  · exact
      finiteModeShearAcceleration_solution_no_timeDependentPolynomialPressurePrimitive

/-- Pointwise version of the coefficient-solution obstruction: the actual
`spatialPressureGradient` of a time-dependent polynomial pressure cannot close
the shear residual produced by the abstract projected ODE. -/
theorem finiteModeProjectedNS_coefficientSolution_no_pointwisePolynomialPressureGradient_obstruction :
    (∀ t : NSTime,
      HasDerivAt finiteModeIdentityCoefficientCurve
        (finiteModeProjectedNSRHS finiteModeUnitForcingCoefficients
          (finiteModeIdentityCoefficientCurve t)) t) ∧
      (∀ t : NSTime,
        finiteModeNonPressureMomentumDefect (0 : ℝ) finiteModeShearAccelerationMode
            finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve t =
          finiteModePolynomialVectorFieldEval
            finiteModeShearAccelerationPolynomialVectorField) ∧
      ¬ ∃ P : NSTime → MvPolynomial (Fin 3) ℝ,
        ∀ t x,
          spatialPressureGradient (fun s y => MvPolynomial.eval y (P s)) t x =
            -finiteModeNonPressureMomentumDefect (0 : ℝ) finiteModeShearAccelerationMode
              finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve t x := by
  refine ⟨finiteModeIdentityCoefficientCurve_hasDerivAt, ?_, ?_⟩
  · intro t
    funext x
    exact finiteModeShearAcceleration_solution_nonPressureDefect_eq_polynomial t x
  · exact finiteModeShearAcceleration_solution_no_pointwisePolynomialPressureGradient

/-- Mixed quadratic pressure mode `x ↦ x_i * x_j`. -/
def finiteModeMixedQuadraticPressureMode (i j : Fin 3) : NSSpace → ℝ :=
  fun x => x i * x j

/-- Mixed quadratic pressure modes are smooth. -/
theorem finiteModeMixedQuadraticPressureMode_contDiff
    (i j : Fin 3) :
    ContDiff ℝ ∞ (finiteModeMixedQuadraticPressureMode i j) := by
  unfold finiteModeMixedQuadraticPressureMode
  have hi : ContDiff ℝ ∞ (fun x : NSSpace => x i) := by
    simpa using (EuclideanSpace.proj i : NSSpace →L[ℝ] ℝ).contDiff
  have hj : ContDiff ℝ ∞ (fun x : NSSpace => x j) := by
    simpa using (EuclideanSpace.proj j : NSSpace →L[ℝ] ℝ).contDiff
  exact hi.mul hj

/-- Mixed quadratic pressure modes are differentiable. -/
theorem finiteModeMixedQuadraticPressureMode_differentiableAt
    (i j : Fin 3) (x : NSSpace) :
    DifferentiableAt ℝ (finiteModeMixedQuadraticPressureMode i j) x := by
  unfold finiteModeMixedQuadraticPressureMode
  exact
    (finiteModeCoordinatePressureMode_differentiableAt i x).mul
      (finiteModeCoordinatePressureMode_differentiableAt j x)

/-- The gradient of `x ↦ x_i * x_j` is `x_j e_i + x_i e_j`. -/
theorem finiteModeMixedQuadraticPressureMode_gradient
    (i j : Fin 3) (x : NSSpace) :
    gradient (finiteModeMixedQuadraticPressureMode i j) x =
      x j • EuclideanSpace.single i (1 : ℝ) +
        x i • EuclideanSpace.single j (1 : ℝ) := by
  unfold finiteModeMixedQuadraticPressureMode gradient
  apply HasGradientAt.gradient
  rw [hasGradientAt_iff_hasFDerivAt]
  have hdual :
      (InnerProductSpace.toDual ℝ NSSpace)
          (x j • EuclideanSpace.single i (1 : ℝ) +
            x i • EuclideanSpace.single j (1 : ℝ)) =
        (x j) • (EuclideanSpace.proj i : NSSpace →L[ℝ] ℝ) +
          (x i) • (EuclideanSpace.proj j : NSSpace →L[ℝ] ℝ) := by
    ext y
    rw [ContinuousLinearMap.add_apply]
    rw [InnerProductSpace.toDual_apply_apply]
    simp [inner_add_left, inner_smul_left, EuclideanSpace.inner_single_left,
      add_comm]
  rw [hdual]
  have hi : HasFDerivAt (fun y : NSSpace => y i)
      (EuclideanSpace.proj i : NSSpace →L[ℝ] ℝ) x := by
    exact (EuclideanSpace.proj i : NSSpace →L[ℝ] ℝ).hasFDerivAt
  have hj : HasFDerivAt (fun y : NSSpace => y j)
      (EuclideanSpace.proj j : NSSpace →L[ℝ] ℝ) x := by
    exact (EuclideanSpace.proj j : NSSpace →L[ℝ] ℝ).hasFDerivAt
  simpa [mul_comm, add_comm, add_left_comm, add_assoc] using hi.mul hj

/-- Finite pressure basis for affine gradient fields: coordinate-linear
pressures, diagonal quadratics, and the three off-diagonal mixed quadratics. -/
abbrev FiniteModeAffineQuadraticPressureIndex :=
  Fin 3 ⊕ (Fin 3 ⊕ Fin 3)

/-- Decode the three off-diagonal quadratic modes as `(0,1)`, `(0,2)`,
and `(1,2)`. -/
def finiteModeOffDiagonalPair : Fin 3 → Fin 3 × Fin 3
  | 0 => ((0 : Fin 3), (1 : Fin 3))
  | 1 => ((0 : Fin 3), (2 : Fin 3))
  | 2 => ((1 : Fin 3), (2 : Fin 3))

/-- The concrete affine-quadratic pressure basis on `ℝ^3`. -/
def finiteModeAffineQuadraticPressureMode :
    FiniteModeAffineQuadraticPressureIndex → NSSpace → ℝ
  | Sum.inl j => finiteModeCoordinatePressureMode j
  | Sum.inr (Sum.inl j) => finiteModeDiagonalQuadraticPressureMode j
  | Sum.inr (Sum.inr r) =>
      finiteModeMixedQuadraticPressureMode
        (finiteModeOffDiagonalPair r).1 (finiteModeOffDiagonalPair r).2

/-- Every affine-quadratic pressure basis mode is smooth. -/
theorem finiteModeAffineQuadraticPressureMode_contDiff
    (k : FiniteModeAffineQuadraticPressureIndex) :
    ContDiff ℝ ∞ (finiteModeAffineQuadraticPressureMode k) := by
  rcases k with j | k
  · exact finiteModeCoordinatePressureMode_contDiff j
  · rcases k with j | r
    · exact finiteModeDiagonalQuadraticPressureMode_contDiff j
    · exact finiteModeMixedQuadraticPressureMode_contDiff
        (finiteModeOffDiagonalPair r).1 (finiteModeOffDiagonalPair r).2

/-- Coefficients for the affine-quadratic pressure basis.  The intended linear
part `A` is symmetric; off-diagonal modes use the upper-triangular entries. -/
def finiteModeAffineQuadraticPressureCoefficientsAt
    (c : NSSpace) (A : Fin 3 → Fin 3 → ℝ) :
    FiniteModeState FiniteModeAffineQuadraticPressureIndex
  | Sum.inl j => c j
  | Sum.inr (Sum.inl j) => A j j
  | Sum.inr (Sum.inr r) =>
      A (finiteModeOffDiagonalPair r).1 (finiteModeOffDiagonalPair r).2

/-- Affine vector field `x ↦ c + A x` on `ℝ^3`. -/
def finiteModeAffineGradientField
    (c : NSSpace) (A : Fin 3 → Fin 3 → ℝ) : NSSpace → NSSpace :=
  fun x => c + ∑ k : Fin 3,
    (∑ j : Fin 3, A k j * x j) • EuclideanSpace.single k (1 : ℝ)

set_option maxHeartbeats 800000

/-- Every affine curl-free vector field is generated by the affine-quadratic
pressure basis.  Curl-freeness is encoded by symmetry of the linear part. -/
theorem finiteModeAffineQuadraticPressureGradientSynthesis
    (c : NSSpace) (A : Fin 3 → Fin 3 → ℝ)
    (hA : ∀ i j, A i j = A j i)
    (x : NSSpace) :
    finiteModePressureGradientSynthesis finiteModeAffineQuadraticPressureMode
        (finiteModeAffineQuadraticPressureCoefficientsAt c A) x =
      finiteModeAffineGradientField c A x := by
  ext k
  fin_cases k <;>
    simp [finiteModePressureGradientSynthesis,
      finiteModeAffineQuadraticPressureMode,
      finiteModeAffineQuadraticPressureCoefficientsAt,
      finiteModeAffineGradientField,
      finiteModeOffDiagonalPair,
      finiteModeCoordinatePressureMode_gradient,
      finiteModeDiagonalQuadraticPressureMode_gradient,
      finiteModeMixedQuadraticPressureMode_gradient,
      Fintype.sum_sum_type, hA, Fin.sum_univ_three, add_comm, add_left_comm, add_assoc,
      mul_comm]

/-- Affine curl-free vector fields lie in the finite pressure-gradient range. -/
theorem finiteModeAffineQuadraticPressureGradient_mem_range
    (c : NSSpace) (A : Fin 3 → Fin 3 → ℝ)
    (hA : ∀ i j, A i j = A j i) :
    finiteModeAffineGradientField c A ∈
      range (finiteModePressureGradientSynthesis finiteModeAffineQuadraticPressureMode) := by
  refine ⟨finiteModeAffineQuadraticPressureCoefficientsAt c A, ?_⟩
  funext x
  exact finiteModeAffineQuadraticPressureGradientSynthesis c A hA x

/-- The affine-quadratic pressure basis consists of differentiable pressure
modes. -/
theorem finiteModeAffineQuadraticPressureMode_differentiableAt
    (k : FiniteModeAffineQuadraticPressureIndex) (x : NSSpace) :
    DifferentiableAt ℝ (finiteModeAffineQuadraticPressureMode k) x := by
  cases k with
  | inl j => exact finiteModeCoordinatePressureMode_differentiableAt j x
  | inr q =>
      cases q with
      | inl j => exact finiteModeDiagonalQuadraticPressureMode_differentiableAt j x
      | inr r =>
          fin_cases r <;>
            simp [finiteModeAffineQuadraticPressureMode, finiteModeOffDiagonalPair,
              finiteModeMixedQuadraticPressureMode_differentiableAt]

/-- A finite-mode Helmholtz pressure closure is exactly a range condition for
the pressure-gradient synthesis map, time slice by time slice. -/
theorem finiteModePressureHelmholtzRangeOn_iff_residualZeroOn
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (I : Set NSTime)
    (ν : ℝ)
    (mode : ι → NSSpace → NSSpace)
    (pressureMode : κ → NSSpace → ℝ)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (hpressureModeDiff : ∀ k x, DifferentiableAt ℝ (pressureMode k) x) :
    (∃ b : ℝ → FiniteModeState κ,
        finiteModeReconstructedMomentumResidualZeroOn
          I ν mode pressureMode C a b) ↔
      ∀ t ∈ I,
        -finiteModeNonPressureMomentumDefect ν mode C a t ∈
          range (finiteModePressureGradientSynthesis pressureMode) := by
  constructor
  · rintro ⟨b, hres⟩ t ht
    refine ⟨b t, ?_⟩
    funext x
    have hzero := hres t ht x
    unfold finiteModeReconstructedMomentumResidualZeroAt at hzero
    unfold finiteModeReconstructedMomentumResidual at hzero
    rw [finiteModeReconstructedPressure_spatialPressureGradient pressureMode b t x
      (fun k => hpressureModeDiff k x)] at hzero
    change
      finiteModePressureGradientSynthesis pressureMode (b t) x =
        (-finiteModeNonPressureMomentumDefect ν mode C a t) x
    have hsum :
        finiteModePressureGradientSynthesis pressureMode (b t) x +
            finiteModeNonPressureMomentumDefect ν mode C a t x =
          0 := by
      simpa [finiteModePressureGradientSynthesis, finiteModeNonPressureMomentumDefect,
        sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hzero
    exact add_eq_zero_iff_eq_neg.mp hsum
  · intro hrange
    classical
    let b : ℝ → FiniteModeState κ :=
      fun t =>
        if ht : t ∈ I then
          Classical.choose (hrange t ht)
        else
          0
    refine ⟨b, ?_⟩
    intro t ht x
    unfold finiteModeReconstructedMomentumResidualZeroAt
    unfold finiteModeReconstructedMomentumResidual
    rw [finiteModeReconstructedPressure_spatialPressureGradient pressureMode b t x
      (fun k => hpressureModeDiff k x)]
    have hb :
        finiteModePressureGradientSynthesis pressureMode (b t) =
          -finiteModeNonPressureMomentumDefect ν mode C a t := by
      dsimp [b]
      simpa [ht] using Classical.choose_spec (hrange t ht)
    have hbx := congrFun hb x
    have hsum :
        finiteModePressureGradientSynthesis pressureMode (b t) x +
            finiteModeNonPressureMomentumDefect ν mode C a t x =
          0 := by
      rw [hbx]
      simp
    simpa [finiteModePressureGradientSynthesis, finiteModeNonPressureMomentumDefect,
      sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsum

/-- A finite pressure-primitive basis turns the Helmholtz range condition into
plain membership in the corresponding gradient subspace. -/
theorem finiteModePressurePrimitiveBasisOn_iff_residualZeroOn
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (I : Set NSTime)
    (ν : ℝ)
    (mode : ι → NSSpace → NSSpace)
    (pressureMode : κ → NSSpace → ℝ)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (V : Submodule ℝ (NSSpace → NSSpace))
    (B : Module.Basis κ ℝ V)
    (hpressureModeDiff : ∀ k x, DifferentiableAt ℝ (pressureMode k) x)
    (hgradientBasis : ∀ k,
      ((B k : V) : NSSpace → NSSpace) =
        fun x => gradient (pressureMode k) x) :
    (∃ b : ℝ → FiniteModeState κ,
        finiteModeReconstructedMomentumResidualZeroOn
          I ν mode pressureMode C a b) ↔
      ∀ t ∈ I,
        -finiteModeNonPressureMomentumDefect ν mode C a t ∈ V := by
  rw [finiteModePressureHelmholtzRangeOn_iff_residualZeroOn
    I ν mode pressureMode C a hpressureModeDiff]
  constructor
  · intro hrange t ht
    change -finiteModeNonPressureMomentumDefect ν mode C a t ∈
      (V : Set (NSSpace → NSSpace))
    rw [← finiteModePressureGradientSynthesis_range_eq_submodule
      pressureMode V B hgradientBasis]
    exact hrange t ht
  · intro hV t ht
    rw [finiteModePressureGradientSynthesis_range_eq_submodule
      pressureMode V B hgradientBasis]
    exact hV t ht

/-- If the finite pressure-mode gradients exactly close the reconstructed
non-pressure residual, then the reconstructed pressure ansatz has zero
Navier-Stokes momentum residual on the time set.  This is the pressure closure
obligation in coefficient form. -/
theorem finiteModeReconstructedMomentumResidualZeroOn_of_pressureModeGradient_balance
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (I : Set NSTime)
    (ν : ℝ)
    (mode : ι → NSSpace → NSSpace)
    (pressureMode : κ → NSSpace → ℝ)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (b : ℝ → FiniteModeState κ)
    (hpressureModeDiff : ∀ k x, DifferentiableAt ℝ (pressureMode k) x)
    (hbalance : ∀ t ∈ I, ∀ x : NSSpace,
      finiteModeReconstructedAcceleration mode C a t x +
          spatialConvection (finiteModeReconstructedVelocity mode a) t x +
            (∑ k : κ, b t k • gradient (pressureMode k) x) =
        ν • spatialLaplacian (finiteModeReconstructedVelocity mode a) t x) :
    finiteModeReconstructedMomentumResidualZeroOn I ν mode pressureMode C a b := by
  intro t ht x
  unfold finiteModeReconstructedMomentumResidualZeroAt
  unfold finiteModeReconstructedMomentumResidual
  rw [finiteModeReconstructedPressure_spatialPressureGradient pressureMode b t x
    (fun k => hpressureModeDiff k x)]
  exact sub_eq_zero.mpr (hbalance t ht x)

/-- A coefficient derivative reconstructs pointwise into the time derivative of
the spatial finite-mode velocity field. -/
theorem finiteModeReconstructedVelocity_timeDerivative_at
    {ι : Type*} [Fintype ι]
    (mode : ι → NSSpace → NSSpace)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (t : NSTime)
    (ha : HasDerivAt a (finiteModeProjectedNSRHS C (a t)) t)
    (x : NSSpace) :
    timeVelocityDerivative (finiteModeReconstructedVelocity mode a) t x =
      finiteModeReconstructedAcceleration mode C a t x := by
  unfold timeVelocityDerivative timeFDeriv
  have hDeriv :
      HasDerivAt
        (fun s : NSTime => finiteModeReconstructionCLM mode x (a s))
        (finiteModeReconstructionCLM mode x (finiteModeProjectedNSRHS C (a t))) t := by
    exact
      HasFDerivAt.comp_hasDerivAt
        (l := fun b : FiniteModeState ι => finiteModeReconstructionCLM mode x b)
        (l' := finiteModeReconstructionCLM mode x)
        (f := a)
        (x := t)
        (f' := finiteModeProjectedNSRHS C (a t))
        ((finiteModeReconstructionCLM mode x).hasFDerivAt (x := a t))
        ha
  change
    (fderiv ℝ (fun s : NSTime => finiteModeReconstructionCLM mode x (a s)) t) 1 =
      finiteModeReconstructionCLM mode x (finiteModeProjectedNSRHS C (a t))
  rw [hDeriv.hasFDerivAt.fderiv]
  simp

/-- The shear coefficient solution cannot be repaired by any time-dependent
polynomial pressure on a time set containing `0`: the actual pointwise momentum
equation would force the forbidden closing gradient `∇p(0) = -(X₁ e₀)`. -/
theorem finiteModeShearAcceleration_solution_no_polynomialPressureMomentumOn
    (I : Set NSTime) (h0 : (0 : NSTime) ∈ I) :
    ¬ ∃ P : NSTime → MvPolynomial (Fin 3) ℝ,
      ∀ t ∈ I, ∀ x : NSSpace,
        timeVelocityDerivative
              (finiteModeReconstructedVelocity finiteModeShearAccelerationMode
                finiteModeIdentityCoefficientCurve)
              t x +
            spatialConvection
              (finiteModeReconstructedVelocity finiteModeShearAccelerationMode
                finiteModeIdentityCoefficientCurve)
              t x +
              spatialPressureGradient
                (fun s y => MvPolynomial.eval y (P s)) t x =
          (0 : ℝ) • spatialLaplacian
            (finiteModeReconstructedVelocity finiteModeShearAccelerationMode
              finiteModeIdentityCoefficientCurve)
            t x := by
  intro hP
  rcases hP with ⟨P, hmom⟩
  exact finiteModeShearAccelerationPolynomialVectorField_no_negative_pressurePrimitive
    ⟨P 0, by
      refine
        (finiteModePolynomialPressureGradient_eq_eval_iff_pderiv
          (P 0) (fun j => -finiteModeShearAccelerationPolynomialVectorField j) 0).mp ?_
      intro x
      have hmom0 := hmom 0 h0 x
      rw [finiteModeReconstructedVelocity_timeDerivative_at
        finiteModeShearAccelerationMode finiteModeUnitForcingCoefficients
        finiteModeIdentityCoefficientCurve 0
        (finiteModeIdentityCoefficientCurve_hasDerivAt 0) x] at hmom0
      have hres :
          finiteModeReconstructedAcceleration finiteModeShearAccelerationMode
                finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve 0 x +
              spatialConvection
                (finiteModeReconstructedVelocity finiteModeShearAccelerationMode
                  finiteModeIdentityCoefficientCurve) 0 x +
                spatialPressureGradient
                  (fun s y => MvPolynomial.eval y (P s)) 0 x -
            (0 : ℝ) • spatialLaplacian
              (finiteModeReconstructedVelocity finiteModeShearAccelerationMode
                finiteModeIdentityCoefficientCurve) 0 x =
            0 :=
        sub_eq_zero.mpr hmom0
      have hsum :
          spatialPressureGradient (fun s y => MvPolynomial.eval y (P s)) 0 x +
              finiteModeNonPressureMomentumDefect (0 : ℝ) finiteModeShearAccelerationMode
                finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve 0 x =
            0 := by
        simpa [finiteModeNonPressureMomentumDefect, sub_eq_add_neg,
          add_assoc, add_left_comm, add_comm] using hres
      have hgrad :
          spatialPressureGradient (fun s y => MvPolynomial.eval y (P s)) 0 x =
            -finiteModeNonPressureMomentumDefect (0 : ℝ) finiteModeShearAccelerationMode
              finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve 0 x :=
        add_eq_zero_iff_eq_neg.mp hsum
      rw [finiteModeShearAcceleration_solution_nonPressureDefect_eq_polynomial] at hgrad
      calc
        spatialPressureGradient (fun x y => MvPolynomial.eval y (P 0)) 0 x =
            -finiteModePolynomialVectorFieldEval
              finiteModeShearAccelerationPolynomialVectorField x := by
              simpa [spatialPressureGradient] using hgrad
        _ = finiteModePolynomialVectorFieldEval
              (fun j => -finiteModeShearAccelerationPolynomialVectorField j) x := by
              ext j
              simp [finiteModePolynomialVectorFieldEval_apply]⟩

/-- The abstract projected finite-mode ODE alone does not imply a local
Navier-Stokes momentum solution after reconstruction.  The identity coefficient
curve solves the one-mode projected ODE, but on the concrete interval
`(-1, 1)` no time-dependent polynomial pressure can make its reconstructed
shear field satisfy the pointwise momentum equation. -/
theorem finiteModeProjectedNS_coefficientSolution_no_polynomialPressureMomentum_obstruction :
    (∀ t : NSTime,
      HasDerivAt finiteModeIdentityCoefficientCurve
        (finiteModeProjectedNSRHS finiteModeUnitForcingCoefficients
          (finiteModeIdentityCoefficientCurve t)) t) ∧
      (∀ t : NSTime,
        finiteModeNonPressureMomentumDefect (0 : ℝ) finiteModeShearAccelerationMode
            finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve t =
          finiteModePolynomialVectorFieldEval
            finiteModeShearAccelerationPolynomialVectorField) ∧
      ¬ ∃ P : NSTime → MvPolynomial (Fin 3) ℝ,
        ∀ t ∈ Ioo (-(1 : ℝ)) (1 : ℝ), ∀ x : NSSpace,
          timeVelocityDerivative
                (finiteModeReconstructedVelocity finiteModeShearAccelerationMode
                  finiteModeIdentityCoefficientCurve)
                t x +
              spatialConvection
                (finiteModeReconstructedVelocity finiteModeShearAccelerationMode
                  finiteModeIdentityCoefficientCurve)
                t x +
                spatialPressureGradient
                  (fun s y => MvPolynomial.eval y (P s)) t x =
            (0 : ℝ) • spatialLaplacian
              (finiteModeReconstructedVelocity finiteModeShearAccelerationMode
                finiteModeIdentityCoefficientCurve)
              t x := by
  refine ⟨finiteModeIdentityCoefficientCurve_hasDerivAt, ?_, ?_⟩
  · intro t
    funext x
    exact finiteModeShearAcceleration_solution_nonPressureDefect_eq_polynomial t x
  · exact
      finiteModeShearAcceleration_solution_no_polynomialPressureMomentumOn
        (Ioo (-(1 : ℝ)) (1 : ℝ)) (by norm_num)

/-- The tempting universal closure theorem is false: solving the abstract
finite-mode coefficient ODE does not, by itself, force existence of a
time-dependent polynomial pressure closing the reconstructed pointwise momentum
equation. -/
theorem finiteModeProjectedNS_polynomialPressureMomentum_not_forced :
    ¬ ∀ (mode : PUnit → NSSpace → NSSpace)
        (C : FiniteModeProjectedNSCoefficients PUnit)
        (a : ℝ → FiniteModeState PUnit),
      (∀ t : NSTime, HasDerivAt a (finiteModeProjectedNSRHS C (a t)) t) →
        ∃ P : NSTime → MvPolynomial (Fin 3) ℝ,
          ∀ t ∈ Ioo (-(1 : ℝ)) (1 : ℝ), ∀ x : NSSpace,
            timeVelocityDerivative (finiteModeReconstructedVelocity mode a) t x +
                spatialConvection (finiteModeReconstructedVelocity mode a) t x +
                  spatialPressureGradient
                    (fun s y => MvPolynomial.eval y (P s)) t x =
              (0 : ℝ) • spatialLaplacian
                (finiteModeReconstructedVelocity mode a) t x := by
  intro h
  exact
    finiteModeShearAcceleration_solution_no_polynomialPressureMomentumOn
      (Ioo (-(1 : ℝ)) (1 : ℝ)) (by norm_num)
      (h finiteModeShearAccelerationMode finiteModeUnitForcingCoefficients
        finiteModeIdentityCoefficientCurve finiteModeIdentityCoefficientCurve_hasDerivAt)

/-- Pressure/residual reconstruction at one point: once the coefficient curve
solves the finite projected ODE, zero residual is exactly the concrete
Navier-Stokes momentum equation for the reconstructed velocity and pressure. -/
theorem finiteModeReconstructedMomentumResidualZeroAt_iff_momentumEquation_at
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (ν : ℝ)
    (mode : ι → NSSpace → NSSpace)
    (pressureMode : κ → NSSpace → ℝ)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (b : ℝ → FiniteModeState κ)
    (t : NSTime)
    (ha : HasDerivAt a (finiteModeProjectedNSRHS C (a t)) t)
    (x : NSSpace) :
    finiteModeReconstructedMomentumResidualZeroAt
        ν mode pressureMode C a b t x ↔
      timeVelocityDerivative (finiteModeReconstructedVelocity mode a) t x +
          spatialConvection (finiteModeReconstructedVelocity mode a) t x +
            spatialPressureGradient
              (finiteModeReconstructedPressure pressureMode b) t x =
        ν • spatialLaplacian (finiteModeReconstructedVelocity mode a) t x := by
  constructor
  · intro hres
    rw [finiteModeReconstructedVelocity_timeDerivative_at mode C a t ha x]
    exact sub_eq_zero.mp hres
  · intro hmom
    rw [finiteModeReconstructedVelocity_timeDerivative_at mode C a t ha x] at hmom
    exact sub_eq_zero.mpr hmom

/-- A one-mode spatial direction for the uniform acceleration field `e₀`. -/
def finiteModeUniformAccelerationMode (_ : PUnit) : NSSpace → NSSpace :=
  fun _ => EuclideanSpace.single (0 : Fin 3) (1 : ℝ)

/-- The constant pressure gradient `-e₀` that cancels the uniform acceleration
mode. -/
def finiteModeUniformAccelerationClosingGradient : NSTime → NSSpace :=
  fun _ => -EuclideanSpace.single (0 : Fin 3) (1 : ℝ)

/-- Coordinate pressure coefficients for the pressure `p(t,x) = -x₀`. -/
def finiteModeUniformAccelerationPressureCoefficients :
    NSTime → FiniteModeState (Fin 3) :=
  finiteModeCoordinatePressureCoefficients
    finiteModeUniformAccelerationClosingGradient

/-- The reconstructed coordinate pressure closing the uniform acceleration
field. -/
def finiteModeUniformAccelerationPressure : NSPressureField :=
  finiteModeReconstructedPressure finiteModeCoordinatePressureMode
    finiteModeUniformAccelerationPressureCoefficients

/-- The identity-coefficient reconstruction of the uniform mode is the
time-dependent constant-in-space velocity `u(t,x)=t e₀`. -/
theorem finiteModeUniformAcceleration_velocity_eq_constant
    (t : NSTime) (x : NSSpace) :
    finiteModeReconstructedVelocity finiteModeUniformAccelerationMode
        finiteModeIdentityCoefficientCurve t x =
      constantVelocityField (t • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) t x := by
  simp [finiteModeReconstructedVelocity, finiteModeReconstructionCLM,
    finiteModeIdentityCoefficientCurve, finiteModeUniformAccelerationMode,
    constantVelocityField]

/-- The reconstructed uniform acceleration velocity has zero convection. -/
theorem finiteModeUniformAcceleration_spatialConvection_zero
    (t : NSTime) (x : NSSpace) :
    spatialConvection
        (finiteModeReconstructedVelocity finiteModeUniformAccelerationMode
          finiteModeIdentityCoefficientCurve) t x = 0 := by
  unfold spatialConvection
  have hfderiv :
      spatialFDeriv
          (finiteModeReconstructedVelocity finiteModeUniformAccelerationMode
            finiteModeIdentityCoefficientCurve) t x =
        spatialFDeriv
          (constantVelocityField (t • EuclideanSpace.single (0 : Fin 3) (1 : ℝ))) t x := by
    unfold spatialFDeriv
    congr 1
    funext y
    exact finiteModeUniformAcceleration_velocity_eq_constant t y
  rw [hfderiv, finiteModeUniformAcceleration_velocity_eq_constant]
  exact spatialConvection_constantVelocityField
    (t • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) t x

/-- The reconstructed uniform acceleration velocity has zero spatial
Laplacian. -/
theorem finiteModeUniformAcceleration_spatialLaplacian_zero
    (t : NSTime) (x : NSSpace) :
    spatialLaplacian
        (finiteModeReconstructedVelocity finiteModeUniformAccelerationMode
          finiteModeIdentityCoefficientCurve) t x = 0 := by
  unfold spatialLaplacian
  have hslice :
      (fun y : NSSpace =>
        finiteModeReconstructedVelocity finiteModeUniformAccelerationMode
          finiteModeIdentityCoefficientCurve t y) =
      fun y : NSSpace =>
        constantVelocityField (t • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) t y := by
    funext y
    exact finiteModeUniformAcceleration_velocity_eq_constant t y
  rw [hslice]
  exact spatialLaplacian_constantVelocityField
    (t • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) t x

/-- The projected RHS reconstructs to the constant acceleration `e₀`. -/
theorem finiteModeUniformAcceleration_acceleration_eq
    (t : NSTime) (x : NSSpace) :
    finiteModeReconstructedAcceleration finiteModeUniformAccelerationMode
        finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve t x =
      EuclideanSpace.single (0 : Fin 3) (1 : ℝ) := by
  simp [finiteModeReconstructedAcceleration,
    finiteModeReconstructedVelocity, finiteModeReconstructionCLM,
    finiteModeProjectedNSRHS, finiteModeUnitForcingCoefficients,
    finiteModeIdentityCoefficientCurve, finiteModeUniformAccelerationMode]

/-- A positive finite-mode reconstruction: the coefficient solution `a(t)=t`
with uniform mode `e₀` and coordinate pressure `p=-x₀` satisfies the pointwise
Navier-Stokes momentum equation for every viscosity. -/
theorem finiteModeUniformAcceleration_reconstructed_momentum
    (ν : ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative
          (finiteModeReconstructedVelocity finiteModeUniformAccelerationMode
            finiteModeIdentityCoefficientCurve) t x +
        spatialConvection
          (finiteModeReconstructedVelocity finiteModeUniformAccelerationMode
            finiteModeIdentityCoefficientCurve) t x +
          spatialPressureGradient finiteModeUniformAccelerationPressure t x =
      ν • spatialLaplacian
        (finiteModeReconstructedVelocity finiteModeUniformAccelerationMode
          finiteModeIdentityCoefficientCurve) t x := by
  rw [finiteModeReconstructedVelocity_timeDerivative_at finiteModeUniformAccelerationMode
    finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve t
    (finiteModeIdentityCoefficientCurve_hasDerivAt t) x]
  rw [finiteModeUniformAcceleration_spatialConvection_zero t x,
    finiteModeUniformAcceleration_spatialLaplacian_zero t x]
  rw [finiteModeUniformAcceleration_acceleration_eq t x]
  rw [show spatialPressureGradient finiteModeUniformAccelerationPressure t x =
      finiteModeUniformAccelerationClosingGradient t from
    finiteModeCoordinatePressure_spatialPressureGradient
      finiteModeUniformAccelerationClosingGradient t x]
  simp [finiteModeUniformAccelerationClosingGradient]

/-- The positive uniform-acceleration reconstruction has zero finite-mode
momentum residual on all time. -/
theorem finiteModeUniformAcceleration_reconstructedResidualZeroOn_univ
    (ν : ℝ) :
    finiteModeReconstructedMomentumResidualZeroOn Set.univ ν
      finiteModeUniformAccelerationMode finiteModeCoordinatePressureMode
      finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve
      finiteModeUniformAccelerationPressureCoefficients := by
  intro t _ht x
  exact
    (finiteModeReconstructedMomentumResidualZeroAt_iff_momentumEquation_at
      ν finiteModeUniformAccelerationMode finiteModeCoordinatePressureMode
      finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve
      finiteModeUniformAccelerationPressureCoefficients t
      (finiteModeIdentityCoefficientCurve_hasDerivAt t) x).mpr
      (finiteModeUniformAcceleration_reconstructed_momentum ν t x)

/-- Existential packaging of the explicit uniform-acceleration reconstructed
velocity and pressure.  This is a pointwise PDE witness for the finite-mode
reconstruction layer, not a Clay finite-energy witness. -/
theorem finiteModeUniformAcceleration_reconstructed_velocityPressure_momentum_exists
    (ν : ℝ) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity finiteModeUniformAccelerationMode
        finiteModeIdentityCoefficientCurve ∧
        p = finiteModeUniformAccelerationPressure ∧
        ∀ t x,
          timeVelocityDerivative u t x +
              spatialConvection u t x +
                spatialPressureGradient p t x =
            ν • spatialLaplacian u t x := by
  exact
    ⟨finiteModeReconstructedVelocity finiteModeUniformAccelerationMode
        finiteModeIdentityCoefficientCurve,
      finiteModeUniformAccelerationPressure, rfl, rfl,
      finiteModeUniformAcceleration_reconstructed_momentum ν⟩

/-- The forward direction of pressure/residual reconstruction at one point. -/
theorem finiteModeReconstructedVelocityPressure_momentumEquation_at_of_residual_zero
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (ν : ℝ)
    (mode : ι → NSSpace → NSSpace)
    (pressureMode : κ → NSSpace → ℝ)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (b : ℝ → FiniteModeState κ)
    (t : NSTime)
    (ha : HasDerivAt a (finiteModeProjectedNSRHS C (a t)) t)
    (hres :
      ∀ x : NSSpace,
        finiteModeReconstructedMomentumResidualZeroAt
          ν mode pressureMode C a b t x)
    (x : NSSpace) :
    timeVelocityDerivative (finiteModeReconstructedVelocity mode a) t x +
        spatialConvection (finiteModeReconstructedVelocity mode a) t x +
          spatialPressureGradient
            (finiteModeReconstructedPressure pressureMode b) t x =
      ν • spatialLaplacian (finiteModeReconstructedVelocity mode a) t x :=
  (finiteModeReconstructedMomentumResidualZeroAt_iff_momentumEquation_at
    ν mode pressureMode C a b t ha x).mp (hres x)

/-- Pressure/residual reconstruction on a time set.  This is the local
finite-dimensional-to-PDE momentum step: no global target or continuation
hypothesis is used, only the coefficient ODE and the explicit residual closure
for the reconstructed pressure ansatz. -/
theorem finiteModeReconstructedVelocityPressure_momentumEquation_on_of_residual_zero
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (I : Set NSTime)
    (ν : ℝ)
    (mode : ι → NSSpace → NSSpace)
    (pressureMode : κ → NSSpace → ℝ)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (b : ℝ → FiniteModeState κ)
    (ha : ∀ t ∈ I, HasDerivAt a (finiteModeProjectedNSRHS C (a t)) t)
    (hres :
      finiteModeReconstructedMomentumResidualZeroOn
        I ν mode pressureMode C a b) :
    ∀ t ∈ I, ∀ x : NSSpace,
      timeVelocityDerivative (finiteModeReconstructedVelocity mode a) t x +
          spatialConvection (finiteModeReconstructedVelocity mode a) t x +
            spatialPressureGradient
              (finiteModeReconstructedPressure pressureMode b) t x =
        ν • spatialLaplacian (finiteModeReconstructedVelocity mode a) t x := by
  intro t ht x
  exact
    finiteModeReconstructedVelocityPressure_momentumEquation_at_of_residual_zero
      ν mode pressureMode C a b t (ha t ht) (hres t ht) x

/-- Given a coefficient solution and a pressure coefficient curve whose
reconstructed residual vanishes on a local time interval, the reconstructed
`u,p` pair satisfies the concrete pointwise momentum equation on that interval. -/
theorem finiteModeProjectedNS_local_reconstructed_velocityPressure_momentum_of_residual_zero
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (ν : ℝ)
    (mode : ι → NSSpace → NSSpace)
    (pressureMode : κ → NSSpace → ℝ)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (b : ℝ → FiniteModeState κ)
    (ε : ℝ)
    (ha : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt a (finiteModeProjectedNSRHS C (a t)) t)
    (hres :
      finiteModeReconstructedMomentumResidualZeroOn
        (Ioo (-ε) ε) ν mode pressureMode C a b) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity mode a ∧
        p = finiteModeReconstructedPressure pressureMode b ∧
          ∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
            timeVelocityDerivative u t x +
                spatialConvection u t x +
                  spatialPressureGradient p t x =
              ν • spatialLaplacian u t x := by
  refine
    ⟨finiteModeReconstructedVelocity mode a,
      finiteModeReconstructedPressure pressureMode b, rfl, rfl, ?_⟩
  exact
    finiteModeReconstructedVelocityPressure_momentumEquation_on_of_residual_zero
      (Ioo (-ε) ε) ν mode pressureMode C a b ha hres

/-- A coefficient ODE solution plus a finite pressure-mode gradient balance
constructs a concrete velocity-pressure pair satisfying the pointwise momentum
equation on the local interval. -/
theorem finiteModeProjectedNS_local_reconstructed_velocityPressure_momentum_of_pressureModeGradient_balance
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (ν : ℝ)
    (mode : ι → NSSpace → NSSpace)
    (pressureMode : κ → NSSpace → ℝ)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (b : ℝ → FiniteModeState κ)
    (ε : ℝ)
    (ha : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt a (finiteModeProjectedNSRHS C (a t)) t)
    (hpressureModeDiff : ∀ k x, DifferentiableAt ℝ (pressureMode k) x)
    (hbalance : ∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
      finiteModeReconstructedAcceleration mode C a t x +
          spatialConvection (finiteModeReconstructedVelocity mode a) t x +
            (∑ k : κ, b t k • gradient (pressureMode k) x) =
        ν • spatialLaplacian (finiteModeReconstructedVelocity mode a) t x) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity mode a ∧
        p = finiteModeReconstructedPressure pressureMode b ∧
          ∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
            timeVelocityDerivative u t x +
                spatialConvection u t x +
                  spatialPressureGradient p t x =
              ν • spatialLaplacian u t x := by
  exact
    finiteModeProjectedNS_local_reconstructed_velocityPressure_momentum_of_residual_zero
      ν mode pressureMode C a b ε ha
      (finiteModeReconstructedMomentumResidualZeroOn_of_pressureModeGradient_balance
        (Ioo (-ε) ε) ν mode pressureMode C a b hpressureModeDiff hbalance)

/-- A local coefficient ODE solution plus the finite-dimensional Helmholtz
range condition constructs pressure coefficients and hence a concrete
velocity-pressure pair satisfying the pointwise momentum equation locally. -/
theorem finiteModeProjectedNS_local_reconstructed_velocityPressure_momentum_of_pressureHelmholtzRange
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (ν : ℝ)
    (mode : ι → NSSpace → NSSpace)
    (pressureMode : κ → NSSpace → ℝ)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (ε : ℝ)
    (ha : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt a (finiteModeProjectedNSRHS C (a t)) t)
    (hpressureModeDiff : ∀ k x, DifferentiableAt ℝ (pressureMode k) x)
    (hrange : ∀ t ∈ Ioo (-ε) ε,
      -finiteModeNonPressureMomentumDefect ν mode C a t ∈
        range (finiteModePressureGradientSynthesis pressureMode)) :
    ∃ b : ℝ → FiniteModeState κ, ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity mode a ∧
        p = finiteModeReconstructedPressure pressureMode b ∧
          finiteModeReconstructedMomentumResidualZeroOn
            (Ioo (-ε) ε) ν mode pressureMode C a b ∧
          ∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
            timeVelocityDerivative u t x +
                spatialConvection u t x +
                  spatialPressureGradient p t x =
              ν • spatialLaplacian u t x := by
  rcases
    (finiteModePressureHelmholtzRangeOn_iff_residualZeroOn
      (Ioo (-ε) ε) ν mode pressureMode C a hpressureModeDiff).mpr hrange with
    ⟨b, hres⟩
  refine
    ⟨b, finiteModeReconstructedVelocity mode a,
      finiteModeReconstructedPressure pressureMode b, rfl, rfl, hres, ?_⟩
  exact
    finiteModeReconstructedVelocityPressure_momentumEquation_on_of_residual_zero
      (Ioo (-ε) ε) ν mode pressureMode C a b ha hres

/-- Local finite-mode momentum reconstruction from a finite-dimensional
pressure-primitive basis.  The remaining Helmholtz obligation is now the
mathematically sharp statement that each non-pressure defect slice lies in the
chosen gradient subspace; pressure coefficients are synthesized from the basis
coordinates. -/
theorem finiteModeProjectedNS_local_reconstructed_velocityPressure_momentum_of_pressurePrimitiveBasis
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (ν : ℝ)
    (mode : ι → NSSpace → NSSpace)
    (pressureMode : κ → NSSpace → ℝ)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (ε : ℝ)
    (ha : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt a (finiteModeProjectedNSRHS C (a t)) t)
    (V : Submodule ℝ (NSSpace → NSSpace))
    (B : Module.Basis κ ℝ V)
    (hpressureModeDiff : ∀ k x, DifferentiableAt ℝ (pressureMode k) x)
    (hgradientBasis : ∀ k,
      ((B k : V) : NSSpace → NSSpace) =
        fun x => gradient (pressureMode k) x)
    (hdefectV : ∀ t ∈ Ioo (-ε) ε,
      -finiteModeNonPressureMomentumDefect ν mode C a t ∈ V) :
    ∃ b : ℝ → FiniteModeState κ, ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity mode a ∧
        p = finiteModeReconstructedPressure pressureMode b ∧
          finiteModeReconstructedMomentumResidualZeroOn
            (Ioo (-ε) ε) ν mode pressureMode C a b ∧
          ∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
            timeVelocityDerivative u t x +
                spatialConvection u t x +
                  spatialPressureGradient p t x =
              ν • spatialLaplacian u t x := by
  rcases
    (finiteModePressurePrimitiveBasisOn_iff_residualZeroOn
      (Ioo (-ε) ε) ν mode pressureMode C a V B
      hpressureModeDiff hgradientBasis).mpr hdefectV with
    ⟨b, hres⟩
  refine
    ⟨b, finiteModeReconstructedVelocity mode a,
      finiteModeReconstructedPressure pressureMode b, rfl, rfl, hres, ?_⟩
  exact
    finiteModeReconstructedVelocityPressure_momentumEquation_on_of_residual_zero
      (Ioo (-ε) ε) ν mode pressureMode C a b ha hres

/-- Local finite-mode momentum reconstruction from the general polynomial
Helmholtz solve.  If the non-pressure defect slice is explicitly represented
by a curl-free polynomial vector field, the pressure is constructed as the
polynomial primitive `P_{G(t)}` rather than supplied as an independent pressure
ansatz. -/
theorem finiteModeProjectedNS_local_reconstructed_velocityPolynomialPressure_momentum_of_polynomialHelmholtz
    {ι : Type*} [Fintype ι]
    (ν : ℝ)
    (mode : ι → NSSpace → NSSpace)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (ε : ℝ)
    (ha : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt a (finiteModeProjectedNSRHS C (a t)) t)
    (G : NSTime → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (hcurl : ∀ t ∈ Ioo (-ε) ε, ∀ i j,
      MvPolynomial.pderiv i (G t j) =
        MvPolynomial.pderiv j (G t i))
    (hdefect : ∀ t ∈ Ioo (-ε) ε,
      -finiteModeNonPressureMomentumDefect ν mode C a t =
        finiteModePolynomialVectorFieldEval (G t)) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity mode a ∧
        p = (fun t x => finiteModePolynomialPressureMode (G t) x) ∧
          ∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
            timeVelocityDerivative u t x +
                spatialConvection u t x +
                  spatialPressureGradient p t x =
              ν • spatialLaplacian u t x := by
  refine
    ⟨finiteModeReconstructedVelocity mode a,
      (fun t x => finiteModePolynomialPressureMode (G t) x), rfl, rfl, ?_⟩
  intro t ht x
  rw [finiteModeReconstructedVelocity_timeDerivative_at mode C a t (ha t ht) x]
  unfold spatialPressureGradient
  rw [finiteModePolynomialPressureMode_gradient (G t) (hcurl t ht) x]
  have hdefx := congrFun (hdefect t ht) x
  have hsum :
      finiteModePolynomialVectorFieldEval (G t) x +
          finiteModeNonPressureMomentumDefect ν mode C a t x = 0 := by
    rw [← hdefx]
    simp
  have hzero :
      finiteModeReconstructedAcceleration mode C a t x +
          spatialConvection (finiteModeReconstructedVelocity mode a) t x +
            finiteModePolynomialVectorFieldEval (G t) x -
        ν • spatialLaplacian (finiteModeReconstructedVelocity mode a) t x = 0 := by
    simpa [finiteModeNonPressureMomentumDefect, sub_eq_add_neg,
      add_assoc, add_left_comm, add_comm] using hsum
  exact sub_eq_zero.mp hzero

/-- Exact residual-level polynomial Helmholtz criterion for reconstructed
finite-mode momentum: once the represented non-pressure defect is a polynomial
vector field, existence of a time-dependent polynomial pressure making the
reconstructed momentum equation hold is equivalent to curl-freeness of that
polynomial defect on the same local interval. -/
theorem finiteModeProjectedNS_local_reconstructed_velocityPolynomialPressure_momentum_iff_curlFree_of_polynomialDefect
    {ι : Type*} [Fintype ι]
    (ν : ℝ)
    (mode : ι → NSSpace → NSSpace)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (ε : ℝ)
    (ha : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt a (finiteModeProjectedNSRHS C (a t)) t)
    (G : NSTime → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (hdefect : ∀ t ∈ Ioo (-ε) ε,
      -finiteModeNonPressureMomentumDefect ν mode C a t =
        finiteModePolynomialVectorFieldEval (G t)) :
    (∃ P : NSTime → MvPolynomial (Fin 3) ℝ,
        ∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
          timeVelocityDerivative (finiteModeReconstructedVelocity mode a) t x +
              spatialConvection (finiteModeReconstructedVelocity mode a) t x +
                spatialPressureGradient
                  (fun s y => MvPolynomial.eval y (P s)) t x =
            ν • spatialLaplacian (finiteModeReconstructedVelocity mode a) t x) ↔
      ∀ t ∈ Ioo (-ε) ε, ∀ i j, MvPolynomial.pderiv i (G t j) =
        MvPolynomial.pderiv j (G t i) := by
  rw [← finiteModePolynomialPressure_closes_nonPressureDefectOn_iff_curlFree_of_polynomialDefect
    (Ioo (-ε) ε) ν mode C a G hdefect]
  constructor
  · rintro ⟨P, hmom⟩
    refine ⟨P, ?_⟩
    intro t ht x
    have hmom' := hmom t ht x
    rw [finiteModeReconstructedVelocity_timeDerivative_at mode C a t (ha t ht) x] at hmom'
    have hres :
        finiteModeReconstructedAcceleration mode C a t x +
            spatialConvection (finiteModeReconstructedVelocity mode a) t x +
              spatialPressureGradient (fun s y => MvPolynomial.eval y (P s)) t x -
          ν • spatialLaplacian (finiteModeReconstructedVelocity mode a) t x = 0 :=
      sub_eq_zero.mpr hmom'
    have hsum :
        spatialPressureGradient (fun s y => MvPolynomial.eval y (P s)) t x +
            finiteModeNonPressureMomentumDefect ν mode C a t x = 0 := by
      simpa [finiteModeNonPressureMomentumDefect, sub_eq_add_neg,
        add_assoc, add_left_comm, add_comm] using hres
    exact add_eq_zero_iff_eq_neg.mp hsum
  · rintro ⟨P, hP⟩
    refine ⟨P, ?_⟩
    intro t ht x
    rw [finiteModeReconstructedVelocity_timeDerivative_at mode C a t (ha t ht) x]
    have hsum :
        spatialPressureGradient (fun s y => MvPolynomial.eval y (P s)) t x +
            finiteModeNonPressureMomentumDefect ν mode C a t x = 0 := by
      rw [hP t ht x]
      simp
    have hres :
        finiteModeReconstructedAcceleration mode C a t x +
            spatialConvection (finiteModeReconstructedVelocity mode a) t x +
              spatialPressureGradient (fun s y => MvPolynomial.eval y (P s)) t x -
          ν • spatialLaplacian (finiteModeReconstructedVelocity mode a) t x = 0 := by
      simpa [finiteModeNonPressureMomentumDefect, sub_eq_add_neg,
        add_assoc, add_left_comm, add_comm] using hsum
    exact sub_eq_zero.mp hres

/-- Residual-level polynomial pressure criterion for polynomial spatial modes:
after acceleration and convection have been computed symbolically, and after
the actual Laplacian slice is represented by `lapPoly`, local polynomial
pressure solvability is exactly curl-freeness of the resulting closing
pressure-gradient polynomial. -/
theorem finiteModeProjectedNS_local_reconstructed_velocityPolynomialPressure_momentum_iff_curlFree_of_polynomialModes_laplacian
    {ι : Type*} [Fintype ι]
    (ν : ℝ)
    (modePoly : ι → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (ε : ℝ)
    (ha : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt a (finiteModeProjectedNSRHS C (a t)) t)
    (lapPoly : NSTime → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (hLap : ∀ t x,
      spatialLaplacian
          (finiteModeReconstructedVelocity
            (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y) a) t x =
        finiteModePolynomialVectorFieldEval (lapPoly t) x) :
    (∃ P : NSTime → MvPolynomial (Fin 3) ℝ,
        ∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
          timeVelocityDerivative
                (finiteModeReconstructedVelocity
                  (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y) a)
                t x +
              spatialConvection
                (finiteModeReconstructedVelocity
                  (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y) a)
                t x +
                spatialPressureGradient
                  (fun s y => MvPolynomial.eval y (P s)) t x =
            ν • spatialLaplacian
              (finiteModeReconstructedVelocity
                (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y) a)
              t x) ↔
      ∀ t ∈ Ioo (-ε) ε, ∀ i j,
        MvPolynomial.pderiv i
            (finiteModePolynomialClosingPressureGradientComponents
              ν modePoly C a lapPoly t j) =
          MvPolynomial.pderiv j
            (finiteModePolynomialClosingPressureGradientComponents
              ν modePoly C a lapPoly t i) := by
  refine
    finiteModeProjectedNS_local_reconstructed_velocityPolynomialPressure_momentum_iff_curlFree_of_polynomialDefect
      ν (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y)
      C a ε ha
      (finiteModePolynomialClosingPressureGradientComponents ν modePoly C a lapPoly) ?_
  intro t _ht
  funext x
  ext j
  have hdefj := congrArg (fun v : NSSpace => v j)
    (finiteModePolynomialNonPressureDefect_eq_eval_of_laplacian
      ν modePoly C a lapPoly hLap t x)
  simp [finiteModePolynomialClosingPressureGradientComponents,
    finiteModePolynomialVectorFieldEval_apply, hdefj]

/-- Residual-level polynomial pressure criterion for polynomial spatial modes
with the Laplacian represented by the formal componentwise polynomial
Laplacian proved above. -/
theorem finiteModeProjectedNS_local_reconstructed_velocityPolynomialPressure_momentum_iff_curlFree_of_polynomialModes
    {ι : Type*} [Fintype ι]
    (ν : ℝ)
    (modePoly : ι → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (ε : ℝ)
    (ha : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt a (finiteModeProjectedNSRHS C (a t)) t) :
    (∃ P : NSTime → MvPolynomial (Fin 3) ℝ,
        ∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
          timeVelocityDerivative
                (finiteModeReconstructedVelocity
                  (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y) a)
                t x +
              spatialConvection
                (finiteModeReconstructedVelocity
                  (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y) a)
                t x +
                spatialPressureGradient
                  (fun s y => MvPolynomial.eval y (P s)) t x =
            ν • spatialLaplacian
              (finiteModeReconstructedVelocity
                (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y) a)
              t x) ↔
      ∀ t ∈ Ioo (-ε) ε, ∀ i j,
        MvPolynomial.pderiv i
            (finiteModePolynomialClosingPressureGradientComponents
              ν modePoly C a
                (fun s => finiteModePolynomialLaplacianComponents
                  (finiteModePolynomialReconstructedVelocityComponents modePoly a s))
              t j) =
          MvPolynomial.pderiv j
            (finiteModePolynomialClosingPressureGradientComponents
              ν modePoly C a
                (fun s => finiteModePolynomialLaplacianComponents
                  (finiteModePolynomialReconstructedVelocityComponents modePoly a s))
              t i) := by
  exact
    finiteModeProjectedNS_local_reconstructed_velocityPolynomialPressure_momentum_iff_curlFree_of_polynomialModes_laplacian
      ν modePoly C a ε ha
      (fun s => finiteModePolynomialLaplacianComponents
        (finiteModePolynomialReconstructedVelocityComponents modePoly a s))
      (fun s y => finiteModePolynomialReconstructedVelocity_spatialLaplacian modePoly a s y)

/-- Constructive polynomial-mode pressure closure.  For polynomial spatial
modes, if the computed closing pressure-gradient polynomial is curl-free on the
local interval, then its explicit polynomial primitive supplies a concrete
pressure field and the reconstructed velocity-pressure pair satisfies the
pointwise momentum equation. -/
theorem finiteModeProjectedNS_local_reconstructed_velocityPolynomialPressure_momentum_of_polynomialModes_curlFree
    {ι : Type*} [Fintype ι]
    (ν : ℝ)
    (modePoly : ι → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (ε : ℝ)
    (ha : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt a (finiteModeProjectedNSRHS C (a t)) t)
    (hcurl : ∀ t ∈ Ioo (-ε) ε, ∀ i j,
      MvPolynomial.pderiv i
          (finiteModePolynomialClosingPressureGradientComponents
            ν modePoly C a
              (fun s => finiteModePolynomialLaplacianComponents
                (finiteModePolynomialReconstructedVelocityComponents modePoly a s))
            t j) =
        MvPolynomial.pderiv j
          (finiteModePolynomialClosingPressureGradientComponents
            ν modePoly C a
              (fun s => finiteModePolynomialLaplacianComponents
                (finiteModePolynomialReconstructedVelocityComponents modePoly a s))
            t i)) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity
        (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y) a ∧
        p = (fun t x =>
          finiteModePolynomialPressureMode
            (finiteModePolynomialClosingPressureGradientComponents
              ν modePoly C a
                (fun s => finiteModePolynomialLaplacianComponents
                  (finiteModePolynomialReconstructedVelocityComponents modePoly a s))
              t) x) ∧
          ∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
            timeVelocityDerivative u t x +
                spatialConvection u t x +
                  spatialPressureGradient p t x =
              ν • spatialLaplacian u t x := by
  refine
    finiteModeProjectedNS_local_reconstructed_velocityPolynomialPressure_momentum_of_polynomialHelmholtz
      ν (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y)
      C a ε ha
      (finiteModePolynomialClosingPressureGradientComponents
        ν modePoly C a
          (fun s => finiteModePolynomialLaplacianComponents
            (finiteModePolynomialReconstructedVelocityComponents modePoly a s)))
      hcurl ?_
  intro t _ht
  funext x
  change
    -finiteModeNonPressureMomentumDefect ν
        (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y) C a t x =
      finiteModePolynomialVectorFieldEval
        (finiteModePolynomialClosingPressureGradientComponents
          ν modePoly C a
            (fun s => finiteModePolynomialLaplacianComponents
              (finiteModePolynomialReconstructedVelocityComponents modePoly a s))
          t) x
  rw [finiteModePolynomialNonPressureDefect_eq_eval ν modePoly C a t x]
  ext j
  simp [finiteModePolynomialClosingPressureGradientComponents,
    finiteModePolynomialVectorFieldEval_apply]

/-- One-mode polynomial spatial mode `x ↦ x`.  This gives a concrete
nonconstant finite-mode reconstruction whose pressure closure is handled by
the general polynomial primitive theorem. -/
def finiteModeRadialLinearPolynomialMode (_ : PUnit) :
    Fin 3 → MvPolynomial (Fin 3) ℝ :=
  fun j => MvPolynomial.X j

/-- The radial linear reconstruction is the concrete field `u(t,x)=t x`. -/
theorem finiteModeRadialLinear_reconstructedVelocity_eq
    (t : NSTime) (x : NSSpace) :
    finiteModeReconstructedVelocity
        (fun i y =>
          finiteModePolynomialVectorFieldEval
            (finiteModeRadialLinearPolynomialMode i) y)
        finiteModeIdentityCoefficientCurve t x =
      t • x := by
  ext j
  simp [finiteModeReconstructedVelocity, finiteModeReconstructionCLM,
    finiteModeRadialLinearPolynomialMode, finiteModeIdentityCoefficientCurve,
    finiteModePolynomialVectorFieldEval_apply]

/-- The projected acceleration for the radial linear identity-coefficient
solution is `x`. -/
theorem finiteModeRadialLinear_reconstructedAcceleration_eq
    (t : NSTime) (x : NSSpace) :
    finiteModeReconstructedAcceleration
        (fun i y =>
          finiteModePolynomialVectorFieldEval
            (finiteModeRadialLinearPolynomialMode i) y)
        finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve t x =
      x := by
  ext j
  simp [finiteModeReconstructedAcceleration, finiteModeReconstructedVelocity,
    finiteModeReconstructionCLM, finiteModeProjectedNSRHS,
    finiteModeUnitForcingCoefficients, finiteModeIdentityCoefficientCurve,
    finiteModeRadialLinearPolynomialMode, finiteModePolynomialVectorFieldEval_apply]

/-- The time derivative of the radial linear reconstruction is `x`. -/
theorem finiteModeRadialLinear_timeVelocityDerivative_eq
    (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative
        (finiteModeReconstructedVelocity
          (fun i y =>
            finiteModePolynomialVectorFieldEval
              (finiteModeRadialLinearPolynomialMode i) y)
          finiteModeIdentityCoefficientCurve) t x =
      x := by
  rw [finiteModeReconstructedVelocity_timeDerivative_at
    (fun i y => finiteModePolynomialVectorFieldEval
      (finiteModeRadialLinearPolynomialMode i) y)
    finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve t
    (finiteModeIdentityCoefficientCurve_hasDerivAt t) x]
  exact finiteModeRadialLinear_reconstructedAcceleration_eq t x

/-- The convection term for `u(t,x)=t x` is `t^2 x`. -/
theorem finiteModeRadialLinear_spatialConvection_eq
    (t : NSTime) (x : NSSpace) :
    spatialConvection
        (finiteModeReconstructedVelocity
          (fun i y =>
            finiteModePolynomialVectorFieldEval
              (finiteModeRadialLinearPolynomialMode i) y)
          finiteModeIdentityCoefficientCurve) t x =
      (t * t) • x := by
  rw [finiteModePolynomialReconstructedVelocity_spatialConvection
    finiteModeRadialLinearPolynomialMode finiteModeIdentityCoefficientCurve t x]
  ext j
  simp [finiteModePolynomialConvectionComponents,
    finiteModePolynomialReconstructedVelocityComponents,
    finiteModeRadialLinearPolynomialMode, finiteModeIdentityCoefficientCurve,
    finiteModePolynomialVectorFieldEval_apply, MvPolynomial.pderiv_X,
    Pi.single_apply, MvPolynomial.eval_mul]
  ring

/-- The radial linear reconstruction has zero spatial Laplacian. -/
theorem finiteModeRadialLinear_spatialLaplacian_zero
    (t : NSTime) (x : NSSpace) :
    spatialLaplacian
        (finiteModeReconstructedVelocity
          (fun i y =>
            finiteModePolynomialVectorFieldEval
              (finiteModeRadialLinearPolynomialMode i) y)
          finiteModeIdentityCoefficientCurve) t x =
      0 := by
  rw [finiteModePolynomialReconstructedVelocity_spatialLaplacian
    finiteModeRadialLinearPolynomialMode finiteModeIdentityCoefficientCurve t x]
  ext j
  fin_cases j <;>
    simp [finiteModePolynomialLaplacianComponents,
      finiteModePolynomialScalarLaplacian,
      finiteModePolynomialReconstructedVelocityComponents,
      finiteModeRadialLinearPolynomialMode, finiteModeIdentityCoefficientCurve,
      finiteModePolynomialVectorFieldEval_apply, Fin.sum_univ_three,
      MvPolynomial.pderiv_X, Pi.single_apply]

/-- The radial linear example has the explicit closing pressure gradient
`-(1 + t^2) x`.  Viscosity drops out because the formal Laplacian of the
linear radial mode is zero. -/
theorem finiteModeRadialLinearPolynomialClosingPressureGradient_eq
    (ν t : ℝ) (j : Fin 3) :
    finiteModePolynomialClosingPressureGradientComponents
        ν finiteModeRadialLinearPolynomialMode
          finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve
          (fun s => finiteModePolynomialLaplacianComponents
            (finiteModePolynomialReconstructedVelocityComponents
              finiteModeRadialLinearPolynomialMode
              finiteModeIdentityCoefficientCurve s))
        t j =
      -(MvPolynomial.C (1 + t * t) * MvPolynomial.X j) := by
  fin_cases j <;>
    simp [finiteModePolynomialClosingPressureGradientComponents,
      finiteModePolynomialNonPressureDefectComponents,
      finiteModePolynomialReconstructedAccelerationComponents,
      finiteModePolynomialConvectionComponents,
      finiteModePolynomialLaplacianComponents,
      finiteModePolynomialReconstructedVelocityComponents,
      finiteModeRadialLinearPolynomialMode,
      finiteModeProjectedNSRHS, finiteModeUnitForcingCoefficients,
      finiteModeIdentityCoefficientCurve, finiteModePolynomialScalarLaplacian,
      Fin.sum_univ_three, MvPolynomial.pderiv_X, Pi.single_apply] <;>
    ring

/-- For the radial linear polynomial mode, the fully computed closing
pressure-gradient polynomial is curl-free.  This is a concrete positive check
of the polynomial closure condition including the convection and Laplacian
computations. -/
theorem finiteModeRadialLinearPolynomialClosingPressureGradient_curlFree
    (ν ε : ℝ) :
    ∀ t ∈ Ioo (-ε) ε, ∀ i j,
      MvPolynomial.pderiv i
          (finiteModePolynomialClosingPressureGradientComponents
            ν finiteModeRadialLinearPolynomialMode
              finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve
              (fun s => finiteModePolynomialLaplacianComponents
                (finiteModePolynomialReconstructedVelocityComponents
                  finiteModeRadialLinearPolynomialMode
                  finiteModeIdentityCoefficientCurve s))
            t j) =
        MvPolynomial.pderiv j
          (finiteModePolynomialClosingPressureGradientComponents
            ν finiteModeRadialLinearPolynomialMode
              finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve
              (fun s => finiteModePolynomialLaplacianComponents
                (finiteModePolynomialReconstructedVelocityComponents
                  finiteModeRadialLinearPolynomialMode
                  finiteModeIdentityCoefficientCurve s))
            t i) := by
  intro t _ht i j
  fin_cases i <;> fin_cases j <;>
    simp [finiteModePolynomialClosingPressureGradientComponents,
      finiteModePolynomialNonPressureDefectComponents,
      finiteModePolynomialReconstructedAccelerationComponents,
      finiteModePolynomialConvectionComponents,
      finiteModePolynomialLaplacianComponents,
      finiteModePolynomialReconstructedVelocityComponents,
      finiteModeRadialLinearPolynomialMode,
      finiteModeProjectedNSRHS, finiteModeUnitForcingCoefficients,
      finiteModeIdentityCoefficientCurve, finiteModePolynomialScalarLaplacian,
      Fin.sum_univ_three, MvPolynomial.pderiv_X, Pi.single_apply]

/-- The explicit polynomial primitive constructed for the radial linear mode has
pressure gradient `-(1 + t^2) x` on the local interval. -/
theorem finiteModeRadialLinearPolynomialPressureGradient_eq
    (ν ε : ℝ) {t : NSTime} (ht : t ∈ Ioo (-ε) ε) (x : NSSpace) :
    spatialPressureGradient
        (fun s y =>
          finiteModePolynomialPressureMode
            (finiteModePolynomialClosingPressureGradientComponents
              ν finiteModeRadialLinearPolynomialMode
                finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve
                (fun r => finiteModePolynomialLaplacianComponents
                  (finiteModePolynomialReconstructedVelocityComponents
                    finiteModeRadialLinearPolynomialMode
                    finiteModeIdentityCoefficientCurve r))
              s) y)
        t x =
      -(1 + t * t) • x := by
  unfold spatialPressureGradient
  rw [finiteModePolynomialPressureMode_gradient
    (finiteModePolynomialClosingPressureGradientComponents
      ν finiteModeRadialLinearPolynomialMode
        finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve
        (fun r => finiteModePolynomialLaplacianComponents
          (finiteModePolynomialReconstructedVelocityComponents
            finiteModeRadialLinearPolynomialMode
            finiteModeIdentityCoefficientCurve r))
      t)
    ((finiteModeRadialLinearPolynomialClosingPressureGradient_curlFree ν ε) t ht) x]
  ext j
  simp [finiteModePolynomialVectorFieldEval_apply,
    finiteModeRadialLinearPolynomialClosingPressureGradient_eq,
    MvPolynomial.eval_mul]
  ring

/-- Direct pointwise momentum identity for the radial linear reconstruction,
using the explicit pressure gradient formula. -/
theorem finiteModeRadialLinear_reconstructed_momentum_explicit
    (ν ε : ℝ) {t : NSTime} (ht : t ∈ Ioo (-ε) ε) (x : NSSpace) :
    timeVelocityDerivative
          (finiteModeReconstructedVelocity
            (fun i y =>
              finiteModePolynomialVectorFieldEval
                (finiteModeRadialLinearPolynomialMode i) y)
            finiteModeIdentityCoefficientCurve) t x +
        spatialConvection
          (finiteModeReconstructedVelocity
            (fun i y =>
              finiteModePolynomialVectorFieldEval
                (finiteModeRadialLinearPolynomialMode i) y)
            finiteModeIdentityCoefficientCurve) t x +
          spatialPressureGradient
            (fun s y =>
              finiteModePolynomialPressureMode
                (finiteModePolynomialClosingPressureGradientComponents
                  ν finiteModeRadialLinearPolynomialMode
                    finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve
                    (fun r => finiteModePolynomialLaplacianComponents
                      (finiteModePolynomialReconstructedVelocityComponents
                        finiteModeRadialLinearPolynomialMode
                        finiteModeIdentityCoefficientCurve r))
                  s) y)
            t x =
      ν • spatialLaplacian
        (finiteModeReconstructedVelocity
          (fun i y =>
            finiteModePolynomialVectorFieldEval
              (finiteModeRadialLinearPolynomialMode i) y)
          finiteModeIdentityCoefficientCurve) t x := by
  rw [finiteModeRadialLinear_timeVelocityDerivative_eq t x,
    finiteModeRadialLinear_spatialConvection_eq t x,
    finiteModeRadialLinearPolynomialPressureGradient_eq ν ε ht x,
    finiteModeRadialLinear_spatialLaplacian_zero t x]
  ext j
  simp
  ring

/-- Diagonal-quadratic pressure coefficients for the radial-linear example:
each coordinate pressure mode receives coefficient `-(1+t^2)`. -/
def finiteModeRadialLinearDiagonalPressureCoefficients :
    NSTime → FiniteModeState (Fin 3) :=
  fun t _ => -(1 + t * t)

/-- The diagonal-quadratic pressure field closing the radial-linear example. -/
def finiteModeRadialLinearDiagonalPressure : NSPressureField :=
  finiteModeReconstructedPressure finiteModeDiagonalQuadraticPressureMode
    finiteModeRadialLinearDiagonalPressureCoefficients

/-- The finite diagonal-quadratic pressure ansatz has the same explicit
pressure gradient `-(1+t^2)x` as the polynomial primitive construction. -/
theorem finiteModeRadialLinearDiagonalPressureGradient_eq
    (t : NSTime) (x : NSSpace) :
    spatialPressureGradient finiteModeRadialLinearDiagonalPressure t x =
      -(1 + t * t) • x := by
  rw [show finiteModeRadialLinearDiagonalPressure =
      finiteModeReconstructedPressure finiteModeDiagonalQuadraticPressureMode
        (finiteModeDiagonalQuadraticPressureCoefficients
          finiteModeRadialLinearDiagonalPressureCoefficients) by
      rfl]
  rw [finiteModeDiagonalQuadraticPressure_spatialPressureGradient
    finiteModeRadialLinearDiagonalPressureCoefficients t x]
  ext j
  fin_cases j <;>
    simp [finiteModeRadialLinearDiagonalPressureCoefficients, Fin.sum_univ_three]

/-- Direct pointwise momentum identity for the radial-linear reconstruction
using the finite diagonal-quadratic pressure ansatz. -/
theorem finiteModeRadialLinear_diagonalPressure_reconstructed_momentum
    (ν : ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative
          (finiteModeReconstructedVelocity
            (fun i y =>
              finiteModePolynomialVectorFieldEval
                (finiteModeRadialLinearPolynomialMode i) y)
            finiteModeIdentityCoefficientCurve) t x +
        spatialConvection
          (finiteModeReconstructedVelocity
            (fun i y =>
              finiteModePolynomialVectorFieldEval
                (finiteModeRadialLinearPolynomialMode i) y)
            finiteModeIdentityCoefficientCurve) t x +
          spatialPressureGradient finiteModeRadialLinearDiagonalPressure t x =
      ν • spatialLaplacian
        (finiteModeReconstructedVelocity
          (fun i y =>
            finiteModePolynomialVectorFieldEval
              (finiteModeRadialLinearPolynomialMode i) y)
          finiteModeIdentityCoefficientCurve) t x := by
  rw [finiteModeRadialLinear_timeVelocityDerivative_eq t x,
    finiteModeRadialLinear_spatialConvection_eq t x,
    finiteModeRadialLinearDiagonalPressureGradient_eq t x,
    finiteModeRadialLinear_spatialLaplacian_zero t x]
  ext j
  simp
  ring

/-- The radial-linear diagonal-quadratic pressure ansatz has zero reconstructed
finite-mode momentum residual on every time set. -/
theorem finiteModeRadialLinear_diagonalPressure_reconstructedResidualZeroOn_univ
    (ν : ℝ) :
    finiteModeReconstructedMomentumResidualZeroOn Set.univ ν
      (fun i y =>
        finiteModePolynomialVectorFieldEval
          (finiteModeRadialLinearPolynomialMode i) y)
      finiteModeDiagonalQuadraticPressureMode
      finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve
      finiteModeRadialLinearDiagonalPressureCoefficients := by
  intro t _ht x
  exact
    (finiteModeReconstructedMomentumResidualZeroAt_iff_momentumEquation_at
      ν
      (fun i y =>
        finiteModePolynomialVectorFieldEval
          (finiteModeRadialLinearPolynomialMode i) y)
      finiteModeDiagonalQuadraticPressureMode
      finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve
      finiteModeRadialLinearDiagonalPressureCoefficients t
      (finiteModeIdentityCoefficientCurve_hasDerivAt t) x).mpr
      (finiteModeRadialLinear_diagonalPressure_reconstructed_momentum ν t x)

/-- Existential packaging of the radial-linear solution with the finite
diagonal-quadratic pressure basis. -/
theorem finiteModeRadialLinear_reconstructed_velocityDiagonalPressure_momentum_exists
    (ν : ℝ) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity
        (fun i y =>
          finiteModePolynomialVectorFieldEval
            (finiteModeRadialLinearPolynomialMode i) y)
        finiteModeIdentityCoefficientCurve ∧
        p = finiteModeRadialLinearDiagonalPressure ∧
        ∀ t x,
          timeVelocityDerivative u t x +
              spatialConvection u t x +
                spatialPressureGradient p t x =
            ν • spatialLaplacian u t x := by
  exact
    ⟨finiteModeReconstructedVelocity
        (fun i y =>
          finiteModePolynomialVectorFieldEval
            (finiteModeRadialLinearPolynomialMode i) y)
        finiteModeIdentityCoefficientCurve,
      finiteModeRadialLinearDiagonalPressure, rfl, rfl,
      finiteModeRadialLinear_diagonalPressure_reconstructed_momentum ν⟩

/-- Concrete nonconstant positive instance of the polynomial finite-mode
pressure construction: the radial linear mode with the identity coefficient
curve admits the explicitly constructed polynomial pressure primitive closing
the local pointwise momentum equation. -/
theorem finiteModeRadialLinear_reconstructed_velocityPolynomialPressure_momentum_exists
    (ν ε : ℝ) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity
        (fun i y =>
          finiteModePolynomialVectorFieldEval
            (finiteModeRadialLinearPolynomialMode i) y)
        finiteModeIdentityCoefficientCurve ∧
        p = (fun t x =>
          finiteModePolynomialPressureMode
            (finiteModePolynomialClosingPressureGradientComponents
              ν finiteModeRadialLinearPolynomialMode
                finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve
                (fun s => finiteModePolynomialLaplacianComponents
                  (finiteModePolynomialReconstructedVelocityComponents
                    finiteModeRadialLinearPolynomialMode
                    finiteModeIdentityCoefficientCurve s))
              t) x) ∧
          ∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
            timeVelocityDerivative u t x +
                spatialConvection u t x +
                  spatialPressureGradient p t x =
              ν • spatialLaplacian u t x := by
  exact
    finiteModeProjectedNS_local_reconstructed_velocityPolynomialPressure_momentum_of_polynomialModes_curlFree
      ν finiteModeRadialLinearPolynomialMode finiteModeUnitForcingCoefficients
      finiteModeIdentityCoefficientCurve ε
      (fun t _ht => finiteModeIdentityCoefficientCurve_hasDerivAt t)
      (finiteModeRadialLinearPolynomialClosingPressureGradient_curlFree ν ε)

/-- Affine Helmholtz closure theorem for the finite-mode reconstruction: if the
non-pressure defect is an affine vector field with symmetric linear part, the
affine-quadratic pressure basis constructs coefficients closing momentum. -/
theorem finiteModeProjectedNS_local_reconstructed_velocityPressure_momentum_of_affineHelmholtz
    {ι : Type*} [Fintype ι]
    (ν : ℝ)
    (mode : ι → NSSpace → NSSpace)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (ε : ℝ)
    (ha : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt a (finiteModeProjectedNSRHS C (a t)) t)
    (c : NSTime → NSSpace)
    (A : NSTime → Fin 3 → Fin 3 → ℝ)
    (hA : ∀ t ∈ Ioo (-ε) ε, ∀ i j, A t i j = A t j i)
    (hdefect : ∀ t ∈ Ioo (-ε) ε,
      -finiteModeNonPressureMomentumDefect ν mode C a t =
        finiteModeAffineGradientField (c t) (A t)) :
    ∃ b : ℝ → FiniteModeState FiniteModeAffineQuadraticPressureIndex,
      ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity mode a ∧
        p = finiteModeReconstructedPressure finiteModeAffineQuadraticPressureMode b ∧
          finiteModeReconstructedMomentumResidualZeroOn
            (Ioo (-ε) ε) ν mode finiteModeAffineQuadraticPressureMode C a b ∧
          ∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
            timeVelocityDerivative u t x +
                spatialConvection u t x +
                  spatialPressureGradient p t x =
              ν • spatialLaplacian u t x := by
  refine
    finiteModeProjectedNS_local_reconstructed_velocityPressure_momentum_of_pressureHelmholtzRange
      ν mode finiteModeAffineQuadraticPressureMode C a ε ha
      (fun k x => finiteModeAffineQuadraticPressureMode_differentiableAt k x) ?_
  intro t ht
  rw [hdefect t ht]
  exact finiteModeAffineQuadraticPressureGradient_mem_range (c t) (A t) (hA t ht)

/-- Polynomial-mode affine finite-pressure closure: if the fully computed
closing pressure-gradient polynomial is an affine vector field with symmetric
linear part, the affine-quadratic pressure basis constructs finite pressure
coefficients closing the reconstructed pointwise momentum equation. -/
theorem finiteModeProjectedNS_local_reconstructed_velocityAffineQuadraticPressure_momentum_of_polynomialModes_affineClosingGradient
    {ι : Type*} [Fintype ι]
    (ν : ℝ)
    (modePoly : ι → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (ε : ℝ)
    (ha : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt a (finiteModeProjectedNSRHS C (a t)) t)
    (c : NSTime → NSSpace)
    (A : NSTime → Fin 3 → Fin 3 → ℝ)
    (hA : ∀ t ∈ Ioo (-ε) ε, ∀ i j, A t i j = A t j i)
    (hclosing : ∀ t ∈ Ioo (-ε) ε,
      finiteModePolynomialVectorFieldEval
          (finiteModePolynomialClosingPressureGradientComponents
            ν modePoly C a
              (fun s => finiteModePolynomialLaplacianComponents
                (finiteModePolynomialReconstructedVelocityComponents modePoly a s))
            t) =
        finiteModeAffineGradientField (c t) (A t)) :
    ∃ b : ℝ → FiniteModeState FiniteModeAffineQuadraticPressureIndex,
      ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity
        (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y) a ∧
        p = finiteModeReconstructedPressure finiteModeAffineQuadraticPressureMode b ∧
          finiteModeReconstructedMomentumResidualZeroOn
            (Ioo (-ε) ε) ν
              (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y)
              finiteModeAffineQuadraticPressureMode C a b ∧
          ∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
            timeVelocityDerivative u t x +
                spatialConvection u t x +
                  spatialPressureGradient p t x =
              ν • spatialLaplacian u t x := by
  refine
    finiteModeProjectedNS_local_reconstructed_velocityPressure_momentum_of_affineHelmholtz
      ν (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y)
      C a ε ha c A hA ?_
  intro t ht
  funext x
  calc
    (-finiteModeNonPressureMomentumDefect ν
        (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y) C a t) x =
      finiteModePolynomialVectorFieldEval
        (finiteModePolynomialClosingPressureGradientComponents
          ν modePoly C a
            (fun s => finiteModePolynomialLaplacianComponents
              (finiteModePolynomialReconstructedVelocityComponents modePoly a s))
          t) x := by
        ext j
        have hdefj := congrArg (fun v : NSSpace => v j)
          (finiteModePolynomialNonPressureDefect_eq_eval ν modePoly C a t x)
        simp [finiteModePolynomialClosingPressureGradientComponents,
          finiteModePolynomialVectorFieldEval_apply, hdefj]
    _ = finiteModeAffineGradientField (c t) (A t) x := by
        exact congrFun (hclosing t ht) x

/-- Zero affine offset for the affine-quadratic presentation of the
radial-linear pressure gradient. -/
def finiteModeRadialLinearAffinePressureConstant : NSTime → NSSpace :=
  fun _ => 0

/-- Diagonal matrix for the affine-gradient presentation of
`-(1+t^2)x`. -/
def finiteModeRadialLinearAffinePressureMatrix
    (t : NSTime) : Fin 3 → Fin 3 → ℝ :=
  fun i j => if i = j then -(1 + t * t) else 0

/-- The radial-linear affine pressure matrix is symmetric. -/
theorem finiteModeRadialLinearAffinePressureMatrix_symm
    (t : NSTime) :
    ∀ i j, finiteModeRadialLinearAffinePressureMatrix t i j =
      finiteModeRadialLinearAffinePressureMatrix t j i := by
  intro i j
  by_cases hij : i = j
  · subst j
    simp [finiteModeRadialLinearAffinePressureMatrix]
  · have hji : j ≠ i := fun h => hij h.symm
    simp [finiteModeRadialLinearAffinePressureMatrix, hij, hji]

/-- The affine-gradient presentation of the radial-linear pressure gradient is
the vector field `-(1+t^2)x`. -/
theorem finiteModeRadialLinearAffineGradientField_eq
    (t : NSTime) (x : NSSpace) :
    finiteModeAffineGradientField
        (finiteModeRadialLinearAffinePressureConstant t)
        (finiteModeRadialLinearAffinePressureMatrix t) x =
      -(1 + t * t) • x := by
  ext j
  fin_cases j <;>
    simp [finiteModeAffineGradientField,
      finiteModeRadialLinearAffinePressureConstant,
      finiteModeRadialLinearAffinePressureMatrix,
      Fin.sum_univ_three]

/-- The computed radial-linear polynomial closing pressure gradient evaluates
to the explicit vector field `-(1+t^2)x`. -/
theorem finiteModeRadialLinearPolynomialClosingPressureGradient_eval_eq
    (ν t : ℝ) (x : NSSpace) :
    finiteModePolynomialVectorFieldEval
        (finiteModePolynomialClosingPressureGradientComponents
          ν finiteModeRadialLinearPolynomialMode
            finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve
            (fun s => finiteModePolynomialLaplacianComponents
              (finiteModePolynomialReconstructedVelocityComponents
                finiteModeRadialLinearPolynomialMode
                finiteModeIdentityCoefficientCurve s))
          t) x =
      -(1 + t * t) • x := by
  ext j
  simp [finiteModePolynomialVectorFieldEval_apply,
    finiteModeRadialLinearPolynomialClosingPressureGradient_eq,
    MvPolynomial.eval_mul]
  ring

/-- The computed radial-linear polynomial closing pressure gradient is an
affine symmetric gradient field, so it lies in the finite affine-quadratic
pressure basis. -/
theorem finiteModeRadialLinearPolynomialClosingPressureGradient_affine_eq
    (ν t : ℝ) :
    finiteModePolynomialVectorFieldEval
        (finiteModePolynomialClosingPressureGradientComponents
          ν finiteModeRadialLinearPolynomialMode
            finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve
            (fun s => finiteModePolynomialLaplacianComponents
              (finiteModePolynomialReconstructedVelocityComponents
                finiteModeRadialLinearPolynomialMode
                finiteModeIdentityCoefficientCurve s))
          t) =
      finiteModeAffineGradientField
        (finiteModeRadialLinearAffinePressureConstant t)
        (finiteModeRadialLinearAffinePressureMatrix t) := by
  funext x
  rw [finiteModeRadialLinearPolynomialClosingPressureGradient_eval_eq ν t x,
    finiteModeRadialLinearAffineGradientField_eq t x]

/-- Explicit affine-quadratic pressure coefficients for the radial-linear
example.  Only the diagonal quadratic slots are nonzero. -/
def finiteModeRadialLinearAffineQuadraticPressureCoefficients :
    NSTime → FiniteModeState FiniteModeAffineQuadraticPressureIndex :=
  fun t =>
    finiteModeAffineQuadraticPressureCoefficientsAt
      (finiteModeRadialLinearAffinePressureConstant t)
      (finiteModeRadialLinearAffinePressureMatrix t)

/-- The explicit affine-quadratic pressure field closing the radial-linear
example. -/
def finiteModeRadialLinearAffineQuadraticPressure : NSPressureField :=
  finiteModeReconstructedPressure finiteModeAffineQuadraticPressureMode
    finiteModeRadialLinearAffineQuadraticPressureCoefficients

/-- The explicit affine-quadratic pressure has spatial gradient
`-(1+t^2)x`. -/
theorem finiteModeRadialLinearAffineQuadraticPressureGradient_eq
    (t : NSTime) (x : NSSpace) :
    spatialPressureGradient finiteModeRadialLinearAffineQuadraticPressure t x =
      -(1 + t * t) • x := by
  unfold finiteModeRadialLinearAffineQuadraticPressure
  rw [finiteModeReconstructedPressure_spatialPressureGradient
    finiteModeAffineQuadraticPressureMode
    finiteModeRadialLinearAffineQuadraticPressureCoefficients t x
    (fun k => finiteModeAffineQuadraticPressureMode_differentiableAt k x)]
  change
    finiteModePressureGradientSynthesis finiteModeAffineQuadraticPressureMode
        (finiteModeAffineQuadraticPressureCoefficientsAt
          (finiteModeRadialLinearAffinePressureConstant t)
          (finiteModeRadialLinearAffinePressureMatrix t)) x =
      -(1 + t * t) • x
  rw [finiteModeAffineQuadraticPressureGradientSynthesis
    (finiteModeRadialLinearAffinePressureConstant t)
    (finiteModeRadialLinearAffinePressureMatrix t)
    (finiteModeRadialLinearAffinePressureMatrix_symm t) x,
    finiteModeRadialLinearAffineGradientField_eq t x]

/-- Direct pointwise momentum identity for the radial-linear reconstruction
using the explicit affine-quadratic pressure coefficients. -/
theorem finiteModeRadialLinear_affineQuadraticPressure_reconstructed_momentum
    (ν : ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative
          (finiteModeReconstructedVelocity
            (fun i y =>
              finiteModePolynomialVectorFieldEval
                (finiteModeRadialLinearPolynomialMode i) y)
            finiteModeIdentityCoefficientCurve) t x +
        spatialConvection
          (finiteModeReconstructedVelocity
            (fun i y =>
              finiteModePolynomialVectorFieldEval
                (finiteModeRadialLinearPolynomialMode i) y)
            finiteModeIdentityCoefficientCurve) t x +
          spatialPressureGradient finiteModeRadialLinearAffineQuadraticPressure t x =
      ν • spatialLaplacian
        (finiteModeReconstructedVelocity
          (fun i y =>
            finiteModePolynomialVectorFieldEval
              (finiteModeRadialLinearPolynomialMode i) y)
          finiteModeIdentityCoefficientCurve) t x := by
  rw [finiteModeRadialLinear_timeVelocityDerivative_eq t x,
    finiteModeRadialLinear_spatialConvection_eq t x,
    finiteModeRadialLinearAffineQuadraticPressureGradient_eq t x,
    finiteModeRadialLinear_spatialLaplacian_zero t x]
  ext j
  simp
  ring

/-- The explicit affine-quadratic pressure coefficients give zero
reconstructed finite-mode momentum residual for the radial-linear example. -/
theorem finiteModeRadialLinear_affineQuadraticPressure_reconstructedResidualZeroOn_univ
    (ν : ℝ) :
    finiteModeReconstructedMomentumResidualZeroOn Set.univ ν
      (fun i y =>
        finiteModePolynomialVectorFieldEval
          (finiteModeRadialLinearPolynomialMode i) y)
      finiteModeAffineQuadraticPressureMode
      finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve
      finiteModeRadialLinearAffineQuadraticPressureCoefficients := by
  intro t _ht x
  exact
    (finiteModeReconstructedMomentumResidualZeroAt_iff_momentumEquation_at
      ν
      (fun i y =>
        finiteModePolynomialVectorFieldEval
          (finiteModeRadialLinearPolynomialMode i) y)
      finiteModeAffineQuadraticPressureMode
      finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve
      finiteModeRadialLinearAffineQuadraticPressureCoefficients t
      (finiteModeIdentityCoefficientCurve_hasDerivAt t) x).mpr
      (by
        simpa [finiteModeRadialLinearAffineQuadraticPressure] using
          finiteModeRadialLinear_affineQuadraticPressure_reconstructed_momentum ν t x)

/-- Existential packaging of the radial-linear solution with the explicit
affine-quadratic pressure field, without using synthesized coefficients. -/
theorem finiteModeRadialLinear_reconstructed_velocityExplicitAffineQuadraticPressure_momentum_exists
    (ν : ℝ) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity
        (fun i y =>
          finiteModePolynomialVectorFieldEval
            (finiteModeRadialLinearPolynomialMode i) y)
        finiteModeIdentityCoefficientCurve ∧
        p = finiteModeRadialLinearAffineQuadraticPressure ∧
        ∀ t x,
          timeVelocityDerivative u t x +
              spatialConvection u t x +
                spatialPressureGradient p t x =
            ν • spatialLaplacian u t x := by
  exact
    ⟨finiteModeReconstructedVelocity
        (fun i y =>
          finiteModePolynomialVectorFieldEval
            (finiteModeRadialLinearPolynomialMode i) y)
        finiteModeIdentityCoefficientCurve,
      finiteModeRadialLinearAffineQuadraticPressure, rfl, rfl,
      finiteModeRadialLinear_affineQuadraticPressure_reconstructed_momentum ν⟩

/-- The radial-linear polynomial mode also closes through the finite
affine-quadratic pressure basis via the polynomial-to-affine bridge theorem. -/
theorem finiteModeRadialLinear_reconstructed_velocityAffineQuadraticPressure_momentum_exists
    (ν ε : ℝ) :
    ∃ b : ℝ → FiniteModeState FiniteModeAffineQuadraticPressureIndex,
      ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity
        (fun i y =>
          finiteModePolynomialVectorFieldEval
            (finiteModeRadialLinearPolynomialMode i) y)
        finiteModeIdentityCoefficientCurve ∧
        p = finiteModeReconstructedPressure finiteModeAffineQuadraticPressureMode b ∧
          finiteModeReconstructedMomentumResidualZeroOn
            (Ioo (-ε) ε) ν
              (fun i y =>
                finiteModePolynomialVectorFieldEval
                  (finiteModeRadialLinearPolynomialMode i) y)
              finiteModeAffineQuadraticPressureMode
              finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve b ∧
          ∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
            timeVelocityDerivative u t x +
                spatialConvection u t x +
                  spatialPressureGradient p t x =
              ν • spatialLaplacian u t x := by
  exact
    finiteModeProjectedNS_local_reconstructed_velocityAffineQuadraticPressure_momentum_of_polynomialModes_affineClosingGradient
      ν finiteModeRadialLinearPolynomialMode
      finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve ε
      (fun t _ht => finiteModeIdentityCoefficientCurve_hasDerivAt t)
      finiteModeRadialLinearAffinePressureConstant
      finiteModeRadialLinearAffinePressureMatrix
      (fun t _ht => finiteModeRadialLinearAffinePressureMatrix_symm t)
      (fun t _ht => finiteModeRadialLinearPolynomialClosingPressureGradient_affine_eq ν t)

/-- Three diagonal linear polynomial modes: mode `i` is the vector field
`x_i e_i`.  Unlike the one-mode radial-linear example, the three coordinate
directions now carry independent amplitudes. -/
def finiteModeDiagonalLinearPolynomialMode (i : Fin 3) :
    Fin 3 → MvPolynomial (Fin 3) ℝ :=
  Pi.single i (MvPolynomial.X i)

/-- Constant projected forcing for the diagonal-linear three-mode family. -/
def finiteModeDiagonalLinearForcingCoefficients
    (lam : Fin 3 → ℝ) : FiniteModeProjectedNSCoefficients (Fin 3) where
  forcing := lam
  linear := fun _ _ => 0
  quadratic := fun _ _ _ => 0

/-- The diagonal-linear forced projected system has constant RHS `lam`. -/
@[simp]
theorem finiteModeDiagonalLinearForcingCoefficients_rhs
    (lam : Fin 3 → ℝ) (a : FiniteModeState (Fin 3)) (i : Fin 3) :
    finiteModeProjectedNSRHS
        (finiteModeDiagonalLinearForcingCoefficients lam) a i =
      lam i := by
  simp [finiteModeProjectedNSRHS, finiteModeDiagonalLinearForcingCoefficients]

/-- Independent linear-in-time amplitudes for the diagonal-linear family. -/
def finiteModeDiagonalLinearCoefficientCurve
    (lam : Fin 3 → ℝ) : ℝ → FiniteModeState (Fin 3) :=
  fun t i => lam i * t

/-- The diagonal-linear coefficient curve solves the forced diagonal projected
ODE with no linear or quadratic coefficient interactions. -/
theorem finiteModeDiagonalLinearCoefficientCurve_hasDerivAt
    (lam : Fin 3 → ℝ) (t : NSTime) :
    HasDerivAt (finiteModeDiagonalLinearCoefficientCurve lam)
      (finiteModeProjectedNSRHS (finiteModeDiagonalLinearForcingCoefficients lam)
        (finiteModeDiagonalLinearCoefficientCurve lam t)) t := by
  rw [hasDerivAt_pi]
  intro i
  simpa [finiteModeDiagonalLinearCoefficientCurve, finiteModeProjectedNSRHS,
    finiteModeDiagonalLinearForcingCoefficients] using
    (hasDerivAt_id t).const_mul (lam i)

/-- Component formula for the anisotropic diagonal-linear reconstructed
velocity: `u_i(t,x)=lam_i t x_i`. -/
theorem finiteModeDiagonalLinear_reconstructedVelocity_apply
    (lam : Fin 3 → ℝ) (t : NSTime) (x : NSSpace) (j : Fin 3) :
    finiteModeReconstructedVelocity
        (fun i y =>
          finiteModePolynomialVectorFieldEval
            (finiteModeDiagonalLinearPolynomialMode i) y)
        (finiteModeDiagonalLinearCoefficientCurve lam) t x j =
      lam j * t * x j := by
  fin_cases j <;>
    simp [finiteModeReconstructedVelocity, finiteModeReconstructionCLM,
      finiteModeDiagonalLinearCoefficientCurve,
      finiteModeDiagonalLinearPolynomialMode,
      finiteModePolynomialVectorFieldEval_apply,
      Fin.sum_univ_three]

/-- Diagonal matrix for the affine-gradient presentation of the pressure
gradient closing the anisotropic diagonal-linear velocity family. -/
def finiteModeDiagonalLinearAffinePressureMatrix
    (lam : Fin 3 → ℝ) (t : NSTime) : Fin 3 → Fin 3 → ℝ :=
  fun i j => if i = j then -(lam i + (lam i * t) * (lam i * t)) else 0

/-- The diagonal-linear affine pressure matrix is symmetric. -/
theorem finiteModeDiagonalLinearAffinePressureMatrix_symm
    (lam : Fin 3 → ℝ) (t : NSTime) :
    ∀ i j, finiteModeDiagonalLinearAffinePressureMatrix lam t i j =
      finiteModeDiagonalLinearAffinePressureMatrix lam t j i := by
  intro i j
  by_cases hij : i = j
  · subst j
    simp [finiteModeDiagonalLinearAffinePressureMatrix]
  · have hji : j ≠ i := fun h => hij h.symm
    simp [finiteModeDiagonalLinearAffinePressureMatrix, hij, hji]

/-- The affine-gradient presentation of the diagonal-linear closing pressure
gradient. -/
theorem finiteModeDiagonalLinearAffineGradientField_eq
    (lam : Fin 3 → ℝ) (t : NSTime) (x : NSSpace) :
    finiteModeAffineGradientField 0
        (finiteModeDiagonalLinearAffinePressureMatrix lam t) x =
      fun j => -(lam j + (lam j * t) * (lam j * t)) * x j := by
  ext j
  fin_cases j <;>
    simp [finiteModeAffineGradientField,
      finiteModeDiagonalLinearAffinePressureMatrix,
      Fin.sum_univ_three]

/-- The fully computed polynomial closing pressure gradient for the
diagonal-linear three-mode family is affine with symmetric diagonal linear
part.  Viscosity drops out because the modes are spatially linear. -/
theorem finiteModeDiagonalLinearPolynomialClosingPressureGradient_affine_eq
    (ν : ℝ) (lam : Fin 3 → ℝ) (t : NSTime) :
    finiteModePolynomialVectorFieldEval
        (finiteModePolynomialClosingPressureGradientComponents
          ν finiteModeDiagonalLinearPolynomialMode
            (finiteModeDiagonalLinearForcingCoefficients lam)
            (finiteModeDiagonalLinearCoefficientCurve lam)
            (fun s => finiteModePolynomialLaplacianComponents
              (finiteModePolynomialReconstructedVelocityComponents
                finiteModeDiagonalLinearPolynomialMode
                (finiteModeDiagonalLinearCoefficientCurve lam) s))
          t) =
      finiteModeAffineGradientField 0
        (finiteModeDiagonalLinearAffinePressureMatrix lam t) := by
  funext x
  ext j
  fin_cases j <;>
    simp [finiteModePolynomialClosingPressureGradientComponents,
      finiteModePolynomialNonPressureDefectComponents,
      finiteModePolynomialReconstructedAccelerationComponents,
      finiteModePolynomialConvectionComponents,
      finiteModePolynomialLaplacianComponents,
      finiteModePolynomialScalarLaplacian,
      finiteModePolynomialReconstructedVelocityComponents,
      finiteModeDiagonalLinearPolynomialMode,
      finiteModeProjectedNSRHS,
      finiteModeDiagonalLinearForcingCoefficients,
      finiteModeDiagonalLinearCoefficientCurve,
      finiteModeAffineGradientField,
      finiteModeDiagonalLinearAffinePressureMatrix,
      finiteModePolynomialVectorFieldEval_apply,
      Fin.sum_univ_three, MvPolynomial.pderiv_X, Pi.single_apply,
      MvPolynomial.eval_mul] <;>
    ring_nf

/-- Multi-mode positive instance: every anisotropic diagonal-linear velocity
family `u_i(t,x)=lam_i t x_i` admits affine-quadratic finite pressure
coefficients closing the reconstructed local pointwise momentum equation. -/
theorem finiteModeDiagonalLinear_reconstructed_velocityAffineQuadraticPressure_momentum_exists
    (ν ε : ℝ) (lam : Fin 3 → ℝ) :
    ∃ b : ℝ → FiniteModeState FiniteModeAffineQuadraticPressureIndex,
      ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity
        (fun i y =>
          finiteModePolynomialVectorFieldEval
            (finiteModeDiagonalLinearPolynomialMode i) y)
        (finiteModeDiagonalLinearCoefficientCurve lam) ∧
        p = finiteModeReconstructedPressure finiteModeAffineQuadraticPressureMode b ∧
          finiteModeReconstructedMomentumResidualZeroOn
            (Ioo (-ε) ε) ν
              (fun i y =>
                finiteModePolynomialVectorFieldEval
                  (finiteModeDiagonalLinearPolynomialMode i) y)
              finiteModeAffineQuadraticPressureMode
              (finiteModeDiagonalLinearForcingCoefficients lam)
              (finiteModeDiagonalLinearCoefficientCurve lam) b ∧
          ∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
            timeVelocityDerivative u t x +
                spatialConvection u t x +
                  spatialPressureGradient p t x =
              ν • spatialLaplacian u t x := by
  exact
    finiteModeProjectedNS_local_reconstructed_velocityAffineQuadraticPressure_momentum_of_polynomialModes_affineClosingGradient
      ν finiteModeDiagonalLinearPolynomialMode
      (finiteModeDiagonalLinearForcingCoefficients lam)
      (finiteModeDiagonalLinearCoefficientCurve lam) ε
      (fun t _ht => finiteModeDiagonalLinearCoefficientCurve_hasDerivAt lam t)
      (fun _ => 0)
      (finiteModeDiagonalLinearAffinePressureMatrix lam)
      (fun t _ht => finiteModeDiagonalLinearAffinePressureMatrix_symm lam t)
      (fun t _ht => finiteModeDiagonalLinearPolynomialClosingPressureGradient_affine_eq ν lam t)

/-- Each diagonal-linear polynomial mode is differentiable at every spatial
point. -/
theorem finiteModeDiagonalLinearPolynomialMode_differentiableAt
    (i : Fin 3) (x : NSSpace) :
    DifferentiableAt ℝ
      (fun y : NSSpace =>
        finiteModePolynomialVectorFieldEval
          (finiteModeDiagonalLinearPolynomialMode i) y) x :=
  (finiteModePolynomialVectorFieldEval_hasFDerivAt
    (finiteModeDiagonalLinearPolynomialMode i) x).differentiableAt

/-- Each diagonal-linear mode `x_i e_i` has spatial divergence `1`. -/
theorem finiteModeDiagonalLinearPolynomialMode_spatialDivergence
    (i : Fin 3) (t : NSTime) (x : NSSpace) :
    spatialDivergence
        (fun _ : NSTime => fun y : NSSpace =>
          finiteModePolynomialVectorFieldEval
            (finiteModeDiagonalLinearPolynomialMode i) y) t x = 1 := by
  unfold spatialDivergence spatialFDeriv
  change
    (∑ j : Fin 3,
      (fderiv ℝ
          (finiteModePolynomialVectorFieldEval
            (finiteModeDiagonalLinearPolynomialMode i)) x
        (EuclideanSpace.single j (1 : ℝ))) j) = 1
  rw [(finiteModePolynomialVectorFieldEval_hasFDerivAt
    (finiteModeDiagonalLinearPolynomialMode i) x).fderiv]
  fin_cases i <;>
    simp [finiteModeDiagonalLinearPolynomialMode,
      finiteModePolynomialVectorFieldFDeriv_apply, Fin.sum_univ_three,
      MvPolynomial.pderiv_X, Pi.single_apply]

/-- If the non-pressure finite-mode residual is closed by a spatially constant
time-dependent vector `c(t)`, the coordinate pressure modes construct a concrete
pressure field whose gradient is `c(t)` and hence close the local momentum
equation. -/
theorem finiteModeProjectedNS_local_reconstructed_velocityCoordinatePressure_momentum_of_constantGradient_balance
    {ι : Type*} [Fintype ι]
    (ν : ℝ)
    (mode : ι → NSSpace → NSSpace)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (c : NSTime → NSSpace)
    (ε : ℝ)
    (ha : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt a (finiteModeProjectedNSRHS C (a t)) t)
    (hbalance : ∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
      finiteModeReconstructedAcceleration mode C a t x +
          spatialConvection (finiteModeReconstructedVelocity mode a) t x +
            c t =
        ν • spatialLaplacian (finiteModeReconstructedVelocity mode a) t x) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity mode a ∧
        p = finiteModeReconstructedPressure finiteModeCoordinatePressureMode
          (finiteModeCoordinatePressureCoefficients c) ∧
          ∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
            timeVelocityDerivative u t x +
                spatialConvection u t x +
                  spatialPressureGradient p t x =
              ν • spatialLaplacian u t x := by
  refine
    finiteModeProjectedNS_local_reconstructed_velocityPressure_momentum_of_pressureModeGradient_balance
      ν mode finiteModeCoordinatePressureMode C a
      (finiteModeCoordinatePressureCoefficients c) ε ha
      (fun j x => finiteModeCoordinatePressureMode_differentiableAt j x) ?_
  intro t ht x
  have hgrad :
      (∑ j : Fin 3,
        finiteModeCoordinatePressureCoefficients c t j •
          gradient (finiteModeCoordinatePressureMode j) x) = c t := by
    calc
      (∑ j : Fin 3,
        finiteModeCoordinatePressureCoefficients c t j •
          gradient (finiteModeCoordinatePressureMode j) x) =
        ∑ j : Fin 3, c t j • EuclideanSpace.single j (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro j _hj
          rw [finiteModeCoordinatePressureMode_gradient]
          rfl
      _ = c t := finiteModeCoordinatePressureMode_gradient_sum (c t)
  rw [hgrad]
  exact hbalance t ht x

/-- If the non-pressure finite-mode residual is closed by a diagonal
linear-in-space gradient field, the diagonal quadratic pressure modes construct
a nonconstant pressure field and close the local momentum equation. -/
theorem finiteModeProjectedNS_local_reconstructed_velocityDiagonalQuadraticPressure_momentum_of_diagonalLinearGradient_balance
    {ι : Type*} [Fintype ι]
    (ν : ℝ)
    (mode : ι → NSSpace → NSSpace)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (d : NSTime → FiniteModeState (Fin 3))
    (ε : ℝ)
    (ha : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt a (finiteModeProjectedNSRHS C (a t)) t)
    (hbalance : ∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
      finiteModeReconstructedAcceleration mode C a t x +
          spatialConvection (finiteModeReconstructedVelocity mode a) t x +
            (∑ j : Fin 3, d t j • (x j • EuclideanSpace.single j (1 : ℝ))) =
        ν • spatialLaplacian (finiteModeReconstructedVelocity mode a) t x) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity mode a ∧
        p = finiteModeReconstructedPressure finiteModeDiagonalQuadraticPressureMode
          (finiteModeDiagonalQuadraticPressureCoefficients d) ∧
          ∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
            timeVelocityDerivative u t x +
                spatialConvection u t x +
                  spatialPressureGradient p t x =
              ν • spatialLaplacian u t x := by
  refine
    finiteModeProjectedNS_local_reconstructed_velocityPressure_momentum_of_pressureModeGradient_balance
      ν mode finiteModeDiagonalQuadraticPressureMode C a
      (finiteModeDiagonalQuadraticPressureCoefficients d) ε ha
      (fun j x => finiteModeDiagonalQuadraticPressureMode_differentiableAt j x) ?_
  intro t ht x
  have hgrad :
      (∑ j : Fin 3,
        finiteModeDiagonalQuadraticPressureCoefficients d t j •
          gradient (finiteModeDiagonalQuadraticPressureMode j) x) =
        ∑ j : Fin 3, d t j • (x j • EuclideanSpace.single j (1 : ℝ)) := by
    apply Finset.sum_congr rfl
    intro j _hj
    rw [finiteModeDiagonalQuadraticPressureMode_gradient]
    rfl
  rw [hgrad]
  exact hbalance t ht x

/-- Spatial divergence of a reconstructed finite-mode velocity is the finite
sum of the modal divergences weighted by the current coefficients. -/
theorem finiteModeReconstructedVelocity_spatialDivergence
    {ι : Type*} [Fintype ι]
    (mode : ι → NSSpace → NSSpace)
    (a : ℝ → FiniteModeState ι)
    (t : NSTime) (x : NSSpace)
    (hmode : ∀ i, DifferentiableAt ℝ (mode i) x) :
    spatialDivergence (finiteModeReconstructedVelocity mode a) t x =
      ∑ i : ι, a t i *
        spatialDivergence (fun _ : NSTime => mode i) t x := by
  unfold spatialDivergence spatialFDeriv
  have hdiff :
      ∀ i ∈ (Finset.univ : Finset ι),
        DifferentiableAt ℝ (fun y : NSSpace => a t i • mode i y) x := by
    intro i _hi
    exact (hmode i).const_smul (a t i)
  have hfderiv :
      fderiv ℝ (fun y : NSSpace => finiteModeReconstructedVelocity mode a t y) x =
        ∑ i : ι, fderiv ℝ (fun y : NSSpace => a t i • mode i y) x := by
    simpa [finiteModeReconstructedVelocity, finiteModeReconstructionCLM] using
      (fderiv_fun_sum hdiff)
  rw [hfderiv]
  calc
    ∑ j : Fin 3,
        ((∑ i : ι, fderiv ℝ (fun y : NSSpace => a t i • mode i y) x)
            (EuclideanSpace.single j (1 : ℝ))) j =
      ∑ j : Fin 3,
        ∑ i : ι,
          (fderiv ℝ (fun y : NSSpace => a t i • mode i y) x
            (EuclideanSpace.single j (1 : ℝ))) j := by
        simp
    _ =
      ∑ i : ι,
        ∑ j : Fin 3,
          (fderiv ℝ (fun y : NSSpace => a t i • mode i y) x
            (EuclideanSpace.single j (1 : ℝ))) j := by
        rw [Finset.sum_comm]
    _ =
      ∑ i : ι, a t i *
        ∑ j : Fin 3,
          (fderiv ℝ (fun y : NSSpace => mode i y) x
            (EuclideanSpace.single j (1 : ℝ))) j := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [fderiv_fun_const_smul (hmode i) (a t i)]
        simp [Finset.mul_sum]
    _ =
      ∑ i : ι, a t i *
        spatialDivergence (fun _ : NSTime => mode i) t x := by
        rfl

/-- If every selected mode is divergence-free, the reconstructed velocity is
divergence-free at every point. -/
theorem finiteModeReconstructedVelocity_spatialDivergence_zero
    {ι : Type*} [Fintype ι]
    (mode : ι → NSSpace → NSSpace)
    (a : ℝ → FiniteModeState ι)
    (hmodeDiff : ∀ i x, DifferentiableAt ℝ (mode i) x)
    (hmodeDiv : ∀ i t x, spatialDivergence (fun _ : NSTime => mode i) t x = 0) :
    ∀ t x, spatialDivergence (finiteModeReconstructedVelocity mode a) t x = 0 := by
  intro t x
  rw [finiteModeReconstructedVelocity_spatialDivergence mode a t x
    (fun i => hmodeDiff i x)]
  simp [hmodeDiv]

/-- The divergence of the diagonal-linear reconstruction is the trace of its
coefficient vector, multiplied by time. -/
theorem finiteModeDiagonalLinear_spatialDivergence_eq
    (lam : Fin 3 → ℝ) (t : NSTime) (x : NSSpace) :
    spatialDivergence
        (finiteModeReconstructedVelocity
          (fun i y =>
            finiteModePolynomialVectorFieldEval
              (finiteModeDiagonalLinearPolynomialMode i) y)
          (finiteModeDiagonalLinearCoefficientCurve lam)) t x =
      t * ∑ i : Fin 3, lam i := by
  rw [finiteModeReconstructedVelocity_spatialDivergence
    (fun i y =>
      finiteModePolynomialVectorFieldEval
        (finiteModeDiagonalLinearPolynomialMode i) y)
    (finiteModeDiagonalLinearCoefficientCurve lam) t x
    (fun i => finiteModeDiagonalLinearPolynomialMode_differentiableAt i x)]
  calc
    (∑ i : Fin 3,
        finiteModeDiagonalLinearCoefficientCurve lam t i *
          spatialDivergence
            (fun _ : NSTime => fun y : NSSpace =>
              finiteModePolynomialVectorFieldEval
                (finiteModeDiagonalLinearPolynomialMode i) y) t x) =
        ∑ i : Fin 3, lam i * t := by
      apply Finset.sum_congr rfl
      intro i _hi
      simp [finiteModeDiagonalLinearCoefficientCurve,
        finiteModeDiagonalLinearPolynomialMode_spatialDivergence]
    _ = (∑ i : Fin 3, lam i) * t := by
      rw [Finset.sum_mul]
    _ = t * ∑ i : Fin 3, lam i := by
      ring

/-- Trace-free diagonal-linear coefficients give a divergence-free
reconstructed velocity. -/
theorem finiteModeDiagonalLinear_spatialDivergence_zero_of_trace
    (lam : Fin 3 → ℝ) (htrace : ∑ i : Fin 3, lam i = 0) :
    ∀ t x,
      spatialDivergence
        (finiteModeReconstructedVelocity
          (fun i y =>
            finiteModePolynomialVectorFieldEval
              (finiteModeDiagonalLinearPolynomialMode i) y)
          (finiteModeDiagonalLinearCoefficientCurve lam)) t x = 0 := by
  intro t x
  rw [finiteModeDiagonalLinear_spatialDivergence_eq lam t x, htrace, mul_zero]

/-- Trace-free diagonal-linear velocity families simultaneously close the
finite-mode momentum equation through affine-quadratic pressure and remain
incompressible. -/
theorem finiteModeDiagonalLinear_traceFree_reconstructed_velocityAffineQuadraticPressure_momentum_incompressible_exists
    (ν ε : ℝ) (lam : Fin 3 → ℝ) (htrace : ∑ i : Fin 3, lam i = 0) :
    ∃ b : ℝ → FiniteModeState FiniteModeAffineQuadraticPressureIndex,
      ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity
        (fun i y =>
          finiteModePolynomialVectorFieldEval
            (finiteModeDiagonalLinearPolynomialMode i) y)
        (finiteModeDiagonalLinearCoefficientCurve lam) ∧
        p = finiteModeReconstructedPressure finiteModeAffineQuadraticPressureMode b ∧
          finiteModeReconstructedMomentumResidualZeroOn
            (Ioo (-ε) ε) ν
              (fun i y =>
                finiteModePolynomialVectorFieldEval
                  (finiteModeDiagonalLinearPolynomialMode i) y)
              finiteModeAffineQuadraticPressureMode
              (finiteModeDiagonalLinearForcingCoefficients lam)
              (finiteModeDiagonalLinearCoefficientCurve lam) b ∧
          (∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
            timeVelocityDerivative u t x +
                spatialConvection u t x +
                  spatialPressureGradient p t x =
              ν • spatialLaplacian u t x) ∧
          ∀ t x, spatialDivergence u t x = 0 := by
  rcases finiteModeDiagonalLinear_reconstructed_velocityAffineQuadraticPressure_momentum_exists
      ν ε lam with
    ⟨b, u, p, hu, hp, hres, hmom⟩
  refine ⟨b, u, p, hu, hp, hres, hmom, ?_⟩
  intro t x
  rw [hu]
  exact finiteModeDiagonalLinear_spatialDivergence_zero_of_trace lam htrace t x

/-- One off-diagonal symmetric trace-free linear mode:
`α (x₁ e₀ + x₀ e₁)`.  This is a positive counterpart to the shear obstruction:
the symmetric partner makes the pressure-closing gradient affine and curl-free. -/
def finiteModeSymmetricShearPolynomialMode (α : ℝ) (_ : PUnit) :
    Fin 3 → MvPolynomial (Fin 3) ℝ :=
  fun j =>
    if j = (0 : Fin 3) then MvPolynomial.C α * MvPolynomial.X (1 : Fin 3)
    else if j = (1 : Fin 3) then MvPolynomial.C α * MvPolynomial.X (0 : Fin 3)
    else 0

/-- Component formula for the symmetric off-diagonal shear reconstruction. -/
theorem finiteModeSymmetricShear_reconstructedVelocity_apply
    (α : ℝ) (t : NSTime) (x : NSSpace) (j : Fin 3) :
    finiteModeReconstructedVelocity
        (fun i y =>
          finiteModePolynomialVectorFieldEval
            (finiteModeSymmetricShearPolynomialMode α i) y)
        finiteModeIdentityCoefficientCurve t x j =
      if j = (0 : Fin 3) then α * t * x (1 : Fin 3)
      else if j = (1 : Fin 3) then α * t * x (0 : Fin 3)
      else 0 := by
  fin_cases j <;>
    simp [finiteModeReconstructedVelocity, finiteModeReconstructionCLM,
      finiteModeIdentityCoefficientCurve, finiteModeSymmetricShearPolynomialMode,
      finiteModePolynomialVectorFieldEval_apply, MvPolynomial.eval_mul,
      mul_assoc] <;>
    ring

/-- Affine pressure matrix closing the symmetric off-diagonal shear mode. -/
def finiteModeSymmetricShearAffinePressureMatrix
    (α : ℝ) (t : NSTime) : Fin 3 → Fin 3 → ℝ :=
  fun i j =>
    if i = (0 : Fin 3) ∧ j = (0 : Fin 3) then -(α * α * (t * t))
    else if i = (1 : Fin 3) ∧ j = (1 : Fin 3) then -(α * α * (t * t))
    else if (i = (0 : Fin 3) ∧ j = (1 : Fin 3)) ∨
        (i = (1 : Fin 3) ∧ j = (0 : Fin 3)) then -α
    else 0

/-- The symmetric off-diagonal shear pressure matrix is symmetric. -/
theorem finiteModeSymmetricShearAffinePressureMatrix_symm
    (α : ℝ) (t : NSTime) :
    ∀ i j, finiteModeSymmetricShearAffinePressureMatrix α t i j =
      finiteModeSymmetricShearAffinePressureMatrix α t j i := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [finiteModeSymmetricShearAffinePressureMatrix]

/-- The affine-gradient form of the symmetric shear closing pressure gradient. -/
theorem finiteModeSymmetricShearAffineGradientField_eq
    (α : ℝ) (t : NSTime) (x : NSSpace) :
    finiteModeAffineGradientField 0
        (finiteModeSymmetricShearAffinePressureMatrix α t) x =
      fun j =>
        if j = (0 : Fin 3) then
          -(α * α * (t * t)) * x (0 : Fin 3) + (-α) * x (1 : Fin 3)
        else if j = (1 : Fin 3) then
          (-α) * x (0 : Fin 3) + -(α * α * (t * t)) * x (1 : Fin 3)
        else 0 := by
  ext j
  fin_cases j <;>
    simp [finiteModeAffineGradientField,
      finiteModeSymmetricShearAffinePressureMatrix, Fin.sum_univ_three]

/-- The computed closing pressure gradient for the symmetric off-diagonal shear
mode is affine with symmetric linear part. -/
theorem finiteModeSymmetricShearPolynomialClosingPressureGradient_affine_eq
    (ν α : ℝ) (t : NSTime) :
    finiteModePolynomialVectorFieldEval
        (finiteModePolynomialClosingPressureGradientComponents
          ν (finiteModeSymmetricShearPolynomialMode α)
            finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve
            (fun s => finiteModePolynomialLaplacianComponents
              (finiteModePolynomialReconstructedVelocityComponents
                (finiteModeSymmetricShearPolynomialMode α)
                finiteModeIdentityCoefficientCurve s))
          t) =
      finiteModeAffineGradientField 0
        (finiteModeSymmetricShearAffinePressureMatrix α t) := by
  funext x
  ext j
  fin_cases j <;>
    simp [finiteModePolynomialClosingPressureGradientComponents,
      finiteModePolynomialNonPressureDefectComponents,
      finiteModePolynomialReconstructedAccelerationComponents,
      finiteModePolynomialConvectionComponents,
      finiteModePolynomialLaplacianComponents,
      finiteModePolynomialScalarLaplacian,
      finiteModePolynomialReconstructedVelocityComponents,
      finiteModeSymmetricShearPolynomialMode,
      finiteModeProjectedNSRHS,
      finiteModeUnitForcingCoefficients,
      finiteModeIdentityCoefficientCurve,
      finiteModeAffineGradientField,
      finiteModeSymmetricShearAffinePressureMatrix,
      finiteModePolynomialVectorFieldEval_apply,
      Fin.sum_univ_three, MvPolynomial.pderiv_X, Pi.single_apply,
      MvPolynomial.eval_mul] <;>
    ring

/-- The symmetric off-diagonal shear mode is divergence-free. -/
theorem finiteModeSymmetricShearPolynomialMode_spatialDivergence
    (α : ℝ) (t : NSTime) (x : NSSpace) :
    spatialDivergence
        (fun _ : NSTime => fun y : NSSpace =>
          finiteModePolynomialVectorFieldEval
            (finiteModeSymmetricShearPolynomialMode α PUnit.unit) y) t x = 0 := by
  unfold spatialDivergence spatialFDeriv
  change
    (∑ j : Fin 3,
      (fderiv ℝ
          (finiteModePolynomialVectorFieldEval
            (finiteModeSymmetricShearPolynomialMode α PUnit.unit)) x
        (EuclideanSpace.single j (1 : ℝ))) j) = 0
  rw [(finiteModePolynomialVectorFieldEval_hasFDerivAt
    (finiteModeSymmetricShearPolynomialMode α PUnit.unit) x).fderiv]
  simp [finiteModeSymmetricShearPolynomialMode,
    finiteModePolynomialVectorFieldFDeriv_apply, Fin.sum_univ_three,
    MvPolynomial.pderiv_X]

/-- The reconstructed symmetric off-diagonal shear velocity is divergence-free
for every amplitude and time. -/
theorem finiteModeSymmetricShear_reconstructed_spatialDivergence_zero
    (α : ℝ) :
    ∀ t x,
      spatialDivergence
        (finiteModeReconstructedVelocity
          (fun i y =>
            finiteModePolynomialVectorFieldEval
              (finiteModeSymmetricShearPolynomialMode α i) y)
          finiteModeIdentityCoefficientCurve) t x = 0 := by
  intro t x
  rw [finiteModeReconstructedVelocity_spatialDivergence
    (fun i y =>
      finiteModePolynomialVectorFieldEval
        (finiteModeSymmetricShearPolynomialMode α i) y)
    finiteModeIdentityCoefficientCurve t x]
  · simp [finiteModeSymmetricShearPolynomialMode_spatialDivergence]
  · intro i
    cases i
    exact (finiteModePolynomialVectorFieldEval_hasFDerivAt
      (finiteModeSymmetricShearPolynomialMode α PUnit.unit) x).differentiableAt

/-- Positive off-diagonal instance: the symmetric trace-free shear mode admits
finite affine-quadratic pressure closure and remains divergence-free. -/
theorem finiteModeSymmetricShear_reconstructed_velocityAffineQuadraticPressure_momentum_incompressible_exists
    (ν ε α : ℝ) :
    ∃ b : ℝ → FiniteModeState FiniteModeAffineQuadraticPressureIndex,
      ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity
        (fun i y =>
          finiteModePolynomialVectorFieldEval
            (finiteModeSymmetricShearPolynomialMode α i) y)
        finiteModeIdentityCoefficientCurve ∧
        p = finiteModeReconstructedPressure finiteModeAffineQuadraticPressureMode b ∧
          finiteModeReconstructedMomentumResidualZeroOn
            (Ioo (-ε) ε) ν
              (fun i y =>
                finiteModePolynomialVectorFieldEval
                  (finiteModeSymmetricShearPolynomialMode α i) y)
              finiteModeAffineQuadraticPressureMode
              finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve b ∧
          (∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
            timeVelocityDerivative u t x +
                spatialConvection u t x +
                  spatialPressureGradient p t x =
              ν • spatialLaplacian u t x) ∧
          ∀ t x, spatialDivergence u t x = 0 := by
  rcases
    finiteModeProjectedNS_local_reconstructed_velocityAffineQuadraticPressure_momentum_of_polynomialModes_affineClosingGradient
      ν (finiteModeSymmetricShearPolynomialMode α)
      finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve ε
      (fun t _ht => finiteModeIdentityCoefficientCurve_hasDerivAt t)
      (fun _ => 0)
      (finiteModeSymmetricShearAffinePressureMatrix α)
      (fun t _ht => finiteModeSymmetricShearAffinePressureMatrix_symm α t)
      (fun t _ht =>
        finiteModeSymmetricShearPolynomialClosingPressureGradient_affine_eq ν α t) with
    ⟨b, u, p, hu, hp, hres, hmom⟩
  refine ⟨b, u, p, hu, hp, hres, hmom, ?_⟩
  intro t x
  rw [hu]
  exact finiteModeSymmetricShear_reconstructed_spatialDivergence_zero α t x

/-- A fixed linear matrix velocity mode `x ↦ A x`, represented polynomially. -/
def finiteModeLinearMatrixPolynomialMode
    (A : Fin 3 → Fin 3 → ℝ) (_ : PUnit) :
    Fin 3 → MvPolynomial (Fin 3) ℝ :=
  fun j => ∑ k : Fin 3, MvPolynomial.C (A j k) * MvPolynomial.X k

/-- Kinetic-energy density associated to a linear spatial velocity profile.
This isolates the whole-space energy obstruction for polynomial linear modes:
nonzero linear growth on `ℝ^3` is not spatially integrable. -/
def finiteModeLinearMapKineticEnergyDensity
    (L : NSSpace →L[ℝ] NSSpace) : NSSpace → ℝ :=
  fun x => ‖L x‖ ^ (2 : ℕ)

/-- Linear-map kinetic-energy densities are continuous. -/
theorem finiteModeLinearMapKineticEnergyDensity_continuous
    (L : NSSpace →L[ℝ] NSSpace) :
    Continuous (finiteModeLinearMapKineticEnergyDensity L) := by
  simpa [finiteModeLinearMapKineticEnergyDensity] using (L.continuous.norm.pow 2)

/-- A nonzero linear spatial velocity profile has nonintegrable kinetic-energy
density on `ℝ^3`.  The proof is the Haar-scaling obstruction: the density scales
like `R^2`, while three-dimensional volume scales like `R^3`. -/
theorem not_integrable_finiteModeLinearMapKineticEnergyDensity
    {L : NSSpace →L[ℝ] NSSpace}
    (hL : L ≠ 0) :
    ¬ MeasureTheory.Integrable (finiteModeLinearMapKineticEnergyDensity L) := by
  intro hInt
  have hpoint : ∃ x : NSSpace, L x ≠ 0 := by
    by_contra hnone
    apply hL
    ext x i
    by_contra hx
    have hLx : L x ≠ 0 := by
      intro hzero
      exact hx (congrArg (fun v : NSSpace => v i) hzero)
    exact hnone ⟨x, hLx⟩
  rcases hpoint with ⟨x₀, hx₀⟩
  have hnonneg : ∀ x, 0 ≤ finiteModeLinearMapKineticEnergyDensity L x := by
    intro x
    simpa [finiteModeLinearMapKineticEnergyDensity, pow_two] using
      (mul_self_nonneg ‖L x‖)
  have hx₀pos : finiteModeLinearMapKineticEnergyDensity L x₀ ≠ 0 := by
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hx₀)
  have hpos : 0 < ∫ x, finiteModeLinearMapKineticEnergyDensity L x := by
    exact MeasureTheory.integral_pos_of_integrable_nonneg_nonzero
      (x := x₀)
      (finiteModeLinearMapKineticEnergyDensity_continuous L)
      hInt hnonneg hx₀pos
  let I : ℝ := ∫ x, finiteModeLinearMapKineticEnergyDensity L x
  have hcomp :
      ∫ x, finiteModeLinearMapKineticEnergyDensity L ((2 : ℝ) • x) = (4 : ℝ) * I := by
    calc
      ∫ x, finiteModeLinearMapKineticEnergyDensity L ((2 : ℝ) • x)
          = ∫ x, (4 : ℝ) * finiteModeLinearMapKineticEnergyDensity L x := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with x
              simp [finiteModeLinearMapKineticEnergyDensity, pow_two, norm_smul]
              ring
      _ = (4 : ℝ) * I := by
            simp [I, MeasureTheory.integral_const_mul]
  have hchange :
      ∫ x, finiteModeLinearMapKineticEnergyDensity L ((2 : ℝ) • x) =
        ((2 : ℝ) ^ Module.finrank ℝ NSSpace)⁻¹ * I := by
    simpa [smul_eq_mul, I] using
      (MeasureTheory.Measure.integral_comp_smul_of_nonneg
        (μ := (MeasureTheory.volume : MeasureTheory.Measure NSSpace))
        (f := finiteModeLinearMapKineticEnergyDensity L)
        (R := (2 : ℝ)) (hR := by positivity))
  have hEq :
      (4 : ℝ) * I = ((2 : ℝ) ^ Module.finrank ℝ NSSpace)⁻¹ * I := by
    rw [← hcomp]
    exact hchange
  have hzero : I = 0 := by
    norm_num at hEq
    linarith
  have hIpos : 0 < I := by
    simpa [I] using hpos
  linarith

/-- Continuous linear map for a concrete matrix acting on `NSSpace`. -/
def finiteModeLinearMatrixCLM
    (A : Fin 3 → Fin 3 → ℝ) : NSSpace →L[ℝ] NSSpace :=
  ∑ i : Fin 3,
    (∑ j : Fin 3, A i j • (EuclideanSpace.proj j : NSSpace →L[ℝ] ℝ)).smulRight
      (EuclideanSpace.single i (1 : ℝ))

@[simp]
theorem finiteModeLinearMatrixCLM_apply
    (A : Fin 3 → Fin 3 → ℝ) (x : NSSpace) (i : Fin 3) :
    finiteModeLinearMatrixCLM A x i = ∑ j : Fin 3, A i j * x j := by
  simp [finiteModeLinearMatrixCLM, Pi.single_apply]

/-- A matrix with a nonzero entry gives a nonzero linear map on `NSSpace`. -/
theorem finiteModeLinearMatrixCLM_ne_zero_of_entry_ne
    {A : Fin 3 → Fin 3 → ℝ} {i j : Fin 3}
    (hA : A i j ≠ 0) :
    finiteModeLinearMatrixCLM A ≠ 0 := by
  intro hzero
  have hcomp :=
    congrArg
      (fun L : NSSpace →L[ℝ] NSSpace => L (EuclideanSpace.single j (1 : ℝ)) i)
      hzero
  simp [finiteModeLinearMatrixCLM, Pi.single_apply] at hcomp
  exact hA hcomp

/-- Matrix square coefficients for the linear matrix mode. -/
def finiteModeMatrixSquare (A : Fin 3 → Fin 3 → ℝ) :
    Fin 3 → Fin 3 → ℝ :=
  fun i j => ∑ k : Fin 3, A i k * A k j

/-- The affine pressure matrix closing `u(t,x)=t A x`. -/
def finiteModeLinearMatrixAffinePressureMatrix
    (A : Fin 3 → Fin 3 → ℝ) (t : NSTime) : Fin 3 → Fin 3 → ℝ :=
  fun i j => -(A i j + t * t * finiteModeMatrixSquare A i j)

/-- The square of a symmetric matrix is symmetric. -/
theorem finiteModeMatrixSquare_symm
    (A : Fin 3 → Fin 3 → ℝ) (hA : ∀ i j, A i j = A j i) :
    ∀ i j, finiteModeMatrixSquare A i j = finiteModeMatrixSquare A j i := by
  intro i j
  unfold finiteModeMatrixSquare
  apply Finset.sum_congr rfl
  intro k _hk
  rw [hA i k, hA k j]
  ring

/-- The linear-matrix affine pressure matrix is symmetric when `A` is
symmetric. -/
theorem finiteModeLinearMatrixAffinePressureMatrix_symm
    (A : Fin 3 → Fin 3 → ℝ) (hA : ∀ i j, A i j = A j i) (t : NSTime) :
    ∀ i j, finiteModeLinearMatrixAffinePressureMatrix A t i j =
      finiteModeLinearMatrixAffinePressureMatrix A t j i := by
  intro i j
  simp [finiteModeLinearMatrixAffinePressureMatrix, hA i j,
    finiteModeMatrixSquare_symm A hA i j]

/-- Component formula for the matrix-linear reconstruction:
`u_j(t,x)=t Σ_k A_{jk} x_k`. -/
theorem finiteModeLinearMatrix_reconstructedVelocity_apply
    (A : Fin 3 → Fin 3 → ℝ) (t : NSTime) (x : NSSpace) (j : Fin 3) :
    finiteModeReconstructedVelocity
        (fun i y =>
          finiteModePolynomialVectorFieldEval
            (finiteModeLinearMatrixPolynomialMode A i) y)
        finiteModeIdentityCoefficientCurve t x j =
      t * ∑ k : Fin 3, A j k * x k := by
  fin_cases j <;>
    simp [finiteModeReconstructedVelocity, finiteModeReconstructionCLM,
      finiteModeIdentityCoefficientCurve, finiteModeLinearMatrixPolynomialMode,
      finiteModePolynomialVectorFieldEval_apply, MvPolynomial.eval_mul,
      Fin.sum_univ_three]

/-- The computed closing pressure gradient for `u(t,x)=t A x` is the affine
field `-(A + t^2 A^2)x`. -/
theorem finiteModeLinearMatrixPolynomialClosingPressureGradient_affine_eq
    (ν : ℝ) (A : Fin 3 → Fin 3 → ℝ) (t : NSTime) :
    finiteModePolynomialVectorFieldEval
        (finiteModePolynomialClosingPressureGradientComponents
          ν (finiteModeLinearMatrixPolynomialMode A)
            finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve
            (fun s => finiteModePolynomialLaplacianComponents
              (finiteModePolynomialReconstructedVelocityComponents
                (finiteModeLinearMatrixPolynomialMode A)
                finiteModeIdentityCoefficientCurve s))
          t) =
      finiteModeAffineGradientField 0
        (finiteModeLinearMatrixAffinePressureMatrix A t) := by
  funext x
  ext j
  fin_cases j <;>
    simp [finiteModePolynomialClosingPressureGradientComponents,
      finiteModePolynomialNonPressureDefectComponents,
      finiteModePolynomialReconstructedAccelerationComponents,
      finiteModePolynomialConvectionComponents,
      finiteModePolynomialLaplacianComponents,
      finiteModePolynomialScalarLaplacian,
      finiteModePolynomialReconstructedVelocityComponents,
      finiteModeLinearMatrixPolynomialMode,
      finiteModeProjectedNSRHS,
      finiteModeUnitForcingCoefficients,
      finiteModeIdentityCoefficientCurve,
      finiteModeAffineGradientField,
      finiteModeLinearMatrixAffinePressureMatrix,
      finiteModeMatrixSquare,
      finiteModePolynomialVectorFieldEval_apply,
      Fin.sum_univ_three, MvPolynomial.pderiv_X, Pi.single_apply,
      MvPolynomial.eval_mul] <;>
    ring_nf

/-- The divergence of the matrix-linear polynomial mode is the trace of `A`. -/
theorem finiteModeLinearMatrixPolynomialMode_spatialDivergence
    (A : Fin 3 → Fin 3 → ℝ) (t : NSTime) (x : NSSpace) :
    spatialDivergence
        (fun _ : NSTime => fun y : NSSpace =>
          finiteModePolynomialVectorFieldEval
            (finiteModeLinearMatrixPolynomialMode A PUnit.unit) y) t x =
      ∑ i : Fin 3, A i i := by
  unfold spatialDivergence spatialFDeriv
  change
    (∑ j : Fin 3,
      (fderiv ℝ
          (finiteModePolynomialVectorFieldEval
            (finiteModeLinearMatrixPolynomialMode A PUnit.unit)) x
        (EuclideanSpace.single j (1 : ℝ))) j) =
      ∑ i : Fin 3, A i i
  rw [(finiteModePolynomialVectorFieldEval_hasFDerivAt
    (finiteModeLinearMatrixPolynomialMode A PUnit.unit) x).fderiv]
  simp [finiteModeLinearMatrixPolynomialMode,
    finiteModePolynomialVectorFieldFDeriv_apply, Fin.sum_univ_three,
    MvPolynomial.pderiv_X, Pi.single_apply]

/-- The divergence of `u(t,x)=t A x` is `t * trace A`. -/
theorem finiteModeLinearMatrix_spatialDivergence_eq
    (A : Fin 3 → Fin 3 → ℝ) (t : NSTime) (x : NSSpace) :
    spatialDivergence
        (finiteModeReconstructedVelocity
          (fun i y =>
            finiteModePolynomialVectorFieldEval
              (finiteModeLinearMatrixPolynomialMode A i) y)
          finiteModeIdentityCoefficientCurve) t x =
      t * ∑ i : Fin 3, A i i := by
  rw [finiteModeReconstructedVelocity_spatialDivergence
    (fun i y =>
      finiteModePolynomialVectorFieldEval
        (finiteModeLinearMatrixPolynomialMode A i) y)
    finiteModeIdentityCoefficientCurve t x]
  · rw [Fintype.sum_eq_single PUnit.unit]
    rw [finiteModeLinearMatrixPolynomialMode_spatialDivergence]
    simp [finiteModeIdentityCoefficientCurve]
    intro i hi
    cases i
    exact (hi rfl).elim
  · intro i
    cases i
    exact (finiteModePolynomialVectorFieldEval_hasFDerivAt
      (finiteModeLinearMatrixPolynomialMode A PUnit.unit) x).differentiableAt

/-- Trace-free matrix-linear velocities are divergence-free. -/
theorem finiteModeLinearMatrix_spatialDivergence_zero_of_trace
    (A : Fin 3 → Fin 3 → ℝ) (htrace : ∑ i : Fin 3, A i i = 0) :
    ∀ t x,
      spatialDivergence
        (finiteModeReconstructedVelocity
          (fun i y =>
            finiteModePolynomialVectorFieldEval
              (finiteModeLinearMatrixPolynomialMode A i) y)
          finiteModeIdentityCoefficientCurve) t x = 0 := by
  intro t x
  rw [finiteModeLinearMatrix_spatialDivergence_eq A t x, htrace, mul_zero]

/-- Matrix-level closure under the exact affine-pressure condition: if the
computed affine closing matrix is symmetric on the local interval, and the
velocity matrix is trace-free, then `u(t,x)=t A x` admits finite
affine-quadratic pressure closure and is incompressible. -/
theorem finiteModeLinearMatrix_traceFreeAffineSymmetric_reconstructed_velocityAffineQuadraticPressure_momentum_incompressible_exists
    (ν ε : ℝ) (A : Fin 3 → Fin 3 → ℝ)
    (hclosure : ∀ t ∈ Ioo (-ε) ε, ∀ i j,
      finiteModeLinearMatrixAffinePressureMatrix A t i j =
        finiteModeLinearMatrixAffinePressureMatrix A t j i)
    (htrace : ∑ i : Fin 3, A i i = 0) :
    ∃ b : ℝ → FiniteModeState FiniteModeAffineQuadraticPressureIndex,
      ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity
        (fun i y =>
          finiteModePolynomialVectorFieldEval
            (finiteModeLinearMatrixPolynomialMode A i) y)
        finiteModeIdentityCoefficientCurve ∧
        p = finiteModeReconstructedPressure finiteModeAffineQuadraticPressureMode b ∧
          finiteModeReconstructedMomentumResidualZeroOn
            (Ioo (-ε) ε) ν
              (fun i y =>
                finiteModePolynomialVectorFieldEval
                  (finiteModeLinearMatrixPolynomialMode A i) y)
              finiteModeAffineQuadraticPressureMode
              finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve b ∧
          (∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
            timeVelocityDerivative u t x +
                spatialConvection u t x +
                  spatialPressureGradient p t x =
              ν • spatialLaplacian u t x) ∧
          ∀ t x, spatialDivergence u t x = 0 := by
  rcases
    finiteModeProjectedNS_local_reconstructed_velocityAffineQuadraticPressure_momentum_of_polynomialModes_affineClosingGradient
      ν (finiteModeLinearMatrixPolynomialMode A)
      finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve ε
      (fun t _ht => finiteModeIdentityCoefficientCurve_hasDerivAt t)
      (fun _ => 0)
      (finiteModeLinearMatrixAffinePressureMatrix A)
      hclosure
      (fun t _ht =>
        finiteModeLinearMatrixPolynomialClosingPressureGradient_affine_eq ν A t) with
    ⟨b, u, p, hu, hp, hres, hmom⟩
  refine ⟨b, u, p, hu, hp, hres, hmom, ?_⟩
  intro t x
  rw [hu]
  exact finiteModeLinearMatrix_spatialDivergence_zero_of_trace A htrace t x

/-- Matrix-level positive construction: every symmetric trace-free matrix
linear field `u(t,x)=t A x` admits finite affine-quadratic pressure closure and
is incompressible. -/
theorem finiteModeLinearMatrix_traceFreeSymmetric_reconstructed_velocityAffineQuadraticPressure_momentum_incompressible_exists
    (ν ε : ℝ) (A : Fin 3 → Fin 3 → ℝ)
    (hA : ∀ i j, A i j = A j i) (htrace : ∑ i : Fin 3, A i i = 0) :
    ∃ b : ℝ → FiniteModeState FiniteModeAffineQuadraticPressureIndex,
      ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity
        (fun i y =>
          finiteModePolynomialVectorFieldEval
            (finiteModeLinearMatrixPolynomialMode A i) y)
        finiteModeIdentityCoefficientCurve ∧
        p = finiteModeReconstructedPressure finiteModeAffineQuadraticPressureMode b ∧
          finiteModeReconstructedMomentumResidualZeroOn
            (Ioo (-ε) ε) ν
              (fun i y =>
                finiteModePolynomialVectorFieldEval
                  (finiteModeLinearMatrixPolynomialMode A i) y)
              finiteModeAffineQuadraticPressureMode
              finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve b ∧
          (∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
            timeVelocityDerivative u t x +
                spatialConvection u t x +
                  spatialPressureGradient p t x =
              ν • spatialLaplacian u t x) ∧
          ∀ t x, spatialDivergence u t x = 0 := by
  exact
    finiteModeLinearMatrix_traceFreeAffineSymmetric_reconstructed_velocityAffineQuadraticPressure_momentum_incompressible_exists
      ν ε A (fun t _ht => finiteModeLinearMatrixAffinePressureMatrix_symm A hA t)
      htrace

/-- The time-dependent matrix-linear velocity `u(t,x)=g(t) A x`, represented
using the same one-mode polynomial reconstruction surface. -/
def finiteModeLinearMatrixTimeVelocity
    (A : Fin 3 → Fin 3 → ℝ) (g : NSTime → ℝ) : NSVelocityField :=
  finiteModeReconstructedVelocity
    (fun (i : PUnit.{1}) y =>
      finiteModePolynomialVectorFieldEval
        (finiteModeLinearMatrixPolynomialMode A i) y)
    (finiteModeScalarAmplitudeCoefficientCurve g)

/-- Component formula for the time-dependent matrix-linear velocity. -/
theorem finiteModeLinearMatrixTimeVelocity_apply
    (A : Fin 3 → Fin 3 → ℝ) (g : NSTime → ℝ)
    (t : NSTime) (x : NSSpace) (j : Fin 3) :
    finiteModeLinearMatrixTimeVelocity A g t x j =
      g t * ∑ k : Fin 3, A j k * x k := by
  unfold finiteModeLinearMatrixTimeVelocity
  fin_cases j <;>
    simp [finiteModeReconstructedVelocity, finiteModeReconstructionCLM,
      finiteModeScalarAmplitudeCoefficientCurve,
      finiteModeLinearMatrixPolynomialMode,
      finiteModePolynomialVectorFieldEval_apply, MvPolynomial.eval_mul,
      Fin.sum_univ_three]

/-- Each time slice of `u(t,x)=g(t)A x` has the kinetic-energy density of the
linear map `(g(t))A`. -/
theorem kineticEnergyDensity_finiteModeLinearMatrixTimeVelocity
    (A : Fin 3 → Fin 3 → ℝ) (g : NSTime → ℝ) (t : NSTime) :
    kineticEnergyDensity (finiteModeLinearMatrixTimeVelocity A g) t =
      finiteModeLinearMapKineticEnergyDensity ((g t) • finiteModeLinearMatrixCLM A) := by
  funext x
  have hvec :
      finiteModeLinearMatrixTimeVelocity A g t x =
        ((g t) • finiteModeLinearMatrixCLM A) x := by
    ext j
    rw [finiteModeLinearMatrixTimeVelocity_apply]
    simp [finiteModeLinearMatrixCLM_apply]
  simp [kineticEnergyDensity, finiteModeLinearMapKineticEnergyDensity, hvec]

/-- If the matrix mode is nonzero and the scalar amplitude is active at a time
slice, the corresponding kinetic-energy density is not integrable on `ℝ^3`. -/
theorem not_integrable_kineticEnergyDensity_finiteModeLinearMatrixTimeVelocity
    {A : Fin 3 → Fin 3 → ℝ} {g : NSTime → ℝ} {t : NSTime}
    (hA : ∃ i j : Fin 3, A i j ≠ 0)
    (hg : g t ≠ 0) :
    ¬ MeasureTheory.Integrable
      (kineticEnergyDensity (finiteModeLinearMatrixTimeVelocity A g) t) := by
  intro hInt
  rw [kineticEnergyDensity_finiteModeLinearMatrixTimeVelocity A g t] at hInt
  rcases hA with ⟨i, j, hij⟩
  have hL : finiteModeLinearMatrixCLM A ≠ 0 :=
    finiteModeLinearMatrixCLM_ne_zero_of_entry_ne hij
  have hsmul : (g t) • finiteModeLinearMatrixCLM A ≠ 0 := by
    intro hzero
    have hmap : finiteModeLinearMatrixCLM A = 0 := by
      ext x j
      have hcomp :=
        congrArg (fun L : NSSpace →L[ℝ] NSSpace => L x j) hzero
      simp at hcomp
      rcases hcomp with hgt | hcoord
      · exact (hg hgt).elim
      · simpa using hcoord
    exact hL hmap
  exact not_integrable_finiteModeLinearMapKineticEnergyDensity hsmul hInt

/-- A genuinely active matrix-linear time-dependent velocity cannot satisfy the
global bounded-energy predicate. -/
theorem not_boundedKineticEnergy_finiteModeLinearMatrixTimeVelocity
    {A : Fin 3 → Fin 3 → ℝ} {g : NSTime → ℝ}
    (hA : ∃ i j : Fin 3, A i j ≠ 0)
    (hg : ∃ t : NSTime, g t ≠ 0) :
    ¬ boundedKineticEnergy (finiteModeLinearMatrixTimeVelocity A g) := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  rcases hg with ⟨t, hgt⟩
  exact not_integrable_kineticEnergyDensity_finiteModeLinearMatrixTimeVelocity
    hA hgt (hbound t).1

/-- If `g(0) ≠ 0`, the initial datum associated to a nonzero matrix-linear
finite-mode velocity is not finite-energy admissible on `ℝ^3`. -/
theorem not_finiteInitialKineticEnergy_finiteModeLinearMatrixTimeVelocity_initial
    {A : Fin 3 → Fin 3 → ℝ} {g : NSTime → ℝ}
    (hA : ∃ i j : Fin 3, A i j ≠ 0)
    (hg0 : g 0 ≠ 0) :
    ¬ finiteInitialKineticEnergy (fun x : NSSpace => finiteModeLinearMatrixTimeVelocity A g 0 x) := by
  intro hE
  have hInt :
      MeasureTheory.Integrable
        (kineticEnergyDensity (finiteModeLinearMatrixTimeVelocity A g) 0) := by
    simpa [finiteInitialKineticEnergy, initialKineticEnergyDensity, kineticEnergyDensity] using hE
  exact not_integrable_kineticEnergyDensity_finiteModeLinearMatrixTimeVelocity hA hg0 hInt

/-- The pressure matrix closing the time-dependent matrix-linear velocity
`u(t,x)=g(t) A x` when `g'(t)=gdot(t)`. -/
def finiteModeLinearMatrixTimePressureMatrix
    (A : Fin 3 → Fin 3 → ℝ) (g gdot : NSTime → ℝ)
    (t : NSTime) : Fin 3 → Fin 3 → ℝ :=
  fun i j => -(gdot t * A i j + g t * g t * finiteModeMatrixSquare A i j)

/-- Coefficients for the affine-quadratic pressure closing the time-dependent
matrix-linear velocity. -/
def finiteModeLinearMatrixTimePressureCoefficients
    (A : Fin 3 → Fin 3 → ℝ) (g gdot : NSTime → ℝ) :
    NSTime → FiniteModeState FiniteModeAffineQuadraticPressureIndex :=
  fun t =>
    finiteModeAffineQuadraticPressureCoefficientsAt
      (0 : NSSpace) (finiteModeLinearMatrixTimePressureMatrix A g gdot t)

/-- The affine-quadratic pressure field for the time-dependent matrix-linear
velocity. -/
def finiteModeLinearMatrixTimePressure
    (A : Fin 3 → Fin 3 → ℝ) (g gdot : NSTime → ℝ) : NSPressureField :=
  finiteModeReconstructedPressure finiteModeAffineQuadraticPressureMode
    (finiteModeLinearMatrixTimePressureCoefficients A g gdot)

/-- If `A` is symmetric, the time-dependent closing pressure matrix is
symmetric at every time. -/
theorem finiteModeLinearMatrixTimePressureMatrix_symm
    (A : Fin 3 → Fin 3 → ℝ) (g gdot : NSTime → ℝ)
    (hA : ∀ i j, A i j = A j i) (t : NSTime) :
    ∀ i j, finiteModeLinearMatrixTimePressureMatrix A g gdot t i j =
      finiteModeLinearMatrixTimePressureMatrix A g gdot t j i := by
  intro i j
  simp [finiteModeLinearMatrixTimePressureMatrix, hA i j,
    finiteModeMatrixSquare_symm A hA i j]

/-- The time derivative of `u(t,x)=g(t) A x` is `gdot(t) A x`. -/
theorem finiteModeLinearMatrix_timeDependent_timeVelocityDerivative_eq
    (A : Fin 3 → Fin 3 → ℝ) (g gdot : NSTime → ℝ)
    {t : NSTime} (hg : HasDerivAt g (gdot t) t) (x : NSSpace) :
    timeVelocityDerivative (finiteModeLinearMatrixTimeVelocity A g) t x =
      fun j => gdot t * ∑ k : Fin 3, A j k * x k := by
  unfold finiteModeLinearMatrixTimeVelocity
  rw [finiteModeReconstructedVelocity_timeDerivative_at
    (fun (i : PUnit.{1}) y =>
      finiteModePolynomialVectorFieldEval
        (finiteModeLinearMatrixPolynomialMode A i) y)
    (finiteModeScalarForcingCoefficients (gdot t))
    (finiteModeScalarAmplitudeCoefficientCurve g) t
    (finiteModeScalarAmplitudeCoefficientCurve_hasDerivAt g gdot hg) x]
  ext j
  fin_cases j <;>
    simp [finiteModeReconstructedAcceleration, finiteModeReconstructedVelocity,
      finiteModeReconstructionCLM, finiteModeProjectedNSRHS,
      finiteModeScalarForcingCoefficients,
      finiteModeScalarAmplitudeCoefficientCurve,
      finiteModeLinearMatrixPolynomialMode,
      finiteModePolynomialVectorFieldEval_apply, MvPolynomial.eval_mul,
      Fin.sum_univ_three]

/-- The convection term for `u(t,x)=g(t) A x` is `g(t)^2 A^2 x`. -/
theorem finiteModeLinearMatrix_timeDependent_spatialConvection_eq
    (A : Fin 3 → Fin 3 → ℝ) (g : NSTime → ℝ)
    (t : NSTime) (x : NSSpace) :
    spatialConvection (finiteModeLinearMatrixTimeVelocity A g) t x =
      fun j => (g t * g t) * ∑ k : Fin 3,
        finiteModeMatrixSquare A j k * x k := by
  unfold finiteModeLinearMatrixTimeVelocity
  rw [finiteModePolynomialReconstructedVelocity_spatialConvection
    (finiteModeLinearMatrixPolynomialMode A)
    (finiteModeScalarAmplitudeCoefficientCurve g) t x]
  ext j
  fin_cases j <;>
    simp [finiteModePolynomialConvectionComponents,
      finiteModePolynomialReconstructedVelocityComponents,
      finiteModeLinearMatrixPolynomialMode,
      finiteModeScalarAmplitudeCoefficientCurve,
      finiteModeMatrixSquare,
      finiteModePolynomialVectorFieldEval_apply, Fin.sum_univ_three,
      MvPolynomial.pderiv_X, Pi.single_apply, MvPolynomial.eval_mul] <;>
    ring_nf

/-- The matrix-linear time-dependent velocity has zero spatial Laplacian. -/
theorem finiteModeLinearMatrix_timeDependent_spatialLaplacian_zero
    (A : Fin 3 → Fin 3 → ℝ) (g : NSTime → ℝ)
    (t : NSTime) (x : NSSpace) :
    spatialLaplacian (finiteModeLinearMatrixTimeVelocity A g) t x = 0 := by
  unfold finiteModeLinearMatrixTimeVelocity
  rw [finiteModePolynomialReconstructedVelocity_spatialLaplacian
    (finiteModeLinearMatrixPolynomialMode A)
    (finiteModeScalarAmplitudeCoefficientCurve g) t x]
  ext j
  fin_cases j <;>
    simp [finiteModePolynomialLaplacianComponents,
      finiteModePolynomialScalarLaplacian,
      finiteModePolynomialReconstructedVelocityComponents,
      finiteModeLinearMatrixPolynomialMode,
      finiteModeScalarAmplitudeCoefficientCurve,
      finiteModePolynomialVectorFieldEval_apply, Fin.sum_univ_three,
      MvPolynomial.pderiv_X, Pi.single_apply]

/-- The divergence of `u(t,x)=g(t) A x` is `g(t) trace(A)`. -/
theorem finiteModeLinearMatrix_timeDependent_spatialDivergence_eq
    (A : Fin 3 → Fin 3 → ℝ) (g : NSTime → ℝ)
    (t : NSTime) (x : NSSpace) :
    spatialDivergence (finiteModeLinearMatrixTimeVelocity A g) t x =
      g t * ∑ i : Fin 3, A i i := by
  unfold finiteModeLinearMatrixTimeVelocity
  rw [finiteModeReconstructedVelocity_spatialDivergence
    (fun (i : PUnit.{1}) y =>
      finiteModePolynomialVectorFieldEval
        (finiteModeLinearMatrixPolynomialMode A i) y)
    (finiteModeScalarAmplitudeCoefficientCurve g) t x]
  · rw [Fintype.sum_eq_single PUnit.unit]
    rw [finiteModeLinearMatrixPolynomialMode_spatialDivergence]
    simp [finiteModeScalarAmplitudeCoefficientCurve]
    intro i hi
    cases i
    exact (hi rfl).elim
  · intro i
    cases i
    exact (finiteModePolynomialVectorFieldEval_hasFDerivAt
      (finiteModeLinearMatrixPolynomialMode A PUnit.unit) x).differentiableAt

/-- Trace-free time-dependent matrix-linear velocities are divergence-free. -/
theorem finiteModeLinearMatrix_timeDependent_spatialDivergence_zero_of_trace
    (A : Fin 3 → Fin 3 → ℝ) (g : NSTime → ℝ)
    (htrace : ∑ i : Fin 3, A i i = 0) :
    ∀ t x, spatialDivergence (finiteModeLinearMatrixTimeVelocity A g) t x = 0 := by
  intro t x
  rw [finiteModeLinearMatrix_timeDependent_spatialDivergence_eq A g t x,
    htrace, mul_zero]

/-- The explicit affine-quadratic pressure has gradient
`-(gdot(t) A + g(t)^2 A^2)x`. -/
theorem finiteModeLinearMatrix_timeDependent_pressureGradient_eq
    (A : Fin 3 → Fin 3 → ℝ) (g gdot : NSTime → ℝ)
    (hA : ∀ i j, A i j = A j i)
    (t : NSTime) (x : NSSpace) :
    spatialPressureGradient (finiteModeLinearMatrixTimePressure A g gdot) t x =
      finiteModeAffineGradientField (0 : NSSpace)
        (finiteModeLinearMatrixTimePressureMatrix A g gdot t) x := by
  unfold finiteModeLinearMatrixTimePressure
  rw [finiteModeReconstructedPressure_spatialPressureGradient
    finiteModeAffineQuadraticPressureMode
    (finiteModeLinearMatrixTimePressureCoefficients A g gdot) t x
    (fun k => finiteModeAffineQuadraticPressureMode_differentiableAt k x)]
  change
    finiteModePressureGradientSynthesis finiteModeAffineQuadraticPressureMode
        (finiteModeAffineQuadraticPressureCoefficientsAt (0 : NSSpace)
          (finiteModeLinearMatrixTimePressureMatrix A g gdot t)) x =
      finiteModeAffineGradientField (0 : NSSpace)
        (finiteModeLinearMatrixTimePressureMatrix A g gdot t) x
  rw [finiteModeAffineQuadraticPressureGradientSynthesis
    (0 : NSSpace) (finiteModeLinearMatrixTimePressureMatrix A g gdot t)
    (finiteModeLinearMatrixTimePressureMatrix_symm A g gdot hA t) x]

/-- Smooth scalar amplitudes give smooth time-dependent matrix-linear
velocities. -/
theorem finiteModeLinearMatrix_timeDependent_smoothSpaceTimeVelocity
    (A : Fin 3 → Fin 3 → ℝ) (g : NSTime → ℝ)
    (hg : ContDiff ℝ ∞ g) :
    smoothSpaceTimeVelocity (finiteModeLinearMatrixTimeVelocity A g) := by
  unfold finiteModeLinearMatrixTimeVelocity
  exact
    finiteModeReconstructedVelocity_smoothSpaceTime
      (fun (i : PUnit.{1}) y =>
        finiteModePolynomialVectorFieldEval
          (finiteModeLinearMatrixPolynomialMode A i) y)
      (finiteModeScalarAmplitudeCoefficientCurve g)
      (fun i => by
        cases i
        simpa [finiteModeScalarAmplitudeCoefficientCurve] using hg)
      (fun i => by
        cases i
        exact finiteModePolynomialVectorFieldEval_contDiff_top
          (finiteModeLinearMatrixPolynomialMode A (PUnit.unit : PUnit.{1})))

/-- The time-dependent pressure coefficients are smooth when `g` and `gdot`
are smooth. -/
theorem finiteModeLinearMatrixTimePressureCoefficients_contDiff
    (A : Fin 3 → Fin 3 → ℝ) (g gdot : NSTime → ℝ)
    (hg : ContDiff ℝ ∞ g) (hgdot : ContDiff ℝ ∞ gdot) :
    ∀ k, ContDiff ℝ ∞
      (fun t : NSTime => finiteModeLinearMatrixTimePressureCoefficients A g gdot t k) := by
  intro k
  rcases k with j | k
  · simpa [finiteModeLinearMatrixTimePressureCoefficients,
      finiteModeAffineQuadraticPressureCoefficientsAt] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ)))
  · rcases k with j | r
    · have h1 : ContDiff ℝ ∞ (fun t : NSTime => gdot t * A j j) :=
        hgdot.mul contDiff_const
      have h2a : ContDiff ℝ ∞ (fun t : NSTime => g t * g t) :=
        hg.mul hg
      have h2 : ContDiff ℝ ∞
          (fun t : NSTime => g t * g t * finiteModeMatrixSquare A j j) :=
        h2a.mul contDiff_const
      simpa [finiteModeLinearMatrixTimePressureCoefficients,
        finiteModeAffineQuadraticPressureCoefficientsAt,
        finiteModeLinearMatrixTimePressureMatrix] using (h1.add h2).neg
    · let i₀ : Fin 3 := (finiteModeOffDiagonalPair r).1
      let i₁ : Fin 3 := (finiteModeOffDiagonalPair r).2
      have h1 : ContDiff ℝ ∞ (fun t : NSTime => gdot t * A i₀ i₁) :=
        hgdot.mul contDiff_const
      have h2a : ContDiff ℝ ∞ (fun t : NSTime => g t * g t) :=
        hg.mul hg
      have h2 : ContDiff ℝ ∞
          (fun t : NSTime => g t * g t * finiteModeMatrixSquare A i₀ i₁) :=
        h2a.mul contDiff_const
      simpa [finiteModeLinearMatrixTimePressureCoefficients,
        finiteModeAffineQuadraticPressureCoefficientsAt,
        finiteModeLinearMatrixTimePressureMatrix, i₀, i₁] using (h1.add h2).neg

/-- Smooth amplitudes and derivative data give a smooth explicit
affine-quadratic pressure for the time-dependent matrix-linear velocity. -/
theorem finiteModeLinearMatrix_timeDependent_smoothSpaceTimePressure
    (A : Fin 3 → Fin 3 → ℝ) (g gdot : NSTime → ℝ)
    (hg : ContDiff ℝ ∞ g) (hgdot : ContDiff ℝ ∞ gdot) :
    smoothSpaceTimePressure (finiteModeLinearMatrixTimePressure A g gdot) := by
  unfold finiteModeLinearMatrixTimePressure
  exact
    finiteModeReconstructedPressure_smoothSpaceTime
      finiteModeAffineQuadraticPressureMode
      (finiteModeLinearMatrixTimePressureCoefficients A g gdot)
      (finiteModeLinearMatrixTimePressureCoefficients_contDiff A g gdot hg hgdot)
      finiteModeAffineQuadraticPressureMode_contDiff

/-- Direct pointwise momentum identity for the global-in-time
time-dependent matrix-linear reconstruction.  The construction is global in
time, but it is only a polynomial finite-mode PDE identity; it does not assert
finite-energy Clay admissibility. -/
theorem finiteModeLinearMatrix_timeDependent_pointwise_momentum_eq
    (ν : ℝ) (A : Fin 3 → Fin 3 → ℝ) (g gdot : NSTime → ℝ)
    (hA : ∀ i j, A i j = A j i)
    (hg : ∀ t : NSTime, HasDerivAt g (gdot t) t) :
    ∀ t x,
      timeVelocityDerivative (finiteModeLinearMatrixTimeVelocity A g) t x +
          spatialConvection (finiteModeLinearMatrixTimeVelocity A g) t x +
            spatialPressureGradient (finiteModeLinearMatrixTimePressure A g gdot) t x =
        ν • spatialLaplacian (finiteModeLinearMatrixTimeVelocity A g) t x := by
  intro t x
  ext j
  have htime := congrFun
    (finiteModeLinearMatrix_timeDependent_timeVelocityDerivative_eq A g gdot
      (hg t) x) j
  have hconv := congrFun
    (finiteModeLinearMatrix_timeDependent_spatialConvection_eq A g t x) j
  have hpress :
      (spatialPressureGradient
        (finiteModeLinearMatrixTimePressure A g gdot) t x).ofLp j =
        (finiteModeAffineGradientField (0 : NSSpace)
          (finiteModeLinearMatrixTimePressureMatrix A g gdot t) x).ofLp j := by
    exact congrArg (fun v : NSSpace => v.ofLp j)
      (finiteModeLinearMatrix_timeDependent_pressureGradient_eq A g gdot hA t x)
  have hlap :
      (spatialLaplacian (finiteModeLinearMatrixTimeVelocity A g) t x).ofLp j =
        (0 : NSSpace).ofLp j := by
    exact congrArg (fun v : NSSpace => v.ofLp j)
      (finiteModeLinearMatrix_timeDependent_spatialLaplacian_zero A g t x)
  simp only [PiLp.add_apply, PiLp.smul_apply]
  rw [htime, hconv, hpress, hlap]
  fin_cases j <;>
    simp [finiteModeAffineGradientField,
      finiteModeLinearMatrixTimePressureMatrix,
      finiteModeMatrixSquare, Fin.sum_univ_three] <;>
    ring_nf

/-- Global-in-time time-dependent positive construction: for any symmetric
trace-free matrix `A` and differentiable scalar amplitude `g`, the field
`u(t,x)=g(t) A x` admits an explicit finite affine-quadratic pressure making the
pointwise momentum equation and incompressibility hold for all times. -/
theorem finiteModeLinearMatrix_timeDependent_global_momentum_incompressible_exists
    (ν : ℝ) (A : Fin 3 → Fin 3 → ℝ) (g gdot : NSTime → ℝ)
    (hA : ∀ i j, A i j = A j i)
    (htrace : ∑ i : Fin 3, A i i = 0)
    (hg : ∀ t : NSTime, HasDerivAt g (gdot t) t) :
    ∃ b : ℝ → FiniteModeState FiniteModeAffineQuadraticPressureIndex,
      ∃ u : NSVelocityField, ∃ p : NSPressureField,
      b = finiteModeLinearMatrixTimePressureCoefficients A g gdot ∧
        u = finiteModeLinearMatrixTimeVelocity A g ∧
          p = finiteModeReconstructedPressure finiteModeAffineQuadraticPressureMode b ∧
            (∀ t x,
              timeVelocityDerivative u t x +
                  spatialConvection u t x +
                    spatialPressureGradient p t x =
                ν • spatialLaplacian u t x) ∧
            ∀ t x, spatialDivergence u t x = 0 := by
  refine
    ⟨finiteModeLinearMatrixTimePressureCoefficients A g gdot,
      finiteModeLinearMatrixTimeVelocity A g,
      finiteModeLinearMatrixTimePressure A g gdot,
      rfl, rfl, rfl, ?_, ?_⟩
  · simpa [finiteModeLinearMatrixTimePressure] using
      finiteModeLinearMatrix_timeDependent_pointwise_momentum_eq
        ν A g gdot hA hg
  · exact finiteModeLinearMatrix_timeDependent_spatialDivergence_zero_of_trace
      A g htrace

/-- Smooth global-in-time finite-mode regularity package for the
time-dependent matrix-linear construction.  It gives smooth velocity and
pressure together with the pointwise PDE identities; it still makes no
bounded-energy assertion, since nonzero linear fields on `ℝ^3` are not
finite-energy. -/
theorem finiteModeLinearMatrix_timeDependent_global_smooth_momentum_incompressible_exists
    (ν : ℝ) (A : Fin 3 → Fin 3 → ℝ) (g gdot : NSTime → ℝ)
    (hA : ∀ i j, A i j = A j i)
    (htrace : ∑ i : Fin 3, A i i = 0)
    (hg : ContDiff ℝ ∞ g) (hgdot : ContDiff ℝ ∞ gdot)
    (hderiv : ∀ t : NSTime, HasDerivAt g (gdot t) t) :
    ∃ b : ℝ → FiniteModeState FiniteModeAffineQuadraticPressureIndex,
      ∃ u : NSVelocityField, ∃ p : NSPressureField,
      b = finiteModeLinearMatrixTimePressureCoefficients A g gdot ∧
        u = finiteModeLinearMatrixTimeVelocity A g ∧
          p = finiteModeReconstructedPressure finiteModeAffineQuadraticPressureMode b ∧
            smoothSpaceTimeVelocity u ∧
              smoothSpaceTimePressure p ∧
                (∀ t x,
                  timeVelocityDerivative u t x +
                      spatialConvection u t x +
                        spatialPressureGradient p t x =
                    ν • spatialLaplacian u t x) ∧
                ∀ t x, spatialDivergence u t x = 0 := by
  refine
    ⟨finiteModeLinearMatrixTimePressureCoefficients A g gdot,
      finiteModeLinearMatrixTimeVelocity A g,
      finiteModeLinearMatrixTimePressure A g gdot,
      rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · exact finiteModeLinearMatrix_timeDependent_smoothSpaceTimeVelocity A g hg
  · simpa [finiteModeLinearMatrixTimePressure] using
      finiteModeLinearMatrix_timeDependent_smoothSpaceTimePressure
        A g gdot hg hgdot
  · simpa [finiteModeLinearMatrixTimePressure] using
      finiteModeLinearMatrix_timeDependent_pointwise_momentum_eq
        ν A g gdot hA hderiv
  · exact finiteModeLinearMatrix_timeDependent_spatialDivergence_zero_of_trace
      A g htrace

/-- The same smooth global-in-time matrix-linear construction, paired with the
honest whole-space obstruction: if the matrix has a nonzero entry and the
amplitude is nonzero at some time, the constructed velocity cannot satisfy the
concrete bounded kinetic-energy predicate. -/
theorem finiteModeLinearMatrix_timeDependent_global_smooth_momentum_incompressible_without_boundedEnergy_exists
    (ν : ℝ) (A : Fin 3 → Fin 3 → ℝ) (g gdot : NSTime → ℝ)
    (hA : ∀ i j, A i j = A j i)
    (htrace : ∑ i : Fin 3, A i i = 0)
    (hAnz : ∃ i j : Fin 3, A i j ≠ 0)
    (hgnz : ∃ t : NSTime, g t ≠ 0)
    (hg : ContDiff ℝ ∞ g) (hgdot : ContDiff ℝ ∞ gdot)
    (hderiv : ∀ t : NSTime, HasDerivAt g (gdot t) t) :
    ∃ b : ℝ → FiniteModeState FiniteModeAffineQuadraticPressureIndex,
      ∃ u : NSVelocityField, ∃ p : NSPressureField,
      b = finiteModeLinearMatrixTimePressureCoefficients A g gdot ∧
        u = finiteModeLinearMatrixTimeVelocity A g ∧
          p = finiteModeReconstructedPressure finiteModeAffineQuadraticPressureMode b ∧
            smoothSpaceTimeVelocity u ∧
              smoothSpaceTimePressure p ∧
                (∀ t x,
                  timeVelocityDerivative u t x +
                      spatialConvection u t x +
                        spatialPressureGradient p t x =
                    ν • spatialLaplacian u t x) ∧
                (∀ t x, spatialDivergence u t x = 0) ∧
                  ¬ boundedKineticEnergy u := by
  refine
    ⟨finiteModeLinearMatrixTimePressureCoefficients A g gdot,
      finiteModeLinearMatrixTimeVelocity A g,
      finiteModeLinearMatrixTimePressure A g gdot,
      rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact finiteModeLinearMatrix_timeDependent_smoothSpaceTimeVelocity A g hg
  · simpa [finiteModeLinearMatrixTimePressure] using
      finiteModeLinearMatrix_timeDependent_smoothSpaceTimePressure
        A g gdot hg hgdot
  · simpa [finiteModeLinearMatrixTimePressure] using
      finiteModeLinearMatrix_timeDependent_pointwise_momentum_eq
        ν A g gdot hA hderiv
  · exact finiteModeLinearMatrix_timeDependent_spatialDivergence_zero_of_trace
      A g htrace
  · exact not_boundedKineticEnergy_finiteModeLinearMatrixTimeVelocity hAnz hgnz

/-- A local coefficient solution supplied by Picard-Lindelof reconstructs to an
actual spatial velocity field whose time derivative is the reconstructed
projected RHS throughout the local interval. -/
theorem finiteModeProjectedNS_local_reconstructed_velocity_exists
    {ι : Type*} [Fintype ι]
    (mode : ι → NSSpace → NSSpace)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a₀ : FiniteModeState ι) :
    ∃ a : ℝ → FiniteModeState ι, ∃ u : NSVelocityField,
      a 0 = a₀ ∧
        u 0 = finiteModeReconstructedInitialVelocity mode a₀ ∧
          ∃ ε > (0 : ℝ), ∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
            timeVelocityDerivative u t x =
              finiteModeReconstructedAcceleration mode C a t x := by
  rcases finiteModeProjectedNSRHS_local_solution_exists C a₀ with
    ⟨a, ha0, ε, hε, ha⟩
  refine ⟨a, finiteModeReconstructedVelocity mode a, ha0, ?_, ε, hε, ?_⟩
  · funext x
    simp [finiteModeReconstructedVelocity, finiteModeReconstructedInitialVelocity, ha0]
  · intro t ht x
    exact finiteModeReconstructedVelocity_timeDerivative_at mode C a t (ha t ht) x

/-- Picard-Lindelof plus divergence-free modes gives a local reconstructed
velocity field with both the projected-RHS time derivative identity and
pointwise incompressibility. -/
theorem finiteModeProjectedNS_local_reconstructed_divergenceFree_velocity_exists
    {ι : Type*} [Fintype ι]
    (mode : ι → NSSpace → NSSpace)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a₀ : FiniteModeState ι)
    (hmodeDiff : ∀ i x, DifferentiableAt ℝ (mode i) x)
    (hmodeDiv : ∀ i t x, spatialDivergence (fun _ : NSTime => mode i) t x = 0) :
    ∃ a : ℝ → FiniteModeState ι, ∃ u : NSVelocityField,
      a 0 = a₀ ∧
        u 0 = finiteModeReconstructedInitialVelocity mode a₀ ∧
          ∃ ε > (0 : ℝ),
            (∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
              timeVelocityDerivative u t x =
                finiteModeReconstructedAcceleration mode C a t x) ∧
            (∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
              spatialDivergence u t x = 0) := by
  rcases finiteModeProjectedNSRHS_local_solution_exists C a₀ with
    ⟨a, ha0, ε, hε, ha⟩
  refine ⟨a, finiteModeReconstructedVelocity mode a, ha0, ?_, ε, hε, ?_, ?_⟩
  · funext x
    simp [finiteModeReconstructedVelocity, finiteModeReconstructedInitialVelocity, ha0]
  · intro t ht x
    exact finiteModeReconstructedVelocity_timeDerivative_at mode C a t (ha t ht) x
  · intro t _ht x
    exact finiteModeReconstructedVelocity_spatialDivergence_zero mode a hmodeDiff hmodeDiv t x

end NavierStokes
end FluidDynamics
end Mettapedia
