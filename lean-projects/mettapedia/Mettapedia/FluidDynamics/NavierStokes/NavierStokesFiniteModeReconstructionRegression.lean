import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeReconstruction

/-!
# Regression Tests for Finite-Mode Spatial Reconstruction
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open Set
open scoped ContDiff
open scoped Laplacian

section FiniteModeReconstructionRegression

/-- A coefficient derivative reconstructs to the spatial time derivative. -/
theorem finiteModeReconstructedVelocity_timeDerivative_at_regression
    {ι : Type*} [Fintype ι]
    (mode : ι → NSSpace → NSSpace)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (t : NSTime)
    (ha : HasDerivAt a (finiteModeProjectedNSRHS C (a t)) t)
    (x : NSSpace) :
    timeVelocityDerivative (finiteModeReconstructedVelocity mode a) t x =
      finiteModeReconstructedAcceleration mode C a t x :=
  finiteModeReconstructedVelocity_timeDerivative_at mode C a t ha x

/-- Pressure modes reconstruct to the intended finite pressure sum. -/
theorem finiteModeReconstructedPressure_apply_regression
    {κ : Type*} [Fintype κ]
    (pressureMode : κ → NSSpace → ℝ) (b : ℝ → FiniteModeState κ)
    (t : NSTime) (x : NSSpace) :
    finiteModeReconstructedPressure pressureMode b t x =
      ∑ k : κ, b t k * pressureMode k x := by
  simp

/-- The reconstructed finite pressure gradient expands into modal gradients. -/
theorem finiteModeReconstructedPressure_spatialPressureGradient_regression
    {κ : Type*} [Fintype κ]
    (pressureMode : κ → NSSpace → ℝ) (b : ℝ → FiniteModeState κ)
    (t : NSTime) (x : NSSpace)
    (hmode : ∀ k, DifferentiableAt ℝ (pressureMode k) x) :
    spatialPressureGradient (finiteModeReconstructedPressure pressureMode b) t x =
      ∑ k : κ, b t k • gradient (pressureMode k) x :=
  finiteModeReconstructedPressure_spatialPressureGradient pressureMode b t x hmode

/-- The coordinate pressure ansatz realizes an arbitrary time-dependent constant
pressure gradient. -/
theorem finiteModeCoordinatePressure_spatialPressureGradient_regression
    (c : NSTime → NSSpace) (t : NSTime) (x : NSSpace) :
    spatialPressureGradient
        (finiteModeReconstructedPressure finiteModeCoordinatePressureMode
          (finiteModeCoordinatePressureCoefficients c)) t x =
      c t :=
  finiteModeCoordinatePressure_spatialPressureGradient c t x

/-- The diagonal quadratic pressure ansatz realizes nonconstant diagonal
linear-in-space pressure gradients. -/
theorem finiteModeDiagonalQuadraticPressure_spatialPressureGradient_regression
    (d : NSTime → FiniteModeState (Fin 3)) (t : NSTime) (x : NSSpace) :
    spatialPressureGradient
        (finiteModeReconstructedPressure finiteModeDiagonalQuadraticPressureMode
          (finiteModeDiagonalQuadraticPressureCoefficients d)) t x =
      ∑ j : Fin 3, d t j • (x j • EuclideanSpace.single j (1 : ℝ)) :=
  finiteModeDiagonalQuadraticPressure_spatialPressureGradient d t x

/-- A finite pressure-mode gradient balance closes the reconstructed momentum
residual. -/
theorem finiteModeReconstructedMomentumResidualZeroOn_of_pressureModeGradient_balance_regression
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
    finiteModeReconstructedMomentumResidualZeroOn I ν mode pressureMode C a b :=
  finiteModeReconstructedMomentumResidualZeroOn_of_pressureModeGradient_balance
    I ν mode pressureMode C a b hpressureModeDiff hbalance

theorem finiteModePressureHelmholtzRangeOn_iff_residualZeroOn_regression
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
          range (finiteModePressureGradientSynthesis pressureMode) :=
  finiteModePressureHelmholtzRangeOn_iff_residualZeroOn
    I ν mode pressureMode C a hpressureModeDiff

/-- A finite pressure-primitive basis realizes exactly its vector-field
subspace as a pressure-gradient range. -/
theorem finiteModePressureGradientSynthesis_range_eq_submodule_regression
    {κ : Type*} [Fintype κ]
    (pressureMode : κ → NSSpace → ℝ)
    (V : Submodule ℝ (NSSpace → NSSpace))
    (B : Module.Basis κ ℝ V)
    (hgradientBasis : ∀ k,
      ((B k : V) : NSSpace → NSSpace) =
        fun x => gradient (pressureMode k) x) :
    range (finiteModePressureGradientSynthesis pressureMode) =
      (V : Set (NSSpace → NSSpace)) :=
  finiteModePressureGradientSynthesis_range_eq_submodule
    pressureMode V B hgradientBasis

/-- With a pressure-primitive basis, residual closure is equivalent to
membership of the non-pressure defect in the gradient subspace. -/
theorem finiteModePressurePrimitiveBasisOn_iff_residualZeroOn_regression
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
        -finiteModeNonPressureMomentumDefect ν mode C a t ∈ V :=
  finiteModePressurePrimitiveBasisOn_iff_residualZeroOn
    I ν mode pressureMode C a V B hpressureModeDiff hgradientBasis

/-- Homogeneous curl-free polynomial vector fields have the radial polynomial
pressure primitive promised by the pressure reconstruction algebra. -/
theorem finiteModeHomogeneousPolynomialPressurePrimitive_pderiv_regression
    (n : ℕ) (F : Fin 3 → MvPolynomial (Fin 3) ℝ)
    (hhom : ∀ j, (F j).IsHomogeneous n)
    (hcurl : ∀ i j, MvPolynomial.pderiv i (F j) =
      MvPolynomial.pderiv j (F i))
    (j : Fin 3) :
    MvPolynomial.pderiv j
        (finiteModeHomogeneousPolynomialPressurePrimitive n F) =
      F j :=
  finiteModeHomogeneousPolynomialPressurePrimitive_pderiv n F hhom hcurl j

/-- Finite homogeneous polynomial decompositions reconstruct pressure
primitives componentwise. -/
theorem finiteModeFiniteHomogeneousPolynomialPressurePrimitive_pderiv_regression
    (s : Finset ℕ) (F : ℕ → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (hhom : ∀ n ∈ s, ∀ j, (F n j).IsHomogeneous n)
    (hcurl : ∀ n ∈ s, ∀ i j,
      MvPolynomial.pderiv i (F n j) =
        MvPolynomial.pderiv j (F n i))
    (j : Fin 3) :
    MvPolynomial.pderiv j
        (finiteModeFiniteHomogeneousPolynomialPressurePrimitive s F) =
      s.sum fun n => F n j :=
  finiteModeFiniteHomogeneousPolynomialPressurePrimitive_pderiv
    s F hhom hcurl j

/-- Coefficients of formal partial derivatives are shifted by one exponent in
the differentiated coordinate. -/
theorem finiteModePolynomial_coeff_pderiv_regression
    (i : Fin 3) (d : Fin 3 →₀ ℕ) (φ : MvPolynomial (Fin 3) ℝ) :
    MvPolynomial.coeff d (MvPolynomial.pderiv i φ) =
      MvPolynomial.coeff (d + Finsupp.single i 1) φ *
        ((d i + 1 : ℕ) : ℝ) :=
  finiteModePolynomial_coeff_pderiv i d φ

/-- Partial differentiation commutes with homogeneous projection up to the
expected degree shift. -/
theorem finiteModeHomogeneousComponent_pderiv_succ_regression
    (n : ℕ) (i : Fin 3) (φ : MvPolynomial (Fin 3) ℝ) :
    MvPolynomial.pderiv i (MvPolynomial.homogeneousComponent (n + 1) φ) =
      MvPolynomial.homogeneousComponent n (MvPolynomial.pderiv i φ) :=
  finiteModeHomogeneousComponent_pderiv_succ n i φ

/-- General curl-free polynomial vector fields have an explicit polynomial
pressure primitive. -/
theorem finiteModePolynomialPressurePrimitive_pderiv_regression
    (G : Fin 3 → MvPolynomial (Fin 3) ℝ)
    (hcurl : ∀ i j,
      MvPolynomial.pderiv i (G j) =
        MvPolynomial.pderiv j (G i))
    (j : Fin 3) :
    MvPolynomial.pderiv j (finiteModePolynomialPressurePrimitive G) =
      G j :=
  finiteModePolynomialPressurePrimitive_pderiv G hcurl j

/-- Formal mixed partial derivatives commute for polynomial pressure
potentials. -/
theorem finiteModePolynomial_pderiv_comm_regression
    (i j : Fin 3) (p : MvPolynomial (Fin 3) ℝ) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j p) =
      MvPolynomial.pderiv j (MvPolynomial.pderiv i p) :=
  finiteModePolynomial_pderiv_comm i j p

/-- Curl-freeness is exactly the polynomial pressure-solvability condition. -/
theorem finiteModePolynomialPressurePrimitive_exists_iff_curlFree_regression
    (G : Fin 3 → MvPolynomial (Fin 3) ℝ) :
    (∃ p : MvPolynomial (Fin 3) ℝ,
        ∀ j, MvPolynomial.pderiv j p = G j) ↔
      ∀ i j, MvPolynomial.pderiv i (G j) =
        MvPolynomial.pderiv j (G i) :=
  finiteModePolynomialPressurePrimitive_exists_iff_curlFree G

/-- Evaluating a multivariate polynomial on `NSSpace` has the expected
coordinate-gradient formula. -/
theorem finiteModePolynomialEval_gradient_regression
    (p : MvPolynomial (Fin 3) ℝ) (x : NSSpace) :
    gradient (fun y : NSSpace => MvPolynomial.eval y p) x =
      finiteModePolynomialEvalGradient p x :=
  finiteModePolynomialEval_gradient p x

/-- Scalar polynomial evaluation has the formal polynomial Laplacian. -/
theorem finiteModePolynomialEval_laplacian_regression
    (p : MvPolynomial (Fin 3) ℝ) (x : NSSpace) :
    Δ (fun y : NSSpace => MvPolynomial.eval y p) x =
      MvPolynomial.eval x (finiteModePolynomialScalarLaplacian p) :=
  finiteModePolynomialEval_laplacian p x

/-- Polynomial vector fields have the expected componentwise Fréchet
derivative. -/
theorem finiteModePolynomialVectorFieldEval_hasFDerivAt_regression
    (U : Fin 3 → MvPolynomial (Fin 3) ℝ) (x : NSSpace) :
    HasFDerivAt (finiteModePolynomialVectorFieldEval U)
      (finiteModePolynomialVectorFieldFDeriv U x) x :=
  finiteModePolynomialVectorFieldEval_hasFDerivAt U x

/-- A one-mode polynomial finite-mode velocity reconstruction is represented by
the explicit polynomial linear combination of its mode components. -/
theorem oneModePolynomialReconstructedVelocity_eq_eval_regression
    (modePoly : PUnit → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (a : ℝ → FiniteModeState PUnit)
    (t : NSTime) (x : NSSpace) :
    finiteModeReconstructedVelocity
        (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y) a t x =
      finiteModePolynomialVectorFieldEval
        (finiteModePolynomialReconstructedVelocityComponents modePoly a t) x :=
  finiteModePolynomialReconstructedVelocity_eq_eval modePoly a t x

/-- A one-mode projected acceleration from polynomial spatial modes is
represented by its explicit polynomial linear combination. -/
theorem oneModePolynomialReconstructedAcceleration_eq_eval_regression
    (modePoly : PUnit → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (C : FiniteModeProjectedNSCoefficients PUnit)
    (a : ℝ → FiniteModeState PUnit)
    (t : NSTime) (x : NSSpace) :
    finiteModeReconstructedAcceleration
        (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y) C a t x =
      finiteModePolynomialVectorFieldEval
        (finiteModePolynomialReconstructedAccelerationComponents modePoly C a t) x :=
  finiteModePolynomialReconstructedAcceleration_eq_eval modePoly C a t x

/-- Concrete convection of a polynomial vector field matches the formal
component formula `Σ_r u_r ∂_r u_j`. -/
theorem finiteModePolynomialVectorField_spatialConvection_regression
    (U : NSTime → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (t : NSTime) (x : NSSpace) :
    spatialConvection
        (fun s y => finiteModePolynomialVectorFieldEval (U s) y) t x =
      finiteModePolynomialVectorFieldEval
        (finiteModePolynomialConvectionComponents (U t)) x :=
  finiteModePolynomialVectorField_spatialConvection U t x

/-- Concrete spatial Laplacian of a polynomial vector field matches the formal
componentwise polynomial Laplacian. -/
theorem finiteModePolynomialVectorField_spatialLaplacian_regression
    (U : NSTime → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (t : NSTime) (x : NSSpace) :
    spatialLaplacian
        (fun s y => finiteModePolynomialVectorFieldEval (U s) y) t x =
      finiteModePolynomialVectorFieldEval
        (finiteModePolynomialLaplacianComponents (U t)) x :=
  finiteModePolynomialVectorField_spatialLaplacian U t x

/-- The concrete convection of a one-mode polynomial finite-mode
reconstruction is represented by the formal polynomial convection of the
reconstructed velocity components. -/
theorem oneModePolynomialReconstructedVelocity_spatialConvection_regression
    (modePoly : PUnit → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (a : ℝ → FiniteModeState PUnit)
    (t : NSTime) (x : NSSpace) :
    spatialConvection
        (finiteModeReconstructedVelocity
          (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y) a) t x =
      finiteModePolynomialVectorFieldEval
        (finiteModePolynomialConvectionComponents
          (finiteModePolynomialReconstructedVelocityComponents modePoly a t)) x :=
  finiteModePolynomialReconstructedVelocity_spatialConvection modePoly a t x

/-- The concrete spatial Laplacian of a one-mode polynomial reconstruction is
represented by the formal componentwise polynomial Laplacian. -/
theorem oneModePolynomialReconstructedVelocity_spatialLaplacian_regression
    (modePoly : PUnit → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (a : ℝ → FiniteModeState PUnit)
    (t : NSTime) (x : NSSpace) :
    spatialLaplacian
        (finiteModeReconstructedVelocity
          (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y) a) t x =
      finiteModePolynomialVectorFieldEval
        (finiteModePolynomialLaplacianComponents
          (finiteModePolynomialReconstructedVelocityComponents modePoly a t)) x :=
  finiteModePolynomialReconstructedVelocity_spatialLaplacian modePoly a t x

/-- With a polynomial Laplacian representation supplied, the full one-mode
non-pressure finite-mode defect is represented by the explicit polynomial
defect components. -/
theorem oneModePolynomialNonPressureDefect_eq_eval_of_laplacian_regression
    (ν : ℝ)
    (modePoly : PUnit → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (C : FiniteModeProjectedNSCoefficients PUnit)
    (a : ℝ → FiniteModeState PUnit)
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
        (finiteModePolynomialNonPressureDefectComponents ν modePoly C a lapPoly t) x :=
  finiteModePolynomialNonPressureDefect_eq_eval_of_laplacian
    ν modePoly C a lapPoly hLap t x

/-- The full one-mode polynomial non-pressure finite-mode defect is represented
by the explicit polynomial defect components with the formal Laplacian. -/
theorem oneModePolynomialNonPressureDefect_eq_eval_regression
    (ν : ℝ)
    (modePoly : PUnit → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (C : FiniteModeProjectedNSCoefficients PUnit)
    (a : ℝ → FiniteModeState PUnit)
    (t : NSTime) (x : NSSpace) :
    finiteModeNonPressureMomentumDefect ν
        (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y) C a t x =
      finiteModePolynomialVectorFieldEval
        (finiteModePolynomialNonPressureDefectComponents ν modePoly C a
          (fun s => finiteModePolynomialLaplacianComponents
            (finiteModePolynomialReconstructedVelocityComponents modePoly a s)) t) x :=
  finiteModePolynomialNonPressureDefect_eq_eval ν modePoly C a t x

/-- The formal polynomial pressure primitive reconstructs a concrete spatial
pressure gradient for any curl-free polynomial vector field. -/
theorem finiteModePolynomialPressureMode_gradient_regression
    (G : Fin 3 → MvPolynomial (Fin 3) ℝ)
    (hcurl : ∀ i j,
      MvPolynomial.pderiv i (G j) =
        MvPolynomial.pderiv j (G i))
    (x : NSSpace) :
    gradient (finiteModePolynomialPressureMode G) x =
      finiteModePolynomialVectorFieldEval G x :=
  finiteModePolynomialPressureMode_gradient G hcurl x

/-- The same polynomial pressure solve through the Navier-Stokes
`spatialPressureGradient` API. -/
theorem finiteModePolynomialPressureMode_spatialPressureGradient_regression
    (G : Fin 3 → MvPolynomial (Fin 3) ℝ)
    (hcurl : ∀ i j,
      MvPolynomial.pderiv i (G j) =
        MvPolynomial.pderiv j (G i))
    (t : NSTime) (x : NSSpace) :
    spatialPressureGradient (fun _ y => finiteModePolynomialPressureMode G y) t x =
      finiteModePolynomialVectorFieldEval G x :=
  finiteModePolynomialPressureMode_spatialPressureGradient G hcurl t x

/-- Pointwise equality of a polynomial pressure gradient with a polynomial
vector field is equivalent to coefficient-level derivative identities. -/
theorem finiteModePolynomialPressureGradient_eq_eval_iff_pderiv_regression
    (p : MvPolynomial (Fin 3) ℝ)
    (G : Fin 3 → MvPolynomial (Fin 3) ℝ)
    (t : NSTime) :
    (∀ x : NSSpace,
      spatialPressureGradient (fun _ y => MvPolynomial.eval y p) t x =
        finiteModePolynomialVectorFieldEval G x) ↔
      ∀ j, MvPolynomial.pderiv j p = G j :=
  finiteModePolynomialPressureGradient_eq_eval_iff_pderiv p G t

/-- Time-dependent version of the polynomial pressure-gradient coefficient
equivalence. -/
theorem finiteModeTimePolynomialPressureGradient_eq_eval_iff_pderiv_regression
    (P : NSTime → MvPolynomial (Fin 3) ℝ)
    (G : NSTime → Fin 3 → MvPolynomial (Fin 3) ℝ) :
    (∀ t x,
      spatialPressureGradient (fun s y => MvPolynomial.eval y (P s)) t x =
        finiteModePolynomialVectorFieldEval (G t) x) ↔
      ∀ t j, MvPolynomial.pderiv j (P t) = G t j :=
  finiteModeTimePolynomialPressureGradient_eq_eval_iff_pderiv P G

/-- Time-dependent polynomial pressure-gradient solvability is exactly the
curl-free condition on each polynomial time slice. -/
theorem finiteModeTimePolynomialPressureGradient_exists_iff_curlFree_regression
    (G : NSTime → Fin 3 → MvPolynomial (Fin 3) ℝ) :
    (∃ P : NSTime → MvPolynomial (Fin 3) ℝ,
        ∀ t x,
          spatialPressureGradient (fun s y => MvPolynomial.eval y (P s)) t x =
            finiteModePolynomialVectorFieldEval (G t) x) ↔
      ∀ t i j, MvPolynomial.pderiv i (G t j) =
        MvPolynomial.pderiv j (G t i) :=
  finiteModeTimePolynomialPressureGradient_exists_iff_curlFree G

/-- On any time set, a polynomial pressure closes a polynomially represented
non-pressure defect exactly when that polynomial defect is curl-free. -/
theorem oneModePolynomialPressure_closes_nonPressureDefectOn_iff_curlFree_of_polynomialDefect_regression
    (I : Set NSTime)
    (ν : ℝ)
    (mode : PUnit → NSSpace → NSSpace)
    (C : FiniteModeProjectedNSCoefficients PUnit)
    (a : ℝ → FiniteModeState PUnit)
    (G : NSTime → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (hdefect : ∀ t ∈ I,
      -finiteModeNonPressureMomentumDefect ν mode C a t =
        finiteModePolynomialVectorFieldEval (G t)) :
    (∃ P : NSTime → MvPolynomial (Fin 3) ℝ,
        ∀ t ∈ I, ∀ x : NSSpace,
          spatialPressureGradient (fun s y => MvPolynomial.eval y (P s)) t x =
            -finiteModeNonPressureMomentumDefect ν mode C a t x) ↔
      ∀ t ∈ I, ∀ i j, MvPolynomial.pderiv i (G t j) =
        MvPolynomial.pderiv j (G t i) :=
  finiteModePolynomialPressure_closes_nonPressureDefectOn_iff_curlFree_of_polynomialDefect
    I ν mode C a G hdefect

/-- The abstract projected finite-mode RHS can produce a polynomial residual
that is not curl-free. -/
theorem finiteModeShearAcceleration_nonPressureDefect_eq_polynomial_regression
    (t : NSTime) (x : NSSpace) :
    finiteModeNonPressureMomentumDefect (0 : ℝ) finiteModeShearAccelerationMode
        finiteModeUnitForcingCoefficients finiteModeZeroCoefficientCurve t x =
      finiteModePolynomialVectorFieldEval
        finiteModeShearAccelerationPolynomialVectorField x :=
  finiteModeShearAcceleration_nonPressureDefect_eq_polynomial t x

/-- The identity coefficient curve is checked as a real solution of the
one-mode unit-forcing projected ODE. -/
theorem finiteModeIdentityCoefficientCurve_hasDerivAt_regression
    (t : NSTime) :
    HasDerivAt finiteModeIdentityCoefficientCurve
      (finiteModeProjectedNSRHS finiteModeUnitForcingCoefficients
        (finiteModeIdentityCoefficientCurve t)) t :=
  finiteModeIdentityCoefficientCurve_hasDerivAt t

/-- The same shear obstruction persists for the actual identity coefficient
solution. -/
theorem finiteModeShearAcceleration_solution_nonPressureDefect_eq_polynomial_regression
    (t : NSTime) (x : NSSpace) :
    finiteModeNonPressureMomentumDefect (0 : ℝ) finiteModeShearAccelerationMode
        finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve t x =
      finiteModePolynomialVectorFieldEval
        finiteModeShearAccelerationPolynomialVectorField x :=
  finiteModeShearAcceleration_solution_nonPressureDefect_eq_polynomial t x

/-- The shear residual polynomial vector field is not a polynomial pressure
gradient. -/
theorem finiteModeShearAccelerationPolynomialVectorField_no_pressurePrimitive_regression :
    ¬ ∃ p : MvPolynomial (Fin 3) ℝ, ∀ j,
      MvPolynomial.pderiv j p =
        finiteModeShearAccelerationPolynomialVectorField j :=
  finiteModeShearAccelerationPolynomialVectorField_no_pressurePrimitive

/-- The sign required to close momentum also has no polynomial pressure
primitive. -/
theorem finiteModeShearAccelerationPolynomialVectorField_no_negative_pressurePrimitive_regression :
    ¬ ∃ p : MvPolynomial (Fin 3) ℝ, ∀ j,
      MvPolynomial.pderiv j p =
        -finiteModeShearAccelerationPolynomialVectorField j :=
  finiteModeShearAccelerationPolynomialVectorField_no_negative_pressurePrimitive

/-- No time-dependent scalar polynomial can primitive the sign-correct closing
gradient for the identity-coefficient shear residual. -/
theorem finiteModeShearAcceleration_solution_no_timeDependentPolynomialPressurePrimitive_regression :
    ¬ ∃ P : NSTime → MvPolynomial (Fin 3) ℝ, ∀ t j,
      MvPolynomial.pderiv j (P t) =
        -finiteModeShearAccelerationPolynomialVectorField j :=
  finiteModeShearAcceleration_solution_no_timeDependentPolynomialPressurePrimitive

/-- No time-dependent scalar polynomial pressure can close the identity-curve
shear residual through the pointwise pressure-gradient API. -/
theorem finiteModeShearAcceleration_solution_no_pointwisePolynomialPressureGradient_regression :
    ¬ ∃ P : NSTime → MvPolynomial (Fin 3) ℝ,
      ∀ t x,
        spatialPressureGradient (fun s y => MvPolynomial.eval y (P s)) t x =
            -finiteModeNonPressureMomentumDefect (0 : ℝ) finiteModeShearAccelerationMode
              finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve t x :=
  finiteModeShearAcceleration_solution_no_pointwisePolynomialPressureGradient

/-- No time-dependent polynomial pressure can make the shear coefficient
solution satisfy pointwise momentum on any time set containing `0`. -/
theorem finiteModeShearAcceleration_solution_no_polynomialPressureMomentumOn_regression
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
            t x :=
  finiteModeShearAcceleration_solution_no_polynomialPressureMomentumOn I h0

/-- The finite-mode projection interface alone does not force residual
curl-freeness. -/
theorem finiteModeProjectedNS_nonPressureDefect_curlFree_not_forced_obstruction_regression :
    (∀ t : NSTime,
      finiteModeNonPressureMomentumDefect (0 : ℝ) finiteModeShearAccelerationMode
          finiteModeUnitForcingCoefficients finiteModeZeroCoefficientCurve t =
        finiteModePolynomialVectorFieldEval
          finiteModeShearAccelerationPolynomialVectorField) ∧
      ¬ ∃ p : MvPolynomial (Fin 3) ℝ, ∀ j,
        MvPolynomial.pderiv j p =
          finiteModeShearAccelerationPolynomialVectorField j :=
  finiteModeProjectedNS_nonPressureDefect_curlFree_not_forced_obstruction

/-- The sharpened obstruction uses an actual solution of the abstract
coefficient ODE. -/
theorem finiteModeProjectedNS_coefficientSolution_nonPressureDefect_curlFree_not_forced_obstruction_regression :
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
          finiteModeShearAccelerationPolynomialVectorField j :=
  finiteModeProjectedNS_coefficientSolution_nonPressureDefect_curlFree_not_forced_obstruction

/-- The coefficient-solution obstruction rules out the sign-correct
time-dependent polynomial pressure primitive needed for momentum closure. -/
theorem finiteModeProjectedNS_coefficientSolution_no_polynomialPressurePrimitive_obstruction_regression :
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
          -finiteModeShearAccelerationPolynomialVectorField j :=
  finiteModeProjectedNS_coefficientSolution_no_polynomialPressurePrimitive_obstruction

/-- Pointwise pressure-gradient version of the coefficient-solution obstruction. -/
theorem finiteModeProjectedNS_coefficientSolution_no_pointwisePolynomialPressureGradient_obstruction_regression :
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
              finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve t x :=
  finiteModeProjectedNS_coefficientSolution_no_pointwisePolynomialPressureGradient_obstruction

/-- The coefficient-solution obstruction reaches the actual pointwise momentum
equation on a concrete interval. -/
theorem finiteModeProjectedNS_coefficientSolution_no_polynomialPressureMomentum_obstruction_regression :
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
              t x :=
  finiteModeProjectedNS_coefficientSolution_no_polynomialPressureMomentum_obstruction

/-- The projected ODE condition alone cannot universally force polynomial
pressure closure of the reconstructed pointwise momentum equation. -/
theorem finiteModeProjectedNS_polynomialPressureMomentum_not_forced_regression :
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
                (finiteModeReconstructedVelocity mode a) t x :=
  finiteModeProjectedNS_polynomialPressureMomentum_not_forced

/-- The uniform-acceleration finite-mode reconstruction has zero momentum
residual on all time. -/
theorem finiteModeUniformAcceleration_reconstructedResidualZeroOn_univ_regression
    (ν : ℝ) :
    finiteModeReconstructedMomentumResidualZeroOn Set.univ ν
      finiteModeUniformAccelerationMode finiteModeCoordinatePressureMode
      finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve
      finiteModeUniformAccelerationPressureCoefficients :=
  finiteModeUniformAcceleration_reconstructedResidualZeroOn_univ ν

/-- The uniform-acceleration mode gives an explicit reconstructed velocity and
pressure satisfying the pointwise momentum equation. -/
theorem finiteModeUniformAcceleration_reconstructed_velocityPressure_momentum_exists_regression
    (ν : ℝ) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity finiteModeUniformAccelerationMode
        finiteModeIdentityCoefficientCurve ∧
        p = finiteModeUniformAccelerationPressure ∧
        ∀ t x,
          timeVelocityDerivative u t x +
              spatialConvection u t x +
                spatialPressureGradient p t x =
            ν • spatialLaplacian u t x :=
  finiteModeUniformAcceleration_reconstructed_velocityPressure_momentum_exists ν

/-- Zero reconstructed residual is exactly the pointwise momentum equation once
the coefficient curve solves the projected ODE. -/
theorem finiteModeReconstructedMomentumResidualZeroAt_iff_momentumEquation_at_regression
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
        ν • spatialLaplacian (finiteModeReconstructedVelocity mode a) t x :=
  finiteModeReconstructedMomentumResidualZeroAt_iff_momentumEquation_at
    ν mode pressureMode C a b t ha x

/-- Picard's one-mode coefficient solution reconstructs to an actual concrete
velocity field with the local projected-RHS derivative identity. -/
theorem oneModeProjectedNS_local_reconstructed_velocity_regression
    (mode : PUnit → NSSpace → NSSpace)
    (c₀ c₁ c₂ a₀ : ℝ) :
    ∃ a : ℝ → FiniteModeState PUnit, ∃ u : NSVelocityField,
      a 0 = (fun _ : PUnit => a₀) ∧
        u 0 =
          finiteModeReconstructedInitialVelocity mode (fun _ : PUnit => a₀) ∧
          ∃ ε > (0 : ℝ), ∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
            timeVelocityDerivative u t x =
              finiteModeReconstructedAcceleration mode
                ({ forcing := fun _ => c₀
                   linear := fun _ _ => c₁
                   quadratic := fun _ _ _ => c₂ } :
                  FiniteModeProjectedNSCoefficients PUnit) a t x := by
  exact
    finiteModeProjectedNS_local_reconstructed_velocity_exists mode
      ({ forcing := fun _ => c₀
         linear := fun _ _ => c₁
         quadratic := fun _ _ _ => c₂ } :
        FiniteModeProjectedNSCoefficients PUnit)
      (fun _ => a₀)

/-- Divergence-free modes reconstruct to a divergence-free velocity field. -/
theorem finiteModeReconstructedVelocity_spatialDivergence_zero_regression
    {ι : Type*} [Fintype ι]
    (mode : ι → NSSpace → NSSpace)
    (a : ℝ → FiniteModeState ι)
    (hmodeDiff : ∀ i x, DifferentiableAt ℝ (mode i) x)
    (hmodeDiv : ∀ i t x, spatialDivergence (fun _ : NSTime => mode i) t x = 0)
    (t : NSTime) (x : NSSpace) :
    spatialDivergence (finiteModeReconstructedVelocity mode a) t x = 0 :=
  finiteModeReconstructedVelocity_spatialDivergence_zero
    mode a hmodeDiff hmodeDiv t x

/-- The one-mode Picard reconstruction can carry incompressibility when the
chosen mode is divergence-free. -/
theorem oneModeProjectedNS_local_reconstructed_divergenceFree_velocity_regression
    (mode : PUnit → NSSpace → NSSpace)
    (c₀ c₁ c₂ a₀ : ℝ)
    (hmodeDiff : ∀ i x, DifferentiableAt ℝ (mode i) x)
    (hmodeDiv : ∀ i t x, spatialDivergence (fun _ : NSTime => mode i) t x = 0) :
    ∃ a : ℝ → FiniteModeState PUnit, ∃ u : NSVelocityField,
      a 0 = (fun _ : PUnit => a₀) ∧
        u 0 =
          finiteModeReconstructedInitialVelocity mode (fun _ : PUnit => a₀) ∧
          ∃ ε > (0 : ℝ),
            (∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
              timeVelocityDerivative u t x =
                finiteModeReconstructedAcceleration mode
                  ({ forcing := fun _ => c₀
                     linear := fun _ _ => c₁
                     quadratic := fun _ _ _ => c₂ } :
                    FiniteModeProjectedNSCoefficients PUnit) a t x) ∧
            (∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace, spatialDivergence u t x = 0) := by
  exact
    finiteModeProjectedNS_local_reconstructed_divergenceFree_velocity_exists mode
      ({ forcing := fun _ => c₀
         linear := fun _ _ => c₁
         quadratic := fun _ _ _ => c₂ } :
        FiniteModeProjectedNSCoefficients PUnit)
      (fun _ => a₀) hmodeDiff hmodeDiv

/-- A one-mode coefficient solution plus explicit zero residual reconstructs
to a concrete velocity-pressure pair satisfying pointwise momentum locally. -/
theorem oneModeProjectedNS_local_reconstructed_velocityPressure_momentum_regression
    (ν : ℝ)
    (mode : PUnit → NSSpace → NSSpace)
    (pressureMode : PUnit → NSSpace → ℝ)
    (C : FiniteModeProjectedNSCoefficients PUnit)
    (a : ℝ → FiniteModeState PUnit)
    (b : ℝ → FiniteModeState PUnit)
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
              ν • spatialLaplacian u t x :=
  finiteModeProjectedNS_local_reconstructed_velocityPressure_momentum_of_residual_zero
    ν mode pressureMode C a b ε ha hres

/-- A one-mode coefficient solution plus a Helmholtz range witness constructs
pressure coefficients and reconstructs local pointwise momentum. -/
theorem oneModeProjectedNS_local_reconstructed_velocityPressure_momentum_of_pressureHelmholtzRange_regression
    (ν : ℝ)
    (mode : PUnit → NSSpace → NSSpace)
    (pressureMode : PUnit → NSSpace → ℝ)
    (C : FiniteModeProjectedNSCoefficients PUnit)
    (a : ℝ → FiniteModeState PUnit)
    (ε : ℝ)
    (ha : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt a (finiteModeProjectedNSRHS C (a t)) t)
    (hpressureModeDiff : ∀ k x, DifferentiableAt ℝ (pressureMode k) x)
    (hrange : ∀ t ∈ Ioo (-ε) ε,
      -finiteModeNonPressureMomentumDefect ν mode C a t ∈
        range (finiteModePressureGradientSynthesis pressureMode)) :
    ∃ b : ℝ → FiniteModeState PUnit, ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity mode a ∧
        p = finiteModeReconstructedPressure pressureMode b ∧
          finiteModeReconstructedMomentumResidualZeroOn
            (Ioo (-ε) ε) ν mode pressureMode C a b ∧
          ∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
            timeVelocityDerivative u t x +
                spatialConvection u t x +
                  spatialPressureGradient p t x =
              ν • spatialLaplacian u t x :=
  finiteModeProjectedNS_local_reconstructed_velocityPressure_momentum_of_pressureHelmholtzRange
    ν mode pressureMode C a ε ha hpressureModeDiff hrange

/-- A local coefficient ODE solution plus a pressure-primitive basis and
subspace-valued defect reconstructs local pointwise momentum. -/
theorem oneModeProjectedNS_local_reconstructed_velocityPressure_momentum_of_pressurePrimitiveBasis_regression
    {κ : Type*} [Fintype κ]
    (ν : ℝ)
    (mode : PUnit → NSSpace → NSSpace)
    (pressureMode : κ → NSSpace → ℝ)
    (C : FiniteModeProjectedNSCoefficients PUnit)
    (a : ℝ → FiniteModeState PUnit)
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
              ν • spatialLaplacian u t x :=
  finiteModeProjectedNS_local_reconstructed_velocityPressure_momentum_of_pressurePrimitiveBasis
    ν mode pressureMode C a ε ha V B hpressureModeDiff hgradientBasis hdefectV

/-- A one-mode coefficient solution whose non-pressure defect is a curl-free
polynomial vector field constructs the corresponding time-dependent polynomial
pressure primitive and reconstructs local pointwise momentum. -/
theorem oneModeProjectedNS_local_reconstructed_velocityPolynomialPressure_momentum_of_polynomialHelmholtz_regression
    (ν : ℝ)
    (mode : PUnit → NSSpace → NSSpace)
    (C : FiniteModeProjectedNSCoefficients PUnit)
    (a : ℝ → FiniteModeState PUnit)
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
              ν • spatialLaplacian u t x :=
  finiteModeProjectedNS_local_reconstructed_velocityPolynomialPressure_momentum_of_polynomialHelmholtz
    ν mode C a ε ha G hcurl hdefect

/-- For one-mode reconstructions, polynomial-pressure solvability of the local
momentum equation is equivalent to curl-freeness of the polynomial defect. -/
theorem oneModeProjectedNS_local_reconstructed_velocityPolynomialPressure_momentum_iff_curlFree_of_polynomialDefect_regression
    (ν : ℝ)
    (mode : PUnit → NSSpace → NSSpace)
    (C : FiniteModeProjectedNSCoefficients PUnit)
    (a : ℝ → FiniteModeState PUnit)
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
        MvPolynomial.pderiv j (G t i) :=
  finiteModeProjectedNS_local_reconstructed_velocityPolynomialPressure_momentum_iff_curlFree_of_polynomialDefect
    ν mode C a ε ha G hdefect

/-- For polynomial one-mode spatial modes with a polynomial Laplacian
representation, local polynomial-pressure solvability is exactly curl-freeness
of the explicit closing pressure-gradient polynomial. -/
theorem oneModeProjectedNS_local_reconstructed_velocityPolynomialPressure_momentum_iff_curlFree_of_polynomialModes_laplacian_regression
    (ν : ℝ)
    (modePoly : PUnit → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (C : FiniteModeProjectedNSCoefficients PUnit)
    (a : ℝ → FiniteModeState PUnit)
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
              ν modePoly C a lapPoly t i) :=
  finiteModeProjectedNS_local_reconstructed_velocityPolynomialPressure_momentum_iff_curlFree_of_polynomialModes_laplacian
    ν modePoly C a ε ha lapPoly hLap

/-- For polynomial one-mode spatial modes, local polynomial-pressure
solvability is exactly curl-freeness of the closing pressure-gradient
polynomial built with the formal Laplacian. -/
theorem oneModeProjectedNS_local_reconstructed_velocityPolynomialPressure_momentum_iff_curlFree_of_polynomialModes_regression
    (ν : ℝ)
    (modePoly : PUnit → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (C : FiniteModeProjectedNSCoefficients PUnit)
    (a : ℝ → FiniteModeState PUnit)
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
              t i) :=
  finiteModeProjectedNS_local_reconstructed_velocityPolynomialPressure_momentum_iff_curlFree_of_polynomialModes
    ν modePoly C a ε ha

/-- Positive polynomial-mode closure: curl-freeness of the computed closing
gradient constructs the explicit polynomial pressure primitive and closes
local pointwise momentum. -/
theorem oneModeProjectedNS_local_reconstructed_velocityPolynomialPressure_momentum_of_polynomialModes_curlFree_regression
    (ν : ℝ)
    (modePoly : PUnit → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (C : FiniteModeProjectedNSCoefficients PUnit)
    (a : ℝ → FiniteModeState PUnit)
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
              ν • spatialLaplacian u t x :=
  finiteModeProjectedNS_local_reconstructed_velocityPolynomialPressure_momentum_of_polynomialModes_curlFree
    ν modePoly C a ε ha hcurl

/-- The radial-linear reconstruction is the concrete field `u(t,x)=t x`. -/
theorem finiteModeRadialLinear_reconstructedVelocity_eq_regression
    (t : NSTime) (x : NSSpace) :
    finiteModeReconstructedVelocity
        (fun i y =>
          finiteModePolynomialVectorFieldEval
            (finiteModeRadialLinearPolynomialMode i) y)
        finiteModeIdentityCoefficientCurve t x =
      t • x :=
  finiteModeRadialLinear_reconstructedVelocity_eq t x

/-- The projected acceleration for the radial-linear identity solution is `x`. -/
theorem finiteModeRadialLinear_reconstructedAcceleration_eq_regression
    (t : NSTime) (x : NSSpace) :
    finiteModeReconstructedAcceleration
        (fun i y =>
          finiteModePolynomialVectorFieldEval
            (finiteModeRadialLinearPolynomialMode i) y)
        finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve t x =
      x :=
  finiteModeRadialLinear_reconstructedAcceleration_eq t x

/-- The time derivative of the radial-linear reconstruction is `x`. -/
theorem finiteModeRadialLinear_timeVelocityDerivative_eq_regression
    (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative
        (finiteModeReconstructedVelocity
          (fun i y =>
            finiteModePolynomialVectorFieldEval
              (finiteModeRadialLinearPolynomialMode i) y)
          finiteModeIdentityCoefficientCurve) t x =
      x :=
  finiteModeRadialLinear_timeVelocityDerivative_eq t x

/-- The convection term for the radial-linear reconstruction is `t^2 x`. -/
theorem finiteModeRadialLinear_spatialConvection_eq_regression
    (t : NSTime) (x : NSSpace) :
    spatialConvection
        (finiteModeReconstructedVelocity
          (fun i y =>
            finiteModePolynomialVectorFieldEval
              (finiteModeRadialLinearPolynomialMode i) y)
          finiteModeIdentityCoefficientCurve) t x =
      (t * t) • x :=
  finiteModeRadialLinear_spatialConvection_eq t x

/-- The radial-linear reconstruction has zero spatial Laplacian. -/
theorem finiteModeRadialLinear_spatialLaplacian_zero_regression
    (t : NSTime) (x : NSSpace) :
    spatialLaplacian
        (finiteModeReconstructedVelocity
          (fun i y =>
            finiteModePolynomialVectorFieldEval
              (finiteModeRadialLinearPolynomialMode i) y)
          finiteModeIdentityCoefficientCurve) t x =
      0 :=
  finiteModeRadialLinear_spatialLaplacian_zero t x

/-- The radial-linear example has closing pressure gradient `-(1+t^2)x`. -/
theorem finiteModeRadialLinearPolynomialClosingPressureGradient_eq_regression
    (ν t : ℝ) (j : Fin 3) :
    finiteModePolynomialClosingPressureGradientComponents
        ν finiteModeRadialLinearPolynomialMode
          finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve
          (fun s => finiteModePolynomialLaplacianComponents
            (finiteModePolynomialReconstructedVelocityComponents
              finiteModeRadialLinearPolynomialMode
              finiteModeIdentityCoefficientCurve s))
        t j =
      -(MvPolynomial.C (1 + t * t) * MvPolynomial.X j) :=
  finiteModeRadialLinearPolynomialClosingPressureGradient_eq ν t j

/-- The polynomial pressure primitive constructed for the radial-linear example
has the expected explicit pressure gradient. -/
theorem finiteModeRadialLinearPolynomialPressureGradient_eq_regression
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
      -(1 + t * t) • x :=
  finiteModeRadialLinearPolynomialPressureGradient_eq ν ε ht x

/-- Direct pointwise momentum identity for the radial-linear reconstruction. -/
theorem finiteModeRadialLinear_reconstructed_momentum_explicit_regression
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
          finiteModeIdentityCoefficientCurve) t x :=
  finiteModeRadialLinear_reconstructed_momentum_explicit ν ε ht x

/-- The finite diagonal-quadratic pressure ansatz realizes the explicit
radial-linear pressure gradient. -/
theorem finiteModeRadialLinearDiagonalPressureGradient_eq_regression
    (t : NSTime) (x : NSSpace) :
    spatialPressureGradient finiteModeRadialLinearDiagonalPressure t x =
      -(1 + t * t) • x :=
  finiteModeRadialLinearDiagonalPressureGradient_eq t x

/-- The radial-linear reconstruction closes pointwise momentum with the finite
diagonal-quadratic pressure ansatz. -/
theorem finiteModeRadialLinear_diagonalPressure_reconstructed_momentum_regression
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
          finiteModeIdentityCoefficientCurve) t x :=
  finiteModeRadialLinear_diagonalPressure_reconstructed_momentum ν t x

/-- The finite diagonal-quadratic pressure ansatz gives zero reconstructed
finite-mode momentum residual for the radial-linear example. -/
theorem finiteModeRadialLinear_diagonalPressure_reconstructedResidualZeroOn_univ_regression
    (ν : ℝ) :
    finiteModeReconstructedMomentumResidualZeroOn Set.univ ν
      (fun i y =>
        finiteModePolynomialVectorFieldEval
          (finiteModeRadialLinearPolynomialMode i) y)
      finiteModeDiagonalQuadraticPressureMode
      finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve
      finiteModeRadialLinearDiagonalPressureCoefficients :=
  finiteModeRadialLinear_diagonalPressure_reconstructedResidualZeroOn_univ ν

/-- Concrete nonconstant radial-linear reconstruction closed by the finite
diagonal-quadratic pressure basis. -/
theorem finiteModeRadialLinear_reconstructed_velocityDiagonalPressure_momentum_exists_regression
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
            ν • spatialLaplacian u t x :=
  finiteModeRadialLinear_reconstructed_velocityDiagonalPressure_momentum_exists ν

/-- The computed radial-linear polynomial closing gradient is represented by
the finite affine-quadratic pressure-gradient space. -/
theorem finiteModeRadialLinearPolynomialClosingPressureGradient_affine_eq_regression
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
        (finiteModeRadialLinearAffinePressureMatrix t) :=
  finiteModeRadialLinearPolynomialClosingPressureGradient_affine_eq ν t

/-- The explicit affine-quadratic pressure has the radial-linear closing
gradient. -/
theorem finiteModeRadialLinearAffineQuadraticPressureGradient_eq_regression
    (t : NSTime) (x : NSSpace) :
    spatialPressureGradient finiteModeRadialLinearAffineQuadraticPressure t x =
      -(1 + t * t) • x :=
  finiteModeRadialLinearAffineQuadraticPressureGradient_eq t x

/-- The radial-linear reconstruction closes pointwise momentum with the
explicit affine-quadratic pressure field. -/
theorem finiteModeRadialLinear_affineQuadraticPressure_reconstructed_momentum_regression
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
          finiteModeIdentityCoefficientCurve) t x :=
  finiteModeRadialLinear_affineQuadraticPressure_reconstructed_momentum ν t x

/-- The explicit affine-quadratic pressure coefficients give zero reconstructed
finite-mode momentum residual for the radial-linear example. -/
theorem finiteModeRadialLinear_affineQuadraticPressure_reconstructedResidualZeroOn_univ_regression
    (ν : ℝ) :
    finiteModeReconstructedMomentumResidualZeroOn Set.univ ν
      (fun i y =>
        finiteModePolynomialVectorFieldEval
          (finiteModeRadialLinearPolynomialMode i) y)
      finiteModeAffineQuadraticPressureMode
      finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve
      finiteModeRadialLinearAffineQuadraticPressureCoefficients :=
  finiteModeRadialLinear_affineQuadraticPressure_reconstructedResidualZeroOn_univ ν

/-- Concrete radial-linear reconstruction closed by the explicit
affine-quadratic pressure field. -/
theorem finiteModeRadialLinear_reconstructed_velocityExplicitAffineQuadraticPressure_momentum_exists_regression
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
            ν • spatialLaplacian u t x :=
  finiteModeRadialLinear_reconstructed_velocityExplicitAffineQuadraticPressure_momentum_exists ν

/-- Concrete radial-linear reconstruction closed by the finite
affine-quadratic pressure basis through the polynomial-to-affine bridge. -/
theorem finiteModeRadialLinear_reconstructed_velocityAffineQuadraticPressure_momentum_exists_regression
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
              ν • spatialLaplacian u t x :=
  finiteModeRadialLinear_reconstructed_velocityAffineQuadraticPressure_momentum_exists ν ε

/-- The diagonal-linear multi-mode coefficient curve solves its forced
projected ODE. -/
theorem finiteModeDiagonalLinearCoefficientCurve_hasDerivAt_regression
    (lam : Fin 3 → ℝ) (t : NSTime) :
    HasDerivAt (finiteModeDiagonalLinearCoefficientCurve lam)
      (finiteModeProjectedNSRHS (finiteModeDiagonalLinearForcingCoefficients lam)
        (finiteModeDiagonalLinearCoefficientCurve lam t)) t :=
  finiteModeDiagonalLinearCoefficientCurve_hasDerivAt lam t

/-- The diagonal-linear multi-mode reconstruction has component formula
`u_j(t,x)=lam_j t x_j`. -/
theorem finiteModeDiagonalLinear_reconstructedVelocity_apply_regression
    (lam : Fin 3 → ℝ) (t : NSTime) (x : NSSpace) (j : Fin 3) :
    finiteModeReconstructedVelocity
        (fun i y =>
          finiteModePolynomialVectorFieldEval
            (finiteModeDiagonalLinearPolynomialMode i) y)
        (finiteModeDiagonalLinearCoefficientCurve lam) t x j =
      lam j * t * x j :=
  finiteModeDiagonalLinear_reconstructedVelocity_apply lam t x j

/-- The computed closing pressure gradient for the diagonal-linear multi-mode
family is affine with symmetric diagonal linear part. -/
theorem finiteModeDiagonalLinearPolynomialClosingPressureGradient_affine_eq_regression
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
        (finiteModeDiagonalLinearAffinePressureMatrix lam t) :=
  finiteModeDiagonalLinearPolynomialClosingPressureGradient_affine_eq ν lam t

/-- Multi-mode diagonal-linear velocity families close through the finite
affine-quadratic pressure basis. -/
theorem finiteModeDiagonalLinear_reconstructed_velocityAffineQuadraticPressure_momentum_exists_regression
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
              ν • spatialLaplacian u t x :=
  finiteModeDiagonalLinear_reconstructed_velocityAffineQuadraticPressure_momentum_exists ν ε lam

/-- Regression: each diagonal-linear mode has divergence `1`. -/
theorem finiteModeDiagonalLinearPolynomialMode_spatialDivergence_regression
    (i : Fin 3) (t : NSTime) (x : NSSpace) :
    spatialDivergence
        (fun _ : NSTime => fun y : NSSpace =>
          finiteModePolynomialVectorFieldEval
            (finiteModeDiagonalLinearPolynomialMode i) y) t x = 1 :=
  finiteModeDiagonalLinearPolynomialMode_spatialDivergence i t x

/-- Regression: the diagonal-linear reconstructed divergence is the time-scaled
coefficient trace. -/
theorem finiteModeDiagonalLinear_spatialDivergence_eq_regression
    (lam : Fin 3 → ℝ) (t : NSTime) (x : NSSpace) :
    spatialDivergence
        (finiteModeReconstructedVelocity
          (fun i y =>
            finiteModePolynomialVectorFieldEval
              (finiteModeDiagonalLinearPolynomialMode i) y)
          (finiteModeDiagonalLinearCoefficientCurve lam)) t x =
      t * ∑ i : Fin 3, lam i :=
  finiteModeDiagonalLinear_spatialDivergence_eq lam t x

/-- Regression: trace-free diagonal-linear coefficients reconstruct a
divergence-free velocity. -/
theorem finiteModeDiagonalLinear_spatialDivergence_zero_of_trace_regression
    (lam : Fin 3 → ℝ) (htrace : ∑ i : Fin 3, lam i = 0) :
    ∀ t x,
      spatialDivergence
        (finiteModeReconstructedVelocity
          (fun i y =>
            finiteModePolynomialVectorFieldEval
              (finiteModeDiagonalLinearPolynomialMode i) y)
          (finiteModeDiagonalLinearCoefficientCurve lam)) t x = 0 :=
  finiteModeDiagonalLinear_spatialDivergence_zero_of_trace lam htrace

/-- Regression: trace-free diagonal-linear velocity families close momentum and
are incompressible. -/
theorem finiteModeDiagonalLinear_traceFree_reconstructed_velocityAffineQuadraticPressure_momentum_incompressible_exists_regression
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
          ∀ t x, spatialDivergence u t x = 0 :=
  finiteModeDiagonalLinear_traceFree_reconstructed_velocityAffineQuadraticPressure_momentum_incompressible_exists
    ν ε lam htrace

/-- Regression: the symmetric off-diagonal shear reconstruction has the
expected component formula. -/
theorem finiteModeSymmetricShear_reconstructedVelocity_apply_regression
    (α : ℝ) (t : NSTime) (x : NSSpace) (j : Fin 3) :
    finiteModeReconstructedVelocity
        (fun i y =>
          finiteModePolynomialVectorFieldEval
            (finiteModeSymmetricShearPolynomialMode α i) y)
        finiteModeIdentityCoefficientCurve t x j =
      if j = (0 : Fin 3) then α * t * x (1 : Fin 3)
      else if j = (1 : Fin 3) then α * t * x (0 : Fin 3)
      else 0 :=
  finiteModeSymmetricShear_reconstructedVelocity_apply α t x j

/-- Regression: the symmetric off-diagonal shear closing pressure gradient is
affine-quadratic. -/
theorem finiteModeSymmetricShearPolynomialClosingPressureGradient_affine_eq_regression
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
        (finiteModeSymmetricShearAffinePressureMatrix α t) :=
  finiteModeSymmetricShearPolynomialClosingPressureGradient_affine_eq ν α t

/-- Regression: the symmetric off-diagonal shear reconstruction is
divergence-free. -/
theorem finiteModeSymmetricShear_reconstructed_spatialDivergence_zero_regression
    (α : ℝ) :
    ∀ t x,
      spatialDivergence
        (finiteModeReconstructedVelocity
          (fun i y =>
            finiteModePolynomialVectorFieldEval
              (finiteModeSymmetricShearPolynomialMode α i) y)
          finiteModeIdentityCoefficientCurve) t x = 0 :=
  finiteModeSymmetricShear_reconstructed_spatialDivergence_zero α

/-- Regression: the symmetric off-diagonal shear mode closes momentum through
finite affine-quadratic pressure and is incompressible. -/
theorem finiteModeSymmetricShear_reconstructed_velocityAffineQuadraticPressure_momentum_incompressible_exists_regression
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
          ∀ t x, spatialDivergence u t x = 0 :=
  finiteModeSymmetricShear_reconstructed_velocityAffineQuadraticPressure_momentum_incompressible_exists
    ν ε α

/-- Regression: the matrix-linear reconstruction has component formula
`u_j(t,x)=t Σ_k A_{jk}x_k`. -/
theorem finiteModeLinearMatrix_reconstructedVelocity_apply_regression
    (A : Fin 3 → Fin 3 → ℝ) (t : NSTime) (x : NSSpace) (j : Fin 3) :
    finiteModeReconstructedVelocity
        (fun i y =>
          finiteModePolynomialVectorFieldEval
            (finiteModeLinearMatrixPolynomialMode A i) y)
        finiteModeIdentityCoefficientCurve t x j =
      t * ∑ k : Fin 3, A j k * x k :=
  finiteModeLinearMatrix_reconstructedVelocity_apply A t x j

/-- Regression: the matrix-linear computed closing gradient is affine with
matrix `-(A+t^2A^2)`. -/
theorem finiteModeLinearMatrixPolynomialClosingPressureGradient_affine_eq_regression
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
        (finiteModeLinearMatrixAffinePressureMatrix A t) :=
  finiteModeLinearMatrixPolynomialClosingPressureGradient_affine_eq ν A t

/-- Regression: matrix-linear reconstructed divergence is `t * trace A`. -/
theorem finiteModeLinearMatrix_spatialDivergence_eq_regression
    (A : Fin 3 → Fin 3 → ℝ) (t : NSTime) (x : NSSpace) :
    spatialDivergence
        (finiteModeReconstructedVelocity
          (fun i y =>
            finiteModePolynomialVectorFieldEval
              (finiteModeLinearMatrixPolynomialMode A i) y)
          finiteModeIdentityCoefficientCurve) t x =
      t * ∑ i : Fin 3, A i i :=
  finiteModeLinearMatrix_spatialDivergence_eq A t x

/-- Regression: the exact affine-symmetry condition on the computed closing
matrix is sufficient for finite pressure closure and incompressibility. -/
theorem finiteModeLinearMatrix_traceFreeAffineSymmetric_reconstructed_velocityAffineQuadraticPressure_momentum_incompressible_exists_regression
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
          ∀ t x, spatialDivergence u t x = 0 :=
  finiteModeLinearMatrix_traceFreeAffineSymmetric_reconstructed_velocityAffineQuadraticPressure_momentum_incompressible_exists
    ν ε A hclosure htrace

/-- Regression: symmetric trace-free matrix-linear fields close momentum
through finite affine-quadratic pressure and are incompressible. -/
theorem finiteModeLinearMatrix_traceFreeSymmetric_reconstructed_velocityAffineQuadraticPressure_momentum_incompressible_exists_regression
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
          ∀ t x, spatialDivergence u t x = 0 :=
  finiteModeLinearMatrix_traceFreeSymmetric_reconstructed_velocityAffineQuadraticPressure_momentum_incompressible_exists
    ν ε A hA htrace

/-- Concrete nonconstant polynomial-mode reconstruction closed by the explicit
polynomial pressure primitive. -/
theorem finiteModeRadialLinear_reconstructed_velocityPolynomialPressure_momentum_exists_regression
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
              ν • spatialLaplacian u t x :=
  finiteModeRadialLinear_reconstructed_velocityPolynomialPressure_momentum_exists ν ε

/-- A one-mode coefficient solution with an affine curl-free non-pressure defect
constructs affine-quadratic pressure coefficients and reconstructs local
pointwise momentum. -/
theorem oneModeProjectedNS_local_reconstructed_velocityPressure_momentum_of_affineHelmholtz_regression
    (ν : ℝ)
    (mode : PUnit → NSSpace → NSSpace)
    (C : FiniteModeProjectedNSCoefficients PUnit)
    (a : ℝ → FiniteModeState PUnit)
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
              ν • spatialLaplacian u t x :=
  finiteModeProjectedNS_local_reconstructed_velocityPressure_momentum_of_affineHelmholtz
    ν mode C a ε ha c A hA hdefect

/-- For polynomial one-mode spatial modes, an affine symmetric computed
closing gradient constructs affine-quadratic finite pressure coefficients and
reconstructs local pointwise momentum. -/
theorem oneModeProjectedNS_local_reconstructed_velocityAffineQuadraticPressure_momentum_of_polynomialModes_affineClosingGradient_regression
    (ν : ℝ)
    (modePoly : PUnit → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (C : FiniteModeProjectedNSCoefficients PUnit)
    (a : ℝ → FiniteModeState PUnit)
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
              ν • spatialLaplacian u t x :=
  finiteModeProjectedNS_local_reconstructed_velocityAffineQuadraticPressure_momentum_of_polynomialModes_affineClosingGradient
    ν modePoly C a ε ha c A hA hclosing

/-- A one-mode coefficient solution whose non-pressure residual is closed by a
constant-gradient coordinate pressure reconstructs to local pointwise momentum. -/
theorem oneModeProjectedNS_local_reconstructed_velocityCoordinatePressure_momentum_regression
    (ν : ℝ)
    (mode : PUnit → NSSpace → NSSpace)
    (C : FiniteModeProjectedNSCoefficients PUnit)
    (a : ℝ → FiniteModeState PUnit)
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
              ν • spatialLaplacian u t x :=
  finiteModeProjectedNS_local_reconstructed_velocityCoordinatePressure_momentum_of_constantGradient_balance
    ν mode C a c ε ha hbalance

/-- A one-mode coefficient solution whose non-pressure residual is closed by a
diagonal linear-in-space pressure gradient reconstructs to local pointwise
momentum using the nonconstant quadratic pressure modes. -/
theorem oneModeProjectedNS_local_reconstructed_velocityDiagonalQuadraticPressure_momentum_regression
    (ν : ℝ)
    (mode : PUnit → NSSpace → NSSpace)
    (C : FiniteModeProjectedNSCoefficients PUnit)
    (a : ℝ → FiniteModeState PUnit)
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
              ν • spatialLaplacian u t x :=
  finiteModeProjectedNS_local_reconstructed_velocityDiagonalQuadraticPressure_momentum_of_diagonalLinearGradient_balance
    ν mode C a d ε ha hbalance

/-- Global time-dependent matrix-linear finite-mode velocities retain the
explicit pointwise momentum identity. -/
theorem finiteModeLinearMatrix_timeDependent_pointwise_momentum_regression
    (ν : ℝ) (A : Fin 3 → Fin 3 → ℝ) (g gdot : NSTime → ℝ)
    (hA : ∀ i j, A i j = A j i)
    (hg : ∀ t : NSTime, HasDerivAt g (gdot t) t) :
    ∀ t x,
      timeVelocityDerivative (finiteModeLinearMatrixTimeVelocity A g) t x +
          spatialConvection (finiteModeLinearMatrixTimeVelocity A g) t x +
            spatialPressureGradient (finiteModeLinearMatrixTimePressure A g gdot) t x =
        ν • spatialLaplacian (finiteModeLinearMatrixTimeVelocity A g) t x :=
  finiteModeLinearMatrix_timeDependent_pointwise_momentum_eq ν A g gdot hA hg

/-- Global time-dependent matrix-linear finite-mode velocities remain
incompressible when the matrix is trace-free. -/
theorem finiteModeLinearMatrix_timeDependent_global_momentum_incompressible_exists_regression
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
            ∀ t x, spatialDivergence u t x = 0 :=
  finiteModeLinearMatrix_timeDependent_global_momentum_incompressible_exists
    ν A g gdot hA htrace hg

/-- Polynomial scalar evaluation is smooth on `NSSpace`. -/
theorem finiteModePolynomialEval_contDiff_top_regression
    (p : MvPolynomial (Fin 3) ℝ) :
    ContDiff ℝ ∞ (fun y : NSSpace => MvPolynomial.eval y p) :=
  finiteModePolynomialEval_contDiff_top p

/-- Polynomial vector fields are smooth on `NSSpace`. -/
theorem finiteModePolynomialVectorFieldEval_contDiff_top_regression
    (U : Fin 3 → MvPolynomial (Fin 3) ℝ) :
    ContDiff ℝ ∞ (finiteModePolynomialVectorFieldEval U) :=
  finiteModePolynomialVectorFieldEval_contDiff_top U

/-- Smooth coefficient curves and smooth spatial modes reconstruct to a smooth
space-time velocity. -/
theorem finiteModeReconstructedVelocity_smoothSpaceTime_regression
    {ι : Type*} [Fintype ι]
    (mode : ι → NSSpace → NSSpace) (a : ℝ → FiniteModeState ι)
    (ha : ∀ i, ContDiff ℝ ∞ (fun t : NSTime => a t i))
    (hmode : ∀ i, ContDiff ℝ ∞ (mode i)) :
    smoothSpaceTimeVelocity (finiteModeReconstructedVelocity mode a) :=
  finiteModeReconstructedVelocity_smoothSpaceTime mode a ha hmode

/-- Smooth pressure coefficient curves and smooth pressure modes reconstruct to
a smooth space-time pressure. -/
theorem finiteModeReconstructedPressure_smoothSpaceTime_regression
    {κ : Type*} [Fintype κ]
    (pressureMode : κ → NSSpace → ℝ) (b : ℝ → FiniteModeState κ)
    (hb : ∀ k, ContDiff ℝ ∞ (fun t : NSTime => b t k))
    (hmode : ∀ k, ContDiff ℝ ∞ (pressureMode k)) :
    smoothSpaceTimePressure (finiteModeReconstructedPressure pressureMode b) :=
  finiteModeReconstructedPressure_smoothSpaceTime pressureMode b hb hmode

/-- Smooth amplitudes give smooth time-dependent matrix-linear velocities. -/
theorem finiteModeLinearMatrix_timeDependent_smoothSpaceTimeVelocity_regression
    (A : Fin 3 → Fin 3 → ℝ) (g : NSTime → ℝ)
    (hg : ContDiff ℝ ∞ g) :
    smoothSpaceTimeVelocity (finiteModeLinearMatrixTimeVelocity A g) :=
  finiteModeLinearMatrix_timeDependent_smoothSpaceTimeVelocity A g hg

/-- Smooth amplitudes and derivative data give a smooth explicit pressure for
the time-dependent matrix-linear construction. -/
theorem finiteModeLinearMatrix_timeDependent_smoothSpaceTimePressure_regression
    (A : Fin 3 → Fin 3 → ℝ) (g gdot : NSTime → ℝ)
    (hg : ContDiff ℝ ∞ g) (hgdot : ContDiff ℝ ∞ gdot) :
    smoothSpaceTimePressure (finiteModeLinearMatrixTimePressure A g gdot) :=
  finiteModeLinearMatrix_timeDependent_smoothSpaceTimePressure A g gdot hg hgdot

/-- Smooth time-dependent matrix-linear finite-mode fields package smooth
regularity, pointwise momentum, and incompressibility. -/
theorem finiteModeLinearMatrix_timeDependent_global_smooth_momentum_incompressible_exists_regression
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
                ∀ t x, spatialDivergence u t x = 0 :=
  finiteModeLinearMatrix_timeDependent_global_smooth_momentum_incompressible_exists
    ν A g gdot hA htrace hg hgdot hderiv

/-- Linear-map kinetic-energy densities are continuous. -/
theorem finiteModeLinearMapKineticEnergyDensity_continuous_regression
    (L : NSSpace →L[ℝ] NSSpace) :
    Continuous (finiteModeLinearMapKineticEnergyDensity L) :=
  finiteModeLinearMapKineticEnergyDensity_continuous L

/-- Nonzero linear profiles have nonintegrable kinetic-energy density on
`ℝ^3`. -/
theorem not_integrable_finiteModeLinearMapKineticEnergyDensity_regression
    {L : NSSpace →L[ℝ] NSSpace}
    (hL : L ≠ 0) :
    ¬ MeasureTheory.Integrable (finiteModeLinearMapKineticEnergyDensity L) :=
  not_integrable_finiteModeLinearMapKineticEnergyDensity hL

/-- Matrix entries are exposed by the associated continuous linear map. -/
theorem finiteModeLinearMatrixCLM_apply_regression
    (A : Fin 3 → Fin 3 → ℝ) (x : NSSpace) (i : Fin 3) :
    finiteModeLinearMatrixCLM A x i = ∑ j : Fin 3, A i j * x j :=
  finiteModeLinearMatrixCLM_apply A x i

/-- A matrix with a nonzero entry gives a nonzero continuous linear map. -/
theorem finiteModeLinearMatrixCLM_ne_zero_of_entry_ne_regression
    {A : Fin 3 → Fin 3 → ℝ} {i j : Fin 3}
    (hA : A i j ≠ 0) :
    finiteModeLinearMatrixCLM A ≠ 0 :=
  finiteModeLinearMatrixCLM_ne_zero_of_entry_ne hA

/-- Time-dependent matrix-linear velocities have the expected component
formula. -/
theorem finiteModeLinearMatrixTimeVelocity_apply_regression
    (A : Fin 3 → Fin 3 → ℝ) (g : NSTime → ℝ)
    (t : NSTime) (x : NSSpace) (j : Fin 3) :
    finiteModeLinearMatrixTimeVelocity A g t x j =
      g t * ∑ k : Fin 3, A j k * x k :=
  finiteModeLinearMatrixTimeVelocity_apply A g t x j

/-- Time-slice kinetic energy for matrix-linear modes is the linear-map
kinetic-energy density of `(g(t))A`. -/
theorem kineticEnergyDensity_finiteModeLinearMatrixTimeVelocity_regression
    (A : Fin 3 → Fin 3 → ℝ) (g : NSTime → ℝ) (t : NSTime) :
    kineticEnergyDensity (finiteModeLinearMatrixTimeVelocity A g) t =
      finiteModeLinearMapKineticEnergyDensity ((g t) • finiteModeLinearMatrixCLM A) :=
  kineticEnergyDensity_finiteModeLinearMatrixTimeVelocity A g t

/-- Active matrix-linear modes have nonintegrable kinetic-energy density on
active time slices. -/
theorem not_integrable_kineticEnergyDensity_finiteModeLinearMatrixTimeVelocity_regression
    {A : Fin 3 → Fin 3 → ℝ} {g : NSTime → ℝ} {t : NSTime}
    (hA : ∃ i j : Fin 3, A i j ≠ 0)
    (hg : g t ≠ 0) :
    ¬ MeasureTheory.Integrable
      (kineticEnergyDensity (finiteModeLinearMatrixTimeVelocity A g) t) :=
  not_integrable_kineticEnergyDensity_finiteModeLinearMatrixTimeVelocity hA hg

/-- Genuinely active matrix-linear modes fail global bounded kinetic energy. -/
theorem not_boundedKineticEnergy_finiteModeLinearMatrixTimeVelocity_regression
    {A : Fin 3 → Fin 3 → ℝ} {g : NSTime → ℝ}
    (hA : ∃ i j : Fin 3, A i j ≠ 0)
    (hg : ∃ t : NSTime, g t ≠ 0) :
    ¬ boundedKineticEnergy (finiteModeLinearMatrixTimeVelocity A g) :=
  not_boundedKineticEnergy_finiteModeLinearMatrixTimeVelocity hA hg

/-- Active matrix-linear initial slices are not finite-energy admissible. -/
theorem not_finiteInitialKineticEnergy_finiteModeLinearMatrixTimeVelocity_initial_regression
    {A : Fin 3 → Fin 3 → ℝ} {g : NSTime → ℝ}
    (hA : ∃ i j : Fin 3, A i j ≠ 0)
    (hg0 : g 0 ≠ 0) :
    ¬ finiteInitialKineticEnergy (fun x : NSSpace => finiteModeLinearMatrixTimeVelocity A g 0 x) :=
  not_finiteInitialKineticEnergy_finiteModeLinearMatrixTimeVelocity_initial hA hg0

/-- Smooth matrix-linear PDE candidates with active modes package the precise
failure of the concrete bounded-energy predicate. -/
theorem finiteModeLinearMatrix_timeDependent_global_smooth_momentum_incompressible_without_boundedEnergy_exists_regression
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
                  ¬ boundedKineticEnergy u :=
  finiteModeLinearMatrix_timeDependent_global_smooth_momentum_incompressible_without_boundedEnergy_exists
    ν A g gdot hA htrace hAnz hgnz hg hgdot hderiv

end FiniteModeReconstructionRegression

end NavierStokes
end FluidDynamics
end Mettapedia
