import Mettapedia.FluidDynamics.NavierStokes.IdentityEnergy
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Finite-Mode Galerkin Toy ODE

This file isolates the smallest honest finite-dimensional existence object
needed before reconnecting any boxed periodization route: a finite collection
of mode coefficients solving an autonomous quadratic ODE.

No spatial PDE reconstruction is claimed here.  The point is only that the
finite projected system has a polynomial vector field, hence mathlib's
Picard-Lindelof theorem supplies a local solution curve.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open Set
open scoped BigOperators ContDiff

/-- The coefficient vector space for a finite collection of modes. -/
abbrev FiniteModeState (ι : Type*) := ι → ℝ

/-- Coefficients for an autonomous finite-mode projected Navier-Stokes toy
system.  The linear and quadratic coefficients are intentionally abstract:
they represent the projected viscosity and convection tensors after a basis
has been chosen. -/
structure FiniteModeProjectedNSCoefficients (ι : Type*) [Fintype ι] where
  forcing : ι → ℝ
  linear : ι → ι → ℝ
  quadratic : ι → ι → ι → ℝ

/-- The autonomous quadratic right-hand side
`aᵢ' = fᵢ + Σⱼ Lᵢⱼ aⱼ + Σⱼₖ Qᵢⱼₖ aⱼ aₖ`. -/
def finiteModeProjectedNSRHS
    {ι : Type*} [Fintype ι]
    (C : FiniteModeProjectedNSCoefficients ι) :
    FiniteModeState ι → FiniteModeState ι :=
  fun a i =>
    C.forcing i +
      ∑ j, C.linear i j * a j +
        ∑ j, ∑ k, C.quadratic i j k * a j * a k

/-- The finite-mode projected RHS is smooth because each coordinate is a
polynomial in finitely many mode amplitudes. -/
theorem finiteModeProjectedNSRHS_contDiff
    {ι : Type*} [Fintype ι]
    (C : FiniteModeProjectedNSCoefficients ι) :
    ContDiff ℝ ∞ (finiteModeProjectedNSRHS C) := by
  rw [contDiff_pi]
  intro i
  dsimp [finiteModeProjectedNSRHS]
  fun_prop

/-- The finite-mode projected RHS is `C¹` at every initial coefficient vector. -/
theorem finiteModeProjectedNSRHS_contDiffAt_one
    {ι : Type*} [Fintype ι]
    (C : FiniteModeProjectedNSCoefficients ι)
    (a₀ : FiniteModeState ι) :
    ContDiffAt ℝ 1 (finiteModeProjectedNSRHS C) a₀ := by
  exact (finiteModeProjectedNSRHS_contDiff C).contDiffAt.of_le (by norm_num)

/-- The finite coefficient energy, reusing the existing finite
carré-du-champ-style square sum. -/
def finiteModeEnergy
    {ι : Type*} [Fintype ι] (a : FiniteModeState ι) : ℝ :=
  gamma a

/-- Finite-mode coefficient energy is nonnegative. -/
theorem finiteModeEnergy_nonneg
    {ι : Type*} [Fintype ι] (a : FiniteModeState ι) :
    0 ≤ finiteModeEnergy a :=
  gamma_nonneg a

/-- If every coefficient has a time derivative, then the finite coefficient
energy has the expected quadratic derivative. -/
theorem finiteModeEnergy_hasDerivAt_of_component_hasDerivAt
    {ι : Type*} [Fintype ι]
    {a : ℝ → FiniteModeState ι} {v : FiniteModeState ι} {t : ℝ}
    (h : ∀ i, HasDerivAt (fun s : ℝ => a s i) (v i) t) :
    HasDerivAt (fun s : ℝ => finiteModeEnergy (a s))
      (2 * ∑ i, a t i * v i) t := by
  unfold finiteModeEnergy gamma
  have hsumFun :
      HasDerivAt (∑ i, fun s : ℝ => (a s i) ^ 2)
        (∑ i, 2 * (a t i * v i)) t := by
    exact
      (HasDerivAt.sum (u := (Finset.univ : Finset ι))
        (A := fun i s => (a s i) ^ 2)
        (A' := fun i => 2 * (a t i * v i))
        (fun i _ => by
          have hi := (h i).pow 2
          simpa [pow_one, mul_assoc] using hi))
  have hsum :
      HasDerivAt (fun s : ℝ => ∑ i, (a s i) ^ 2)
        (∑ i, 2 * (a t i * v i)) t := by
    convert hsumFun using 1
    ext s
    simp
  have hscale : (∑ i, 2 * (a t i * v i)) = 2 * ∑ i, a t i * v i := by
    rw [Finset.mul_sum]
  simpa [hscale] using hsum

/-- Vector-valued differentiability of a coefficient path gives the same energy
identity. -/
theorem finiteModeEnergy_hasDerivAt_of_hasDerivAt
    {ι : Type*} [Fintype ι]
    {a : ℝ → FiniteModeState ι} {v : FiniteModeState ι} {t : ℝ}
    (ha : HasDerivAt a v t) :
    HasDerivAt (fun s : ℝ => finiteModeEnergy (a s))
      (2 * ∑ i, a t i * v i) t :=
  finiteModeEnergy_hasDerivAt_of_component_hasDerivAt (hasDerivAt_pi.mp ha)

/-- Along a finite-mode projected ODE solution, the coefficient-energy
derivative is twice the coefficient/RHS pairing. -/
theorem finiteModeEnergy_hasDerivAt_of_projectedNS
    {ι : Type*} [Fintype ι]
    (C : FiniteModeProjectedNSCoefficients ι)
    {a : ℝ → FiniteModeState ι} {t : ℝ}
    (ha : HasDerivAt a (finiteModeProjectedNSRHS C (a t)) t) :
    HasDerivAt (fun s : ℝ => finiteModeEnergy (a s))
      (2 * ∑ i, a t i * finiteModeProjectedNSRHS C (a t) i) t :=
  finiteModeEnergy_hasDerivAt_of_hasDerivAt ha

/-- The zero coefficient curve for any finite mode index set. -/
def finiteModeZeroCurve {ι : Type*} [Fintype ι] : ℝ → FiniteModeState ι :=
  fun _ => 0

/-- At the zero coefficient vector the projected RHS is exactly the forcing
term; all linear and quadratic mode interactions vanish. -/
theorem finiteModeProjectedNSRHS_zero
    {ι : Type*} [Fintype ι]
    (C : FiniteModeProjectedNSCoefficients ι) :
    finiteModeProjectedNSRHS C (0 : FiniteModeState ι) = C.forcing := by
  funext i
  simp [finiteModeProjectedNSRHS]

/-- The zero coefficient vector is an equilibrium exactly when every forcing
coefficient vanishes. -/
theorem finiteModeProjectedNSRHS_zero_eq_zero_iff
    {ι : Type*} [Fintype ι]
    (C : FiniteModeProjectedNSCoefficients ι) :
    finiteModeProjectedNSRHS C (0 : FiniteModeState ι) = 0 ↔
      ∀ i, C.forcing i = 0 := by
  constructor
  · intro h i
    have hi := congr_fun h i
    simpa [finiteModeProjectedNSRHS] using hi
  · intro h
    funext i
    simp [finiteModeProjectedNSRHS, h i]

/-- At any time, the zero coefficient curve solves the projected ODE exactly
when the forcing vector is zero. -/
theorem finiteModeZeroCurve_hasDerivAt_iff_forcing_zero
    {ι : Type*} [Fintype ι]
    (C : FiniteModeProjectedNSCoefficients ι) (t : ℝ) :
    HasDerivAt (finiteModeZeroCurve : ℝ → FiniteModeState ι)
        (finiteModeProjectedNSRHS C (finiteModeZeroCurve t)) t ↔
      ∀ i, C.forcing i = 0 := by
  constructor
  · intro h i
    have hconst : HasDerivAt (finiteModeZeroCurve : ℝ → FiniteModeState ι) 0 t := by
      simpa [finiteModeZeroCurve] using
        (hasDerivAt_const (𝕜 := ℝ) t (0 : FiniteModeState ι))
    have hzero :
        finiteModeProjectedNSRHS C (finiteModeZeroCurve t) = 0 := h.unique hconst
    exact
      (finiteModeProjectedNSRHS_zero_eq_zero_iff C).mp
        (by simpa [finiteModeZeroCurve] using hzero) i
  · intro hforcing
    change HasDerivAt (fun _ : ℝ => (0 : FiniteModeState ι))
      (finiteModeProjectedNSRHS C (0 : FiniteModeState ι)) t
    rw [(finiteModeProjectedNSRHS_zero_eq_zero_iff C).mpr hforcing]
    exact hasDerivAt_const t (0 : FiniteModeState ι)

/-- The zero coefficient curve is a global solution of the finite projected
ODE exactly for unforced systems. -/
theorem finiteModeZeroCurve_solves_iff_forcing_zero
    {ι : Type*} [Fintype ι]
    (C : FiniteModeProjectedNSCoefficients ι) :
    (∀ t : ℝ,
        HasDerivAt (finiteModeZeroCurve : ℝ → FiniteModeState ι)
          (finiteModeProjectedNSRHS C (finiteModeZeroCurve t)) t) ↔
      ∀ i, C.forcing i = 0 := by
  constructor
  · intro h
    exact (finiteModeZeroCurve_hasDerivAt_iff_forcing_zero C 0).mp (h 0)
  · intro h t
    exact (finiteModeZeroCurve_hasDerivAt_iff_forcing_zero C t).mpr h

/-- A single nonzero forcing coefficient blocks the zero coefficient curve from
being a global solution of the projected ODE. -/
theorem not_forall_finiteModeZeroCurve_hasDerivAt_of_forcing_ne_zero
    {ι : Type*} [Fintype ι]
    (C : FiniteModeProjectedNSCoefficients ι) {i : ι}
    (hforce : C.forcing i ≠ 0) :
    ¬ ∀ t : ℝ,
        HasDerivAt (finiteModeZeroCurve : ℝ → FiniteModeState ι)
          (finiteModeProjectedNSRHS C (finiteModeZeroCurve t)) t := by
  intro hsol
  exact hforce ((finiteModeZeroCurve_solves_iff_forcing_zero C).mp hsol i)

/-- Constant coefficient curve through a fixed finite-mode state. -/
def finiteModeConstantCurve {ι : Type*} [Fintype ι]
    (a₀ : FiniteModeState ι) : ℝ → FiniteModeState ι :=
  fun _ => a₀

/-- At any time, a constant coefficient curve solves the projected ODE exactly
when the projected RHS vanishes at that fixed coefficient state. -/
theorem finiteModeConstantCurve_hasDerivAt_iff_rhs_eq_zero
    {ι : Type*} [Fintype ι]
    (C : FiniteModeProjectedNSCoefficients ι) (a₀ : FiniteModeState ι) (t : ℝ) :
    HasDerivAt (finiteModeConstantCurve a₀)
        (finiteModeProjectedNSRHS C (finiteModeConstantCurve a₀ t)) t ↔
      finiteModeProjectedNSRHS C a₀ = 0 := by
  constructor
  · intro h
    have hconst : HasDerivAt (finiteModeConstantCurve a₀) 0 t := by
      simpa [finiteModeConstantCurve] using
        (hasDerivAt_const (𝕜 := ℝ) t a₀)
    simpa [finiteModeConstantCurve] using h.unique hconst
  · intro hres
    change HasDerivAt (fun _ : ℝ => a₀) (finiteModeProjectedNSRHS C a₀) t
    rw [hres]
    exact hasDerivAt_const t a₀

/-- A constant coefficient curve is a global solution of the finite projected
ODE exactly when its fixed coefficient state is an equilibrium of the projected
RHS. -/
theorem finiteModeConstantCurve_solves_iff_rhs_eq_zero
    {ι : Type*} [Fintype ι]
    (C : FiniteModeProjectedNSCoefficients ι) (a₀ : FiniteModeState ι) :
    (∀ t : ℝ,
        HasDerivAt (finiteModeConstantCurve a₀)
          (finiteModeProjectedNSRHS C (finiteModeConstantCurve a₀ t)) t) ↔
      finiteModeProjectedNSRHS C a₀ = 0 := by
  constructor
  · intro h
    exact (finiteModeConstantCurve_hasDerivAt_iff_rhs_eq_zero C a₀ 0).mp (h 0)
  · intro h t
    exact (finiteModeConstantCurve_hasDerivAt_iff_rhs_eq_zero C a₀ t).mpr h

/-- A constant coefficient curve is a global solution exactly when every
component of the projected RHS vanishes at the fixed coefficient state. -/
theorem finiteModeConstantCurve_solves_iff_forall_rhs_component_eq_zero
    {ι : Type*} [Fintype ι]
    (C : FiniteModeProjectedNSCoefficients ι) (a₀ : FiniteModeState ι) :
    (∀ t : ℝ,
        HasDerivAt (finiteModeConstantCurve a₀)
          (finiteModeProjectedNSRHS C (finiteModeConstantCurve a₀ t)) t) ↔
      ∀ i, finiteModeProjectedNSRHS C a₀ i = 0 := by
  constructor
  · intro h i
    have hzero := (finiteModeConstantCurve_solves_iff_rhs_eq_zero C a₀).mp h
    exact congr_fun hzero i
  · intro h
    exact
      (finiteModeConstantCurve_solves_iff_rhs_eq_zero C a₀).mpr
        (by
          funext i
          exact h i)

/-- A nonzero projected RHS at the fixed coefficient state blocks the
corresponding constant coefficient curve from being a global solution. -/
theorem not_forall_finiteModeConstantCurve_hasDerivAt_of_rhs_ne_zero
    {ι : Type*} [Fintype ι]
    (C : FiniteModeProjectedNSCoefficients ι) (a₀ : FiniteModeState ι)
    (hres : finiteModeProjectedNSRHS C a₀ ≠ 0) :
    ¬ ∀ t : ℝ,
        HasDerivAt (finiteModeConstantCurve a₀)
          (finiteModeProjectedNSRHS C (finiteModeConstantCurve a₀ t)) t := by
  intro hsol
  exact hres ((finiteModeConstantCurve_solves_iff_rhs_eq_zero C a₀).mp hsol)

/-- A single nonzero component of the projected RHS at the fixed coefficient
state blocks the corresponding constant coefficient curve. -/
theorem not_forall_finiteModeConstantCurve_hasDerivAt_of_rhs_component_ne_zero
    {ι : Type*} [Fintype ι]
    (C : FiniteModeProjectedNSCoefficients ι) (a₀ : FiniteModeState ι) {i : ι}
    (hres : finiteModeProjectedNSRHS C a₀ i ≠ 0) :
    ¬ ∀ t : ℝ,
        HasDerivAt (finiteModeConstantCurve a₀)
          (finiteModeProjectedNSRHS C (finiteModeConstantCurve a₀ t)) t := by
  exact
    not_forall_finiteModeConstantCurve_hasDerivAt_of_rhs_ne_zero C a₀
      (by
        intro hzero
        exact hres (congr_fun hzero i))

/-- Pure-forcing projected coefficients: no linear or quadratic interaction,
only a fixed forcing vector. -/
def finiteModePureForcingCoefficients
    {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    FiniteModeProjectedNSCoefficients ι where
  forcing := f
  linear := fun _ _ => 0
  quadratic := fun _ _ _ => 0

/-- The pure-forcing projected RHS is the forcing vector, independently of the
current coefficient state. -/
@[simp]
theorem finiteModeProjectedNSRHS_pureForcing
    {ι : Type*} [Fintype ι]
    (f : ι → ℝ) (a : FiniteModeState ι) :
    finiteModeProjectedNSRHS (finiteModePureForcingCoefficients f) a = f := by
  funext i
  simp [finiteModeProjectedNSRHS, finiteModePureForcingCoefficients]

/-- The affine coefficient curve `a₀ + t f` for a pure-forcing projected
system. -/
def finiteModeAffineForcingCurve
    {ι : Type*} [Fintype ι] (a₀ f : FiniteModeState ι) :
    ℝ → FiniteModeState ι :=
  fun t i => a₀ i + f i * t

/-- The affine pure-forcing curve starts at the prescribed coefficient
vector. -/
@[simp]
theorem finiteModeAffineForcingCurve_zero
    {ι : Type*} [Fintype ι]
    (a₀ f : FiniteModeState ι) :
    finiteModeAffineForcingCurve a₀ f 0 = a₀ := by
  funext i
  simp [finiteModeAffineForcingCurve]

/-- The affine pure-forcing curve solves the pure-forcing projected ODE at
every time. -/
theorem finiteModeAffineForcingCurve_hasDerivAt
    {ι : Type*} [Fintype ι]
    (a₀ f : FiniteModeState ι) (t : ℝ) :
    HasDerivAt (finiteModeAffineForcingCurve a₀ f)
      (finiteModeProjectedNSRHS
        (finiteModePureForcingCoefficients f)
        (finiteModeAffineForcingCurve a₀ f t)) t := by
  rw [hasDerivAt_pi]
  intro i
  simpa [finiteModeAffineForcingCurve] using
    ((hasDerivAt_id t).const_mul (f i)).const_add (a₀ i)

/-- The affine pure-forcing curve is a global solution of the pure-forcing
projected ODE. -/
theorem finiteModeAffineForcingCurve_solves
    {ι : Type*} [Fintype ι]
    (a₀ f : FiniteModeState ι) :
    ∀ t : ℝ,
      HasDerivAt (finiteModeAffineForcingCurve a₀ f)
        (finiteModeProjectedNSRHS
          (finiteModePureForcingCoefficients f)
          (finiteModeAffineForcingCurve a₀ f t)) t :=
  finiteModeAffineForcingCurve_hasDerivAt a₀ f

/-- Decoupled diagonal-linear projected coefficients:
`aᵢ' = λᵢ aᵢ`. -/
def finiteModeDiagonalLinearCoefficients
    {ι : Type*} [Fintype ι] [DecidableEq ι] (lam : ι → ℝ) :
    FiniteModeProjectedNSCoefficients ι where
  forcing := fun _ => 0
  linear := fun i j => if j = i then lam i else 0
  quadratic := fun _ _ _ => 0

/-- The diagonal-linear projected RHS is componentwise multiplication by the
diagonal rate vector. -/
@[simp]
theorem finiteModeProjectedNSRHS_diagonalLinear
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lam : ι → ℝ) (a : FiniteModeState ι) (i : ι) :
    finiteModeProjectedNSRHS (finiteModeDiagonalLinearCoefficients lam) a i =
      lam i * a i := by
  simp [finiteModeProjectedNSRHS, finiteModeDiagonalLinearCoefficients]

/-- The exponential coefficient curve solving the diagonal-linear projected
system. -/
def finiteModeDiagonalLinearExpCurve
    {ι : Type*} [Fintype ι] (lam a₀ : FiniteModeState ι) :
    ℝ → FiniteModeState ι :=
  fun t i => a₀ i * Real.exp (lam i * t)

/-- The diagonal-linear exponential curve starts at the prescribed coefficient
vector. -/
@[simp]
theorem finiteModeDiagonalLinearExpCurve_zero
    {ι : Type*} [Fintype ι]
    (lam a₀ : FiniteModeState ι) :
    finiteModeDiagonalLinearExpCurve lam a₀ 0 = a₀ := by
  funext i
  simp [finiteModeDiagonalLinearExpCurve]

/-- The diagonal-linear exponential curve solves the decoupled linear
projected ODE at every time. -/
theorem finiteModeDiagonalLinearExpCurve_hasDerivAt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lam a₀ : FiniteModeState ι) (t : ℝ) :
    HasDerivAt (finiteModeDiagonalLinearExpCurve lam a₀)
      (finiteModeProjectedNSRHS
        (finiteModeDiagonalLinearCoefficients lam)
        (finiteModeDiagonalLinearExpCurve lam a₀ t)) t := by
  rw [hasDerivAt_pi]
  intro i
  have hlin : HasDerivAt (fun s : ℝ => lam i * s) (lam i) t := by
    simpa using (hasDerivAt_id t).const_mul (lam i)
  have hexp :
      HasDerivAt
        (fun s : ℝ => a₀ i * Real.exp (lam i * s))
        (lam i * (a₀ i * Real.exp (lam i * t))) t := by
    convert hlin.exp.const_mul (a₀ i) using 1
    ring
  simpa [finiteModeDiagonalLinearExpCurve, mul_assoc, mul_left_comm, mul_comm] using hexp

/-- The diagonal-linear exponential curve is a global solution of the
decoupled linear projected ODE. -/
theorem finiteModeDiagonalLinearExpCurve_solves
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lam a₀ : FiniteModeState ι) :
    ∀ t : ℝ,
      HasDerivAt (finiteModeDiagonalLinearExpCurve lam a₀)
        (finiteModeProjectedNSRHS
          (finiteModeDiagonalLinearCoefficients lam)
          (finiteModeDiagonalLinearExpCurve lam a₀ t)) t :=
  finiteModeDiagonalLinearExpCurve_hasDerivAt lam a₀

/-- The energy pairing for a diagonal-linear projected RHS is the expected
weighted square sum. -/
theorem finiteModeDiagonalLinearEnergyRHS_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lam a : FiniteModeState ι) :
    2 * ∑ i, a i * finiteModeProjectedNSRHS (finiteModeDiagonalLinearCoefficients lam) a i =
      2 * ∑ i, lam i * (a i) ^ 2 := by
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [finiteModeProjectedNSRHS_diagonalLinear]
  ring

/-- Nonpositive diagonal rates make the diagonal-linear projected RHS
dissipative for the finite coefficient energy. -/
theorem finiteModeDiagonalLinearEnergyRHS_nonpos
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lam a : FiniteModeState ι) (hLam : ∀ i, lam i ≤ 0) :
    2 * ∑ i, a i * finiteModeProjectedNSRHS (finiteModeDiagonalLinearCoefficients lam) a i ≤
      0 := by
  rw [finiteModeDiagonalLinearEnergyRHS_eq]
  have hsum : ∑ i, lam i * (a i) ^ 2 ≤ 0 := by
    calc
      ∑ i, lam i * (a i) ^ 2 ≤ ∑ _i : ι, (0 : ℝ) := by
        refine Finset.sum_le_sum ?_
        intro i _
        nlinarith [hLam i, sq_nonneg (a i)]
      _ = 0 := by simp
  nlinarith

/-- The diagonal-linear exponential solution has the exact finite-energy
derivative dictated by its diagonal rates. -/
theorem finiteModeDiagonalLinearExpCurve_energy_hasDerivAt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lam a₀ : FiniteModeState ι) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => finiteModeEnergy (finiteModeDiagonalLinearExpCurve lam a₀ s))
      (2 * ∑ i, lam i * (finiteModeDiagonalLinearExpCurve lam a₀ t i) ^ 2) t := by
  have h :=
    finiteModeEnergy_hasDerivAt_of_projectedNS
      (finiteModeDiagonalLinearCoefficients lam)
      (finiteModeDiagonalLinearExpCurve_hasDerivAt lam a₀ t)
  convert h using 1
  apply congrArg (fun x => 2 * x)
  apply Finset.sum_congr rfl
  intro i _
  rw [finiteModeProjectedNSRHS_diagonalLinear]
  ring

/-- Decoupled diagonal-affine projected coefficients:
`aᵢ' = fᵢ + λᵢ aᵢ`. -/
def finiteModeDiagonalAffineCoefficients
    {ι : Type*} [Fintype ι] [DecidableEq ι] (lam f : ι → ℝ) :
    FiniteModeProjectedNSCoefficients ι where
  forcing := f
  linear := fun i j => if j = i then lam i else 0
  quadratic := fun _ _ _ => 0

/-- The diagonal-affine projected RHS is the prescribed forcing plus
componentwise diagonal multiplication. -/
@[simp]
theorem finiteModeProjectedNSRHS_diagonalAffine
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lam f : ι → ℝ) (a : FiniteModeState ι) (i : ι) :
    finiteModeProjectedNSRHS (finiteModeDiagonalAffineCoefficients lam f) a i =
      f i + lam i * a i := by
  simp [finiteModeProjectedNSRHS, finiteModeDiagonalAffineCoefficients]

/-- The explicit equilibrium-centered solution curve for a decoupled
diagonal-affine projected system. -/
def finiteModeDiagonalAffineEquilibriumCurve
    {ι : Type*} [Fintype ι] (lam aEq a₀ : FiniteModeState ι) :
    ℝ → FiniteModeState ι :=
  fun t i => aEq i + (a₀ i - aEq i) * Real.exp (lam i * t)

/-- The equilibrium-centered diagonal-affine curve starts at the prescribed
coefficient vector. -/
@[simp]
theorem finiteModeDiagonalAffineEquilibriumCurve_zero
    {ι : Type*} [Fintype ι]
    (lam aEq a₀ : FiniteModeState ι) :
    finiteModeDiagonalAffineEquilibriumCurve lam aEq a₀ 0 = a₀ := by
  funext i
  simp [finiteModeDiagonalAffineEquilibriumCurve]

/-- If `aEq` is an equilibrium of the decoupled diagonal-affine projected
system, the equilibrium-centered exponential curve solves the projected ODE at
every time. -/
theorem finiteModeDiagonalAffineEquilibriumCurve_hasDerivAt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lam f aEq a₀ : FiniteModeState ι)
    (hEq : ∀ i, f i + lam i * aEq i = 0) (t : ℝ) :
    HasDerivAt (finiteModeDiagonalAffineEquilibriumCurve lam aEq a₀)
      (finiteModeProjectedNSRHS
        (finiteModeDiagonalAffineCoefficients lam f)
        (finiteModeDiagonalAffineEquilibriumCurve lam aEq a₀ t)) t := by
  rw [hasDerivAt_pi]
  intro i
  have hlin : HasDerivAt (fun s : ℝ => lam i * s) (lam i) t := by
    simpa using (hasDerivAt_id t).const_mul (lam i)
  have hexp :
      HasDerivAt
        (fun s : ℝ => aEq i + (a₀ i - aEq i) * Real.exp (lam i * s))
        (lam i * ((a₀ i - aEq i) * Real.exp (lam i * t))) t := by
    have hbase :
        HasDerivAt
          (fun s : ℝ => (a₀ i - aEq i) * Real.exp (lam i * s))
          (lam i * ((a₀ i - aEq i) * Real.exp (lam i * t))) t := by
      convert hlin.exp.const_mul (a₀ i - aEq i) using 1
      ring
    exact hbase.const_add (aEq i)
  have hrhs :
      finiteModeProjectedNSRHS
        (finiteModeDiagonalAffineCoefficients lam f)
        (finiteModeDiagonalAffineEquilibriumCurve lam aEq a₀ t) i =
        lam i * ((a₀ i - aEq i) * Real.exp (lam i * t)) := by
    calc
      finiteModeProjectedNSRHS
          (finiteModeDiagonalAffineCoefficients lam f)
          (finiteModeDiagonalAffineEquilibriumCurve lam aEq a₀ t) i
          = f i +
              lam i * (aEq i + (a₀ i - aEq i) * Real.exp (lam i * t)) := by
              simp [finiteModeDiagonalAffineEquilibriumCurve]
      _ = (f i + lam i * aEq i) +
            lam i * ((a₀ i - aEq i) * Real.exp (lam i * t)) := by
          ring
      _ = lam i * ((a₀ i - aEq i) * Real.exp (lam i * t)) := by
          rw [hEq i]
          ring
  simpa [finiteModeDiagonalAffineEquilibriumCurve, hrhs] using hexp

/-- The equilibrium-centered diagonal-affine curve is a global solution when
the chosen center is an equilibrium. -/
theorem finiteModeDiagonalAffineEquilibriumCurve_solves
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lam f aEq a₀ : FiniteModeState ι)
    (hEq : ∀ i, f i + lam i * aEq i = 0) :
    ∀ t : ℝ,
      HasDerivAt (finiteModeDiagonalAffineEquilibriumCurve lam aEq a₀)
        (finiteModeProjectedNSRHS
          (finiteModeDiagonalAffineCoefficients lam f)
          (finiteModeDiagonalAffineEquilibriumCurve lam aEq a₀ t)) t :=
  finiteModeDiagonalAffineEquilibriumCurve_hasDerivAt lam f aEq a₀ hEq

/-- A local solution curve exists for every finite-mode projected quadratic
system and every initial coefficient vector.  This is the precise Picard
object missing before any finite-mode PDE reconstruction step. -/
theorem finiteModeProjectedNSRHS_local_solution_exists
    {ι : Type*} [Fintype ι]
    (C : FiniteModeProjectedNSCoefficients ι)
    (a₀ : FiniteModeState ι) :
    ∃ a : ℝ → FiniteModeState ι, a 0 = a₀ ∧ ∃ ε > (0 : ℝ),
      ∀ t ∈ Ioo (-ε) ε, HasDerivAt a (finiteModeProjectedNSRHS C (a t)) t := by
  simpa [sub_eq_add_neg] using
    (ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀
      (finiteModeProjectedNSRHS_contDiffAt_one C a₀) 0)

end NavierStokes
end FluidDynamics
end Mettapedia
