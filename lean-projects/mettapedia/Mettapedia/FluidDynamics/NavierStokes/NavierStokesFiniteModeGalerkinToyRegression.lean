import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeGalerkinToy

/-!
# Regression Tests for the Finite-Mode Galerkin Toy ODE
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open Set
open scoped ContDiff

section FiniteModeGalerkinToyRegression

/-- The finite-mode RHS stays smooth for arbitrary abstract coefficients. -/
theorem finiteModeProjectedNSRHS_smooth_regression
    {ι : Type*} [Fintype ι]
    (C : FiniteModeProjectedNSCoefficients ι) :
    ContDiff ℝ ∞ (finiteModeProjectedNSRHS C) :=
  finiteModeProjectedNSRHS_contDiff C

/-- Even a one-mode quadratic projected system has an actual local solution
curve supplied by Picard-Lindelof. -/
theorem oneModeProjectedNS_local_solution_regression
    (c₀ c₁ c₂ a₀ : ℝ) :
    ∃ a : ℝ → FiniteModeState PUnit, a 0 = (fun _ : PUnit => a₀) ∧ ∃ ε > (0 : ℝ),
      ∀ t ∈ Ioo (-ε) ε,
        HasDerivAt a
          (finiteModeProjectedNSRHS
            ({ forcing := fun _ => c₀
               linear := fun _ _ => c₁
               quadratic := fun _ _ _ => c₂ } :
              FiniteModeProjectedNSCoefficients PUnit)
            (a t)) t := by
  exact
    finiteModeProjectedNSRHS_local_solution_exists
      ({ forcing := fun _ => c₀
         linear := fun _ _ => c₁
         quadratic := fun _ _ _ => c₂ } :
        FiniteModeProjectedNSCoefficients PUnit)
      (fun _ => a₀)

/-- In the one-mode toy system, a nonzero forcing term is enough to rule out
the zero coefficient curve as a global ODE solution. -/
theorem oneModeProjectedNS_zeroCurve_blocked_by_nonzero_forcing_regression :
    ¬ ∀ t : ℝ,
        HasDerivAt (finiteModeZeroCurve : ℝ → FiniteModeState PUnit)
          (finiteModeProjectedNSRHS
            ({ forcing := fun _ => (1 : ℝ)
               linear := fun _ _ => 0
               quadratic := fun _ _ _ => 0 } :
              FiniteModeProjectedNSCoefficients PUnit)
            (finiteModeZeroCurve t)) t := by
  exact
    not_forall_finiteModeZeroCurve_hasDerivAt_of_forcing_ne_zero
      ({ forcing := fun _ => (1 : ℝ)
         linear := fun _ _ => 0
         quadratic := fun _ _ _ => 0 } :
        FiniteModeProjectedNSCoefficients PUnit)
      (i := PUnit.unit) (by norm_num)

/-- The same audit catches any frozen one-mode state whose projected residual
is nonzero, not only the zero coefficient state. -/
theorem oneModeProjectedNS_constantCurve_blocked_by_nonzero_residual_regression :
    ¬ ∀ t : ℝ,
        HasDerivAt (finiteModeConstantCurve (fun _ : PUnit => (2 : ℝ)))
          (finiteModeProjectedNSRHS
            ({ forcing := fun _ => (1 : ℝ)
               linear := fun _ _ => 0
               quadratic := fun _ _ _ => 0 } :
              FiniteModeProjectedNSCoefficients PUnit)
            (finiteModeConstantCurve (fun _ : PUnit => (2 : ℝ)) t)) t := by
  refine
    not_forall_finiteModeConstantCurve_hasDerivAt_of_rhs_ne_zero
      ({ forcing := fun _ => (1 : ℝ)
         linear := fun _ _ => 0
         quadratic := fun _ _ _ => 0 } :
        FiniteModeProjectedNSCoefficients PUnit)
      (fun _ : PUnit => (2 : ℝ)) ?_
  intro h
  have hunit := congr_fun h PUnit.unit
  norm_num [finiteModeProjectedNSRHS] at hunit

/-- The componentwise residual blocker avoids constructing a whole-vector
inequality when a single projected coordinate is visibly nonzero. -/
theorem oneModeProjectedNS_constantCurve_blocked_by_nonzero_residual_component_regression :
    ¬ ∀ t : ℝ,
        HasDerivAt (finiteModeConstantCurve (fun _ : PUnit => (2 : ℝ)))
          (finiteModeProjectedNSRHS
            ({ forcing := fun _ => (1 : ℝ)
               linear := fun _ _ => 0
               quadratic := fun _ _ _ => 0 } :
              FiniteModeProjectedNSCoefficients PUnit)
            (finiteModeConstantCurve (fun _ : PUnit => (2 : ℝ)) t)) t := by
  exact
    not_forall_finiteModeConstantCurve_hasDerivAt_of_rhs_component_ne_zero
      ({ forcing := fun _ => (1 : ℝ)
         linear := fun _ _ => 0
         quadratic := fun _ _ _ => 0 } :
        FiniteModeProjectedNSCoefficients PUnit)
      (fun _ : PUnit => (2 : ℝ)) (i := PUnit.unit)
      (by norm_num [finiteModeProjectedNSRHS])

/-- Pure forcing has the expected affine global solution curve in every finite
mode dimension. -/
theorem finiteModeAffineForcingCurve_hasDerivAt_regression
    {ι : Type*} [Fintype ι]
    (a₀ f : FiniteModeState ι) (t : ℝ) :
    HasDerivAt (finiteModeAffineForcingCurve a₀ f)
      (finiteModeProjectedNSRHS
        (finiteModePureForcingCoefficients f)
        (finiteModeAffineForcingCurve a₀ f t)) t :=
  finiteModeAffineForcingCurve_hasDerivAt a₀ f t

/-- The affine pure-forcing curve starts at its prescribed initial coefficient
vector. -/
theorem finiteModeAffineForcingCurve_zero_regression
    {ι : Type*} [Fintype ι]
    (a₀ f : FiniteModeState ι) :
    finiteModeAffineForcingCurve a₀ f 0 = a₀ :=
  finiteModeAffineForcingCurve_zero a₀ f

/-- Decoupled diagonal-linear projected systems reduce componentwise to
`λᵢ aᵢ`. -/
theorem finiteModeProjectedNSRHS_diagonalLinear_regression
    (lam : Fin 3 → ℝ) (a : FiniteModeState (Fin 3)) (i : Fin 3) :
    finiteModeProjectedNSRHS (finiteModeDiagonalLinearCoefficients lam) a i =
      lam i * a i :=
  finiteModeProjectedNSRHS_diagonalLinear lam a i

/-- The exponential curve solves every decoupled diagonal-linear finite-mode
projected system. -/
theorem finiteModeDiagonalLinearExpCurve_hasDerivAt_regression
    (lam a₀ : FiniteModeState (Fin 3)) (t : ℝ) :
    HasDerivAt (finiteModeDiagonalLinearExpCurve lam a₀)
      (finiteModeProjectedNSRHS
        (finiteModeDiagonalLinearCoefficients lam)
        (finiteModeDiagonalLinearExpCurve lam a₀ t)) t :=
  finiteModeDiagonalLinearExpCurve_hasDerivAt lam a₀ t

/-- The diagonal-linear exponential curve starts at its prescribed initial
coefficient vector. -/
theorem finiteModeDiagonalLinearExpCurve_zero_regression
    (lam a₀ : FiniteModeState (Fin 3)) :
    finiteModeDiagonalLinearExpCurve lam a₀ 0 = a₀ :=
  finiteModeDiagonalLinearExpCurve_zero lam a₀

/-- Along any three-mode projected ODE solution, coefficient energy has the
expected coefficient/RHS derivative. -/
theorem finiteModeEnergy_hasDerivAt_of_projectedNS_regression
    (C : FiniteModeProjectedNSCoefficients (Fin 3))
    {a : ℝ → FiniteModeState (Fin 3)} {t : ℝ}
    (ha : HasDerivAt a (finiteModeProjectedNSRHS C (a t)) t) :
    HasDerivAt (fun s : ℝ => finiteModeEnergy (a s))
      (2 * ∑ i, a t i * finiteModeProjectedNSRHS C (a t) i) t :=
  finiteModeEnergy_hasDerivAt_of_projectedNS C ha

/-- Nonpositive diagonal rates make the diagonal-linear projected RHS
dissipative for the finite coefficient energy. -/
theorem finiteModeDiagonalLinearEnergyRHS_nonpos_regression
    (lam a : FiniteModeState (Fin 3)) (hLam : ∀ i, lam i ≤ 0) :
    2 * ∑ i, a i * finiteModeProjectedNSRHS (finiteModeDiagonalLinearCoefficients lam) a i ≤
      0 :=
  finiteModeDiagonalLinearEnergyRHS_nonpos lam a hLam

/-- The diagonal-linear exponential solution has the exact finite-energy
derivative induced by the diagonal rates. -/
theorem finiteModeDiagonalLinearExpCurve_energy_hasDerivAt_regression
    (lam a₀ : FiniteModeState (Fin 3)) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => finiteModeEnergy (finiteModeDiagonalLinearExpCurve lam a₀ s))
      (2 * ∑ i, lam i * (finiteModeDiagonalLinearExpCurve lam a₀ t i) ^ 2) t :=
  finiteModeDiagonalLinearExpCurve_energy_hasDerivAt lam a₀ t

/-- Decoupled diagonal-affine projected systems reduce componentwise to
`fᵢ + λᵢ aᵢ`. -/
theorem finiteModeProjectedNSRHS_diagonalAffine_regression
    (lam f : Fin 3 → ℝ) (a : FiniteModeState (Fin 3)) (i : Fin 3) :
    finiteModeProjectedNSRHS (finiteModeDiagonalAffineCoefficients lam f) a i =
      f i + lam i * a i :=
  finiteModeProjectedNSRHS_diagonalAffine lam f a i

/-- The equilibrium-centered curve solves a decoupled diagonal-affine
finite-mode system whenever the supplied center is an equilibrium. -/
theorem finiteModeDiagonalAffineEquilibriumCurve_hasDerivAt_regression
    (lam f aEq a₀ : FiniteModeState (Fin 3))
    (hEq : ∀ i, f i + lam i * aEq i = 0) (t : ℝ) :
    HasDerivAt (finiteModeDiagonalAffineEquilibriumCurve lam aEq a₀)
      (finiteModeProjectedNSRHS
        (finiteModeDiagonalAffineCoefficients lam f)
        (finiteModeDiagonalAffineEquilibriumCurve lam aEq a₀ t)) t :=
  finiteModeDiagonalAffineEquilibriumCurve_hasDerivAt lam f aEq a₀ hEq t

/-- The equilibrium-centered diagonal-affine curve starts at its prescribed
initial coefficient vector. -/
theorem finiteModeDiagonalAffineEquilibriumCurve_zero_regression
    (lam aEq a₀ : FiniteModeState (Fin 3)) :
    finiteModeDiagonalAffineEquilibriumCurve lam aEq a₀ 0 = a₀ :=
  finiteModeDiagonalAffineEquilibriumCurve_zero lam aEq a₀

end FiniteModeGalerkinToyRegression

end NavierStokes
end FluidDynamics
end Mettapedia
