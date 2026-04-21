import Mathlib.Analysis.ODE.PicardLindelof

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
