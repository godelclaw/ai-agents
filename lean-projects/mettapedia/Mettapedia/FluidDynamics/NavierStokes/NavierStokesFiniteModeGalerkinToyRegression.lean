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

end FiniteModeGalerkinToyRegression

end NavierStokes
end FluidDynamics
end Mettapedia
