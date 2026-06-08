import Mettapedia.Computability.PNP.InfinitaryHMLObstruction

/-!
# Regression checks for infinitary HML obstruction

These wrappers pin both directions of the finite-code obstruction.  If minimal
contexts are infinite, no finite decoder can cover the depth-`1` HML fragment or
all formulas, and no finite encoder can injectively encode either surface.
-/

namespace Mettapedia.Computability.PNP.InfinitaryHMLObstructionRegression

open Mettapedia.Computability.PNP
open Mettapedia.GSLT
open Mettapedia.GSLT.Meredith.RhoExample
open Mettapedia.GSLT.HMLFormula

theorem not_surjective_depth_fragment_one_of_finite_code_regression
    {S : GSLT} [HasMinimalContexts S] [Infinite (MinimalContext S)]
    {Code : Type*} [Fintype Code]
    (decode : Code → DepthFragment (S := S) 1) :
    ¬ Function.Surjective decode := by
  exact not_surjective_depthFragment_one_of_finite_code (S := S) decode

theorem not_surjective_hml_formula_of_finite_code_regression
    {S : GSLT} [HasMinimalContexts S] [Infinite (MinimalContext S)]
    {Code : Type*} [Fintype Code]
    (decode : Code → HMLFormula S) :
    ¬ Function.Surjective decode := by
  exact not_surjective_hmlFormula_of_finite_code (S := S) decode

theorem not_injective_depth_fragment_one_to_finite_code_regression
    {S : GSLT} [HasMinimalContexts S] [Infinite (MinimalContext S)]
    {Code : Type*} [Fintype Code]
    (encode : DepthFragment (S := S) 1 → Code) :
    ¬ Function.Injective encode := by
  exact not_injective_depthFragment_one_to_finite_code (S := S) encode

theorem not_injective_hml_formula_to_finite_code_regression
    {S : GSLT} [HasMinimalContexts S] [Infinite (MinimalContext S)]
    {Code : Type*} [Fintype Code]
    (encode : HMLFormula S → Code) :
    ¬ Function.Injective encode := by
  exact not_injective_hmlFormula_to_finite_code (S := S) encode

theorem not_surjective_rho_depth_fragment_one_of_finite_code_regression
    {Code : Type*} [Fintype Code]
    (decode : Code → DepthFragment (S := rhoGSLT) 1) :
    ¬ Function.Surjective decode := by
  exact not_surjective_rhoDepthFragment_one_of_finite_code decode

theorem not_surjective_rho_hml_formula_of_finite_code_regression
    {Code : Type*} [Fintype Code]
    (decode : Code → HMLFormula rhoGSLT) :
    ¬ Function.Surjective decode := by
  exact not_surjective_rhoHMLFormula_of_finite_code decode

theorem not_injective_rho_depth_fragment_one_to_finite_code_regression
    {Code : Type*} [Fintype Code]
    (encode : DepthFragment (S := rhoGSLT) 1 → Code) :
    ¬ Function.Injective encode := by
  exact not_injective_rhoDepthFragment_one_to_finite_code encode

theorem not_injective_rho_hml_formula_to_finite_code_regression
    {Code : Type*} [Fintype Code]
    (encode : HMLFormula rhoGSLT → Code) :
    ¬ Function.Injective encode := by
  exact not_injective_rhoHMLFormula_to_finite_code encode

end Mettapedia.Computability.PNP.InfinitaryHMLObstructionRegression
