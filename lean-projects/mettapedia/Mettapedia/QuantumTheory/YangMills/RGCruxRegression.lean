import Mettapedia.QuantumTheory.YangMills.RGCrux

/-!
# Yang-Mills RG Crux Regression

Regression wrappers for the same-constant lower-extraction route obstruction.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace RGCruxRegression

theorem no_same_constant_lower_extraction_rg_certificate_regression
    {dmax : ℕ} :
    ¬ SameConstantLowerExtractionRGCertificate dmax := by
  exact not_sameConstantLowerExtractionRGCertificate

theorem even_below_sixteen_le_fourteen_regression
    {dmax : ℕ} (hlt : dmax < 16) (heven : Even dmax) :
    dmax ≤ 14 := by
  exact even_lt_sixteen_le_fourteen hlt heven

theorem no_same_constant_even_below_sixteen_rg_certificate_regression
    {dmax : ℕ} :
    ¬ SameConstantEvenBelowSixteenRGCertificate dmax := by
  exact not_sameConstantEvenBelowSixteenRGCertificate

theorem no_at_least_2048_even_below_sixteen_rg_certificate_regression
    {C : ℝ} {dmax : ℕ} :
    ¬ AtLeast2048EvenBelowSixteenRGCertificate C dmax := by
  exact not_atLeast2048EvenBelowSixteenRGCertificate

theorem no_same_constant_lower_extraction_rg_certificate_exists_regression :
    ¬ ∃ dmax : ℕ, SameConstantLowerExtractionRGCertificate dmax := by
  exact not_exists_sameConstantLowerExtractionRGCertificate

theorem no_same_constant_even_below_sixteen_rg_certificate_exists_regression :
    ¬ ∃ dmax : ℕ, SameConstantEvenBelowSixteenRGCertificate dmax := by
  exact not_exists_sameConstantEvenBelowSixteenRGCertificate

theorem no_at_least_2048_even_below_sixteen_rg_certificate_exists_regression
    {C : ℝ} :
    ¬ ∃ dmax : ℕ, AtLeast2048EvenBelowSixteenRGCertificate C dmax := by
  exact not_exists_atLeast2048EvenBelowSixteenRGCertificate

theorem no_same_constant_lower_extraction_gap_route_regression
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {corr : SpatialCorrelation} {Δ : ℝ} :
    ¬ SameConstantLowerExtractionGapRouteCertificate A corr Δ := by
  exact not_sameConstantLowerExtractionGapRouteCertificate

theorem no_same_constant_even_below_sixteen_gap_route_regression
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {corr : SpatialCorrelation} {Δ : ℝ} :
    ¬ SameConstantEvenBelowSixteenGapRouteCertificate A corr Δ := by
  exact not_sameConstantEvenBelowSixteenGapRouteCertificate

theorem no_at_least_2048_even_below_sixteen_gap_route_regression
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {corr : SpatialCorrelation} {Δ : ℝ} {C : ℝ} :
    ¬ AtLeast2048EvenBelowSixteenGapRouteCertificate A corr Δ C := by
  exact not_atLeast2048EvenBelowSixteenGapRouteCertificate

theorem no_same_constant_fourteen_extraction_gap_route_regression
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {corr : SpatialCorrelation} {Δ : ℝ} :
    ¬ (HasSpectralMassGap A Δ ∧
        SpectralGapClusteringBridge A corr ∧
          HasExtendedExtractionContraction 2224 2 14) := by
  exact not_sameConstantFourteenExtractionGapRouteCertificate

end RGCruxRegression
end YangMills
end QuantumTheory
end Mettapedia
