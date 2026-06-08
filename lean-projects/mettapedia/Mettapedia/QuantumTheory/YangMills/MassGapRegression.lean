import Mettapedia.QuantumTheory.YangMills.MassGap

/-!
# Yang-Mills Mass Gap Regression

Small theorem-level checks for the spectral and quadratic mass-gap audit layer.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace MassGapRegression

theorem spectral_gap_positive_regression
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {Δ : ℝ}
    (hgap : HasSpectralMassGap A Δ) :
    0 < Δ :=
  hgap.positive

theorem spectral_gap_point_obstruction_regression
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {Δ E : ℝ}
    (hE : E ∈ spectrum ℝ A)
    (hEpos : 0 < E) (hElt : E < Δ) :
    ¬ HasSpectralMassGap A Δ := by
  exact not_hasSpectralMassGap_of_spectrum_in_gap hE hEpos hElt

theorem spectral_gap_downward_closed_regression
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {δ Δ : ℝ}
    (hgap : HasSpectralMassGap A Δ)
    (hδ : 0 < δ) (hδΔ : δ ≤ Δ) :
    HasSpectralMassGap A δ := by
  exact hgap.mono hδ hδΔ

theorem spectral_gap_positive_energy_split_regression
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {Δ E : ℝ}
    (hgap : HasSpectralMassGap A Δ)
    (hpos : HasPositiveEnergySpectrum A)
    (hE : E ∈ spectrum ℝ A) :
    E = 0 ∨ Δ ≤ E := by
  exact hgap.eq_zero_or_gap_le_of_positive_energy hpos hE

theorem spectral_gap_positive_spectrum_threshold_regression
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {Δ E : ℝ}
    (hgap : HasSpectralMassGap A Δ)
    (hE : E ∈ spectrum ℝ A)
    (hEpos : 0 < E) :
    Δ ≤ E := by
  exact hgap.gap_le_of_pos_spectrum hE hEpos

theorem spectral_gap_excludes_low_positive_spectrum_regression
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {Δ E : ℝ}
    (hgap : HasSpectralMassGap A Δ)
    (hEpos : 0 < E) (hElt : E < Δ) :
    E ∉ spectrum ℝ A := by
  exact hgap.not_spectrum_of_pos_lt hEpos hElt

theorem spectral_gap_subset_nonpos_or_gap_regression
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {Δ : ℝ}
    (hgap : HasSpectralMassGap A Δ) :
    spectrum ℝ A ⊆ {E : ℝ | E ≤ 0 ∨ Δ ≤ E} := by
  exact hgap.spectrum_subset_nonpos_or_gap

theorem spectral_gap_iff_positive_and_subset_nonpos_or_gap_regression
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {Δ : ℝ} :
    HasSpectralMassGap A Δ ↔
      0 < Δ ∧ spectrum ℝ A ⊆ {E : ℝ | E ≤ 0 ∨ Δ ≤ E} := by
  exact hasSpectralMassGap_iff_positive_and_spectrum_subset_nonpos_or_gap

theorem spectral_gap_positive_energy_nonvacuum_threshold_regression
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {Δ E : ℝ}
    (hgap : HasSpectralMassGap A Δ)
    (hpos : HasPositiveEnergySpectrum A)
    (hE : E ∈ spectrum ℝ A)
    (hne : E ≠ 0) :
    Δ ≤ E := by
  exact hgap.gap_le_of_positive_energy_of_ne_zero hpos hE hne

theorem spectral_gap_positive_energy_subset_vacuum_or_gap_regression
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {Δ : ℝ}
    (hgap : HasSpectralMassGap A Δ)
    (hpos : HasPositiveEnergySpectrum A) :
    spectrum ℝ A ⊆ {E : ℝ | E = 0 ∨ Δ ≤ E} := by
  exact hgap.spectrum_subset_vacuum_or_gap_of_positive_energy hpos

theorem spectral_gap_iff_positive_and_subset_vacuum_or_gap_of_positive_energy_regression
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {Δ : ℝ}
    (hpos : HasPositiveEnergySpectrum A) :
    HasSpectralMassGap A Δ ↔
      0 < Δ ∧ spectrum ℝ A ⊆ {E : ℝ | E = 0 ∨ Δ ≤ E} := by
  exact hasSpectralMassGap_iff_positive_and_spectrum_subset_vacuum_or_gap_of_positive_energy hpos

theorem first_positive_spectral_value_excludes_lower_positive_spectrum_regression
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {m E : ℝ}
    (hfirst : HasFirstPositiveSpectralValue A m)
    (hEpos : 0 < E) (hEm : E < m) :
    E ∉ spectrum ℝ A := by
  exact hfirst.not_spectrum_of_pos_lt hEpos hEm

theorem first_positive_spectral_value_unique_regression
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {m n : ℝ}
    (hm : HasFirstPositiveSpectralValue A m)
    (hn : HasFirstPositiveSpectralValue A n) :
    m = n := by
  exact hm.unique hn

theorem first_positive_spectral_value_isLeast_positive_spectrum_regression
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {m : ℝ}
    (hfirst : HasFirstPositiveSpectralValue A m) :
    IsLeast (PositiveSpectrumSet A) m := by
  exact hfirst.isLeast_positiveSpectrumSet

theorem first_positive_spectral_value_iff_isLeast_positive_spectrum_regression
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {m : ℝ} :
    HasFirstPositiveSpectralValue A m ↔
      IsLeast (PositiveSpectrumSet A) m := by
  exact hasFirstPositiveSpectralValue_iff_isLeast_positiveSpectrumSet

theorem first_positive_spectral_value_positive_spectral_inf_eq_regression
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {m : ℝ}
    (hfirst : HasFirstPositiveSpectralValue A m) :
    PositiveSpectralInf A = m := by
  exact hfirst.positiveSpectralInf_eq

theorem first_positive_spectral_value_subset_nonpos_or_first_regression
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {m : ℝ}
    (hfirst : HasFirstPositiveSpectralValue A m) :
    spectrum ℝ A ⊆ {E : ℝ | E ≤ 0 ∨ m ≤ E} := by
  exact hfirst.spectrum_subset_nonpos_or_first

theorem first_positive_spectral_value_positive_energy_subset_vacuum_or_first_regression
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {m : ℝ}
    (hfirst : HasFirstPositiveSpectralValue A m)
    (hpos : HasPositiveEnergySpectrum A) :
    spectrum ℝ A ⊆ {E : ℝ | E = 0 ∨ m ≤ E} := by
  exact hfirst.spectrum_subset_vacuum_or_first_of_positiveEnergy hpos

theorem first_positive_spectral_value_gap_of_le_regression
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {m Δ : ℝ}
    (hfirst : HasFirstPositiveSpectralValue A m)
    (hΔpos : 0 < Δ) (hΔm : Δ ≤ m) :
    HasSpectralMassGap A Δ := by
  exact hfirst.hasSpectralMassGap_of_le hΔpos hΔm

theorem first_positive_spectral_value_gap_self_regression
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {m : ℝ}
    (hfirst : HasFirstPositiveSpectralValue A m) :
    HasSpectralMassGap A m := by
  exact hfirst.hasSpectralMassGap_self

theorem spectral_gap_endpoint_spectral_has_first_positive_regression
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {m : ℝ}
    (hgap : HasSpectralMassGap A m)
    (hm : m ∈ spectrum ℝ A) :
    HasFirstPositiveSpectralValue A m := by
  exact hgap.hasFirstPositiveSpectralValue_of_spectrum_mem hm

theorem first_positive_spectral_value_iff_endpoint_gap_regression
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {m : ℝ} :
    HasFirstPositiveSpectralValue A m ↔
      m ∈ spectrum ℝ A ∧ HasSpectralMassGap A m := by
  exact hasFirstPositiveSpectralValue_iff_spectrum_mem_and_hasSpectralMassGap

theorem first_positive_spectral_value_gap_iff_regression
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {m Δ : ℝ}
    (hfirst : HasFirstPositiveSpectralValue A m) :
    HasSpectralMassGap A Δ ↔ 0 < Δ ∧ Δ ≤ m := by
  exact hfirst.hasSpectralMassGap_iff

theorem first_positive_spectral_value_gap_set_eq_Ioc_regression
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {m : ℝ}
    (hfirst : HasFirstPositiveSpectralValue A m) :
    SpectralGapSet A = Set.Ioc 0 m := by
  exact hfirst.spectralGapSet_eq_Ioc

theorem finite_spectral_mass_of_positive_spectral_value_regression
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {E : ℝ}
    (hE : E ∈ spectrum ℝ A)
    (hEpos : 0 < E) :
    HasFiniteSpectralMass A := by
  exact hasFiniteSpectralMass_of_pos_spectrum hE hEpos

theorem first_positive_spectral_value_finite_mass_regression
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {m : ℝ}
    (hfirst : HasFirstPositiveSpectralValue A m) :
    HasFiniteSpectralMass A := by
  exact hfirst.hasFiniteSpectralMass

theorem finite_spectral_mass_iff_bddAbove_gap_set_regression
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} :
    HasFiniteSpectralMass A ↔ BddAbove (SpectralGapSet A) := by
  exact hasFiniteSpectralMass_iff_bddAbove_spectralGapSet

theorem spectral_gap_sup_isLUB_regression
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {Δ : ℝ}
    (hfinite : HasFiniteSpectralMass A)
    (hgap : HasSpectralMassGap A Δ) :
    IsLUB (SpectralGapSet A) (SpectralGapSup A) := by
  exact spectralGapSup_isLUB_of_hasFiniteSpectralMass_of_gap hfinite hgap

theorem spectral_gap_le_sup_regression
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {Δ : ℝ}
    (hfinite : HasFiniteSpectralMass A)
    (hgap : HasSpectralMassGap A Δ) :
    Δ ≤ SpectralGapSup A := by
  exact hgap.le_spectralGapSup_of_hasFiniteSpectralMass hfinite

theorem spectral_gap_sup_positive_regression
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {Δ : ℝ}
    (hfinite : HasFiniteSpectralMass A)
    (hgap : HasSpectralMassGap A Δ) :
    0 < SpectralGapSup A := by
  exact spectralGapSup_pos_of_hasFiniteSpectralMass_of_gap hfinite hgap

theorem spectral_gap_sup_le_positive_spectrum_regression
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {Δ E : ℝ}
    (hgap : HasSpectralMassGap A Δ)
    (hE : E ∈ spectrum ℝ A)
    (hEpos : 0 < E) :
    SpectralGapSup A ≤ E := by
  exact spectralGapSup_le_of_pos_spectrum_of_gap hgap hE hEpos

theorem first_positive_spectral_value_sup_eq_regression
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {m : ℝ}
    (hfirst : HasFirstPositiveSpectralValue A m) :
    SpectralGapSup A = m := by
  exact hfirst.spectralGapSup_eq

theorem first_positive_spectral_value_gap_sup_eq_positive_spectral_inf_regression
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {m : ℝ}
    (hfirst : HasFirstPositiveSpectralValue A m) :
    SpectralGapSup A = PositiveSpectralInf A := by
  exact hfirst.spectralGapSup_eq_positiveSpectralInf

theorem not_finite_spectral_mass_of_arbitrarily_large_gaps_regression
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H}
    (hlarge : ∀ M : ℝ, ∃ Δ : ℝ, M < Δ ∧ HasSpectralMassGap A Δ) :
    ¬ HasFiniteSpectralMass A := by
  exact not_hasFiniteSpectralMass_of_arbitrarily_large_gaps hlarge

theorem not_finite_spectral_mass_of_all_positive_gaps_regression
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H}
    (hall : ∀ Δ : ℝ, 0 < Δ → HasSpectralMassGap A Δ) :
    ¬ HasFiniteSpectralMass A := by
  exact not_hasFiniteSpectralMass_of_all_positive_gaps hall

theorem quadratic_gap_downward_closed_regression
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {A : LinearOperator H} {Ω : H} {δ Δ : ℝ}
    (hgap : HasQuadraticMassGap A Ω Δ)
    (hδ : 0 < δ) (hδΔ : δ ≤ Δ) :
    HasQuadraticMassGap A Ω δ := by
  exact hgap.mono hδ hδΔ

end MassGapRegression
end YangMills
end QuantumTheory
end Mettapedia
