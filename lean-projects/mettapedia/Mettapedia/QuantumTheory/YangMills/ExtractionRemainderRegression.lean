import Mettapedia.QuantumTheory.YangMills.ExtractionRemainder

/-!
# Yang-Mills Extraction Remainder Regression

Regression wrappers for the coefficient-surface post-extraction remainder.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills

theorem coefficient_reconstructs_from_extraction_and_remainder_regression
    {α : Type*} [AddGroup α]
    (d : CanonicalDimension) (coeff : DimensionCoefficients α) :
    coeff = extendedExtraction d coeff + extractionRemainder d coeff := by
  exact coeff_eq_extendedExtraction_add_extractionRemainder d coeff

theorem extraction_remainder_vanishes_below_cutoff_regression
    {α : Type*} [AddGroup α]
    {d n : CanonicalDimension} {coeff : DimensionCoefficients α}
    (hn : n ≤ d) :
    extractionRemainder d coeff n = 0 := by
  exact extractionRemainder_apply_of_le hn

theorem extraction_remainder_agrees_above_cutoff_regression
    {α : Type*} [AddGroup α]
    {d n : CanonicalDimension} {coeff : DimensionCoefficients α}
    (hdn : d < n) :
    extractionRemainder d coeff n = coeff n := by
  exact extractionRemainder_apply_of_lt hdn

theorem extraction_remainder_zero_iff_supported_regression
    {α : Type*} [AddGroup α]
    {d : CanonicalDimension} {coeff : DimensionCoefficients α} :
    extractionRemainder d coeff = 0 ↔ SupportedUpTo d coeff := by
  exact extractionRemainder_eq_zero_iff_supportedUpTo

theorem successor_cutoff_remainder_irrelevant_when_new_term_vanishes_regression
    {α : Type*} [AddGroup α]
    {d : CanonicalDimension} {coeff : DimensionCoefficients α}
    (hvanish : coeff (d + 1) = 0) :
    extractionRemainder (d + 1) coeff = extractionRemainder d coeff := by
  exact extractionRemainder_succ_eq_of_succ_vanish hvanish

theorem remainder_fifteen_equals_fourteen_on_odd_vanishing_surface_regression
    {α : Type*} [AddGroup α]
    {coeff : DimensionCoefficients α}
    (hvanish : VanishesOnOddDimensions coeff) :
    extractionRemainder 15 coeff = extractionRemainder 14 coeff := by
  exact extractionRemainder_fifteen_eq_fourteen_of_vanishOnOddDimensions hvanish

end YangMills
end QuantumTheory
end Mettapedia
