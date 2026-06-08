import Mettapedia.QuantumTheory.YangMills.ExtractionProjection

/-!
# Yang-Mills Extraction Projection Regression

Small regression wrappers for the algebraic extraction-projection surface.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills

theorem extract_projection_idempotent_regression
    {α : Type*} [Zero α]
    (d : CanonicalDimension) (coeff : DimensionCoefficients α) :
    extractLE d (extractLE d coeff) = extractLE d coeff := by
  exact extractLE_idem d coeff

theorem extract_projection_compose_min_regression
    {α : Type*} [Zero α]
    (d₁ d₂ : CanonicalDimension) (coeff : DimensionCoefficients α) :
    extractLE d₁ (extractLE d₂ coeff) = extractLE (min d₁ d₂) coeff := by
  exact extractLE_compose d₁ d₂ coeff

theorem extract_projection_zero_regression
    {α : Type*} [AddMonoid α]
    (d : CanonicalDimension) :
    extractLE d (0 : DimensionCoefficients α) = 0 := by
  exact extractLE_zero d

theorem extract_projection_add_regression
    {α : Type*} [AddMonoid α]
    (d : CanonicalDimension)
    (coeff₁ coeff₂ : DimensionCoefficients α) :
    extractLE d (coeff₁ + coeff₂) =
      extractLE d coeff₁ + extractLE d coeff₂ := by
  exact extractLE_add d coeff₁ coeff₂

theorem extract_projection_fixed_iff_supported_regression
    {α : Type*} [Zero α]
    {d : CanonicalDimension} {coeff : DimensionCoefficients α} :
    extractLE d coeff = coeff ↔ SupportedUpTo d coeff := by
  exact extractLE_eq_self_iff_supportedUpTo

theorem standard_extended_extraction_coherence_regression
    {α : Type*} [Zero α]
    {dmax : CanonicalDimension}
    (hd : 4 ≤ dmax) :
    (standardExtraction (α := α)) ∘ extendedExtraction dmax =
      (standardExtraction (α := α)) := by
  exact standardExtraction_compose_extendedExtraction_of_four_le (α := α) hd

theorem standard_extended_extraction_pointwise_coherence_regression
    {α : Type*} [Zero α]
    {dmax : CanonicalDimension}
    (hd : 4 ≤ dmax) (coeff : DimensionCoefficients α) :
    standardExtraction (α := α) (extendedExtraction dmax coeff) =
      standardExtraction (α := α) coeff := by
  exact standardExtraction_after_extendedExtraction_of_four_le (α := α) hd coeff

theorem standard_extraction_higher_block_vanishes_regression
    {α : Type*} [AddMonoid α]
    (dmax : CanonicalDimension) (coeff : DimensionCoefficients α) :
    standardExtraction (α := α) (higherExtractionBlock dmax coeff) = 0 := by
  exact standardExtraction_higherExtractionBlock_eq_zero (α := α) dmax coeff

theorem extended_extraction_splits_into_standard_plus_higher_block_regression
    {α : Type*} [AddMonoid α]
    {dmax : CanonicalDimension}
    (hd : 4 ≤ dmax) (coeff : DimensionCoefficients α) :
    extendedExtraction dmax coeff =
      standardExtraction (α := α) coeff + higherExtractionBlock dmax coeff := by
  exact extendedExtraction_eq_standard_plus_higherExtractionBlock_of_four_le
    (α := α) hd coeff

theorem standard_extraction_ignores_added_higher_block_regression
    {α : Type*} [AddMonoid α]
    (dmax : CanonicalDimension)
    (coeff extra : DimensionCoefficients α) :
    standardExtraction (α := α) (coeff + higherExtractionBlock dmax extra) =
      standardExtraction (α := α) coeff := by
  exact standardExtraction_add_higherExtractionBlock_eq (α := α) dmax coeff extra

theorem higher_block_is_extended_minus_standard_regression
    {α : Type*} [AddGroup α]
    {dmax : CanonicalDimension}
    (hd : 4 ≤ dmax) (coeff : DimensionCoefficients α) :
    higherExtractionBlock dmax coeff =
      extendedExtraction dmax coeff - standardExtraction (α := α) coeff := by
  exact higherExtractionBlock_eq_extendedExtraction_sub_standard_of_four_le
    (α := α) hd coeff

theorem standard_extraction_of_extended_minus_standard_vanishes_regression
    {α : Type*} [AddGroup α]
    {dmax : CanonicalDimension}
    (hd : 4 ≤ dmax) (coeff : DimensionCoefficients α) :
    standardExtraction (α := α)
      (extendedExtraction dmax coeff - standardExtraction (α := α) coeff) = 0 := by
  exact standardExtraction_extendedExtraction_sub_standard_eq_zero_of_four_le
    (α := α) hd coeff

end YangMills
end QuantumTheory
end Mettapedia
