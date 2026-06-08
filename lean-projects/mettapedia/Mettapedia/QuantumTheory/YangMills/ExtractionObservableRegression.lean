import Mettapedia.QuantumTheory.YangMills.ExtractionObservable

/-!
# Yang-Mills Extraction Observable Regression

Regression wrappers for observables determined by the standard extraction
surface `P≤4`.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills

theorem determined_by_standard_extraction_from_pointwise_factorization_regression
    {α β : Type*} [Zero α]
    {F : DimensionCoefficients α → β}
    (hF : ∀ coeff : DimensionCoefficients α,
      F coeff = F (standardExtraction (α := α) coeff)) :
    DeterminedByStandardExtraction (α := α) F := by
  exact DeterminedByStandardExtraction.of_eq_on_standardExtraction (α := α) hF

theorem determined_by_standard_extraction_ignores_extended_extraction_regression
    {α β : Type*} [Zero α]
    {F : DimensionCoefficients α → β}
    (hF : DeterminedByStandardExtraction (α := α) F)
    {dmax : CanonicalDimension}
    (hd : 4 ≤ dmax) (coeff : DimensionCoefficients α) :
    F (extendedExtraction dmax coeff) = F coeff := by
  exact hF.extendedExtraction_eq hd coeff

theorem determined_by_standard_extraction_ignores_added_higher_block_regression
    {α β : Type*} [AddMonoid α]
    {F : DimensionCoefficients α → β}
    (hF : DeterminedByStandardExtraction (α := α) F)
    (dmax : CanonicalDimension)
    (coeff extra : DimensionCoefficients α) :
    F (coeff + higherExtractionBlock dmax extra) = F coeff := by
  exact hF.add_higherExtractionBlock_eq dmax coeff extra

theorem determined_by_standard_extraction_sends_higher_block_to_zero_regression
    {α β : Type*} [AddMonoid α]
    {F : DimensionCoefficients α → β}
    (hF : DeterminedByStandardExtraction (α := α) F)
    (dmax : CanonicalDimension)
    (coeff : DimensionCoefficients α) :
    F (higherExtractionBlock dmax coeff) = F 0 := by
  exact hF.higherExtractionBlock_eq_zero dmax coeff

theorem determined_by_standard_extraction_kills_extended_minus_standard_regression
    {α β : Type*} [AddGroup α]
    {F : DimensionCoefficients α → β}
    (hF : DeterminedByStandardExtraction (α := α) F)
    {dmax : CanonicalDimension}
    (hd : 4 ≤ dmax) (coeff : DimensionCoefficients α) :
    F (extendedExtraction dmax coeff - standardExtraction (α := α) coeff) = F 0 := by
  exact hF.extendedExtraction_sub_standard_eq_zero hd coeff

theorem split_observable_higher_block_difference_is_pure_error_regression
    {α β : Type*} [AddMonoid α] [AddCommGroup β]
    {G F E : DimensionCoefficients α → β}
    (hF : DeterminedByStandardExtraction (α := α) F)
    (hdecomp : ∀ coeff : DimensionCoefficients α, G coeff = F coeff + E coeff)
    (dmax : CanonicalDimension)
    (coeff extra : DimensionCoefficients α) :
    G (coeff + higherExtractionBlock dmax extra) - G coeff =
      E (coeff + higherExtractionBlock dmax extra) - E coeff := by
  exact difference_eq_errorDifference_of_add_higherExtractionBlock
    (α := α) (β := β) hF hdecomp dmax coeff extra

theorem split_observable_extended_extraction_difference_is_pure_error_regression
    {α β : Type*} [Zero α] [AddCommGroup β]
    {G F E : DimensionCoefficients α → β}
    (hF : DeterminedByStandardExtraction (α := α) F)
    (hdecomp : ∀ coeff : DimensionCoefficients α, G coeff = F coeff + E coeff)
    {dmax : CanonicalDimension}
    (hd : 4 ≤ dmax) (coeff : DimensionCoefficients α) :
    G (extendedExtraction dmax coeff) - G coeff =
      E (extendedExtraction dmax coeff) - E coeff := by
  exact difference_eq_errorDifference_of_extendedExtraction
    (α := α) (β := β) hF hdecomp hd coeff

theorem split_observable_extended_minus_standard_difference_is_pure_error_regression
    {α β : Type*} [AddGroup α] [AddCommGroup β]
    {G F E : DimensionCoefficients α → β}
    (hF : DeterminedByStandardExtraction (α := α) F)
    (hdecomp : ∀ coeff : DimensionCoefficients α, G coeff = F coeff + E coeff)
    {dmax : CanonicalDimension}
    (hd : 4 ≤ dmax) (coeff : DimensionCoefficients α) :
    G (extendedExtraction dmax coeff - standardExtraction (α := α) coeff) - G 0 =
      E (extendedExtraction dmax coeff - standardExtraction (α := α) coeff) - E 0 := by
  exact difference_from_zero_eq_errorDifference_of_extendedExtraction_sub_standard
    (α := α) (β := β) hF hdecomp hd coeff

theorem split_observable_higher_block_norm_bound_from_error_regression
    {α β : Type*} [AddMonoid α] [NormedAddCommGroup β]
    {G F E : DimensionCoefficients α → β}
    (hF : DeterminedByStandardExtraction (α := α) F)
    (hdecomp : ∀ coeff : DimensionCoefficients α, G coeff = F coeff + E coeff)
    (dmax : CanonicalDimension)
    (coeff extra : DimensionCoefficients α)
    {B : ℝ}
    (hE : ‖E (coeff + higherExtractionBlock dmax extra) - E coeff‖ ≤ B) :
    ‖G (coeff + higherExtractionBlock dmax extra) - G coeff‖ ≤ B := by
  exact norm_difference_le_of_add_higherExtractionBlock_errorBound
    (α := α) (β := β) hF hdecomp dmax coeff extra hE

theorem split_observable_extended_extraction_norm_bound_from_error_regression
    {α β : Type*} [Zero α] [NormedAddCommGroup β]
    {G F E : DimensionCoefficients α → β}
    (hF : DeterminedByStandardExtraction (α := α) F)
    (hdecomp : ∀ coeff : DimensionCoefficients α, G coeff = F coeff + E coeff)
    {dmax : CanonicalDimension}
    (hd : 4 ≤ dmax) (coeff : DimensionCoefficients α)
    {B : ℝ}
    (hE : ‖E (extendedExtraction dmax coeff) - E coeff‖ ≤ B) :
    ‖G (extendedExtraction dmax coeff) - G coeff‖ ≤ B := by
  exact norm_difference_le_of_extendedExtraction_errorBound
    (α := α) (β := β) hF hdecomp hd coeff hE

theorem split_observable_extended_extraction_abs_bound_from_error_regression
    {α : Type*} [Zero α]
    {G F E : DimensionCoefficients α → ℝ}
    (hF : DeterminedByStandardExtraction (α := α) F)
    (hdecomp : ∀ coeff : DimensionCoefficients α, G coeff = F coeff + E coeff)
    {dmax : CanonicalDimension}
    (hd : 4 ≤ dmax) (coeff : DimensionCoefficients α)
    {B : ℝ}
    (hE : |E (extendedExtraction dmax coeff) - E coeff| ≤ B) :
    |G (extendedExtraction dmax coeff) - G coeff| ≤ B := by
  exact abs_difference_le_of_extendedExtraction_errorBound
    (α := α) hF hdecomp hd coeff hE

theorem split_observable_extended_extraction_threshold_failure_survives_regression
    {α : Type*} [Zero α]
    {G F E : DimensionCoefficients α → ℝ}
    (hF : DeterminedByStandardExtraction (α := α) F)
    (hdecomp : ∀ coeff : DimensionCoefficients α, G coeff = F coeff + E coeff)
    {dmax : CanonicalDimension}
    (hd : 4 ≤ dmax) (coeff : DimensionCoefficients α)
    {T B : ℝ}
    (hG : G coeff ≤ T - B)
    (hE : |E (extendedExtraction dmax coeff) - E coeff| ≤ B) :
    G (extendedExtraction dmax coeff) ≤ T := by
  exact extendedExtraction_le_target_of_le_target_sub_of_errorBound
    (α := α) hF hdecomp hd coeff hG hE

theorem split_observable_extended_extraction_strict_threshold_failure_survives_regression
    {α : Type*} [Zero α]
    {G F E : DimensionCoefficients α → ℝ}
    (hF : DeterminedByStandardExtraction (α := α) F)
    (hdecomp : ∀ coeff : DimensionCoefficients α, G coeff = F coeff + E coeff)
    {dmax : CanonicalDimension}
    (hd : 4 ≤ dmax) (coeff : DimensionCoefficients α)
    {T B : ℝ}
    (hG : G coeff < T - B)
    (hE : |E (extendedExtraction dmax coeff) - E coeff| ≤ B) :
    G (extendedExtraction dmax coeff) < T := by
  exact extendedExtraction_lt_target_of_lt_target_sub_of_errorBound
    (α := α) hF hdecomp hd coeff hG hE

theorem split_observable_extended_minus_standard_norm_bound_from_error_regression
    {α β : Type*} [AddGroup α] [NormedAddCommGroup β]
    {G F E : DimensionCoefficients α → β}
    (hF : DeterminedByStandardExtraction (α := α) F)
    (hdecomp : ∀ coeff : DimensionCoefficients α, G coeff = F coeff + E coeff)
    {dmax : CanonicalDimension}
    (hd : 4 ≤ dmax) (coeff : DimensionCoefficients α)
    {B : ℝ}
    (hE : ‖E (extendedExtraction dmax coeff - standardExtraction (α := α) coeff) - E 0‖ ≤ B) :
    ‖G (extendedExtraction dmax coeff - standardExtraction (α := α) coeff) - G 0‖ ≤ B := by
  exact norm_difference_le_of_extendedExtraction_sub_standard_errorBound
    (α := α) (β := β) hF hdecomp hd coeff hE

theorem split_observable_step_difference_is_pure_error_step_difference_regression
    {α β : Type*} [Zero α] [AddCommGroup β]
    {G F E : DimensionCoefficients α → β}
    (hF : DeterminedByStandardExtraction (α := α) F)
    (hdecomp : ∀ coeff : DimensionCoefficients α, G coeff = F coeff + E coeff)
    {dmax : CanonicalDimension}
    (hd : 4 ≤ dmax)
    (coeffNext coeffCur : DimensionCoefficients α) :
    (G (extendedExtraction dmax coeffNext) - G (extendedExtraction dmax coeffCur)) -
        (G coeffNext - G coeffCur) =
      (E (extendedExtraction dmax coeffNext) - E coeffNext) -
        (E (extendedExtraction dmax coeffCur) - E coeffCur) := by
  exact stepDifference_eq_errorStepDifference_of_extendedExtraction
    (α := α) (β := β) hF hdecomp hd coeffNext coeffCur

theorem split_observable_step_difference_norm_bound_from_error_regression
    {α β : Type*} [Zero α] [NormedAddCommGroup β]
    {G F E : DimensionCoefficients α → β}
    (hF : DeterminedByStandardExtraction (α := α) F)
    (hdecomp : ∀ coeff : DimensionCoefficients α, G coeff = F coeff + E coeff)
    {dmax : CanonicalDimension}
    (hd : 4 ≤ dmax)
    (coeffNext coeffCur : DimensionCoefficients α)
    {Bnext Bcur : ℝ}
    (hEnext : ‖E (extendedExtraction dmax coeffNext) - E coeffNext‖ ≤ Bnext)
    (hEcur : ‖E (extendedExtraction dmax coeffCur) - E coeffCur‖ ≤ Bcur) :
    ‖(G (extendedExtraction dmax coeffNext) - G (extendedExtraction dmax coeffCur)) -
        (G coeffNext - G coeffCur)‖ ≤ Bnext + Bcur := by
  exact norm_stepDifference_le_of_extendedExtraction_errorBounds
    (α := α) (β := β) hF hdecomp hd coeffNext coeffCur hEnext hEcur

theorem split_observable_step_difference_threshold_failure_survives_regression
    {α : Type*} [Zero α]
    {G F E : DimensionCoefficients α → ℝ}
    (hF : DeterminedByStandardExtraction (α := α) F)
    (hdecomp : ∀ coeff : DimensionCoefficients α, G coeff = F coeff + E coeff)
    {dmax : CanonicalDimension}
    (hd : 4 ≤ dmax)
    (coeffNext coeffCur : DimensionCoefficients α)
    {T Bnext Bcur : ℝ}
    (hG : G coeffNext - G coeffCur ≤ T - (Bnext + Bcur))
    (hEnext : |E (extendedExtraction dmax coeffNext) - E coeffNext| ≤ Bnext)
    (hEcur : |E (extendedExtraction dmax coeffCur) - E coeffCur| ≤ Bcur) :
    G (extendedExtraction dmax coeffNext) - G (extendedExtraction dmax coeffCur) ≤ T := by
  exact stepDifference_le_target_of_le_target_sub_of_errorBounds
    (α := α) hF hdecomp hd coeffNext coeffCur hG hEnext hEcur

theorem split_observable_step_difference_strict_threshold_failure_survives_regression
    {α : Type*} [Zero α]
    {G F E : DimensionCoefficients α → ℝ}
    (hF : DeterminedByStandardExtraction (α := α) F)
    (hdecomp : ∀ coeff : DimensionCoefficients α, G coeff = F coeff + E coeff)
    {dmax : CanonicalDimension}
    (hd : 4 ≤ dmax)
    (coeffNext coeffCur : DimensionCoefficients α)
    {T Bnext Bcur : ℝ}
    (hG : G coeffNext - G coeffCur < T - (Bnext + Bcur))
    (hEnext : |E (extendedExtraction dmax coeffNext) - E coeffNext| ≤ Bnext)
    (hEcur : |E (extendedExtraction dmax coeffCur) - E coeffCur| ≤ Bcur) :
    G (extendedExtraction dmax coeffNext) - G (extendedExtraction dmax coeffCur) < T := by
  exact stepDifference_lt_target_of_lt_target_sub_of_errorBounds
    (α := α) hF hdecomp hd coeffNext coeffCur hG hEnext hEcur

end YangMills
end QuantumTheory
end Mettapedia
