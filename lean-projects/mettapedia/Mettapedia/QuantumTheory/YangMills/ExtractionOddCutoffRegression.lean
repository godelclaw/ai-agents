import Mettapedia.QuantumTheory.YangMills.ExtractionOddCutoff

/-!
# Yang-Mills Odd-Cutoff Extraction Regression

Regression wrappers for the odd-cutoff obstruction on the manuscript's
even-dimensional extraction surface.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills

theorem successor_cutoff_irrelevant_when_new_term_vanishes_regression
    {α : Type*} [Zero α]
    {d : CanonicalDimension} {coeff : DimensionCoefficients α}
    (hvanish : coeff (d + 1) = 0) :
    extractLE (d + 1) coeff = extractLE d coeff := by
  exact extractLE_succ_eq_of_succ_vanish hvanish

theorem odd_successor_extended_extraction_collapses_regression
    {α : Type*} [Zero α]
    {d : CanonicalDimension} {coeff : DimensionCoefficients α}
    (hodd : Odd (d + 1))
    (hvanish : VanishesOnOddDimensions coeff) :
    extendedExtraction (d + 1) coeff = extendedExtraction d coeff := by
  exact extendedExtraction_succ_eq_of_succOdd_and_vanishOnOddDimensions hodd hvanish

theorem fifteen_cutoff_equals_fourteen_on_odd_vanishing_surface_regression
    {α : Type*} [Zero α]
    {coeff : DimensionCoefficients α}
    (hvanish : VanishesOnOddDimensions coeff) :
    extendedExtraction 15 coeff = extendedExtraction 14 coeff := by
  exact extendedExtraction_fifteen_eq_fourteen_of_vanishOnOddDimensions hvanish

theorem higher_block_successor_cutoff_irrelevant_when_new_term_vanishes_regression
    {α : Type*} [Zero α]
    {d : CanonicalDimension} {coeff : DimensionCoefficients α}
    (hvanish : coeff (d + 1) = 0) :
    higherExtractionBlock (d + 1) coeff = higherExtractionBlock d coeff := by
  exact higherExtractionBlock_succ_eq_of_succ_vanish hvanish

theorem higher_block_fifteen_equals_fourteen_on_odd_vanishing_surface_regression
    {α : Type*} [Zero α]
    {coeff : DimensionCoefficients α}
    (hvanish : VanishesOnOddDimensions coeff) :
    higherExtractionBlock 15 coeff = higherExtractionBlock 14 coeff := by
  exact higherExtractionBlock_fifteen_eq_fourteen_of_vanishOnOddDimensions hvanish

end YangMills
end QuantumTheory
end Mettapedia
