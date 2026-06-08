import Mathlib.Tactic
import Mettapedia.QuantumTheory.YangMills.ExtractionProjection

/-!
# Yang-Mills Odd-Cutoff Extraction Obstruction

The manuscript enumerates extracted local operators by canonical dimensions
`0, 4, 6, 8, ...`.  On any coefficient family with no odd-dimensional terms,
an odd extraction cutoff adds nothing beyond the preceding even cutoff.

This file isolates that algebraic fact on the coefficient-surface extraction
model from `ExtractionProjection.lean`.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills

/-- Coefficient families with no odd canonical-dimension terms.  This matches
the manuscript's even-dimensional extracted-operator indexing surface. -/
def VanishesOnOddDimensions
    {α : Type*} [Zero α]
    (coeff : DimensionCoefficients α) : Prop :=
  ∀ ⦃n : CanonicalDimension⦄, Odd n → coeff n = 0

/-- If the coefficient at the new successor cutoff already vanishes, then
raising the extraction cutoff from `d` to `d + 1` changes nothing. -/
theorem extractLE_succ_eq_of_succ_vanish
    {α : Type*} [Zero α]
    {d : CanonicalDimension} {coeff : DimensionCoefficients α}
    (hvanish : coeff (d + 1) = 0) :
    extractLE (d + 1) coeff = extractLE d coeff := by
  funext n
  by_cases hn : n ≤ d
  · have hns : n ≤ d + 1 := Nat.le_succ_of_le hn
    simp [extractLE, hn, hns]
  · have hgt : d < n := lt_of_not_ge hn
    by_cases hns : n ≤ d + 1
    · have heq : n = d + 1 := by
        exact Nat.le_antisymm hns (Nat.succ_le_of_lt hgt)
      subst heq
      simp [extractLE, hvanish]
    · simp [extractLE, hn, hns]

/-- On an odd successor cutoff, odd-vanishing coefficient families have the
same extended extraction as at the preceding cutoff. -/
theorem extendedExtraction_succ_eq_of_succOdd_and_vanishOnOddDimensions
    {α : Type*} [Zero α]
    {d : CanonicalDimension} {coeff : DimensionCoefficients α}
    (hodd : Odd (d + 1))
    (hvanish : VanishesOnOddDimensions coeff) :
    extendedExtraction (d + 1) coeff = extendedExtraction d coeff := by
  exact extractLE_succ_eq_of_succ_vanish (d := d) (coeff := coeff) (hvanish hodd)

/-- The manuscript's putative odd repair cutoff `dmax = 15` adds no new
extracted terms on an odd-vanishing coefficient family. -/
theorem extendedExtraction_fifteen_eq_fourteen_of_vanishOnOddDimensions
    {α : Type*} [Zero α]
    {coeff : DimensionCoefficients α}
    (hvanish : VanishesOnOddDimensions coeff) :
    extendedExtraction 15 coeff = extendedExtraction 14 coeff := by
  exact extendedExtraction_succ_eq_of_succOdd_and_vanishOnOddDimensions
    (d := 14) (coeff := coeff) (by norm_num) hvanish

/-- If the new successor coefficient already vanishes, then enlarging the
higher extracted block cutoff from `d` to `d + 1` changes nothing. -/
theorem higherExtractionBlock_succ_eq_of_succ_vanish
    {α : Type*} [Zero α]
    {d : CanonicalDimension} {coeff : DimensionCoefficients α}
    (hvanish : coeff (d + 1) = 0) :
    higherExtractionBlock (d + 1) coeff = higherExtractionBlock d coeff := by
  funext n
  by_cases h5 : 5 ≤ n
  · by_cases hn : n ≤ d
    · have hns : n ≤ d + 1 := Nat.le_succ_of_le hn
      simp [higherExtractionBlock, h5, hn, hns]
    · have hgt : d < n := lt_of_not_ge hn
      by_cases hns : n ≤ d + 1
      · have heq : n = d + 1 := by
          exact Nat.le_antisymm hns (Nat.succ_le_of_lt hgt)
        subst heq
        simp [higherExtractionBlock, h5, hvanish]
      · simp [higherExtractionBlock, h5, hn, hns]
  · simp [higherExtractionBlock, h5]

/-- The manuscript's putative odd repair cutoff `dmax = 15` adds no new
higher extracted block beyond `dmax = 14` on an odd-vanishing coefficient
family. -/
theorem higherExtractionBlock_fifteen_eq_fourteen_of_vanishOnOddDimensions
    {α : Type*} [Zero α]
    {coeff : DimensionCoefficients α}
    (hvanish : VanishesOnOddDimensions coeff) :
    higherExtractionBlock 15 coeff = higherExtractionBlock 14 coeff := by
  exact higherExtractionBlock_succ_eq_of_succ_vanish
    (d := 14) (coeff := coeff) (hvanish (by norm_num))

end YangMills
end QuantumTheory
end Mettapedia
