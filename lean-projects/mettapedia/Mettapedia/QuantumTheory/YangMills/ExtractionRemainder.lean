import Mathlib.Tactic
import Mettapedia.QuantumTheory.YangMills.ExtractionOddCutoff

/-!
# Yang-Mills Extraction Remainder Audit

The RG bootstrap tracks the post-extraction remainder.  This file isolates that
remainder on the coefficient-surface extraction model and records the basic
facts needed for route audits.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills

/-- The coefficient-family remainder left after extracting all dimensions at
most `d`. -/
def extractionRemainder
    {α : Type*} [AddGroup α]
    (d : CanonicalDimension) (coeff : DimensionCoefficients α) :
    DimensionCoefficients α :=
  coeff - extendedExtraction d coeff

/-- Reconstruct the original coefficient family from the extracted part and the
remainder. -/
theorem coeff_eq_extendedExtraction_add_extractionRemainder
    {α : Type*} [AddGroup α]
    (d : CanonicalDimension) (coeff : DimensionCoefficients α) :
    coeff = extendedExtraction d coeff + extractionRemainder d coeff := by
  funext n
  by_cases hn : n ≤ d
  · simp [extractionRemainder, extendedExtraction, extractLE, hn]
  · have hdn : d < n := lt_of_not_ge hn
    simp [extractionRemainder, extendedExtraction, extractLE, hn]

/-- The extracted remainder vanishes on coefficients already captured by the
cutoff. -/
theorem extractionRemainder_apply_of_le
    {α : Type*} [AddGroup α]
    {d n : CanonicalDimension} {coeff : DimensionCoefficients α}
    (hn : n ≤ d) :
    extractionRemainder d coeff n = 0 := by
  simp [extractionRemainder, extendedExtraction, extractLE, hn]

/-- Above the extraction cutoff, the remainder agrees pointwise with the
original coefficient family. -/
theorem extractionRemainder_apply_of_lt
    {α : Type*} [AddGroup α]
    {d n : CanonicalDimension} {coeff : DimensionCoefficients α}
    (hdn : d < n) :
    extractionRemainder d coeff n = coeff n := by
  simp [extractionRemainder, extendedExtraction, extractLE, Nat.not_le_of_lt hdn]

/-- The remainder is identically zero exactly when the original family is
supported up to the extraction cutoff. -/
theorem extractionRemainder_eq_zero_iff_supportedUpTo
    {α : Type*} [AddGroup α]
    {d : CanonicalDimension} {coeff : DimensionCoefficients α} :
    extractionRemainder d coeff = 0 ↔ SupportedUpTo d coeff := by
  constructor
  · intro hrem n hn
    have happly := congrFun hrem n
    simpa [extractionRemainder, extendedExtraction, extractLE,
      Nat.not_le_of_lt hn] using happly
  · intro hsupp
    funext n
    by_cases hn : n ≤ d
    · simp [extractionRemainder, extendedExtraction, extractLE, hn]
    · have hdn : d < n := lt_of_not_ge hn
      simp [extractionRemainder, extendedExtraction, extractLE, hn, hsupp hdn]

/-- If the newly added successor coefficient already vanishes, then the actual
post-extraction remainder is unchanged by raising the cutoff from `d` to
`d + 1`. -/
theorem extractionRemainder_succ_eq_of_succ_vanish
    {α : Type*} [AddGroup α]
    {d : CanonicalDimension} {coeff : DimensionCoefficients α}
    (hvanish : coeff (d + 1) = 0) :
    extractionRemainder (d + 1) coeff = extractionRemainder d coeff := by
  simp [extractionRemainder, extractLE_succ_eq_of_succ_vanish (d := d) (coeff := coeff) hvanish]

/-- On the manuscript's even-dimensional extraction surface, the actual
post-extraction remainder at cutoff `15` is exactly the same as at cutoff
`14`. -/
theorem extractionRemainder_fifteen_eq_fourteen_of_vanishOnOddDimensions
    {α : Type*} [AddGroup α]
    {coeff : DimensionCoefficients α}
    (hvanish : VanishesOnOddDimensions coeff) :
    extractionRemainder 15 coeff = extractionRemainder 14 coeff := by
  exact extractionRemainder_succ_eq_of_succ_vanish
    (d := 14) (coeff := coeff) (hvanish (by norm_num))

end YangMills
end QuantumTheory
end Mettapedia
