import Mathlib.Tactic

/-!
# Yang-Mills Extraction Projection Audit

The Yang-Mills manuscript uses two extraction cutoffs:

* standard extraction `P≤4` for the coupling/observable flow;
* extended extraction `P≤dmax` for the RG bootstrap.

This file isolates the algebraic compatibility claim
`P≤4 = P≤4 ∘ P≤dmax` on coefficient families indexed by canonical dimension.
It does not define the actual jet-based extraction map from local functionals.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills

/-- Canonical dimensions used by the manuscript's extraction cutoffs. -/
abbrev CanonicalDimension := ℕ

/-- A concrete coefficient surface for local expansions indexed by canonical
dimension.  The file only uses this as an algebraic truncation model. -/
abbrev DimensionCoefficients (α : Type*) := CanonicalDimension → α

/-- Truncation to canonical dimensions at most `d`.  This is the coefficient
family model of the extraction projection `P≤d`. -/
def extractLE {α : Type*} [Zero α]
    (d : CanonicalDimension) (coeff : DimensionCoefficients α) :
    DimensionCoefficients α :=
  fun n => if n ≤ d then coeff n else 0

/-- Support condition saying that every coefficient above canonical dimension
`d` vanishes. -/
def SupportedUpTo {α : Type*} [Zero α]
    (d : CanonicalDimension) (coeff : DimensionCoefficients α) : Prop :=
  ∀ ⦃n : CanonicalDimension⦄, d < n → coeff n = 0

/-- The manuscript's standard extraction cutoff. -/
abbrev standardExtraction {α : Type*} [Zero α] :
    DimensionCoefficients α → DimensionCoefficients α :=
  extractLE 4

/-- The manuscript's extended extraction cutoff. -/
abbrev extendedExtraction {α : Type*} [Zero α]
    (dmax : CanonicalDimension) :
    DimensionCoefficients α → DimensionCoefficients α :=
  extractLE dmax

/-- Coefficients extracted strictly above the standard cutoff `4` and up to the
extended cutoff `dmax`.  This models the manuscript's additional extracted
couplings in dimensions `6, ..., dmax` at the coefficient level. -/
def higherExtractionBlock {α : Type*} [Zero α]
    (dmax : CanonicalDimension) (coeff : DimensionCoefficients α) :
    DimensionCoefficients α :=
  fun n => if 5 ≤ n ∧ n ≤ dmax then coeff n else 0

theorem extractLE_apply_of_le
    {α : Type*} [Zero α]
    {d n : CanonicalDimension} {coeff : DimensionCoefficients α}
    (hn : n ≤ d) :
    extractLE d coeff n = coeff n := by
  simp [extractLE, hn]

theorem extractLE_apply_of_lt
    {α : Type*} [Zero α]
    {d n : CanonicalDimension} {coeff : DimensionCoefficients α}
    (hdn : d < n) :
    extractLE d coeff n = 0 := by
  simp [extractLE, Nat.not_le_of_lt hdn]

theorem extractLE_zero
    {α : Type*} [AddMonoid α]
    (d : CanonicalDimension) :
    extractLE d (0 : DimensionCoefficients α) = 0 := by
  funext n
  by_cases hn : n ≤ d <;> simp [extractLE, hn]

theorem extractLE_add
    {α : Type*} [AddMonoid α]
    (d : CanonicalDimension)
    (coeff₁ coeff₂ : DimensionCoefficients α) :
    extractLE d (coeff₁ + coeff₂) =
      extractLE d coeff₁ + extractLE d coeff₂ := by
  funext n
  by_cases hn : n ≤ d <;> simp [extractLE, hn]

theorem supportedUpTo_extractLE
    {α : Type*} [Zero α]
    (d : CanonicalDimension) (coeff : DimensionCoefficients α) :
    SupportedUpTo d (extractLE d coeff) := by
  intro n hn
  exact extractLE_apply_of_lt hn

theorem extractLE_idem
    {α : Type*} [Zero α]
    (d : CanonicalDimension) (coeff : DimensionCoefficients α) :
    extractLE d (extractLE d coeff) = extractLE d coeff := by
  funext n
  by_cases hn : n ≤ d
  · simp [extractLE, hn]
  · simp [extractLE, hn]

/-- Composing two extraction projections is extraction at the smaller cutoff. -/
theorem extractLE_compose
    {α : Type*} [Zero α]
    (d₁ d₂ : CanonicalDimension) (coeff : DimensionCoefficients α) :
    extractLE d₁ (extractLE d₂ coeff) = extractLE (min d₁ d₂) coeff := by
  funext n
  by_cases h₁ : n ≤ d₁
  · by_cases h₂ : n ≤ d₂
    · have hmin : n ≤ min d₁ d₂ := le_min h₁ h₂
      simp [extractLE, h₁, h₂, hmin]
    · have hmin : ¬ n ≤ min d₁ d₂ := by
        intro h
        exact h₂ (le_trans h (Nat.min_le_right _ _))
      simp [extractLE, h₁, h₂, hmin]
  · have hmin : ¬ n ≤ min d₁ d₂ := by
      intro h
      exact h₁ (le_trans h (Nat.min_le_left _ _))
    simp [extractLE, h₁, hmin]

/-- If `d₁ ≤ d₂`, then extracting at `d₂` and then at `d₁` is the same as just
extracting at `d₁`. -/
theorem extractLE_compose_of_le
    {α : Type*} [Zero α]
    {d₁ d₂ : CanonicalDimension}
    (hd : d₁ ≤ d₂) (coeff : DimensionCoefficients α) :
    extractLE d₁ (extractLE d₂ coeff) = extractLE d₁ coeff := by
  simpa [Nat.min_eq_left hd] using extractLE_compose d₁ d₂ coeff

theorem extractLE_eq_self_of_supportedUpTo
    {α : Type*} [Zero α]
    {d : CanonicalDimension} {coeff : DimensionCoefficients α}
    (hsupp : SupportedUpTo d coeff) :
    extractLE d coeff = coeff := by
  funext n
  by_cases hn : n ≤ d
  · simp [extractLE, hn]
  · have hdn : d < n := lt_of_not_ge hn
    simp [extractLE, hn, hsupp hdn]

theorem extractLE_eq_self_iff_supportedUpTo
    {α : Type*} [Zero α]
    {d : CanonicalDimension} {coeff : DimensionCoefficients α} :
    extractLE d coeff = coeff ↔ SupportedUpTo d coeff := by
  constructor
  · intro hcoeff n hn
    have happly := congrFun hcoeff n
    simpa [extractLE, Nat.not_le_of_lt hn] using happly.symm
  · intro hsupp
    exact extractLE_eq_self_of_supportedUpTo hsupp

/-- Manuscript coherence claim: once `dmax ≥ 4`, standard extraction is
unchanged by first applying extended extraction. -/
theorem standardExtraction_compose_extendedExtraction_of_four_le
    {α : Type*} [Zero α]
    {dmax : CanonicalDimension}
    (hd : 4 ≤ dmax) :
    (standardExtraction (α := α)) ∘ extendedExtraction dmax =
      (standardExtraction (α := α)) := by
  funext coeff
  exact extractLE_compose_of_le hd coeff

/-- Pointwise form of the manuscript's extraction coherence claim. -/
theorem standardExtraction_after_extendedExtraction_of_four_le
    {α : Type*} [Zero α]
    {dmax : CanonicalDimension}
    (hd : 4 ≤ dmax) (coeff : DimensionCoefficients α) :
    standardExtraction (α := α) (extendedExtraction dmax coeff) =
      standardExtraction (α := α) coeff :=
  congrFun (standardExtraction_compose_extendedExtraction_of_four_le (α := α) hd) coeff

/-- The higher extracted block contributes nothing to the standard
extraction/projection `P≤4`. -/
theorem standardExtraction_higherExtractionBlock_eq_zero
    {α : Type*} [AddMonoid α]
    (dmax : CanonicalDimension) (coeff : DimensionCoefficients α) :
    standardExtraction (α := α) (higherExtractionBlock dmax coeff) = 0 := by
  funext n
  by_cases hn : n ≤ 4
  · have hnot5 : ¬ 5 ≤ n := by
      exact Nat.not_le_of_lt (Nat.lt_succ_of_le hn)
    simp [standardExtraction, extractLE, higherExtractionBlock, hn, hnot5]
  · simp [standardExtraction, extractLE, hn]

/-- Once `dmax ≥ 4`, extended extraction splits exactly into the standard
`≤ 4` part plus the higher extracted block in dimensions `5..dmax`. -/
theorem extendedExtraction_eq_standard_plus_higherExtractionBlock_of_four_le
    {α : Type*} [AddMonoid α]
    {dmax : CanonicalDimension}
    (hd : 4 ≤ dmax) (coeff : DimensionCoefficients α) :
    extendedExtraction dmax coeff =
      standardExtraction (α := α) coeff + higherExtractionBlock dmax coeff := by
  funext n
  by_cases h4 : n ≤ 4
  · have hnd : n ≤ dmax := le_trans h4 hd
    have hnot5 : ¬ 5 ≤ n := by
      exact Nat.not_le_of_lt (Nat.lt_succ_of_le h4)
    simp [extendedExtraction, standardExtraction, extractLE, higherExtractionBlock, h4, hnd, hnot5]
  · by_cases hdn : n ≤ dmax
    · have h5 : 5 ≤ n := by
        exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h4)
      simp [extendedExtraction, standardExtraction, extractLE, higherExtractionBlock, h4, hdn, h5]
    · simp [extendedExtraction, standardExtraction, extractLE, higherExtractionBlock, h4, hdn]

/-- Adding a pure higher extracted block cannot change the standard extraction
`P≤4`. -/
theorem standardExtraction_add_higherExtractionBlock_eq
    {α : Type*} [AddMonoid α]
    (dmax : CanonicalDimension)
    (coeff extra : DimensionCoefficients α) :
    standardExtraction (α := α) (coeff + higherExtractionBlock dmax extra) =
      standardExtraction (α := α) coeff := by
  calc
    standardExtraction (α := α) (coeff + higherExtractionBlock dmax extra)
        = standardExtraction (α := α) coeff +
            standardExtraction (α := α) (higherExtractionBlock dmax extra) := by
            simpa [standardExtraction] using
              extractLE_add 4 coeff (higherExtractionBlock dmax extra)
    _ = standardExtraction (α := α) coeff + 0 := by
          rw [standardExtraction_higherExtractionBlock_eq_zero]
    _ = standardExtraction (α := α) coeff := by
          simp

/-- For `dmax ≥ 4`, the higher extracted block is exactly the residual between
the extended extraction and the standard `≤ 4` extraction. -/
theorem higherExtractionBlock_eq_extendedExtraction_sub_standard_of_four_le
    {α : Type*} [AddGroup α]
    {dmax : CanonicalDimension}
    (hd : 4 ≤ dmax) (coeff : DimensionCoefficients α) :
    higherExtractionBlock dmax coeff =
      extendedExtraction dmax coeff - standardExtraction (α := α) coeff := by
  funext n
  by_cases h4 : n ≤ 4
  · have hnd : n ≤ dmax := le_trans h4 hd
    have hnot5 : ¬ 5 ≤ n := by
      exact Nat.not_le_of_lt (Nat.lt_succ_of_le h4)
    simp [higherExtractionBlock, extendedExtraction, standardExtraction, extractLE, h4, hnd, hnot5]
  · by_cases hdn : n ≤ dmax
    · have h5 : 5 ≤ n := by
        exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h4)
      simp [higherExtractionBlock, extendedExtraction, standardExtraction, extractLE, h4, hdn, h5]
    · simp [higherExtractionBlock, extendedExtraction, standardExtraction, extractLE, h4, hdn]

/-- Equivalent residual form of the higher-block invisibility statement:
after removing the standard extraction from the extended extraction, the
remaining part has zero `P≤4` projection. -/
theorem standardExtraction_extendedExtraction_sub_standard_eq_zero_of_four_le
    {α : Type*} [AddGroup α]
    {dmax : CanonicalDimension}
    (hd : 4 ≤ dmax) (coeff : DimensionCoefficients α) :
    standardExtraction (α := α)
      (extendedExtraction dmax coeff - standardExtraction (α := α) coeff) = 0 := by
  rw [← higherExtractionBlock_eq_extendedExtraction_sub_standard_of_four_le (α := α) hd coeff]
  exact standardExtraction_higherExtractionBlock_eq_zero (α := α) dmax coeff

end YangMills
end QuantumTheory
end Mettapedia
