import Mettapedia.Computability.PNP.BadCodeAgreementObstruction

/-!
# Regression checks for atomic bad-code agreement obstructions

These wrappers pin the strict pure-atom obstruction used to audit the PNP
exact-ZAB ERM recovery route.
-/

namespace Mettapedia.Computability.PNP.BadCodeAgreementObstructionRegression

open Mettapedia.Computability.PNP
open scoped ENNReal
open scoped BigOperators

universe u

theorem atomic_bad_code_blocks_strict_agreement_bound_regression
    {Input : Type u} [Fintype Input]
    {s : ℕ} (F : BitEncodedClassifierFamily Input s)
    {x : Input} {target : Input → Bool} {q : ℝ≥0∞}
    (c : F.toEncodedFamily.BadCodes target)
    (hagree : F.decode c.1 x = target x)
    (hq_lt : q < 1) :
    ¬ (∀ d : F.toEncodedFamily.BadCodes target,
        agreementMass (PMF.pure x) target (F.decode d.1) ≤ q) := by
  exact F.not_badCodeAgreementBound_pure_of_agrees c hagree hq_lt

theorem support_agreeing_bad_code_blocks_strict_agreement_bound_regression
    {Input : Type u} [Fintype Input]
    {s : ℕ} (F : BitEncodedClassifierFamily Input s)
    {μ : PMF Input} {target : Input → Bool} {q : ℝ≥0∞}
    (c : F.toEncodedFamily.BadCodes target)
    (hagree : ∀ x, μ x ≠ 0 → F.decode c.1 x = target x)
    (hq_lt : q < 1) :
    ¬ (∀ d : F.toEncodedFamily.BadCodes target,
        agreementMass μ target (F.decode d.1) ≤ q) := by
  exact F.not_badCodeAgreementBound_of_agrees_on_support c hagree hq_lt

theorem region_agreeing_bad_code_forces_threshold_mass_regression
    {Input : Type u} [Fintype Input]
    {s : ℕ} (F : BitEncodedClassifierFamily Input s)
    {μ : PMF Input} {target : Input → Bool} {q : ℝ≥0∞}
    (hbound :
      ∀ c : F.toEncodedFamily.BadCodes target,
        agreementMass μ target (F.decode c.1) ≤ q)
    (c : F.toEncodedFamily.BadCodes target)
    (region : Finset Input)
    (hagree : ∀ x, x ∈ region → F.decode c.1 x = target x) :
    region.sum (fun x => μ x) ≤ q := by
  exact F.regionMass_le_of_badCode_agrees_on hbound c region hagree

theorem region_agreeing_bad_code_blocks_small_threshold_regression
    {Input : Type u} [Fintype Input]
    {s : ℕ} (F : BitEncodedClassifierFamily Input s)
    {μ : PMF Input} {target : Input → Bool} {q : ℝ≥0∞}
    (c : F.toEncodedFamily.BadCodes target)
    (region : Finset Input)
    (hagree : ∀ x, x ∈ region → F.decode c.1 x = target x)
    (hmass : q < region.sum (fun x => μ x)) :
    ¬ (∀ d : F.toEncodedFamily.BadCodes target,
        agreementMass μ target (F.decode d.1) ≤ q) := by
  exact F.not_badCodeAgreementBound_of_agrees_on_region_gt c region hagree hmass

theorem large_region_forces_positive_mass_bad_code_disagreement_regression
    {Input : Type u} [Fintype Input]
    {s : ℕ} (F : BitEncodedClassifierFamily Input s)
    {μ : PMF Input} {target : Input → Bool} {q : ℝ≥0∞}
    (hbound :
      ∀ c : F.toEncodedFamily.BadCodes target,
        agreementMass μ target (F.decode c.1) ≤ q)
    (c : F.toEncodedFamily.BadCodes target)
    (region : Finset Input)
    (hmass : q < region.sum (fun x => μ x)) :
    ∃ x, x ∈ region ∧ μ x ≠ 0 ∧ F.decode c.1 x ≠ target x := by
  exact
    F.exists_pos_mass_disagreement_in_region_of_badCodeAgreementBound_lt_mass
      hbound c region hmass

theorem region_agreeing_bad_code_forces_deceptive_sample_mass_regression
    {Input : Type u} [Fintype Input]
    {s : ℕ} (F : BitEncodedClassifierFamily Input s)
    {μ : PMF Input} {target : Input → Bool}
    (c : F.toEncodedFamily.BadCodes target)
    (region : Finset Input)
    (hagree : ∀ x, x ∈ region → F.decode c.1 x = target x)
    (m : ℕ) :
    region.sum (fun x => μ x) ^ m ≤
      F.toEncodedFamily.deceptiveSampleMass μ target m := by
  exact F.regionMass_pow_le_deceptiveSampleMass_of_badCode_agrees_on c region hagree m

theorem pure_agreement_bound_forces_global_decode_regression
    {Input : Type u} [Fintype Input]
    {s : ℕ} (F : BitEncodedClassifierFamily Input s)
    {x : Input} {target : Input → Bool} {q : ℝ≥0∞}
    (hbound :
      ∀ c : F.toEncodedFamily.BadCodes target,
        agreementMass (PMF.pure x) target (F.decode c.1) ≤ q)
    (hq_lt : q < 1)
    {code : BitCode s}
    (hagree : F.decode code x = target x) :
    F.decode code = target := by
  exact F.decode_eq_target_of_pure_agreementBound_lt_one hbound hq_lt hagree

theorem strict_agreement_bound_forces_positive_mass_disagreement_regression
    {Input : Type u} [Fintype Input]
    {s : ℕ} (F : BitEncodedClassifierFamily Input s)
    {μ : PMF Input} {target : Input → Bool} {q : ℝ≥0∞}
    (hbound :
      ∀ c : F.toEncodedFamily.BadCodes target,
        agreementMass μ target (F.decode c.1) ≤ q)
    (hq_lt : q < 1)
    (c : F.toEncodedFamily.BadCodes target) :
    ∃ x, μ x ≠ 0 ∧ F.decode c.1 x ≠ target x := by
  exact F.exists_pos_mass_disagreement_of_badCode_agreementBound_lt_one hbound hq_lt c

theorem exact_zab_recovery_forces_positive_mass_bad_code_disagreement_regression
    {Z : Type*} [Fintype Z] {r k : ℕ} {Index : Type*}
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hq_lt : q < 1)
    (i : Index)
    (c :
      (rawExactZABDecisionListBitFamily Z r k zfeat).toEncodedFamily.BadCodes
        (G.predict i)) :
    ∃ x, μ x ≠ 0 ∧
      (rawExactZABDecisionListBitFamily Z r k zfeat).decode c.1 x ≠
        G.predict i x := by
  exact h.exists_pos_mass_disagreement_of_badCode hq_lt i c

theorem exact_zab_recovery_region_mass_le_of_bad_code_agrees_regression
    {Z : Type*} [Fintype Z] {r k : ℕ} {Index : Type*}
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (i : Index)
    (c :
      (rawExactZABDecisionListBitFamily Z r k zfeat).toEncodedFamily.BadCodes
        (G.predict i))
    (region : Finset (ExactVisiblePostSwitchSurface Z k))
    (hagree :
      ∀ x, x ∈ region →
        (rawExactZABDecisionListBitFamily Z r k zfeat).decode c.1 x =
          G.predict i x) :
    region.sum (fun x => μ x) ≤ q := by
  exact h.regionMass_le_of_badCode_agrees_on i c region hagree

theorem exact_zab_recovery_large_region_forces_positive_mass_bad_code_disagreement_regression
    {Z : Type*} [Fintype Z] {r k : ℕ} {Index : Type*}
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (i : Index)
    (c :
      (rawExactZABDecisionListBitFamily Z r k zfeat).toEncodedFamily.BadCodes
        (G.predict i))
    (region : Finset (ExactVisiblePostSwitchSurface Z k))
    (hmass : q < region.sum (fun x => μ x)) :
    ∃ x, x ∈ region ∧ μ x ≠ 0 ∧
      (rawExactZABDecisionListBitFamily Z r k zfeat).decode c.1 x ≠
        G.predict i x := by
  exact h.exists_pos_mass_disagreement_in_region_of_badCode i c region hmass

theorem exact_zab_region_agreeing_bad_code_blocks_erm_recovery_regression
    {Z : Type*} [Fintype Z] {r k : ℕ} {Index : Type*}
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (i : Index)
    (c :
      (rawExactZABDecisionListBitFamily Z r k zfeat).toEncodedFamily.BadCodes
        (G.predict i))
    (region : Finset (ExactVisiblePostSwitchSurface Z k))
    (hagree :
      ∀ x, x ∈ region →
        (rawExactZABDecisionListBitFamily Z r k zfeat).decode c.1 x =
          G.predict i x)
    (hmass : q < region.sum (fun x => μ x)) :
    ¬ Nonempty (ExactZABERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ zfeat G q) := by
  exact
    not_ExactZABERMRecoveryData_of_badCode_agrees_on_region_gt
      (Z := Z) (r := r) (k := k) (Index := Index)
      i c region hagree hmass

theorem exact_zab_region_bad_code_forces_deceptive_sample_mass_regression
    {Z : Type*} [Fintype Z] {r k : ℕ} {Index : Type*}
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (i : Index)
    (c :
      (rawExactZABDecisionListBitFamily Z r k zfeat).toEncodedFamily.BadCodes
        (G.predict i))
    (region : Finset (ExactVisiblePostSwitchSurface Z k))
    (hagree :
      ∀ x, x ∈ region →
        (rawExactZABDecisionListBitFamily Z r k zfeat).decode c.1 x =
          G.predict i x)
    (m : ℕ) :
    region.sum (fun x => μ x) ^ m ≤
      (rawExactZABDecisionListBitFamily Z r k zfeat).toEncodedFamily.deceptiveSampleMass
        μ (G.predict i) m := by
  exact exactZAB_regionMass_pow_le_deceptiveSampleMass_of_badCode_agrees_on
    (Z := Z) (r := r) (k := k) (Index := Index) i c region hagree m

theorem exact_zab_pure_bad_code_blocks_erm_recovery_regression
    {Z : Type*} [Fintype Z] {r k : ℕ} {Index : Type*}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞} {x : ExactVisiblePostSwitchSurface Z k}
    (i : Index)
    (c :
      (rawExactZABDecisionListBitFamily Z r k zfeat).toEncodedFamily.BadCodes
        (G.predict i))
    (hagree :
      (rawExactZABDecisionListBitFamily Z r k zfeat).decode c.1 x =
        G.predict i x)
    (hq_lt : q < 1) :
    ¬ Nonempty (ExactZABERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index)
        (PMF.pure x) zfeat G q) := by
  exact
    not_ExactZABERMRecoveryData_of_pure_badCode_agrees
      (Z := Z) (r := r) (k := k) (Index := Index)
      i c hagree hq_lt

end Mettapedia.Computability.PNP.BadCodeAgreementObstructionRegression
