import Mettapedia.Computability.PNP.ActualSwitchedLocalZABDecisionListWidthObstruction
import Mettapedia.Computability.PNP.ExactZABInjectiveBranchObstruction
import Mathlib.Tactic

/-!
# P vs NP crux: the same-width exact ZAB branch is already impossible

The remaining exact `z+a+b` branch after the collision blockers is the
injective-width side `r ≥ n`.  This file closes the smallest such sub-branch:
if the extractor stays same-width (`r = n`), then the exact/shared local
decision-list budget is still only `n + 2k + 1` bits.  Once the visible width
`n + 2k` is at least `2`, that budget is already smaller than the full exact
visible truth-table size `2^(n + 2k)`.

So even before asking whether a same-width extractor is injective, the current
exact ZAB route cannot be surjective on any nontrivial visible surface.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section Arithmetic

theorem sameWidthBudget_lt_surfaceCard_of_two_le_visibleWidth
    {n k : ℕ}
    (hvisible : 2 ≤ n + 2 * k) :
    n + 2 * k + 1 < 2 ^ (n + 2 * k) := by
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le hvisible
  rw [hc]
  have h :
      ∀ d : ℕ, d + 3 < 2 ^ (d + 2) := by
    intro d
    induction d with
    | zero =>
        norm_num
    | succ d ih =>
        have hle : d + 4 ≤ 2 ^ (d + 2) := Nat.succ_le_of_lt ih
        have hltpow : 2 ^ (d + 2) < 2 ^ (d + 3) := by
          have hpos : 0 < 2 ^ (d + 2) := by
            exact pow_pos (by decide) _
          calc
            2 ^ (d + 2) < 2 ^ (d + 2) + 2 ^ (d + 2) := Nat.lt_add_of_pos_right hpos
            _ = 2 ^ (d + 3) := by
              rw [← two_mul, Nat.mul_comm]
              simp [Nat.pow_succ]
        exact lt_of_le_of_lt hle hltpow
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h c

theorem sameWidthExtractor_lt_truthTableGap_of_two_le_visibleWidth
    {n k : ℕ}
    (hvisible : 2 ≤ n + 2 * k) :
    n < 2 ^ (n + 2 * k) - (2 * k + 1) := by
  have hbudget :
      n + 2 * k + 1 < 2 ^ (n + 2 * k) :=
    sameWidthBudget_lt_surfaceCard_of_two_le_visibleWidth (n := n) (k := k) hvisible
  omega

end Arithmetic

section ExactERM

variable {n k : ℕ} {Index : Type*}

theorem exactZABDecisionListERMFamily_not_surjective_of_sameWidth
    (zfeat : BitVec n → BitVec n)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool)
    (hvisible : 2 ≤ n + 2 * k) :
    ¬ Function.Surjective
        (exactZABDecisionListERMFamily
          (Z := BitVec n) (r := n) (k := k) zfeat samples).predict := by
  exact
    exactZABDecisionListERMFamily_not_surjective_of_extractorWidth_lt_truthTableGap
      (n := n) (r := n) (k := k) (Index := Index) zfeat samples
      (sameWidthExtractor_lt_truthTableGap_of_two_le_visibleWidth
        (n := n) (k := k) hvisible)

end ExactERM

namespace ActualSwitchedLocalInterface

section ActualLocal

universe u v

variable {n k : ℕ} {Index : Type u} {Block : Type v}

theorem not_nonempty_zabDecisionListData_of_surjective_predict_of_sameWidth
    (T : ActualSwitchedLocalInterface (BitVec n) k Index Block)
    (zfeat : BitVec n → BitVec n)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    (hvisible : 2 ≤ n + 2 * k) :
    ¬ Nonempty (ZABDecisionListData T zfeat) := by
  exact
    not_nonempty_zabDecisionListData_of_surjective_predict_of_extractorWidth_lt_truthTableGap
      (T := T) zfeat hsurj
      (sameWidthExtractor_lt_truthTableGap_of_two_le_visibleWidth
        (n := n) (k := k) hvisible)

theorem fullRuleActualSwitchedLocalInterface_not_zabDecisionListData_of_sameWidth
    (zfeat : BitVec n → BitVec n)
    (hvisible : 2 ≤ n + 2 * k) :
    ¬ Nonempty
        (ZABDecisionListData
          (fullRuleActualSwitchedLocalInterface (BitVec n) k) zfeat) := by
  exact
    not_nonempty_zabDecisionListData_of_surjective_predict_of_sameWidth
      (T := fullRuleActualSwitchedLocalInterface (BitVec n) k)
      zfeat
      (fullRuleActualSwitchedLocalInterface_surjective (BitVec n) k)
      hvisible

end ActualLocal

end ActualSwitchedLocalInterface

end Mettapedia.Computability.PNP
