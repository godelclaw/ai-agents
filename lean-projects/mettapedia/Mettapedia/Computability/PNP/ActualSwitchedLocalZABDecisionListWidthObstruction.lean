import Mettapedia.Computability.PNP.ActualSwitchedLocalStructure
import Mettapedia.Computability.PNP.BitVecZABCompressionObstruction

/-!
# P vs NP crux: actual switched-local ZAB data still forces exponential extractor width

The manuscript's switched-local normal form is already formalized by
`ActualSwitchedLocalInterface`.  The concrete exact-route strengthening used by
the current PNP packet is `ActualSwitchedLocalInterface.ZABDecisionListData`:
every selected local rule must come from one shared exact `(zfeat z, a, b)`
decision-list family.

This file lifts the live injective-branch arithmetic onto that manuscript-facing
data interface.  If the resulting predictor family is still surjective on the
full exact visible surface, then:

* abstractly, the extractor width must be at least
  `|ExactVisiblePostSwitchSurface Z k| - (2k + 1)`;
* on the bit-valued surface `Z = BitVec n`, this becomes
  `r ≥ 2^(n + 2k) - (2k + 1)`.

So the remaining injective branch cannot be repaired on the current actual-local
ZAB route by keeping the extractor merely linear-sized.
-/

namespace Mettapedia.Computability.PNP

universe u v w

namespace ActualSwitchedLocalInterface

section Abstract

variable {Z : Type v} [Fintype Z] {k r : ℕ} {Index : Type u} {Block : Type w}
variable {T : ActualSwitchedLocalInterface Z k Index Block}
variable {zfeat : Z → BitVec r}

/-- If an actual switched-local family is both surjective and realized by one
shared exact `(zfeat z, a, b)` decision-list class, then the extractor width
must absorb the whole visible-surface cardinality gap. -/
theorem ZABDecisionListData.visibleCardGapLowerBound_of_surjective_predict
    (h : ZABDecisionListData T zfeat)
    (hsurj : Function.Surjective T.predictorFamily.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) - (2 * k + 1) ≤ r := by
  have hs : Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ r + 2 * k + 1 :=
    h.targetData.surfaceCard_le_of_surjective_predict hsurj
  rw [Nat.sub_le_iff_le_add]
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hs

/-- Therefore a surjective actual switched-local family cannot carry exact ZAB
decision-list data below the visible-surface cardinality gap. -/
theorem not_nonempty_zabDecisionListData_of_surjective_predict_of_lt_visibleCardGap
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (zfeat : Z → BitVec r)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    (hgap : r < Fintype.card (ExactVisiblePostSwitchSurface Z k) - (2 * k + 1)) :
    ¬ Nonempty (ZABDecisionListData T zfeat) := by
  rintro ⟨h⟩
  exact Nat.not_le_of_lt hgap <|
    h.visibleCardGapLowerBound_of_surjective_predict hsurj

end Abstract

section BitVec

variable {n k r : ℕ} {Index : Type u} {Block : Type w}
variable {T : ActualSwitchedLocalInterface (BitVec n) k Index Block}
variable {zfeat : BitVec n → BitVec r}

/-- On the concrete `BitVec n` visible surface, surjective actual-local exact
ZAB data forces extractor width at least `2^(n + 2k) - (2k + 1)`. -/
theorem ZABDecisionListData.extractorWidthLowerBound_of_surjective_predict
    (h : ZABDecisionListData T zfeat)
    (hsurj : Function.Surjective T.predictorFamily.predict) :
    2 ^ (n + 2 * k) - (2 * k + 1) ≤ r := by
  simpa [card_exactVisiblePostSwitchSurface_bitVec] using
    (h.visibleCardGapLowerBound_of_surjective_predict hsurj)

/-- Hence a surjective `BitVec n` actual-local family cannot carry exact ZAB
decision-list data when the extractor width stays below the full truth-table
gap. -/
theorem not_nonempty_zabDecisionListData_of_surjective_predict_of_extractorWidth_lt_truthTableGap
    (T : ActualSwitchedLocalInterface (BitVec n) k Index Block)
    (zfeat : BitVec n → BitVec r)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    (hgap : r < 2 ^ (n + 2 * k) - (2 * k + 1)) :
    ¬ Nonempty (ZABDecisionListData T zfeat) := by
  exact
    not_nonempty_zabDecisionListData_of_surjective_predict_of_lt_visibleCardGap
      (T := T) zfeat hsurj
      (by simpa [card_exactVisiblePostSwitchSurface_bitVec] using hgap)

/-- In particular, the full-rule actual-local counterexample still refutes the
exact ZAB route at every sub-threshold extractor width. -/
theorem fullRuleActualSwitchedLocalInterface_not_zabDecisionListData_of_extractorWidth_lt_truthTableGap
    (zfeat : BitVec n → BitVec r)
    (hgap : r < 2 ^ (n + 2 * k) - (2 * k + 1)) :
    ¬ Nonempty
        (ZABDecisionListData
          (fullRuleActualSwitchedLocalInterface (BitVec n) k) zfeat) := by
  exact
    not_nonempty_zabDecisionListData_of_surjective_predict_of_extractorWidth_lt_truthTableGap
      (T := fullRuleActualSwitchedLocalInterface (BitVec n) k)
      zfeat
      (fullRuleActualSwitchedLocalInterface_surjective (BitVec n) k)
      hgap

end BitVec

end ActualSwitchedLocalInterface

end Mettapedia.Computability.PNP
