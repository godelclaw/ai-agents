import FourColor.GoertzelV23.Section6BoundaryTarget
import FourColor.GoertzelV23.Section6RepairBasisTarget
import FourColor.GoertzelV23.Section6ExceptionalPairingTarget

namespace FourColor.GoertzelV23

universe u v w z

/--
Unified theorem-back package for Ben Goertzel's Section 6.

This is the chapter-level assembly for the CAP5 package. It puts the boundary
criterion, repair basis, and exceptional-pairing exclusion under one shared
signature and derives the existing `Section6Target`.

What remains explicit after this assembly is the final chapter-level bridge from
realized repair types on arbitrary bad CAP5 cases back to concrete good boundary
words/extensible outside colorings.
-/
structure Section6ChapterData where
  BoundaryWord : Type u
  RepairType : Type v
  Counterexample : Type w
  MoveType : Type z
  ParityAllowed : BoundaryWord → Prop
  GoodBoundaryWord : BoundaryWord → Prop
  BadBoundaryWord : BoundaryWord → Prop
  ExtendsAcrossCap : BoundaryWord → Prop
  CanonicalBadWord : BoundaryWord
  InRepairBasis : RepairType → Prop
  repairedCanonicalWord : RepairType → BoundaryWord
  MinimalCounterexample : Counterexample → Prop
  Cap5Case : Counterexample → MoveType → Prop
  ExceptionalPairing : Counterexample → MoveType → Prop
  RealizedRepairType : Counterexample → MoveType → RepairType → Prop
  parity_normal_form :
    ∀ {w : BoundaryWord},
      ParityAllowed w →
      GoodBoundaryWord w ∨ BadBoundaryWord w
  lemma_6_4 :
    ∀ {w : BoundaryWord},
      GoodBoundaryWord w ↔ ExtendsAcrossCap w
  canonical_bad :
    BadBoundaryWord CanonicalBadWord
  lemma_6_6 :
    ∀ {r : RepairType},
      InRepairBasis r →
      GoodBoundaryWord (repairedCanonicalWord r)
  repair_or_exceptional :
    ∀ {C : Counterexample} {m : MoveType},
      MinimalCounterexample C →
      Cap5Case C m →
      (∃ r : RepairType, InRepairBasis r ∧ RealizedRepairType C m r)
        ∨ ExceptionalPairing C m
  sublemma_6_8 :
    ∀ {C : Counterexample} {m : MoveType},
      MinimalCounterexample C →
      Cap5Case C m →
      ¬ ExceptionalPairing C m
  repairedBoundaryWord : Counterexample → MoveType → RepairType → BoundaryWord

/-- Extract the Section 6 boundary package. -/
def Section6ChapterData.toBoundaryTarget
    (S : Section6ChapterData) :
    Section6BoundaryTarget where
  BoundaryWord := S.BoundaryWord
  ParityAllowed := S.ParityAllowed
  GoodBoundaryWord := S.GoodBoundaryWord
  BadBoundaryWord := S.BadBoundaryWord
  ExtendsAcrossCap := S.ExtendsAcrossCap
  parity_normal_form := S.parity_normal_form
  lemma_6_4 := S.lemma_6_4

/-- Extract the finite repair-basis package. -/
def Section6ChapterData.toRepairBasisTarget
    (S : Section6ChapterData) :
    Section6RepairBasisTarget where
  boundary := S.toBoundaryTarget
  RepairType := S.RepairType
  CanonicalBadWord := S.CanonicalBadWord
  InRepairBasis := S.InRepairBasis
  repairedCanonicalWord := S.repairedCanonicalWord
  canonical_bad := S.canonical_bad
  lemma_6_6 := S.lemma_6_6

/-- Extract the exceptional-pairing / move-realizability core. -/
def Section6ChapterData.toExceptionalPairingTarget
    (S : Section6ChapterData) :
    Section6ExceptionalPairingTarget where
  Counterexample := S.Counterexample
  MoveType := S.MoveType
  RepairType := S.RepairType
  MinimalCounterexample := S.MinimalCounterexample
  Cap5Case := S.Cap5Case
  ExceptionalPairing := S.ExceptionalPairing
  InRepairBasis := S.InRepairBasis
  RealizedRepairType := S.RealizedRepairType
  repair_or_exceptional := S.repair_or_exceptional
  sublemma_6_8 := S.sublemma_6_8

/-- Extract the existing abstract Section 6 target. -/
def Section6ChapterData.toSection6Target
    (S : Section6ChapterData) :
    Section6Target :=
  (S.toExceptionalPairingTarget).toSection6Target

/-- Chapter-level form of Lemma 6.7. -/
theorem Section6ChapterData.lemma_6_7
    (S : Section6ChapterData) :
    ∀ {C : S.Counterexample} {m : S.MoveType},
      S.MinimalCounterexample C →
      S.Cap5Case C m →
      (S.toExceptionalPairingTarget).MoveRealizable C m := by
  intro C m hminimal hcap5
  exact (S.toExceptionalPairingTarget).lemma_6_7 hminimal hcap5

/--
The explicit remaining chapter-level gap after the current assembly: connecting
realized repair types on arbitrary bad CAP5 cases back to concrete good boundary
words suitable for the extension criterion.
-/
def Section6ChapterData.RemainingGap (S : Section6ChapterData) : Prop :=
  ∀ {C : S.Counterexample} {m : S.MoveType} {r : S.RepairType},
    S.MinimalCounterexample C →
    S.Cap5Case C m →
    S.InRepairBasis r →
    S.RealizedRepairType C m r →
    S.GoodBoundaryWord (S.repairedBoundaryWord C m r)

/--
If the remaining gap closes, every realized repair yields an extendable CAP5
boundary word.
-/
theorem Section6ChapterData.realized_repair_extends
    (S : Section6ChapterData)
    (hgap : S.RemainingGap) :
    ∀ {C : S.Counterexample} {m : S.MoveType} {r : S.RepairType},
      S.MinimalCounterexample C →
      S.Cap5Case C m →
      S.InRepairBasis r →
      S.RealizedRepairType C m r →
      S.ExtendsAcrossCap (S.repairedBoundaryWord C m r) := by
  intro C m r hminimal hcap5 hr hrealized
  exact
    (S.toBoundaryTarget).good_implies_extends
      (hgap hminimal hcap5 hr hrealized)

end FourColor.GoertzelV23
