import FourColor.GoertzelV23.Section6Target

namespace FourColor.GoertzelV23

universe u v w

/--
Theorem-back target for Ben Goertzel's Section 6.4 core:
Lemma 6.7 plus Sublemma 6.8.

The key proof shape is:
- every minimal CAP5 case either realizes a repair-basis move or falls into the
  exceptional pairing configuration
- the exceptional pairing configuration is impossible in the minimal regime
- therefore some repair-basis move is realized
-/
structure Section6ExceptionalPairingTarget where
  Counterexample : Type u
  MoveType : Type v
  RepairType : Type w
  MinimalCounterexample : Counterexample → Prop
  Cap5Case : Counterexample → MoveType → Prop
  ExceptionalPairing : Counterexample → MoveType → Prop
  InRepairBasis : RepairType → Prop
  RealizedRepairType : Counterexample → MoveType → RepairType → Prop
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

/-- Move realizability extracted from Lemma 6.7 plus Sublemma 6.8. -/
def Section6ExceptionalPairingTarget.MoveRealizable
    (S : Section6ExceptionalPairingTarget) :
    S.Counterexample → S.MoveType → Prop :=
  fun C m =>
    ∃ r : S.RepairType, S.InRepairBasis r ∧ S.RealizedRepairType C m r

/-- Ben's move-type realizability lemma in theorem form. -/
theorem Section6ExceptionalPairingTarget.lemma_6_7
    (S : Section6ExceptionalPairingTarget) :
    ∀ {C : S.Counterexample} {m : S.MoveType},
      S.MinimalCounterexample C →
      S.Cap5Case C m →
      S.MoveRealizable C m := by
  intro C m hminimal hcap5
  rcases S.repair_or_exceptional hminimal hcap5 with hrepair | hexc
  · exact hrepair
  · exact False.elim ((S.sublemma_6_8 hminimal hcap5) hexc)

/-- Convert the repaired core directly into the existing Section 6 target. -/
def Section6ExceptionalPairingTarget.toSection6Target
    (S : Section6ExceptionalPairingTarget) :
    Section6Target where
  Counterexample := S.Counterexample
  MoveType := S.MoveType
  MinimalCounterexample := S.MinimalCounterexample
  Cap5Case := S.Cap5Case
  ExceptionalPairing := S.ExceptionalPairing
  MoveRealizable := S.MoveRealizable
  sublemma_6_8 := S.sublemma_6_8
  lemma_6_7 := by
    intro C m hminimal hcap5 _
    exact S.lemma_6_7 hminimal hcap5

end FourColor.GoertzelV23
