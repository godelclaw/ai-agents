namespace FourColor.GoertzelV23

universe u v

/--
The Section 6 theorem-back target for Ben Goertzel's `v23` route.

This isolates the `CAP5` burden:
- `MinimalCounterexample C` is the active counterexample regime
- `Cap5Case C m` is the local move-type case under inspection
- `ExceptionalPairing C m` is the pairing obstruction excluded by Sublemma 6.8
- `MoveRealizable C m` is the realizability conclusion supplied by Lemma 6.7

The package is intentionally theorem-back: it records the exact local mouth that
must close without importing the old reducibility proof surface.
-/
structure Section6Target where
  Counterexample : Type u
  MoveType : Type v
  MinimalCounterexample : Counterexample → Prop
  Cap5Case : Counterexample → MoveType → Prop
  ExceptionalPairing : Counterexample → MoveType → Prop
  MoveRealizable : Counterexample → MoveType → Prop
  sublemma_6_8 :
    ∀ {C : Counterexample} {m : MoveType},
      MinimalCounterexample C →
      Cap5Case C m →
      ¬ ExceptionalPairing C m
  lemma_6_7 :
    ∀ {C : Counterexample} {m : MoveType},
      MinimalCounterexample C →
      Cap5Case C m →
      ¬ ExceptionalPairing C m →
      MoveRealizable C m

/--
The extracted Section 6 normal-form predicate: every minimal `CAP5` case is
realizable once the exceptional pairing has been ruled out.
-/
def Section6Target.Cap5FreeNormalForm (S : Section6Target) : Prop :=
  ∀ {C : S.Counterexample} {m : S.MoveType},
    S.MinimalCounterexample C →
    S.Cap5Case C m →
    S.MoveRealizable C m

/-- Ben Section 6 yields the `CAP5`-free normal form package. -/
theorem Section6Target.cap5_free_normal_form (S : Section6Target) :
    S.Cap5FreeNormalForm := by
  intro C m hminimal hcap5
  exact
    S.lemma_6_7
      hminimal
      hcap5
      (S.sublemma_6_8 hminimal hcap5)

end FourColor.GoertzelV23
