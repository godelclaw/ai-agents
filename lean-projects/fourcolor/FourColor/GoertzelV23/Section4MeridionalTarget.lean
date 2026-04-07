import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace FourColor.GoertzelV23

universe u v

/--
Theorem-back target for Ben Goertzel's Lemma 4.5.

This isolates the annular decomposition mouth:
- `InZeroBoundary A x` is the full annular difference space `W₀(H)`
- `InNullRelative A x` is the null-relative part spanned by internal face data
- `meridianRed A` and `meridianBlue A` are the two explicit meridional classes
- `redFlux` and `blueFlux` are the two annular flux coordinates

The field `decompose` is the exact lemma-back statement: every zero-boundary
chain splits into a null-relative piece plus the two meridional classes with
`F₂`-style coefficients.
-/
structure Section4MeridionalTarget where
  Annulus : Type u
  Chain : Type v
  instAddCommMonoidChain : AddCommMonoid Chain
  InZeroBoundary : (A : Annulus) → Chain → Prop
  InNullRelative : (A : Annulus) → Chain → Prop
  meridianRed : Annulus → Chain
  meridianBlue : Annulus → Chain
  redFlux : (A : Annulus) → Chain → Bool
  blueFlux : (A : Annulus) → Chain → Bool
  decompose :
    ∀ {A : Annulus} {x : Chain},
      InZeroBoundary A x →
      ∃ xnull : Chain,
        InNullRelative A xnull ∧
        x =
          xnull
            + (if redFlux A x then meridianRed A else 0)
            + (if blueFlux A x then meridianBlue A else 0)

attribute [instance] Section4MeridionalTarget.instAddCommMonoidChain

/--
Lift any additive span predicate from the null-relative subspace and the two
meridians to all of `W₀(H)`.

This is the exact algebraic use of Lemma 4.5 inside Ben's Section 4 proof.
-/
theorem Section4MeridionalTarget.liftSpanFromNullRelative
    (S : Section4MeridionalTarget)
    {P : S.Annulus → S.Chain → Prop}
    (hzero : ∀ A : S.Annulus, P A 0)
    (hadd :
      ∀ {A : S.Annulus} {x y : S.Chain},
        P A x → P A y → P A (x + y))
    (hnull :
      ∀ {A : S.Annulus} {x : S.Chain},
        S.InNullRelative A x → P A x)
    (hMr : ∀ A : S.Annulus, P A (S.meridianRed A))
    (hMb : ∀ A : S.Annulus, P A (S.meridianBlue A)) :
    ∀ {A : S.Annulus} {x : S.Chain},
      S.InZeroBoundary A x →
      P A x := by
  intro A x hx
  have hred : P A (if S.redFlux A x then S.meridianRed A else 0) := by
    by_cases hr : S.redFlux A x
    · simp [hr, hMr A]
    · simp [hr, hzero A]
  have hblue : P A (if S.blueFlux A x then S.meridianBlue A else 0) := by
    by_cases hb : S.blueFlux A x
    · simp [hb, hMb A]
    · simp [hb, hzero A]
  rcases S.decompose hx with ⟨xnull, hxnull, hdecomp⟩
  rw [hdecomp]
  exact hadd (hadd (hnull hxnull) hred) hblue

end FourColor.GoertzelV23
