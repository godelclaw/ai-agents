namespace FourColor.GoertzelV23

universe u v

/--
The Section 4 theorem target for Ben Goertzel's `v23` route.

This isolates the annular spanning mouth:
- `InZeroBoundary A x` is the annular difference-space side
- `InGeneratorSpan A x` is the Kempe-closure-generator side

The field `theorem_4_9` is the direct formal target corresponding to the
annular spanning theorem.
-/
structure Section4Target where
  Annulus : Type u
  Chain : Type v
  InZeroBoundary : Annulus → Chain → Prop
  InGeneratorSpan : Annulus → Chain → Prop
  theorem_4_9 :
    ∀ {A : Annulus} {x : Chain},
      InZeroBoundary A x → InGeneratorSpan A x

/-- The per-annulus spanning predicate extracted from the Section 4 package. -/
def Section4Target.AnnularSpanning (S : Section4Target) : S.Annulus → Prop :=
  fun A => ∀ x : S.Chain, S.InZeroBoundary A x → S.InGeneratorSpan A x

/-- Ben Section 4 package yields annular spanning for every annulus. -/
theorem Section4Target.allAnnuliSpan (S : Section4Target) :
    ∀ A : S.Annulus, S.AnnularSpanning A := by
  intro A x hx
  exact S.theorem_4_9 hx

end FourColor.GoertzelV23
