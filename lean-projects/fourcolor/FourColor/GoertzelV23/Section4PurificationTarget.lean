import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Basic

open BigOperators
open scoped BigOperators

namespace FourColor.GoertzelV23

universe u v w z

/--
Theorem-back target for Ben Goertzel's purification step in Section 4.2.

This isolates the bridge from null-relative face-boundary data to the actual
Kempe-closure generator family:
- null-relative chains are finite sums of purified generators
- each purified generator lies in the span of Kempe-closure generators

The file keeps the statement algebraic and finite, without yet committing to the
paper's concrete run/cycle combinatorics.
-/
structure Section4PurificationTarget where
  Annulus : Type u
  Chain : Type v
  PurifiedGenerator : Annulus → Type w
  Generator : Annulus → Type z
  instAddCommMonoidChain : AddCommMonoid Chain
  instDecidableEqPurifiedGenerator : ∀ A : Annulus, DecidableEq (PurifiedGenerator A)
  instDecidableEqGenerator : ∀ A : Annulus, DecidableEq (Generator A)
  InNullRelative : (A : Annulus) → Chain → Prop
  purifiedValue : {A : Annulus} → PurifiedGenerator A → Chain
  generatorValue : {A : Annulus} → Generator A → Chain
  null_relative_spanning :
    ∀ {A : Annulus} {x : Chain},
      InNullRelative A x →
      ∃ support : Finset (PurifiedGenerator A),
        x = ∑ g ∈ support, purifiedValue (A := A) g
  purified_generator_in_generator_span :
    ∀ {A : Annulus} (g : PurifiedGenerator A),
      ∃ support : Finset (Generator A),
        purifiedValue (A := A) g = ∑ h ∈ support, generatorValue (A := A) h

attribute [instance] Section4PurificationTarget.instAddCommMonoidChain
attribute [instance] Section4PurificationTarget.instDecidableEqPurifiedGenerator
attribute [instance] Section4PurificationTarget.instDecidableEqGenerator

/-- Finite span of purified generators inside a fixed annulus. -/
def Section4PurificationTarget.InPurifiedSpan
    (S : Section4PurificationTarget) :
    (A : S.Annulus) → S.Chain → Prop :=
  fun A x =>
    ∃ support : Finset (S.PurifiedGenerator A),
      x = ∑ g ∈ support, S.purifiedValue (A := A) g

/-- Finite span of Kempe-closure generators inside a fixed annulus. -/
def Section4PurificationTarget.InGeneratorSpan
    (S : Section4PurificationTarget) :
    (A : S.Annulus) → S.Chain → Prop :=
  fun A x =>
    ∃ support : Finset (S.Generator A),
      x = ∑ g ∈ support, S.generatorValue (A := A) g

/-- Null-relative chains lie in the purified span. -/
theorem Section4PurificationTarget.null_relative_in_purified_span
    (S : Section4PurificationTarget) :
    ∀ {A : S.Annulus} {x : S.Chain},
      S.InNullRelative A x →
      S.InPurifiedSpan A x := by
  intro A x hx
  exact S.null_relative_spanning hx

/-- Every purified generator lies in the Kempe-closure generator span. -/
theorem Section4PurificationTarget.purified_value_in_generator_span
    (S : Section4PurificationTarget) :
    ∀ {A : S.Annulus} (g : S.PurifiedGenerator A),
      S.InGeneratorSpan A (S.purifiedValue (A := A) g) := by
  intro A g
  exact S.purified_generator_in_generator_span g

/--
If the Kempe-closure span contains `0` and is closed under addition, then the
entire purified span lands in the Kempe-closure span.
-/
theorem Section4PurificationTarget.purified_span_in_generator_span
    (S : Section4PurificationTarget)
    (hzero : ∀ A : S.Annulus, S.InGeneratorSpan A 0)
    (hadd :
      ∀ {A : S.Annulus} {x y : S.Chain},
        S.InGeneratorSpan A x →
        S.InGeneratorSpan A y →
        S.InGeneratorSpan A (x + y)) :
    ∀ {A : S.Annulus} {x : S.Chain},
      S.InPurifiedSpan A x →
      S.InGeneratorSpan A x := by
  intro A x hx
  rcases hx with ⟨support, rfl⟩
  classical
  refine Finset.induction_on support ?base ?step
  · simpa using hzero A
  · intro g s hg hs
    have hg' : S.InGeneratorSpan A (S.purifiedValue (A := A) g) :=
      S.purified_value_in_generator_span g
    have hs' :
        S.InGeneratorSpan A (∑ h ∈ s, S.purifiedValue (A := A) h) :=
      hs
    simpa [Finset.sum_insert, hg] using hadd hg' hs'

/--
Corollary: null-relative chains lie in the Kempe-closure generator span once
the latter has the expected additive closure properties.
-/
theorem Section4PurificationTarget.null_relative_in_generator_span
    (S : Section4PurificationTarget)
    (hzero : ∀ A : S.Annulus, S.InGeneratorSpan A 0)
    (hadd :
      ∀ {A : S.Annulus} {x y : S.Chain},
        S.InGeneratorSpan A x →
        S.InGeneratorSpan A y →
        S.InGeneratorSpan A (x + y)) :
    ∀ {A : S.Annulus} {x : S.Chain},
      S.InNullRelative A x →
      S.InGeneratorSpan A x := by
  intro A x hx
  exact
    S.purified_span_in_generator_span hzero hadd
      (S.null_relative_in_purified_span hx)

end FourColor.GoertzelV23
