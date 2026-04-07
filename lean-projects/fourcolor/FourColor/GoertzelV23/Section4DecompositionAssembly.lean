import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Basic
import FourColor.GoertzelV23.Section4ConcreteTarget
import FourColor.GoertzelV23.Section4MeridionalTarget

open BigOperators
open scoped BigOperators

namespace FourColor.GoertzelV23

universe u v w

/--
Assembly data for the direct spanning route through Ben Goertzel's Lemma 4.5.

This file does not prove the additive closure of the Kempe-closure span from
first principles. Instead it makes that requirement explicit, together with the
three span-membership ingredients needed after Lemma 4.5:
- the null-relative part lies in the generator span
- the red meridian lies in the generator span
- the blue meridian lies in the generator span

From those, the concrete Section 4 spanning target follows.
-/
structure Section4DecompositionAssemblyData where
  Annulus : Type u
  Chain : Type v
  Generator : Annulus → Type w
  instAddCommMonoidChain : AddCommMonoid Chain
  instDecidableEqGenerator : ∀ A : Annulus, DecidableEq (Generator A)
  InZeroBoundary : (A : Annulus) → Chain → Prop
  InNullRelative : (A : Annulus) → Chain → Prop
  generatorValue : {A : Annulus} → Generator A → Chain
  meridianRed : Annulus → Chain
  meridianBlue : Annulus → Chain
  redFlux : Annulus → Chain → Bool
  blueFlux : Annulus → Chain → Bool
  decompose :
    ∀ {A : Annulus} {x : Chain},
      InZeroBoundary A x →
      ∃ xnull : Chain,
        InNullRelative A xnull ∧
        x =
          xnull
            + (if redFlux A x then meridianRed A else 0)
            + (if blueFlux A x then meridianBlue A else 0)
  generator_span_zero :
    ∀ A : Annulus,
      ∃ support : Finset (Generator A),
        (0 : Chain) = ∑ g ∈ support, generatorValue (A := A) g
  generator_span_add :
    ∀ {A : Annulus} {x y : Chain},
      (∃ support : Finset (Generator A),
        x = ∑ g ∈ support, generatorValue (A := A) g) →
      (∃ support : Finset (Generator A),
        y = ∑ g ∈ support, generatorValue (A := A) g) →
      ∃ support : Finset (Generator A),
        x + y = ∑ g ∈ support, generatorValue (A := A) g
  null_relative_in_generator_span :
    ∀ {A : Annulus} {x : Chain},
      InNullRelative A x →
      ∃ support : Finset (Generator A),
        x = ∑ g ∈ support, generatorValue (A := A) g
  meridianRed_in_generator_span :
    ∀ A : Annulus,
      ∃ support : Finset (Generator A),
        meridianRed A = ∑ g ∈ support, generatorValue (A := A) g
  meridianBlue_in_generator_span :
    ∀ A : Annulus,
      ∃ support : Finset (Generator A),
        meridianBlue A = ∑ g ∈ support, generatorValue (A := A) g

attribute [instance] Section4DecompositionAssemblyData.instAddCommMonoidChain
attribute [instance] Section4DecompositionAssemblyData.instDecidableEqGenerator

/-- The associated meridional decomposition package. -/
def Section4DecompositionAssemblyData.toMeridionalTarget
    (S : Section4DecompositionAssemblyData) :
    Section4MeridionalTarget where
  Annulus := S.Annulus
  Chain := S.Chain
  instAddCommMonoidChain := S.instAddCommMonoidChain
  InZeroBoundary := S.InZeroBoundary
  InNullRelative := S.InNullRelative
  meridianRed := S.meridianRed
  meridianBlue := S.meridianBlue
  redFlux := S.redFlux
  blueFlux := S.blueFlux
  decompose := S.decompose

/-- The Kempe-closure generator span extracted from the assembly data. -/
def Section4DecompositionAssemblyData.InGeneratorSpan
    (S : Section4DecompositionAssemblyData) :
    (A : S.Annulus) → S.Chain → Prop :=
  fun A x =>
    ∃ support : Finset (S.Generator A),
      x = ∑ g ∈ support, S.generatorValue (A := A) g

/--
The direct decomposition route yields Ben's concrete Section 4 spanning theorem.
-/
theorem Section4DecompositionAssemblyData.theorem_4_9
    (S : Section4DecompositionAssemblyData) :
    ∀ {A : S.Annulus} {x : S.Chain},
      S.InZeroBoundary A x →
      S.InGeneratorSpan A x := by
  intro A x hx
  let M := S.toMeridionalTarget
  have hzero : ∀ A : S.Annulus, S.InGeneratorSpan A 0 := by
    intro A
    exact S.generator_span_zero A
  have hadd :
      ∀ {A : S.Annulus} {x y : S.Chain},
        S.InGeneratorSpan A x →
        S.InGeneratorSpan A y →
        S.InGeneratorSpan A (x + y) := by
    intro A x y hx hy
    exact S.generator_span_add hx hy
  have hnull :
      ∀ {A : S.Annulus} {x : S.Chain},
        M.InNullRelative A x →
        S.InGeneratorSpan A x := by
    intro A x hxnull
    exact S.null_relative_in_generator_span hxnull
  have hMr : ∀ A : S.Annulus, S.InGeneratorSpan A (M.meridianRed A) := by
    intro A
    exact S.meridianRed_in_generator_span A
  have hMb : ∀ A : S.Annulus, S.InGeneratorSpan A (M.meridianBlue A) := by
    intro A
    exact S.meridianBlue_in_generator_span A
  exact M.liftSpanFromNullRelative hzero @hadd @hnull hMr hMb hx

/-- Convert the decomposition route directly into the concrete Section 4 target. -/
def Section4DecompositionAssemblyData.toConcreteTarget
    (S : Section4DecompositionAssemblyData) :
    Section4ConcreteTarget where
  Annulus := S.Annulus
  Chain := S.Chain
  KempeClosureGenerator := S.Generator
  instAddCommMonoidChain := S.instAddCommMonoidChain
  instDecidableEqGenerator := S.instDecidableEqGenerator
  InZeroBoundary := S.InZeroBoundary
  generatorValue := S.generatorValue
  theorem_4_9 := S.theorem_4_9

end FourColor.GoertzelV23
