import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Basic
import FourColor.GoertzelV23.Section4ConcreteTarget
import FourColor.GoertzelV23.Section4PurificationTarget
import FourColor.GoertzelV23.Section4PurifiedFaceTarget
import FourColor.GoertzelV23.Section4MeridionalTarget
import FourColor.GoertzelV23.Section4AnnihilatorAssembly
import FourColor.GoertzelV23.Section4DecompositionAssembly

open BigOperators
open scoped BigOperators

namespace FourColor.GoertzelV23

universe u v w z

/--
Unified theorem-back package for Ben Goertzel's Section 4.

This file is the first chapter-level assembly of the Ben route. It puts the
shared algebraic data for Section 4 in one place and derives:
- the purification package
- the purified-face orthogonality package
- the meridional decomposition package
- the decomposition-based concrete spanning target
- the annihilator-route package

What remains explicit after this assembly is the genuine chapter-level gap:
bridging the annihilator route all the way back to the same concrete spanning
target, rather than merely to the annihilator-zero form.
-/
structure Section4ChapterData where
  Annulus : Type u
  Chain : Type v
  PurifiedGenerator : Annulus → Type w
  Generator : Annulus → Type z
  instAddCommMonoidChain : AddCommMonoid Chain
  instDecidableEqPurifiedGenerator : ∀ A : Annulus, DecidableEq (PurifiedGenerator A)
  instDecidableEqGenerator : ∀ A : Annulus, DecidableEq (Generator A)
  InZeroBoundary : (A : Annulus) → Chain → Prop
  InNullRelative : (A : Annulus) → Chain → Prop
  purifiedValue : {A : Annulus} → PurifiedGenerator A → Chain
  generatorValue : {A : Annulus} → Generator A → Chain
  meridianRed : Annulus → Chain
  meridianBlue : Annulus → Chain
  redFlux : Annulus → Chain → Bool
  blueFlux : Annulus → Chain → Bool
  Orthogonal : Chain → Chain → Prop
  HasDualForestPeeling : Annulus → Prop
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
  decompose :
    ∀ {A : Annulus} {x : Chain},
      InZeroBoundary A x →
      ∃ xnull : Chain,
        InNullRelative A xnull ∧
        x =
          xnull
            + (if redFlux A x then meridianRed A else 0)
            + (if blueFlux A x then meridianBlue A else 0)
  null_relative_spanning :
    ∀ {A : Annulus} {x : Chain},
      InNullRelative A x →
      ∃ support : Finset (PurifiedGenerator A),
        x = ∑ g ∈ support, purifiedValue (A := A) g
  purified_generator_in_generator_span :
    ∀ {A : Annulus} (g : PurifiedGenerator A),
      ∃ support : Finset (Generator A),
        purifiedValue (A := A) g = ∑ h ∈ support, generatorValue (A := A) h
  meridianRed_in_generator_span :
    ∀ A : Annulus,
      ∃ support : Finset (Generator A),
        meridianRed A = ∑ g ∈ support, generatorValue (A := A) g
  meridianBlue_in_generator_span :
    ∀ A : Annulus,
      ∃ support : Finset (Generator A),
        meridianBlue A = ∑ g ∈ support, generatorValue (A := A) g
  orthogonal_zero :
    ∀ x : Chain, Orthogonal x 0
  orthogonal_add_right :
    ∀ {x y z : Chain},
      Orthogonal x y →
      Orthogonal x z →
      Orthogonal x (y + z)
  dual_forest_peeling :
    ∀ {A : Annulus} {x : Chain},
      InZeroBoundary A x →
      (∀ g : PurifiedGenerator A, Orthogonal x (purifiedValue (A := A) g)) →
      HasDualForestPeeling A →
      x = 0
  interior_dual_spanning_forest :
    ∀ A : Annulus, HasDualForestPeeling A

attribute [instance] Section4ChapterData.instAddCommMonoidChain
attribute [instance] Section4ChapterData.instDecidableEqPurifiedGenerator
attribute [instance] Section4ChapterData.instDecidableEqGenerator

/-- Extract the purification package. -/
def Section4ChapterData.toPurificationTarget
    (S : Section4ChapterData) :
    Section4PurificationTarget where
  Annulus := S.Annulus
  Chain := S.Chain
  PurifiedGenerator := S.PurifiedGenerator
  Generator := S.Generator
  instAddCommMonoidChain := S.instAddCommMonoidChain
  instDecidableEqPurifiedGenerator := S.instDecidableEqPurifiedGenerator
  instDecidableEqGenerator := S.instDecidableEqGenerator
  InNullRelative := S.InNullRelative
  purifiedValue := S.purifiedValue
  generatorValue := S.generatorValue
  null_relative_spanning := S.null_relative_spanning
  purified_generator_in_generator_span := S.purified_generator_in_generator_span

/-- Extract the meridional decomposition package. -/
def Section4ChapterData.toMeridionalTarget
    (S : Section4ChapterData) :
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

/-- Extract the purified-face orthogonality package. -/
def Section4ChapterData.toPurifiedFaceTarget
    (S : Section4ChapterData) :
    Section4PurifiedFaceTarget where
  purification := S.toPurificationTarget
  Orthogonal := S.Orthogonal
  orthogonal_zero := S.orthogonal_zero
  orthogonal_add_right := S.orthogonal_add_right

/-- Extract the direct decomposition route. -/
def Section4ChapterData.toDecompositionAssemblyData
    (S : Section4ChapterData) :
    Section4DecompositionAssemblyData where
  Annulus := S.Annulus
  Chain := S.Chain
  Generator := S.Generator
  instAddCommMonoidChain := S.instAddCommMonoidChain
  instDecidableEqGenerator := S.instDecidableEqGenerator
  InZeroBoundary := S.InZeroBoundary
  InNullRelative := S.InNullRelative
  generatorValue := S.generatorValue
  meridianRed := S.meridianRed
  meridianBlue := S.meridianBlue
  redFlux := S.redFlux
  blueFlux := S.blueFlux
  decompose := S.decompose
  generator_span_zero := S.generator_span_zero
  generator_span_add := S.generator_span_add
  null_relative_in_generator_span := by
    intro A x hx
    exact
      (S.toPurificationTarget).null_relative_in_generator_span
        S.generator_span_zero
        @S.generator_span_add
        hx
  meridianRed_in_generator_span := S.meridianRed_in_generator_span
  meridianBlue_in_generator_span := S.meridianBlue_in_generator_span

/-- Extract the annihilator route. -/
def Section4ChapterData.toAnnihilatorAssemblyData
    (S : Section4ChapterData) :
    Section4AnnihilatorAssemblyData where
  purifiedFace := S.toPurifiedFaceTarget
  InZeroBoundary := S.InZeroBoundary
  HasDualForestPeeling := S.HasDualForestPeeling
  dual_forest_peeling := by
    intro A x hx hpurified hforest
    exact S.dual_forest_peeling hx hpurified hforest
  interior_dual_spanning_forest := S.interior_dual_spanning_forest

/-- Extract the concrete Section 4 target via the decomposition route. -/
def Section4ChapterData.toConcreteTarget
    (S : Section4ChapterData) :
    Section4ConcreteTarget :=
  (S.toDecompositionAssemblyData).toConcreteTarget

/-- Extract the annihilator target via the orthogonality route. -/
def Section4ChapterData.toAnnihilatorTarget
    (S : Section4ChapterData) :
    Section4AnnihilatorTarget :=
  (S.toAnnihilatorAssemblyData).toAnnihilatorTarget

/-- Decomposition-route form of Ben's Theorem 4.9. -/
theorem Section4ChapterData.theorem_4_9
    (S : Section4ChapterData) :
    ∀ {A : S.Annulus} {x : S.Chain},
      S.InZeroBoundary A x →
      (S.toConcreteTarget).InKempeClosureSpan A x := by
  intro A x hx
  exact (S.toConcreteTarget).theorem_4_9_as_span hx

/-- Annihilator-route form of Ben's Theorem 4.9. -/
theorem Section4ChapterData.annihilator_zero
    (S : Section4ChapterData) :
    ∀ {A : S.Annulus} {x : S.Chain},
      S.InZeroBoundary A x →
      (∀ g : S.Generator A,
        (S.toPurifiedFaceTarget).OrthogonalToGenerator x g) →
      x = 0 := by
  intro A x hx horth
  exact (S.toAnnihilatorTarget).annihilator_zero hx horth

/--
The explicit chapter-level remaining gap after the current assembly: the route
from annihilator-zero back to the same concrete spanning target.
-/
def Section4ChapterData.RemainingGap (S : Section4ChapterData) : Prop :=
  ∀ {A : S.Annulus} {x : S.Chain},
    S.InZeroBoundary A x →
    (x = 0 → (S.toConcreteTarget).InKempeClosureSpan A x) →
    (∀ g : S.Generator A,
      (S.toPurifiedFaceTarget).OrthogonalToGenerator x g) →
    (S.toConcreteTarget).InKempeClosureSpan A x

end FourColor.GoertzelV23
