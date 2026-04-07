import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Basic
import FourColor.GoertzelV23.Section4Target

open BigOperators
open scoped BigOperators

namespace FourColor.GoertzelV23

universe u v w

/--
Concrete theorem-back target for Ben Goertzel's Section 4 spanning theorem.

This upgrades the earlier abstract `Section4Target` to the actual algebraic shape
used in `v23`: every zero-boundary annular difference chain is a finite `F₂`-style
sum of Kempe-closure generators supported in that annulus.

We still keep the statement theorem-back. The file records the correct finite-sum
mouth without committing yet to a specific combinatorial encoding of annuli,
chains, or generators.
-/
structure Section4ConcreteTarget where
  Annulus : Type u
  Chain : Type v
  KempeClosureGenerator : Annulus → Type w
  instAddCommMonoidChain : AddCommMonoid Chain
  instDecidableEqGenerator : ∀ A : Annulus, DecidableEq (KempeClosureGenerator A)
  InZeroBoundary : (A : Annulus) → Chain → Prop
  generatorValue : {A : Annulus} → KempeClosureGenerator A → Chain
  theorem_4_9 :
    ∀ {A : Annulus} {x : Chain},
      InZeroBoundary A x →
      ∃ support : Finset (KempeClosureGenerator A),
        x = ∑ g ∈ support, generatorValue (A := A) g

attribute [instance] Section4ConcreteTarget.instAddCommMonoidChain
attribute [instance] Section4ConcreteTarget.instDecidableEqGenerator

/-- Finite `F₂`-style Kempe-closure span inside a fixed annulus. -/
def Section4ConcreteTarget.InKempeClosureSpan
    (S : Section4ConcreteTarget) :
    (A : S.Annulus) → S.Chain → Prop :=
  fun A x =>
    ∃ support : Finset (S.KempeClosureGenerator A),
      x = ∑ g ∈ support, S.generatorValue (A := A) g

/-- Ben's Theorem 4.9 immediately yields span-membership in the concrete form. -/
theorem Section4ConcreteTarget.theorem_4_9_as_span
    (S : Section4ConcreteTarget) :
    ∀ {A : S.Annulus} {x : S.Chain},
      S.InZeroBoundary A x →
      S.InKempeClosureSpan A x := by
  intro A x hx
  exact S.theorem_4_9 hx

/--
Forgetful map from the concrete algebraic target to the earlier abstract
`Section4Target`.
-/
def Section4ConcreteTarget.toSection4Target
    (S : Section4ConcreteTarget) :
    Section4Target where
  Annulus := S.Annulus
  Chain := S.Chain
  InZeroBoundary := S.InZeroBoundary
  InGeneratorSpan := S.InKempeClosureSpan
  theorem_4_9 := by
    intro A x hx
    exact S.theorem_4_9_as_span hx

/-- The concrete target still yields annular spanning for every annulus. -/
theorem Section4ConcreteTarget.allAnnuliSpan
    (S : Section4ConcreteTarget) :
    ∀ A : S.Annulus, (S.toSection4Target).AnnularSpanning A := by
  intro A
  exact (S.toSection4Target).allAnnuliSpan A

end FourColor.GoertzelV23
