import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Basic
import FourColor.GoertzelV23.Section4PurificationTarget

open BigOperators
open scoped BigOperators

namespace FourColor.GoertzelV23

/--
Theorem-back target for the purified-face family used in Ben Goertzel's
Section 4.4 annihilator proof.

This packages the missing bridge from generator orthogonality to purified-face
orthogonality:
- a chain-level orthogonality relation
- its closure under finite `F₂`-style sums on the right
- the consequence that orthogonality to every Kempe-closure generator implies
  orthogonality to every purified face generator
-/
structure Section4PurifiedFaceTarget where
  purification : Section4PurificationTarget
  Orthogonal : purification.Chain → purification.Chain → Prop
  orthogonal_zero :
    ∀ x : purification.Chain, Orthogonal x 0
  orthogonal_add_right :
    ∀ {x y z : purification.Chain},
      Orthogonal x y →
      Orthogonal x z →
      Orthogonal x (y + z)

/-- Orthogonality to a Kempe-closure generator. -/
def Section4PurifiedFaceTarget.OrthogonalToGenerator
    (S : Section4PurifiedFaceTarget) :
    {A : S.purification.Annulus} →
      S.purification.Chain →
      S.purification.Generator A →
      Prop :=
  fun {A} x g =>
    S.Orthogonal x (S.purification.generatorValue (A := A) g)

/-- Orthogonality to a purified face generator. -/
def Section4PurifiedFaceTarget.OrthogonalToPurified
    (S : Section4PurifiedFaceTarget) :
    {A : S.purification.Annulus} →
      S.purification.Chain →
      S.purification.PurifiedGenerator A →
      Prop :=
  fun {A} x g =>
    S.Orthogonal x (S.purification.purifiedValue (A := A) g)

/--
The purified-face reduction predicate used by the annihilator route: a chain is
orthogonal to every purified face generator in the annulus.
-/
def Section4PurifiedFaceTarget.PurifiedFaceReduction
    (S : Section4PurifiedFaceTarget) :
    (A : S.purification.Annulus) → S.purification.Chain → Prop :=
  fun A x =>
    ∀ g : S.purification.PurifiedGenerator A,
      S.OrthogonalToPurified x g

/--
Orthogonality to every Kempe-closure generator extends to any finite generator
sum in the span.
-/
theorem Section4PurifiedFaceTarget.orthogonal_to_generator_span
    (S : Section4PurifiedFaceTarget) :
    ∀ {A : S.purification.Annulus} {x y : S.purification.Chain},
      (∀ g : S.purification.Generator A, S.OrthogonalToGenerator x g) →
      S.purification.InGeneratorSpan A y →
      S.Orthogonal x y := by
  intro A x y hgen hy
  rcases hy with ⟨support, rfl⟩
  classical
  refine Finset.induction_on support ?base ?step
  · simpa using S.orthogonal_zero x
  · intro g s hg hs
    have hg' : S.Orthogonal x (S.purification.generatorValue (A := A) g) :=
      hgen g
    have hs' :
        S.Orthogonal x (∑ h ∈ s, S.purification.generatorValue (A := A) h) :=
      hs
    simpa [Finset.sum_insert, hg] using S.orthogonal_add_right hg' hs'

/--
Orthogonality to every Kempe-closure generator forces orthogonality to every
purified face generator, by Ben's purification step.
-/
theorem Section4PurifiedFaceTarget.orthogonal_to_purified
    (S : Section4PurifiedFaceTarget) :
    ∀ {A : S.purification.Annulus}
      {x : S.purification.Chain}
      (g : S.purification.PurifiedGenerator A),
      (∀ h : S.purification.Generator A, S.OrthogonalToGenerator x h) →
      S.OrthogonalToPurified x g := by
  intro A x g hgen
  exact
    S.orthogonal_to_generator_span
      hgen
      (S.purification.purified_value_in_generator_span g)

/--
Main purified-face reduction theorem: orthogonality to all Kempe-closure
generators implies the purified-face constraint needed by Section 4.4.
-/
theorem Section4PurifiedFaceTarget.purified_face_reduction
    (S : Section4PurifiedFaceTarget) :
    ∀ {A : S.purification.Annulus} {x : S.purification.Chain},
      (∀ g : S.purification.Generator A, S.OrthogonalToGenerator x g) →
      S.PurifiedFaceReduction A x := by
  intro A x hgen g
  exact S.orthogonal_to_purified g hgen

end FourColor.GoertzelV23
