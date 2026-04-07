namespace FourColor.GoertzelV23

universe u v w

/--
Theorem-back target for Ben Goertzel's dual-forest / annihilator proof of
Theorem 4.9.

This packages the actual proof mouth from Section 4.4:
- orthogonality to the generator family
- reduction to purified face constraints
- dual-forest peeling
- conclusion that the chain is zero

The point is to keep the proof spine explicit without yet committing to the
combinatorial implementation of faces, cuts, or peel order.
-/
structure Section4AnnihilatorTarget where
  Annulus : Type u
  Chain : Type v
  Generator : Annulus → Type w
  instZeroChain : Zero Chain
  InZeroBoundary : (A : Annulus) → Chain → Prop
  OrthogonalToGenerator : {A : Annulus} → Chain → Generator A → Prop
  PurifiedFaceReduction : (A : Annulus) → Chain → Prop
  HasDualForestPeeling : Annulus → Prop
  purified_face_reduction :
    ∀ {A : Annulus} {x : Chain},
      InZeroBoundary A x →
      (∀ g : Generator A, OrthogonalToGenerator x g) →
      PurifiedFaceReduction A x
  dual_forest_peeling :
    ∀ {A : Annulus} {x : Chain},
      InZeroBoundary A x →
      PurifiedFaceReduction A x →
      HasDualForestPeeling A →
      x = 0
  interior_dual_spanning_forest :
    ∀ A : Annulus, HasDualForestPeeling A

attribute [instance] Section4AnnihilatorTarget.instZeroChain

/--
Ben's annihilator form of Theorem 4.9: any zero-boundary chain orthogonal to
the full generator family must be zero.
-/
theorem Section4AnnihilatorTarget.annihilator_zero
    (S : Section4AnnihilatorTarget) :
    ∀ {A : S.Annulus} {x : S.Chain},
      S.InZeroBoundary A x →
      (∀ g : S.Generator A, S.OrthogonalToGenerator x g) →
      x = 0 := by
  intro A x hx horth
  exact
    S.dual_forest_peeling
      hx
      (S.purified_face_reduction hx horth)
      (S.interior_dual_spanning_forest A)

end FourColor.GoertzelV23
