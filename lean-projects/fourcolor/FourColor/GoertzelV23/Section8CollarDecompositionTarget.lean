namespace FourColor.GoertzelV23

universe u v

/--
The Section 8.4 theorem-back target for Ben Goertzel's `v23` route.

This packages the bounded-width collar decomposition side of the operator
chapter:
- Lemma 8.5: a radius-1 collar cuts open to a bounded gadget chain
- Lemma 8.6: every such gadget is the canonical three-cell gadget up to mirror
-/
structure Section8CollarDecompositionTarget where
  Collar : Type u
  Gadget : Type v
  RadiusOneCollar : Collar → Prop
  CutOpenTo : Collar → Gadget → Prop
  CanonicalThreeCell : Gadget → Prop
  MirrorCanonicalThreeCell : Gadget → Prop
  Decomposable : Gadget → Prop
  lemma_8_5 :
    ∀ {A : Collar},
      RadiusOneCollar A →
      ∃ G : Gadget, CutOpenTo A G ∧ Decomposable G
  lemma_8_6 :
    ∀ {A : Collar} {G : Gadget},
      CutOpenTo A G →
      Decomposable G →
      CanonicalThreeCell G ∨ MirrorCanonicalThreeCell G

/-- The canonical gadget family from Ben's Lemma 8.6. -/
def Section8CollarDecompositionTarget.CanonicalFamily
    (S : Section8CollarDecompositionTarget) : S.Gadget → Prop :=
  fun G => S.CanonicalThreeCell G ∨ S.MirrorCanonicalThreeCell G

/-- Every radius-1 collar has a cut-open gadget in the canonical family. -/
theorem Section8CollarDecompositionTarget.radius_one_collar_has_canonical_family
    (S : Section8CollarDecompositionTarget) :
    ∀ {A : S.Collar},
      S.RadiusOneCollar A →
      ∃ G : S.Gadget, S.CutOpenTo A G ∧ S.CanonicalFamily G := by
  intro A hcollar
  rcases S.lemma_8_5 hcollar with ⟨G, hcut, hdecomp⟩
  exact ⟨G, hcut, S.lemma_8_6 hcut hdecomp⟩

end FourColor.GoertzelV23
