namespace FourColor.GoertzelV23

universe u v

/--
The Section 7 theorem-back target for Ben Goertzel's `v23` route.

This isolates the radius-1 locality package:
- `ThreeCellPatch P` is the local patch regime
- `RadiusOneTube P T` is the associated collar/tube view
- `TubeForced P T` records the forcing step
- `CommutativeOnTube P T` is the local commutativity conclusion

The theorem fields mirror the proof spine highlighted in the `v23` review map:
Sublemma 7.7 followed by Lemmas 7.8-7.10.
-/
structure Section7Target where
  Patch : Type u
  Tube : Type v
  ThreeCellPatch : Patch → Prop
  RadiusOneTube : Patch → Tube → Prop
  TubeForced : Patch → Tube → Prop
  CommutativeOnTube : Patch → Tube → Prop
  sublemma_7_7 :
    ∀ {P : Patch},
      ThreeCellPatch P →
      ∃ T : Tube, RadiusOneTube P T
  lemma_7_8 :
    ∀ {P : Patch} {T : Tube},
      RadiusOneTube P T →
      TubeForced P T
  lemma_7_9 :
    ∀ {P : Patch} {T : Tube},
      TubeForced P T →
      CommutativeOnTube P T
  lemma_7_10 :
    ∀ {P : Patch},
      ThreeCellPatch P →
      ∃ T : Tube, CommutativeOnTube P T

/--
The extracted Section 7 locality predicate: every three-cell patch admits a
radius-1 tube on which the local moves commute.
-/
def Section7Target.RadiusOneLocality (S : Section7Target) : Prop :=
  ∀ {P : S.Patch},
    S.ThreeCellPatch P →
    ∃ T : S.Tube, S.CommutativeOnTube P T

/-- Ben Section 7 yields the radius-1 locality package. -/
theorem Section7Target.radius_one_locality (S : Section7Target) :
    S.RadiusOneLocality := by
  intro P hpatch
  rcases S.sublemma_7_7 hpatch with ⟨T, htube⟩
  exact ⟨T, S.lemma_7_9 (S.lemma_7_8 htube)⟩

/--
Lemma 7.10 is stronger than the extracted locality package, so we expose it as a
derived corollary too. This keeps the theorem-back layer aligned with Ben's
actual proof spine rather than collapsing everything into one anonymous `Prop`.
-/
theorem Section7Target.three_cell_patch_commutes (S : Section7Target) :
    ∀ {P : S.Patch},
      S.ThreeCellPatch P →
      ∃ T : S.Tube, S.CommutativeOnTube P T := by
  intro P hpatch
  exact S.lemma_7_10 hpatch

end FourColor.GoertzelV23
