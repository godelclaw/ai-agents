namespace FourColor.GoertzelV23

universe u v

/--
The Section 7.4 theorem-back target for Ben Goertzel's `v23` route.

This isolates the local forcing engine:
- Sublemma 7.7: the three-cell patch admits a radius-1 tube
- Lemma 7.8: the tube forces the required local consequence
-/
structure Section7TubeForcingTarget where
  Patch : Type u
  Tube : Type v
  ThreeCellPatch : Patch → Prop
  RadiusOneTube : Patch → Tube → Prop
  TubeForced : Patch → Tube → Prop
  sublemma_7_7 :
    ∀ {P : Patch},
      ThreeCellPatch P →
      ∃ T : Tube, RadiusOneTube P T
  lemma_7_8 :
    ∀ {P : Patch} {T : Tube},
      RadiusOneTube P T →
      TubeForced P T

/-- Extracted Section 7.4 output: every three-cell patch admits a forced tube. -/
def Section7TubeForcingTarget.ForcedLocalTube
    (S : Section7TubeForcingTarget) : Prop :=
  ∀ {P : S.Patch},
    S.ThreeCellPatch P →
    ∃ T : S.Tube, S.TubeForced P T

theorem Section7TubeForcingTarget.forced_local_tube
    (S : Section7TubeForcingTarget) :
    S.ForcedLocalTube := by
  intro P hpatch
  rcases S.sublemma_7_7 hpatch with ⟨T, htube⟩
  exact ⟨T, S.lemma_7_8 htube⟩

end FourColor.GoertzelV23
