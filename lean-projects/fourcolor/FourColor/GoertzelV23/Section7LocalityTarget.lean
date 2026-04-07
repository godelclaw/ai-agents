import FourColor.GoertzelV23.Section7Target
import FourColor.GoertzelV23.Section7TubeForcingTarget

namespace FourColor.GoertzelV23

/--
The Section 7.5-7.6 theorem-back target for Ben Goertzel's `v23` route.

This packages the cap-aware locality and commutativity finish:
- Lemma 7.9 upgrades forced tubes to local commutativity
- Lemma 7.10 records the resulting radius-1 commutativity package
-/
structure Section7LocalityTarget where
  tube : Section7TubeForcingTarget
  CommutativeOnTube : tube.Patch → tube.Tube → Prop
  lemma_7_9 :
    ∀ {P : tube.Patch} {T : tube.Tube},
      tube.TubeForced P T →
      CommutativeOnTube P T
  lemma_7_10 :
    ∀ {P : tube.Patch},
      tube.ThreeCellPatch P →
      ∃ T : tube.Tube, CommutativeOnTube P T

/-- The extracted locality predicate from Ben's Section 7 finish. -/
def Section7LocalityTarget.RadiusOneLocality
    (S : Section7LocalityTarget) : Prop :=
  ∀ {P : S.tube.Patch},
    S.tube.ThreeCellPatch P →
    ∃ T : S.tube.Tube, S.CommutativeOnTube P T

theorem Section7LocalityTarget.radius_one_locality
    (S : Section7LocalityTarget) :
    S.RadiusOneLocality := by
  intro P hpatch
  exact S.lemma_7_10 hpatch

/-- Package the locality finish back into the existing abstract Section 7 target. -/
def Section7LocalityTarget.toSection7Target
    (S : Section7LocalityTarget) :
    Section7Target where
  Patch := S.tube.Patch
  Tube := S.tube.Tube
  ThreeCellPatch := S.tube.ThreeCellPatch
  RadiusOneTube := S.tube.RadiusOneTube
  TubeForced := S.tube.TubeForced
  CommutativeOnTube := S.CommutativeOnTube
  sublemma_7_7 := S.tube.sublemma_7_7
  lemma_7_8 := S.tube.lemma_7_8
  lemma_7_9 := S.lemma_7_9
  lemma_7_10 := S.lemma_7_10

/-- Three-cell patches commute in the extracted Section 7 locality package. -/
theorem Section7LocalityTarget.three_cell_patch_commutes
    (S : Section7LocalityTarget) :
    ∀ {P : S.tube.Patch},
      S.tube.ThreeCellPatch P →
      ∃ T : S.tube.Tube, S.CommutativeOnTube P T := by
  intro P hpatch
  exact S.lemma_7_10 hpatch

end FourColor.GoertzelV23
