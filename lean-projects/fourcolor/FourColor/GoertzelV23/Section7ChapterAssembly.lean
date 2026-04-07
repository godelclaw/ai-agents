import FourColor.GoertzelV23.Section7BoundedInteractionTarget
import FourColor.GoertzelV23.Section7GateReductionTarget
import FourColor.GoertzelV23.Section7LocalityTarget

namespace FourColor.GoertzelV23

universe u v w z

/--
Unified theorem-back package for Ben Goertzel's Section 7.

This chapter-level assembly follows Ben's actual proof spine:
- bounded interaction and the zig-zag collar boundary
- minimal gate reduction to a three-cell patch
- tube forcing on that patch
- cap-aware locality / commutativity on the resulting tube

The remaining explicit gap after this assembly is the short-gate bridge: how
minimal gates below the long-gate threshold are converted back into the same
radius-1 commutativity output.
-/
structure Section7ChapterData where
  Face : Type u
  Boundary : Type v
  Patch : Type w
  Tube : Type z
  BoundedInteraction : Face → Prop
  ZigZagBoundary : Face → Boundary → Prop
  LongGate : Boundary → Prop
  GatePatch : Face → Boundary → Patch → Prop
  EscapingAnchoredCycle : Face → Prop
  MinimalGate : Face → Boundary → Prop
  ThreeCellPatch : Patch → Prop
  RadiusOneTube : Patch → Tube → Prop
  TubeForced : Patch → Tube → Prop
  CommutativeOnTube : Patch → Tube → Prop
  lemma_7_3 :
    ∀ f : Face, BoundedInteraction f
  lemma_7_5 :
    ∀ {f : Face},
      BoundedInteraction f →
      ∃ Γ : Boundary, ZigZagBoundary f Γ
  long_gate_contains_patch :
    ∀ {f : Face} {Γ : Boundary},
      ZigZagBoundary f Γ →
      LongGate Γ →
      ∃ P : Patch, ThreeCellPatch P ∧ GatePatch f Γ P
  minimal_gate_exists :
    ∀ {f : Face},
      EscapingAnchoredCycle f →
      ∃ Γ : Boundary, MinimalGate f Γ
  lemma_7_6 :
    ∀ {f : Face} {Γ : Boundary},
      EscapingAnchoredCycle f →
      MinimalGate f Γ →
      LongGate Γ →
      ∃ P : Patch, ThreeCellPatch P ∧ GatePatch f Γ P
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

/-- Extract the bounded-interaction / zig-zag boundary package. -/
def Section7ChapterData.toBoundedInteractionTarget
    (S : Section7ChapterData) :
    Section7BoundedInteractionTarget where
  Face := S.Face
  Boundary := S.Boundary
  Patch := S.Patch
  BoundedInteraction := S.BoundedInteraction
  ZigZagBoundary := S.ZigZagBoundary
  LongGate := S.LongGate
  ThreeCellPatch := S.ThreeCellPatch
  GatePatch := S.GatePatch
  lemma_7_3 := S.lemma_7_3
  lemma_7_5 := S.lemma_7_5
  long_gate_contains_patch := S.long_gate_contains_patch

/-- Extract the minimal-gate reduction package. -/
def Section7ChapterData.toGateReductionTarget
    (S : Section7ChapterData) :
    Section7GateReductionTarget where
  interaction := S.toBoundedInteractionTarget
  EscapingAnchoredCycle := S.EscapingAnchoredCycle
  MinimalGate := S.MinimalGate
  lemma_7_6 := S.lemma_7_6

/-- Extract the tube-forcing package. -/
def Section7ChapterData.toTubeForcingTarget
    (S : Section7ChapterData) :
    Section7TubeForcingTarget where
  Patch := S.Patch
  Tube := S.Tube
  ThreeCellPatch := S.ThreeCellPatch
  RadiusOneTube := S.RadiusOneTube
  TubeForced := S.TubeForced
  sublemma_7_7 := S.sublemma_7_7
  lemma_7_8 := S.lemma_7_8

/-- Extract the locality / commutativity finish. -/
def Section7ChapterData.toLocalityTarget
    (S : Section7ChapterData) :
    Section7LocalityTarget where
  tube := S.toTubeForcingTarget
  CommutativeOnTube := S.CommutativeOnTube
  lemma_7_9 := S.lemma_7_9
  lemma_7_10 := S.lemma_7_10

/-- Extract the existing abstract Section 7 target. -/
def Section7ChapterData.toSection7Target
    (S : Section7ChapterData) :
    Section7Target :=
  (S.toLocalityTarget).toSection7Target

/--
Long minimal gates already feed the commuting-tube conclusion through the
three-cell patch route.
-/
theorem Section7ChapterData.long_gate_commutative_tube
    (S : Section7ChapterData) :
    ∀ {f : S.Face} {Γ : S.Boundary},
      S.EscapingAnchoredCycle f →
      S.MinimalGate f Γ →
      S.LongGate Γ →
      ∃ P : S.Patch, ∃ T : S.Tube,
        S.ThreeCellPatch P ∧ S.GatePatch f Γ P ∧ S.CommutativeOnTube P T := by
  intro f Γ hescape hminimal hlong
  rcases S.lemma_7_6 hescape hminimal hlong with ⟨P, hpatch, hgate⟩
  rcases (S.toLocalityTarget).three_cell_patch_commutes hpatch with ⟨T, hcomm⟩
  exact ⟨P, T, hpatch, hgate, hcomm⟩

/-- The chapter still derives the existing abstract Section 7 locality package. -/
theorem Section7ChapterData.radius_one_locality
    (S : Section7ChapterData) :
    (S.toSection7Target).RadiusOneLocality := by
  exact (S.toSection7Target).radius_one_locality

/--
The explicit remaining chapter-level gap after the current assembly: handling
minimal gates that are already short enough that the long-gate reduction does
not apply directly.
-/
def Section7ChapterData.RemainingGap (S : Section7ChapterData) : Prop :=
  ∀ {f : S.Face} {Γ : S.Boundary},
    S.EscapingAnchoredCycle f →
    S.MinimalGate f Γ →
    ¬ S.LongGate Γ →
    ∃ P : S.Patch, ∃ T : S.Tube,
      S.ThreeCellPatch P ∧ S.CommutativeOnTube P T

/--
If the short-gate bridge closes, every escaping anchored cycle yields a
three-cell patch carrying the same local commutativity output.
-/
theorem Section7ChapterData.escaping_cycle_commutative_tube
    (S : Section7ChapterData)
    (hgap : S.RemainingGap) :
    ∀ {f : S.Face},
      S.EscapingAnchoredCycle f →
      ∃ P : S.Patch, ∃ T : S.Tube,
        S.ThreeCellPatch P ∧ S.CommutativeOnTube P T := by
  intro f hescape
  rcases S.minimal_gate_exists hescape with ⟨Γ, hminimal⟩
  by_cases hlong : S.LongGate Γ
  · rcases S.long_gate_commutative_tube hescape hminimal hlong with
      ⟨P, T, hpatch, _, hcomm⟩
    exact ⟨P, T, hpatch, hcomm⟩
  · exact hgap hescape hminimal hlong

end FourColor.GoertzelV23
