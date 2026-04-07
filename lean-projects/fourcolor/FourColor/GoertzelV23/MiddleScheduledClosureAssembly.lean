import FourColor.GoertzelV23.MiddleChapterAssembly
import FourColor.GoertzelV23.Section8BoundarySafeLiftTarget
import FourColor.GoertzelV23.Section8BoundarySafetyTarget
import FourColor.GoertzelV23.Section8CollarMatchTarget
import FourColor.GoertzelV23.Section8CollarClosureTarget
import FourColor.GoertzelV23.Section8NoCutOpenSeamCrossingTarget
import FourColor.GoertzelV23.Section8SeamInterfacePreservationTarget
import FourColor.GoertzelV23.Section8SeamTouchAvoidanceTarget
import FourColor.GoertzelV23.Section8CutOpenSeamPreservationTarget
import FourColor.GoertzelV23.Section8CutOpenTransferTarget
import FourColor.GoertzelV23.Section8CutOpenReachabilityAssembly
import FourColor.GoertzelV23.Section8FixedBoundaryPreservationTarget
import FourColor.GoertzelV23.Section8LiftBackTarget
import FourColor.GoertzelV23.Section8RealizedCorrectionTarget
import FourColor.GoertzelV23.Section9ScheduledClosureTarget

namespace FourColor.GoertzelV23

universe u

/--
Sharper middle-layer package for the hardest live Ben-route mouth.

This replaces the old over-strong demand

  every collar is reachable

with the schedule-restricted demand Ben's Section 9 actually needs:

  every collar that appears in the peeled schedule is reachable.

It also threads in the already discharged first half of the Section 8 bridge,
and sharpens the second half into Ben's actual Step 4 substeps on scheduled
radius-1 collars:
- lift the cut-open collar word back into the ambient annulus;
- prove that the lifted ambient word avoids the already-fixed outer boundary;
- conclude from that boundary-safe lifted word that the collar itself is
  reachable.
-/
structure MiddleScheduledClosureData
    (Trail : Type u)
    (LocalReachable : Trail → Prop) where
  section4 : Section4ChapterData
  section6 : Section6ChapterData
  section7 : Section7ChapterData
  section8 : Section8ChapterData
  section9 : Section9ScheduledClosureTarget section4.Annulus section8.Collar
  trailAnnulus : Trail → section4.Annulus
  section9_annular_spanning :
    ∀ {A : section4.Annulus},
      (section4.toConcreteTarget.toSection4Target).AnnularSpanning A →
      section9.base.AnnularSpanning A
  section9_cap5_free :
    section6.toSection6Target.Cap5FreeNormalForm →
    section9.base.Cap5FreeNormalForm
  section9_radius_one_locality :
    (section7.toSection7Target).RadiusOneLocality →
    section9.base.RadiusOneLocality
  LiftedWord : Type
  Step4Component : Type
  LiftedBackTo : section8.Collar → LiftedWord → Prop
  BoundarySafe : LiftedWord → Prop
  NoFixedBoundaryTouch : section8.Collar → LiftedWord → Prop
  PreservesFixedBoundary : section8.Collar → LiftedWord → Prop
  SeamTransparent : section8.Collar → LiftedWord → Prop
  PreservesSeamInterfacePairing : section8.Collar → LiftedWord → Prop
  NoCutOpenSeamCrossing : section8.Collar → LiftedWord → Prop
  PreservesCutOpenSeam : section8.Collar → LiftedWord → Prop
  MatchesCutOpenTransfer : section8.Collar → LiftedWord → Prop
  RealizesTargetCorrection : section8.Collar → LiftedWord → Prop
  MatchesTargetOnCollar : section8.Collar → LiftedWord → Prop
  AdvancesInnerBoundary : section8.Collar → LiftedWord → Prop
  UsesStep4Component : LiftedWord → Step4Component → Prop
  AvoidsInputStubs : LiftedWord → Prop
  TouchesFixedBoundary : section8.Collar → Step4Component → Prop
  TouchesCutOpenSeam : section8.Collar → Step4Component → Prop
  AnchoredAtFixedBoundary : section8.Collar → Step4Component → Prop
  ConfinedToCollar : section8.Collar → Step4Component → Prop
  MeetsInputStub : section8.Collar → Step4Component → Prop
  scheduled_section8_radius_one :
    ∀ {A : section4.Annulus} {C : section8.Collar},
      C ∈ section9.base.collarSchedule A →
      section8.RadiusOneCollar C
  scheduled_cut_open_lifts_back :
    ∀ {A : section4.Annulus} {C : section8.Collar} {G : section8.Gadget},
      C ∈ section9.base.collarSchedule A →
      section8.RadiusOneCollar C →
      section8.CutOpenTo C G →
      section8.CutOpenReachable G →
      ∃ w : LiftedWord, LiftedBackTo C w
  scheduled_lifted_word_boundary_safe :
    ∀ {A : section4.Annulus} {C : section8.Collar} {w : LiftedWord},
      C ∈ section9.base.collarSchedule A →
      section8.RadiusOneCollar C →
      LiftedBackTo C w →
      AvoidsInputStubs w
  scheduled_boundary_touch_is_anchored :
    ∀ {A : section4.Annulus} {C : section8.Collar} {K : Step4Component},
      C ∈ section9.base.collarSchedule A →
      section8.RadiusOneCollar C →
      TouchesFixedBoundary C K →
      AnchoredAtFixedBoundary C K
  scheduled_anchored_component_confined :
    ∀ {A : section4.Annulus} {C : section8.Collar} {K : Step4Component},
      C ∈ section9.base.collarSchedule A →
      section8.RadiusOneCollar C →
      AnchoredAtFixedBoundary C K →
      ConfinedToCollar C K
  scheduled_confined_component_meets_input_stub :
    ∀ {A : section4.Annulus} {C : section8.Collar} {K : Step4Component},
      C ∈ section9.base.collarSchedule A →
      section8.RadiusOneCollar C →
      ConfinedToCollar C K →
      MeetsInputStub C K
  scheduled_input_stub_avoidance_forbids_component :
    ∀ {A : section4.Annulus} {C : section8.Collar} {w : LiftedWord} {K : Step4Component},
      C ∈ section9.base.collarSchedule A →
      AvoidsInputStubs w →
      UsesStep4Component w K →
      ¬ MeetsInputStub C K
  scheduled_boundary_safe_of_components_avoid_fixed_boundary :
    ∀ {A : section4.Annulus} {C : section8.Collar} {w : LiftedWord},
      C ∈ section9.base.collarSchedule A →
      section8.RadiusOneCollar C →
      LiftedBackTo C w →
      (∀ K : Step4Component, UsesStep4Component w K → ¬ TouchesFixedBoundary C K) →
      BoundarySafe w
  scheduled_boundary_safe_preserves_fixed_boundary :
    ∀ {A : section4.Annulus} {C : section8.Collar} {w : LiftedWord},
      C ∈ section9.base.collarSchedule A →
      section8.RadiusOneCollar C →
      LiftedBackTo C w →
      BoundarySafe w →
      NoFixedBoundaryTouch C w
  scheduled_no_fixed_boundary_touch_preserves_boundary :
    ∀ {A : section4.Annulus} {C : section8.Collar} {w : LiftedWord},
      C ∈ section9.base.collarSchedule A →
      section8.RadiusOneCollar C →
      LiftedBackTo C w →
      NoFixedBoundaryTouch C w →
      PreservesFixedBoundary C w
  scheduled_boundary_safe_is_seam_transparent :
    ∀ {A : section4.Annulus} {C : section8.Collar} {w : LiftedWord},
      C ∈ section9.base.collarSchedule A →
      section8.RadiusOneCollar C →
      LiftedBackTo C w →
      BoundarySafe w →
      SeamTransparent C w
  scheduled_seam_transparent_preserves_seam_interface_pairing :
    ∀ {A : section4.Annulus} {C : section8.Collar} {w : LiftedWord},
      C ∈ section9.base.collarSchedule A →
      section8.RadiusOneCollar C →
      LiftedBackTo C w →
      SeamTransparent C w →
      PreservesSeamInterfacePairing C w
  scheduled_preserved_seam_interface_pairing_forbids_seam_touch :
    ∀ {A : section4.Annulus} {C : section8.Collar} {w : LiftedWord},
      C ∈ section9.base.collarSchedule A →
      section8.RadiusOneCollar C →
      LiftedBackTo C w →
      PreservesSeamInterfacePairing C w →
      ∀ K : Step4Component, UsesStep4Component w K → ¬ TouchesCutOpenSeam C K
  scheduled_components_avoiding_cut_open_seam_forbid_crossing :
    ∀ {A : section4.Annulus} {C : section8.Collar} {w : LiftedWord},
      C ∈ section9.base.collarSchedule A →
      section8.RadiusOneCollar C →
      LiftedBackTo C w →
      (∀ K : Step4Component, UsesStep4Component w K → ¬ TouchesCutOpenSeam C K) →
      NoCutOpenSeamCrossing C w
  scheduled_no_cut_open_seam_crossing_preserves_cut_open_seam :
    ∀ {A : section4.Annulus} {C : section8.Collar} {w : LiftedWord},
      C ∈ section9.base.collarSchedule A →
      section8.RadiusOneCollar C →
      LiftedBackTo C w →
      NoCutOpenSeamCrossing C w →
      PreservesCutOpenSeam C w
  scheduled_cut_open_seam_preservation_matches_transfer :
    ∀ {A : section4.Annulus} {C : section8.Collar} {w : LiftedWord},
      C ∈ section9.base.collarSchedule A →
      section8.RadiusOneCollar C →
      LiftedBackTo C w →
      PreservesCutOpenSeam C w →
      MatchesCutOpenTransfer C w
  scheduled_cut_open_transfer_matches_target_on_collar :
    ∀ {A : section4.Annulus} {C : section8.Collar} {w : LiftedWord},
      C ∈ section9.base.collarSchedule A →
      section8.RadiusOneCollar C →
      LiftedBackTo C w →
      MatchesCutOpenTransfer C w →
      MatchesTargetOnCollar C w
  scheduled_collar_match_advances_inner_boundary :
    ∀ {A : section4.Annulus} {C : section8.Collar} {w : LiftedWord},
      C ∈ section9.base.collarSchedule A →
      section8.RadiusOneCollar C →
      MatchesTargetOnCollar C w →
      AdvancesInnerBoundary C w
  scheduled_collar_match_and_inner_boundary_realize_correction :
    ∀ {A : section4.Annulus} {C : section8.Collar} {w : LiftedWord},
      C ∈ section9.base.collarSchedule A →
      section8.RadiusOneCollar C →
      MatchesTargetOnCollar C w →
      AdvancesInnerBoundary C w →
      RealizesTargetCorrection C w
  scheduled_preservation_and_correction_close_collar :
    ∀ {A : section4.Annulus} {C : section8.Collar} {w : LiftedWord},
      C ∈ section9.base.collarSchedule A →
      section8.RadiusOneCollar C →
      PreservesFixedBoundary C w →
      RealizesTargetCorrection C w →
      section9.base.CollarReachable C
  annulus_reachability_implies_local :
    (∀ A : section4.Annulus, section9.base.AnnulusReachable A) →
    ∀ T : Trail, LocalReachable T

/--
For a fixed annulus stage, the Step 4 boundary-safety contradiction can be
packaged as a standalone target over the subtype of collars that actually occur
in that schedule.
-/
def MiddleScheduledClosureData.toBoundarySafetyTarget
    {Trail : Type u}
    {LocalReachable : Trail → Prop}
    (M : MiddleScheduledClosureData Trail LocalReachable)
    (A : M.section4.Annulus) :
    Section8BoundarySafetyTarget where
  Collar := {C : M.section8.Collar // C ∈ M.section9.base.collarSchedule A}
  LiftedWord := M.LiftedWord
  Component := M.Step4Component
  RadiusOneCollar := fun C => M.section8.RadiusOneCollar C.1
  LiftedBackTo := fun C w => M.LiftedBackTo C.1 w
  BoundarySafe := M.BoundarySafe
  UsesComponent := M.UsesStep4Component
  AvoidsInputStubs := M.AvoidsInputStubs
  TouchesFixedBoundary := fun C K => M.TouchesFixedBoundary C.1 K
  AnchoredAtFixedBoundary := fun C K => M.AnchoredAtFixedBoundary C.1 K
  ConfinedToCollar := fun C K => M.ConfinedToCollar C.1 K
  MeetsInputStub := fun C K => M.MeetsInputStub C.1 K
  lifted_words_avoid_input_stubs := by
    intro C w hcollar hlift
    exact
      M.scheduled_lifted_word_boundary_safe
        (A := A) (C := C.1) (w := w) C.2 hcollar hlift
  touching_fixed_boundary_is_anchored := by
    intro C K hcollar htouch
    exact
      M.scheduled_boundary_touch_is_anchored
        (A := A) (C := C.1) (K := K) C.2 hcollar htouch
  anchored_component_confined := by
    intro C K hcollar hanch
    exact
      M.scheduled_anchored_component_confined
        (A := A) (C := C.1) (K := K) C.2 hcollar hanch
  confined_component_meets_input_stub := by
    intro C K hcollar hconf
    exact
      M.scheduled_confined_component_meets_input_stub
        (A := A) (C := C.1) (K := K) C.2 hcollar hconf
  avoids_input_stubs_forbids_component := by
    intro C w K havoid huse
    exact
      M.scheduled_input_stub_avoidance_forbids_component
        (A := A) (C := C.1) (w := w) (K := K) C.2 havoid huse
  boundary_safe_of_components_avoid_fixed_boundary := by
    intro C w hcollar hlift hno
    exact
      M.scheduled_boundary_safe_of_components_avoid_fixed_boundary
        (A := A) (C := C.1) (w := w) C.2 hcollar hlift hno

/-- The fixed-boundary preservation branch on the subtype of scheduled collars. -/
def MiddleScheduledClosureData.toFixedBoundaryPreservationTarget
    {Trail : Type u}
    {LocalReachable : Trail → Prop}
    (M : MiddleScheduledClosureData Trail LocalReachable)
    (A : M.section4.Annulus) :
    Section8FixedBoundaryPreservationTarget where
  Collar := {C : M.section8.Collar // C ∈ M.section9.base.collarSchedule A}
  LiftedWord := M.LiftedWord
  RadiusOneCollar := fun C => M.section8.RadiusOneCollar C.1
  LiftedBackTo := fun C w => M.LiftedBackTo C.1 w
  BoundarySafe := M.BoundarySafe
  NoFixedBoundaryTouch := fun C w => M.NoFixedBoundaryTouch C.1 w
  PreservesFixedBoundary := fun C w => M.PreservesFixedBoundary C.1 w
  boundary_safe_lift_has_no_fixed_boundary_touch := by
    intro C w hcollar hlift hsafe
    exact
      M.scheduled_boundary_safe_preserves_fixed_boundary
        (A := A) (C := C.1) (w := w) C.2 hcollar hlift hsafe
  no_fixed_boundary_touch_preserves_boundary := by
    intro C w hcollar hlift hno
    exact
      M.scheduled_no_fixed_boundary_touch_preserves_boundary
        (A := A) (C := C.1) (w := w) C.2 hcollar hlift hno

/-- The seam-interface preservation branch on the subtype of scheduled collars. -/
def MiddleScheduledClosureData.toSeamInterfacePreservationTarget
    {Trail : Type u}
    {LocalReachable : Trail → Prop}
    (M : MiddleScheduledClosureData Trail LocalReachable)
    (A : M.section4.Annulus) :
    Section8SeamInterfacePreservationTarget where
  Collar := {C : M.section8.Collar // C ∈ M.section9.base.collarSchedule A}
  LiftedWord := M.LiftedWord
  RadiusOneCollar := fun C => M.section8.RadiusOneCollar C.1
  LiftedBackTo := fun C w => M.LiftedBackTo C.1 w
  BoundarySafe := M.BoundarySafe
  SeamTransparent := fun C w => M.SeamTransparent C.1 w
  PreservesSeamInterfacePairing := fun C w => M.PreservesSeamInterfacePairing C.1 w
  boundary_safe_lift_is_seam_transparent := by
    intro C w hcollar hlift hsafe
    exact
      M.scheduled_boundary_safe_is_seam_transparent
        (A := A) (C := C.1) (w := w) C.2 hcollar hlift hsafe
  seam_transparent_lift_preserves_seam_interface_pairing := by
    intro C w hcollar hlift htrans
    exact
      M.scheduled_seam_transparent_preserves_seam_interface_pairing
        (A := A) (C := C.1) (w := w) C.2 hcollar hlift htrans

/-- The seam-touch avoidance branch on the subtype of scheduled collars. -/
def MiddleScheduledClosureData.toSeamTouchAvoidanceTarget
    {Trail : Type u}
    {LocalReachable : Trail → Prop}
    (M : MiddleScheduledClosureData Trail LocalReachable)
    (A : M.section4.Annulus) :
    Section8SeamTouchAvoidanceTarget where
  Collar := {C : M.section8.Collar // C ∈ M.section9.base.collarSchedule A}
  LiftedWord := M.LiftedWord
  Component := M.Step4Component
  RadiusOneCollar := fun C => M.section8.RadiusOneCollar C.1
  LiftedBackTo := fun C w => M.LiftedBackTo C.1 w
  BoundarySafe := M.BoundarySafe
  UsesComponent := M.UsesStep4Component
  PreservesSeamInterfacePairing := fun C w => M.PreservesSeamInterfacePairing C.1 w
  TouchesCutOpenSeam := fun C K => M.TouchesCutOpenSeam C.1 K
  boundary_safe_lift_preserves_seam_interface_pairing := by
    intro C w hcollar hlift hsafe
    let S := M.toSeamInterfacePreservationTarget A
    exact S.boundary_safe_lift_preserves_seam_interface_pairing (A := C) hcollar hlift hsafe
  preserved_seam_interface_pairing_forbids_seam_touch := by
    intro C w hcollar hlift hpair K huse
    exact
      M.scheduled_preserved_seam_interface_pairing_forbids_seam_touch
        (A := A) (C := C.1) (w := w) C.2 hcollar hlift hpair K huse

/-- The no-cut-open-seam-crossing branch on the subtype of scheduled collars. -/
def MiddleScheduledClosureData.toNoCutOpenSeamCrossingTarget
    {Trail : Type u}
    {LocalReachable : Trail → Prop}
    (M : MiddleScheduledClosureData Trail LocalReachable)
    (A : M.section4.Annulus) :
    Section8NoCutOpenSeamCrossingTarget where
  Collar := {C : M.section8.Collar // C ∈ M.section9.base.collarSchedule A}
  LiftedWord := M.LiftedWord
  Component := M.Step4Component
  RadiusOneCollar := fun C => M.section8.RadiusOneCollar C.1
  LiftedBackTo := fun C w => M.LiftedBackTo C.1 w
  BoundarySafe := M.BoundarySafe
  UsesComponent := M.UsesStep4Component
  TouchesCutOpenSeam := fun C K => M.TouchesCutOpenSeam C.1 K
  NoCutOpenSeamCrossing := fun C w => M.NoCutOpenSeamCrossing C.1 w
  boundary_safe_components_avoid_cut_open_seam := by
    intro C w hcollar hlift hsafe K huse
    let S := M.toSeamTouchAvoidanceTarget A
    exact S.boundary_safe_components_avoid_cut_open_seam (A := C) hcollar hlift hsafe K huse
  components_avoiding_cut_open_seam_forbid_crossing := by
    intro C w hcollar hlift hno
    exact
      M.scheduled_components_avoiding_cut_open_seam_forbid_crossing
        (A := A) (C := C.1) (w := w) C.2 hcollar hlift hno

/-- The cut-open seam preservation branch on the subtype of scheduled collars. -/
def MiddleScheduledClosureData.toCutOpenSeamPreservationTarget
    {Trail : Type u}
    {LocalReachable : Trail → Prop}
    (M : MiddleScheduledClosureData Trail LocalReachable)
    (A : M.section4.Annulus) :
    Section8CutOpenSeamPreservationTarget where
  Collar := {C : M.section8.Collar // C ∈ M.section9.base.collarSchedule A}
  LiftedWord := M.LiftedWord
  RadiusOneCollar := fun C => M.section8.RadiusOneCollar C.1
  LiftedBackTo := fun C w => M.LiftedBackTo C.1 w
  BoundarySafe := M.BoundarySafe
  NoCutOpenSeamCrossing := fun C w => M.NoCutOpenSeamCrossing C.1 w
  PreservesCutOpenSeam := fun C w => M.PreservesCutOpenSeam C.1 w
  boundary_safe_lift_has_no_cut_open_seam_crossing := by
    intro C w hcollar hlift hsafe
    let S := M.toNoCutOpenSeamCrossingTarget A
    exact S.boundary_safe_lift_has_no_cut_open_seam_crossing (A := C) hcollar hlift hsafe
  no_cut_open_seam_crossing_preserves_cut_open_seam := by
    intro C w hcollar hlift hno
    exact
      M.scheduled_no_cut_open_seam_crossing_preserves_cut_open_seam
        (A := A) (C := C.1) (w := w) C.2 hcollar hlift hno

/-- The cut-open transfer branch on the subtype of scheduled collars. -/
def MiddleScheduledClosureData.toCutOpenTransferTarget
    {Trail : Type u}
    {LocalReachable : Trail → Prop}
    (M : MiddleScheduledClosureData Trail LocalReachable)
    (A : M.section4.Annulus) :
    Section8CutOpenTransferTarget where
  Collar := {C : M.section8.Collar // C ∈ M.section9.base.collarSchedule A}
  LiftedWord := M.LiftedWord
  RadiusOneCollar := fun C => M.section8.RadiusOneCollar C.1
  LiftedBackTo := fun C w => M.LiftedBackTo C.1 w
  BoundarySafe := M.BoundarySafe
  PreservesCutOpenSeam := fun C w => M.PreservesCutOpenSeam C.1 w
  MatchesCutOpenTransfer := fun C w => M.MatchesCutOpenTransfer C.1 w
  boundary_safe_lift_preserves_cut_open_seam := by
    intro C w hcollar hlift hsafe
    let S := M.toCutOpenSeamPreservationTarget A
    exact S.boundary_safe_lift_preserves_cut_open_seam (A := C) hcollar hlift hsafe
  cut_open_seam_preservation_matches_transfer := by
    intro C w hcollar hlift hseam
    exact
      M.scheduled_cut_open_seam_preservation_matches_transfer
        (A := A) (C := C.1) (w := w) C.2 hcollar hlift hseam

/-- The collar-match branch on the subtype of scheduled collars. -/
def MiddleScheduledClosureData.toCollarMatchTarget
    {Trail : Type u}
    {LocalReachable : Trail → Prop}
    (M : MiddleScheduledClosureData Trail LocalReachable)
    (A : M.section4.Annulus) :
    Section8CollarMatchTarget where
  Collar := {C : M.section8.Collar // C ∈ M.section9.base.collarSchedule A}
  LiftedWord := M.LiftedWord
  RadiusOneCollar := fun C => M.section8.RadiusOneCollar C.1
  LiftedBackTo := fun C w => M.LiftedBackTo C.1 w
  BoundarySafe := M.BoundarySafe
  MatchesCutOpenTransfer := fun C w => M.MatchesCutOpenTransfer C.1 w
  MatchesTargetOnCollar := fun C w => M.MatchesTargetOnCollar C.1 w
  boundary_safe_lift_matches_cut_open_transfer := by
    intro C w hcollar hlift hsafe
    let S := M.toCutOpenTransferTarget A
    exact S.boundary_safe_lift_matches_cut_open_transfer (A := C) hcollar hlift hsafe
  cut_open_transfer_matches_target_on_collar := by
    intro C w hcollar hlift htransfer
    exact
      M.scheduled_cut_open_transfer_matches_target_on_collar
        (A := A) (C := C.1) (w := w) C.2 hcollar hlift htransfer

/-- The realized-correction branch on the subtype of scheduled collars. -/
def MiddleScheduledClosureData.toRealizedCorrectionTarget
    {Trail : Type u}
    {LocalReachable : Trail → Prop}
    (M : MiddleScheduledClosureData Trail LocalReachable)
    (A : M.section4.Annulus) :
    Section8RealizedCorrectionTarget where
  Collar := {C : M.section8.Collar // C ∈ M.section9.base.collarSchedule A}
  LiftedWord := M.LiftedWord
  RadiusOneCollar := fun C => M.section8.RadiusOneCollar C.1
  LiftedBackTo := fun C w => M.LiftedBackTo C.1 w
  BoundarySafe := M.BoundarySafe
  MatchesTargetOnCollar := fun C w => M.MatchesTargetOnCollar C.1 w
  AdvancesInnerBoundary := fun C w => M.AdvancesInnerBoundary C.1 w
  RealizesTargetCorrection := fun C w => M.RealizesTargetCorrection C.1 w
  boundary_safe_lift_matches_target_on_collar := by
    intro C w hcollar hlift hsafe
    let S := M.toCollarMatchTarget A
    exact S.boundary_safe_lift_matches_target_on_collar (A := C) hcollar hlift hsafe
  collar_match_advances_inner_boundary := by
    intro C w hcollar hmatch
    exact
      M.scheduled_collar_match_advances_inner_boundary
        (A := A) (C := C.1) (w := w) C.2 hcollar hmatch
  collar_match_and_inner_boundary_realize_correction := by
    intro C w hcollar hmatch hadv
    exact
      M.scheduled_collar_match_and_inner_boundary_realize_correction
        (A := A) (C := C.1) (w := w) C.2 hcollar hmatch hadv

/--
For a fixed annulus stage, the final Step 4 closure can also be packaged as a
standalone target over the scheduled collar subtype.
-/
def MiddleScheduledClosureData.toCollarClosureTarget
    {Trail : Type u}
    {LocalReachable : Trail → Prop}
    (M : MiddleScheduledClosureData Trail LocalReachable)
    (A : M.section4.Annulus) :
    Section8CollarClosureTarget where
  Collar := {C : M.section8.Collar // C ∈ M.section9.base.collarSchedule A}
  LiftedWord := M.LiftedWord
  RadiusOneCollar := fun C => M.section8.RadiusOneCollar C.1
  LiftedBackTo := fun C w => M.LiftedBackTo C.1 w
  BoundarySafe := M.BoundarySafe
  PreservesFixedBoundary := fun C w => M.PreservesFixedBoundary C.1 w
  RealizesTargetCorrection := fun C w => M.RealizesTargetCorrection C.1 w
  CollarReachable := fun C => M.section9.base.CollarReachable C.1
  boundary_safe_lift_preserves_fixed_boundary := by
    intro C w hcollar hlift hsafe
    let S := M.toFixedBoundaryPreservationTarget A
    exact S.boundary_safe_lift_preserves_fixed_boundary (A := C) hcollar hlift hsafe
  boundary_safe_lift_realizes_target_correction := by
    intro C w hcollar hlift hsafe
    let S := M.toRealizedCorrectionTarget A
    exact S.boundary_safe_lift_realizes_target_correction (A := C) hcollar hlift hsafe
  preservation_and_correction_close_collar := by
    intro C w hcollar hpres hcorr
    exact
      M.scheduled_preservation_and_correction_close_collar
        (A := A) (C := C.1) (w := w) C.2 hcollar hpres hcorr

/--
On scheduled collars, Ben's first two Step 4 substeps compose directly:
cut-open reachability produces a lifted ambient word, and locality upgrades that
lifted word to a boundary-safe one.
-/
theorem MiddleScheduledClosureData.scheduled_cut_open_lifts_boundary_safely
    {Trail : Type u}
    {LocalReachable : Trail → Prop}
    (M : MiddleScheduledClosureData Trail LocalReachable) :
    ∀ {A : M.section4.Annulus} {C : M.section8.Collar} {G : M.section8.Gadget},
      C ∈ M.section9.base.collarSchedule A →
      M.section8.RadiusOneCollar C →
      M.section8.CutOpenTo C G →
      M.section8.CutOpenReachable G →
      ∃ w : M.LiftedWord, M.LiftedBackTo C w ∧ M.BoundarySafe w := by
  intro A C G hmem hcollar hcut hreach
  rcases M.scheduled_cut_open_lifts_back hmem hcollar hcut hreach with ⟨w, hlift⟩
  let S := M.toBoundarySafetyTarget A
  let C' : S.Collar := ⟨C, hmem⟩
  have hsafe : S.BoundarySafe w := by
    exact S.lifted_word_is_boundary_safe (A := C') hcollar hlift
  exact ⟨w, hlift, hsafe⟩

/-- Scheduled collars are reachable once the concrete second half of Section 8 closes. -/
theorem MiddleScheduledClosureData.scheduled_collars_reachable
    {Trail : Type u}
    {LocalReachable : Trail → Prop}
    (M : MiddleScheduledClosureData Trail LocalReachable) :
    M.section9.base.ScheduledCollarsReachable := by
  intro A C hmem
  have hradius : M.section8.RadiusOneCollar C :=
    M.scheduled_section8_radius_one hmem
  rcases M.section8.radius_one_collar_executes hradius with ⟨G, op, hcut, _, hexec⟩
  rcases
      M.scheduled_cut_open_lifts_boundary_safely
        hmem
        hradius
        hcut
        (M.section8.execution_implies_cut_open_reachability hexec)
    with ⟨w, hlift, hsafe⟩
  let S := M.toCollarClosureTarget A
  let C' : S.Collar := ⟨C, hmem⟩
  exact S.boundary_safe_lift_closes_collar (A := C') hradius hlift hsafe

/--
Chapter-level Section 9 closure on scheduled collars plus the chapter outputs
from Sections 4, 6, 7, and the concrete first half of Section 8 imply
trail-level local reachability.
-/
theorem MiddleScheduledClosureData.local_reachability_of_scheduled_closure
    {Trail : Type u}
    {LocalReachable : Trail → Prop}
    (M : MiddleScheduledClosureData Trail LocalReachable) :
    ∀ T : Trail, LocalReachable T := by
  have h4 :
      ∀ A : M.section4.Annulus, M.section9.base.AnnularSpanning A := by
    intro A
    exact
      M.section9_annular_spanning
        ((M.section4.toConcreteTarget.toSection4Target).allAnnuliSpan A)
  have h6 : M.section9.base.Cap5FreeNormalForm :=
    M.section9_cap5_free (M.section6.toSection6Target.cap5_free_normal_form)
  have h7 : M.section9.base.RadiusOneLocality :=
    M.section9_radius_one_locality ((M.section7.toSection7Target).radius_one_locality)
  have hAnn :
      ∀ A : M.section4.Annulus, M.section9.base.AnnulusReachable A := by
    intro A
    exact M.section9.annulus_reachable h4 h6 h7 M.scheduled_collars_reachable A
  exact M.annulus_reachability_implies_local hAnn

end FourColor.GoertzelV23
