namespace FourColor.GoertzelV23

universe u v

/--
Ben's cut-open seam preservation branch inside the final Step 4 closure.

After a lifted collar word is boundary-safe, the proof still needs to show that
the cut-open seam data used by the local gadget execution survives lift-back
into the ambient annulus. We split that into:
- boundary safety prevents the lifted word from crossing the cut-open seam;
- if the lifted word never crosses that seam, then the seam data is preserved.
-/
structure Section8CutOpenSeamPreservationTarget where
  Collar : Type u
  LiftedWord : Type v
  RadiusOneCollar : Collar → Prop
  LiftedBackTo : Collar → LiftedWord → Prop
  BoundarySafe : LiftedWord → Prop
  NoCutOpenSeamCrossing : Collar → LiftedWord → Prop
  PreservesCutOpenSeam : Collar → LiftedWord → Prop
  boundary_safe_lift_has_no_cut_open_seam_crossing :
    ∀ {A : Collar} {w : LiftedWord},
      RadiusOneCollar A →
      LiftedBackTo A w →
      BoundarySafe w →
      NoCutOpenSeamCrossing A w
  no_cut_open_seam_crossing_preserves_cut_open_seam :
    ∀ {A : Collar} {w : LiftedWord},
      RadiusOneCollar A →
      LiftedBackTo A w →
      NoCutOpenSeamCrossing A w →
      PreservesCutOpenSeam A w

/--
The extracted seam-preservation theorem: a boundary-safe lifted collar word
preserves the cut-open seam data needed for the later transfer argument.
-/
theorem
    Section8CutOpenSeamPreservationTarget.boundary_safe_lift_preserves_cut_open_seam
    (S : Section8CutOpenSeamPreservationTarget) :
    ∀ {A : S.Collar} {w : S.LiftedWord},
      S.RadiusOneCollar A →
      S.LiftedBackTo A w →
      S.BoundarySafe w →
      S.PreservesCutOpenSeam A w := by
  intro A w hcollar hlift hsafe
  exact
    S.no_cut_open_seam_crossing_preserves_cut_open_seam
      hcollar
      hlift
      (S.boundary_safe_lift_has_no_cut_open_seam_crossing hcollar hlift hsafe)

end FourColor.GoertzelV23
