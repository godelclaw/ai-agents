namespace FourColor.GoertzelV23

universe u v

/--
Ben's seam-interface preservation branch inside the final Step 4 closure.

After a lifted collar word is boundary-safe, the next live question is whether
the seam interface pairing inherited from the cut-open execution survives
lift-back. We isolate that as:
- boundary safety forces transparency across the cut-open seam;
- seam transparency preserves the seam interface pairing.
-/
structure Section8SeamInterfacePreservationTarget where
  Collar : Type u
  LiftedWord : Type v
  RadiusOneCollar : Collar → Prop
  LiftedBackTo : Collar → LiftedWord → Prop
  BoundarySafe : LiftedWord → Prop
  SeamTransparent : Collar → LiftedWord → Prop
  PreservesSeamInterfacePairing : Collar → LiftedWord → Prop
  boundary_safe_lift_is_seam_transparent :
    ∀ {A : Collar} {w : LiftedWord},
      RadiusOneCollar A →
      LiftedBackTo A w →
      BoundarySafe w →
      SeamTransparent A w
  seam_transparent_lift_preserves_seam_interface_pairing :
    ∀ {A : Collar} {w : LiftedWord},
      RadiusOneCollar A →
      LiftedBackTo A w →
      SeamTransparent A w →
      PreservesSeamInterfacePairing A w

/--
The extracted seam-interface theorem: a boundary-safe lifted collar word
preserves the seam interface pairing needed in the later Step 4 arguments.
-/
theorem
    Section8SeamInterfacePreservationTarget.boundary_safe_lift_preserves_seam_interface_pairing
    (S : Section8SeamInterfacePreservationTarget) :
    ∀ {A : S.Collar} {w : S.LiftedWord},
      S.RadiusOneCollar A →
      S.LiftedBackTo A w →
      S.BoundarySafe w →
      S.PreservesSeamInterfacePairing A w := by
  intro A w hcollar hlift hsafe
  exact
    S.seam_transparent_lift_preserves_seam_interface_pairing
      hcollar
      hlift
      (S.boundary_safe_lift_is_seam_transparent hcollar hlift hsafe)

end FourColor.GoertzelV23
