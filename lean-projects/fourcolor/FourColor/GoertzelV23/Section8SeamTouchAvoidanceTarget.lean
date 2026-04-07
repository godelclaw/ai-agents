namespace FourColor.GoertzelV23

universe u v w

/--
Ben's seam-touch avoidance branch inside the final Step 4 closure.

After a lifted collar word is boundary-safe, the next live question is whether
any switched component can still touch the cut-open seam. We isolate that as:
- boundary safety preserves the seam interface pairing inherited from the
  cut-open execution;
- preserved seam interface pairing forbids any switched component from touching
  the cut-open seam.
-/
structure Section8SeamTouchAvoidanceTarget where
  Collar : Type u
  LiftedWord : Type v
  Component : Type w
  RadiusOneCollar : Collar → Prop
  LiftedBackTo : Collar → LiftedWord → Prop
  BoundarySafe : LiftedWord → Prop
  UsesComponent : LiftedWord → Component → Prop
  PreservesSeamInterfacePairing : Collar → LiftedWord → Prop
  TouchesCutOpenSeam : Collar → Component → Prop
  boundary_safe_lift_preserves_seam_interface_pairing :
    ∀ {A : Collar} {w : LiftedWord},
      RadiusOneCollar A →
      LiftedBackTo A w →
      BoundarySafe w →
      PreservesSeamInterfacePairing A w
  preserved_seam_interface_pairing_forbids_seam_touch :
    ∀ {A : Collar} {w : LiftedWord},
      RadiusOneCollar A →
      LiftedBackTo A w →
      PreservesSeamInterfacePairing A w →
      ∀ K : Component, UsesComponent w K → ¬ TouchesCutOpenSeam A K

/--
The extracted seam-touch avoidance theorem: a boundary-safe lifted collar word
has no seam-touching switched component.
-/
theorem Section8SeamTouchAvoidanceTarget.boundary_safe_components_avoid_cut_open_seam
    (S : Section8SeamTouchAvoidanceTarget) :
    ∀ {A : S.Collar} {w : S.LiftedWord},
      S.RadiusOneCollar A →
      S.LiftedBackTo A w →
      S.BoundarySafe w →
      ∀ K : S.Component, S.UsesComponent w K → ¬ S.TouchesCutOpenSeam A K := by
  intro A w hcollar hlift hsafe
  exact
    S.preserved_seam_interface_pairing_forbids_seam_touch
      hcollar
      hlift
      (S.boundary_safe_lift_preserves_seam_interface_pairing hcollar hlift hsafe)

end FourColor.GoertzelV23
