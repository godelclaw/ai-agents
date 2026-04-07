namespace FourColor.GoertzelV23

universe u v w

/--
Ben's no-seam-crossing branch inside the final Step 4 closure.

After a lifted collar word is boundary-safe, the next live question is whether
any switched component can still touch the cut-open seam. We isolate that as:
- boundary safety forces every switched component to avoid the cut-open seam;
- if every switched component avoids the seam, then the lifted word has no
  cut-open seam crossing.
-/
structure Section8NoCutOpenSeamCrossingTarget where
  Collar : Type u
  LiftedWord : Type v
  Component : Type w
  RadiusOneCollar : Collar → Prop
  LiftedBackTo : Collar → LiftedWord → Prop
  BoundarySafe : LiftedWord → Prop
  UsesComponent : LiftedWord → Component → Prop
  TouchesCutOpenSeam : Collar → Component → Prop
  NoCutOpenSeamCrossing : Collar → LiftedWord → Prop
  boundary_safe_components_avoid_cut_open_seam :
    ∀ {A : Collar} {w : LiftedWord},
      RadiusOneCollar A →
      LiftedBackTo A w →
      BoundarySafe w →
      ∀ K : Component, UsesComponent w K → ¬ TouchesCutOpenSeam A K
  components_avoiding_cut_open_seam_forbid_crossing :
    ∀ {A : Collar} {w : LiftedWord},
      RadiusOneCollar A →
      LiftedBackTo A w →
      (∀ K : Component, UsesComponent w K → ¬ TouchesCutOpenSeam A K) →
      NoCutOpenSeamCrossing A w

/--
The extracted no-seam-crossing theorem: a boundary-safe lifted collar word has
no cut-open seam crossing.
-/
theorem
    Section8NoCutOpenSeamCrossingTarget.boundary_safe_lift_has_no_cut_open_seam_crossing
    (S : Section8NoCutOpenSeamCrossingTarget) :
    ∀ {A : S.Collar} {w : S.LiftedWord},
      S.RadiusOneCollar A →
      S.LiftedBackTo A w →
      S.BoundarySafe w →
      S.NoCutOpenSeamCrossing A w := by
  intro A w hcollar hlift hsafe
  exact
    S.components_avoiding_cut_open_seam_forbid_crossing
      hcollar
      hlift
      (S.boundary_safe_components_avoid_cut_open_seam hcollar hlift hsafe)

end FourColor.GoertzelV23
