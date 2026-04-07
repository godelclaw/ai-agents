namespace FourColor.GoertzelV23

universe u v w

/--
Ben's first Step 4 substep for a single radius-1 collar.

After Section 8 proves reachability for the cut-open collar gadget, Ben's proof
does not jump straight to collar reachability. It first interprets the cut-open
Kempe word back in the ambient annulus, and only then uses locality to show
that this lifted word avoids the already-fixed outer boundary.
-/
structure Section8LiftBackTarget where
  Collar : Type u
  Gadget : Type v
  LiftedWord : Type w
  RadiusOneCollar : Collar → Prop
  CutOpenTo : Collar → Gadget → Prop
  CutOpenReachable : Gadget → Prop
  LiftedBackTo : Collar → LiftedWord → Prop
  BoundarySafe : LiftedWord → Prop
  cut_open_reachability_lifts_back :
    ∀ {A : Collar} {G : Gadget},
      RadiusOneCollar A →
      CutOpenTo A G →
      CutOpenReachable G →
      ∃ w : LiftedWord, LiftedBackTo A w
  lifted_word_is_boundary_safe :
    ∀ {A : Collar} {w : LiftedWord},
      RadiusOneCollar A →
      LiftedBackTo A w →
      BoundarySafe w

/--
The extracted first Step 4 conclusion: every reachable cut-open collar gadget
produces a lifted ambient word which is already boundary-safe.
-/
theorem Section8LiftBackTarget.cut_open_reachability_lifts_boundary_safely
    (S : Section8LiftBackTarget) :
    ∀ {A : S.Collar} {G : S.Gadget},
      S.RadiusOneCollar A →
      S.CutOpenTo A G →
      S.CutOpenReachable G →
      ∃ w : S.LiftedWord, S.LiftedBackTo A w ∧ S.BoundarySafe w := by
  intro A G hcollar hcut hreach
  rcases S.cut_open_reachability_lifts_back hcollar hcut hreach with ⟨w, hlift⟩
  exact ⟨w, hlift, S.lifted_word_is_boundary_safe hcollar hlift⟩

end FourColor.GoertzelV23
