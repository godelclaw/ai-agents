namespace FourColor.GoertzelV23

universe u v

/--
Ben's collar-match branch inside the final Step 4 closure.

After a lifted collar word is boundary-safe, the proof still needs to show that
it agrees with the intended correction on the collar itself. In Ben's route
this can be split into:
- boundary safety keeps the lifted word aligned with the cut-open transfer data
  carried by the local gadget execution;
- that cut-open transfer data is exactly the target collar data.
-/
structure Section8CollarMatchTarget where
  Collar : Type u
  LiftedWord : Type v
  RadiusOneCollar : Collar → Prop
  LiftedBackTo : Collar → LiftedWord → Prop
  BoundarySafe : LiftedWord → Prop
  MatchesCutOpenTransfer : Collar → LiftedWord → Prop
  MatchesTargetOnCollar : Collar → LiftedWord → Prop
  boundary_safe_lift_matches_cut_open_transfer :
    ∀ {A : Collar} {w : LiftedWord},
      RadiusOneCollar A →
      LiftedBackTo A w →
      BoundarySafe w →
      MatchesCutOpenTransfer A w
  cut_open_transfer_matches_target_on_collar :
    ∀ {A : Collar} {w : LiftedWord},
      RadiusOneCollar A →
      LiftedBackTo A w →
      MatchesCutOpenTransfer A w →
      MatchesTargetOnCollar A w

/--
The extracted collar-match theorem: a boundary-safe lifted collar word matches
the target correction on the whole collar.
-/
theorem Section8CollarMatchTarget.boundary_safe_lift_matches_target_on_collar
    (S : Section8CollarMatchTarget) :
    ∀ {A : S.Collar} {w : S.LiftedWord},
      S.RadiusOneCollar A →
      S.LiftedBackTo A w →
      S.BoundarySafe w →
      S.MatchesTargetOnCollar A w := by
  intro A w hcollar hlift hsafe
  exact
    S.cut_open_transfer_matches_target_on_collar
      hcollar
      hlift
      (S.boundary_safe_lift_matches_cut_open_transfer hcollar hlift hsafe)

end FourColor.GoertzelV23
