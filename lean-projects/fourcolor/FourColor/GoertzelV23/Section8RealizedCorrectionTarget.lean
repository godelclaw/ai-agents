namespace FourColor.GoertzelV23

universe u v

/--
Ben's realized-correction branch inside the final Step 4 closure.

After a lifted collar word is known to be boundary-safe, the proof still needs
to show that it actually performs the intended local correction. In Ben's
outside-in argument this is naturally split into:
- the resulting coloring matches the target on the whole collar;
- therefore, in particular, the inner boundary of that collar advances to the
  target boundary data;
- together these facts package the intended collar correction.
-/
structure Section8RealizedCorrectionTarget where
  Collar : Type u
  LiftedWord : Type v
  RadiusOneCollar : Collar → Prop
  LiftedBackTo : Collar → LiftedWord → Prop
  BoundarySafe : LiftedWord → Prop
  MatchesTargetOnCollar : Collar → LiftedWord → Prop
  AdvancesInnerBoundary : Collar → LiftedWord → Prop
  RealizesTargetCorrection : Collar → LiftedWord → Prop
  boundary_safe_lift_matches_target_on_collar :
    ∀ {A : Collar} {w : LiftedWord},
      RadiusOneCollar A →
      LiftedBackTo A w →
      BoundarySafe w →
      MatchesTargetOnCollar A w
  collar_match_advances_inner_boundary :
    ∀ {A : Collar} {w : LiftedWord},
      RadiusOneCollar A →
      MatchesTargetOnCollar A w →
      AdvancesInnerBoundary A w
  collar_match_and_inner_boundary_realize_correction :
    ∀ {A : Collar} {w : LiftedWord},
      RadiusOneCollar A →
      MatchesTargetOnCollar A w →
      AdvancesInnerBoundary A w →
      RealizesTargetCorrection A w

/-- A boundary-safe lifted collar word therefore realizes the intended correction. -/
theorem Section8RealizedCorrectionTarget.boundary_safe_lift_realizes_target_correction
    (S : Section8RealizedCorrectionTarget) :
    ∀ {A : S.Collar} {w : S.LiftedWord},
      S.RadiusOneCollar A →
      S.LiftedBackTo A w →
      S.BoundarySafe w →
      S.RealizesTargetCorrection A w := by
  intro A w hcollar hlift hsafe
  have hmatch : S.MatchesTargetOnCollar A w :=
    S.boundary_safe_lift_matches_target_on_collar hcollar hlift hsafe
  have hadv : S.AdvancesInnerBoundary A w :=
    S.collar_match_advances_inner_boundary hcollar hmatch
  exact
    S.collar_match_and_inner_boundary_realize_correction
      hcollar
      hmatch
      hadv

end FourColor.GoertzelV23
