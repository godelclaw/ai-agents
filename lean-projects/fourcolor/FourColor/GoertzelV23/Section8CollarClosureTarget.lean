namespace FourColor.GoertzelV23

universe u v

/--
Ben's final Step 4 substep for a single radius-1 collar.

Once a lifted collar word is known to be boundary-safe, the proof still needs
two separate conclusions:
- the already-fixed outer boundary stays fixed;
- the intended collar correction is still realized inside the ambient annulus.

Only after those two facts are available does the collar-level reachability
statement follow.
-/
structure Section8CollarClosureTarget where
  Collar : Type u
  LiftedWord : Type v
  RadiusOneCollar : Collar → Prop
  LiftedBackTo : Collar → LiftedWord → Prop
  BoundarySafe : LiftedWord → Prop
  PreservesFixedBoundary : Collar → LiftedWord → Prop
  RealizesTargetCorrection : Collar → LiftedWord → Prop
  CollarReachable : Collar → Prop
  boundary_safe_lift_preserves_fixed_boundary :
    ∀ {A : Collar} {w : LiftedWord},
      RadiusOneCollar A →
      LiftedBackTo A w →
      BoundarySafe w →
      PreservesFixedBoundary A w
  boundary_safe_lift_realizes_target_correction :
    ∀ {A : Collar} {w : LiftedWord},
      RadiusOneCollar A →
      LiftedBackTo A w →
      BoundarySafe w →
      RealizesTargetCorrection A w
  preservation_and_correction_close_collar :
    ∀ {A : Collar} {w : LiftedWord},
      RadiusOneCollar A →
      PreservesFixedBoundary A w →
      RealizesTargetCorrection A w →
      CollarReachable A

/--
The extracted closure theorem: a boundary-safe lifted collar word closes the
collar once preservation and correction are both available.
-/
theorem Section8CollarClosureTarget.boundary_safe_lift_closes_collar
    (S : Section8CollarClosureTarget) :
    ∀ {A : S.Collar} {w : S.LiftedWord},
      S.RadiusOneCollar A →
      S.LiftedBackTo A w →
      S.BoundarySafe w →
      S.CollarReachable A := by
  intro A w hcollar hlift hsafe
  exact
    S.preservation_and_correction_close_collar
      hcollar
      (S.boundary_safe_lift_preserves_fixed_boundary hcollar hlift hsafe)
      (S.boundary_safe_lift_realizes_target_correction hcollar hlift hsafe)

end FourColor.GoertzelV23
