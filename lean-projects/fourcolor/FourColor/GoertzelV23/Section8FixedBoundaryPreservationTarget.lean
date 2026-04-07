namespace FourColor.GoertzelV23

universe u v

/--
Ben's fixed-boundary preservation branch inside the final Step 4 closure.

After a lifted collar word is known to be boundary-safe, the proof still uses
two distinct ideas to conclude that the already-fixed outer boundary remains
fixed:
- boundary safety means the lifted word never touches that fixed boundary;
- if no switched component touches the fixed boundary, then those boundary
  colors are preserved.
-/
structure Section8FixedBoundaryPreservationTarget where
  Collar : Type u
  LiftedWord : Type v
  RadiusOneCollar : Collar → Prop
  LiftedBackTo : Collar → LiftedWord → Prop
  BoundarySafe : LiftedWord → Prop
  NoFixedBoundaryTouch : Collar → LiftedWord → Prop
  PreservesFixedBoundary : Collar → LiftedWord → Prop
  boundary_safe_lift_has_no_fixed_boundary_touch :
    ∀ {A : Collar} {w : LiftedWord},
      RadiusOneCollar A →
      LiftedBackTo A w →
      BoundarySafe w →
      NoFixedBoundaryTouch A w
  no_fixed_boundary_touch_preserves_boundary :
    ∀ {A : Collar} {w : LiftedWord},
      RadiusOneCollar A →
      LiftedBackTo A w →
      NoFixedBoundaryTouch A w →
      PreservesFixedBoundary A w

/--
The extracted preservation theorem: a boundary-safe lifted collar word keeps
the fixed boundary fixed.
-/
theorem Section8FixedBoundaryPreservationTarget.boundary_safe_lift_preserves_fixed_boundary
    (S : Section8FixedBoundaryPreservationTarget) :
    ∀ {A : S.Collar} {w : S.LiftedWord},
      S.RadiusOneCollar A →
      S.LiftedBackTo A w →
      S.BoundarySafe w →
      S.PreservesFixedBoundary A w := by
  intro A w hcollar hlift hsafe
  exact
    S.no_fixed_boundary_touch_preserves_boundary
      hcollar
      hlift
      (S.boundary_safe_lift_has_no_fixed_boundary_touch hcollar hlift hsafe)

end FourColor.GoertzelV23
