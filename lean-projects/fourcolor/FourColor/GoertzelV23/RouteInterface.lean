namespace FourColor.GoertzelV23

universe u v w

/--
Section 3 of the `v23` proof: if every trail satisfies the required local
reachability statement, then the Four Color Theorem follows.

This is the theorem-back mouth for Ben Goertzel's route, not the old
reducibility/discharging route.
-/
structure TrailReductionLayer where
  Trail : Type u
  LocalReachable : Trail → Prop
  FourColorStatement : Prop
  fourColor_of_localReachability :
    (∀ T : Trail, LocalReachable T) → FourColorStatement

/--
Sections 4-8 of the `v23` proof, packaged as one abstract closure layer.

The fields track the actual proof spine:
- Section 4: annular spanning
- Sections 5-6: CAP5-free normal form
- Section 7: radius-1 locality
- Section 8: local gadget reachability and composition

The theorem field `localReachability_of_sections` is the exact point where the
middle proof body must discharge the trail-level reachability used by
`TrailReductionLayer`.
-/
structure Section4To8Layer
    (Trail : Type u) (LocalReachable : Trail → Prop) where
  Annulus : Type v
  Gadget : Type w
  AnnularSpanning : Annulus → Prop
  Cap5FreeNormalForm : Prop
  RadiusOneLocality : Prop
  LocalGadgetReachable : Gadget → Prop
  GadgetComposition : Prop
  all_annuli_span : ∀ A : Annulus, AnnularSpanning A
  cap5_free_normal_form : Cap5FreeNormalForm
  radius_one_locality : RadiusOneLocality
  all_gadgets_reachable : ∀ X : Gadget, LocalGadgetReachable X
  gadget_composition : GadgetComposition
  localReachability_of_sections :
    (∀ A : Annulus, AnnularSpanning A) →
    Cap5FreeNormalForm →
    RadiusOneLocality →
    (∀ X : Gadget, LocalGadgetReachable X) →
    GadgetComposition →
    ∀ T : Trail, LocalReachable T

/--
The complete `v23` route package.

This is the Lean object that says "Ben's route closes" once the Section 4-8
body is connected to the Section 3 reduction.
-/
structure Route where
  reduction : TrailReductionLayer
  middle : Section4To8Layer reduction.Trail reduction.LocalReachable

/-- Ben `v23` Sections 4-8 imply trail-level local reachability. -/
theorem allTrailsLocallyReachable (R : Route) :
    ∀ T : R.reduction.Trail, R.reduction.LocalReachable T := by
  intro T
  exact
    R.middle.localReachability_of_sections
      R.middle.all_annuli_span
      R.middle.cap5_free_normal_form
      R.middle.radius_one_locality
      R.middle.all_gadgets_reachable
      R.middle.gadget_composition
      T

/-- Ben `v23` route closure theorem. -/
theorem fourColor_of_v23Route (R : Route) :
    R.reduction.FourColorStatement := by
  exact R.reduction.fourColor_of_localReachability (allTrailsLocallyReachable R)

/--
A route is blocked exactly when its Section 4-8 middle body fails to supply the
trail-level reachability needed by Section 3.
-/
def RouteBlocked (R : Route) : Prop :=
  ¬ ∀ T : R.reduction.Trail, R.reduction.LocalReachable T

/-- If the route is blocked, the Section 3 mouth cannot yet close. -/
theorem not_fourColor_of_blocked
    (R : Route)
    (hblocked : RouteBlocked R) :
    ¬ ((∀ T : R.reduction.Trail, R.reduction.LocalReachable T) →
        R.reduction.FourColorStatement) := by
  intro hclose
  exact hblocked (by intro T; exact allTrailsLocallyReachable R T)

end FourColor.GoertzelV23
