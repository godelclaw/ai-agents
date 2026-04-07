namespace FourColor.GoertzelV23

universe u v w x

/--
The Section 9 theorem-back target for Ben Goertzel's `v23` route.

This isolates the hardest remaining proof mouth: the outside-in collar
execution that turns the chapter outputs from Sections 4, 6, 7, and 8 into the
between-region reachability needed by Section 3.

The file stays theorem-back, but it now records the actual closure shape from
Ben's Section 9:
- a wide annulus is peeled into a finite schedule of radius-1 collars
- every scheduled collar is radius-1
- if every radius-1 collar is reachable, then the whole annulus is reachable
- that implication depends on annular spanning, CAP5-free normal form, and
  radius-1 locality
-/
structure Section9ClosureTarget
    (Annulus : Type u)
    (Collar : Type v) where
  Coloring : Type w
  Word : Type x
  BoundaryCompatible : Annulus → Coloring → Coloring → Prop
  ConnectsInsideAnnulus : Annulus → Coloring → Coloring → Word → Prop
  RadiusOneCollar : Annulus → Collar → Prop
  CollarReachable : Collar → Prop
  AnnularSpanning : Annulus → Prop
  Cap5FreeNormalForm : Prop
  RadiusOneLocality : Prop
  collarSchedule : Annulus → List Collar
  schedule_radius_one :
    ∀ {A : Annulus} {C : Collar},
      C ∈ collarSchedule A →
      RadiusOneCollar A C
  execute_schedule :
    (∀ A : Annulus, AnnularSpanning A) →
    Cap5FreeNormalForm →
    RadiusOneLocality →
    (∀ C : Collar, CollarReachable C) →
    ∀ {A : Annulus} {φ ψ : Coloring},
      BoundaryCompatible A φ ψ →
      ∃ w : Word, ConnectsInsideAnnulus A φ ψ w

/-- Every collar in the Section 9 schedule is radius-1. -/
theorem Section9ClosureTarget.scheduled_collar_is_radius_one
    {Annulus : Type u}
    {Collar : Type v}
    (S : Section9ClosureTarget Annulus Collar) :
    ∀ {A : Annulus} {C : Collar},
      C ∈ S.collarSchedule A →
      S.RadiusOneCollar A C := by
  intro A C hmem
  exact S.schedule_radius_one hmem

/--
The extracted Section 9 closure predicate: every boundary-compatible pair of
colorings on the annulus is connected by the outside-in collar schedule.
-/
def Section9ClosureTarget.AnnulusReachable
    {Annulus : Type u}
    {Collar : Type v}
    (S : Section9ClosureTarget Annulus Collar) :
    Annulus → Prop :=
  fun A =>
    ∀ {φ ψ : S.Coloring},
      S.BoundaryCompatible A φ ψ →
      ∃ w : S.Word, S.ConnectsInsideAnnulus A φ ψ w

/-- Ben's Section 9 closure theorem in extracted annulus form. -/
theorem Section9ClosureTarget.annulus_reachable
    {Annulus : Type u}
    {Collar : Type v}
    (S : Section9ClosureTarget Annulus Collar)
    (h4 : ∀ A : Annulus, S.AnnularSpanning A)
    (h6 : S.Cap5FreeNormalForm)
    (h7 : S.RadiusOneLocality)
    (h8 : ∀ C : Collar, S.CollarReachable C) :
    ∀ A : Annulus, S.AnnulusReachable A := by
  intro A φ ψ hcompat
  exact S.execute_schedule h4 h6 h7 h8 hcompat

end FourColor.GoertzelV23
