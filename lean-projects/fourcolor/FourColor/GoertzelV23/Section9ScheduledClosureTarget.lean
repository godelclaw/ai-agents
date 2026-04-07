import FourColor.GoertzelV23.Section9ClosureTarget

namespace FourColor.GoertzelV23

universe u v

/-
The schedule-restricted refinement of Ben's Section 9 closure target.

Ben's outside-in proof only needs reachability for collars that actually appear
in the peeled collar schedule. This file captures that sharper dependency
explicitly, instead of asking for reachability of every collar in the ambient
type.
-/

/-- Reachability of the collars that actually occur in the schedule. -/
def Section9ClosureTarget.ScheduledCollarsReachable
    {Annulus : Type u}
    {Collar : Type v}
    (S : Section9ClosureTarget Annulus Collar) : Prop :=
  ∀ {A : Annulus} {C : Collar},
    C ∈ S.collarSchedule A →
    S.CollarReachable C

/--
Sharper Section 9 theorem-back package: the schedule executes as soon as the
collars that actually occur in that schedule are reachable.
-/
structure Section9ScheduledClosureTarget
    (Annulus : Type u)
    (Collar : Type v) where
  base : Section9ClosureTarget Annulus Collar
  execute_schedule_of_scheduled :
    (∀ A : Annulus, base.AnnularSpanning A) →
    base.Cap5FreeNormalForm →
    base.RadiusOneLocality →
    base.ScheduledCollarsReachable →
    ∀ {A : Annulus} {φ ψ : base.Coloring},
      base.BoundaryCompatible A φ ψ →
      ∃ w : base.Word, base.ConnectsInsideAnnulus A φ ψ w

/-- Ben's Section 9 closure theorem in schedule-restricted form. -/
theorem Section9ScheduledClosureTarget.annulus_reachable
    {Annulus : Type u}
    {Collar : Type v}
    (S : Section9ScheduledClosureTarget Annulus Collar)
    (h4 : ∀ A : Annulus, S.base.AnnularSpanning A)
    (h6 : S.base.Cap5FreeNormalForm)
    (h7 : S.base.RadiusOneLocality)
    (hSched : S.base.ScheduledCollarsReachable) :
    ∀ A : Annulus, S.base.AnnulusReachable A := by
  intro A φ ψ hcompat
  exact S.execute_schedule_of_scheduled h4 h6 h7 hSched hcompat

end FourColor.GoertzelV23
