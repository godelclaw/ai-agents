import FourColor.GoertzelV23.RouteInterface
import FourColor.GoertzelV23.Section4Target
import FourColor.GoertzelV23.Section6Target
import FourColor.GoertzelV23.Section7Target
import FourColor.GoertzelV23.Section8Target

namespace FourColor.GoertzelV23

universe u

/--
Data needed to assemble Ben Goertzel's Sections 4/6/7/8 targets into the
abstract middle layer used by `RouteInterface`.

This is still theorem-back. The only genuinely route-specific burden left here
is the bridge from the extracted section predicates to trail reachability.
-/
structure MiddleBridgeData
    (Trail : Type u)
    (LocalReachable : Trail → Prop)
    (S4 : Section4Target)
    (S6 : Section6Target)
    (S7 : Section7Target)
    (S8 : Section8Target) where
  allGadgetsDecomposable : ∀ G : S8.Gadget, S8.Decomposable G
  localReachability_of_targets :
    (∀ A : S4.Annulus, S4.AnnularSpanning A) →
    S6.Cap5FreeNormalForm →
    S7.RadiusOneLocality →
    (∀ G : S8.Gadget, S8.LocalGadgetReachable G) →
    S8.GadgetComposition →
    ∀ T : Trail, LocalReachable T

/-- Assemble the Section 4/6/7/8 targets into the middle route layer. -/
def assembleMiddle
    {Trail : Type u}
    {LocalReachable : Trail → Prop}
    (S4 : Section4Target)
    (S6 : Section6Target)
    (S7 : Section7Target)
    (S8 : Section8Target)
    (B : MiddleBridgeData Trail LocalReachable S4 S6 S7 S8) :
    Section4To8Layer Trail LocalReachable where
  Annulus := S4.Annulus
  Gadget := S8.Gadget
  AnnularSpanning := S4.AnnularSpanning
  Cap5FreeNormalForm := S6.Cap5FreeNormalForm
  RadiusOneLocality := S7.RadiusOneLocality
  LocalGadgetReachable := S8.LocalGadgetReachable
  GadgetComposition := S8.GadgetComposition
  all_annuli_span := S4.allAnnuliSpan
  cap5_free_normal_form := S6.cap5_free_normal_form
  radius_one_locality := S7.radius_one_locality
  all_gadgets_reachable := by
    intro G
    exact S8.decomposable_gadget_reachable (B.allGadgetsDecomposable G)
  gadget_composition := S8.gadget_composition
  localReachability_of_sections := B.localReachability_of_targets

/-- Assemble a full Ben `v23` route from the section targets plus bridge data. -/
def assembleRoute
    (reduction : TrailReductionLayer)
    (S4 : Section4Target)
    (S6 : Section6Target)
    (S7 : Section7Target)
    (S8 : Section8Target)
    (B :
      MiddleBridgeData
        reduction.Trail
        reduction.LocalReachable
        S4
        S6
        S7
        S8) :
    Route where
  reduction := reduction
  middle := assembleMiddle S4 S6 S7 S8 B

end FourColor.GoertzelV23
