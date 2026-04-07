import FourColor.GoertzelV23.MiddleAssembly
import FourColor.GoertzelV23.Section4ChapterAssembly
import FourColor.GoertzelV23.Section6ChapterAssembly
import FourColor.GoertzelV23.Section7ChapterAssembly
import FourColor.GoertzelV23.Section8ChapterAssembly
import FourColor.GoertzelV23.Section9ClosureTarget

namespace FourColor.GoertzelV23

universe u

/--
Unified middle-layer theorem-back package built directly from the chapter-level
data for Sections 4, 6, 7, 8, and the new Section 9 closure target.

This is the first file that packages the whole hard middle of Ben's route in
chapter terms rather than only in the earlier abstract section-target terms.
-/
structure MiddleChapterData
    (Trail : Type u)
    (LocalReachable : Trail → Prop) where
  section4 : Section4ChapterData
  section6 : Section6ChapterData
  section7 : Section7ChapterData
  section8 : Section8ChapterData
  section9 : Section9ClosureTarget section4.Annulus section8.Collar
  trailAnnulus : Trail → section4.Annulus
  section9_annular_spanning :
    ∀ {A : section4.Annulus},
      (section4.toConcreteTarget.toSection4Target).AnnularSpanning A →
      section9.AnnularSpanning A
  section9_cap5_free :
    section6.toSection6Target.Cap5FreeNormalForm →
    section9.Cap5FreeNormalForm
  section9_radius_one_locality :
    (section7.toSection7Target).RadiusOneLocality →
    section9.RadiusOneLocality
  collar_reachability_of_section8 :
    (∀ G : section8.Gadget, (section8.toSection8Target).LocalGadgetReachable G) →
    (section8.toSection8Target).GadgetComposition →
    ∀ C : section8.Collar, section9.CollarReachable C
  annulus_reachability_implies_local :
    (∀ A : section4.Annulus, section9.AnnulusReachable A) →
    ∀ T : Trail, LocalReachable T
  allGadgetsDecomposable :
    ∀ G : section8.Gadget, section8.Decomposable G

/--
Chapter-level Section 9 closure plus the chapter outputs from Sections 4, 6, 7,
and 8 imply trail-level local reachability.
-/
theorem MiddleChapterData.local_reachability_of_chapters
    {Trail : Type u}
    {LocalReachable : Trail → Prop}
    (M : MiddleChapterData Trail LocalReachable) :
    ∀ T : Trail, LocalReachable T := by
  have h4 :
      ∀ A : M.section4.Annulus, M.section9.AnnularSpanning A := by
    intro A
    exact M.section9_annular_spanning ((M.section4.toConcreteTarget.toSection4Target).allAnnuliSpan A)
  have h6 : M.section9.Cap5FreeNormalForm :=
    M.section9_cap5_free (M.section6.toSection6Target.cap5_free_normal_form)
  have h7 : M.section9.RadiusOneLocality :=
    M.section9_radius_one_locality ((M.section7.toSection7Target).radius_one_locality)
  have h8g :
      ∀ G : M.section8.Gadget,
        (M.section8.toSection8Target).LocalGadgetReachable G := by
    intro G
    exact (M.section8.toSection8Target).decomposable_gadget_reachable (M.allGadgetsDecomposable G)
  have h8c :
      ∀ C : M.section8.Collar, M.section9.CollarReachable C := by
    exact M.collar_reachability_of_section8 h8g (M.section8.toSection8Target).gadget_composition
  have hAnn :
      ∀ A : M.section4.Annulus, M.section9.AnnulusReachable A := by
    intro A
    exact M.section9.annulus_reachable h4 h6 h7 h8c A
  exact M.annulus_reachability_implies_local hAnn

/-- Convert the chapter-level middle package back to the existing bridge layer. -/
def MiddleChapterData.toMiddleBridgeData
    {Trail : Type u}
    {LocalReachable : Trail → Prop}
    (M : MiddleChapterData Trail LocalReachable) :
    MiddleBridgeData
      Trail
      LocalReachable
      (M.section4.toConcreteTarget.toSection4Target)
      (M.section6.toSection6Target)
      (M.section7.toSection7Target)
      (M.section8.toSection8Target) where
  allGadgetsDecomposable := M.allGadgetsDecomposable
  localReachability_of_targets := by
    intro _ _ _ _ _
    exact M.local_reachability_of_chapters

/-- Assemble the abstract middle layer directly from the chapter-level data. -/
def MiddleChapterData.toSection4To8Layer
    {Trail : Type u}
    {LocalReachable : Trail → Prop}
    (M : MiddleChapterData Trail LocalReachable) :
    Section4To8Layer Trail LocalReachable :=
  assembleMiddle
    (M.section4.toConcreteTarget.toSection4Target)
    (M.section6.toSection6Target)
    (M.section7.toSection7Target)
    (M.section8.toSection8Target)
    M.toMiddleBridgeData

end FourColor.GoertzelV23
