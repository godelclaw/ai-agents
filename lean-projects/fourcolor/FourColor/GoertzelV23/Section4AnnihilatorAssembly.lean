import FourColor.GoertzelV23.Section4AnnihilatorTarget
import FourColor.GoertzelV23.Section4PurifiedFaceTarget

namespace FourColor.GoertzelV23

/--
Assembly data for Ben Goertzel's annihilator route through Section 4:
- purification upgrades generator orthogonality to purified-face orthogonality
- dual-forest peeling kills any zero-boundary chain satisfying the purified-face
  constraints

This packages those ingredients into a concrete `Section4AnnihilatorTarget`.
-/
structure Section4AnnihilatorAssemblyData where
  purifiedFace : Section4PurifiedFaceTarget
  InZeroBoundary :
    purifiedFace.purification.Annulus →
      purifiedFace.purification.Chain →
      Prop
  HasDualForestPeeling : purifiedFace.purification.Annulus → Prop
  dual_forest_peeling :
    ∀ {A : purifiedFace.purification.Annulus}
      {x : purifiedFace.purification.Chain},
      InZeroBoundary A x →
      purifiedFace.PurifiedFaceReduction A x →
      HasDualForestPeeling A →
      x = 0
  interior_dual_spanning_forest :
    ∀ A : purifiedFace.purification.Annulus, HasDualForestPeeling A

/-- Convert the assembled data into Ben's Section 4 annihilator target. -/
def Section4AnnihilatorAssemblyData.toAnnihilatorTarget
    (S : Section4AnnihilatorAssemblyData) :
    Section4AnnihilatorTarget where
  Annulus := S.purifiedFace.purification.Annulus
  Chain := S.purifiedFace.purification.Chain
  Generator := S.purifiedFace.purification.Generator
  instZeroChain := by infer_instance
  InZeroBoundary := S.InZeroBoundary
  OrthogonalToGenerator := S.purifiedFace.OrthogonalToGenerator
  PurifiedFaceReduction := S.purifiedFace.PurifiedFaceReduction
  HasDualForestPeeling := S.HasDualForestPeeling
  purified_face_reduction := by
    intro A x hx horth
    exact S.purifiedFace.purified_face_reduction horth
  dual_forest_peeling := S.dual_forest_peeling
  interior_dual_spanning_forest := S.interior_dual_spanning_forest

/--
Assembled annihilator route: zero-boundary plus orthogonality to the full
generator family forces the chain to vanish.
-/
theorem Section4AnnihilatorAssemblyData.annihilator_zero
    (S : Section4AnnihilatorAssemblyData) :
    ∀ {A : S.purifiedFace.purification.Annulus}
      {x : S.purifiedFace.purification.Chain},
      S.InZeroBoundary A x →
      (∀ g : S.purifiedFace.purification.Generator A,
        S.purifiedFace.OrthogonalToGenerator x g) →
      x = 0 := by
  intro A x hx horth
  exact (S.toAnnihilatorTarget).annihilator_zero hx horth

end FourColor.GoertzelV23
