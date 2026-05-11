import Mettapedia.GraphTheory.FourColor.Theorem49ResidualBoundaryRoute
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryAnnulusRootInteriorDualPositiveRegression
import Mettapedia.GraphTheory.FourColor.Theorem49ForcingInteriorEdgeObstruction

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

namespace Theorem49ResidualBoundaryPositiveRegression

open Theorem49PlanarBoundaryAnnulusRootInteriorDualPositiveRegression
open Theorem49ForcingInteriorEdgeObstruction

/-- Proper nonzero edge coloring on the two-triangle benchmark: each boundary triangle uses the
three nonzero colors once.  This gives a concrete Tait-world exact-v23 seed on the degenerate
no-interior source branch. -/
def twoTriangleTaitEdgeColor (e : twoTriangleAnnulusGraph.edgeSet) : Color :=
  if e = tta01 ∨ e = tta34 then red
  else if e = tta12 ∨ e = tta45 then blue
  else purple

@[simp] theorem twoTriangleTaitEdgeColor_tta01 :
    twoTriangleTaitEdgeColor tta01 = red := by
  decide

@[simp] theorem twoTriangleTaitEdgeColor_tta12 :
    twoTriangleTaitEdgeColor tta12 = blue := by
  decide

@[simp] theorem twoTriangleTaitEdgeColor_tta20 :
    twoTriangleTaitEdgeColor tta20 = purple := by
  decide

@[simp] theorem twoTriangleTaitEdgeColor_tta34 :
    twoTriangleTaitEdgeColor tta34 = red := by
  decide

@[simp] theorem twoTriangleTaitEdgeColor_tta45 :
    twoTriangleTaitEdgeColor tta45 = blue := by
  decide

@[simp] theorem twoTriangleTaitEdgeColor_tta53 :
    twoTriangleTaitEdgeColor tta53 = purple := by
  decide

/-- The concrete proper edge coloring on the two-triangle line graph. -/
def twoTriangleTaitEdgeColoring : twoTriangleAnnulusGraph.EdgeColoring Color :=
  Coloring.mk twoTriangleTaitEdgeColor (by
    intro e f hadj
    rcases twoTriangleAnnulus_edge_eq e with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases twoTriangleAnnulus_edge_eq f with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [twoTriangleTaitEdgeColor, SimpleGraph.lineGraph_adj_iff_exists,
        twoTriangleAnnulusGraph, tta01, tta12, tta20, tta34, tta45, tta53] at hadj ⊢ <;>
      decide)

theorem twoTriangleTaitEdgeColoring_isTait :
    IsTaitEdgeColoring twoTriangleAnnulusGraph twoTriangleTaitEdgeColoring := by
  intro e
  rcases twoTriangleAnnulus_edge_eq e with rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

/-- Exact Step~2 residual seed on the outer face of the degenerate two-triangle annulus source. -/
theorem nonempty_twoTriangleOuterFace_v23ResidualBoundaryInitialState :
    Nonempty
      (V23ResidualBoundaryInitialState twoTriangleTaitEdgeColoring red blue
        (twoTriangleAnnulusEmbedding.faceBoundary twoTriangleOuterFace.1)) := by
  exact
    ⟨residualBoundaryInitialState_of_sum_v23_single_component_purifications_eq_boundaryOnlyGenerator
      twoTriangleTaitEdgeColoring red blue
      (twoTriangleAnnulusEmbedding.faceBoundary twoTriangleOuterFace.1)⟩

/-- Positive exact-v23 coexistence benchmark on the honest closed-walk no-interior shell: the
two-triangle source simultaneously carries the exact Step~2 seed, the source-fixed root-cover
facts, and empty interior edge support. -/
theorem
    twoTriangle_closedWalkSource_tait_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsNoInteriorEdges
    :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource twoTriangleAnnulusEmbedding) ∧
      IsTaitEdgeColoring twoTriangleAnnulusGraph twoTriangleTaitEdgeColoring ∧
      Nonempty
        (V23ResidualBoundaryInitialState twoTriangleTaitEdgeColoring red blue
          (twoTriangleAnnulusEmbedding.faceBoundary twoTriangleOuterFace.1)) ∧
      RootSetCovers
        (interiorDualGraph twoTriangleAnnulusEmbedding.faceBoundary
          twoTriangleAnnulusEmbedding.faces)
        twoTriangleClosedWalkAnnulusBoundarySource.boundaryFaceRoots ∧
      RootSetSeparated
        (interiorDualGraph twoTriangleAnnulusEmbedding.faceBoundary
          twoTriangleAnnulusEmbedding.faces)
        twoTriangleClosedWalkAnnulusBoundarySource.boundaryFaceRoots ∧
      interiorEdgeSupport twoTriangleAnnulusEmbedding.faceBoundary
        twoTriangleAnnulusEmbedding.faces = ∅ := by
  exact
    ⟨⟨twoTriangleClosedWalkAnnulusBoundarySource⟩,
      twoTriangleTaitEdgeColoring_isTait,
      nonempty_twoTriangleOuterFace_v23ResidualBoundaryInitialState,
      rootSetCovers_twoTriangleAnnulusBoundaryFaceRoots,
      rootSetSeparated_twoTriangleAnnulusBoundaryFaceRoots,
      twoTriangleAnnulus_interiorEdgeSupport_eq_empty⟩

/-- The same exact-v23 seed is compatible with the strongest current degenerate source-fixed
parent package on the two-triangle benchmark. -/
theorem
    twoTriangle_closedWalkSource_tait_and_v23ResidualBoundaryInitialState_and_interiorDualBoundaryRootParentPeelData
    :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource twoTriangleAnnulusEmbedding) ∧
      IsTaitEdgeColoring twoTriangleAnnulusGraph twoTriangleTaitEdgeColoring ∧
      Nonempty
        (V23ResidualBoundaryInitialState twoTriangleTaitEdgeColoring red blue
          (twoTriangleAnnulusEmbedding.faceBoundary twoTriangleOuterFace.1)) ∧
      Nonempty
        (InteriorDualBoundaryRootParentPeelData twoTriangleAnnulusEmbedding.faces
          twoTriangleAnnulusEmbedding.faceBoundary) := by
  exact
    ⟨⟨twoTriangleClosedWalkAnnulusBoundarySource⟩,
      twoTriangleTaitEdgeColoring_isTait,
      nonempty_twoTriangleOuterFace_v23ResidualBoundaryInitialState,
      ⟨twoTriangleClosedWalkSourceInteriorDualBoundaryRootParentPeelData⟩⟩

/-- The same exact-v23 seed is also compatible with the local boundary-free selector surface on
the same degenerate source benchmark. -/
theorem
    twoTriangle_closedWalkSource_tait_and_v23ResidualBoundaryInitialState_and_boundaryFreeIncidentFaceSelector
    :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource twoTriangleAnnulusEmbedding) ∧
      IsTaitEdgeColoring twoTriangleAnnulusGraph twoTriangleTaitEdgeColoring ∧
      Nonempty
        (V23ResidualBoundaryInitialState twoTriangleTaitEdgeColoring red blue
          (twoTriangleAnnulusEmbedding.faceBoundary twoTriangleOuterFace.1)) ∧
      Nonempty (BoundaryFreeIncidentFaceSelector twoTriangleAnnulusEmbedding) := by
  exact
    ⟨⟨twoTriangleClosedWalkAnnulusBoundarySource⟩,
      twoTriangleTaitEdgeColoring_isTait,
      nonempty_twoTriangleOuterFace_v23ResidualBoundaryInitialState,
      nonempty_boundaryFreeIncidentFaceSelector_twoTriangleAnnulusEmbedding⟩

end Theorem49ResidualBoundaryPositiveRegression

end Mettapedia.GraphTheory.FourColor
