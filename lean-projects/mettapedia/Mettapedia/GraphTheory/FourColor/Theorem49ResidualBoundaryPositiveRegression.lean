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

def twoTriangleOuterFaceDartSuccessor (d : twoTriangleAnnulusGraph.Dart) :
    twoTriangleAnnulusGraph.Dart :=
  if d = ttaDart01 then ttaDart12
  else if d = ttaDart12 then ttaDart20
  else ttaDart01

def twoTriangleInnerFaceDartSuccessor (d : twoTriangleAnnulusGraph.Dart) :
    twoTriangleAnnulusGraph.Dart :=
  if d = ttaDart34 then ttaDart45
  else if d = ttaDart45 then ttaDart53
  else ttaDart34

def twoTriangleOuterFaceDartSuccessorCycle
    (hf : (0 : TwoTriangleAnnulusFace) ∈ twoTriangleAnnulusEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryDartSuccessorCycle
      twoTriangleAnnulusEmbedding ⟨(0 : TwoTriangleAnnulusFace), hf⟩ where
  darts := [ttaDart01, ttaDart12, ttaDart20]
  hnonempty := by simp
  successor := twoTriangleOuterFaceDartSuccessor
  hsuccessor_order := by
    simp [twoTriangleOuterFaceDartSuccessor, ttaDart01, ttaDart12, ttaDart20]
  hsuccessor_adj := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;>
      simp [SimpleGraph.DartAdj, twoTriangleOuterFaceDartSuccessor,
        ttaDart01, ttaDart12, ttaDart20]
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    exact (twoTriangleOuterFacePureDartCycle hf).hedge_sub d hd
  hface_sub := by
    intro e he
    exact (twoTriangleOuterFacePureDartCycle hf).hface_sub e he

def twoTriangleInnerFaceDartSuccessorCycle
    (hf : (1 : TwoTriangleAnnulusFace) ∈ twoTriangleAnnulusEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryDartSuccessorCycle
      twoTriangleAnnulusEmbedding ⟨(1 : TwoTriangleAnnulusFace), hf⟩ where
  darts := [ttaDart34, ttaDart45, ttaDart53]
  hnonempty := by simp
  successor := twoTriangleInnerFaceDartSuccessor
  hsuccessor_order := by
    simp [twoTriangleInnerFaceDartSuccessor, ttaDart34, ttaDart45, ttaDart53]
  hsuccessor_adj := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;>
      simp [SimpleGraph.DartAdj, twoTriangleInnerFaceDartSuccessor,
        ttaDart34, ttaDart45, ttaDart53]
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    exact (twoTriangleInnerFacePureDartCycle hf).hedge_sub d hd
  hface_sub := by
    intro e he
    exact (twoTriangleInnerFacePureDartCycle hf).hface_sub e he

def twoTriangleDartSuccessorCycleGeometry :
    PlanarBoundaryDartSuccessorCycleEmbeddingData twoTriangleAnnulusEmbedding where
  faceBoundaryDartSuccessorCycle := by
    intro f
    rcases f with ⟨f, hfmem⟩
    change TwoTriangleAnnulusFace at f
    by_cases h0 : f = (0 : TwoTriangleAnnulusFace)
    · subst f
      exact twoTriangleOuterFaceDartSuccessorCycle hfmem
    · have h1 : f = (1 : TwoTriangleAnnulusFace) := by
        fin_cases f
        · exact False.elim (h0 rfl)
        · rfl
      subst f
      exact twoTriangleInnerFaceDartSuccessorCycle hfmem

theorem twoTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace :
    ∀ f : AmbientFace twoTriangleAnnulusEmbedding.faces,
      (twoTriangleDartSuccessorCycleGeometry.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f := by
  intro f
  rcases twoTriangleAnnulusFace_cases f with rfl | rfl
  ·
    refine ⟨[tta01, tta12, tta20], ?_, ?_⟩
    · decide
    · intro e
      rcases twoTriangleAnnulus_edge_eq e with rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide
  ·
    refine ⟨[tta34, tta45, tta53], ?_, ?_⟩
    · decide
    · intro e
      rcases twoTriangleAnnulus_edge_eq e with rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide

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

/-- The same exact-v23 seed is compatible with the residual/current-boundary selector surface on
the same degenerate source benchmark. -/
noncomputable def twoTriangleClosedWalkSourceResidualBoundarySelectorData :
    ResidualBoundarySelectorData twoTriangleAnnulusEmbedding :=
  Classical.choice
    (nonempty_residualBoundarySelectorData_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsNoInteriorEdges
      twoTriangleClosedWalkAnnulusBoundarySource
      rootSetCovers_twoTriangleAnnulusBoundaryFaceRoots
      rootSetSeparated_twoTriangleAnnulusBoundaryFaceRoots
      twoTriangleAnnulus_interiorEdgeSupport_eq_empty)

theorem nonempty_twoTriangleClosedWalkSourceResidualBoundarySelectorData :
    Nonempty (ResidualBoundarySelectorData twoTriangleAnnulusEmbedding) :=
  ⟨twoTriangleClosedWalkSourceResidualBoundarySelectorData⟩

/-- The annulus-construction shell extracted from the exact-v23 two-triangle residual selector
package. -/
noncomputable def twoTriangleClosedWalkSourcePlanarBoundaryAnnulusConstruction :
    PlanarBoundaryAnnulusConstruction twoTriangleAnnulusEmbedding :=
  twoTriangleClosedWalkSourceResidualBoundarySelectorData.toPlanarBoundaryAnnulusConstruction

theorem nonempty_twoTriangleClosedWalkSourcePlanarBoundaryAnnulusConstruction :
    Nonempty (PlanarBoundaryAnnulusConstruction twoTriangleAnnulusEmbedding) :=
  ⟨twoTriangleClosedWalkSourcePlanarBoundaryAnnulusConstruction⟩

/-- The exact-v23 two-triangle benchmark also reaches the residual/current-boundary selector
package. -/
theorem
    twoTriangle_closedWalkSource_tait_and_v23ResidualBoundaryInitialState_and_residualBoundarySelectorData
    :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource twoTriangleAnnulusEmbedding) ∧
      IsTaitEdgeColoring twoTriangleAnnulusGraph twoTriangleTaitEdgeColoring ∧
      Nonempty
        (V23ResidualBoundaryInitialState twoTriangleTaitEdgeColoring red blue
          (twoTriangleAnnulusEmbedding.faceBoundary twoTriangleOuterFace.1)) ∧
      Nonempty (ResidualBoundarySelectorData twoTriangleAnnulusEmbedding) := by
  exact
    ⟨⟨twoTriangleClosedWalkAnnulusBoundarySource⟩,
      twoTriangleTaitEdgeColoring_isTait,
      nonempty_twoTriangleOuterFace_v23ResidualBoundaryInitialState,
      nonempty_twoTriangleClosedWalkSourceResidualBoundarySelectorData⟩

/-- The exact-v23 two-triangle benchmark already reaches the base annulus-construction shell on
the honest closed-walk no-interior branch. -/
theorem
    twoTriangle_closedWalkSource_tait_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusConstruction
    :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource twoTriangleAnnulusEmbedding) ∧
      IsTaitEdgeColoring twoTriangleAnnulusGraph twoTriangleTaitEdgeColoring ∧
      Nonempty
        (V23ResidualBoundaryInitialState twoTriangleTaitEdgeColoring red blue
          (twoTriangleAnnulusEmbedding.faceBoundary twoTriangleOuterFace.1)) ∧
      Nonempty (PlanarBoundaryAnnulusConstruction twoTriangleAnnulusEmbedding) := by
  exact
    ⟨⟨twoTriangleClosedWalkAnnulusBoundarySource⟩,
      twoTriangleTaitEdgeColoring_isTait,
      nonempty_twoTriangleOuterFace_v23ResidualBoundaryInitialState,
      nonempty_twoTriangleClosedWalkSourcePlanarBoundaryAnnulusConstruction⟩

/-- Residual/current-boundary face-peel witness data extracted from the concrete exact-v23
two-triangle selector package. -/
noncomputable def twoTriangleClosedWalkSourceResidualBoundaryLayerFacePeelWitnessData :
    PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData twoTriangleAnnulusEmbedding :=
  twoTriangleClosedWalkSourceResidualBoundarySelectorData.toResidualBoundaryLayerFacePeelWitnessData

theorem nonempty_twoTriangleClosedWalkSourceResidualBoundaryLayerFacePeelWitnessData :
    Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData twoTriangleAnnulusEmbedding) :=
  ⟨twoTriangleClosedWalkSourceResidualBoundaryLayerFacePeelWitnessData⟩

/-- The exact-v23 two-triangle benchmark reaches the residual/current-boundary witness interface
itself, not just the upstream source-fixed or selector shells. -/
theorem
    twoTriangle_closedWalkSource_tait_and_v23ResidualBoundaryInitialState_and_residualBoundaryLayerFacePeelWitnessData
    :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource twoTriangleAnnulusEmbedding) ∧
      IsTaitEdgeColoring twoTriangleAnnulusGraph twoTriangleTaitEdgeColoring ∧
      Nonempty
        (V23ResidualBoundaryInitialState twoTriangleTaitEdgeColoring red blue
          (twoTriangleAnnulusEmbedding.faceBoundary twoTriangleOuterFace.1)) ∧
      Nonempty
        (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData twoTriangleAnnulusEmbedding) := by
  exact
    ⟨⟨twoTriangleClosedWalkAnnulusBoundarySource⟩,
      twoTriangleTaitEdgeColoring_isTait,
      nonempty_twoTriangleOuterFace_v23ResidualBoundaryInitialState,
      nonempty_twoTriangleClosedWalkSourceResidualBoundaryLayerFacePeelWitnessData⟩

/-- The exact-v23 two-triangle benchmark also reaches the residual selector surface on the actual
successor-cycle boundary-order shell. -/
theorem
    twoTriangle_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_nonempty_residualBoundarySelectorData
    :
    ∃ _boundaryData :
        PlanarBoundaryAnnulusBoundaryReachabilityData twoTriangleAnnulusEmbedding,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData twoTriangleAnnulusEmbedding,
        (∀ f : AmbientFace twoTriangleAnnulusEmbedding.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          IsTaitEdgeColoring twoTriangleAnnulusGraph twoTriangleTaitEdgeColoring ∧
          Nonempty
            (V23ResidualBoundaryInitialState twoTriangleTaitEdgeColoring red blue
              (twoTriangleAnnulusEmbedding.faceBoundary twoTriangleOuterFace.1)) ∧
          Nonempty (ResidualBoundarySelectorData twoTriangleAnnulusEmbedding) := by
  exact
    ⟨twoTriangleAnnulusBoundaryReachabilityData,
      twoTriangleDartSuccessorCycleGeometry,
      twoTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      twoTriangleTaitEdgeColoring_isTait,
      nonempty_twoTriangleOuterFace_v23ResidualBoundaryInitialState,
      nonempty_twoTriangleClosedWalkSourceResidualBoundarySelectorData⟩

/-- The same exact-v23 two-triangle benchmark reaches the base annulus-construction shell on the
actual successor-cycle boundary-order interface. -/
theorem
    twoTriangle_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_nonempty_planarBoundaryAnnulusConstruction
    :
    ∃ _boundaryData :
        PlanarBoundaryAnnulusBoundaryReachabilityData twoTriangleAnnulusEmbedding,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData twoTriangleAnnulusEmbedding,
        (∀ f : AmbientFace twoTriangleAnnulusEmbedding.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          IsTaitEdgeColoring twoTriangleAnnulusGraph twoTriangleTaitEdgeColoring ∧
          Nonempty
            (V23ResidualBoundaryInitialState twoTriangleTaitEdgeColoring red blue
              (twoTriangleAnnulusEmbedding.faceBoundary twoTriangleOuterFace.1)) ∧
          Nonempty (PlanarBoundaryAnnulusConstruction twoTriangleAnnulusEmbedding) := by
  exact
    ⟨twoTriangleAnnulusBoundaryReachabilityData,
      twoTriangleDartSuccessorCycleGeometry,
      twoTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      twoTriangleTaitEdgeColoring_isTait,
      nonempty_twoTriangleOuterFace_v23ResidualBoundaryInitialState,
      nonempty_twoTriangleClosedWalkSourcePlanarBoundaryAnnulusConstruction⟩

/-- The same exact-v23 two-triangle benchmark reaches the residual face-peel witness surface on
the actual successor-cycle boundary-order shell. -/
theorem
    twoTriangle_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_nonempty_residualBoundaryLayerFacePeelWitnessData
    :
    ∃ _boundaryData :
        PlanarBoundaryAnnulusBoundaryReachabilityData twoTriangleAnnulusEmbedding,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData twoTriangleAnnulusEmbedding,
        (∀ f : AmbientFace twoTriangleAnnulusEmbedding.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          IsTaitEdgeColoring twoTriangleAnnulusGraph twoTriangleTaitEdgeColoring ∧
          Nonempty
            (V23ResidualBoundaryInitialState twoTriangleTaitEdgeColoring red blue
              (twoTriangleAnnulusEmbedding.faceBoundary twoTriangleOuterFace.1)) ∧
          Nonempty
            (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData
              twoTriangleAnnulusEmbedding) := by
  exact
    ⟨twoTriangleAnnulusBoundaryReachabilityData,
      twoTriangleDartSuccessorCycleGeometry,
      twoTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      twoTriangleTaitEdgeColoring_isTait,
      nonempty_twoTriangleOuterFace_v23ResidualBoundaryInitialState,
      nonempty_twoTriangleClosedWalkSourceResidualBoundaryLayerFacePeelWitnessData⟩

end Theorem49ResidualBoundaryPositiveRegression

end Mettapedia.GraphTheory.FourColor
