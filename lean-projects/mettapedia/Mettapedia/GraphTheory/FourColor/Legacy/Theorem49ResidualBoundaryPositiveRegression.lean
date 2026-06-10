import Mettapedia.GraphTheory.FourColor.Theorem49ResidualBoundaryRoute
import Mettapedia.GraphTheory.FourColor.Legacy.Theorem49PlanarBoundaryAnnulusRootInteriorDualPositiveRegression
import Mettapedia.GraphTheory.FourColor.Theorem49ForcingInteriorEdgeObstruction
import Mettapedia.GraphTheory.FourColor.Theorem49Synthesis

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

/-- The same no-interior parent package already closes the full current Theorem 4.9 endpoint on
the concrete two-triangle embedding.  So this positive exact-v23 benchmark is not merely
compatible with the parent route; it actually reaches the full synthesis target on that branch. -/
theorem
    theorem49BoundaryRootSynthesis_twoTriangleAnnulusEmbedding_for_explicitTaitColoring_via_noInteriorParentRoute
    [Fintype twoTriangleAnnulusGraph.edgeSet]
    [FiniteDimensional F2 (twoTriangleAnnulusGraph.edgeSet → Color)] :
    Theorem49BoundaryRootSynthesis twoTriangleAnnulusEmbedding twoTriangleTaitEdgeColoring := by
  exact
    theorem49BoundaryRootSynthesis_of_planarBoundaryInteriorDualBoundaryRootParentPeelData
      twoTriangleClosedWalkSourceInteriorDualBoundaryRootParentPeelData
      twoTriangleTaitEdgeColoring
      twoTriangleTaitEdgeColoring_isTait

/-- The exact-v23 seed, honest closed-walk source, and no-interior parent route coexist with the
full theorem-4.9 endpoint on the same concrete two-triangle embedding. -/
theorem
    twoTriangle_closedWalkSource_tait_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis
    [Fintype twoTriangleAnnulusGraph.edgeSet]
    [FiniteDimensional F2 (twoTriangleAnnulusGraph.edgeSet → Color)] :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource twoTriangleAnnulusEmbedding) ∧
      IsTaitEdgeColoring twoTriangleAnnulusGraph twoTriangleTaitEdgeColoring ∧
      Nonempty
        (V23ResidualBoundaryInitialState twoTriangleTaitEdgeColoring red blue
          (twoTriangleAnnulusEmbedding.faceBoundary twoTriangleOuterFace.1)) ∧
      Theorem49BoundaryRootSynthesis
        twoTriangleAnnulusEmbedding twoTriangleTaitEdgeColoring := by
  exact
    ⟨⟨twoTriangleClosedWalkAnnulusBoundarySource⟩,
      twoTriangleTaitEdgeColoring_isTait,
      nonempty_twoTriangleOuterFace_v23ResidualBoundaryInitialState,
      theorem49BoundaryRootSynthesis_twoTriangleAnnulusEmbedding_for_explicitTaitColoring_via_noInteriorParentRoute⟩

/-- On the honest exact-v23 closed-walk shell, the same concrete two-triangle embedding already
reaches full theorem-4.9 synthesis while simultaneously failing every currently formalized
positive-stage construction shell. -/
theorem
    twoTriangle_closedWalkSource_tait_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_noPositiveStageConstructionShells
    [Fintype twoTriangleAnnulusGraph.edgeSet]
    [FiniteDimensional F2 (twoTriangleAnnulusGraph.edgeSet → Color)] :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource twoTriangleAnnulusEmbedding) ∧
      IsTaitEdgeColoring twoTriangleAnnulusGraph twoTriangleTaitEdgeColoring ∧
      Nonempty
        (V23ResidualBoundaryInitialState twoTriangleTaitEdgeColoring red blue
          (twoTriangleAnnulusEmbedding.faceBoundary twoTriangleOuterFace.1)) ∧
      Theorem49BoundaryRootSynthesis
        twoTriangleAnnulusEmbedding twoTriangleTaitEdgeColoring ∧
      NoPositiveStageConstructionShells twoTriangleAnnulusEmbedding := by
  exact
    ⟨⟨twoTriangleClosedWalkAnnulusBoundarySource⟩,
      twoTriangleTaitEdgeColoring_isTait,
      nonempty_twoTriangleOuterFace_v23ResidualBoundaryInitialState,
      theorem49BoundaryRootSynthesis_twoTriangleAnnulusEmbedding_for_explicitTaitColoring_via_noInteriorParentRoute,
      noPositiveStageConstructionShells_of_interiorEdgeSupport_eq_empty
        twoTriangleAnnulus_interiorEdgeSupport_eq_empty⟩

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

/-- On the honest exact-v23 closed-walk shell, the same concrete two-triangle embedding already
supports a local boundary-free selector while simultaneously reaching full theorem-4.9
synthesis. -/
theorem
    twoTriangle_closedWalkSource_tait_and_v23ResidualBoundaryInitialState_and_boundaryFreeIncidentFaceSelector_and_theorem49BoundaryRootSynthesis
    [Fintype twoTriangleAnnulusGraph.edgeSet]
    [FiniteDimensional F2 (twoTriangleAnnulusGraph.edgeSet → Color)] :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource twoTriangleAnnulusEmbedding) ∧
      IsTaitEdgeColoring twoTriangleAnnulusGraph twoTriangleTaitEdgeColoring ∧
      Nonempty
        (V23ResidualBoundaryInitialState twoTriangleTaitEdgeColoring red blue
          (twoTriangleAnnulusEmbedding.faceBoundary twoTriangleOuterFace.1)) ∧
      Nonempty (BoundaryFreeIncidentFaceSelector twoTriangleAnnulusEmbedding) ∧
      Theorem49BoundaryRootSynthesis
        twoTriangleAnnulusEmbedding twoTriangleTaitEdgeColoring := by
  exact
    ⟨⟨twoTriangleClosedWalkAnnulusBoundarySource⟩,
      twoTriangleTaitEdgeColoring_isTait,
      nonempty_twoTriangleOuterFace_v23ResidualBoundaryInitialState,
      nonempty_boundaryFreeIncidentFaceSelector_twoTriangleAnnulusEmbedding,
      theorem49BoundaryRootSynthesis_twoTriangleAnnulusEmbedding_for_explicitTaitColoring_via_noInteriorParentRoute⟩

/-- On the honest exact-v23 closed-walk shell, the same concrete two-triangle embedding already
supports a local boundary-free selector and full theorem-4.9 synthesis while still failing every
currently formalized positive-stage construction shell. -/
theorem
    twoTriangle_closedWalkSource_tait_and_v23ResidualBoundaryInitialState_and_boundaryFreeIncidentFaceSelector_and_theorem49BoundaryRootSynthesis_and_noPositiveStageConstructionShells
    [Fintype twoTriangleAnnulusGraph.edgeSet]
    [FiniteDimensional F2 (twoTriangleAnnulusGraph.edgeSet → Color)] :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource twoTriangleAnnulusEmbedding) ∧
      IsTaitEdgeColoring twoTriangleAnnulusGraph twoTriangleTaitEdgeColoring ∧
      Nonempty
        (V23ResidualBoundaryInitialState twoTriangleTaitEdgeColoring red blue
          (twoTriangleAnnulusEmbedding.faceBoundary twoTriangleOuterFace.1)) ∧
      Nonempty (BoundaryFreeIncidentFaceSelector twoTriangleAnnulusEmbedding) ∧
      Theorem49BoundaryRootSynthesis
        twoTriangleAnnulusEmbedding twoTriangleTaitEdgeColoring ∧
      NoPositiveStageConstructionShells twoTriangleAnnulusEmbedding := by
  exact
    ⟨⟨twoTriangleClosedWalkAnnulusBoundarySource⟩,
      twoTriangleTaitEdgeColoring_isTait,
      nonempty_twoTriangleOuterFace_v23ResidualBoundaryInitialState,
      nonempty_boundaryFreeIncidentFaceSelector_twoTriangleAnnulusEmbedding,
      theorem49BoundaryRootSynthesis_twoTriangleAnnulusEmbedding_for_explicitTaitColoring_via_noInteriorParentRoute,
      noPositiveStageConstructionShells_of_interiorEdgeSupport_eq_empty
        twoTriangleAnnulus_interiorEdgeSupport_eq_empty⟩

/-- The exact-v23 two-triangle benchmark also packages an honest closed-walk witness showing
that a real residual seed, a real Tait coloring, a real local boundary-free selector, and full
theorem-4.9 synthesis can coexist with failure of the entire currently formalized positive-stage
construction surface. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_boundaryFreeIncidentFaceSelector_and_theorem49BoundaryRootSynthesis_without_somePositiveStageConstructionShell_twoTriangleAnnulusGraph
    [Fintype twoTriangleAnnulusGraph.edgeSet]
    [FiniteDimensional F2 (twoTriangleAnnulusGraph.edgeSet → Color)] :
    ∃ emb : PlaneEmbeddingWithBoundary twoTriangleAnnulusGraph,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ C : twoTriangleAnnulusGraph.EdgeColoring Color,
          IsTaitEdgeColoring twoTriangleAnnulusGraph C ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset twoTriangleAnnulusGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  Nonempty (BoundaryFreeIncidentFaceSelector emb) ∧
                  Theorem49BoundaryRootSynthesis emb C ∧
                  ¬ SomePositiveStageConstructionShell emb := by
  exact
    ⟨twoTriangleAnnulusEmbedding,
      twoTriangleClosedWalkAnnulusBoundarySource,
      twoTriangleTaitEdgeColoring,
      twoTriangleTaitEdgeColoring_isTait,
      red, blue,
      twoTriangleAnnulusEmbedding.faceBoundary twoTriangleOuterFace.1,
      nonempty_twoTriangleOuterFace_v23ResidualBoundaryInitialState,
      nonempty_boundaryFreeIncidentFaceSelector_twoTriangleAnnulusEmbedding,
      theorem49BoundaryRootSynthesis_twoTriangleAnnulusEmbedding_for_explicitTaitColoring_via_noInteriorParentRoute,
      not_somePositiveStageConstructionShell_of_noPositiveStageConstructionShells
        (noPositiveStageConstructionShells_of_interiorEdgeSupport_eq_empty
          twoTriangleAnnulus_interiorEdgeSupport_eq_empty)⟩

/-- So even the honest closed-walk exact-v23 source shell plus a real Tait coloring, a real
local boundary-free selector, and full theorem-4.9 synthesis does not universally force any
currently formalized positive-stage construction shell. -/
theorem
    not_forall_somePositiveStageConstructionShell_of_closedWalkAnnulusBoundarySource_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_boundaryFreeIncidentFaceSelector_and_theorem49BoundaryRootSynthesis_twoTriangleAnnulusGraph
    [Fintype twoTriangleAnnulusGraph.edgeSet]
    [FiniteDimensional F2 (twoTriangleAnnulusGraph.edgeSet → Color)] :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary twoTriangleAnnulusGraph,
        ∀ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          ∀ C : twoTriangleAnnulusGraph.EdgeColoring Color,
            IsTaitEdgeColoring twoTriangleAnnulusGraph C →
              ∀ a b : Color,
                ∀ faceBoundary : Finset twoTriangleAnnulusGraph.edgeSet,
                  Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                    Theorem49BoundaryRootSynthesis emb C →
                      Nonempty (BoundaryFreeIncidentFaceSelector emb) →
                        SomePositiveStageConstructionShell emb := by
  rcases
      twoTriangle_closedWalkSource_tait_and_v23ResidualBoundaryInitialState_and_boundaryFreeIncidentFaceSelector_and_theorem49BoundaryRootSynthesis_and_noPositiveStageConstructionShells with
    ⟨hSource, hC, hv23, hSelector, hSynth, hNo⟩
  rcases hSource with ⟨source⟩
  exact
    not_forall_somePositiveStageConstructionShell_of_exists_embedding_closedWalkAnnulusBoundarySource_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_boundaryFreeIncidentFaceSelector_and_theorem49BoundaryRootSynthesis_and_noPositiveStageConstructionShells
      (G := twoTriangleAnnulusGraph)
      ⟨twoTriangleAnnulusEmbedding, source, twoTriangleTaitEdgeColoring, hC, red, blue,
        twoTriangleAnnulusEmbedding.faceBoundary twoTriangleOuterFace.1, hv23, hSelector, hSynth,
        hNo⟩

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

/-- On the exact-v23 two-triangle benchmark, the stronger selected-boundary-contact annulus
construction shell cannot hold because every positive-stage frontier is forced into the empty
interior-edge support. -/
theorem not_nonempty_planarBoundaryAnnulusConstructionBoundarySupportFaceData_twoTriangleAnnulusEmbedding
    :
    ¬ Nonempty
      (PlanarBoundaryAnnulusConstructionBoundarySupportFaceData twoTriangleAnnulusEmbedding) :=
  not_nonempty_planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_interiorEdgeSupport_eq_empty
    twoTriangleAnnulus_interiorEdgeSupport_eq_empty

/-- The exact-v23 two-triangle benchmark also refutes the explicit outer/peeled/inner
face-partition annulus shell for the same reason. -/
theorem not_nonempty_planarBoundaryAnnulusConstructionFacePartitionData_twoTriangleAnnulusEmbedding
    :
    ¬ Nonempty
      (PlanarBoundaryAnnulusConstructionFacePartitionData twoTriangleAnnulusEmbedding) :=
  not_nonempty_planarBoundaryAnnulusConstructionFacePartitionData_of_interiorEdgeSupport_eq_empty
    twoTriangleAnnulus_interiorEdgeSupport_eq_empty

/-- The exact-v23 two-triangle benchmark cannot realize any positive-stage outer-frontier shell,
even though the base annulus construction itself exists. -/
theorem not_nonempty_planarBoundaryAnnulusConstructionPositiveFrontierData_twoTriangleAnnulusEmbedding
    :
    ¬ Nonempty
      (PlanarBoundaryAnnulusConstructionPositiveFrontierData twoTriangleAnnulusEmbedding) :=
  not_nonempty_planarBoundaryAnnulusConstructionPositiveFrontierData_of_interiorEdgeSupport_eq_empty
    twoTriangleAnnulus_interiorEdgeSupport_eq_empty

/-- The strongest construction-side face-layer shell also fails on the exact-v23 two-triangle
benchmark because its positive-stage outer boundaries would have to be nonempty. -/
theorem not_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_twoTriangleAnnulusEmbedding
    :
    ¬ Nonempty
      (PlanarBoundaryAnnulusConstructionFaceLayerData twoTriangleAnnulusEmbedding) :=
  not_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_interiorEdgeSupport_eq_empty
    twoTriangleAnnulus_interiorEdgeSupport_eq_empty

/-- The exact-v23 two-triangle benchmark simultaneously refutes all currently formalized
positive-stage construction shells. -/
theorem noPositiveStageConstructionShells_twoTriangleAnnulusEmbedding :
    NoPositiveStageConstructionShells twoTriangleAnnulusEmbedding := by
  exact
    noPositiveStageConstructionShells_of_interiorEdgeSupport_eq_empty
      twoTriangleAnnulus_interiorEdgeSupport_eq_empty

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
    twoTriangle_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_nonempty_boundaryFreeIncidentFaceSelector
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
          Nonempty (BoundaryFreeIncidentFaceSelector twoTriangleAnnulusEmbedding) := by
  exact
    ⟨twoTriangleAnnulusBoundaryReachabilityData,
      twoTriangleDartSuccessorCycleGeometry,
      twoTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      twoTriangleTaitEdgeColoring_isTait,
      nonempty_twoTriangleOuterFace_v23ResidualBoundaryInitialState,
      nonempty_boundaryFreeIncidentFaceSelector_twoTriangleAnnulusEmbedding⟩

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

/-- On the actual exact-v23 successor-cycle shell, the same concrete two-triangle benchmark
simultaneously supports a local boundary-free selector and reaches full theorem-4.9 synthesis. -/
theorem
    twoTriangle_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_nonempty_boundaryFreeIncidentFaceSelector_and_theorem49BoundaryRootSynthesis
    [Fintype twoTriangleAnnulusGraph.edgeSet]
    [FiniteDimensional F2 (twoTriangleAnnulusGraph.edgeSet → Color)] :
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
          Nonempty (BoundaryFreeIncidentFaceSelector twoTriangleAnnulusEmbedding) ∧
          Theorem49BoundaryRootSynthesis
            twoTriangleAnnulusEmbedding twoTriangleTaitEdgeColoring := by
  exact
    ⟨twoTriangleAnnulusBoundaryReachabilityData,
      twoTriangleDartSuccessorCycleGeometry,
      twoTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      twoTriangleTaitEdgeColoring_isTait,
      nonempty_twoTriangleOuterFace_v23ResidualBoundaryInitialState,
      nonempty_boundaryFreeIncidentFaceSelector_twoTriangleAnnulusEmbedding,
      theorem49BoundaryRootSynthesis_twoTriangleAnnulusEmbedding_for_explicitTaitColoring_via_noInteriorParentRoute⟩

/-- On the actual exact-v23 successor-cycle shell, the same concrete two-triangle benchmark
already supports a local boundary-free selector and full theorem-4.9 synthesis while still
failing every currently formalized positive-stage construction shell. -/
theorem
    twoTriangle_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_nonempty_boundaryFreeIncidentFaceSelector_and_theorem49BoundaryRootSynthesis_and_noPositiveStageConstructionShells
    [Fintype twoTriangleAnnulusGraph.edgeSet]
    [FiniteDimensional F2 (twoTriangleAnnulusGraph.edgeSet → Color)] :
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
          Nonempty (BoundaryFreeIncidentFaceSelector twoTriangleAnnulusEmbedding) ∧
          Theorem49BoundaryRootSynthesis
            twoTriangleAnnulusEmbedding twoTriangleTaitEdgeColoring ∧
          NoPositiveStageConstructionShells twoTriangleAnnulusEmbedding := by
  exact
    ⟨twoTriangleAnnulusBoundaryReachabilityData,
      twoTriangleDartSuccessorCycleGeometry,
      twoTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      twoTriangleTaitEdgeColoring_isTait,
      nonempty_twoTriangleOuterFace_v23ResidualBoundaryInitialState,
      nonempty_boundaryFreeIncidentFaceSelector_twoTriangleAnnulusEmbedding,
      theorem49BoundaryRootSynthesis_twoTriangleAnnulusEmbedding_for_explicitTaitColoring_via_noInteriorParentRoute,
      noPositiveStageConstructionShells_twoTriangleAnnulusEmbedding⟩

/-- The exact-v23 two-triangle benchmark also packages the same selector-strengthened failure
directly on the live successor-cycle selected-arc shell. -/
theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_boundaryFreeIncidentFaceSelector_and_theorem49BoundaryRootSynthesis_without_somePositiveStageConstructionShell_twoTriangleAnnulusGraph
    [Fintype twoTriangleAnnulusGraph.edgeSet]
    [FiniteDimensional F2 (twoTriangleAnnulusGraph.edgeSet → Color)] :
    ∃ emb : PlaneEmbeddingWithBoundary twoTriangleAnnulusGraph,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        ∃ C : twoTriangleAnnulusGraph.EdgeColoring Color,
          IsTaitEdgeColoring twoTriangleAnnulusGraph C ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset twoTriangleAnnulusGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  Nonempty (BoundaryFreeIncidentFaceSelector emb) ∧
                  Theorem49BoundaryRootSynthesis emb C ∧
                  ¬ SomePositiveStageConstructionShell emb := by
  exact
    ⟨twoTriangleAnnulusEmbedding,
      twoTriangleAnnulusBoundaryReachabilityData,
      twoTriangleDartSuccessorCycleGeometry,
      twoTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      twoTriangleTaitEdgeColoring,
      twoTriangleTaitEdgeColoring_isTait,
      red, blue,
      twoTriangleAnnulusEmbedding.faceBoundary twoTriangleOuterFace.1,
      nonempty_twoTriangleOuterFace_v23ResidualBoundaryInitialState,
      nonempty_boundaryFreeIncidentFaceSelector_twoTriangleAnnulusEmbedding,
      theorem49BoundaryRootSynthesis_twoTriangleAnnulusEmbedding_for_explicitTaitColoring_via_noInteriorParentRoute,
      not_somePositiveStageConstructionShell_of_noPositiveStageConstructionShells
        noPositiveStageConstructionShells_twoTriangleAnnulusEmbedding⟩

/-- So even the actual successor-cycle exact-v23 selected-arc shell, together with a real Tait
coloring, a real local boundary-free selector, and full theorem-4.9 synthesis, does not
universally force any currently formalized positive-stage construction shell. -/
theorem
    not_forall_somePositiveStageConstructionShell_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_boundaryFreeIncidentFaceSelector_and_theorem49BoundaryRootSynthesis_twoTriangleAnnulusGraph
    [Fintype twoTriangleAnnulusGraph.edgeSet]
    [FiniteDimensional F2 (twoTriangleAnnulusGraph.edgeSet → Color)] :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary twoTriangleAnnulusGraph,
        ∀ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
            ∀ C : twoTriangleAnnulusGraph.EdgeColoring Color,
              IsTaitEdgeColoring twoTriangleAnnulusGraph C →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset twoTriangleAnnulusGraph.edgeSet,
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                      Theorem49BoundaryRootSynthesis emb C →
                        Nonempty (BoundaryFreeIncidentFaceSelector emb) →
                          SomePositiveStageConstructionShell emb := by
  rcases
      twoTriangle_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_nonempty_boundaryFreeIncidentFaceSelector_and_theorem49BoundaryRootSynthesis_and_noPositiveStageConstructionShells with
    ⟨boundaryData, dartCycles, hSelectedBoundaryArc, hC, hv23, hSelector, hSynth, hNo⟩
  exact
    not_forall_somePositiveStageConstructionShell_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_boundaryFreeIncidentFaceSelector_and_theorem49BoundaryRootSynthesis_and_noPositiveStageConstructionShells
      (G := twoTriangleAnnulusGraph)
      ⟨twoTriangleAnnulusEmbedding, boundaryData, dartCycles, hSelectedBoundaryArc,
        twoTriangleTaitEdgeColoring, hC, red, blue,
        twoTriangleAnnulusEmbedding.faceBoundary twoTriangleOuterFace.1, hv23, hSelector, hSynth,
        hNo⟩

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

/-- The same exact-v23 two-triangle benchmark reaches the base annulus construction on the actual
successor-cycle boundary-order interface, but still cannot realize any positive-stage outer
frontier shell. -/
theorem
    twoTriangle_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_nonempty_planarBoundaryAnnulusConstruction_and_not_nonempty_planarBoundaryAnnulusConstructionPositiveFrontierData
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
          Nonempty (PlanarBoundaryAnnulusConstruction twoTriangleAnnulusEmbedding) ∧
          ¬ Nonempty
            (PlanarBoundaryAnnulusConstructionPositiveFrontierData
              twoTriangleAnnulusEmbedding) := by
  exact
    ⟨twoTriangleAnnulusBoundaryReachabilityData,
      twoTriangleDartSuccessorCycleGeometry,
      twoTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      twoTriangleTaitEdgeColoring_isTait,
      nonempty_twoTriangleOuterFace_v23ResidualBoundaryInitialState,
      nonempty_twoTriangleClosedWalkSourcePlanarBoundaryAnnulusConstruction,
      not_nonempty_planarBoundaryAnnulusConstructionPositiveFrontierData_twoTriangleAnnulusEmbedding⟩

/-- The same exact-v23 seed and actual successor-cycle selected-arc shell also coexist with the
full theorem-4.9 endpoint on the concrete two-triangle embedding. -/
theorem
    twoTriangle_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis
    [Fintype twoTriangleAnnulusGraph.edgeSet]
    [FiniteDimensional F2 (twoTriangleAnnulusGraph.edgeSet → Color)] :
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
          Theorem49BoundaryRootSynthesis
            twoTriangleAnnulusEmbedding twoTriangleTaitEdgeColoring := by
  exact
    ⟨twoTriangleAnnulusBoundaryReachabilityData,
      twoTriangleDartSuccessorCycleGeometry,
      twoTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      twoTriangleTaitEdgeColoring_isTait,
      nonempty_twoTriangleOuterFace_v23ResidualBoundaryInitialState,
      theorem49BoundaryRootSynthesis_twoTriangleAnnulusEmbedding_for_explicitTaitColoring_via_noInteriorParentRoute⟩

/-- On the same exact-v23 successor-cycle shell, the explicit theorem-4.9 endpoint still
coexists with failure of the positive-stage frontier package.  So this benchmark does not merely
separate base construction from frontier growth; it separates the full synthesis endpoint from
that frontier shell too. -/
theorem
    twoTriangle_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_not_nonempty_planarBoundaryAnnulusConstructionPositiveFrontierData
    [Fintype twoTriangleAnnulusGraph.edgeSet]
    [FiniteDimensional F2 (twoTriangleAnnulusGraph.edgeSet → Color)] :
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
          Theorem49BoundaryRootSynthesis
            twoTriangleAnnulusEmbedding twoTriangleTaitEdgeColoring ∧
          ¬ Nonempty
            (PlanarBoundaryAnnulusConstructionPositiveFrontierData
              twoTriangleAnnulusEmbedding) := by
  exact
    ⟨twoTriangleAnnulusBoundaryReachabilityData,
      twoTriangleDartSuccessorCycleGeometry,
      twoTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      twoTriangleTaitEdgeColoring_isTait,
      nonempty_twoTriangleOuterFace_v23ResidualBoundaryInitialState,
      theorem49BoundaryRootSynthesis_twoTriangleAnnulusEmbedding_for_explicitTaitColoring_via_noInteriorParentRoute,
      not_nonempty_planarBoundaryAnnulusConstructionPositiveFrontierData_twoTriangleAnnulusEmbedding⟩

/-- On the actual exact-v23 successor-cycle shell, the concrete two-triangle benchmark already
reaches full theorem-4.9 synthesis while simultaneously failing every currently formalized
positive-stage construction shell. -/
theorem
    twoTriangle_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_noPositiveStageConstructionShells
    [Fintype twoTriangleAnnulusGraph.edgeSet]
    [FiniteDimensional F2 (twoTriangleAnnulusGraph.edgeSet → Color)] :
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
          Theorem49BoundaryRootSynthesis
            twoTriangleAnnulusEmbedding twoTriangleTaitEdgeColoring ∧
          NoPositiveStageConstructionShells twoTriangleAnnulusEmbedding := by
  exact
    ⟨twoTriangleAnnulusBoundaryReachabilityData,
      twoTriangleDartSuccessorCycleGeometry,
      twoTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      twoTriangleTaitEdgeColoring_isTait,
      nonempty_twoTriangleOuterFace_v23ResidualBoundaryInitialState,
      theorem49BoundaryRootSynthesis_twoTriangleAnnulusEmbedding_for_explicitTaitColoring_via_noInteriorParentRoute,
      noPositiveStageConstructionShells_twoTriangleAnnulusEmbedding⟩

/-- Graph-level witness form of the same benchmark: one explicit Tait-colored embedding already
has full theorem-4.9 synthesis while failing every currently formalized positive-stage
construction shell. -/
theorem
    exists_embedding_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_and_noPositiveStageConstructionShells_twoTriangleAnnulusGraph
    [Fintype twoTriangleAnnulusGraph.edgeSet]
    [FiniteDimensional F2 (twoTriangleAnnulusGraph.edgeSet → Color)] :
    ∃ emb : PlaneEmbeddingWithBoundary twoTriangleAnnulusGraph,
      (∃ C : twoTriangleAnnulusGraph.EdgeColoring Color,
        IsTaitEdgeColoring twoTriangleAnnulusGraph C ∧
          Theorem49BoundaryRootSynthesis emb C) ∧
        NoPositiveStageConstructionShells emb := by
  exact
    ⟨twoTriangleAnnulusEmbedding,
      ⟨twoTriangleTaitEdgeColoring,
        twoTriangleTaitEdgeColoring_isTait,
        theorem49BoundaryRootSynthesis_twoTriangleAnnulusEmbedding_for_explicitTaitColoring_via_noInteriorParentRoute⟩,
      noPositiveStageConstructionShells_twoTriangleAnnulusEmbedding⟩

/-- The exact-v23 two-triangle benchmark also packages an honest closed-walk witness showing
that a real residual seed, a real Tait coloring, and full theorem-4.9 synthesis can coexist with
failure of the entire currently formalized positive-stage construction surface. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_without_somePositiveStageConstructionShell_twoTriangleAnnulusGraph
    [Fintype twoTriangleAnnulusGraph.edgeSet]
    [FiniteDimensional F2 (twoTriangleAnnulusGraph.edgeSet → Color)] :
    ∃ emb : PlaneEmbeddingWithBoundary twoTriangleAnnulusGraph,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ C : twoTriangleAnnulusGraph.EdgeColoring Color,
          IsTaitEdgeColoring twoTriangleAnnulusGraph C ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset twoTriangleAnnulusGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  Theorem49BoundaryRootSynthesis emb C ∧
                  ¬ SomePositiveStageConstructionShell emb := by
  exact
    ⟨twoTriangleAnnulusEmbedding,
      twoTriangleClosedWalkAnnulusBoundarySource,
      twoTriangleTaitEdgeColoring,
      twoTriangleTaitEdgeColoring_isTait,
      red, blue,
      twoTriangleAnnulusEmbedding.faceBoundary twoTriangleOuterFace.1,
      nonempty_twoTriangleOuterFace_v23ResidualBoundaryInitialState,
      theorem49BoundaryRootSynthesis_twoTriangleAnnulusEmbedding_for_explicitTaitColoring_via_noInteriorParentRoute,
      not_somePositiveStageConstructionShell_of_noPositiveStageConstructionShells
        noPositiveStageConstructionShells_twoTriangleAnnulusEmbedding⟩

/-- So even the honest closed-walk exact-v23 source shell plus a real Tait coloring and full
theorem-4.9 synthesis does not universally force any currently formalized positive-stage
construction shell. -/
theorem
    not_forall_somePositiveStageConstructionShell_of_closedWalkAnnulusBoundarySource_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_twoTriangleAnnulusGraph
    [Fintype twoTriangleAnnulusGraph.edgeSet]
    [FiniteDimensional F2 (twoTriangleAnnulusGraph.edgeSet → Color)] :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary twoTriangleAnnulusGraph,
        ∀ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          ∀ C : twoTriangleAnnulusGraph.EdgeColoring Color,
            IsTaitEdgeColoring twoTriangleAnnulusGraph C →
              ∀ a b : Color,
                ∀ faceBoundary : Finset twoTriangleAnnulusGraph.edgeSet,
                  Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                    Theorem49BoundaryRootSynthesis emb C →
                      SomePositiveStageConstructionShell emb := by
  rcases
      twoTriangle_closedWalkSource_tait_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_noPositiveStageConstructionShells with
    ⟨hSource, hC, hv23, hSynth, hNo⟩
  rcases hSource with ⟨source⟩
  exact
    not_forall_somePositiveStageConstructionShell_of_exists_embedding_closedWalkAnnulusBoundarySource_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_noPositiveStageConstructionShells
      (G := twoTriangleAnnulusGraph)
      ⟨twoTriangleAnnulusEmbedding, source, twoTriangleTaitEdgeColoring, hC, red, blue,
        twoTriangleAnnulusEmbedding.faceBoundary twoTriangleOuterFace.1, hv23, hSynth, hNo⟩

/-- The exact-v23 two-triangle benchmark also packages the same failure directly on the live
successor-cycle selected-arc shell. -/
theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_without_somePositiveStageConstructionShell_twoTriangleAnnulusGraph
    [Fintype twoTriangleAnnulusGraph.edgeSet]
    [FiniteDimensional F2 (twoTriangleAnnulusGraph.edgeSet → Color)] :
    ∃ emb : PlaneEmbeddingWithBoundary twoTriangleAnnulusGraph,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        ∃ C : twoTriangleAnnulusGraph.EdgeColoring Color,
          IsTaitEdgeColoring twoTriangleAnnulusGraph C ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset twoTriangleAnnulusGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  Theorem49BoundaryRootSynthesis emb C ∧
                  ¬ SomePositiveStageConstructionShell emb := by
  exact
    ⟨twoTriangleAnnulusEmbedding,
      twoTriangleAnnulusBoundaryReachabilityData,
      twoTriangleDartSuccessorCycleGeometry,
      twoTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      twoTriangleTaitEdgeColoring,
      twoTriangleTaitEdgeColoring_isTait,
      red, blue,
      twoTriangleAnnulusEmbedding.faceBoundary twoTriangleOuterFace.1,
      nonempty_twoTriangleOuterFace_v23ResidualBoundaryInitialState,
      theorem49BoundaryRootSynthesis_twoTriangleAnnulusEmbedding_for_explicitTaitColoring_via_noInteriorParentRoute,
      not_somePositiveStageConstructionShell_of_noPositiveStageConstructionShells
        noPositiveStageConstructionShells_twoTriangleAnnulusEmbedding⟩

/-- So even the actual successor-cycle exact-v23 selected-arc shell, together with a real Tait
coloring and full theorem-4.9 synthesis, does not universally force any currently formalized
positive-stage construction shell. -/
theorem
    not_forall_somePositiveStageConstructionShell_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_twoTriangleAnnulusGraph
    [Fintype twoTriangleAnnulusGraph.edgeSet]
    [FiniteDimensional F2 (twoTriangleAnnulusGraph.edgeSet → Color)] :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary twoTriangleAnnulusGraph,
        ∀ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
            ∀ C : twoTriangleAnnulusGraph.EdgeColoring Color,
              IsTaitEdgeColoring twoTriangleAnnulusGraph C →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset twoTriangleAnnulusGraph.edgeSet,
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                      Theorem49BoundaryRootSynthesis emb C →
                        SomePositiveStageConstructionShell emb := by
  rcases
      twoTriangle_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_noPositiveStageConstructionShells with
    ⟨boundaryData, dartCycles, hSelectedBoundaryArc, hC, hv23, hSynth, hNo⟩
  exact
    not_forall_somePositiveStageConstructionShell_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_noPositiveStageConstructionShells
      (G := twoTriangleAnnulusGraph)
      ⟨twoTriangleAnnulusEmbedding, boundaryData, dartCycles, hSelectedBoundaryArc,
        twoTriangleTaitEdgeColoring, hC, red, blue,
        twoTriangleAnnulusEmbedding.faceBoundary twoTriangleOuterFace.1, hv23, hSynth, hNo⟩

/-- So even the final theorem-4.9 boundary-root synthesis endpoint under an actual Tait coloring
does not universally force any of the currently formalized positive-stage construction shells. -/
theorem
    not_forall_somePositiveStageConstructionShell_of_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_twoTriangleAnnulusGraph
    [Fintype twoTriangleAnnulusGraph.edgeSet]
    [FiniteDimensional F2 (twoTriangleAnnulusGraph.edgeSet → Color)] :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary twoTriangleAnnulusGraph}
        (C : twoTriangleAnnulusGraph.EdgeColoring Color),
        IsTaitEdgeColoring twoTriangleAnnulusGraph C →
          Theorem49BoundaryRootSynthesis emb C →
            SomePositiveStageConstructionShell emb := by
  exact
    not_forall_somePositiveStageConstructionShell_of_exists_embedding_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_and_noPositiveStageConstructionShells
      (G := twoTriangleAnnulusGraph)
      exists_embedding_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_and_noPositiveStageConstructionShells_twoTriangleAnnulusGraph

/-- The explicit two-triangle benchmark already witnesses that the final theorem-4.9 endpoint
under a real Tait coloring can coexist with failure of boundary-support face data on the same
embedding. -/
theorem
    exists_embedding_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_without_planarBoundaryAnnulusConstructionBoundarySupportFaceData_twoTriangleAnnulusGraph
    [Fintype twoTriangleAnnulusGraph.edgeSet]
    [FiniteDimensional F2 (twoTriangleAnnulusGraph.edgeSet → Color)] :
    ∃ emb : PlaneEmbeddingWithBoundary twoTriangleAnnulusGraph,
      (∃ C : twoTriangleAnnulusGraph.EdgeColoring Color,
        IsTaitEdgeColoring twoTriangleAnnulusGraph C ∧
          Theorem49BoundaryRootSynthesis emb C) ∧
        ¬ Nonempty (PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb) := by
  exact
    ⟨twoTriangleAnnulusEmbedding,
      ⟨twoTriangleTaitEdgeColoring,
        twoTriangleTaitEdgeColoring_isTait,
        theorem49BoundaryRootSynthesis_twoTriangleAnnulusEmbedding_for_explicitTaitColoring_via_noInteriorParentRoute⟩,
      not_nonempty_planarBoundaryAnnulusConstructionBoundarySupportFaceData_twoTriangleAnnulusEmbedding⟩

/-- The explicit two-triangle benchmark already witnesses that the final theorem-4.9 endpoint
under a real Tait coloring can coexist with failure of face-partition data on the same
embedding. -/
theorem
    exists_embedding_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_without_planarBoundaryAnnulusConstructionFacePartitionData_twoTriangleAnnulusGraph
    [Fintype twoTriangleAnnulusGraph.edgeSet]
    [FiniteDimensional F2 (twoTriangleAnnulusGraph.edgeSet → Color)] :
    ∃ emb : PlaneEmbeddingWithBoundary twoTriangleAnnulusGraph,
      (∃ C : twoTriangleAnnulusGraph.EdgeColoring Color,
        IsTaitEdgeColoring twoTriangleAnnulusGraph C ∧
          Theorem49BoundaryRootSynthesis emb C) ∧
        ¬ Nonempty (PlanarBoundaryAnnulusConstructionFacePartitionData emb) := by
  exact
    ⟨twoTriangleAnnulusEmbedding,
      ⟨twoTriangleTaitEdgeColoring,
        twoTriangleTaitEdgeColoring_isTait,
        theorem49BoundaryRootSynthesis_twoTriangleAnnulusEmbedding_for_explicitTaitColoring_via_noInteriorParentRoute⟩,
      not_nonempty_planarBoundaryAnnulusConstructionFacePartitionData_twoTriangleAnnulusEmbedding⟩

/-- The explicit two-triangle benchmark already witnesses that the final theorem-4.9 endpoint
under a real Tait coloring can coexist with failure of face-layer data on the same embedding. -/
theorem
    exists_embedding_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_without_planarBoundaryAnnulusConstructionFaceLayerData_twoTriangleAnnulusGraph
    [Fintype twoTriangleAnnulusGraph.edgeSet]
    [FiniteDimensional F2 (twoTriangleAnnulusGraph.edgeSet → Color)] :
    ∃ emb : PlaneEmbeddingWithBoundary twoTriangleAnnulusGraph,
      (∃ C : twoTriangleAnnulusGraph.EdgeColoring Color,
        IsTaitEdgeColoring twoTriangleAnnulusGraph C ∧
          Theorem49BoundaryRootSynthesis emb C) ∧
        ¬ Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb) := by
  exact
    ⟨twoTriangleAnnulusEmbedding,
      ⟨twoTriangleTaitEdgeColoring,
        twoTriangleTaitEdgeColoring_isTait,
        theorem49BoundaryRootSynthesis_twoTriangleAnnulusEmbedding_for_explicitTaitColoring_via_noInteriorParentRoute⟩,
      not_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_twoTriangleAnnulusEmbedding⟩

/-- The explicit two-triangle benchmark already witnesses that the final theorem-4.9 endpoint
under a real Tait coloring can coexist with failure of positive-frontier annulus-construction
data on the same embedding. -/
theorem
    exists_embedding_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_without_planarBoundaryAnnulusConstructionPositiveFrontierData_twoTriangleAnnulusGraph
    [Fintype twoTriangleAnnulusGraph.edgeSet]
    [FiniteDimensional F2 (twoTriangleAnnulusGraph.edgeSet → Color)] :
    ∃ emb : PlaneEmbeddingWithBoundary twoTriangleAnnulusGraph,
      (∃ C : twoTriangleAnnulusGraph.EdgeColoring Color,
        IsTaitEdgeColoring twoTriangleAnnulusGraph C ∧
          Theorem49BoundaryRootSynthesis emb C) ∧
        ¬ Nonempty (PlanarBoundaryAnnulusConstructionPositiveFrontierData emb) := by
  exact
    ⟨twoTriangleAnnulusEmbedding,
      ⟨twoTriangleTaitEdgeColoring,
        twoTriangleTaitEdgeColoring_isTait,
        theorem49BoundaryRootSynthesis_twoTriangleAnnulusEmbedding_for_explicitTaitColoring_via_noInteriorParentRoute⟩,
      not_nonempty_planarBoundaryAnnulusConstructionPositiveFrontierData_twoTriangleAnnulusEmbedding⟩

/-- So even the final theorem-4.9 boundary-root synthesis endpoint under an actual Tait coloring
does not universally force the boundary-support face-data annulus shell. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_twoTriangleAnnulusGraph
    [Fintype twoTriangleAnnulusGraph.edgeSet]
    [FiniteDimensional F2 (twoTriangleAnnulusGraph.edgeSet → Color)] :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary twoTriangleAnnulusGraph}
        (C : twoTriangleAnnulusGraph.EdgeColoring Color),
        IsTaitEdgeColoring twoTriangleAnnulusGraph C →
          Theorem49BoundaryRootSynthesis emb C →
            Nonempty (PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb) := by
  exact
    not_forall_nonempty_planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_exists_embedding_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_without_planarBoundaryAnnulusConstructionBoundarySupportFaceData
      (G := twoTriangleAnnulusGraph)
      exists_embedding_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_without_planarBoundaryAnnulusConstructionBoundarySupportFaceData_twoTriangleAnnulusGraph

/-- So even the final theorem-4.9 boundary-root synthesis endpoint under an actual Tait coloring
does not universally force the face-partition annulus shell. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusConstructionFacePartitionData_of_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_twoTriangleAnnulusGraph
    [Fintype twoTriangleAnnulusGraph.edgeSet]
    [FiniteDimensional F2 (twoTriangleAnnulusGraph.edgeSet → Color)] :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary twoTriangleAnnulusGraph}
        (C : twoTriangleAnnulusGraph.EdgeColoring Color),
        IsTaitEdgeColoring twoTriangleAnnulusGraph C →
          Theorem49BoundaryRootSynthesis emb C →
            Nonempty (PlanarBoundaryAnnulusConstructionFacePartitionData emb) := by
  exact
    not_forall_nonempty_planarBoundaryAnnulusConstructionFacePartitionData_of_exists_embedding_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_without_planarBoundaryAnnulusConstructionFacePartitionData
      (G := twoTriangleAnnulusGraph)
      exists_embedding_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_without_planarBoundaryAnnulusConstructionFacePartitionData_twoTriangleAnnulusGraph

/-- So even the final theorem-4.9 boundary-root synthesis endpoint under an actual Tait coloring
does not universally force the face-layer annulus shell. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_twoTriangleAnnulusGraph
    [Fintype twoTriangleAnnulusGraph.edgeSet]
    [FiniteDimensional F2 (twoTriangleAnnulusGraph.edgeSet → Color)] :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary twoTriangleAnnulusGraph}
        (C : twoTriangleAnnulusGraph.EdgeColoring Color),
        IsTaitEdgeColoring twoTriangleAnnulusGraph C →
          Theorem49BoundaryRootSynthesis emb C →
            Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb) := by
  exact
    not_forall_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_exists_embedding_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_without_planarBoundaryAnnulusConstructionFaceLayerData
      (G := twoTriangleAnnulusGraph)
      exists_embedding_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_without_planarBoundaryAnnulusConstructionFaceLayerData_twoTriangleAnnulusGraph

/-- So even the final theorem-4.9 boundary-root synthesis endpoint under an actual Tait coloring
does not universally force the positive-frontier annulus-construction shell. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusConstructionPositiveFrontierData_of_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_twoTriangleAnnulusGraph
    [Fintype twoTriangleAnnulusGraph.edgeSet]
    [FiniteDimensional F2 (twoTriangleAnnulusGraph.edgeSet → Color)] :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary twoTriangleAnnulusGraph}
        (C : twoTriangleAnnulusGraph.EdgeColoring Color),
        IsTaitEdgeColoring twoTriangleAnnulusGraph C →
          Theorem49BoundaryRootSynthesis emb C →
            Nonempty (PlanarBoundaryAnnulusConstructionPositiveFrontierData emb) := by
  exact
    not_forall_nonempty_planarBoundaryAnnulusConstructionPositiveFrontierData_of_exists_embedding_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_without_planarBoundaryAnnulusConstructionPositiveFrontierData
      (G := twoTriangleAnnulusGraph)
      exists_embedding_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_without_planarBoundaryAnnulusConstructionPositiveFrontierData_twoTriangleAnnulusGraph

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

/-- The same exact-v23 two-triangle benchmark reaches the residual face-peel witness surface on
the actual exact one-collar successor-cycle boundary-order shell as well. -/
theorem
    twoTriangle_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_nonempty_residualBoundaryLayerFacePeelWitnessData
    :
    ∃ _boundaryData :
        PlanarBoundaryAnnulusBoundaryReachabilityData twoTriangleAnnulusEmbedding,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData twoTriangleAnnulusEmbedding,
        (∀ f : AmbientFace twoTriangleAnnulusEmbedding.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData twoTriangleAnnulusEmbedding,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              twoTriangleAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData) ∧
          IsTaitEdgeColoring twoTriangleAnnulusGraph twoTriangleTaitEdgeColoring ∧
          Nonempty
            (V23ResidualBoundaryInitialState twoTriangleTaitEdgeColoring red blue
              (twoTriangleAnnulusEmbedding.faceBoundary twoTriangleOuterFace.1)) ∧
          Nonempty
            (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData
              twoTriangleAnnulusEmbedding) := by
  have hcurrent :
      ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData twoTriangleAnnulusEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            twoTriangleAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData := by
    let source : PlanarBoundaryClosedWalkAnnulusBoundarySource twoTriangleAnnulusEmbedding :=
      PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        twoTriangleAnnulusBoundaryReachabilityData
        twoTriangleDartSuccessorCycleGeometry
        twoTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
    rcases exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource source with
      ⟨data, hnum, hboundary⟩
    exact ⟨data, hnum, by
      simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
        hboundary⟩
  exact
    ⟨twoTriangleAnnulusBoundaryReachabilityData,
      twoTriangleDartSuccessorCycleGeometry,
      twoTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      hcurrent,
      twoTriangleTaitEdgeColoring_isTait,
      nonempty_twoTriangleOuterFace_v23ResidualBoundaryInitialState,
      nonempty_twoTriangleClosedWalkSourceResidualBoundaryLayerFacePeelWitnessData⟩

/-- On the same live exact one-collar/v23 successor-cycle shell, the positive two-triangle
benchmark already carries both a residual/current-boundary witness and the full theorem-4.9
synthesis endpoint on the same embedding. -/
theorem
    twoTriangle_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_nonempty_residualBoundaryLayerFacePeelWitnessData
    [Fintype twoTriangleAnnulusGraph.edgeSet]
    [FiniteDimensional F2 (twoTriangleAnnulusGraph.edgeSet → Color)] :
    ∃ _boundaryData :
        PlanarBoundaryAnnulusBoundaryReachabilityData twoTriangleAnnulusEmbedding,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData twoTriangleAnnulusEmbedding,
        (∀ f : AmbientFace twoTriangleAnnulusEmbedding.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData twoTriangleAnnulusEmbedding,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              twoTriangleAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData) ∧
          IsTaitEdgeColoring twoTriangleAnnulusGraph twoTriangleTaitEdgeColoring ∧
          Nonempty
            (V23ResidualBoundaryInitialState twoTriangleTaitEdgeColoring red blue
              (twoTriangleAnnulusEmbedding.faceBoundary twoTriangleOuterFace.1)) ∧
          Theorem49BoundaryRootSynthesis
            twoTriangleAnnulusEmbedding twoTriangleTaitEdgeColoring ∧
          Nonempty
            (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData
              twoTriangleAnnulusEmbedding) := by
  rcases
      twoTriangle_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_nonempty_residualBoundaryLayerFacePeelWitnessData with
    ⟨boundaryData, dartCycles, hArc, hCurrent, hTait, hv23, hResidual⟩
  exact
    ⟨boundaryData,
      dartCycles,
      hArc,
      hCurrent,
      hTait,
      hv23,
      theorem49BoundaryRootSynthesis_twoTriangleAnnulusEmbedding_for_explicitTaitColoring_via_noInteriorParentRoute,
      hResidual⟩

/-- The same degenerate exact-v23 successor-cycle shell cannot support an unblocked interior
endpoint: the two-triangle benchmark still has empty interior-edge support on that embedding. -/
theorem not_hasUnblockedInteriorEndpoint_twoTriangleAnnulusEmbedding :
    ¬ HasUnblockedInteriorEndpoint twoTriangleAnnulusEmbedding := by
  exact
    not_hasUnblockedInteriorEndpoint_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsNoInteriorEdges
      twoTriangleAnnulusBoundaryReachabilityData
      twoTriangleDartSuccessorCycleGeometry
      twoTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
      rootSetCovers_twoTriangleAnnulusBoundaryFaceRoots
      rootSetSeparated_twoTriangleAnnulusBoundaryFaceRoots
      twoTriangleAnnulus_interiorEdgeSupport_eq_empty

/-- Equivalently, the exact-v23 two-triangle benchmark has no purified selected-boundary
interior-edge endpoint carrier on the same embedding, so the positive projected-geometry lane
cannot even start from this residual witness. -/
theorem not_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_twoTriangleAnnulusEmbedding :
    ¬ (selectedBoundaryInteriorEdgeEndpointVertices twoTriangleAnnulusEmbedding).Nonempty := by
  exact
    not_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsNoInteriorEdges
      twoTriangleAnnulusBoundaryReachabilityData
      twoTriangleDartSuccessorCycleGeometry
      twoTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
      rootSetCovers_twoTriangleAnnulusBoundaryFaceRoots
      rootSetSeparated_twoTriangleAnnulusBoundaryFaceRoots
      twoTriangleAnnulus_interiorEdgeSupport_eq_empty

/-- So no coloring can put the exact-v23 two-triangle residual benchmark into the projected
nonempty theorem-4.9 endpoint itself: the selected-boundary purification has already removed every
possible endpoint carrier on this embedding. -/
theorem not_theorem49BoundaryRootNonemptyProjectedSynthesis_twoTriangle
    [Fintype twoTriangleAnnulusGraph.edgeSet]
    [FiniteDimensional F2 (twoTriangleAnnulusGraph.edgeSet → Color)]
    (C0 : twoTriangleAnnulusGraph.EdgeColoring Color) :
    ¬ Theorem49BoundaryRootNonemptyProjectedSynthesis twoTriangleAnnulusEmbedding C0 := by
  intro h
  exact
    not_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_twoTriangleAnnulusEmbedding
      h.nonemptySynthesis.carrier_nonempty

/-- So although the exact-v23 two-triangle benchmark reaches the residual/current-boundary
witness surface itself, it still cannot inhabit the residual positive projected-geometry
package on that same embedding because the required purified carrier is absent. -/
theorem not_theorem49ResidualBoundaryPositiveProjectedGeometryOn_twoTriangle :
    ¬ Theorem49ResidualBoundaryPositiveProjectedGeometryOn twoTriangleAnnulusEmbedding := by
  rintro ⟨_data, hCarrier⟩
  exact not_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_twoTriangleAnnulusEmbedding hCarrier

/-- The same carrier obstruction also blocks the stronger finite-collar replacement-positive
package on the degenerate two-triangle benchmark. -/
theorem not_theorem49CollarLayerPositiveProjectedGeometryOn_twoTriangle :
    ¬ Theorem49CollarLayerPositiveProjectedGeometryOn twoTriangleAnnulusEmbedding := by
  rintro ⟨_data, hCarrier⟩
  exact not_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_twoTriangleAnnulusEmbedding hCarrier

/-- The height-ordered replacement-positive package is impossible for the same reason on this
benchmark: there is no surviving selected-boundary interior endpoint carrier to pair with any
witness-cover data. -/
theorem not_theorem49HeightOrderedPositiveProjectedGeometryOn_twoTriangle :
    ¬ Theorem49HeightOrderedPositiveProjectedGeometryOn twoTriangleAnnulusEmbedding := by
  rintro ⟨_data, hCarrier⟩
  exact not_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_twoTriangleAnnulusEmbedding hCarrier

/-- The same carrier obstruction also blocks the route-facing honest closed-walk annulus-collar
replacement-positive package on this exact-v23 benchmark. -/
theorem not_theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_twoTriangle :
    ¬ Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn
      twoTriangleAnnulusEmbedding := by
  intro geom
  exact
    not_theorem49CollarLayerPositiveProjectedGeometryOn_twoTriangle
      (theorem49CollarLayerPositiveProjectedGeometryOn_of_closedWalkAnnulusCollarPositiveProjectedGeometryOn
        geom)

/-- The same carrier obstruction also blocks the route-facing successor-cycle annulus-collar
replacement-positive package on this exact-v23 benchmark. -/
theorem not_theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn_twoTriangle :
    ¬ Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn
      twoTriangleAnnulusEmbedding := by
  intro geom
  exact
    not_theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_twoTriangle
      (theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_of_successorCycleAnnulusCollarPositiveProjectedGeometryOn
        geom)

/-- Lean-visible blocker on the exact one-collar/v23 two-triangle shell: the benchmark does
reach residual/current-boundary witness data on the actual successor-cycle boundary-order
interface, but it still has no purified endpoint carrier and therefore no residual, collar-layer,
or height-ordered positive projected geometry on that same embedding. -/
theorem
    twoTriangle_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_nonempty_residualBoundaryLayerFacePeelWitnessData_without_any_positiveProjectedGeometryOn
    :
    ∃ _boundaryData :
        PlanarBoundaryAnnulusBoundaryReachabilityData twoTriangleAnnulusEmbedding,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData twoTriangleAnnulusEmbedding,
        (∀ f : AmbientFace twoTriangleAnnulusEmbedding.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData twoTriangleAnnulusEmbedding,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              twoTriangleAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData) ∧
          IsTaitEdgeColoring twoTriangleAnnulusGraph twoTriangleTaitEdgeColoring ∧
          Nonempty
            (V23ResidualBoundaryInitialState twoTriangleTaitEdgeColoring red blue
              (twoTriangleAnnulusEmbedding.faceBoundary twoTriangleOuterFace.1)) ∧
          Nonempty
            (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData
              twoTriangleAnnulusEmbedding) ∧
          ¬ HasUnblockedInteriorEndpoint twoTriangleAnnulusEmbedding ∧
          ¬ (selectedBoundaryInteriorEdgeEndpointVertices
                twoTriangleAnnulusEmbedding).Nonempty ∧
          ¬ Theorem49ResidualBoundaryPositiveProjectedGeometryOn
                twoTriangleAnnulusEmbedding ∧
          ¬ Theorem49CollarLayerPositiveProjectedGeometryOn
                twoTriangleAnnulusEmbedding ∧
          ¬ Theorem49HeightOrderedPositiveProjectedGeometryOn
                twoTriangleAnnulusEmbedding := by
  rcases
      twoTriangle_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_nonempty_residualBoundaryLayerFacePeelWitnessData with
    ⟨boundaryData, dartCycles, hArc, hCurrent, hTait, hv23, hResidual⟩
  exact
    ⟨boundaryData,
      dartCycles,
      hArc,
      hCurrent,
      hTait,
      hv23,
      hResidual,
      not_hasUnblockedInteriorEndpoint_twoTriangleAnnulusEmbedding,
      not_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_twoTriangleAnnulusEmbedding,
      not_theorem49ResidualBoundaryPositiveProjectedGeometryOn_twoTriangle,
      not_theorem49CollarLayerPositiveProjectedGeometryOn_twoTriangle,
      not_theorem49HeightOrderedPositiveProjectedGeometryOn_twoTriangle⟩

/-- Stronger exact-shell blocker on the same positive benchmark: even after adjoining the full
theorem-4.9 synthesis endpoint to the exact one-collar residual witness package, the live
two-triangle shell still cannot inhabit any current positive projected-geometry route because
the purified endpoint carrier is absent. -/
theorem
    twoTriangle_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_nonempty_residualBoundaryLayerFacePeelWitnessData_without_any_positiveProjectedGeometryOn
    [Fintype twoTriangleAnnulusGraph.edgeSet]
    [FiniteDimensional F2 (twoTriangleAnnulusGraph.edgeSet → Color)] :
    ∃ _boundaryData :
        PlanarBoundaryAnnulusBoundaryReachabilityData twoTriangleAnnulusEmbedding,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData twoTriangleAnnulusEmbedding,
        (∀ f : AmbientFace twoTriangleAnnulusEmbedding.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData twoTriangleAnnulusEmbedding,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              twoTriangleAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData) ∧
          IsTaitEdgeColoring twoTriangleAnnulusGraph twoTriangleTaitEdgeColoring ∧
          Nonempty
            (V23ResidualBoundaryInitialState twoTriangleTaitEdgeColoring red blue
              (twoTriangleAnnulusEmbedding.faceBoundary twoTriangleOuterFace.1)) ∧
          Theorem49BoundaryRootSynthesis
            twoTriangleAnnulusEmbedding twoTriangleTaitEdgeColoring ∧
          Nonempty
            (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData
              twoTriangleAnnulusEmbedding) ∧
          ¬ HasUnblockedInteriorEndpoint twoTriangleAnnulusEmbedding ∧
          ¬ (selectedBoundaryInteriorEdgeEndpointVertices
                twoTriangleAnnulusEmbedding).Nonempty ∧
          ¬ Theorem49ResidualBoundaryPositiveProjectedGeometryOn
                twoTriangleAnnulusEmbedding ∧
          ¬ Theorem49CollarLayerPositiveProjectedGeometryOn
                twoTriangleAnnulusEmbedding ∧
          ¬ Theorem49HeightOrderedPositiveProjectedGeometryOn
                twoTriangleAnnulusEmbedding := by
  rcases
      twoTriangle_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_nonempty_residualBoundaryLayerFacePeelWitnessData with
    ⟨boundaryData, dartCycles, hArc, hCurrent, hTait, hv23, hSynth, hResidual⟩
  exact
    ⟨boundaryData,
      dartCycles,
      hArc,
      hCurrent,
      hTait,
      hv23,
      hSynth,
      hResidual,
      not_hasUnblockedInteriorEndpoint_twoTriangleAnnulusEmbedding,
      not_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_twoTriangleAnnulusEmbedding,
      not_theorem49ResidualBoundaryPositiveProjectedGeometryOn_twoTriangle,
      not_theorem49CollarLayerPositiveProjectedGeometryOn_twoTriangle,
      not_theorem49HeightOrderedPositiveProjectedGeometryOn_twoTriangle⟩

/-- The same exact-v23 successor-cycle benchmark is already strong enough to make the sharper
endpoint failure explicit: even after adjoining full theorem-4.9 synthesis to the same
residual-layer witness shell, the projected nonempty theorem-4.9 endpoint still fails on that
embedding because the purified carrier remains empty. -/
theorem
    twoTriangle_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_nonempty_residualBoundaryLayerFacePeelWitnessData_without_theorem49BoundaryRootNonemptyProjectedSynthesis
    [Fintype twoTriangleAnnulusGraph.edgeSet]
    [FiniteDimensional F2 (twoTriangleAnnulusGraph.edgeSet → Color)] :
    ∃ _boundaryData :
        PlanarBoundaryAnnulusBoundaryReachabilityData twoTriangleAnnulusEmbedding,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData twoTriangleAnnulusEmbedding,
        (∀ f : AmbientFace twoTriangleAnnulusEmbedding.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData twoTriangleAnnulusEmbedding,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              twoTriangleAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData) ∧
          IsTaitEdgeColoring twoTriangleAnnulusGraph twoTriangleTaitEdgeColoring ∧
          Nonempty
            (V23ResidualBoundaryInitialState twoTriangleTaitEdgeColoring red blue
              (twoTriangleAnnulusEmbedding.faceBoundary twoTriangleOuterFace.1)) ∧
          Theorem49BoundaryRootSynthesis
            twoTriangleAnnulusEmbedding twoTriangleTaitEdgeColoring ∧
          Nonempty
            (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData
              twoTriangleAnnulusEmbedding) ∧
          ¬ Theorem49BoundaryRootNonemptyProjectedSynthesis
                twoTriangleAnnulusEmbedding twoTriangleTaitEdgeColoring := by
  rcases
      twoTriangle_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_nonempty_residualBoundaryLayerFacePeelWitnessData with
    ⟨boundaryData, dartCycles, hArc, hCurrent, hTait, hv23, hSynth, hResidual⟩
  exact
    ⟨boundaryData,
      dartCycles,
      hArc,
      hCurrent,
      hTait,
      hv23,
      hSynth,
      hResidual,
      not_theorem49BoundaryRootNonemptyProjectedSynthesis_twoTriangle
        twoTriangleTaitEdgeColoring⟩

/-- Stronger exact-shell blocker on the same positive benchmark: even after adjoining exact
one-collar current-boundary data, the exact v23 seed, and a residual-boundary layer witness, the
live successor-cycle shell still cannot inhabit any of the current replacement-positive targets
because the purified endpoint carrier is absent. -/
theorem
    twoTriangle_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_nonempty_residualBoundaryLayerFacePeelWitnessData_without_any_replacementPositiveProjectedGeometryOn
    :
    ∃ _boundaryData :
        PlanarBoundaryAnnulusBoundaryReachabilityData twoTriangleAnnulusEmbedding,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData twoTriangleAnnulusEmbedding,
        (∀ f : AmbientFace twoTriangleAnnulusEmbedding.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData twoTriangleAnnulusEmbedding,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              twoTriangleAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData) ∧
          IsTaitEdgeColoring twoTriangleAnnulusGraph twoTriangleTaitEdgeColoring ∧
          Nonempty
            (V23ResidualBoundaryInitialState twoTriangleTaitEdgeColoring red blue
              (twoTriangleAnnulusEmbedding.faceBoundary twoTriangleOuterFace.1)) ∧
          Nonempty
            (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData
              twoTriangleAnnulusEmbedding) ∧
          ¬ Theorem49HeightOrderedPositiveProjectedGeometryOn
                twoTriangleAnnulusEmbedding ∧
          ¬ Theorem49CollarLayerPositiveProjectedGeometryOn
                twoTriangleAnnulusEmbedding ∧
          ¬ Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn
                twoTriangleAnnulusEmbedding ∧
          ¬ Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn
                twoTriangleAnnulusEmbedding := by
  rcases
      twoTriangle_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_nonempty_residualBoundaryLayerFacePeelWitnessData with
    ⟨boundaryData, dartCycles, hArc, hCurrent, hTait, hv23, hResidual⟩
  exact
    ⟨boundaryData,
      dartCycles,
      hArc,
      hCurrent,
      hTait,
      hv23,
      hResidual,
      not_theorem49HeightOrderedPositiveProjectedGeometryOn_twoTriangle,
      not_theorem49CollarLayerPositiveProjectedGeometryOn_twoTriangle,
      not_theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_twoTriangle,
      not_theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn_twoTriangle⟩

/-- The same replacement-positive blocker survives even after adjoining the full theorem-4.9
synthesis endpoint to that exact successor-cycle one-collar residual shell. -/
theorem
    twoTriangle_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_nonempty_residualBoundaryLayerFacePeelWitnessData_without_any_replacementPositiveProjectedGeometryOn
    [Fintype twoTriangleAnnulusGraph.edgeSet]
    [FiniteDimensional F2 (twoTriangleAnnulusGraph.edgeSet → Color)] :
    ∃ _boundaryData :
        PlanarBoundaryAnnulusBoundaryReachabilityData twoTriangleAnnulusEmbedding,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData twoTriangleAnnulusEmbedding,
        (∀ f : AmbientFace twoTriangleAnnulusEmbedding.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData twoTriangleAnnulusEmbedding,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              twoTriangleAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData) ∧
          IsTaitEdgeColoring twoTriangleAnnulusGraph twoTriangleTaitEdgeColoring ∧
          Nonempty
            (V23ResidualBoundaryInitialState twoTriangleTaitEdgeColoring red blue
              (twoTriangleAnnulusEmbedding.faceBoundary twoTriangleOuterFace.1)) ∧
          Theorem49BoundaryRootSynthesis
            twoTriangleAnnulusEmbedding twoTriangleTaitEdgeColoring ∧
          Nonempty
            (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData
              twoTriangleAnnulusEmbedding) ∧
          ¬ Theorem49HeightOrderedPositiveProjectedGeometryOn
                twoTriangleAnnulusEmbedding ∧
          ¬ Theorem49CollarLayerPositiveProjectedGeometryOn
                twoTriangleAnnulusEmbedding ∧
          ¬ Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn
                twoTriangleAnnulusEmbedding ∧
          ¬ Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn
                twoTriangleAnnulusEmbedding := by
  rcases
      twoTriangle_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_nonempty_residualBoundaryLayerFacePeelWitnessData with
    ⟨boundaryData, dartCycles, hArc, hCurrent, hTait, hv23, hSynth, hResidual⟩
  exact
    ⟨boundaryData,
      dartCycles,
      hArc,
      hCurrent,
      hTait,
      hv23,
      hSynth,
      hResidual,
      not_theorem49HeightOrderedPositiveProjectedGeometryOn_twoTriangle,
      not_theorem49CollarLayerPositiveProjectedGeometryOn_twoTriangle,
      not_theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_twoTriangle,
      not_theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn_twoTriangle⟩

/-- The positive exact-v23 two-triangle benchmark is no longer only a benchmark-local blocker.
Any claimed universal derivation from the exact successor-cycle one-collar residual shell plus a
same-embedding residual-boundary layer witness to one of the currently formalized positive
projected-geometry targets is false. -/
theorem
    not_forall_any_positiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_nonempty_residualBoundaryLayerFacePeelWitnessData_twoTriangle :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary twoTriangleAnnulusGraph,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) →
          ∀ C : twoTriangleAnnulusGraph.EdgeColoring Color,
            IsTaitEdgeColoring twoTriangleAnnulusGraph C →
            ∀ a b : Color,
              ∀ faceBoundary : Finset twoTriangleAnnulusGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) →
                Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb ∨
                  Theorem49CollarLayerPositiveProjectedGeometryOn emb ∨
                    Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  intro h
  rcases
      twoTriangle_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_nonempty_residualBoundaryLayerFacePeelWitnessData_without_any_positiveProjectedGeometryOn with
    ⟨boundaryData, dartCycles, hArc, _hCurrent, hTait, hv23, hResidual, _hNoEndpoint,
      _hNoCarrier, hNoResidual, hNoCollar, hNoHeight⟩
  have hCurrent' :
      ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData twoTriangleAnnulusEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            boundaryData.toPlanarBoundaryAnnulusBoundaryData := by
    let source : PlanarBoundaryClosedWalkAnnulusBoundarySource twoTriangleAnnulusEmbedding :=
      PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hArc
    rcases exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource source with
      ⟨data, hnum, hboundary⟩
    exact ⟨data, hnum, by
      simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
        hboundary⟩
  have hAny :=
    h twoTriangleAnnulusEmbedding boundaryData dartCycles hArc hCurrent'
      twoTriangleTaitEdgeColoring
      hTait red blue (twoTriangleAnnulusEmbedding.faceBoundary twoTriangleOuterFace.1) hv23
      hResidual
  rcases hAny with hResidualGeom | hRest
  · exact hNoResidual hResidualGeom
  · rcases hRest with hCollar | hHeight
    · exact hNoCollar hCollar
    · exact hNoHeight hHeight

/-- The same failed converse survives even after adjoining the full theorem-4.9 synthesis
endpoint to that exact successor-cycle one-collar residual shell. -/
theorem
    not_forall_any_positiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_nonempty_residualBoundaryLayerFacePeelWitnessData_twoTriangle
    [Fintype twoTriangleAnnulusGraph.edgeSet]
    [FiniteDimensional F2 (twoTriangleAnnulusGraph.edgeSet → Color)] :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary twoTriangleAnnulusGraph,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) →
          ∀ C : twoTriangleAnnulusGraph.EdgeColoring Color,
            IsTaitEdgeColoring twoTriangleAnnulusGraph C →
            ∀ a b : Color,
              ∀ faceBoundary : Finset twoTriangleAnnulusGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                Theorem49BoundaryRootSynthesis emb C →
                Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) →
                Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb ∨
                  Theorem49CollarLayerPositiveProjectedGeometryOn emb ∨
                    Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  intro h
  rcases
      twoTriangle_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_nonempty_residualBoundaryLayerFacePeelWitnessData_without_any_positiveProjectedGeometryOn with
    ⟨boundaryData, dartCycles, hArc, _hCurrent, hTait, hv23, hSynth, hResidual, _hNoEndpoint,
      _hNoCarrier, hNoResidual, hNoCollar, hNoHeight⟩
  have hCurrent' :
      ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData twoTriangleAnnulusEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            boundaryData.toPlanarBoundaryAnnulusBoundaryData := by
    let source : PlanarBoundaryClosedWalkAnnulusBoundarySource twoTriangleAnnulusEmbedding :=
      PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hArc
    rcases exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource source with
      ⟨data, hnum, hboundary⟩
    exact ⟨data, hnum, by
      simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
        hboundary⟩
  have hAny :=
    h twoTriangleAnnulusEmbedding boundaryData dartCycles hArc hCurrent'
      twoTriangleTaitEdgeColoring hTait red blue
      (twoTriangleAnnulusEmbedding.faceBoundary twoTriangleOuterFace.1) hv23 hSynth hResidual
  rcases hAny with hResidualGeom | hRest
  · exact hNoResidual hResidualGeom
  · rcases hRest with hCollar | hHeight
    · exact hNoCollar hCollar
    · exact hNoHeight hHeight

/-- The exact-v23 two-triangle benchmark also refutes any universal derivation from that same
successor-cycle residual-layer shell to the current route-facing replacement-positive targets. -/
theorem
    not_forall_any_replacementPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_nonempty_residualBoundaryLayerFacePeelWitnessData_twoTriangle :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary twoTriangleAnnulusGraph,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) →
          ∀ C : twoTriangleAnnulusGraph.EdgeColoring Color,
            IsTaitEdgeColoring twoTriangleAnnulusGraph C →
            ∀ a b : Color,
              ∀ faceBoundary : Finset twoTriangleAnnulusGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) →
                Theorem49HeightOrderedPositiveProjectedGeometryOn emb ∨
                  Theorem49CollarLayerPositiveProjectedGeometryOn emb ∨
                    Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb ∨
                      Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb := by
  intro h
  rcases
      twoTriangle_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_nonempty_residualBoundaryLayerFacePeelWitnessData_without_any_replacementPositiveProjectedGeometryOn with
    ⟨boundaryData, dartCycles, hArc, _hCurrent, hTait, hv23, hResidual, hNoHeight,
      hNoCollar, hNoClosedWalk, hNoSuccessor⟩
  have hCurrent' :
      ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData twoTriangleAnnulusEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            boundaryData.toPlanarBoundaryAnnulusBoundaryData := by
    let source : PlanarBoundaryClosedWalkAnnulusBoundarySource twoTriangleAnnulusEmbedding :=
      PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hArc
    rcases exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource source with
      ⟨data, hnum, hboundary⟩
    exact ⟨data, hnum, by
      simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
        hboundary⟩
  have hAny :=
    h twoTriangleAnnulusEmbedding boundaryData dartCycles hArc hCurrent'
      twoTriangleTaitEdgeColoring hTait red blue
      (twoTriangleAnnulusEmbedding.faceBoundary twoTriangleOuterFace.1) hv23 hResidual
  rcases hAny with hHeight | hRest
  · exact hNoHeight hHeight
  · rcases hRest with hCollar | hRest
    · exact hNoCollar hCollar
    · rcases hRest with hClosedWalk | hSuccessor
      · exact hNoClosedWalk hClosedWalk
      · exact hNoSuccessor hSuccessor

/-- The same route-facing replacement-positive failed converse survives after adjoining the full
theorem-4.9 synthesis endpoint to that exact successor-cycle one-collar residual shell. -/
theorem
    not_forall_any_replacementPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_nonempty_residualBoundaryLayerFacePeelWitnessData_twoTriangle
    [Fintype twoTriangleAnnulusGraph.edgeSet]
    [FiniteDimensional F2 (twoTriangleAnnulusGraph.edgeSet → Color)] :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary twoTriangleAnnulusGraph,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) →
          ∀ C : twoTriangleAnnulusGraph.EdgeColoring Color,
            IsTaitEdgeColoring twoTriangleAnnulusGraph C →
            ∀ a b : Color,
              ∀ faceBoundary : Finset twoTriangleAnnulusGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                Theorem49BoundaryRootSynthesis emb C →
                Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) →
                Theorem49HeightOrderedPositiveProjectedGeometryOn emb ∨
                  Theorem49CollarLayerPositiveProjectedGeometryOn emb ∨
                    Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb ∨
                      Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb := by
  intro h
  rcases
      twoTriangle_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_nonempty_residualBoundaryLayerFacePeelWitnessData_without_any_replacementPositiveProjectedGeometryOn with
    ⟨boundaryData, dartCycles, hArc, _hCurrent, hTait, hv23, hSynth, hResidual, hNoHeight,
      hNoCollar, hNoClosedWalk, hNoSuccessor⟩
  have hCurrent' :
      ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData twoTriangleAnnulusEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            boundaryData.toPlanarBoundaryAnnulusBoundaryData := by
    let source : PlanarBoundaryClosedWalkAnnulusBoundarySource twoTriangleAnnulusEmbedding :=
      PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hArc
    rcases exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource source with
      ⟨data, hnum, hboundary⟩
    exact ⟨data, hnum, by
      simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
        hboundary⟩
  have hAny :=
    h twoTriangleAnnulusEmbedding boundaryData dartCycles hArc hCurrent'
      twoTriangleTaitEdgeColoring hTait red blue
      (twoTriangleAnnulusEmbedding.faceBoundary twoTriangleOuterFace.1) hv23 hSynth hResidual
  rcases hAny with hHeight | hRest
  · exact hNoHeight hHeight
  · rcases hRest with hCollar | hRest
    · exact hNoCollar hCollar
    · rcases hRest with hClosedWalk | hSuccessor
      · exact hNoClosedWalk hClosedWalk
      · exact hNoSuccessor hSuccessor

/-- The same exact-v23 two-triangle benchmark also refutes any universal derivation from that
successor-cycle residual-layer shell plus full theorem-4.9 synthesis to the projected nonempty
theorem-4.9 endpoint itself. -/
theorem
    not_forall_theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_nonempty_residualBoundaryLayerFacePeelWitnessData_twoTriangle
    [Fintype twoTriangleAnnulusGraph.edgeSet]
    [FiniteDimensional F2 (twoTriangleAnnulusGraph.edgeSet → Color)] :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary twoTriangleAnnulusGraph,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) →
          ∀ C : twoTriangleAnnulusGraph.EdgeColoring Color,
            IsTaitEdgeColoring twoTriangleAnnulusGraph C →
            ∀ a b : Color,
              ∀ faceBoundary : Finset twoTriangleAnnulusGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                Theorem49BoundaryRootSynthesis emb C →
                Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) →
                Theorem49BoundaryRootNonemptyProjectedSynthesis emb C := by
  intro h
  rcases
      twoTriangle_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_nonempty_residualBoundaryLayerFacePeelWitnessData_without_theorem49BoundaryRootNonemptyProjectedSynthesis with
    ⟨boundaryData, dartCycles, hArc, _hCurrent, hTait, hv23, hSynth, hResidual, hNoProjected⟩
  have hCurrent' :
      ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData twoTriangleAnnulusEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            boundaryData.toPlanarBoundaryAnnulusBoundaryData := by
    let source : PlanarBoundaryClosedWalkAnnulusBoundarySource twoTriangleAnnulusEmbedding :=
      PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hArc
    rcases exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource source with
      ⟨data, hnum, hboundary⟩
    exact ⟨data, hnum, by
      simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
        hboundary⟩
  exact
    hNoProjected
      (h twoTriangleAnnulusEmbedding boundaryData dartCycles hArc hCurrent'
        twoTriangleTaitEdgeColoring hTait red blue
        (twoTriangleAnnulusEmbedding.faceBoundary twoTriangleOuterFace.1) hv23 hSynth hResidual)

/-- Any explicit same-embedding witness of the exact successor-cycle one-collar/v23 residual
shell together with a residual-boundary layer witness and simultaneous failure of the current
direct positive endpoints already refutes a universal derivation of that three-way positive
disjunction. -/
theorem
    not_forall_any_positiveProjectedGeometryOn_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_nonempty_residualBoundaryLayerFacePeelWitnessData
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : G.EdgeColoring Color,
          IsTaitEdgeColoring G C ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∧
                  ¬ Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49CollarLayerPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49HeightOrderedPositiveProjectedGeometryOn emb) :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary G,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) →
          ∀ C : G.EdgeColoring Color,
            IsTaitEdgeColoring G C →
            ∀ a b : Color,
              ∀ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) →
                Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb ∨
                  Theorem49CollarLayerPositiveProjectedGeometryOn emb ∨
                    Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  intro h
  rcases hWitness with
    ⟨emb, boundaryData, dartCycles, hBoundaryArc, hCurrent, C, hC, a, b, faceBoundary,
      hv23, hResidual, hNoResidual, hNoCollar, hNoHeight⟩
  rcases h emb boundaryData dartCycles hBoundaryArc hCurrent C hC a b faceBoundary hv23 hResidual with
    hResidual' | hRest
  · exact hNoResidual hResidual'
  · rcases hRest with hCollar | hHeight
    · exact hNoCollar hCollar
    · exact hNoHeight hHeight

/-- The same existential failed converse survives after adjoining the full theorem-4.9 synthesis
endpoint to that exact successor-cycle one-collar/v23 residual shell. -/
theorem
    not_forall_any_positiveProjectedGeometryOn_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_nonempty_residualBoundaryLayerFacePeelWitnessData
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : G.EdgeColoring Color,
          IsTaitEdgeColoring G C ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  Theorem49BoundaryRootSynthesis emb C ∧
                  Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∧
                  ¬ Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49CollarLayerPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49HeightOrderedPositiveProjectedGeometryOn emb) :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary G,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) →
          ∀ C : G.EdgeColoring Color,
            IsTaitEdgeColoring G C →
            ∀ a b : Color,
              ∀ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                Theorem49BoundaryRootSynthesis emb C →
                Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) →
                Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb ∨
                  Theorem49CollarLayerPositiveProjectedGeometryOn emb ∨
                    Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  intro h
  rcases hWitness with
    ⟨emb, boundaryData, dartCycles, hBoundaryArc, hCurrent, C, hC, a, b, faceBoundary, hv23,
      hSynth, hResidual, hNoResidual, hNoCollar, hNoHeight⟩
  rcases
      h emb boundaryData dartCycles hBoundaryArc hCurrent C hC a b faceBoundary hv23 hSynth
        hResidual with
    hResidual' | hRest
  · exact hNoResidual hResidual'
  · rcases hRest with hCollar | hHeight
    · exact hNoCollar hCollar
    · exact hNoHeight hHeight

/-- The same existential witness shape also refutes any universal derivation from that exact
successor-cycle one-collar/v23 residual shell to the current route-facing replacement-positive
targets. -/
theorem
    not_forall_any_replacementPositiveProjectedGeometryOn_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_nonempty_residualBoundaryLayerFacePeelWitnessData
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : G.EdgeColoring Color,
          IsTaitEdgeColoring G C ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∧
                  ¬ Theorem49HeightOrderedPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49CollarLayerPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb) :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary G,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) →
          ∀ C : G.EdgeColoring Color,
            IsTaitEdgeColoring G C →
            ∀ a b : Color,
              ∀ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) →
                Theorem49HeightOrderedPositiveProjectedGeometryOn emb ∨
                  Theorem49CollarLayerPositiveProjectedGeometryOn emb ∨
                    Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb ∨
                      Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb := by
  intro h
  rcases hWitness with
    ⟨emb, boundaryData, dartCycles, hBoundaryArc, hCurrent, C, hC, a, b, faceBoundary,
      hv23, hResidual, hNoHeight, hNoCollar, hNoClosedWalk, hNoSuccessor⟩
  rcases h emb boundaryData dartCycles hBoundaryArc hCurrent C hC a b faceBoundary hv23 hResidual with
    hHeight | hRest
  · exact hNoHeight hHeight
  · rcases hRest with hCollar | hRest
    · exact hNoCollar hCollar
    · rcases hRest with hClosedWalk | hSuccessor
      · exact hNoClosedWalk hClosedWalk
      · exact hNoSuccessor hSuccessor

/-- The same route-facing existential failed converse survives after adjoining the full
theorem-4.9 synthesis endpoint to that exact successor-cycle one-collar/v23 residual shell. -/
theorem
    not_forall_any_replacementPositiveProjectedGeometryOn_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_nonempty_residualBoundaryLayerFacePeelWitnessData
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : G.EdgeColoring Color,
          IsTaitEdgeColoring G C ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  Theorem49BoundaryRootSynthesis emb C ∧
                  Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∧
                  ¬ Theorem49HeightOrderedPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49CollarLayerPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb) :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary G,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) →
          ∀ C : G.EdgeColoring Color,
            IsTaitEdgeColoring G C →
            ∀ a b : Color,
              ∀ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                Theorem49BoundaryRootSynthesis emb C →
                Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) →
                Theorem49HeightOrderedPositiveProjectedGeometryOn emb ∨
                  Theorem49CollarLayerPositiveProjectedGeometryOn emb ∨
                    Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb ∨
                      Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb := by
  intro h
  rcases hWitness with
    ⟨emb, boundaryData, dartCycles, hBoundaryArc, hCurrent, C, hC, a, b, faceBoundary, hv23,
      hSynth, hResidual, hNoHeight, hNoCollar, hNoClosedWalk, hNoSuccessor⟩
  rcases
      h emb boundaryData dartCycles hBoundaryArc hCurrent C hC a b faceBoundary hv23 hSynth
        hResidual with
    hHeight | hRest
  · exact hNoHeight hHeight
  · rcases hRest with hCollar | hRest
    · exact hNoCollar hCollar
    · rcases hRest with hClosedWalk | hSuccessor
      · exact hNoClosedWalk hClosedWalk
      · exact hNoSuccessor hSuccessor

/-- Graph-level witness form of the same positive exact-v23 diagnosis on the live
successor-cycle selected-arc shell: one embedding of the two-triangle annulus graph already
has exact one-collar current-boundary data, a real residual-layer witness, and still fails the
current direct positive targets. -/
theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_nonempty_residualBoundaryLayerFacePeelWitnessData_without_any_positiveProjectedGeometryOn_twoTriangleAnnulusGraph
    :
    ∃ emb : PlaneEmbeddingWithBoundary twoTriangleAnnulusGraph,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : twoTriangleAnnulusGraph.EdgeColoring Color,
          IsTaitEdgeColoring twoTriangleAnnulusGraph C ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset twoTriangleAnnulusGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∧
                  ¬ Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49CollarLayerPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  exact
    ⟨twoTriangleAnnulusEmbedding,
      twoTriangleAnnulusBoundaryReachabilityData,
      twoTriangleDartSuccessorCycleGeometry,
      twoTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        twoTriangleClosedWalkAnnulusBoundarySource,
      twoTriangleTaitEdgeColoring,
      twoTriangleTaitEdgeColoring_isTait,
      red, blue,
      twoTriangleAnnulusEmbedding.faceBoundary twoTriangleOuterFace.1,
      nonempty_twoTriangleOuterFace_v23ResidualBoundaryInitialState,
      nonempty_twoTriangleClosedWalkSourceResidualBoundaryLayerFacePeelWitnessData,
      not_theorem49ResidualBoundaryPositiveProjectedGeometryOn_twoTriangle,
      not_theorem49CollarLayerPositiveProjectedGeometryOn_twoTriangle,
      not_theorem49HeightOrderedPositiveProjectedGeometryOn_twoTriangle⟩

/-- The same graph-level successor-cycle witness survives after adjoining full theorem-4.9
synthesis to that exact one-collar/v23 residual shell. -/
theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_nonempty_residualBoundaryLayerFacePeelWitnessData_without_any_positiveProjectedGeometryOn_twoTriangleAnnulusGraph
    [Fintype twoTriangleAnnulusGraph.edgeSet]
    [FiniteDimensional F2 (twoTriangleAnnulusGraph.edgeSet → Color)] :
    ∃ emb : PlaneEmbeddingWithBoundary twoTriangleAnnulusGraph,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : twoTriangleAnnulusGraph.EdgeColoring Color,
          IsTaitEdgeColoring twoTriangleAnnulusGraph C ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset twoTriangleAnnulusGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  Theorem49BoundaryRootSynthesis emb C ∧
                  Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∧
                  ¬ Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49CollarLayerPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  exact
    ⟨twoTriangleAnnulusEmbedding,
      twoTriangleAnnulusBoundaryReachabilityData,
      twoTriangleDartSuccessorCycleGeometry,
      twoTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        twoTriangleClosedWalkAnnulusBoundarySource,
      twoTriangleTaitEdgeColoring,
      twoTriangleTaitEdgeColoring_isTait,
      red, blue,
      twoTriangleAnnulusEmbedding.faceBoundary twoTriangleOuterFace.1,
      nonempty_twoTriangleOuterFace_v23ResidualBoundaryInitialState,
      theorem49BoundaryRootSynthesis_twoTriangleAnnulusEmbedding_for_explicitTaitColoring_via_noInteriorParentRoute,
      nonempty_twoTriangleClosedWalkSourceResidualBoundaryLayerFacePeelWitnessData,
      not_theorem49ResidualBoundaryPositiveProjectedGeometryOn_twoTriangle,
      not_theorem49CollarLayerPositiveProjectedGeometryOn_twoTriangle,
      not_theorem49HeightOrderedPositiveProjectedGeometryOn_twoTriangle⟩

/-- Graph-level witness form of the same route-facing replacement-positive obstruction on the live
successor-cycle exact-v23 residual shell. -/
theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_nonempty_residualBoundaryLayerFacePeelWitnessData_without_any_replacementPositiveProjectedGeometryOn_twoTriangleAnnulusGraph
    :
    ∃ emb : PlaneEmbeddingWithBoundary twoTriangleAnnulusGraph,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : twoTriangleAnnulusGraph.EdgeColoring Color,
          IsTaitEdgeColoring twoTriangleAnnulusGraph C ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset twoTriangleAnnulusGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∧
                  ¬ Theorem49HeightOrderedPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49CollarLayerPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb := by
  exact
    ⟨twoTriangleAnnulusEmbedding,
      twoTriangleAnnulusBoundaryReachabilityData,
      twoTriangleDartSuccessorCycleGeometry,
      twoTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        twoTriangleClosedWalkAnnulusBoundarySource,
      twoTriangleTaitEdgeColoring,
      twoTriangleTaitEdgeColoring_isTait,
      red, blue,
      twoTriangleAnnulusEmbedding.faceBoundary twoTriangleOuterFace.1,
      nonempty_twoTriangleOuterFace_v23ResidualBoundaryInitialState,
      nonempty_twoTriangleClosedWalkSourceResidualBoundaryLayerFacePeelWitnessData,
      not_theorem49HeightOrderedPositiveProjectedGeometryOn_twoTriangle,
      not_theorem49CollarLayerPositiveProjectedGeometryOn_twoTriangle,
      not_theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_twoTriangle,
      not_theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn_twoTriangle⟩

/-- The same graph-level successor-cycle replacement-positive obstruction persists after adjoining
full theorem-4.9 synthesis on that exact one-collar/v23 residual shell. -/
theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_nonempty_residualBoundaryLayerFacePeelWitnessData_without_any_replacementPositiveProjectedGeometryOn_twoTriangleAnnulusGraph
    [Fintype twoTriangleAnnulusGraph.edgeSet]
    [FiniteDimensional F2 (twoTriangleAnnulusGraph.edgeSet → Color)] :
    ∃ emb : PlaneEmbeddingWithBoundary twoTriangleAnnulusGraph,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : twoTriangleAnnulusGraph.EdgeColoring Color,
          IsTaitEdgeColoring twoTriangleAnnulusGraph C ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset twoTriangleAnnulusGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  Theorem49BoundaryRootSynthesis emb C ∧
                  Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∧
                  ¬ Theorem49HeightOrderedPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49CollarLayerPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb := by
  exact
    ⟨twoTriangleAnnulusEmbedding,
      twoTriangleAnnulusBoundaryReachabilityData,
      twoTriangleDartSuccessorCycleGeometry,
      twoTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        twoTriangleClosedWalkAnnulusBoundarySource,
      twoTriangleTaitEdgeColoring,
      twoTriangleTaitEdgeColoring_isTait,
      red, blue,
      twoTriangleAnnulusEmbedding.faceBoundary twoTriangleOuterFace.1,
      nonempty_twoTriangleOuterFace_v23ResidualBoundaryInitialState,
      theorem49BoundaryRootSynthesis_twoTriangleAnnulusEmbedding_for_explicitTaitColoring_via_noInteriorParentRoute,
      nonempty_twoTriangleClosedWalkSourceResidualBoundaryLayerFacePeelWitnessData,
      not_theorem49HeightOrderedPositiveProjectedGeometryOn_twoTriangle,
      not_theorem49CollarLayerPositiveProjectedGeometryOn_twoTriangle,
      not_theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_twoTriangle,
      not_theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn_twoTriangle⟩

/-- Graph-level live-shell packaging of the same sharper endpoint obstruction: one embedding of
the two-triangle annulus graph already has exact one-collar current-boundary data, a real
residual-layer witness, and full theorem-4.9 synthesis on the live successor-cycle shell while
still failing the projected nonempty theorem-4.9 endpoint itself. -/
theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_nonempty_residualBoundaryLayerFacePeelWitnessData_without_theorem49BoundaryRootNonemptyProjectedSynthesis_twoTriangleAnnulusGraph
    [Fintype twoTriangleAnnulusGraph.edgeSet]
    [FiniteDimensional F2 (twoTriangleAnnulusGraph.edgeSet → Color)] :
    ∃ emb : PlaneEmbeddingWithBoundary twoTriangleAnnulusGraph,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : twoTriangleAnnulusGraph.EdgeColoring Color,
          IsTaitEdgeColoring twoTriangleAnnulusGraph C ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset twoTriangleAnnulusGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  Theorem49BoundaryRootSynthesis emb C ∧
                  Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∧
                  ¬ Theorem49BoundaryRootNonemptyProjectedSynthesis emb C := by
  exact
    ⟨twoTriangleAnnulusEmbedding,
      twoTriangleAnnulusBoundaryReachabilityData,
      twoTriangleDartSuccessorCycleGeometry,
      twoTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        twoTriangleClosedWalkAnnulusBoundarySource,
      twoTriangleTaitEdgeColoring,
      twoTriangleTaitEdgeColoring_isTait,
      red, blue,
      twoTriangleAnnulusEmbedding.faceBoundary twoTriangleOuterFace.1,
      nonempty_twoTriangleOuterFace_v23ResidualBoundaryInitialState,
      theorem49BoundaryRootSynthesis_twoTriangleAnnulusEmbedding_for_explicitTaitColoring_via_noInteriorParentRoute,
      nonempty_twoTriangleClosedWalkSourceResidualBoundaryLayerFacePeelWitnessData,
      not_theorem49BoundaryRootNonemptyProjectedSynthesis_twoTriangle
        twoTriangleTaitEdgeColoring⟩

/-- The same graph-level witness already refutes any universal derivation from the exact
successor-cycle one-collar/v23 residual shell plus full theorem-4.9 synthesis to the projected
nonempty theorem-4.9 endpoint itself. -/
theorem
    not_forall_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_nonempty_residualBoundaryLayerFacePeelWitnessData
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : G.EdgeColoring Color,
          IsTaitEdgeColoring G C ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  Theorem49BoundaryRootSynthesis emb C ∧
                  Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∧
                  ¬ Theorem49BoundaryRootNonemptyProjectedSynthesis emb C) :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary G,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) →
          ∀ C : G.EdgeColoring Color,
            IsTaitEdgeColoring G C →
            ∀ a b : Color,
              ∀ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                Theorem49BoundaryRootSynthesis emb C →
                Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) →
                Theorem49BoundaryRootNonemptyProjectedSynthesis emb C := by
  intro h
  rcases hWitness with
    ⟨emb, boundaryData, dartCycles, hBoundaryArc, hCurrent, C, hC, a, b, faceBoundary, hv23,
      hSynth, hResidual, hNoProjected⟩
  exact
    hNoProjected
      (h emb boundaryData dartCycles hBoundaryArc hCurrent C hC a b faceBoundary hv23 hSynth
        hResidual)

/-- Honest closed-walk exact-v23 residual-layer benchmark on the two-triangle source: even after
adding exact one-collar current-boundary data, the same embedding carries a real residual-layer
witness while failing the current direct positive targets. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_nonempty_residualBoundaryLayerFacePeelWitnessData_without_any_positiveProjectedGeometryOn_twoTriangleAnnulusGraph
    :
    ∃ emb : PlaneEmbeddingWithBoundary twoTriangleAnnulusGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        (∃ C : twoTriangleAnnulusGraph.EdgeColoring Color,
          IsTaitEdgeColoring twoTriangleAnnulusGraph C ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset twoTriangleAnnulusGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∧
                  ¬ Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49CollarLayerPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49HeightOrderedPositiveProjectedGeometryOn emb) := by
  exact
    ⟨twoTriangleAnnulusEmbedding,
      twoTriangleClosedWalkAnnulusBoundarySource,
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        twoTriangleClosedWalkAnnulusBoundarySource,
      twoTriangleTaitEdgeColoring,
      twoTriangleTaitEdgeColoring_isTait,
      red, blue,
      (twoTriangleAnnulusEmbedding.faceBoundary twoTriangleOuterFace.1),
      nonempty_twoTriangleOuterFace_v23ResidualBoundaryInitialState,
      nonempty_twoTriangleClosedWalkSourceResidualBoundaryLayerFacePeelWitnessData,
      not_theorem49ResidualBoundaryPositiveProjectedGeometryOn_twoTriangle,
      not_theorem49CollarLayerPositiveProjectedGeometryOn_twoTriangle,
      not_theorem49HeightOrderedPositiveProjectedGeometryOn_twoTriangle⟩

/-- The same honest-source exact-v23 residual-layer obstruction survives after adjoining full
theorem-4.9 synthesis on the same embedding. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_nonempty_residualBoundaryLayerFacePeelWitnessData_without_any_positiveProjectedGeometryOn_twoTriangleAnnulusGraph
    [Fintype twoTriangleAnnulusGraph.edgeSet]
    [FiniteDimensional F2 (twoTriangleAnnulusGraph.edgeSet → Color)] :
    ∃ emb : PlaneEmbeddingWithBoundary twoTriangleAnnulusGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        (∃ C : twoTriangleAnnulusGraph.EdgeColoring Color,
          IsTaitEdgeColoring twoTriangleAnnulusGraph C ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset twoTriangleAnnulusGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  Theorem49BoundaryRootSynthesis emb C ∧
                  Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∧
                  ¬ Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49CollarLayerPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49HeightOrderedPositiveProjectedGeometryOn emb) := by
  exact
    ⟨twoTriangleAnnulusEmbedding,
      twoTriangleClosedWalkAnnulusBoundarySource,
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        twoTriangleClosedWalkAnnulusBoundarySource,
      twoTriangleTaitEdgeColoring,
      twoTriangleTaitEdgeColoring_isTait,
      red, blue,
      (twoTriangleAnnulusEmbedding.faceBoundary twoTriangleOuterFace.1),
      nonempty_twoTriangleOuterFace_v23ResidualBoundaryInitialState,
      theorem49BoundaryRootSynthesis_twoTriangleAnnulusEmbedding_for_explicitTaitColoring_via_noInteriorParentRoute,
      nonempty_twoTriangleClosedWalkSourceResidualBoundaryLayerFacePeelWitnessData,
      not_theorem49ResidualBoundaryPositiveProjectedGeometryOn_twoTriangle,
      not_theorem49CollarLayerPositiveProjectedGeometryOn_twoTriangle,
      not_theorem49HeightOrderedPositiveProjectedGeometryOn_twoTriangle⟩

/-- The same honest-source exact-v23 residual-layer benchmark also makes the sharper endpoint
failure explicit: even after adjoining full theorem-4.9 synthesis to that one-collar shell, the
projected nonempty theorem-4.9 endpoint still fails on the same embedding. -/
theorem
    twoTriangle_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_nonempty_residualBoundaryLayerFacePeelWitnessData_without_theorem49BoundaryRootNonemptyProjectedSynthesis
    [Fintype twoTriangleAnnulusGraph.edgeSet]
    [FiniteDimensional F2 (twoTriangleAnnulusGraph.edgeSet → Color)] :
    ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource twoTriangleAnnulusEmbedding,
      (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData twoTriangleAnnulusEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            source.toPlanarBoundaryAnnulusBoundaryData) ∧
      IsTaitEdgeColoring twoTriangleAnnulusGraph twoTriangleTaitEdgeColoring ∧
      Nonempty
        (V23ResidualBoundaryInitialState twoTriangleTaitEdgeColoring red blue
          (twoTriangleAnnulusEmbedding.faceBoundary twoTriangleOuterFace.1)) ∧
      Theorem49BoundaryRootSynthesis
        twoTriangleAnnulusEmbedding twoTriangleTaitEdgeColoring ∧
      Nonempty
        (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData twoTriangleAnnulusEmbedding) ∧
      ¬ Theorem49BoundaryRootNonemptyProjectedSynthesis
            twoTriangleAnnulusEmbedding twoTriangleTaitEdgeColoring := by
  exact
    ⟨twoTriangleClosedWalkAnnulusBoundarySource,
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        twoTriangleClosedWalkAnnulusBoundarySource,
      twoTriangleTaitEdgeColoring_isTait,
      nonempty_twoTriangleOuterFace_v23ResidualBoundaryInitialState,
      theorem49BoundaryRootSynthesis_twoTriangleAnnulusEmbedding_for_explicitTaitColoring_via_noInteriorParentRoute,
      nonempty_twoTriangleClosedWalkSourceResidualBoundaryLayerFacePeelWitnessData,
      not_theorem49BoundaryRootNonemptyProjectedSynthesis_twoTriangle
        twoTriangleTaitEdgeColoring⟩

/-- Any explicit same-embedding witness of the honest closed-walk exact one-collar/v23 residual
shell together with a residual-layer witness and simultaneous failure of the current direct
positive endpoints already refutes the corresponding universal converse. -/
theorem
    not_forall_any_positiveProjectedGeometryOn_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_nonempty_residualBoundaryLayerFacePeelWitnessData
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : G.EdgeColoring Color,
          IsTaitEdgeColoring G C ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∧
                  ¬ Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49CollarLayerPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49HeightOrderedPositiveProjectedGeometryOn emb) :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary G)
        (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
        (C : G.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset G.edgeSet),
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) →
          IsTaitEdgeColoring G C →
            Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
              Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) →
                Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb ∨
                  Theorem49CollarLayerPositiveProjectedGeometryOn emb ∨
                    Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  intro h
  rcases hWitness with
    ⟨emb, source, hCurrent, C, hC, a, b, faceBoundary, hv23, hResidual, hNoResidual,
      hNoCollar, hNoHeight⟩
  rcases h emb source C a b faceBoundary hCurrent hC hv23 hResidual with hResidual' | hRest
  · exact hNoResidual hResidual'
  · rcases hRest with hCollar | hHeight
    · exact hNoCollar hCollar
    · exact hNoHeight hHeight

/-- The same existential failed converse survives after adjoining full theorem-4.9 synthesis to
the honest closed-walk exact one-collar/v23 residual shell. -/
theorem
    not_forall_any_positiveProjectedGeometryOn_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_nonempty_residualBoundaryLayerFacePeelWitnessData
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : G.EdgeColoring Color,
          IsTaitEdgeColoring G C ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  Theorem49BoundaryRootSynthesis emb C ∧
                  Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∧
                  ¬ Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49CollarLayerPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49HeightOrderedPositiveProjectedGeometryOn emb) :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary G)
        (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
        (C : G.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset G.edgeSet),
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) →
          IsTaitEdgeColoring G C →
            Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
              Theorem49BoundaryRootSynthesis emb C →
                Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) →
                  Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb ∨
                    Theorem49CollarLayerPositiveProjectedGeometryOn emb ∨
                      Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  intro h
  rcases hWitness with
    ⟨emb, source, hCurrent, C, hC, a, b, faceBoundary, hv23, hSynth, hResidual, hNoResidual,
      hNoCollar, hNoHeight⟩
  rcases h emb source C a b faceBoundary hCurrent hC hv23 hSynth hResidual with
    hResidual' | hRest
  · exact hNoResidual hResidual'
  · rcases hRest with hCollar | hHeight
    · exact hNoCollar hCollar
    · exact hNoHeight hHeight

/-- The same honest-source exact-v23 residual-layer benchmark also refutes any universal
derivation from that shell plus full theorem-4.9 synthesis to the projected nonempty theorem-4.9
endpoint itself. -/
theorem
    not_forall_theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_nonempty_residualBoundaryLayerFacePeelWitnessData_twoTriangle
    [Fintype twoTriangleAnnulusGraph.edgeSet]
    [FiniteDimensional F2 (twoTriangleAnnulusGraph.edgeSet → Color)] :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary twoTriangleAnnulusGraph)
        (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
        (C : twoTriangleAnnulusGraph.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset twoTriangleAnnulusGraph.edgeSet),
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) →
          IsTaitEdgeColoring twoTriangleAnnulusGraph C →
            Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
              Theorem49BoundaryRootSynthesis emb C →
                Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) →
                  Theorem49BoundaryRootNonemptyProjectedSynthesis emb C := by
  intro h
  rcases
      twoTriangle_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_nonempty_residualBoundaryLayerFacePeelWitnessData_without_theorem49BoundaryRootNonemptyProjectedSynthesis with
    ⟨source, hCurrent, hC, hv23, hSynth, hResidual, hNoProjected⟩
  exact
    hNoProjected
      (h twoTriangleAnnulusEmbedding source twoTriangleTaitEdgeColoring red blue
        (twoTriangleAnnulusEmbedding.faceBoundary twoTriangleOuterFace.1) hCurrent hC hv23 hSynth
        hResidual)

/-- Honest closed-walk exact-v23 residual-layer benchmark on the two-triangle source: even after
adding exact one-collar current-boundary data, the same embedding carries a real residual-layer
witness while failing every current route-facing replacement-positive target. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_nonempty_residualBoundaryLayerFacePeelWitnessData_without_any_replacementPositiveProjectedGeometryOn_twoTriangleAnnulusGraph
    :
    ∃ emb : PlaneEmbeddingWithBoundary twoTriangleAnnulusGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        (∃ C : twoTriangleAnnulusGraph.EdgeColoring Color,
          IsTaitEdgeColoring twoTriangleAnnulusGraph C ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset twoTriangleAnnulusGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∧
                  ¬ Theorem49HeightOrderedPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49CollarLayerPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb) := by
  exact
    ⟨twoTriangleAnnulusEmbedding,
      twoTriangleClosedWalkAnnulusBoundarySource,
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        twoTriangleClosedWalkAnnulusBoundarySource,
      twoTriangleTaitEdgeColoring,
      twoTriangleTaitEdgeColoring_isTait,
      red, blue,
      (twoTriangleAnnulusEmbedding.faceBoundary twoTriangleOuterFace.1),
      nonempty_twoTriangleOuterFace_v23ResidualBoundaryInitialState,
      nonempty_twoTriangleClosedWalkSourceResidualBoundaryLayerFacePeelWitnessData,
      not_theorem49HeightOrderedPositiveProjectedGeometryOn_twoTriangle,
      not_theorem49CollarLayerPositiveProjectedGeometryOn_twoTriangle,
      not_theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_twoTriangle,
      not_theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn_twoTriangle⟩

/-- The same honest-source exact-v23 replacement-positive obstruction survives after adjoining
full theorem-4.9 synthesis on the same embedding. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_nonempty_residualBoundaryLayerFacePeelWitnessData_without_any_replacementPositiveProjectedGeometryOn_twoTriangleAnnulusGraph
    [Fintype twoTriangleAnnulusGraph.edgeSet]
    [FiniteDimensional F2 (twoTriangleAnnulusGraph.edgeSet → Color)] :
    ∃ emb : PlaneEmbeddingWithBoundary twoTriangleAnnulusGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        (∃ C : twoTriangleAnnulusGraph.EdgeColoring Color,
          IsTaitEdgeColoring twoTriangleAnnulusGraph C ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset twoTriangleAnnulusGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  Theorem49BoundaryRootSynthesis emb C ∧
                  Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∧
                  ¬ Theorem49HeightOrderedPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49CollarLayerPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb) := by
  exact
    ⟨twoTriangleAnnulusEmbedding,
      twoTriangleClosedWalkAnnulusBoundarySource,
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        twoTriangleClosedWalkAnnulusBoundarySource,
      twoTriangleTaitEdgeColoring,
      twoTriangleTaitEdgeColoring_isTait,
      red, blue,
      (twoTriangleAnnulusEmbedding.faceBoundary twoTriangleOuterFace.1),
      nonempty_twoTriangleOuterFace_v23ResidualBoundaryInitialState,
      theorem49BoundaryRootSynthesis_twoTriangleAnnulusEmbedding_for_explicitTaitColoring_via_noInteriorParentRoute,
      nonempty_twoTriangleClosedWalkSourceResidualBoundaryLayerFacePeelWitnessData,
      not_theorem49HeightOrderedPositiveProjectedGeometryOn_twoTriangle,
      not_theorem49CollarLayerPositiveProjectedGeometryOn_twoTriangle,
      not_theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_twoTriangle,
      not_theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn_twoTriangle⟩

/-- Graph-level witness form of the same sharper endpoint obstruction on the honest closed-walk
exact-v23 residual shell. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_nonempty_residualBoundaryLayerFacePeelWitnessData_without_theorem49BoundaryRootNonemptyProjectedSynthesis_twoTriangleAnnulusGraph
    [Fintype twoTriangleAnnulusGraph.edgeSet]
    [FiniteDimensional F2 (twoTriangleAnnulusGraph.edgeSet → Color)] :
    ∃ emb : PlaneEmbeddingWithBoundary twoTriangleAnnulusGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        (∃ C : twoTriangleAnnulusGraph.EdgeColoring Color,
          IsTaitEdgeColoring twoTriangleAnnulusGraph C ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset twoTriangleAnnulusGraph.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  Theorem49BoundaryRootSynthesis emb C ∧
                  Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∧
                  ¬ Theorem49BoundaryRootNonemptyProjectedSynthesis emb C) := by
  exact
    ⟨twoTriangleAnnulusEmbedding,
      twoTriangleClosedWalkAnnulusBoundarySource,
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        twoTriangleClosedWalkAnnulusBoundarySource,
      twoTriangleTaitEdgeColoring,
      twoTriangleTaitEdgeColoring_isTait,
      red, blue,
      (twoTriangleAnnulusEmbedding.faceBoundary twoTriangleOuterFace.1),
      nonempty_twoTriangleOuterFace_v23ResidualBoundaryInitialState,
      theorem49BoundaryRootSynthesis_twoTriangleAnnulusEmbedding_for_explicitTaitColoring_via_noInteriorParentRoute,
      nonempty_twoTriangleClosedWalkSourceResidualBoundaryLayerFacePeelWitnessData,
      not_theorem49BoundaryRootNonemptyProjectedSynthesis_twoTriangle
        twoTriangleTaitEdgeColoring⟩

/-- Any explicit same-embedding witness of the honest closed-walk exact one-collar/v23 residual
shell together with simultaneous failure of the current replacement-positive endpoints already
refutes the corresponding universal converse. -/
theorem
    not_forall_any_replacementPositiveProjectedGeometryOn_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_nonempty_residualBoundaryLayerFacePeelWitnessData
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : G.EdgeColoring Color,
          IsTaitEdgeColoring G C ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∧
                  ¬ Theorem49HeightOrderedPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49CollarLayerPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb) :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary G)
        (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
        (C : G.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset G.edgeSet),
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) →
          IsTaitEdgeColoring G C →
            Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
              Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) →
                Theorem49HeightOrderedPositiveProjectedGeometryOn emb ∨
                  Theorem49CollarLayerPositiveProjectedGeometryOn emb ∨
                    Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb ∨
                      Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb := by
  intro h
  rcases hWitness with
    ⟨emb, source, hCurrent, C, hC, a, b, faceBoundary, hv23, hResidual, hNoHeight, hNoCollar,
      hNoClosedWalk, hNoSuccessor⟩
  rcases h emb source C a b faceBoundary hCurrent hC hv23 hResidual with hHeight | hRest
  · exact hNoHeight hHeight
  · rcases hRest with hCollar | hRest
    · exact hNoCollar hCollar
    · rcases hRest with hClosedWalk | hSuccessor
      · exact hNoClosedWalk hClosedWalk
      · exact hNoSuccessor hSuccessor

/-- The same replacement-positive existential failed converse survives after adjoining full
theorem-4.9 synthesis to the honest closed-walk exact one-collar/v23 residual shell. -/
theorem
    not_forall_any_replacementPositiveProjectedGeometryOn_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_nonempty_residualBoundaryLayerFacePeelWitnessData
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : G.EdgeColoring Color,
          IsTaitEdgeColoring G C ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  Theorem49BoundaryRootSynthesis emb C ∧
                  Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∧
                  ¬ Theorem49HeightOrderedPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49CollarLayerPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb ∧
                  ¬ Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb) :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary G)
        (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
        (C : G.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset G.edgeSet),
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) →
          IsTaitEdgeColoring G C →
            Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
              Theorem49BoundaryRootSynthesis emb C →
                Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) →
                  Theorem49HeightOrderedPositiveProjectedGeometryOn emb ∨
                    Theorem49CollarLayerPositiveProjectedGeometryOn emb ∨
                      Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb ∨
                        Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb := by
  intro h
  rcases hWitness with
    ⟨emb, source, hCurrent, C, hC, a, b, faceBoundary, hv23, hSynth, hResidual, hNoHeight,
      hNoCollar, hNoClosedWalk, hNoSuccessor⟩
  rcases h emb source C a b faceBoundary hCurrent hC hv23 hSynth hResidual with hHeight | hRest
  · exact hNoHeight hHeight
  · rcases hRest with hCollar | hRest
    · exact hNoCollar hCollar
    · rcases hRest with hClosedWalk | hSuccessor
      · exact hNoClosedWalk hClosedWalk
      · exact hNoSuccessor hSuccessor

/-- The same graph-level honest-source witness already refutes any universal derivation from the
exact one-collar/v23 residual shell plus full theorem-4.9 synthesis to the projected nonempty
theorem-4.9 endpoint itself. -/
theorem
    not_forall_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_nonempty_residualBoundaryLayerFacePeelWitnessData
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C : G.EdgeColoring Color,
          IsTaitEdgeColoring G C ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                  Theorem49BoundaryRootSynthesis emb C ∧
                  Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∧
                  ¬ Theorem49BoundaryRootNonemptyProjectedSynthesis emb C) :
    ¬ ∀ (emb : PlaneEmbeddingWithBoundary G)
        (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
        (C : G.EdgeColoring Color)
        (a b : Color) (faceBoundary : Finset G.edgeSet),
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) →
          IsTaitEdgeColoring G C →
            Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
              Theorem49BoundaryRootSynthesis emb C →
                Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) →
                  Theorem49BoundaryRootNonemptyProjectedSynthesis emb C := by
  intro h
  rcases hWitness with
    ⟨emb, source, hCurrent, C, hC, a, b, faceBoundary, hv23, hSynth, hResidual, hNoProjected⟩
  exact
    hNoProjected
      (h emb source C a b faceBoundary hCurrent hC hv23 hSynth hResidual)

end Theorem49ResidualBoundaryPositiveRegression

end Mettapedia.GraphTheory.FourColor
