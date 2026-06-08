import Mettapedia.GraphTheory.FourColor.GoertzelLemma44
import Mettapedia.GraphTheory.FourColor.Theorem49ResidualBoundaryPeeling
import Mettapedia.GraphTheory.FourColor.PlanarBoundaryClosedWalkSource
import Mettapedia.GraphTheory.FourColor.Theorem49BoundaryFreeSelectorConstruction
import Mettapedia.GraphTheory.FourColor.Theorem49BoundaryFreeSelectorPositiveRoute
import Mettapedia.GraphTheory.FourColor.Theorem49AtMostOneNonemptyCarrierImpossibility
import Mettapedia.GraphTheory.FourColor.Theorem49PositiveGeometricSourceConstruction
import Mettapedia.GraphTheory.FourColor.Theorem49PositiveGeometricSourceReplacementRoute
import Mettapedia.GraphTheory.FourColor.Theorem49Synthesis

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open Theorem49ForcingInteriorEdgeObstruction
open Theorem49InteriorVerticesEndpointObstruction
open Theorem49PlanarBoundaryAnnulusHonestGeometryRegression

variable {V : Type*} [DecidableEq V]

/-- Minimal residual seed object extracted from the exact v23 Step 2 single-component
purification theorem. -/
structure V23ResidualBoundarySeed {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (a b : Color) (faceBoundary : Finset G.edgeSet) where
  component_purification :
    ∀ K : (C.bicoloredSubgraph a b).ConnectedComponent,
      v23PolarizedFaceGenerator C a b faceBoundary +
          v23PolarizedFaceGenerator (C.swapOnKempeComponent a b K) a b faceBoundary =
        componentBoundarySlice C a b faceBoundary K

/-- Finite initial residual state: the exact componentwise purification data together with the
already-proved recovery of the downstream boundary-only generator. -/
structure V23ResidualBoundaryInitialState {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (a b : Color) (faceBoundary : Finset G.edgeSet) where
  seed : V23ResidualBoundarySeed C a b faceBoundary
  sum_purification_eq_boundaryOnly :
    Finset.sum (boundaryKempeComponents C a b faceBoundary)
      (fun K : (C.bicoloredSubgraph a b).ConnectedComponent =>
        v23PolarizedFaceGenerator C a b faceBoundary +
          (v23PolarizedFaceGenerator (C.swapOnKempeComponent a b K) a b faceBoundary :
            G.edgeSet → Color)) =
      polarizedFaceGenerator C a b faceBoundary

theorem residualBoundarySeed_of_v23_single_component_purification
    {G : SimpleGraph V} (C : G.EdgeColoring Color)
    (a b : Color) (faceBoundary : Finset G.edgeSet) :
    V23ResidualBoundarySeed C a b faceBoundary := by
  exact ⟨fun K => v23_single_component_purification C a b faceBoundary K⟩

theorem residualBoundaryInitialState_of_sum_v23_single_component_purifications_eq_boundaryOnlyGenerator
    {G : SimpleGraph V} (C : G.EdgeColoring Color)
    (a b : Color) (faceBoundary : Finset G.edgeSet) :
    V23ResidualBoundaryInitialState C a b faceBoundary := by
  exact
    ⟨residualBoundarySeed_of_v23_single_component_purification C a b faceBoundary,
      sum_v23_single_component_purifications_eq_boundaryOnlyGenerator C a b faceBoundary⟩

/-- Any explicit same-embedding exact-v23 honest-source witness carrying a real Tait coloring,
the final theorem-4.9 boundary-root synthesis endpoint, and failure of an embedding-indexed
target refutes a universal derivation from that exact-v23 honest-source package to the target. -/
theorem
    not_forall_target_of_exists_embedding_closedWalkAnnulusBoundarySource_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_without_target
    {G : SimpleGraph V}
    [Fintype G.edgeSet]
    [FiniteDimensional F2 (G.edgeSet → Color)]
    (Target : PlaneEmbeddingWithBoundary G → Prop)
    (hWitness :
      ∃ emb : PlaneEmbeddingWithBoundary G,
        ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          ∃ C : G.EdgeColoring Color,
            IsTaitEdgeColoring G C ∧
              ∃ a b : Color,
                ∃ faceBoundary : Finset G.edgeSet,
                  Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                    Theorem49BoundaryRootSynthesis emb C ∧
                    ¬ Target emb) :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary G,
        ∀ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          ∀ C : G.EdgeColoring Color,
            IsTaitEdgeColoring G C →
              ∀ a b : Color,
                ∀ faceBoundary : Finset G.edgeSet,
                  Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                    Theorem49BoundaryRootSynthesis emb C →
                      Target emb := by
  refine
    not_forall_target_of_exists_embedding_closedWalkAnnulusBoundarySource_without_target
      (Target := fun emb _source =>
        ∀ C : G.EdgeColoring Color,
          IsTaitEdgeColoring G C →
            ∀ a b : Color,
              ∀ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                  Theorem49BoundaryRootSynthesis emb C →
                    Target emb) ?_
  rcases hWitness with ⟨emb, source, C, hC, a, b, faceBoundary, hv23, hSynth, hNo⟩
  exact
    ⟨emb, source, by
      intro hTarget
      exact hNo (hTarget C hC a b faceBoundary hv23 hSynth)⟩

/-- Any explicit same-embedding exact-v23 successor-cycle witness carrying a real Tait coloring,
the final theorem-4.9 boundary-root synthesis endpoint, and failure of an embedding-indexed
target refutes a universal derivation from that exact-v23 successor-cycle package to the target. -/
theorem
    not_forall_target_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_without_target
    {G : SimpleGraph V}
    [Fintype G.edgeSet]
    [FiniteDimensional F2 (G.edgeSet → Color)]
    (Target : PlaneEmbeddingWithBoundary G → Prop)
    (hWitness :
      ∃ emb : PlaneEmbeddingWithBoundary G,
        ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          ∃ C : G.EdgeColoring Color,
            IsTaitEdgeColoring G C ∧
              ∃ a b : Color,
                ∃ faceBoundary : Finset G.edgeSet,
                  Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                    Theorem49BoundaryRootSynthesis emb C ∧
                    ¬ Target emb) :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary G,
        ∀ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
            ∀ C : G.EdgeColoring Color,
              IsTaitEdgeColoring G C →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset G.edgeSet,
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                      Theorem49BoundaryRootSynthesis emb C →
                        Target emb := by
  refine
    not_forall_target_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_without_target
      (Target := fun emb =>
        ∀ C : G.EdgeColoring Color,
          IsTaitEdgeColoring G C →
            ∀ a b : Color,
              ∀ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                  Theorem49BoundaryRootSynthesis emb C →
                    Target emb) ?_
  rcases hWitness with
    ⟨emb, boundaryData, dartCycles, hSelectedBoundaryArc, C, hC, a, b, faceBoundary, hv23,
      hSynth, hNo⟩
  exact
    ⟨emb, boundaryData, dartCycles, hSelectedBoundaryArc, by
      intro hTarget
      exact hNo (hTarget C hC a b faceBoundary hv23 hSynth)⟩

/-- Any explicit same-embedding exact-v23 honest-source witness carrying exact one-collar
current-boundary data, a real Tait coloring, the final theorem-4.9 boundary-root synthesis
endpoint, and failure of an embedding-indexed target refutes a universal derivation from that
strengthened exact-v23 honest-source package to the target. -/
theorem
    not_forall_target_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_without_target
    {G : SimpleGraph V}
    [Fintype G.edgeSet]
    [FiniteDimensional F2 (G.edgeSet → Color)]
    (Target : PlaneEmbeddingWithBoundary G → Prop)
    (hWitness :
      ∃ emb : PlaneEmbeddingWithBoundary G,
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
                    ¬ Target emb) :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary G,
        ∀ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                source.toPlanarBoundaryAnnulusBoundaryData) →
            ∀ C : G.EdgeColoring Color,
              IsTaitEdgeColoring G C →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset G.edgeSet,
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                      Theorem49BoundaryRootSynthesis emb C →
                        Target emb := by
  refine
    not_forall_target_of_exists_embedding_closedWalkAnnulusBoundarySource_without_target
      (Target := fun emb source =>
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) →
          ∀ C : G.EdgeColoring Color,
            IsTaitEdgeColoring G C →
              ∀ a b : Color,
                ∀ faceBoundary : Finset G.edgeSet,
                  Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                    Theorem49BoundaryRootSynthesis emb C →
                      Target emb) ?_
  rcases hWitness with ⟨emb, source, hcurrent, C, hC, a, b, faceBoundary, hv23, hSynth, hNo⟩
  exact
    ⟨emb, source, by
      intro hTarget
      exact hNo (hTarget hcurrent C hC a b faceBoundary hv23 hSynth)⟩

/-- Any explicit same-embedding exact-v23 successor-cycle witness carrying exact one-collar
current-boundary data, a real Tait coloring, the final theorem-4.9 boundary-root synthesis
endpoint, and failure of an embedding-indexed target refutes a universal derivation from that
strengthened exact-v23 successor-cycle package to the target. -/
theorem
    not_forall_target_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_without_target
    {G : SimpleGraph V}
    [Fintype G.edgeSet]
    [FiniteDimensional F2 (G.edgeSet → Color)]
    (Target : PlaneEmbeddingWithBoundary G → Prop)
    (hWitness :
      ∃ emb : PlaneEmbeddingWithBoundary G,
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
                    ¬ Target emb) :
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
                        Target emb := by
  intro h
  rcases hWitness with
    ⟨emb, boundaryData, dartCycles, hSelectedBoundaryArc, hcurrent, C, hC, a, b, faceBoundary,
      hv23, hSynth, hNo⟩
  exact hNo (h emb boundaryData dartCycles hSelectedBoundaryArc hcurrent C hC a b faceBoundary hv23 hSynth)

/-- Any explicit same-embedding exact-v23 honest-source witness carrying a real Tait coloring,
the final theorem-4.9 boundary-root synthesis endpoint, and simultaneous failure of every
currently formalized positive-stage construction shell refutes a universal derivation from that
exact-v23 honest-source package to the whole positive-stage surface. -/
theorem
    not_forall_somePositiveStageConstructionShell_of_exists_embedding_closedWalkAnnulusBoundarySource_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_noPositiveStageConstructionShells
    {G : SimpleGraph V}
    [Fintype G.edgeSet]
    [FiniteDimensional F2 (G.edgeSet → Color)]
    (hWitness :
      ∃ emb : PlaneEmbeddingWithBoundary G,
        ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          ∃ C : G.EdgeColoring Color,
            IsTaitEdgeColoring G C ∧
              ∃ a b : Color,
                ∃ faceBoundary : Finset G.edgeSet,
                  Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                    Theorem49BoundaryRootSynthesis emb C ∧
                    NoPositiveStageConstructionShells emb) :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary G,
        ∀ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          ∀ C : G.EdgeColoring Color,
            IsTaitEdgeColoring G C →
              ∀ a b : Color,
                ∀ faceBoundary : Finset G.edgeSet,
                  Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                    Theorem49BoundaryRootSynthesis emb C →
                      SomePositiveStageConstructionShell emb := by
  refine
    not_forall_target_of_exists_embedding_closedWalkAnnulusBoundarySource_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_without_target
      (G := G) (Target := fun emb => SomePositiveStageConstructionShell emb) ?_
  rcases hWitness with ⟨emb, source, C, hC, a, b, faceBoundary, hv23, hSynth, hNo⟩
  exact
    ⟨emb, source, C, hC, a, b, faceBoundary, hv23, hSynth,
      not_somePositiveStageConstructionShell_of_noPositiveStageConstructionShells hNo⟩

/-- Any explicit same-embedding exact-v23 successor-cycle witness carrying a real Tait coloring,
the final theorem-4.9 boundary-root synthesis endpoint, and simultaneous failure of every
currently formalized positive-stage construction shell refutes a universal derivation from that
exact-v23 successor-cycle package to the whole positive-stage surface. -/
theorem
    not_forall_somePositiveStageConstructionShell_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_noPositiveStageConstructionShells
    {G : SimpleGraph V}
    [Fintype G.edgeSet]
    [FiniteDimensional F2 (G.edgeSet → Color)]
    (hWitness :
      ∃ emb : PlaneEmbeddingWithBoundary G,
        ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          ∃ C : G.EdgeColoring Color,
            IsTaitEdgeColoring G C ∧
              ∃ a b : Color,
                ∃ faceBoundary : Finset G.edgeSet,
                  Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                    Theorem49BoundaryRootSynthesis emb C ∧
                    NoPositiveStageConstructionShells emb) :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary G,
        ∀ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
            ∀ C : G.EdgeColoring Color,
              IsTaitEdgeColoring G C →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset G.edgeSet,
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                      Theorem49BoundaryRootSynthesis emb C →
                        SomePositiveStageConstructionShell emb := by
  refine
    not_forall_target_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_without_target
      (G := G) (Target := fun emb => SomePositiveStageConstructionShell emb) ?_
  rcases hWitness with
    ⟨emb, boundaryData, dartCycles, hSelectedBoundaryArc, C, hC, a, b, faceBoundary, hv23,
      hSynth, hNo⟩
  exact
    ⟨emb, boundaryData, dartCycles, hSelectedBoundaryArc, C, hC, a, b, faceBoundary, hv23,
      hSynth, not_somePositiveStageConstructionShell_of_noPositiveStageConstructionShells hNo⟩

/-- Any explicit same-embedding exact-v23 honest-source witness carrying exact one-collar
current-boundary data, a real Tait coloring, the final theorem-4.9 boundary-root synthesis
endpoint, and simultaneous failure of every currently formalized positive-stage construction shell
refutes a universal derivation from that strengthened exact-v23 honest-source package to the
whole positive-stage surface. -/
theorem
    not_forall_somePositiveStageConstructionShell_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_noPositiveStageConstructionShells
    {G : SimpleGraph V}
    [Fintype G.edgeSet]
    [FiniteDimensional F2 (G.edgeSet → Color)]
    (hWitness :
      ∃ emb : PlaneEmbeddingWithBoundary G,
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
                    NoPositiveStageConstructionShells emb) :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary G,
        ∀ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                source.toPlanarBoundaryAnnulusBoundaryData) →
            ∀ C : G.EdgeColoring Color,
              IsTaitEdgeColoring G C →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset G.edgeSet,
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                      Theorem49BoundaryRootSynthesis emb C →
                        SomePositiveStageConstructionShell emb := by
  refine
    not_forall_target_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_without_target
      (G := G) (Target := fun emb => SomePositiveStageConstructionShell emb) ?_
  rcases hWitness with ⟨emb, source, hcurrent, C, hC, a, b, faceBoundary, hv23, hSynth, hNo⟩
  exact
    ⟨emb, source, hcurrent, C, hC, a, b, faceBoundary, hv23, hSynth,
      not_somePositiveStageConstructionShell_of_noPositiveStageConstructionShells hNo⟩

/-- Any explicit same-embedding exact-v23 successor-cycle witness carrying exact one-collar
current-boundary data, a real Tait coloring, the final theorem-4.9 boundary-root synthesis
endpoint, and simultaneous failure of every currently formalized positive-stage construction shell
refutes a universal derivation from that strengthened exact-v23 successor-cycle package to the
whole positive-stage surface. -/
theorem
    not_forall_somePositiveStageConstructionShell_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_noPositiveStageConstructionShells
    {G : SimpleGraph V}
    [Fintype G.edgeSet]
    [FiniteDimensional F2 (G.edgeSet → Color)]
    (hWitness :
      ∃ emb : PlaneEmbeddingWithBoundary G,
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
                    NoPositiveStageConstructionShells emb) :
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
                        SomePositiveStageConstructionShell emb := by
  refine
    not_forall_target_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_without_target
      (G := G) (Target := fun emb => SomePositiveStageConstructionShell emb) ?_
  rcases hWitness with
    ⟨emb, boundaryData, dartCycles, hSelectedBoundaryArc, hcurrent, C, hC, a, b, faceBoundary,
      hv23, hSynth, hNo⟩
  exact
    ⟨emb, boundaryData, dartCycles, hSelectedBoundaryArc, hcurrent, C, hC, a, b, faceBoundary,
      hv23, hSynth, not_somePositiveStageConstructionShell_of_noPositiveStageConstructionShells hNo⟩

/-- Any explicit same-embedding exact-v23 honest-source witness carrying a real Tait coloring,
a local boundary-free selector, the final theorem-4.9 boundary-root synthesis endpoint, and
simultaneous failure of every currently formalized positive-stage construction shell refutes a
universal derivation from that selector-strengthened exact-v23 honest-source package to the whole
positive-stage surface. -/
theorem
    not_forall_somePositiveStageConstructionShell_of_exists_embedding_closedWalkAnnulusBoundarySource_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_boundaryFreeIncidentFaceSelector_and_theorem49BoundaryRootSynthesis_and_noPositiveStageConstructionShells
    {G : SimpleGraph V}
    [Fintype G.edgeSet]
    [FiniteDimensional F2 (G.edgeSet → Color)]
    (hWitness :
      ∃ emb : PlaneEmbeddingWithBoundary G,
        ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          ∃ C : G.EdgeColoring Color,
            IsTaitEdgeColoring G C ∧
              ∃ a b : Color,
                ∃ faceBoundary : Finset G.edgeSet,
                  Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                    Nonempty (BoundaryFreeIncidentFaceSelector emb) ∧
                    Theorem49BoundaryRootSynthesis emb C ∧
                    NoPositiveStageConstructionShells emb) :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary G,
        ∀ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          ∀ C : G.EdgeColoring Color,
            IsTaitEdgeColoring G C →
              ∀ a b : Color,
                ∀ faceBoundary : Finset G.edgeSet,
                  Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                    Theorem49BoundaryRootSynthesis emb C →
                      Nonempty (BoundaryFreeIncidentFaceSelector emb) →
                        SomePositiveStageConstructionShell emb := by
  refine
    not_forall_target_of_exists_embedding_closedWalkAnnulusBoundarySource_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_without_target
      (G := G)
      (Target := fun emb =>
        Nonempty (BoundaryFreeIncidentFaceSelector emb) →
          SomePositiveStageConstructionShell emb) ?_
  rcases hWitness with ⟨emb, source, C, hC, a, b, faceBoundary, hv23, hSelector, hSynth, hNo⟩
  exact
    ⟨emb, source, C, hC, a, b, faceBoundary, hv23, hSynth, by
      intro hTarget
      exact
        not_somePositiveStageConstructionShell_of_noPositiveStageConstructionShells hNo
          (hTarget hSelector)⟩

/-- Any explicit same-embedding exact-v23 successor-cycle witness carrying a real Tait coloring,
a local boundary-free selector, the final theorem-4.9 boundary-root synthesis endpoint, and
simultaneous failure of every currently formalized positive-stage construction shell refutes a
universal derivation from that selector-strengthened exact-v23 successor-cycle package to the
whole positive-stage surface. -/
theorem
    not_forall_somePositiveStageConstructionShell_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_boundaryFreeIncidentFaceSelector_and_theorem49BoundaryRootSynthesis_and_noPositiveStageConstructionShells
    {G : SimpleGraph V}
    [Fintype G.edgeSet]
    [FiniteDimensional F2 (G.edgeSet → Color)]
    (hWitness :
      ∃ emb : PlaneEmbeddingWithBoundary G,
        ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          ∃ C : G.EdgeColoring Color,
            IsTaitEdgeColoring G C ∧
              ∃ a b : Color,
                ∃ faceBoundary : Finset G.edgeSet,
                  Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) ∧
                    Nonempty (BoundaryFreeIncidentFaceSelector emb) ∧
                    Theorem49BoundaryRootSynthesis emb C ∧
                    NoPositiveStageConstructionShells emb) :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary G,
        ∀ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
            ∀ C : G.EdgeColoring Color,
              IsTaitEdgeColoring G C →
                ∀ a b : Color,
                  ∀ faceBoundary : Finset G.edgeSet,
                    Nonempty (V23ResidualBoundaryInitialState C a b faceBoundary) →
                      Theorem49BoundaryRootSynthesis emb C →
                        Nonempty (BoundaryFreeIncidentFaceSelector emb) →
                          SomePositiveStageConstructionShell emb := by
  refine
    not_forall_target_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_without_target
      (G := G)
      (Target := fun emb =>
        Nonempty (BoundaryFreeIncidentFaceSelector emb) →
          SomePositiveStageConstructionShell emb) ?_
  rcases hWitness with
    ⟨emb, boundaryData, dartCycles, hSelectedBoundaryArc, C, hC, a, b, faceBoundary, hv23,
      hSelector, hSynth, hNo⟩
  exact
    ⟨emb, boundaryData, dartCycles, hSelectedBoundaryArc, C, hC, a, b, faceBoundary, hv23,
      hSynth, by
        intro hTarget
        exact
          not_somePositiveStageConstructionShell_of_noPositiveStageConstructionShells hNo
            (hTarget hSelector)⟩

theorem
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (_source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C₀ := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
      data hEndpoint C₀ hC₀

theorem
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (data : PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C₀ := by
  let source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hselectedBoundaryArc
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
      source data hEndpoint C₀ hC₀

theorem
    theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusBoundarySource_and_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (_source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C₀ x := by
  exact
    theorem49BoundaryRawQuotientErrorPackage_of_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
      data hEndpoint C₀ hC₀ hx

theorem
    theorem49BoundaryRawQuotientErrorPackage_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (data : PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C₀ x := by
  let source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hselectedBoundaryArc
  exact
    theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusBoundarySource_and_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
      source data hEndpoint C₀ hC₀ hx

theorem
    theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_residualBoundaryLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (_source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Theorem49BoundaryRootSynthesis emb C₀ := by
  exact
    theorem49BoundaryRootSynthesis_of_residualBoundaryLayerFacePeelWitnessData
      data C₀ hC₀

theorem
    theorem49BoundaryRootSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_residualBoundaryLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (data : PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Theorem49BoundaryRootSynthesis emb C₀ := by
  let source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hselectedBoundaryArc
  exact
    theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_residualBoundaryLayerFacePeelWitnessData
      source data C₀ hC₀

theorem
    theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_residualBoundarySelectorData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (_source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : ResidualBoundarySelectorData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Theorem49BoundaryRootSynthesis emb C₀ := by
  exact
    theorem49BoundaryRootSynthesis_of_residualBoundarySelectorData
      data C₀ hC₀

theorem
    theorem49BoundaryRootSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_residualBoundarySelectorData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (data : ResidualBoundarySelectorData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Theorem49BoundaryRootSynthesis emb C₀ := by
  let source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hselectedBoundaryArc
  exact
    theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_residualBoundarySelectorData
      source data C₀ hC₀

theorem
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_residualBoundarySelectorData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (_source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : ResidualBoundarySelectorData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C₀ := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_residualBoundarySelectorData_and_hasUnblockedInteriorEndpoint
      data hEndpoint C₀ hC₀

theorem
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_residualBoundarySelectorData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (data : ResidualBoundarySelectorData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C₀ := by
  let source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hselectedBoundaryArc
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_residualBoundarySelectorData_and_hasUnblockedInteriorEndpoint
      source data hEndpoint C₀ hC₀

theorem
    theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusBoundarySource_and_residualBoundarySelectorData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (_source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : ResidualBoundarySelectorData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C₀ x := by
  exact
    theorem49BoundaryRawQuotientErrorPackage_of_residualBoundarySelectorData_and_hasUnblockedInteriorEndpoint
      data hEndpoint C₀ hC₀ hx

theorem
    theorem49BoundaryRawQuotientErrorPackage_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_residualBoundarySelectorData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (data : ResidualBoundarySelectorData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C₀ x := by
  let source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hselectedBoundaryArc
  exact
    theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusBoundarySource_and_residualBoundarySelectorData_and_hasUnblockedInteriorEndpoint
      source data hEndpoint C₀ hC₀ hx

theorem
    theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (_source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb := by
  exact
    theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
      data hEndpoint

theorem
    theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (data : PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb := by
  let source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hselectedBoundaryArc
  exact
    theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
      source data hEndpoint

theorem
    theorem49CurrentBoundaryRemainders_of_closedWalkAnnulusBoundarySource_and_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint_via_residualBoundary
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (_source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    ∃ i : Fin data.numLayers, ∃ f ∈ data.layerFaces i,
      ∀ e ∈ (emb.faceBoundary f.1).erase (data.witnessEdge f), e ∈ data.currentBoundary i := by
  exact
    exists_layerFace_currentBoundary_remainders_of_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
      data hEndpoint

theorem
    theorem49CurrentBoundaryRemainders_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint_via_residualBoundary
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (data : PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    ∃ i : Fin data.numLayers, ∃ f ∈ data.layerFaces i,
      ∀ e ∈ (emb.faceBoundary f.1).erase (data.witnessEdge f), e ∈ data.currentBoundary i := by
  let source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hselectedBoundaryArc
  exact
    theorem49CurrentBoundaryRemainders_of_closedWalkAnnulusBoundarySource_and_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint_via_residualBoundary
      source data hEndpoint

theorem
    theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_residualBoundarySelectorData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (_source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : ResidualBoundarySelectorData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb := by
  exact
    theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_residualBoundarySelectorData_and_hasUnblockedInteriorEndpoint
      data hEndpoint

theorem
    theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_residualBoundarySelectorData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (data : ResidualBoundarySelectorData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb := by
  let source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hselectedBoundaryArc
  exact
    theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_residualBoundarySelectorData_and_hasUnblockedInteriorEndpoint
      source data hEndpoint

theorem
    theorem49CurrentBoundaryRemainders_of_closedWalkAnnulusBoundarySource_and_residualBoundarySelectorData_and_hasUnblockedInteriorEndpoint_via_residualBoundary
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (_source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : ResidualBoundarySelectorData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    ∃ i : Fin data.toResidualBoundaryLayerFacePeelWitnessData.numLayers,
      ∃ f ∈ data.toResidualBoundaryLayerFacePeelWitnessData.layerFaces i,
        ∀ e ∈ (emb.faceBoundary f.1).erase
            (data.toResidualBoundaryLayerFacePeelWitnessData.witnessEdge f),
          e ∈ data.toResidualBoundaryLayerFacePeelWitnessData.currentBoundary i := by
  exact
    exists_layerFace_currentBoundary_remainders_of_residualBoundarySelectorData_and_hasUnblockedInteriorEndpoint
      data hEndpoint

theorem
    theorem49CurrentBoundaryRemainders_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_residualBoundarySelectorData_and_hasUnblockedInteriorEndpoint_via_residualBoundary
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (data : ResidualBoundarySelectorData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    ∃ i : Fin data.toResidualBoundaryLayerFacePeelWitnessData.numLayers,
      ∃ f ∈ data.toResidualBoundaryLayerFacePeelWitnessData.layerFaces i,
        ∀ e ∈ (emb.faceBoundary f.1).erase
            (data.toResidualBoundaryLayerFacePeelWitnessData.witnessEdge f),
          e ∈ data.toResidualBoundaryLayerFacePeelWitnessData.currentBoundary i := by
  let source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hselectedBoundaryArc
  exact
    theorem49CurrentBoundaryRemainders_of_closedWalkAnnulusBoundarySource_and_residualBoundarySelectorData_and_hasUnblockedInteriorEndpoint_via_residualBoundary
      source data hEndpoint

/-- Direct selector-side forcing-edge repair on the actual boundary-order shell. If boundary
reachability plus facewise selected-boundary arcs already support a boundary-free selector with
the local selected-boundary-contact and positive current-outer-boundary conditions needed by the
construction shell, then forcing interior edges are excluded on that same embedding without
passing through annulus-root parent packaging. -/
theorem
    not_nonempty_forcingInteriorEdgeWitness_of_boundaryReachabilityData_and_closedWalkEmbeddingData_and_selectedBoundaryArcOnFace_and_boundaryFreeIncidentFaceSelector_and_boundarySupportFaceData_conditions
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (boundaryGeom : PlanarBoundaryClosedWalkEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (boundaryGeom.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (selector : BoundaryFreeIncidentFaceSelector emb)
    (fallbackEdge : AmbientFace emb.faces → G.edgeSet)
    (faceDistance : AmbientFace emb.faces → ℕ)
    (hinjective :
      ∀ {e₁ e₂ : G.edgeSet}
        (he₁ : e₁ ∈ interiorEdgeSupport emb.faceBoundary emb.faces)
        (he₂ : e₂ ∈ interiorEdgeSupport emb.faceBoundary emb.faces),
          selector.faceOf e₁ he₁ = selector.faceOf e₂ he₂ → e₁ = e₂)
    (hrest :
      ∀ f ∈ selector.peelFaces,
        ∀ e ∈ (emb.faceBoundary f.1).erase (selector.selectedWitnessEdge fallbackEdge f),
          e ∈
              boundaryData.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                boundaryData.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary ∨
            ∃ g ∈ selector.peelFaces,
              selector.selectedWitnessEdge fallbackEdge g = e ∧
                faceDistance f < faceDistance g)
    (hnonPeelSelectedBoundary : ∀ f : AmbientFace emb.faces,
      f ∉ selector.peelFaces →
        ∃ e ∈ emb.faceBoundary f.1,
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (hcurrentOuterBoundaryNonempty :
      ∀ i :
          Fin
            (selector.toPlanarBoundaryAnnulusConstruction
              boundaryData.toPlanarBoundaryAnnulusBoundaryData
              fallbackEdge faceDistance hinjective hrest).numCollars,
        0 < i.1 →
          ((selector.toPlanarBoundaryAnnulusConstruction
              boundaryData.toPlanarBoundaryAnnulusBoundaryData
              fallbackEdge faceDistance hinjective hrest).currentOuterBoundary i).Nonempty)
    (hcurrentOuterBoundaryDisjoint :
      ∀ {i j :
          Fin
            (selector.toPlanarBoundaryAnnulusConstruction
              boundaryData.toPlanarBoundaryAnnulusBoundaryData
              fallbackEdge faceDistance hinjective hrest).numCollars},
        0 < i.1 → 0 < j.1 → i ≠ j →
          Disjoint
            ((selector.toPlanarBoundaryAnnulusConstruction
                boundaryData.toPlanarBoundaryAnnulusBoundaryData
                fallbackEdge faceDistance hinjective hrest).currentOuterBoundary i)
            ((selector.toPlanarBoundaryAnnulusConstruction
                boundaryData.toPlanarBoundaryAnnulusBoundaryData
                fallbackEdge faceDistance hinjective hrest).currentOuterBoundary j)) :
    ¬ Nonempty
      (Theorem49ForcingInteriorEdgeObstruction.ForcingInteriorEdgeWitness emb) := by
  exact
    selector.not_nonempty_forcingInteriorEdgeWitness_of_boundarySupportFaceData_conditions
      boundaryData.toPlanarBoundaryAnnulusBoundaryData
      fallbackEdge
      faceDistance
      hinjective
      hrest
      hnonPeelSelectedBoundary
      (by
        intro f
        exact
          boundaryData.boundaryFaceSeparated_of_closedWalkEmbeddingData_and_selectedBoundaryArcOnFace
            boundaryGeom hboundaryArc (f := f))
      hcurrentOuterBoundaryNonempty
      hcurrentOuterBoundaryDisjoint

/-- Route-facing successor-cycle form of the same selector-side forcing-edge repair. This names
the actual boundary-order shell used by the live route rather than its closed-walk projection:
once the successor-cycle data supports the local boundary-free selector package with the positive
selected-boundary and current-outer-boundary conditions, forcing interior edges are excluded on
that same embedding. -/
theorem
    not_nonempty_forcingInteriorEdgeWitness_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFreeIncidentFaceSelector_and_boundarySupportFaceData_conditions
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (selector : BoundaryFreeIncidentFaceSelector emb)
    (fallbackEdge : AmbientFace emb.faces → G.edgeSet)
    (faceDistance : AmbientFace emb.faces → ℕ)
    (hinjective :
      ∀ {e₁ e₂ : G.edgeSet}
        (he₁ : e₁ ∈ interiorEdgeSupport emb.faceBoundary emb.faces)
        (he₂ : e₂ ∈ interiorEdgeSupport emb.faceBoundary emb.faces),
          selector.faceOf e₁ he₁ = selector.faceOf e₂ he₂ → e₁ = e₂)
    (hrest :
      ∀ f ∈ selector.peelFaces,
        ∀ e ∈ (emb.faceBoundary f.1).erase (selector.selectedWitnessEdge fallbackEdge f),
          e ∈
              boundaryData.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                boundaryData.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary ∨
            ∃ g ∈ selector.peelFaces,
              selector.selectedWitnessEdge fallbackEdge g = e ∧
                faceDistance f < faceDistance g)
    (hnonPeelSelectedBoundary : ∀ f : AmbientFace emb.faces,
      f ∉ selector.peelFaces →
        ∃ e ∈ emb.faceBoundary f.1,
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (hcurrentOuterBoundaryNonempty :
      ∀ i :
          Fin
            (selector.toPlanarBoundaryAnnulusConstruction
              boundaryData.toPlanarBoundaryAnnulusBoundaryData
              fallbackEdge faceDistance hinjective hrest).numCollars,
        0 < i.1 →
          ((selector.toPlanarBoundaryAnnulusConstruction
              boundaryData.toPlanarBoundaryAnnulusBoundaryData
              fallbackEdge faceDistance hinjective hrest).currentOuterBoundary i).Nonempty)
    (hcurrentOuterBoundaryDisjoint :
      ∀ {i j :
          Fin
            (selector.toPlanarBoundaryAnnulusConstruction
              boundaryData.toPlanarBoundaryAnnulusBoundaryData
              fallbackEdge faceDistance hinjective hrest).numCollars},
        0 < i.1 → 0 < j.1 → i ≠ j →
          Disjoint
            ((selector.toPlanarBoundaryAnnulusConstruction
                boundaryData.toPlanarBoundaryAnnulusBoundaryData
                fallbackEdge faceDistance hinjective hrest).currentOuterBoundary i)
            ((selector.toPlanarBoundaryAnnulusConstruction
                boundaryData.toPlanarBoundaryAnnulusBoundaryData
                fallbackEdge faceDistance hinjective hrest).currentOuterBoundary j)) :
    ¬ Nonempty
      (Theorem49ForcingInteriorEdgeObstruction.ForcingInteriorEdgeWitness emb) := by
  exact
    not_nonempty_forcingInteriorEdgeWitness_of_boundaryReachabilityData_and_closedWalkEmbeddingData_and_selectedBoundaryArcOnFace_and_boundaryFreeIncidentFaceSelector_and_boundarySupportFaceData_conditions
      boundaryData
      dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
      hselectedBoundaryArc
      selector
      fallbackEdge
      faceDistance
      hinjective
      hrest
      hnonPeelSelectedBoundary
      hcurrentOuterBoundaryNonempty
      hcurrentOuterBoundaryDisjoint

/-- Exact-v23/v23.5 forcing-edge repair on the honest closed-walk shell: once the same boundary
split carries annulus-root parent peel data, the selector-deficit selected-boundary condition, and
the positive current-outer-boundary side conditions needed by the construction shell, the known
forcing-interior-edge obstruction disappears on that exact shell. -/
theorem
    not_nonempty_forcingInteriorEdgeWitness_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          source.toPlanarBoundaryAnnulusBoundaryData)
    (C₀ : G.EdgeColoring Color)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary))
    (parentData : PlanarBoundaryAnnulusRootParentPeelData emb)
    (hparentBoundary :
      parentData.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData)
    (hselectorDeficitSelectedBoundary : ∀ f : AmbientFace emb.faces,
      f ∈ parentData.interiorData.peelFaces →
        f ∉
            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).peelFaces →
          ∃ e ∈ emb.faceBoundary f.1,
            e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (hcurrentOuterBoundaryNonempty :
      ∀ i :
          Fin
            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).numCollars,
        0 < i.1 →
          ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).currentOuterBoundary i).Nonempty)
    (hcurrentOuterBoundaryDisjoint :
      ∀ {i j :
          Fin
            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).numCollars},
        0 < i.1 → 0 < j.1 → i ≠ j →
          Disjoint
            ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).currentOuterBoundary i)
            ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).currentOuterBoundary j)) :
    ¬ Nonempty
      (Theorem49ForcingInteriorEdgeObstruction.ForcingInteriorEdgeWitness emb) := by
  exact
    Theorem49ForcingInteriorEdgeObstruction.not_nonempty_forcingInteriorEdgeWitness_of_planarBoundaryAnnulusConstructionBoundarySupportFaceData
      (planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_closedWalkEmbeddingData_and_selectedBoundaryArcOnFace_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary
        source.boundaryReachability
        source.closedWalks
        source.selectedBoundaryArc
        parentData
        (by
          simpa [PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData]
            using hparentBoundary)
        hselectorDeficitSelectedBoundary
        hcurrentOuterBoundaryNonempty
        hcurrentOuterBoundaryDisjoint)

/-- Successor-cycle form of the same exact-v23/v23.5 forcing-edge repair. This matches the
boundary-order shell used by the current live route: same-split parent peel data plus the exact
selector-deficit and positive current-outer-boundary hypotheses suffice to rule out forcing
interior edges. -/
theorem
    not_nonempty_forcingInteriorEdgeWitness_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (C₀ : G.EdgeColoring Color)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary))
    (parentData : PlanarBoundaryAnnulusRootParentPeelData emb)
    (hparentBoundary :
      parentData.boundaryData = boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (hselectorDeficitSelectedBoundary : ∀ f : AmbientFace emb.faces,
      f ∈ parentData.interiorData.peelFaces →
        f ∉
            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).peelFaces →
          ∃ e ∈ emb.faceBoundary f.1,
            e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (hcurrentOuterBoundaryNonempty :
      ∀ i :
          Fin
            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).numCollars,
        0 < i.1 →
          ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).currentOuterBoundary i).Nonempty)
    (hcurrentOuterBoundaryDisjoint :
      ∀ {i j :
          Fin
            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).numCollars},
        0 < i.1 → 0 < j.1 → i ≠ j →
          Disjoint
            ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).currentOuterBoundary i)
            ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).currentOuterBoundary j)) :
    ¬ Nonempty
      (Theorem49ForcingInteriorEdgeObstruction.ForcingInteriorEdgeWitness emb) := by
  exact
    Theorem49ForcingInteriorEdgeObstruction.not_nonempty_forcingInteriorEdgeWitness_of_planarBoundaryAnnulusConstructionBoundarySupportFaceData
      (planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary
        boundaryData
        dartCycles
        hselectedBoundaryArc
        parentData
        hparentBoundary
        hselectorDeficitSelectedBoundary
        hcurrentOuterBoundaryNonempty
        hcurrentOuterBoundaryDisjoint)

/-- The construction face-layer shell already lowers to a real annulus decomposition on the same
embedding. This is the smallest downstream construction package needed before witness ownership
can finish the theorem-4.9 route. -/
theorem nonempty_planarBoundaryAnnulusDecomposition_of_planarBoundaryAnnulusConstructionFaceLayerData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstructionFaceLayerData emb) :
    Nonempty (PlanarBoundaryAnnulusDecomposition emb) := by
  exact ⟨data.toPlanarBoundaryAnnulusFaceLayerData.toPlanarBoundaryAnnulusDecomposition⟩

/-- Once the repaired route reaches construction face-layer data, the only remaining theorem-4.9
burden is witness ownership on the exact annulus decomposition canonically induced by that
construction shell. -/
theorem
    theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusConstructionFaceLayerData_and_inducedDecompositionWitnessAssignment
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstructionFaceLayerData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (hwitness :
      Nonempty
        (PlanarBoundaryAnnulusWitnessAssignment
          data.toPlanarBoundaryAnnulusFaceLayerData.toPlanarBoundaryAnnulusDecomposition)) :
    Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases hwitness with ⟨witnessData⟩
  exact theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusWitnessAssignment witnessData C₀ hC₀

/-- Once the repaired route reaches construction face-layer data, the only remaining theorem-4.9
burden is witness ownership on the resulting annulus decomposition. -/
theorem
    theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusConstructionFaceLayerData_and_resultingDecompositionWitnessAssignment
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstructionFaceLayerData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (hwitness :
      let decomp : PlanarBoundaryAnnulusDecomposition emb :=
        Classical.choice
          (nonempty_planarBoundaryAnnulusDecomposition_of_planarBoundaryAnnulusConstructionFaceLayerData
            data)
      Nonempty (PlanarBoundaryAnnulusWitnessAssignment decomp)) :
    Theorem49BoundaryRootSynthesis emb C₀ := by
  classical
  let decomp : PlanarBoundaryAnnulusDecomposition emb :=
    Classical.choice
      (nonempty_planarBoundaryAnnulusDecomposition_of_planarBoundaryAnnulusConstructionFaceLayerData
        data)
  have hwitness' : Nonempty (PlanarBoundaryAnnulusWitnessAssignment decomp) := by
    simpa [decomp] using hwitness
  rcases hwitness' with ⟨witnessData⟩
  exact theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusWitnessAssignment witnessData C₀ hC₀

/-- The selected-boundary construction shell already lowers to a real annulus decomposition on the
same embedding. This isolates the positive current-outer-boundary obligations at the exact shell
where they enter the proof route. -/
theorem nonempty_planarBoundaryAnnulusDecomposition_of_planarBoundaryAnnulusConstructionBoundarySupportFaceData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb) :
    Nonempty (PlanarBoundaryAnnulusDecomposition emb) := by
  exact
    nonempty_planarBoundaryAnnulusDecomposition_of_planarBoundaryAnnulusConstructionFaceLayerData
      data.toPlanarBoundaryAnnulusConstructionFaceLayerData

/-- Once the repaired construction-side selected-boundary shell is present, the only remaining
theorem-4.9 burden is witness ownership on the exact annulus decomposition canonically induced by
that shell. -/
theorem
    theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusConstructionBoundarySupportFaceData_and_inducedDecompositionWitnessAssignment
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (hwitness :
      Nonempty
        (PlanarBoundaryAnnulusWitnessAssignment
          data.toPlanarBoundaryAnnulusFaceLayerData.toPlanarBoundaryAnnulusDecomposition)) :
    Theorem49BoundaryRootSynthesis emb C₀ := by
  exact
    theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusConstructionFaceLayerData_and_inducedDecompositionWitnessAssignment
      data.toPlanarBoundaryAnnulusConstructionFaceLayerData C₀ hC₀ hwitness

/-- Once the repaired construction-side selected-boundary shell is present, the only remaining
theorem-4.9 burden is witness ownership on the resulting annulus decomposition. -/
theorem
    theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusConstructionBoundarySupportFaceData_and_resultingDecompositionWitnessAssignment
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (hwitness :
      let decomp : PlanarBoundaryAnnulusDecomposition emb :=
        Classical.choice
          (nonempty_planarBoundaryAnnulusDecomposition_of_planarBoundaryAnnulusConstructionBoundarySupportFaceData
            data)
      Nonempty (PlanarBoundaryAnnulusWitnessAssignment decomp)) :
    Theorem49BoundaryRootSynthesis emb C₀ := by
  exact
    theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusConstructionFaceLayerData_and_resultingDecompositionWitnessAssignment
      data.toPlanarBoundaryAnnulusConstructionFaceLayerData C₀ hC₀
      (by
        simpa using hwitness)

/-- Direct selector-side theorem-4.9 route package on the actual boundary-order shell. Once
boundary reachability plus facewise selected-boundary arcs already support a boundary-free
selector with the local selected-boundary-contact and positive current-outer-boundary conditions,
the canonical annulus decomposition induced by that selector is already the exact remaining
carrier for witness ownership. -/
theorem
    theorem49BoundaryRootSynthesis_of_boundaryReachabilityData_and_closedWalkEmbeddingData_and_selectedBoundaryArcOnFace_and_boundaryFreeIncidentFaceSelector_and_boundarySupportFaceData_conditions_and_inducedDecompositionWitnessAssignment
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (boundaryGeom : PlanarBoundaryClosedWalkEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (boundaryGeom.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (selector : BoundaryFreeIncidentFaceSelector emb)
    (fallbackEdge : AmbientFace emb.faces → G.edgeSet)
    (faceDistance : AmbientFace emb.faces → ℕ)
    (hinjective :
      ∀ {e₁ e₂ : G.edgeSet}
        (he₁ : e₁ ∈ interiorEdgeSupport emb.faceBoundary emb.faces)
        (he₂ : e₂ ∈ interiorEdgeSupport emb.faceBoundary emb.faces),
          selector.faceOf e₁ he₁ = selector.faceOf e₂ he₂ → e₁ = e₂)
    (hrest :
      ∀ f ∈ selector.peelFaces,
        ∀ e ∈ (emb.faceBoundary f.1).erase (selector.selectedWitnessEdge fallbackEdge f),
          e ∈
              boundaryData.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                boundaryData.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary ∨
            ∃ g ∈ selector.peelFaces,
              selector.selectedWitnessEdge fallbackEdge g = e ∧
                faceDistance f < faceDistance g)
    (hnonPeelSelectedBoundary : ∀ f : AmbientFace emb.faces,
      f ∉ selector.peelFaces →
        ∃ e ∈ emb.faceBoundary f.1,
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (hcurrentOuterBoundaryNonempty :
      ∀ i :
          Fin
            (selector.toPlanarBoundaryAnnulusConstruction
              boundaryData.toPlanarBoundaryAnnulusBoundaryData
              fallbackEdge faceDistance hinjective hrest).numCollars,
        0 < i.1 →
          ((selector.toPlanarBoundaryAnnulusConstruction
              boundaryData.toPlanarBoundaryAnnulusBoundaryData
              fallbackEdge faceDistance hinjective hrest).currentOuterBoundary i).Nonempty)
    (hcurrentOuterBoundaryDisjoint :
      ∀ {i j :
          Fin
            (selector.toPlanarBoundaryAnnulusConstruction
              boundaryData.toPlanarBoundaryAnnulusBoundaryData
              fallbackEdge faceDistance hinjective hrest).numCollars},
        0 < i.1 → 0 < j.1 → i ≠ j →
          Disjoint
            ((selector.toPlanarBoundaryAnnulusConstruction
                boundaryData.toPlanarBoundaryAnnulusBoundaryData
                fallbackEdge faceDistance hinjective hrest).currentOuterBoundary i)
            ((selector.toPlanarBoundaryAnnulusConstruction
                boundaryData.toPlanarBoundaryAnnulusBoundaryData
                fallbackEdge faceDistance hinjective hrest).currentOuterBoundary j))
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (hwitness :
      let supportData :=
        selector.toPlanarBoundaryAnnulusConstructionBoundarySupportFaceData
          boundaryData.toPlanarBoundaryAnnulusBoundaryData
          fallbackEdge
          faceDistance
          hinjective
          hrest
          hnonPeelSelectedBoundary
          (by
            intro f
            exact
              boundaryData.boundaryFaceSeparated_of_closedWalkEmbeddingData_and_selectedBoundaryArcOnFace
                boundaryGeom hboundaryArc (f := f))
          hcurrentOuterBoundaryNonempty
          hcurrentOuterBoundaryDisjoint
      Nonempty
        (PlanarBoundaryAnnulusWitnessAssignment
          supportData.toPlanarBoundaryAnnulusFaceLayerData.toPlanarBoundaryAnnulusDecomposition)) :
    Theorem49BoundaryRootSynthesis emb C₀ := by
  classical
  let supportData : PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb :=
    selector.toPlanarBoundaryAnnulusConstructionBoundarySupportFaceData
      boundaryData.toPlanarBoundaryAnnulusBoundaryData
      fallbackEdge
      faceDistance
      hinjective
      hrest
      hnonPeelSelectedBoundary
      (by
        intro f
        exact
          boundaryData.boundaryFaceSeparated_of_closedWalkEmbeddingData_and_selectedBoundaryArcOnFace
            boundaryGeom hboundaryArc (f := f))
      hcurrentOuterBoundaryNonempty
      hcurrentOuterBoundaryDisjoint
  have hwitness' :
      Nonempty
        (PlanarBoundaryAnnulusWitnessAssignment
          supportData.toPlanarBoundaryAnnulusFaceLayerData.toPlanarBoundaryAnnulusDecomposition) := by
    simpa [supportData] using hwitness
  exact
    theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusConstructionBoundarySupportFaceData_and_inducedDecompositionWitnessAssignment
      supportData C₀ hC₀ hwitness'

/-- Route-facing successor-cycle form of the same selector-side theorem-4.9 synthesis closure.
Once the actual boundary-order shell supports the local boundary-free selector package, the exact
remaining burden is witness ownership on the selector-induced annulus decomposition itself. -/
theorem
    theorem49BoundaryRootSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFreeIncidentFaceSelector_and_boundarySupportFaceData_conditions_and_inducedDecompositionWitnessAssignment
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (selector : BoundaryFreeIncidentFaceSelector emb)
    (fallbackEdge : AmbientFace emb.faces → G.edgeSet)
    (faceDistance : AmbientFace emb.faces → ℕ)
    (hinjective :
      ∀ {e₁ e₂ : G.edgeSet}
        (he₁ : e₁ ∈ interiorEdgeSupport emb.faceBoundary emb.faces)
        (he₂ : e₂ ∈ interiorEdgeSupport emb.faceBoundary emb.faces),
          selector.faceOf e₁ he₁ = selector.faceOf e₂ he₂ → e₁ = e₂)
    (hrest :
      ∀ f ∈ selector.peelFaces,
        ∀ e ∈ (emb.faceBoundary f.1).erase (selector.selectedWitnessEdge fallbackEdge f),
          e ∈
              boundaryData.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                boundaryData.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary ∨
            ∃ g ∈ selector.peelFaces,
              selector.selectedWitnessEdge fallbackEdge g = e ∧
                faceDistance f < faceDistance g)
    (hnonPeelSelectedBoundary : ∀ f : AmbientFace emb.faces,
      f ∉ selector.peelFaces →
        ∃ e ∈ emb.faceBoundary f.1,
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (hcurrentOuterBoundaryNonempty :
      ∀ i :
          Fin
            (selector.toPlanarBoundaryAnnulusConstruction
              boundaryData.toPlanarBoundaryAnnulusBoundaryData
              fallbackEdge faceDistance hinjective hrest).numCollars,
        0 < i.1 →
          ((selector.toPlanarBoundaryAnnulusConstruction
              boundaryData.toPlanarBoundaryAnnulusBoundaryData
              fallbackEdge faceDistance hinjective hrest).currentOuterBoundary i).Nonempty)
    (hcurrentOuterBoundaryDisjoint :
      ∀ {i j :
          Fin
            (selector.toPlanarBoundaryAnnulusConstruction
              boundaryData.toPlanarBoundaryAnnulusBoundaryData
              fallbackEdge faceDistance hinjective hrest).numCollars},
        0 < i.1 → 0 < j.1 → i ≠ j →
          Disjoint
            ((selector.toPlanarBoundaryAnnulusConstruction
                boundaryData.toPlanarBoundaryAnnulusBoundaryData
                fallbackEdge faceDistance hinjective hrest).currentOuterBoundary i)
            ((selector.toPlanarBoundaryAnnulusConstruction
                boundaryData.toPlanarBoundaryAnnulusBoundaryData
                fallbackEdge faceDistance hinjective hrest).currentOuterBoundary j))
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (hwitness :
      let supportData :=
        selector.toPlanarBoundaryAnnulusConstructionBoundarySupportFaceData
          boundaryData.toPlanarBoundaryAnnulusBoundaryData
          fallbackEdge
          faceDistance
          hinjective
          hrest
          hnonPeelSelectedBoundary
          (by
            intro f
            exact
              boundaryData.boundaryFaceSeparated_of_closedWalkEmbeddingData_and_selectedBoundaryArcOnFace
                dartCycles.toPlanarBoundaryClosedWalkEmbeddingData hselectedBoundaryArc (f := f))
          hcurrentOuterBoundaryNonempty
          hcurrentOuterBoundaryDisjoint
      Nonempty
        (PlanarBoundaryAnnulusWitnessAssignment
          supportData.toPlanarBoundaryAnnulusFaceLayerData.toPlanarBoundaryAnnulusDecomposition)) :
    Theorem49BoundaryRootSynthesis emb C₀ := by
  exact
    theorem49BoundaryRootSynthesis_of_boundaryReachabilityData_and_closedWalkEmbeddingData_and_selectedBoundaryArcOnFace_and_boundaryFreeIncidentFaceSelector_and_boundarySupportFaceData_conditions_and_inducedDecompositionWitnessAssignment
      boundaryData
      dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
      hselectedBoundaryArc
      selector
      fallbackEdge
      faceDistance
      hinjective
      hrest
      hnonPeelSelectedBoundary
      hcurrentOuterBoundaryNonempty
      hcurrentOuterBoundaryDisjoint
      C₀
      hC₀
      hwitness

/-- Direct selector-side theorem-4.9 route package on the actual boundary-order shell. Once
boundary reachability plus facewise selected-boundary arcs already support a boundary-free
selector with the local selected-boundary-contact and positive current-outer-boundary conditions,
the only remaining burden is witness ownership on the annulus decomposition induced by that
selector-side construction package. -/
theorem
    theorem49BoundaryRootSynthesis_of_boundaryReachabilityData_and_closedWalkEmbeddingData_and_selectedBoundaryArcOnFace_and_boundaryFreeIncidentFaceSelector_and_boundarySupportFaceData_conditions_and_resultingDecompositionWitnessAssignment
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (boundaryGeom : PlanarBoundaryClosedWalkEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (boundaryGeom.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (selector : BoundaryFreeIncidentFaceSelector emb)
    (fallbackEdge : AmbientFace emb.faces → G.edgeSet)
    (faceDistance : AmbientFace emb.faces → ℕ)
    (hinjective :
      ∀ {e₁ e₂ : G.edgeSet}
        (he₁ : e₁ ∈ interiorEdgeSupport emb.faceBoundary emb.faces)
        (he₂ : e₂ ∈ interiorEdgeSupport emb.faceBoundary emb.faces),
          selector.faceOf e₁ he₁ = selector.faceOf e₂ he₂ → e₁ = e₂)
    (hrest :
      ∀ f ∈ selector.peelFaces,
        ∀ e ∈ (emb.faceBoundary f.1).erase (selector.selectedWitnessEdge fallbackEdge f),
          e ∈
              boundaryData.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                boundaryData.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary ∨
            ∃ g ∈ selector.peelFaces,
              selector.selectedWitnessEdge fallbackEdge g = e ∧
                faceDistance f < faceDistance g)
    (hnonPeelSelectedBoundary : ∀ f : AmbientFace emb.faces,
      f ∉ selector.peelFaces →
        ∃ e ∈ emb.faceBoundary f.1,
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (hcurrentOuterBoundaryNonempty :
      ∀ i :
          Fin
            (selector.toPlanarBoundaryAnnulusConstruction
              boundaryData.toPlanarBoundaryAnnulusBoundaryData
              fallbackEdge faceDistance hinjective hrest).numCollars,
        0 < i.1 →
          ((selector.toPlanarBoundaryAnnulusConstruction
              boundaryData.toPlanarBoundaryAnnulusBoundaryData
              fallbackEdge faceDistance hinjective hrest).currentOuterBoundary i).Nonempty)
    (hcurrentOuterBoundaryDisjoint :
      ∀ {i j :
          Fin
            (selector.toPlanarBoundaryAnnulusConstruction
              boundaryData.toPlanarBoundaryAnnulusBoundaryData
              fallbackEdge faceDistance hinjective hrest).numCollars},
        0 < i.1 → 0 < j.1 → i ≠ j →
          Disjoint
            ((selector.toPlanarBoundaryAnnulusConstruction
                boundaryData.toPlanarBoundaryAnnulusBoundaryData
                fallbackEdge faceDistance hinjective hrest).currentOuterBoundary i)
            ((selector.toPlanarBoundaryAnnulusConstruction
                boundaryData.toPlanarBoundaryAnnulusBoundaryData
                fallbackEdge faceDistance hinjective hrest).currentOuterBoundary j))
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (hwitness :
      let supportData :=
        selector.toPlanarBoundaryAnnulusConstructionBoundarySupportFaceData
          boundaryData.toPlanarBoundaryAnnulusBoundaryData
          fallbackEdge
          faceDistance
          hinjective
          hrest
          hnonPeelSelectedBoundary
          (by
            intro f
            exact
              boundaryData.boundaryFaceSeparated_of_closedWalkEmbeddingData_and_selectedBoundaryArcOnFace
                boundaryGeom hboundaryArc (f := f))
          hcurrentOuterBoundaryNonempty
          hcurrentOuterBoundaryDisjoint
      let decomp : PlanarBoundaryAnnulusDecomposition emb :=
        Classical.choice
          (nonempty_planarBoundaryAnnulusDecomposition_of_planarBoundaryAnnulusConstructionBoundarySupportFaceData
            supportData)
      Nonempty (PlanarBoundaryAnnulusWitnessAssignment decomp)) :
    Theorem49BoundaryRootSynthesis emb C₀ := by
  classical
  let supportData : PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb :=
    selector.toPlanarBoundaryAnnulusConstructionBoundarySupportFaceData
      boundaryData.toPlanarBoundaryAnnulusBoundaryData
      fallbackEdge
      faceDistance
      hinjective
      hrest
      hnonPeelSelectedBoundary
      (by
        intro f
        exact
          boundaryData.boundaryFaceSeparated_of_closedWalkEmbeddingData_and_selectedBoundaryArcOnFace
            boundaryGeom hboundaryArc (f := f))
      hcurrentOuterBoundaryNonempty
      hcurrentOuterBoundaryDisjoint
  exact
    theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusConstructionBoundarySupportFaceData_and_resultingDecompositionWitnessAssignment
      supportData C₀ hC₀
      (by
        simpa [supportData] using hwitness)

/-- Honest closed-walk source data plus same-embedding construction face-layer data already give
the graph-level theorem-4.9 synthesis endpoint once the resulting annulus decomposition carries a
witness assignment. -/
theorem
    exists_theorem49BoundaryRootSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_planarBoundaryAnnulusConstructionFaceLayerData_and_resultingDecompositionWitnessAssignment_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ data : PlanarBoundaryAnnulusConstructionFaceLayerData emb,
        let decomp : PlanarBoundaryAnnulusDecomposition emb :=
          Classical.choice
            (nonempty_planarBoundaryAnnulusDecomposition_of_planarBoundaryAnnulusConstructionFaceLayerData
              data)
        Nonempty (PlanarBoundaryAnnulusWitnessAssignment decomp))
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases hG with ⟨emb, _source, data, hwitness⟩
  exact
    ⟨emb,
      theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusConstructionFaceLayerData_and_resultingDecompositionWitnessAssignment
        data C₀ hC₀ hwitness⟩

/-- The stronger selected-boundary-contact construction shell lowers to the same graph-level
theorem-4.9 synthesis endpoint once the resulting annulus decomposition carries witness
ownership. -/
theorem
    exists_theorem49BoundaryRootSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_planarBoundaryAnnulusConstructionBoundarySupportFaceData_and_resultingDecompositionWitnessAssignment_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ data : PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb,
        let decomp : PlanarBoundaryAnnulusDecomposition emb :=
          Classical.choice
            (nonempty_planarBoundaryAnnulusDecomposition_of_planarBoundaryAnnulusConstructionBoundarySupportFaceData
              data)
        Nonempty (PlanarBoundaryAnnulusWitnessAssignment decomp))
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases hG with ⟨emb, _source, data, hwitness⟩
  exact
    ⟨emb,
      theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusConstructionBoundarySupportFaceData_and_resultingDecompositionWitnessAssignment
        data C₀ hC₀ hwitness⟩

/-- Successor-cycle boundary-order data plus same-embedding construction face-layer data already
give the graph-level theorem-4.9 synthesis endpoint once the resulting annulus decomposition
carries witness ownership. -/
theorem
    exists_theorem49BoundaryRootSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_planarBoundaryAnnulusConstructionFaceLayerData_and_resultingDecompositionWitnessAssignment_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ data : PlanarBoundaryAnnulusConstructionFaceLayerData emb,
        let decomp : PlanarBoundaryAnnulusDecomposition emb :=
          Classical.choice
            (nonempty_planarBoundaryAnnulusDecomposition_of_planarBoundaryAnnulusConstructionFaceLayerData
              data)
        ∃ _ : PlanarBoundaryAnnulusWitnessAssignment decomp,
          ∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases hG with ⟨emb, _boundaryData, dartCycles, data, hwitness, hselectedBoundaryArc⟩
  exact
    ⟨emb,
      theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusConstructionFaceLayerData_and_resultingDecompositionWitnessAssignment
        data C₀ hC₀ ⟨hwitness⟩⟩

/-- The stronger selected-boundary-contact successor-cycle shell lowers to the same graph-level
theorem-4.9 synthesis endpoint once the resulting annulus decomposition carries witness
ownership. -/
theorem
    exists_theorem49BoundaryRootSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_planarBoundaryAnnulusConstructionBoundarySupportFaceData_and_resultingDecompositionWitnessAssignment_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ data : PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb,
        let decomp : PlanarBoundaryAnnulusDecomposition emb :=
          Classical.choice
            (nonempty_planarBoundaryAnnulusDecomposition_of_planarBoundaryAnnulusConstructionBoundarySupportFaceData
              data)
        ∃ _ : PlanarBoundaryAnnulusWitnessAssignment decomp,
          ∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases hG with ⟨emb, _boundaryData, dartCycles, data, hwitness, hselectedBoundaryArc⟩
  exact
    ⟨emb,
      theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusConstructionBoundarySupportFaceData_and_resultingDecompositionWitnessAssignment
        data C₀ hC₀ ⟨hwitness⟩⟩

/-- The actual successor-cycle boundary-order selector package already gives the graph-level
theorem-4.9 synthesis endpoint once its exact selector-induced annulus decomposition carries
witness ownership. This is the direct graph-level closure for the live local route package,
without lowering through a chosen decomposition surrogate. -/
theorem
    exists_theorem49BoundaryRootSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFreeIncidentFaceSelector_and_boundarySupportFaceData_conditions_and_inducedDecompositionWitnessAssignment_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
        (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ selector : BoundaryFreeIncidentFaceSelector emb,
      ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
      ∃ faceDistance : AmbientFace emb.faces → ℕ,
      ∃ hinjective :
        ∀ {e₁ e₂ : G.edgeSet}
          (he₁ : e₁ ∈ interiorEdgeSupport emb.faceBoundary emb.faces)
          (he₂ : e₂ ∈ interiorEdgeSupport emb.faceBoundary emb.faces),
            selector.faceOf e₁ he₁ = selector.faceOf e₂ he₂ → e₁ = e₂,
      ∃ hrest :
        ∀ f ∈ selector.peelFaces,
          ∀ e ∈ (emb.faceBoundary f.1).erase (selector.selectedWitnessEdge fallbackEdge f),
            e ∈
                boundaryData.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                  boundaryData.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary ∨
              ∃ g ∈ selector.peelFaces,
                selector.selectedWitnessEdge fallbackEdge g = e ∧
                  faceDistance f < faceDistance g,
      ∃ hnonPeelSelectedBoundary : ∀ f : AmbientFace emb.faces,
        f ∉ selector.peelFaces →
          ∃ e ∈ emb.faceBoundary f.1,
            e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces,
      ∃ hcurrentOuterBoundaryNonempty :
        ∀ i :
            Fin
              (selector.toPlanarBoundaryAnnulusConstruction
                boundaryData.toPlanarBoundaryAnnulusBoundaryData
                fallbackEdge faceDistance hinjective hrest).numCollars,
          0 < i.1 →
            ((selector.toPlanarBoundaryAnnulusConstruction
                boundaryData.toPlanarBoundaryAnnulusBoundaryData
                fallbackEdge faceDistance hinjective hrest).currentOuterBoundary i).Nonempty,
      ∃ hcurrentOuterBoundaryDisjoint :
        ∀ {i j :
            Fin
              (selector.toPlanarBoundaryAnnulusConstruction
                boundaryData.toPlanarBoundaryAnnulusBoundaryData
                fallbackEdge faceDistance hinjective hrest).numCollars},
          0 < i.1 → 0 < j.1 → i ≠ j →
            Disjoint
              ((selector.toPlanarBoundaryAnnulusConstruction
                  boundaryData.toPlanarBoundaryAnnulusBoundaryData
                  fallbackEdge faceDistance hinjective hrest).currentOuterBoundary i)
              ((selector.toPlanarBoundaryAnnulusConstruction
                  boundaryData.toPlanarBoundaryAnnulusBoundaryData
                  fallbackEdge faceDistance hinjective hrest).currentOuterBoundary j),
      let supportData :=
        selector.toPlanarBoundaryAnnulusConstructionBoundarySupportFaceData
          boundaryData.toPlanarBoundaryAnnulusBoundaryData
          fallbackEdge
          faceDistance
          hinjective
          hrest
          hnonPeelSelectedBoundary
          (by
            intro f
            exact
              boundaryData.boundaryFaceSeparated_of_closedWalkEmbeddingData_and_selectedBoundaryArcOnFace
                dartCycles.toPlanarBoundaryClosedWalkEmbeddingData hselectedBoundaryArc (f := f))
          hcurrentOuterBoundaryNonempty
          hcurrentOuterBoundaryDisjoint
      Nonempty
        (PlanarBoundaryAnnulusWitnessAssignment
          supportData.toPlanarBoundaryAnnulusFaceLayerData.toPlanarBoundaryAnnulusDecomposition))
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases hG with
    ⟨emb, boundaryData, dartCycles, hselectedBoundaryArc, selector, fallbackEdge, faceDistance,
      hinjective, hrest, hnonPeelSelectedBoundary, hcurrentOuterBoundaryNonempty,
      hcurrentOuterBoundaryDisjoint, hwitness⟩
  exact
    ⟨emb,
      theorem49BoundaryRootSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFreeIncidentFaceSelector_and_boundarySupportFaceData_conditions_and_inducedDecompositionWitnessAssignment
        boundaryData
        dartCycles
        hselectedBoundaryArc
        selector
        fallbackEdge
        faceDistance
        hinjective
        hrest
        hnonPeelSelectedBoundary
        hcurrentOuterBoundaryNonempty
        hcurrentOuterBoundaryDisjoint
        C₀
        hC₀
        hwitness⟩

/-- Exact-v23/v23.5 constructive shell repair on the honest closed-walk route: under the same
same-split parent-peel and selector-deficit hypotheses that already lower to the selected-boundary
construction shell, the exact one-collar residual package also reaches the downstream
construction-side face-layer data used by annulus decomposition. -/
theorem
    nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          source.toPlanarBoundaryAnnulusBoundaryData)
    (C₀ : G.EdgeColoring Color)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary))
    (parentData : PlanarBoundaryAnnulusRootParentPeelData emb)
    (hparentBoundary :
      parentData.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData)
    (hselectorDeficitSelectedBoundary : ∀ f : AmbientFace emb.faces,
      f ∈ parentData.interiorData.peelFaces →
        f ∉
            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).peelFaces →
          ∃ e ∈ emb.faceBoundary f.1,
            e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (hcurrentOuterBoundaryNonempty :
      ∀ i :
          Fin
            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).numCollars,
        0 < i.1 →
          ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).currentOuterBoundary i).Nonempty)
    (hcurrentOuterBoundaryDisjoint :
      ∀ {i j :
          Fin
            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).numCollars},
        0 < i.1 → 0 < j.1 → i ≠ j →
          Disjoint
            ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).currentOuterBoundary i)
            ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).currentOuterBoundary j)) :
    Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb) := by
  refine ⟨?_⟩
  exact
    (planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_closedWalkEmbeddingData_and_selectedBoundaryArcOnFace_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary
      source.boundaryReachability
      source.closedWalks
      source.selectedBoundaryArc
      parentData
      (by
        simpa [PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData]
          using hparentBoundary)
      hselectorDeficitSelectedBoundary
      hcurrentOuterBoundaryNonempty
      hcurrentOuterBoundaryDisjoint).toPlanarBoundaryAnnulusConstructionFaceLayerData

/-- Successor-cycle form of the same exact-v23/v23.5 constructive shell repair. This matches the
current boundary-order interface: the one-collar residual shell already reaches
`PlanarBoundaryAnnulusConstructionFaceLayerData` once the same-split parent-peel and
selector-deficit package is supplied. -/
theorem
    nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (C₀ : G.EdgeColoring Color)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary))
    (parentData : PlanarBoundaryAnnulusRootParentPeelData emb)
    (hparentBoundary :
      parentData.boundaryData = boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (hselectorDeficitSelectedBoundary : ∀ f : AmbientFace emb.faces,
      f ∈ parentData.interiorData.peelFaces →
        f ∉
            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).peelFaces →
          ∃ e ∈ emb.faceBoundary f.1,
            e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (hcurrentOuterBoundaryNonempty :
      ∀ i :
          Fin
            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).numCollars,
        0 < i.1 →
          ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).currentOuterBoundary i).Nonempty)
    (hcurrentOuterBoundaryDisjoint :
      ∀ {i j :
          Fin
            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).numCollars},
        0 < i.1 → 0 < j.1 → i ≠ j →
          Disjoint
            ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).currentOuterBoundary i)
            ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).currentOuterBoundary j)) :
    Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb) := by
  refine ⟨?_⟩
  exact
    (planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary
      boundaryData
      dartCycles
      hselectedBoundaryArc
      parentData
      hparentBoundary
      hselectorDeficitSelectedBoundary
      hcurrentOuterBoundaryNonempty
      hcurrentOuterBoundaryDisjoint).toPlanarBoundaryAnnulusConstructionFaceLayerData

/-- The repaired exact closed-walk shell is still inconsistent if it asks for the old positive
current-outer-boundary side conditions on the same parent-peel construction.  The selector-driven
parent construction is already parent-oriented, while any resulting selected-boundary-support
construction shell forbids parent orientation on that same construction. -/
theorem
    false_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary_and_currentOuterBoundary
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          source.toPlanarBoundaryAnnulusBoundaryData)
    (C₀ : G.EdgeColoring Color)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary))
    (parentData : PlanarBoundaryAnnulusRootParentPeelData emb)
    (hparentBoundary :
      parentData.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData)
    (hselectorDeficitSelectedBoundary : ∀ f : AmbientFace emb.faces,
      f ∈ parentData.interiorData.peelFaces →
        f ∉
            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).peelFaces →
          ∃ e ∈ emb.faceBoundary f.1,
            e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (hcurrentOuterBoundaryNonempty :
      ∀ i :
          Fin
            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).numCollars,
        0 < i.1 →
          ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).currentOuterBoundary i).Nonempty)
    (hcurrentOuterBoundaryDisjoint :
      ∀ {i j :
          Fin
            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).numCollars},
        0 < i.1 → 0 < j.1 → i ≠ j →
          Disjoint
            ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).currentOuterBoundary i)
            ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).currentOuterBoundary j)) :
    False := by
  exact
    false_of_boundaryReachabilityData_and_closedWalkEmbeddingData_and_selectedBoundaryArcOnFace_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary_and_currentOuterBoundary
      source.boundaryReachability source.closedWalks source.selectedBoundaryArc
      parentData
      (by
        simpa [PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData]
          using hparentBoundary)
      hselectorDeficitSelectedBoundary
      hcurrentOuterBoundaryNonempty
      hcurrentOuterBoundaryDisjoint

/-- Successor-cycle form of the same exact-shell inconsistency.  This is the current
boundary-order interface, so it records directly that the repaired one-collar shell cannot keep
the older positive current-boundary package together with same-embedding parent-peel data. -/
theorem
    false_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary_and_currentOuterBoundary
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (C₀ : G.EdgeColoring Color)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary))
    (parentData : PlanarBoundaryAnnulusRootParentPeelData emb)
    (hparentBoundary :
      parentData.boundaryData = boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (hselectorDeficitSelectedBoundary : ∀ f : AmbientFace emb.faces,
      f ∈ parentData.interiorData.peelFaces →
        f ∉
            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).peelFaces →
          ∃ e ∈ emb.faceBoundary f.1,
            e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (hcurrentOuterBoundaryNonempty :
      ∀ i :
          Fin
            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).numCollars,
        0 < i.1 →
          ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).currentOuterBoundary i).Nonempty)
    (hcurrentOuterBoundaryDisjoint :
      ∀ {i j :
          Fin
            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).numCollars},
        0 < i.1 → 0 < j.1 → i ≠ j →
          Disjoint
            ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).currentOuterBoundary i)
            ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).currentOuterBoundary j)) :
    False := by
  exact
    false_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary_and_currentOuterBoundary
      boundaryData dartCycles hselectedBoundaryArc parentData hparentBoundary
      hselectorDeficitSelectedBoundary hcurrentOuterBoundaryNonempty
      hcurrentOuterBoundaryDisjoint

/-- The stronger exact closed-walk repair branch is inconsistent too: replacing the
selector-deficit premise by the older non-peeled-face selected-boundary contact hypothesis still
cannot coexist with the positive current-outer-boundary side conditions on the same parent-peel
construction. -/
theorem
    false_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_nonPeelSelectedBoundary_and_currentOuterBoundary
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          source.toPlanarBoundaryAnnulusBoundaryData)
    (C₀ : G.EdgeColoring Color)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary))
    (parentData : PlanarBoundaryAnnulusRootParentPeelData emb)
    (hparentBoundary :
      parentData.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData)
    (hnonPeelSelectedBoundary : ∀ f : AmbientFace emb.faces,
      f ∉
          (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
            parentData).peelFaces →
        ∃ e ∈ emb.faceBoundary f.1,
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (hcurrentOuterBoundaryNonempty :
      ∀ i :
          Fin
            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).numCollars,
        0 < i.1 →
          ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).currentOuterBoundary i).Nonempty)
    (hcurrentOuterBoundaryDisjoint :
      ∀ {i j :
          Fin
            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).numCollars},
        0 < i.1 → 0 < j.1 → i ≠ j →
          Disjoint
            ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).currentOuterBoundary i)
            ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).currentOuterBoundary j)) :
    False := by
  let hselectorDeficitSelectedBoundary :=
    selectorDeficitSelectedBoundary_of_planarBoundaryAnnulusRootParentPeelData_and_nonPeelSelectedBoundary
      parentData hnonPeelSelectedBoundary
  exact
    false_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary_and_currentOuterBoundary
      source _hcurrent C₀ (a := a) (b := b) (faceBoundary := faceBoundary) _hv23
      parentData hparentBoundary hselectorDeficitSelectedBoundary
      hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint

/-- Successor-cycle form of the same stronger exact-shell inconsistency.  So even the older
non-peeled-face selected-boundary-contact repair cannot keep the positive current-boundary
side conditions on the live boundary-order shell. -/
theorem
    false_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_nonPeelSelectedBoundary_and_currentOuterBoundary
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (C₀ : G.EdgeColoring Color)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary))
    (parentData : PlanarBoundaryAnnulusRootParentPeelData emb)
    (hparentBoundary :
      parentData.boundaryData = boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (hnonPeelSelectedBoundary : ∀ f : AmbientFace emb.faces,
      f ∉
          (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
            parentData).peelFaces →
        ∃ e ∈ emb.faceBoundary f.1,
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (hcurrentOuterBoundaryNonempty :
      ∀ i :
          Fin
            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).numCollars,
        0 < i.1 →
          ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).currentOuterBoundary i).Nonempty)
    (hcurrentOuterBoundaryDisjoint :
      ∀ {i j :
          Fin
            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).numCollars},
        0 < i.1 → 0 < j.1 → i ≠ j →
          Disjoint
            ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).currentOuterBoundary i)
            ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).currentOuterBoundary j)) :
    False := by
  let hselectorDeficitSelectedBoundary :=
    selectorDeficitSelectedBoundary_of_planarBoundaryAnnulusRootParentPeelData_and_nonPeelSelectedBoundary
      parentData hnonPeelSelectedBoundary
  exact
    false_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary_and_currentOuterBoundary
      boundaryData dartCycles hselectedBoundaryArc _hcurrent C₀
      (a := a) (b := b) (faceBoundary := faceBoundary) _hv23
      parentData hparentBoundary hselectorDeficitSelectedBoundary
      hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint

/-- Graph-level exact-shell obstruction form of the same closed-walk inconsistency.  No
embedding can simultaneously realize honest one-collar closed-walk source data, exact-v23
residual state, same-split parent-peel data, the selector-deficit selected-boundary contact
premise, and the older positive `currentOuterBoundary` side conditions. -/
theorem
    not_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary_and_currentOuterBoundary
    {G : SimpleGraph V} :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            source.toPlanarBoundaryAnnulusBoundaryData,
      ∃ C₀ : G.EdgeColoring Color,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      ∃ parentData : PlanarBoundaryAnnulusRootParentPeelData emb,
        parentData.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData ∧
        (∀ f : AmbientFace emb.faces,
          f ∈ parentData.interiorData.peelFaces →
            f ∉
                (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                  parentData).peelFaces →
              ∃ e ∈ emb.faceBoundary f.1,
                e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) ∧
        (∀ i :
            Fin
              (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).numCollars,
          0 < i.1 →
            ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).currentOuterBoundary i).Nonempty) ∧
        (∀ {i j :
            Fin
              (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).numCollars},
          0 < i.1 → 0 < j.1 → i ≠ j →
            Disjoint
              ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                  parentData).currentOuterBoundary i)
              ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                  parentData).currentOuterBoundary j)) := by
  rintro ⟨emb, source, hcurrent, C₀, a, b, faceBoundary, hv23, parentData, hparentBoundary,
    hselectorDeficitSelectedBoundary, hcurrentOuterBoundaryNonempty,
    hcurrentOuterBoundaryDisjoint⟩
  exact
    false_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary_and_currentOuterBoundary
      source hcurrent C₀ (a := a) (b := b) (faceBoundary := faceBoundary) hv23
      parentData hparentBoundary hselectorDeficitSelectedBoundary
      hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint

/-- Graph-level exact-shell obstruction form of the same successor-cycle inconsistency.  The live
boundary-order one-collar shell cannot realize the repaired parent-peel plus old positive
`currentOuterBoundary` package on any embedding. -/
theorem
    not_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary_and_currentOuterBoundary
    {G : SimpleGraph V} :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
        (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            boundaryData.toPlanarBoundaryAnnulusBoundaryData,
      ∃ C₀ : G.EdgeColoring Color,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      ∃ parentData : PlanarBoundaryAnnulusRootParentPeelData emb,
        parentData.boundaryData = boundaryData.toPlanarBoundaryAnnulusBoundaryData ∧
        (∀ f : AmbientFace emb.faces,
          f ∈ parentData.interiorData.peelFaces →
            f ∉
                (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                  parentData).peelFaces →
              ∃ e ∈ emb.faceBoundary f.1,
                e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) ∧
        (∀ i :
            Fin
              (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).numCollars,
          0 < i.1 →
            ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).currentOuterBoundary i).Nonempty) ∧
        (∀ {i j :
            Fin
              (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).numCollars},
          0 < i.1 → 0 < j.1 → i ≠ j →
            Disjoint
              ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                  parentData).currentOuterBoundary i)
              ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                  parentData).currentOuterBoundary j)) := by
  rintro ⟨emb, boundaryData, dartCycles, hselectedBoundaryArc, hcurrent, C₀, a, b, faceBoundary,
    hv23, parentData, hparentBoundary, hselectorDeficitSelectedBoundary,
    hcurrentOuterBoundaryNonempty, hcurrentOuterBoundaryDisjoint⟩
  exact
    false_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary_and_currentOuterBoundary
      boundaryData dartCycles hselectedBoundaryArc hcurrent C₀
      (a := a) (b := b) (faceBoundary := faceBoundary) hv23
      parentData hparentBoundary hselectorDeficitSelectedBoundary
      hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint

/-- Graph-level exact-shell obstruction form of the same stronger closed-walk inconsistency.
Even the older non-peeled-face selected-boundary-contact repair cannot coexist with the positive
current-outer-boundary side conditions on any one-collar/v23 honest-source shell. -/
theorem
    not_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_nonPeelSelectedBoundary_and_currentOuterBoundary
    {G : SimpleGraph V} :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            source.toPlanarBoundaryAnnulusBoundaryData,
      ∃ C₀ : G.EdgeColoring Color,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      ∃ parentData : PlanarBoundaryAnnulusRootParentPeelData emb,
        parentData.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData ∧
        (∀ f : AmbientFace emb.faces,
          f ∉
              (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).peelFaces →
            ∃ e ∈ emb.faceBoundary f.1,
              e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) ∧
        (∀ i :
            Fin
              (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).numCollars,
          0 < i.1 →
            ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).currentOuterBoundary i).Nonempty) ∧
        (∀ {i j :
            Fin
              (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).numCollars},
          0 < i.1 → 0 < j.1 → i ≠ j →
            Disjoint
              ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                  parentData).currentOuterBoundary i)
              ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                  parentData).currentOuterBoundary j)) := by
  rintro ⟨emb, source, hcurrent, C₀, a, b, faceBoundary, hv23, parentData, hparentBoundary,
    hnonPeelSelectedBoundary, hcurrentOuterBoundaryNonempty,
    hcurrentOuterBoundaryDisjoint⟩
  exact
    false_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_nonPeelSelectedBoundary_and_currentOuterBoundary
      source hcurrent C₀ (a := a) (b := b) (faceBoundary := faceBoundary) hv23
      parentData hparentBoundary hnonPeelSelectedBoundary
      hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint

/-- Graph-level exact-shell obstruction form of the same stronger successor-cycle inconsistency.
The live boundary-order one-collar shell cannot realize the older non-peeled-face repair
together with the positive current-boundary side conditions on any embedding. -/
theorem
    not_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_nonPeelSelectedBoundary_and_currentOuterBoundary
    {G : SimpleGraph V} :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
        (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            boundaryData.toPlanarBoundaryAnnulusBoundaryData,
      ∃ C₀ : G.EdgeColoring Color,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      ∃ parentData : PlanarBoundaryAnnulusRootParentPeelData emb,
        parentData.boundaryData = boundaryData.toPlanarBoundaryAnnulusBoundaryData ∧
        (∀ f : AmbientFace emb.faces,
          f ∉
              (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).peelFaces →
            ∃ e ∈ emb.faceBoundary f.1,
              e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) ∧
        (∀ i :
            Fin
              (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).numCollars,
          0 < i.1 →
            ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).currentOuterBoundary i).Nonempty) ∧
        (∀ {i j :
            Fin
              (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).numCollars},
          0 < i.1 → 0 < j.1 → i ≠ j →
            Disjoint
              ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                  parentData).currentOuterBoundary i)
              ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                  parentData).currentOuterBoundary j)) := by
  rintro ⟨emb, boundaryData, dartCycles, hselectedBoundaryArc, hcurrent, C₀, a, b, faceBoundary,
    hv23, parentData, hparentBoundary, hnonPeelSelectedBoundary,
    hcurrentOuterBoundaryNonempty, hcurrentOuterBoundaryDisjoint⟩
  exact
    false_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_nonPeelSelectedBoundary_and_currentOuterBoundary
      boundaryData dartCycles hselectedBoundaryArc hcurrent C₀
      (a := a) (b := b) (faceBoundary := faceBoundary) hv23
      parentData hparentBoundary hnonPeelSelectedBoundary
      hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint

/-- Exact-v23/v23.5 decomposition shell repair on the honest closed-walk route: once the exact
one-collar shell reaches the repaired construction face-layer package, it already lowers to a real
annulus decomposition on the same embedding. -/
theorem
    nonempty_planarBoundaryAnnulusDecomposition_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          source.toPlanarBoundaryAnnulusBoundaryData)
    (C₀ : G.EdgeColoring Color)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary))
    (parentData : PlanarBoundaryAnnulusRootParentPeelData emb)
    (hparentBoundary :
      parentData.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData)
    (hselectorDeficitSelectedBoundary : ∀ f : AmbientFace emb.faces,
      f ∈ parentData.interiorData.peelFaces →
        f ∉
            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).peelFaces →
          ∃ e ∈ emb.faceBoundary f.1,
            e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (hcurrentOuterBoundaryNonempty :
      ∀ i :
          Fin
            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).numCollars,
        0 < i.1 →
          ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).currentOuterBoundary i).Nonempty)
    (hcurrentOuterBoundaryDisjoint :
      ∀ {i j :
          Fin
            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).numCollars},
        0 < i.1 → 0 < j.1 → i ≠ j →
          Disjoint
            ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).currentOuterBoundary i)
            ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).currentOuterBoundary j)) :
    Nonempty (PlanarBoundaryAnnulusDecomposition emb) := by
  exact
    nonempty_planarBoundaryAnnulusDecomposition_of_planarBoundaryAnnulusConstructionFaceLayerData
      (Classical.choice
        (nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary
          source _hcurrent C₀ (a := a) (b := b) (faceBoundary := faceBoundary) _hv23
          parentData hparentBoundary hselectorDeficitSelectedBoundary
          hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint))

/-- Successor-cycle form of the same exact-v23/v23.5 decomposition shell repair. The repaired
selector-deficit package already yields a real annulus decomposition on the same embedding. -/
theorem
    nonempty_planarBoundaryAnnulusDecomposition_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (C₀ : G.EdgeColoring Color)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary))
    (parentData : PlanarBoundaryAnnulusRootParentPeelData emb)
    (hparentBoundary :
      parentData.boundaryData = boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (hselectorDeficitSelectedBoundary : ∀ f : AmbientFace emb.faces,
      f ∈ parentData.interiorData.peelFaces →
        f ∉
            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).peelFaces →
          ∃ e ∈ emb.faceBoundary f.1,
            e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (hcurrentOuterBoundaryNonempty :
      ∀ i :
          Fin
            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).numCollars,
        0 < i.1 →
          ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).currentOuterBoundary i).Nonempty)
    (hcurrentOuterBoundaryDisjoint :
      ∀ {i j :
          Fin
            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).numCollars},
        0 < i.1 → 0 < j.1 → i ≠ j →
          Disjoint
            ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).currentOuterBoundary i)
            ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).currentOuterBoundary j)) :
    Nonempty (PlanarBoundaryAnnulusDecomposition emb) := by
  exact
    nonempty_planarBoundaryAnnulusDecomposition_of_planarBoundaryAnnulusConstructionFaceLayerData
      (Classical.choice
        (nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary
          boundaryData dartCycles hselectedBoundaryArc _hcurrent C₀
          (a := a) (b := b) (faceBoundary := faceBoundary) _hv23
          parentData hparentBoundary hselectorDeficitSelectedBoundary
          hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint))

/-- Exact-v23/v23.5 synthesis repair on the honest closed-walk shell: once the repaired local
selector package reaches its derived annulus decomposition and that exact decomposition carries
witness ownership, no further theorem-4.9 algebra remains. -/
theorem
    theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary_and_inducedDecompositionWitnessAssignment
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          source.toPlanarBoundaryAnnulusBoundaryData)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary))
    (parentData : PlanarBoundaryAnnulusRootParentPeelData emb)
    (hparentBoundary :
      parentData.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData)
    (hselectorDeficitSelectedBoundary : ∀ f : AmbientFace emb.faces,
      f ∈ parentData.interiorData.peelFaces →
        f ∉
            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).peelFaces →
          ∃ e ∈ emb.faceBoundary f.1,
            e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (hcurrentOuterBoundaryNonempty :
      ∀ i :
          Fin
            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).numCollars,
        0 < i.1 →
          ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).currentOuterBoundary i).Nonempty)
    (hcurrentOuterBoundaryDisjoint :
      ∀ {i j :
          Fin
            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).numCollars},
        0 < i.1 → 0 < j.1 → i ≠ j →
          Disjoint
            ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).currentOuterBoundary i)
            ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).currentOuterBoundary j))
    (hwitness :
      let supportData :=
        planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_closedWalkEmbeddingData_and_selectedBoundaryArcOnFace_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary
          source.boundaryReachability
          source.closedWalks
          source.selectedBoundaryArc
          parentData
          (by
            simpa [PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData]
              using hparentBoundary)
          hselectorDeficitSelectedBoundary
          hcurrentOuterBoundaryNonempty
          hcurrentOuterBoundaryDisjoint
      Nonempty
        (PlanarBoundaryAnnulusWitnessAssignment
          supportData.toPlanarBoundaryAnnulusFaceLayerData.toPlanarBoundaryAnnulusDecomposition)) :
    Theorem49BoundaryRootSynthesis emb C₀ := by
  classical
  let supportData : PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb :=
    planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_closedWalkEmbeddingData_and_selectedBoundaryArcOnFace_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary
      source.boundaryReachability
      source.closedWalks
      source.selectedBoundaryArc
      parentData
      (by
        simpa [PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData]
          using hparentBoundary)
      hselectorDeficitSelectedBoundary
      hcurrentOuterBoundaryNonempty
      hcurrentOuterBoundaryDisjoint
  have hwitness' :
      Nonempty
        (PlanarBoundaryAnnulusWitnessAssignment
          supportData.toPlanarBoundaryAnnulusFaceLayerData.toPlanarBoundaryAnnulusDecomposition) := by
    simpa [supportData] using hwitness
  exact
    theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusConstructionBoundarySupportFaceData_and_inducedDecompositionWitnessAssignment
      supportData C₀ hC₀ hwitness'

/-- Exact-v23/v23.5 synthesis repair on the honest closed-walk shell: once the repaired local
selector package reaches its derived annulus decomposition and that exact decomposition carries
witness ownership, no further theorem-4.9 algebra remains. -/
theorem
    theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary_and_resultingDecompositionWitnessAssignment
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          source.toPlanarBoundaryAnnulusBoundaryData)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary))
    (parentData : PlanarBoundaryAnnulusRootParentPeelData emb)
    (hparentBoundary :
      parentData.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData)
    (hselectorDeficitSelectedBoundary : ∀ f : AmbientFace emb.faces,
      f ∈ parentData.interiorData.peelFaces →
        f ∉
            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).peelFaces →
          ∃ e ∈ emb.faceBoundary f.1,
            e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (hcurrentOuterBoundaryNonempty :
      ∀ i :
          Fin
            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).numCollars,
        0 < i.1 →
          ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).currentOuterBoundary i).Nonempty)
    (hcurrentOuterBoundaryDisjoint :
      ∀ {i j :
          Fin
            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).numCollars},
        0 < i.1 → 0 < j.1 → i ≠ j →
          Disjoint
            ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).currentOuterBoundary i)
            ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).currentOuterBoundary j))
    (hwitness :
      let decomp : PlanarBoundaryAnnulusDecomposition emb :=
        Classical.choice
          (nonempty_planarBoundaryAnnulusDecomposition_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary
            source _hcurrent C₀ (a := a) (b := b) (faceBoundary := faceBoundary) _hv23
            parentData hparentBoundary hselectorDeficitSelectedBoundary
            hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint)
      Nonempty (PlanarBoundaryAnnulusWitnessAssignment decomp)) :
    Theorem49BoundaryRootSynthesis emb C₀ := by
  exact
    theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusConstructionFaceLayerData_and_resultingDecompositionWitnessAssignment
      (Classical.choice
        (nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary
          source _hcurrent C₀ (a := a) (b := b) (faceBoundary := faceBoundary) _hv23
          parentData hparentBoundary hselectorDeficitSelectedBoundary
          hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint))
      C₀ hC₀
      (by
        simpa using hwitness)

/-- Successor-cycle form of the same exact-v23/v23.5 synthesis repair. Once the repaired local
selector package reaches its same-embedding annulus decomposition and that decomposition carries
witness ownership, the boundary-order shell closes directly to the full theorem-4.9 synthesis
package. -/
theorem
    theorem49BoundaryRootSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary_and_inducedDecompositionWitnessAssignment
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary))
    (parentData : PlanarBoundaryAnnulusRootParentPeelData emb)
    (hparentBoundary :
      parentData.boundaryData = boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (hselectorDeficitSelectedBoundary : ∀ f : AmbientFace emb.faces,
      f ∈ parentData.interiorData.peelFaces →
        f ∉
            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).peelFaces →
          ∃ e ∈ emb.faceBoundary f.1,
            e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (hcurrentOuterBoundaryNonempty :
      ∀ i :
          Fin
            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).numCollars,
        0 < i.1 →
          ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).currentOuterBoundary i).Nonempty)
    (hcurrentOuterBoundaryDisjoint :
      ∀ {i j :
          Fin
            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).numCollars},
        0 < i.1 → 0 < j.1 → i ≠ j →
          Disjoint
            ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).currentOuterBoundary i)
            ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).currentOuterBoundary j))
    (hwitness :
      let supportData :=
        planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary
          boundaryData
          dartCycles
          hselectedBoundaryArc
          parentData
          hparentBoundary
          hselectorDeficitSelectedBoundary
          hcurrentOuterBoundaryNonempty
          hcurrentOuterBoundaryDisjoint
      Nonempty
        (PlanarBoundaryAnnulusWitnessAssignment
          supportData.toPlanarBoundaryAnnulusFaceLayerData.toPlanarBoundaryAnnulusDecomposition)) :
    Theorem49BoundaryRootSynthesis emb C₀ := by
  classical
  let supportData : PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb :=
    planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary
      boundaryData
      dartCycles
      hselectedBoundaryArc
      parentData
      hparentBoundary
      hselectorDeficitSelectedBoundary
      hcurrentOuterBoundaryNonempty
      hcurrentOuterBoundaryDisjoint
  have hwitness' :
      Nonempty
        (PlanarBoundaryAnnulusWitnessAssignment
          supportData.toPlanarBoundaryAnnulusFaceLayerData.toPlanarBoundaryAnnulusDecomposition) := by
    simpa [supportData] using hwitness
  exact
    theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusConstructionBoundarySupportFaceData_and_inducedDecompositionWitnessAssignment
      supportData C₀ hC₀ hwitness'

/-- Successor-cycle form of the same exact-v23/v23.5 synthesis repair. Once the repaired local
selector package reaches its same-embedding annulus decomposition and that decomposition carries
witness ownership, the boundary-order shell closes directly to the full theorem-4.9 synthesis
package. -/
theorem
    theorem49BoundaryRootSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary_and_resultingDecompositionWitnessAssignment
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary))
    (parentData : PlanarBoundaryAnnulusRootParentPeelData emb)
    (hparentBoundary :
      parentData.boundaryData = boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (hselectorDeficitSelectedBoundary : ∀ f : AmbientFace emb.faces,
      f ∈ parentData.interiorData.peelFaces →
        f ∉
            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).peelFaces →
          ∃ e ∈ emb.faceBoundary f.1,
            e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (hcurrentOuterBoundaryNonempty :
      ∀ i :
          Fin
            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).numCollars,
        0 < i.1 →
          ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).currentOuterBoundary i).Nonempty)
    (hcurrentOuterBoundaryDisjoint :
      ∀ {i j :
          Fin
            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).numCollars},
        0 < i.1 → 0 < j.1 → i ≠ j →
          Disjoint
            ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).currentOuterBoundary i)
            ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).currentOuterBoundary j))
    (hwitness :
      let decomp : PlanarBoundaryAnnulusDecomposition emb :=
        Classical.choice
          (nonempty_planarBoundaryAnnulusDecomposition_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary
            boundaryData dartCycles hselectedBoundaryArc _hcurrent C₀
            (a := a) (b := b) (faceBoundary := faceBoundary) _hv23
            parentData hparentBoundary hselectorDeficitSelectedBoundary
            hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint)
      Nonempty (PlanarBoundaryAnnulusWitnessAssignment decomp)) :
    Theorem49BoundaryRootSynthesis emb C₀ := by
  exact
    theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusConstructionFaceLayerData_and_resultingDecompositionWitnessAssignment
      (Classical.choice
        (nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary
          boundaryData dartCycles hselectedBoundaryArc _hcurrent C₀
          (a := a) (b := b) (faceBoundary := faceBoundary) _hv23
          parentData hparentBoundary hselectorDeficitSelectedBoundary
          hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint))
      C₀ hC₀
      (by
        simpa using hwitness)

/-- Successor-cycle exact-v23/v23.5 synthesis repair under the stronger older non-peeled-face
contact hypothesis. This discharges the smaller selector-deficit premise internally, so the
remaining live exact-shell burdens are witness ownership plus the positive current-boundary side
conditions. -/
theorem
    theorem49BoundaryRootSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_nonPeelSelectedBoundary_and_resultingDecompositionWitnessAssignment
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary))
    (parentData : PlanarBoundaryAnnulusRootParentPeelData emb)
    (hparentBoundary :
      parentData.boundaryData = boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (hnonPeelSelectedBoundary : ∀ f : AmbientFace emb.faces,
      f ∉
          (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
            parentData).peelFaces →
        ∃ e ∈ emb.faceBoundary f.1,
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (hcurrentOuterBoundaryNonempty :
      ∀ i :
          Fin
            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).numCollars,
        0 < i.1 →
          ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).currentOuterBoundary i).Nonempty)
    (hcurrentOuterBoundaryDisjoint :
      ∀ {i j :
          Fin
            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).numCollars},
        0 < i.1 → 0 < j.1 → i ≠ j →
          Disjoint
            ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).currentOuterBoundary i)
            ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).currentOuterBoundary j))
    (hwitness :
      let hselectorDeficitSelectedBoundary :=
        selectorDeficitSelectedBoundary_of_planarBoundaryAnnulusRootParentPeelData_and_nonPeelSelectedBoundary
          parentData hnonPeelSelectedBoundary
      let decomp : PlanarBoundaryAnnulusDecomposition emb :=
        Classical.choice
          (nonempty_planarBoundaryAnnulusDecomposition_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary
            boundaryData dartCycles hselectedBoundaryArc _hcurrent C₀
            (a := a) (b := b) (faceBoundary := faceBoundary) _hv23
            parentData hparentBoundary hselectorDeficitSelectedBoundary
            hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint)
      Nonempty (PlanarBoundaryAnnulusWitnessAssignment decomp)) :
    Theorem49BoundaryRootSynthesis emb C₀ := by
  let hselectorDeficitSelectedBoundary :=
    selectorDeficitSelectedBoundary_of_planarBoundaryAnnulusRootParentPeelData_and_nonPeelSelectedBoundary
      parentData hnonPeelSelectedBoundary
  exact
    theorem49BoundaryRootSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary_and_resultingDecompositionWitnessAssignment
      boundaryData dartCycles hselectedBoundaryArc _hcurrent C₀ hC₀
      (a := a) (b := b) (faceBoundary := faceBoundary) _hv23
      parentData hparentBoundary hselectorDeficitSelectedBoundary
      hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint
      (by
        simpa [hselectorDeficitSelectedBoundary] using hwitness)

/-- Repaired exact-v23/v23.5 closed-walk route: if the one-collar current-boundary shell already
carries annulus-root parent peel data on the same boundary split, then the remaining local
endpoint witness is enough to reach the projected Theorem 4.9 synthesis endpoint.  The exact
residual state is recorded explicitly so this theorem can serve as the current strongest sound
replacement for the obstructed one-collar implication. -/
theorem
    theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (_source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          _source.toPlanarBoundaryAnnulusBoundaryData)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary))
    (parentData : PlanarBoundaryAnnulusRootParentPeelData emb)
    (_hparentBoundary :
      parentData.boundaryData = _source.toPlanarBoundaryAnnulusBoundaryData) :
    Theorem49BoundaryRootSynthesis emb C₀ := by
  exact
    theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusRootParentPeelData
      (G := G) parentData C₀ hC₀

/-- Successor-cycle form of the same strongest currently sound exact-v23/v23.5 repair.  Once the
actual one-collar boundary-order shell carries same-split annulus-root parent peel data, the
Theorem 4.9 synthesis endpoint is already immediate on that embedding. -/
theorem
    theorem49BoundaryRootSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (_boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (_dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (_hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
      (_dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          _boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary))
    (parentData : PlanarBoundaryAnnulusRootParentPeelData emb)
    (_hparentBoundary :
      parentData.boundaryData = _boundaryData.toPlanarBoundaryAnnulusBoundaryData) :
    Theorem49BoundaryRootSynthesis emb C₀ := by
  exact
    theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusRootParentPeelData
      (G := G) parentData C₀ hC₀

/-- Exact-v23/v23.5 closed-walk route one layer earlier than annulus-root parent peel: once the
same one-collar shell already carries the raw source-fixed canonical-parent shared-edge cover on
the honest boundary-face roots, full theorem-4.9 synthesis is immediate on that embedding.  No
extra endpoint witness or parent-peel repackaging remains below that concrete source-fixed
cover surface. -/
theorem
    theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalParentSharedEdgeCover
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (_source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          _source.toPlanarBoundaryAnnulusBoundaryData)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary))
    (peelFaces : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      _source.boundaryFaceRoots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      _source.boundaryFaceRoots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces _source.boundaryFaceRoots
          hcoverRoots hsepRoots)
        _source.fallbackEdge)) :
    Theorem49BoundaryRootSynthesis emb C₀ := by
  exact
    theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_via_residualBoundary
      _source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover C₀ hC₀

/-- Successor-cycle form of the same exact-v23/v23.5 canonical-parent cover closure.  Once the
live one-collar boundary-order shell carries the raw source-fixed canonical-parent shared-edge
cover on the boundary-face roots extracted from the successor data, full theorem-4.9 synthesis is
already immediate on that embedding. -/
theorem
    theorem49BoundaryRootSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalParentSharedEdgeCover
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (_boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (_dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (_hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
      (_dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          _boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary))
    (peelFaces : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        _boundaryData _dartCycles _hselectedBoundaryArc).boundaryFaceRoots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        _boundaryData _dartCycles _hselectedBoundaryArc).boundaryFaceRoots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            _boundaryData _dartCycles _hselectedBoundaryArc).boundaryFaceRoots
          hcoverRoots hsepRoots)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          _boundaryData _dartCycles _hselectedBoundaryArc).fallbackEdge)) :
    Theorem49BoundaryRootSynthesis emb C₀ := by
  exact
    theorem49BoundaryRootSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_via_residualBoundary
      _boundaryData _dartCycles _hselectedBoundaryArc peelFaces hunique hcoverRoots hsepRoots
      hpeelInterior hcover C₀ hC₀

/-- Exact-v23/v23.5 closed-walk route already closes on the sharper rooted shared-edge
face-membership shell: once the same one-collar shell carries the concrete source-fixed rooted
cover package on the honest boundary-face roots, full theorem-4.9 synthesis is immediate on that
embedding. -/
theorem
    theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (_source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          _source.toPlanarBoundaryAnnulusBoundaryData)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary))
    (peelFaces : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      _source.boundaryFaceRoots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      _source.boundaryFaceRoots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces _source.boundaryFaceRoots
          hcoverRoots hsepRoots)
        _source.fallbackEdge))
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
        (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
            _source.boundaryFaceRoots hcoverRoots hsepRoots)
          _source.fallbackEdge f),
      e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
        ∃ g ∈ peelFaces,
          (interiorDualSpanningForest emb.faceBoundary emb.faces).Adj f g ∧
          e ∈ emb.faceBoundary g.1 ∧
          (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
              f
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                _source.boundaryFaceRoots hcoverRoots hsepRoots f) <
            (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
              g
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                _source.boundaryFaceRoots hcoverRoots hsepRoots g)) :
    Theorem49BoundaryRootSynthesis emb C₀ := by
  exact
    theorem49BoundaryRootSynthesis_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      (G := G)
      (interiorDualBoundaryRootAdjDistancePeelDataOfClosedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover
        _source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover hchildren)
      C₀ hC₀

/-- Successor-cycle form of the same exact-v23/v23.5 rooted shared-edge face-membership
closure.  Once the live one-collar boundary-order shell carries this concrete source-fixed rooted
cover package, no additional route-side repackaging remains before full theorem-4.9 synthesis. -/
theorem
    theorem49BoundaryRootSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (_boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (_dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (_hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
      (_dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          _boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary))
    (peelFaces : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        _boundaryData _dartCycles _hselectedBoundaryArc).boundaryFaceRoots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        _boundaryData _dartCycles _hselectedBoundaryArc).boundaryFaceRoots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            _boundaryData _dartCycles _hselectedBoundaryArc).boundaryFaceRoots
          hcoverRoots hsepRoots)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          _boundaryData _dartCycles _hselectedBoundaryArc).fallbackEdge))
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
        (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              _boundaryData _dartCycles _hselectedBoundaryArc).boundaryFaceRoots
            hcoverRoots hsepRoots)
          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            _boundaryData _dartCycles _hselectedBoundaryArc).fallbackEdge f),
      e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
        ∃ g ∈ peelFaces,
          (interiorDualSpanningForest emb.faceBoundary emb.faces).Adj f g ∧
          e ∈ emb.faceBoundary g.1 ∧
          (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
              f
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                  _boundaryData _dartCycles _hselectedBoundaryArc).boundaryFaceRoots
                hcoverRoots hsepRoots f) <
            (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
              g
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                  _boundaryData _dartCycles _hselectedBoundaryArc).boundaryFaceRoots
                hcoverRoots hsepRoots g)) :
    Theorem49BoundaryRootSynthesis emb C₀ := by
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      _boundaryData _dartCycles _hselectedBoundaryArc
  exact
    theorem49BoundaryRootSynthesis_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      (G := G)
      (interiorDualBoundaryRootAdjDistancePeelDataOfClosedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover
        source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover hchildren)
      C₀ hC₀

/-- Stronger exact-v23/v23.5 closed-walk repair: if the same exact one-collar shell already
carries generic boundary-root interior-dual adjacency-distance data, then the full Theorem 4.9
synthesis endpoint is immediate on that embedding.  This lowers the live exact-shell burden one
step further than the annulus-root parent-peel package. -/
theorem
    theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (_source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          _source.toPlanarBoundaryAnnulusBoundaryData)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary))
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) :
    Theorem49BoundaryRootSynthesis emb C₀ := by
  exact
    theorem49BoundaryRootSynthesis_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      (G := G) interiorData C₀ hC₀

/-- Successor-cycle form of the same stronger exact-v23/v23.5 repair.  Once the live one-collar
boundary-order shell carries generic boundary-root interior-dual adjacency-distance data on the
same embedding, no further annulus-root packaging is needed to reach the full Theorem 4.9
synthesis endpoint. -/
theorem
    theorem49BoundaryRootSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (_boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (_dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (_hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
      (_dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          _boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary))
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) :
    Theorem49BoundaryRootSynthesis emb C₀ := by
  exact
    theorem49BoundaryRootSynthesis_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      (G := G) interiorData C₀ hC₀

/-- Existential closed-walk exact-shell parent-peel data already reaches the full theorem-4.9
boundary-root synthesis endpoint at graph level, with no additional endpoint-side hypothesis. -/
theorem
    exists_theorem49BoundaryRootSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            source.toPlanarBoundaryAnnulusBoundaryData,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      ∃ parentData : PlanarBoundaryAnnulusRootParentPeelData emb,
        parentData.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases h with
    ⟨emb, source, hcurrent, a, b, faceBoundary, hv23, parentData, hparentBoundary⟩
  exact
    ⟨emb,
      theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData
        source hcurrent C₀ hC₀ hv23 parentData hparentBoundary⟩

/-- Successor-cycle form of the same exact-shell graph-level parent-peel synthesis closure. -/
theorem
    exists_theorem49BoundaryRootSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
        (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            boundaryData.toPlanarBoundaryAnnulusBoundaryData,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      ∃ parentData : PlanarBoundaryAnnulusRootParentPeelData emb,
        parentData.boundaryData = boundaryData.toPlanarBoundaryAnnulusBoundaryData) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases h with
    ⟨emb, boundaryData, dartCycles, hselectedBoundaryArc, hcurrent, a, b, faceBoundary, hv23,
      parentData, hparentBoundary⟩
  exact
    ⟨emb,
      theorem49BoundaryRootSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData
        boundaryData dartCycles hselectedBoundaryArc hcurrent C₀ hC₀ hv23 parentData
        hparentBoundary⟩

/-- Existential exact-shell closed-walk canonical-parent cover data already reaches the full
theorem-4.9 synthesis endpoint at graph level, with no additional endpoint-side hypothesis. -/
theorem
    exists_theorem49BoundaryRootSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            source.toPlanarBoundaryAnnulusBoundaryData,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      ∃ peelFaces : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        source.boundaryFaceRoots,
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        source.boundaryFaceRoots,
        (∀ f ∈ peelFaces,
          Disjoint (emb.faceBoundary f.1)
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
        interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces source.boundaryFaceRoots
              hcoverRoots hsepRoots)
            source.fallbackEdge)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases h with
    ⟨emb, source, hcurrent, a, b, faceBoundary, hv23, peelFaces, hunique, hcoverRoots, hsepRoots,
      hpeelInterior, hcover⟩
  exact
    ⟨emb,
      theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalParentSharedEdgeCover
        source hcurrent C₀ hC₀ hv23 peelFaces hunique hcoverRoots hsepRoots
        hpeelInterior hcover⟩

/-- Successor-cycle form of the same exact-shell graph-level canonical-parent-cover synthesis
closure. -/
theorem
    exists_theorem49BoundaryRootSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
        (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            boundaryData.toPlanarBoundaryAnnulusBoundaryData,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      ∃ peelFaces : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles _hselectedBoundaryArc).boundaryFaceRoots,
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles _hselectedBoundaryArc).boundaryFaceRoots,
        (∀ f ∈ peelFaces,
          Disjoint (emb.faceBoundary f.1)
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
        interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                boundaryData dartCycles _hselectedBoundaryArc).boundaryFaceRoots
              hcoverRoots hsepRoots)
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles _hselectedBoundaryArc).fallbackEdge)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases h with
    ⟨emb, boundaryData, dartCycles, hselectedBoundaryArc, hcurrent, a, b, faceBoundary, hv23,
      peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover⟩
  exact
    ⟨emb,
      theorem49BoundaryRootSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalParentSharedEdgeCover
        boundaryData dartCycles hselectedBoundaryArc hcurrent C₀ hC₀ hv23 peelFaces hunique
        hcoverRoots hsepRoots hpeelInterior hcover⟩

/-- Existential exact-shell closed-walk rooted shared-edge face-membership data already reaches
full theorem-4.9 synthesis at graph level. -/
theorem
    exists_theorem49BoundaryRootSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            source.toPlanarBoundaryAnnulusBoundaryData,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      ∃ peelFaces : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        source.boundaryFaceRoots,
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        source.boundaryFaceRoots,
        (∀ f ∈ peelFaces,
          Disjoint (emb.faceBoundary f.1)
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
        interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces source.boundaryFaceRoots
              hcoverRoots hsepRoots)
            source.fallbackEdge) ∧
        (∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
            (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                source.boundaryFaceRoots hcoverRoots hsepRoots)
              source.fallbackEdge f),
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
            ∃ g ∈ peelFaces,
              (interiorDualSpanningForest emb.faceBoundary emb.faces).Adj f g ∧
              e ∈ emb.faceBoundary g.1 ∧
              (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                  f
                  (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                    source.boundaryFaceRoots hcoverRoots hsepRoots f) <
                (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                  g
                  (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                    source.boundaryFaceRoots hcoverRoots hsepRoots g))) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases h with
    ⟨emb, source, hcurrent, a, b, faceBoundary, hv23, peelFaces, hunique, hcoverRoots, hsepRoots,
      hpeelInterior, hcover, hchildren⟩
  exact
    ⟨emb,
      theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover
        source hcurrent C₀ hC₀ hv23 peelFaces hunique hcoverRoots hsepRoots
        hpeelInterior hcover hchildren⟩

/-- Successor-cycle form of the same exact-shell graph-level rooted shared-edge face-membership
synthesis closure. -/
theorem
    exists_theorem49BoundaryRootSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
        (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            boundaryData.toPlanarBoundaryAnnulusBoundaryData,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      ∃ peelFaces : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles _hselectedBoundaryArc).boundaryFaceRoots,
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles _hselectedBoundaryArc).boundaryFaceRoots,
        (∀ f ∈ peelFaces,
          Disjoint (emb.faceBoundary f.1)
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
        interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                boundaryData dartCycles _hselectedBoundaryArc).boundaryFaceRoots
              hcoverRoots hsepRoots)
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles _hselectedBoundaryArc).fallbackEdge) ∧
        (∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
            (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                  boundaryData dartCycles _hselectedBoundaryArc).boundaryFaceRoots
                hcoverRoots hsepRoots)
              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                boundaryData dartCycles _hselectedBoundaryArc).fallbackEdge f),
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
            ∃ g ∈ peelFaces,
              (interiorDualSpanningForest emb.faceBoundary emb.faces).Adj f g ∧
              e ∈ emb.faceBoundary g.1 ∧
              (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                  f
                  (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                    (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                      boundaryData dartCycles _hselectedBoundaryArc).boundaryFaceRoots
                    hcoverRoots hsepRoots f) <
                (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                  g
                  (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                    (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                      boundaryData dartCycles _hselectedBoundaryArc).boundaryFaceRoots
                    hcoverRoots hsepRoots g))) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases h with
    ⟨emb, boundaryData, dartCycles, hselectedBoundaryArc, hcurrent, a, b, faceBoundary, hv23,
      peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover, hchildren⟩
  exact
    ⟨emb,
      theorem49BoundaryRootSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover
        boundaryData dartCycles hselectedBoundaryArc hcurrent C₀ hC₀ hv23 peelFaces hunique
        hcoverRoots hsepRoots hpeelInterior hcover hchildren⟩

/-- Existential closed-walk exact-shell adj-distance data already reaches the full theorem-4.9
boundary-root synthesis endpoint at graph level. -/
theorem
    exists_theorem49BoundaryRootSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_interiorDualBoundaryRootAdjDistancePeelData_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            source.toPlanarBoundaryAnnulusBoundaryData,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      Nonempty (InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases h with ⟨emb, source, hcurrent, a, b, faceBoundary, hv23, ⟨interiorData⟩⟩
  exact
    ⟨emb,
      theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_interiorDualBoundaryRootAdjDistancePeelData
        source hcurrent C₀ hC₀ hv23 interiorData⟩

/-- Successor-cycle form of the same exact-shell graph-level adj-distance synthesis closure. -/
theorem
    exists_theorem49BoundaryRootSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_interiorDualBoundaryRootAdjDistancePeelData_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
        (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            boundaryData.toPlanarBoundaryAnnulusBoundaryData,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      Nonempty (InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases h with
    ⟨emb, boundaryData, dartCycles, hselectedBoundaryArc, hcurrent, a, b, faceBoundary, hv23,
      ⟨interiorData⟩⟩
  exact
    ⟨emb,
      theorem49BoundaryRootSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_interiorDualBoundaryRootAdjDistancePeelData
        boundaryData dartCycles hselectedBoundaryArc hcurrent C₀ hC₀ hv23 interiorData⟩

/-- The exact one-collar v23/v23.5 closed-walk shell already reaches the named
height-ordered positive geometry surface on the raw canonical-parent shared-edge-cover package
once a local unblocked endpoint exists.  This exposes the selector-built positive route directly
on the live shell, before any residual-boundary repackaging. -/
theorem
    theorem49HeightOrderedPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_via_boundaryFreeSelector
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          source.toPlanarBoundaryAnnulusBoundaryData)
    (_C₀ : G.EdgeColoring Color)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState _C₀ a b faceBoundary))
    (peelFaces : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces source.boundaryFaceRoots
          hcoverRoots hsepRoots)
        source.fallbackEdge))
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  exact
    theorem49HeightOrderedPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_via_boundaryFreeSelector
      source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover hEndpoint

/-- Successor-cycle form of the same exact-shell selector-side lowering to height-ordered
positive geometry on the raw canonical-parent shared-edge-cover package. -/
theorem
    theorem49HeightOrderedPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_via_boundaryFreeSelector
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (_C₀ : G.EdgeColoring Color)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState _C₀ a b faceBoundary))
    (peelFaces : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
          hcoverRoots hsepRoots)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hselectedBoundaryArc).fallbackEdge))
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  exact
    theorem49HeightOrderedPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_via_boundaryFreeSelector
      boundaryData dartCycles hselectedBoundaryArc peelFaces hunique hcoverRoots hsepRoots
      hpeelInterior hcover hEndpoint

/-- Graph-level height-ordered positive geometry closure for the exact one-collar/v23
closed-walk canonical-parent raw-cover shell. -/
theorem
    exists_theorem49HeightOrderedPositiveProjectedGeometryOn_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_and_hasUnblockedInteriorEndpoint_via_boundaryFreeSelector
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            source.toPlanarBoundaryAnnulusBoundaryData,
      ∃ C₀ : G.EdgeColoring Color,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      ∃ peelFaces : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        source.boundaryFaceRoots,
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        source.boundaryFaceRoots,
      ∃ _hpeelInterior : ∀ f ∈ peelFaces,
          Disjoint (emb.faceBoundary f.1)
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces),
      ∃ _hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces source.boundaryFaceRoots
              hcoverRoots hsepRoots)
            source.fallbackEdge),
      HasUnblockedInteriorEndpoint emb) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  rcases h with
    ⟨emb, source, hcurrent, C₀, a, b, faceBoundary, hv23, peelFaces, hunique, hcoverRoots,
      hsepRoots, hpeelInterior, hcover, hEndpoint⟩
  exact
    ⟨emb,
      theorem49HeightOrderedPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_via_boundaryFreeSelector
        source hcurrent C₀ hv23 peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover
        hEndpoint⟩

/-- Graph-level height-ordered positive geometry closure for the exact one-collar/v23
successor-cycle canonical-parent raw-cover shell. -/
theorem
    exists_theorem49HeightOrderedPositiveProjectedGeometryOn_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_and_hasUnblockedInteriorEndpoint_via_boundaryFreeSelector
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
        (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            boundaryData.toPlanarBoundaryAnnulusBoundaryData,
      ∃ C₀ : G.EdgeColoring Color,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      ∃ peelFaces : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots,
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots,
      ∃ _hpeelInterior : ∀ f ∈ peelFaces,
          Disjoint (emb.faceBoundary f.1)
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces),
      ∃ _hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
              hcoverRoots hsepRoots)
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hselectedBoundaryArc).fallbackEdge),
      HasUnblockedInteriorEndpoint emb) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  rcases h with
    ⟨emb, boundaryData, dartCycles, hselectedBoundaryArc, hcurrent, C₀, a, b, faceBoundary, hv23,
      peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover, hEndpoint⟩
  exact
    ⟨emb,
      theorem49HeightOrderedPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_via_boundaryFreeSelector
        boundaryData dartCycles hselectedBoundaryArc hcurrent C₀ hv23 peelFaces hunique
        hcoverRoots hsepRoots hpeelInterior hcover hEndpoint⟩

/-- The exact one-collar v23/v23.5 closed-walk shell already lands on the named
route-facing annulus-root parent positive geometry surface once it carries same-split
parent-peel data and a local endpoint witness. -/
theorem
    theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          source.toPlanarBoundaryAnnulusBoundaryData)
    (_C₀ : G.EdgeColoring Color)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState _C₀ a b faceBoundary))
    (parentData : PlanarBoundaryAnnulusRootParentPeelData emb)
    (_hparentBoundary :
      parentData.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometryOn emb := by
  exact
    ⟨source, parentData.interiorData,
      (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).1 hEndpoint⟩

/-- Successor-cycle form of the same exact one-collar v23/v23.5 lowering to the named
route-facing annulus-root parent positive geometry surface. -/
theorem
    theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (_C₀ : G.EdgeColoring Color)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState _C₀ a b faceBoundary))
    (parentData : PlanarBoundaryAnnulusRootParentPeelData emb)
    (_hparentBoundary :
      parentData.boundaryData = boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometryOn emb := by
  exact
    ⟨boundaryData, dartCycles, parentData.interiorData, hselectedBoundaryArc,
      (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).1 hEndpoint⟩

/-- The exact one-collar v23/v23.5 closed-walk shell already lands on the named
route-facing annulus root-distance positive geometry surface once it carries generic
boundary-root adjacency-distance data and a local endpoint witness. -/
theorem
    theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          source.toPlanarBoundaryAnnulusBoundaryData)
    (_C₀ : G.EdgeColoring Color)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState _C₀ a b faceBoundary))
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn emb := by
  exact
    ⟨source, interiorData,
      (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).1 hEndpoint⟩

/-- Successor-cycle form of the same exact one-collar v23/v23.5 lowering to the named
route-facing annulus root-distance positive geometry surface. -/
theorem
    theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (_C₀ : G.EdgeColoring Color)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState _C₀ a b faceBoundary))
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn emb := by
  exact
    ⟨boundaryData, dartCycles, interiorData, hselectedBoundaryArc,
      (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).1 hEndpoint⟩

/-- The exact one-collar v23/v23.5 closed-walk shell already lands on the named route-facing
annulus root-distance positive geometry surface once it carries the concrete rooted shared-edge
face-membership cover package and a local endpoint witness. -/
theorem
    theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          source.toPlanarBoundaryAnnulusBoundaryData)
    (_C₀ : G.EdgeColoring Color)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState _C₀ a b faceBoundary))
    (peelFaces : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces source.boundaryFaceRoots
          hcoverRoots hsepRoots)
        source.fallbackEdge))
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
        (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
            source.boundaryFaceRoots hcoverRoots hsepRoots)
          source.fallbackEdge f),
      e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
        ∃ g ∈ peelFaces,
          (interiorDualSpanningForest emb.faceBoundary emb.faces).Adj f g ∧
          e ∈ emb.faceBoundary g.1 ∧
          (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
              f
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                source.boundaryFaceRoots hcoverRoots hsepRoots f) <
            (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
              g
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                source.boundaryFaceRoots hcoverRoots hsepRoots g))
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn emb := by
  exact
    theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint
      source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover hchildren hEndpoint

/-- Successor-cycle form of the same exact one-collar v23/v23.5 rooted-cover lowering to the
named route-facing annulus root-distance positive geometry surface. -/
theorem
    theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (_C₀ : G.EdgeColoring Color)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState _C₀ a b faceBoundary))
    (peelFaces : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
          hcoverRoots hsepRoots)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hselectedBoundaryArc).fallbackEdge))
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
        (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
            hcoverRoots hsepRoots)
          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hselectedBoundaryArc).fallbackEdge f),
      e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
        ∃ g ∈ peelFaces,
          (interiorDualSpanningForest emb.faceBoundary emb.faces).Adj f g ∧
          e ∈ emb.faceBoundary g.1 ∧
          (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
              f
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                  boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
                hcoverRoots hsepRoots f) <
            (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
              g
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                  boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
                hcoverRoots hsepRoots g))
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn emb := by
  exact
    theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint
      boundaryData dartCycles hselectedBoundaryArc peelFaces hunique hcoverRoots hsepRoots
      hpeelInterior hcover hchildren hEndpoint

/-- The exact one-collar v23/v23.5 closed-walk shell already reaches the named height-ordered
positive geometry surface once it carries the sharper rooted shared-edge face-membership cover
package and a local endpoint witness. -/
theorem
    theorem49HeightOrderedPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          source.toPlanarBoundaryAnnulusBoundaryData)
    (_C₀ : G.EdgeColoring Color)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState _C₀ a b faceBoundary))
    (peelFaces : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces source.boundaryFaceRoots
          hcoverRoots hsepRoots)
        source.fallbackEdge))
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
        (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
            source.boundaryFaceRoots hcoverRoots hsepRoots)
          source.fallbackEdge f),
      e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
        ∃ g ∈ peelFaces,
          (interiorDualSpanningForest emb.faceBoundary emb.faces).Adj f g ∧
          e ∈ emb.faceBoundary g.1 ∧
          (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
              f
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                source.boundaryFaceRoots hcoverRoots hsepRoots f) <
            (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
              g
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                source.boundaryFaceRoots hcoverRoots hsepRoots g))
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  exact
    theorem49HeightOrderedPositiveProjectedGeometryOn_of_closedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn
      (theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint
        source _hcurrent _C₀ _hv23 peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover
        hchildren hEndpoint)

/-- Successor-cycle form of the same exact-shell rooted-cover lowering to height-ordered positive
geometry. -/
theorem
    theorem49HeightOrderedPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (_C₀ : G.EdgeColoring Color)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState _C₀ a b faceBoundary))
    (peelFaces : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
          hcoverRoots hsepRoots)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hselectedBoundaryArc).fallbackEdge))
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
        (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
            hcoverRoots hsepRoots)
          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hselectedBoundaryArc).fallbackEdge f),
      e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
        ∃ g ∈ peelFaces,
          (interiorDualSpanningForest emb.faceBoundary emb.faces).Adj f g ∧
          e ∈ emb.faceBoundary g.1 ∧
          (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
              f
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                  boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
                hcoverRoots hsepRoots f) <
            (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
              g
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                  boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
                hcoverRoots hsepRoots g))
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  exact
    theorem49HeightOrderedPositiveProjectedGeometryOn_of_successorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn
      (theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint
        boundaryData dartCycles hselectedBoundaryArc _hcurrent _C₀ _hv23 peelFaces hunique
        hcoverRoots hsepRoots hpeelInterior hcover hchildren hEndpoint)

/-- Graph-level height-ordered positive geometry closure for the exact one-collar/v23
closed-walk rooted shared-edge face-membership-cover shell. -/
theorem
    exists_theorem49HeightOrderedPositiveProjectedGeometryOn_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            source.toPlanarBoundaryAnnulusBoundaryData,
      ∃ C₀ : G.EdgeColoring Color,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      ∃ peelFaces : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        source.boundaryFaceRoots,
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        source.boundaryFaceRoots,
      ∃ _hpeelInterior : ∀ f ∈ peelFaces,
          Disjoint (emb.faceBoundary f.1)
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces),
      ∃ _hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces source.boundaryFaceRoots
              hcoverRoots hsepRoots)
            source.fallbackEdge),
      ∃ _hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              source.boundaryFaceRoots hcoverRoots hsepRoots)
            source.fallbackEdge f),
        e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
          ∃ g ∈ peelFaces,
            (interiorDualSpanningForest emb.faceBoundary emb.faces).Adj f g ∧
            e ∈ emb.faceBoundary g.1 ∧
            (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                f
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                  source.boundaryFaceRoots hcoverRoots hsepRoots f) <
              (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                g
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                  source.boundaryFaceRoots hcoverRoots hsepRoots g),
      HasUnblockedInteriorEndpoint emb) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  rcases h with
    ⟨emb, source, hcurrent, C₀, a, b, faceBoundary, hv23, peelFaces, hunique, hcoverRoots,
      hsepRoots, hpeelInterior, hcover, hchildren, hEndpoint⟩
  have hGeom :
      Nonempty (Theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometry G) :=
    nonempty_theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometry_of_exists_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint
      ⟨emb, source, peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover, hchildren,
        hEndpoint⟩
  rcases
    (Theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometry.nonempty_iff_exists_on).1
      hGeom with ⟨emb, geom⟩
  exact
    ⟨emb,
      theorem49HeightOrderedPositiveProjectedGeometryOn_of_closedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn
        geom⟩

/-- Graph-level height-ordered positive geometry closure for the exact one-collar/v23
successor-cycle rooted shared-edge face-membership-cover shell. -/
theorem
    exists_theorem49HeightOrderedPositiveProjectedGeometryOn_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
        (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            boundaryData.toPlanarBoundaryAnnulusBoundaryData,
      ∃ C₀ : G.EdgeColoring Color,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      ∃ peelFaces : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots,
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots,
      ∃ _hpeelInterior : ∀ f ∈ peelFaces,
          Disjoint (emb.faceBoundary f.1)
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces),
      ∃ _hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
              hcoverRoots hsepRoots)
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hselectedBoundaryArc).fallbackEdge),
      ∃ _hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
              hcoverRoots hsepRoots)
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hselectedBoundaryArc).fallbackEdge f),
        e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
          ∃ g ∈ peelFaces,
            (interiorDualSpanningForest emb.faceBoundary emb.faces).Adj f g ∧
            e ∈ emb.faceBoundary g.1 ∧
            (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                f
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                  (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                    boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
                  hcoverRoots hsepRoots f) <
              (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                g
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                  (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                    boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
                  hcoverRoots hsepRoots g),
      HasUnblockedInteriorEndpoint emb) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  rcases h with
    ⟨emb, boundaryData, dartCycles, hselectedBoundaryArc, hcurrent, C₀, a, b, faceBoundary, hv23,
      peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover, hchildren, hEndpoint⟩
  have hGeom :
      Nonempty (Theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometry G) :=
    nonempty_theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometry_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint
      ⟨emb, boundaryData, dartCycles, hselectedBoundaryArc, peelFaces, hunique, hcoverRoots,
        hsepRoots, hpeelInterior, hcover, hchildren, hEndpoint⟩
  rcases
    (Theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometry.nonempty_iff_exists_on).1
      hGeom with ⟨emb, geom⟩
  exact
    ⟨emb,
      theorem49HeightOrderedPositiveProjectedGeometryOn_of_successorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn
        geom⟩

/-- The exact one-collar v23/v23.5 closed-walk shell also already reaches the finite-collar
replacement source once it carries the sharper rooted shared-edge face-membership cover package
and a local endpoint witness. -/
theorem
    theorem49CollarLayerPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          source.toPlanarBoundaryAnnulusBoundaryData)
    (_C₀ : G.EdgeColoring Color)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState _C₀ a b faceBoundary))
    (peelFaces : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces source.boundaryFaceRoots
          hcoverRoots hsepRoots)
        source.fallbackEdge))
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
        (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
            source.boundaryFaceRoots hcoverRoots hsepRoots)
          source.fallbackEdge f),
      e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
        ∃ g ∈ peelFaces,
          (interiorDualSpanningForest emb.faceBoundary emb.faces).Adj f g ∧
          e ∈ emb.faceBoundary g.1 ∧
          (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
              f
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                source.boundaryFaceRoots hcoverRoots hsepRoots f) <
            (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
              g
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                source.boundaryFaceRoots hcoverRoots hsepRoots g))
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49CollarLayerPositiveProjectedGeometryOn emb := by
  exact
    heightOrderedPositiveProjectedGeometryOn_iff_collarLayerPositiveProjectedGeometryOn.1
      (theorem49HeightOrderedPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint
        source _hcurrent _C₀ _hv23 peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover
        hchildren hEndpoint)

/-- Successor-cycle form of the same exact-shell rooted-cover lowering to the finite-collar
replacement source. -/
theorem
    theorem49CollarLayerPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (_C₀ : G.EdgeColoring Color)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState _C₀ a b faceBoundary))
    (peelFaces : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
          hcoverRoots hsepRoots)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hselectedBoundaryArc).fallbackEdge))
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
        (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
            hcoverRoots hsepRoots)
          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hselectedBoundaryArc).fallbackEdge f),
      e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
        ∃ g ∈ peelFaces,
          (interiorDualSpanningForest emb.faceBoundary emb.faces).Adj f g ∧
          e ∈ emb.faceBoundary g.1 ∧
          (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
              f
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                  boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
                hcoverRoots hsepRoots f) <
            (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
              g
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                  boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
                hcoverRoots hsepRoots g))
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49CollarLayerPositiveProjectedGeometryOn emb := by
  exact
    heightOrderedPositiveProjectedGeometryOn_iff_collarLayerPositiveProjectedGeometryOn.1
      (theorem49HeightOrderedPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint
        boundaryData dartCycles hselectedBoundaryArc _hcurrent _C₀ _hv23 peelFaces hunique
        hcoverRoots hsepRoots hpeelInterior hcover hchildren hEndpoint)

/-- Graph-level finite-collar replacement closure for the exact one-collar/v23 closed-walk
rooted shared-edge face-membership-cover shell. -/
theorem
    exists_theorem49CollarLayerPositiveProjectedGeometryOn_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            source.toPlanarBoundaryAnnulusBoundaryData,
      ∃ C₀ : G.EdgeColoring Color,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      ∃ peelFaces : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        source.boundaryFaceRoots,
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        source.boundaryFaceRoots,
      ∃ _hpeelInterior : ∀ f ∈ peelFaces,
          Disjoint (emb.faceBoundary f.1)
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces),
      ∃ _hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces source.boundaryFaceRoots
              hcoverRoots hsepRoots)
            source.fallbackEdge),
      ∃ _hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              source.boundaryFaceRoots hcoverRoots hsepRoots)
            source.fallbackEdge f),
        e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
          ∃ g ∈ peelFaces,
            (interiorDualSpanningForest emb.faceBoundary emb.faces).Adj f g ∧
            e ∈ emb.faceBoundary g.1 ∧
            (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                f
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                  source.boundaryFaceRoots hcoverRoots hsepRoots f) <
              (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                g
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                  source.boundaryFaceRoots hcoverRoots hsepRoots g),
      HasUnblockedInteriorEndpoint emb) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49CollarLayerPositiveProjectedGeometryOn emb := by
  rcases h with
    ⟨emb, source, hcurrent, C₀, a, b, faceBoundary, hv23, peelFaces, hunique, hcoverRoots,
      hsepRoots, hpeelInterior, hcover, hchildren, hEndpoint⟩
  exact
    ⟨emb,
      theorem49CollarLayerPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint
        source hcurrent C₀ hv23 peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover
        hchildren hEndpoint⟩

/-- Graph-level finite-collar replacement closure for the exact one-collar/v23 successor-cycle
rooted shared-edge face-membership-cover shell. -/
theorem
    exists_theorem49CollarLayerPositiveProjectedGeometryOn_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
        (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            boundaryData.toPlanarBoundaryAnnulusBoundaryData,
      ∃ C₀ : G.EdgeColoring Color,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      ∃ peelFaces : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots,
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots,
      ∃ _hpeelInterior : ∀ f ∈ peelFaces,
          Disjoint (emb.faceBoundary f.1)
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces),
      ∃ _hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
              hcoverRoots hsepRoots)
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hselectedBoundaryArc).fallbackEdge),
      ∃ _hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
              hcoverRoots hsepRoots)
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hselectedBoundaryArc).fallbackEdge f),
        e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
          ∃ g ∈ peelFaces,
            (interiorDualSpanningForest emb.faceBoundary emb.faces).Adj f g ∧
            e ∈ emb.faceBoundary g.1 ∧
            (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                f
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                  (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                    boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
                  hcoverRoots hsepRoots f) <
              (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                g
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                  (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                    boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
                  hcoverRoots hsepRoots g),
      HasUnblockedInteriorEndpoint emb) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49CollarLayerPositiveProjectedGeometryOn emb := by
  rcases h with
    ⟨emb, boundaryData, dartCycles, hselectedBoundaryArc, hcurrent, C₀, a, b, faceBoundary, hv23,
      peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover, hchildren, hEndpoint⟩
  exact
    ⟨emb,
      theorem49CollarLayerPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint
        boundaryData dartCycles hselectedBoundaryArc hcurrent C₀ hv23 peelFaces hunique
        hcoverRoots hsepRoots hpeelInterior hcover hchildren hEndpoint⟩

/-- On the exact one-collar closed-walk shell, same-split annulus-root parent-peel data already
supplies the local boundary-free incident-face selector needed by the selector route. -/
theorem
    nonempty_boundaryFreeIncidentFaceSelector_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (_source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          _source.toPlanarBoundaryAnnulusBoundaryData)
    (_C₀ : G.EdgeColoring Color)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState _C₀ a b faceBoundary))
    (parentData : PlanarBoundaryAnnulusRootParentPeelData emb)
    (_hparentBoundary :
      parentData.boundaryData = _source.toPlanarBoundaryAnnulusBoundaryData) :
    Nonempty (BoundaryFreeIncidentFaceSelector emb) :=
  nonempty_boundaryFreeIncidentFaceSelector_of_planarBoundaryAnnulusRootParentPeelData parentData

/-- Successor-cycle form of the same exact-shell parent-peel-to-selector consequence. -/
theorem
    nonempty_boundaryFreeIncidentFaceSelector_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (_boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (_dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (_hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
      (_dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          _boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (_C₀ : G.EdgeColoring Color)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState _C₀ a b faceBoundary))
    (parentData : PlanarBoundaryAnnulusRootParentPeelData emb)
    (_hparentBoundary :
      parentData.boundaryData = _boundaryData.toPlanarBoundaryAnnulusBoundaryData) :
    Nonempty (BoundaryFreeIncidentFaceSelector emb) :=
  nonempty_boundaryFreeIncidentFaceSelector_of_planarBoundaryAnnulusRootParentPeelData parentData

/-- On the exact one-collar closed-walk shell, generic boundary-root adjacency-distance data
already supplies the local boundary-free incident-face selector shell. -/
theorem
    nonempty_boundaryFreeIncidentFaceSelector_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (_source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          _source.toPlanarBoundaryAnnulusBoundaryData)
    (_C₀ : G.EdgeColoring Color)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState _C₀ a b faceBoundary))
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) :
    Nonempty (BoundaryFreeIncidentFaceSelector emb) :=
  nonempty_boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootAdjDistancePeelData
    interiorData

/-- Successor-cycle form of the same exact-shell adjacency-distance-to-selector consequence. -/
theorem
    nonempty_boundaryFreeIncidentFaceSelector_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (_boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (_dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (_hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
      (_dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          _boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (_C₀ : G.EdgeColoring Color)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState _C₀ a b faceBoundary))
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) :
    Nonempty (BoundaryFreeIncidentFaceSelector emb) :=
  nonempty_boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootAdjDistancePeelData
    interiorData

/-- Existential exact-shell closed-walk data with same-split annulus-root parent peel data and a
local endpoint witness packages into the graph-level closed-walk annulus-parent positive route
surface. -/
theorem
    nonempty_theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometry_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            source.toPlanarBoundaryAnnulusBoundaryData,
      ∃ C₀ : G.EdgeColoring Color,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      ∃ parentData : PlanarBoundaryAnnulusRootParentPeelData emb,
        parentData.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData ∧
          HasUnblockedInteriorEndpoint emb) :
    Nonempty (Theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometry G) := by
  rcases h with
    ⟨emb, source, hcurrent, C₀, a, b, faceBoundary, hv23, parentData, hparentBoundary, hEndpoint⟩
  exact
    ⟨{ emb := emb,
        source := source,
        interiorData := parentData.interiorData,
        carrier_nonempty :=
          (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
            emb).1 hEndpoint }⟩

/-- Successor-cycle form of the same graph-level packaging for the exact one-collar
v23/v23.5 annulus-parent route surface. -/
theorem
    nonempty_theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometry_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
        (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            boundaryData.toPlanarBoundaryAnnulusBoundaryData,
      ∃ C₀ : G.EdgeColoring Color,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      ∃ parentData : PlanarBoundaryAnnulusRootParentPeelData emb,
        parentData.boundaryData = boundaryData.toPlanarBoundaryAnnulusBoundaryData ∧
          HasUnblockedInteriorEndpoint emb) :
    Nonempty (Theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometry G) := by
  rcases h with
    ⟨emb, boundaryData, dartCycles, hselectedBoundaryArc, hcurrent, C₀, a, b, faceBoundary, hv23,
      parentData, hparentBoundary, hEndpoint⟩
  exact
    ⟨{ emb := emb,
        boundaryData := boundaryData,
        dartCycles := dartCycles,
        interiorData := parentData.interiorData,
        selectedBoundaryArc := hselectedBoundaryArc,
        carrier_nonempty :=
          (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
            emb).1 hEndpoint }⟩

/-- Existential exact-shell closed-walk data with same-embedding generic boundary-root
adjacency-distance data and a local endpoint witness packages into the graph-level closed-walk
annulus root-distance positive route surface. -/
theorem
    nonempty_theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometry_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            source.toPlanarBoundaryAnnulusBoundaryData,
      ∃ C₀ : G.EdgeColoring Color,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      ∃ peelFaces : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        source.boundaryFaceRoots,
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        source.boundaryFaceRoots,
      ∃ _hpeelInterior : ∀ f ∈ peelFaces,
          Disjoint (emb.faceBoundary f.1)
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces),
      ∃ _hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces source.boundaryFaceRoots
              hcoverRoots hsepRoots)
            source.fallbackEdge),
      ∃ _hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              source.boundaryFaceRoots hcoverRoots hsepRoots)
            source.fallbackEdge f),
        e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
          ∃ g ∈ peelFaces,
            (interiorDualSpanningForest emb.faceBoundary emb.faces).Adj f g ∧
            e ∈ emb.faceBoundary g.1 ∧
            (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                f
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                  source.boundaryFaceRoots hcoverRoots hsepRoots f) <
              (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                g
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                  source.boundaryFaceRoots hcoverRoots hsepRoots g),
      HasUnblockedInteriorEndpoint emb) :
    Nonempty (Theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometry G) := by
  rcases h with
    ⟨emb, source, hcurrent, C₀, a, b, faceBoundary, hv23, peelFaces, hunique, hcoverRoots,
      hsepRoots, hpeelInterior, hcover, hchildren, hEndpoint⟩
  exact
    nonempty_theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometry_of_exists_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint
      ⟨emb, source, peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover,
        hchildren, hEndpoint⟩

/-- Successor-cycle form of the same graph-level packaging for the exact one-collar v23/v23.5
rooted-cover annulus root-distance route surface. -/
theorem
    nonempty_theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometry_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
        (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            boundaryData.toPlanarBoundaryAnnulusBoundaryData,
      ∃ C₀ : G.EdgeColoring Color,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      ∃ peelFaces : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles _hselectedBoundaryArc).boundaryFaceRoots,
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles _hselectedBoundaryArc).boundaryFaceRoots,
      ∃ _hpeelInterior : ∀ f ∈ peelFaces,
          Disjoint (emb.faceBoundary f.1)
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces),
      ∃ _hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                boundaryData dartCycles _hselectedBoundaryArc).boundaryFaceRoots
              hcoverRoots hsepRoots)
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles _hselectedBoundaryArc).fallbackEdge),
      ∃ _hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                boundaryData dartCycles _hselectedBoundaryArc).boundaryFaceRoots
              hcoverRoots hsepRoots)
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles _hselectedBoundaryArc).fallbackEdge f),
        e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
          ∃ g ∈ peelFaces,
            (interiorDualSpanningForest emb.faceBoundary emb.faces).Adj f g ∧
            e ∈ emb.faceBoundary g.1 ∧
            (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                f
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                  (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                    boundaryData dartCycles _hselectedBoundaryArc).boundaryFaceRoots
                  hcoverRoots hsepRoots f) <
              (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                g
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                  (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                    boundaryData dartCycles _hselectedBoundaryArc).boundaryFaceRoots
                  hcoverRoots hsepRoots g),
      HasUnblockedInteriorEndpoint emb) :
    Nonempty (Theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometry G) := by
  rcases h with
    ⟨emb, boundaryData, dartCycles, hselectedBoundaryArc, hcurrent, C₀, a, b, faceBoundary, hv23,
      peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover, hchildren,
      hEndpoint⟩
  exact
    nonempty_theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometry_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint
      ⟨emb, boundaryData, dartCycles, hselectedBoundaryArc, peelFaces, hunique, hcoverRoots,
        hsepRoots, hpeelInterior, hcover, hchildren, hEndpoint⟩

/-- Existential exact-shell closed-walk data with same-embedding generic boundary-root
adjacency-distance data and a local endpoint witness packages into the graph-level closed-walk
annulus root-distance positive route surface. -/
theorem
    nonempty_theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometry_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            source.toPlanarBoundaryAnnulusBoundaryData,
      ∃ C₀ : G.EdgeColoring Color,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      ∃ _interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
        HasUnblockedInteriorEndpoint emb) :
    Nonempty (Theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometry G) := by
  rcases h with
    ⟨emb, source, hcurrent, C₀, a, b, faceBoundary, hv23, interiorData, hEndpoint⟩
  exact
    ⟨{ emb := emb,
        source := source,
        interiorData := interiorData,
        carrier_nonempty :=
          (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
            emb).1 hEndpoint }⟩

/-- Successor-cycle form of the same graph-level packaging for the exact one-collar
v23/v23.5 annulus root-distance route surface. -/
theorem
    nonempty_theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometry_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
        (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            boundaryData.toPlanarBoundaryAnnulusBoundaryData,
      ∃ C₀ : G.EdgeColoring Color,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      ∃ _interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
        HasUnblockedInteriorEndpoint emb) :
    Nonempty (Theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometry G) := by
  rcases h with
    ⟨emb, boundaryData, dartCycles, hselectedBoundaryArc, hcurrent, C₀, a, b, faceBoundary, hv23,
      interiorData, hEndpoint⟩
  exact
    ⟨{ emb := emb,
        boundaryData := boundaryData,
        dartCycles := dartCycles,
        interiorData := interiorData,
        selectedBoundaryArc := hselectedBoundaryArc,
        carrier_nonempty :=
          (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
            emb).1 hEndpoint }⟩

/-- The closed-walk annulus root-parent positive route surface already lowers to residual
current-boundary positive geometry on the same embedding. -/
theorem
    theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_closedWalkAnnulusRootParentPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometryOn emb) :
    Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb := by
  exact
    (theorem49ResidualBoundaryPositiveProjectedGeometryOn_iff_collarLayerPositiveProjectedGeometryOn).2
      (theorem49CollarLayerPositiveProjectedGeometryOn_of_closedWalkAnnulusRootParentPositiveProjectedGeometryOn
        geom)

/-- The successor-cycle annulus root-parent positive route surface lowers to the same residual
current-boundary positive geometry interface. -/
theorem
    theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_successorCycleAnnulusRootParentPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometryOn emb) :
    Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb := by
  exact
    (theorem49ResidualBoundaryPositiveProjectedGeometryOn_iff_collarLayerPositiveProjectedGeometryOn).2
      (theorem49CollarLayerPositiveProjectedGeometryOn_of_successorCycleAnnulusRootParentPositiveProjectedGeometryOn
        geom)

/-- The closed-walk annulus root-parent positive route surface also already carries a residual
current-boundary remainder witness on the same embedding. -/
theorem
    theorem49CurrentBoundaryRemainders_of_closedWalkAnnulusRootParentPositiveProjectedGeometryOn_via_residualBoundary
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometryOn emb) :
    ∃ data : PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb,
      ∃ i : Fin data.numLayers, ∃ f ∈ data.layerFaces i,
        ∀ e ∈ (emb.faceBoundary f.1).erase (data.witnessEdge f), e ∈ data.currentBoundary i := by
  exact
    theorem49CurrentBoundaryRemainders_of_residualBoundaryPositiveProjectedGeometryOn
      (theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_closedWalkAnnulusRootParentPositiveProjectedGeometryOn
        geom)

/-- The successor-cycle annulus root-parent positive route surface carries the same residual
current-boundary remainder witness interface. -/
theorem
    theorem49CurrentBoundaryRemainders_of_successorCycleAnnulusRootParentPositiveProjectedGeometryOn_via_residualBoundary
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometryOn emb) :
    ∃ data : PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb,
      ∃ i : Fin data.numLayers, ∃ f ∈ data.layerFaces i,
        ∀ e ∈ (emb.faceBoundary f.1).erase (data.witnessEdge f), e ∈ data.currentBoundary i := by
  exact
    theorem49CurrentBoundaryRemainders_of_residualBoundaryPositiveProjectedGeometryOn
      (theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_successorCycleAnnulusRootParentPositiveProjectedGeometryOn
        geom)

/-- The exact one-collar v23/v23.5 closed-walk shell already reaches residual-boundary positive
geometry once it carries same-split annulus-root parent peel data and an unblocked interior
endpoint. -/
theorem
    theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          source.toPlanarBoundaryAnnulusBoundaryData)
    (_C₀ : G.EdgeColoring Color)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState _C₀ a b faceBoundary))
    (parentData : PlanarBoundaryAnnulusRootParentPeelData emb)
    (_hparentBoundary :
      parentData.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb := by
  exact
    theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_closedWalkAnnulusRootParentPositiveProjectedGeometryOn
      (theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint
        source _hcurrent _C₀ _hv23 parentData _hparentBoundary hEndpoint)

/-- Successor-cycle form of the same exact one-collar v23/v23.5 parent-peel residual-boundary
lowering. -/
theorem
    theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (_hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (_C₀ : G.EdgeColoring Color)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState _C₀ a b faceBoundary))
    (parentData : PlanarBoundaryAnnulusRootParentPeelData emb)
    (_hparentBoundary :
      parentData.boundaryData = boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb := by
  exact
    theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_successorCycleAnnulusRootParentPositiveProjectedGeometryOn
      (theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint
        boundaryData dartCycles _hselectedBoundaryArc _hcurrent _C₀ _hv23 parentData
        _hparentBoundary hEndpoint)

/-- The same exact one-collar v23/v23.5 closed-walk parent-peel shell already yields a concrete
current-boundary remainder witness on the same embedding. -/
theorem
    theorem49CurrentBoundaryRemainders_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint_via_residualBoundary
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          source.toPlanarBoundaryAnnulusBoundaryData)
    (_C₀ : G.EdgeColoring Color)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState _C₀ a b faceBoundary))
    (parentData : PlanarBoundaryAnnulusRootParentPeelData emb)
    (_hparentBoundary :
      parentData.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    ∃ data : PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb,
      ∃ i : Fin data.numLayers, ∃ f ∈ data.layerFaces i,
        ∀ e ∈ (emb.faceBoundary f.1).erase (data.witnessEdge f), e ∈ data.currentBoundary i := by
  exact
    theorem49CurrentBoundaryRemainders_of_closedWalkAnnulusRootParentPositiveProjectedGeometryOn_via_residualBoundary
      (theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint
        source _hcurrent _C₀ _hv23 parentData _hparentBoundary hEndpoint)

/-- Successor-cycle form of the same exact one-collar v23/v23.5 parent-peel current-boundary
remainder consequence. -/
theorem
    theorem49CurrentBoundaryRemainders_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint_via_residualBoundary
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (_hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (_C₀ : G.EdgeColoring Color)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState _C₀ a b faceBoundary))
    (parentData : PlanarBoundaryAnnulusRootParentPeelData emb)
    (_hparentBoundary :
      parentData.boundaryData = boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    ∃ data : PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb,
      ∃ i : Fin data.numLayers, ∃ f ∈ data.layerFaces i,
        ∀ e ∈ (emb.faceBoundary f.1).erase (data.witnessEdge f), e ∈ data.currentBoundary i := by
  exact
    theorem49CurrentBoundaryRemainders_of_successorCycleAnnulusRootParentPositiveProjectedGeometryOn_via_residualBoundary
      (theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint
        boundaryData dartCycles _hselectedBoundaryArc _hcurrent _C₀ _hv23 parentData
        _hparentBoundary hEndpoint)

/-- Graph-level residual-positive closure for the exact one-collar/v23 closed-walk parent-peel
shell. -/
theorem
    exists_embedding_residualBoundaryPositiveProjectedGeometryOn_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            source.toPlanarBoundaryAnnulusBoundaryData,
      ∃ C₀ : G.EdgeColoring Color,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      ∃ parentData : PlanarBoundaryAnnulusRootParentPeelData emb,
        parentData.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData ∧
          HasUnblockedInteriorEndpoint emb) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb := by
  rcases h with
    ⟨emb, source, hcurrent, C₀, a, b, faceBoundary, hv23, parentData, hparentBoundary,
      hEndpoint⟩
  exact
    ⟨emb,
      theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint
        source hcurrent C₀ hv23 parentData hparentBoundary hEndpoint⟩

/-- Graph-level current-boundary remainder closure for the exact one-collar/v23 closed-walk
parent-peel shell. -/
theorem
    exists_embedding_currentBoundaryRemainders_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint_via_residualBoundary
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            source.toPlanarBoundaryAnnulusBoundaryData,
      ∃ C₀ : G.EdgeColoring Color,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      ∃ parentData : PlanarBoundaryAnnulusRootParentPeelData emb,
        parentData.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData ∧
          HasUnblockedInteriorEndpoint emb) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb,
      ∃ i : Fin data.numLayers, ∃ f ∈ data.layerFaces i,
        ∀ e ∈ (emb.faceBoundary f.1).erase (data.witnessEdge f), e ∈ data.currentBoundary i := by
  rcases h with
    ⟨emb, source, hcurrent, C₀, a, b, faceBoundary, hv23, parentData, hparentBoundary,
      hEndpoint⟩
  rcases
    theorem49CurrentBoundaryRemainders_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint_via_residualBoundary
      source hcurrent C₀ hv23 parentData hparentBoundary hEndpoint with
    ⟨data, i, f, hf, hremainders⟩
  exact ⟨emb, data, i, f, hf, hremainders⟩

/-- Graph-level residual-positive closure for the exact one-collar/v23 successor-cycle
parent-peel shell. -/
theorem
    exists_embedding_residualBoundaryPositiveProjectedGeometryOn_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
        (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            boundaryData.toPlanarBoundaryAnnulusBoundaryData,
      ∃ C₀ : G.EdgeColoring Color,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      ∃ parentData : PlanarBoundaryAnnulusRootParentPeelData emb,
        parentData.boundaryData = boundaryData.toPlanarBoundaryAnnulusBoundaryData ∧
          HasUnblockedInteriorEndpoint emb) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb := by
  rcases h with
    ⟨emb, boundaryData, dartCycles, hselectedBoundaryArc, hcurrent, C₀, a, b, faceBoundary, hv23,
      parentData, hparentBoundary, hEndpoint⟩
  exact
    ⟨emb,
      theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint
        boundaryData dartCycles hselectedBoundaryArc hcurrent C₀ hv23 parentData hparentBoundary
        hEndpoint⟩

/-- Graph-level current-boundary remainder closure for the exact one-collar/v23 successor-cycle
parent-peel shell. -/
theorem
    exists_embedding_currentBoundaryRemainders_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint_via_residualBoundary
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
        (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            boundaryData.toPlanarBoundaryAnnulusBoundaryData,
      ∃ C₀ : G.EdgeColoring Color,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      ∃ parentData : PlanarBoundaryAnnulusRootParentPeelData emb,
        parentData.boundaryData = boundaryData.toPlanarBoundaryAnnulusBoundaryData ∧
          HasUnblockedInteriorEndpoint emb) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb,
      ∃ i : Fin data.numLayers, ∃ f ∈ data.layerFaces i,
        ∀ e ∈ (emb.faceBoundary f.1).erase (data.witnessEdge f), e ∈ data.currentBoundary i := by
  rcases h with
    ⟨emb, boundaryData, dartCycles, hselectedBoundaryArc, hcurrent, C₀, a, b, faceBoundary, hv23,
      parentData, hparentBoundary, hEndpoint⟩
  rcases
    theorem49CurrentBoundaryRemainders_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint_via_residualBoundary
      boundaryData dartCycles hselectedBoundaryArc hcurrent C₀ hv23 parentData hparentBoundary
      hEndpoint with
    ⟨data, i, f, hf, hremainders⟩
  exact ⟨emb, data, i, f, hf, hremainders⟩

/-- The closed-walk annulus root-distance positive route surface already lowers to residual
current-boundary positive geometry on the same embedding. -/
theorem
    theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_closedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn emb) :
    Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb := by
  exact
    (theorem49ResidualBoundaryPositiveProjectedGeometryOn_iff_collarLayerPositiveProjectedGeometryOn).2
      (theorem49CollarLayerPositiveProjectedGeometryOn_of_closedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn
        geom)

/-- The successor-cycle annulus root-distance positive route surface lowers to the same residual
current-boundary positive geometry interface. -/
theorem
    theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_successorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn emb) :
    Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb := by
  exact
    (theorem49ResidualBoundaryPositiveProjectedGeometryOn_iff_collarLayerPositiveProjectedGeometryOn).2
      (theorem49CollarLayerPositiveProjectedGeometryOn_of_successorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn
        geom)

/-- The closed-walk annulus root-distance positive route surface also already carries a residual
current-boundary remainder witness on the same embedding. -/
theorem
    theorem49CurrentBoundaryRemainders_of_closedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn_via_residualBoundary
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn emb) :
    ∃ data : PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb,
      ∃ i : Fin data.numLayers, ∃ f ∈ data.layerFaces i,
        ∀ e ∈ (emb.faceBoundary f.1).erase (data.witnessEdge f), e ∈ data.currentBoundary i := by
  exact
    theorem49CurrentBoundaryRemainders_of_residualBoundaryPositiveProjectedGeometryOn
      (theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_closedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn
        geom)

/-- The successor-cycle annulus root-distance positive route surface carries the same residual
current-boundary remainder witness interface. -/
theorem
    theorem49CurrentBoundaryRemainders_of_successorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn_via_residualBoundary
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn emb) :
    ∃ data : PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb,
      ∃ i : Fin data.numLayers, ∃ f ∈ data.layerFaces i,
        ∀ e ∈ (emb.faceBoundary f.1).erase (data.witnessEdge f), e ∈ data.currentBoundary i := by
  exact
    theorem49CurrentBoundaryRemainders_of_residualBoundaryPositiveProjectedGeometryOn
      (theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_successorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn
        geom)

/-- The exact rooted-cover closed-walk one-collar shell already reaches residual-boundary
positive geometry directly on the same embedding, without unpacking the intermediate
root-distance route package by hand. -/
theorem
    theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          source.toPlanarBoundaryAnnulusBoundaryData)
    (_C₀ : G.EdgeColoring Color)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState _C₀ a b faceBoundary))
    (peelFaces : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces source.boundaryFaceRoots
          hcoverRoots hsepRoots)
        source.fallbackEdge))
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
        (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
            source.boundaryFaceRoots hcoverRoots hsepRoots)
          source.fallbackEdge f),
      e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
        ∃ g ∈ peelFaces,
          (interiorDualSpanningForest emb.faceBoundary emb.faces).Adj f g ∧
          e ∈ emb.faceBoundary g.1 ∧
          (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
              f
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                source.boundaryFaceRoots hcoverRoots hsepRoots f) <
            (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
              g
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                source.boundaryFaceRoots hcoverRoots hsepRoots g))
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb := by
  exact
    theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint
      source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover hchildren hEndpoint

/-- Successor-cycle form of the same direct exact-shell rooted-cover residual-boundary lowering. -/
theorem
    theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (_C₀ : G.EdgeColoring Color)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState _C₀ a b faceBoundary))
    (peelFaces : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
          hcoverRoots hsepRoots)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hselectedBoundaryArc).fallbackEdge))
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
        (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
            hcoverRoots hsepRoots)
          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hselectedBoundaryArc).fallbackEdge f),
      e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
        ∃ g ∈ peelFaces,
          (interiorDualSpanningForest emb.faceBoundary emb.faces).Adj f g ∧
          e ∈ emb.faceBoundary g.1 ∧
          (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
              f
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                  boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
                hcoverRoots hsepRoots f) <
            (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
              g
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                  boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
                hcoverRoots hsepRoots g))
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb := by
  exact
    theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint
      boundaryData dartCycles hselectedBoundaryArc peelFaces hunique hcoverRoots hsepRoots
      hpeelInterior hcover hchildren hEndpoint

/-- The same exact rooted-cover closed-walk one-collar shell already yields a concrete
current-boundary remainder witness on the same embedding. -/
theorem
    theorem49CurrentBoundaryRemainders_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint_via_residualBoundary
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          source.toPlanarBoundaryAnnulusBoundaryData)
    (_C₀ : G.EdgeColoring Color)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState _C₀ a b faceBoundary))
    (peelFaces : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces source.boundaryFaceRoots
          hcoverRoots hsepRoots)
        source.fallbackEdge))
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
        (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
            source.boundaryFaceRoots hcoverRoots hsepRoots)
          source.fallbackEdge f),
      e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
        ∃ g ∈ peelFaces,
          (interiorDualSpanningForest emb.faceBoundary emb.faces).Adj f g ∧
          e ∈ emb.faceBoundary g.1 ∧
          (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
              f
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                source.boundaryFaceRoots hcoverRoots hsepRoots f) <
            (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
              g
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                source.boundaryFaceRoots hcoverRoots hsepRoots g))
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    ∃ i : Fin
        ((residualBoundarySelectorData_of_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData
          source.toPlanarBoundaryAnnulusBoundaryData
          (interiorDualBoundaryRootAdjDistancePeelDataOfClosedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover
            source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover hchildren)).toResidualBoundaryLayerFacePeelWitnessData.numLayers),
      ∃ f ∈
          (residualBoundarySelectorData_of_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData
            source.toPlanarBoundaryAnnulusBoundaryData
            (interiorDualBoundaryRootAdjDistancePeelDataOfClosedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover
              source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover hchildren)).toResidualBoundaryLayerFacePeelWitnessData.layerFaces i,
        ∀ e ∈ (emb.faceBoundary f.1).erase
            ((residualBoundarySelectorData_of_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData
              source.toPlanarBoundaryAnnulusBoundaryData
              (interiorDualBoundaryRootAdjDistancePeelDataOfClosedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover
                source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover hchildren)).toResidualBoundaryLayerFacePeelWitnessData.witnessEdge f),
          e ∈
            (residualBoundarySelectorData_of_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData
              source.toPlanarBoundaryAnnulusBoundaryData
              (interiorDualBoundaryRootAdjDistancePeelDataOfClosedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover
                source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover hchildren)).toResidualBoundaryLayerFacePeelWitnessData.currentBoundary i := by
  exact
    theorem49CurrentBoundaryRemainders_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint_via_residualBoundary
      source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover hchildren hEndpoint

/-- Successor-cycle form of the same exact-shell rooted-cover current-boundary remainder
consequence. -/
theorem
    theorem49CurrentBoundaryRemainders_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint_via_residualBoundary
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (_C₀ : G.EdgeColoring Color)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState _C₀ a b faceBoundary))
    (peelFaces : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
          hcoverRoots hsepRoots)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hselectedBoundaryArc).fallbackEdge))
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
        (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
            hcoverRoots hsepRoots)
          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hselectedBoundaryArc).fallbackEdge f),
      e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
        ∃ g ∈ peelFaces,
          (interiorDualSpanningForest emb.faceBoundary emb.faces).Adj f g ∧
          e ∈ emb.faceBoundary g.1 ∧
          (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
              f
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                  boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
                hcoverRoots hsepRoots f) <
            (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
              g
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                  boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
                hcoverRoots hsepRoots g))
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    ∃ i : Fin
        ((residualBoundarySelectorData_of_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData
          boundaryData.toPlanarBoundaryAnnulusBoundaryData
          (interiorDualBoundaryRootAdjDistancePeelData_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover
            boundaryData dartCycles hselectedBoundaryArc peelFaces hunique hcoverRoots hsepRoots
            hpeelInterior hcover hchildren)).toResidualBoundaryLayerFacePeelWitnessData.numLayers),
      ∃ f ∈
          (residualBoundarySelectorData_of_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData
            boundaryData.toPlanarBoundaryAnnulusBoundaryData
            (interiorDualBoundaryRootAdjDistancePeelData_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover
              boundaryData dartCycles hselectedBoundaryArc peelFaces hunique hcoverRoots hsepRoots
              hpeelInterior hcover hchildren)).toResidualBoundaryLayerFacePeelWitnessData.layerFaces i,
        ∀ e ∈ (emb.faceBoundary f.1).erase
            ((residualBoundarySelectorData_of_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData.toPlanarBoundaryAnnulusBoundaryData
              (interiorDualBoundaryRootAdjDistancePeelData_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover
                boundaryData dartCycles hselectedBoundaryArc peelFaces hunique hcoverRoots hsepRoots
                hpeelInterior hcover hchildren)).toResidualBoundaryLayerFacePeelWitnessData.witnessEdge f),
          e ∈
            (residualBoundarySelectorData_of_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData.toPlanarBoundaryAnnulusBoundaryData
              (interiorDualBoundaryRootAdjDistancePeelData_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover
                boundaryData dartCycles hselectedBoundaryArc peelFaces hunique hcoverRoots hsepRoots
                hpeelInterior hcover hchildren)).toResidualBoundaryLayerFacePeelWitnessData.currentBoundary i := by
  exact
    theorem49CurrentBoundaryRemainders_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint_via_residualBoundary
      boundaryData dartCycles hselectedBoundaryArc peelFaces hunique hcoverRoots hsepRoots
      hpeelInterior hcover hchildren hEndpoint

/-- Graph-level residual-positive closure for the exact one-collar/v23 closed-walk rooted-cover
shell. -/
theorem
    exists_embedding_residualBoundaryPositiveProjectedGeometryOn_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            source.toPlanarBoundaryAnnulusBoundaryData,
      ∃ C₀ : G.EdgeColoring Color,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      ∃ peelFaces : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        source.boundaryFaceRoots,
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        source.boundaryFaceRoots,
      ∃ _hpeelInterior : ∀ f ∈ peelFaces,
          Disjoint (emb.faceBoundary f.1)
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces),
      ∃ _hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces source.boundaryFaceRoots
              hcoverRoots hsepRoots)
            source.fallbackEdge),
      ∃ _hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              source.boundaryFaceRoots hcoverRoots hsepRoots)
            source.fallbackEdge f),
        e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
          ∃ g ∈ peelFaces,
            (interiorDualSpanningForest emb.faceBoundary emb.faces).Adj f g ∧
            e ∈ emb.faceBoundary g.1 ∧
            (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                f
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                  source.boundaryFaceRoots hcoverRoots hsepRoots f) <
              (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                g
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                  source.boundaryFaceRoots hcoverRoots hsepRoots g),
      HasUnblockedInteriorEndpoint emb) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb := by
  rcases h with
    ⟨emb, source, hcurrent, C₀, a, b, faceBoundary, hv23, peelFaces, hunique, hcoverRoots,
      hsepRoots, hpeelInterior, hcover, hchildren, hEndpoint⟩
  exact
    ⟨emb,
      theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint
        source hcurrent C₀ hv23 peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover
        hchildren hEndpoint⟩

/-- Graph-level current-boundary remainder closure for the exact one-collar/v23 closed-walk
rooted-cover shell. -/
theorem
    exists_embedding_currentBoundaryRemainders_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint_via_residualBoundary
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            source.toPlanarBoundaryAnnulusBoundaryData,
      ∃ C₀ : G.EdgeColoring Color,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      ∃ peelFaces : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        source.boundaryFaceRoots,
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        source.boundaryFaceRoots,
      ∃ _hpeelInterior : ∀ f ∈ peelFaces,
          Disjoint (emb.faceBoundary f.1)
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces),
      ∃ _hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces source.boundaryFaceRoots
              hcoverRoots hsepRoots)
            source.fallbackEdge),
      ∃ _hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              source.boundaryFaceRoots hcoverRoots hsepRoots)
            source.fallbackEdge f),
        e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
          ∃ g ∈ peelFaces,
            (interiorDualSpanningForest emb.faceBoundary emb.faces).Adj f g ∧
            e ∈ emb.faceBoundary g.1 ∧
            (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                f
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                  source.boundaryFaceRoots hcoverRoots hsepRoots f) <
              (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                g
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                  source.boundaryFaceRoots hcoverRoots hsepRoots g),
      HasUnblockedInteriorEndpoint emb) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb,
      ∃ i : Fin data.numLayers, ∃ f ∈ data.layerFaces i,
        ∀ e ∈ (emb.faceBoundary f.1).erase (data.witnessEdge f), e ∈ data.currentBoundary i := by
  rcases h with
    ⟨emb, source, hcurrent, C₀, a, b, faceBoundary, hv23, peelFaces, hunique, hcoverRoots,
      hsepRoots, hpeelInterior, hcover, hchildren, hEndpoint⟩
  rcases
    theorem49CurrentBoundaryRemainders_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint_via_residualBoundary
      source hcurrent C₀ hv23 peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover
      hchildren hEndpoint with
    ⟨i, f, hf, hremainders⟩
  exact
    ⟨emb,
      (residualBoundarySelectorData_of_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData
        source.toPlanarBoundaryAnnulusBoundaryData
        (interiorDualBoundaryRootAdjDistancePeelDataOfClosedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover
          source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover hchildren)).toResidualBoundaryLayerFacePeelWitnessData,
      i, f, hf, hremainders⟩

/-- Graph-level residual-positive closure for the exact one-collar/v23 successor-cycle
rooted-cover shell. -/
theorem
    exists_embedding_residualBoundaryPositiveProjectedGeometryOn_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
        (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            boundaryData.toPlanarBoundaryAnnulusBoundaryData,
      ∃ C₀ : G.EdgeColoring Color,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      ∃ peelFaces : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots,
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots,
      ∃ _hpeelInterior : ∀ f ∈ peelFaces,
          Disjoint (emb.faceBoundary f.1)
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces),
      ∃ _hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
              hcoverRoots hsepRoots)
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hselectedBoundaryArc).fallbackEdge),
      ∃ _hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
              hcoverRoots hsepRoots)
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hselectedBoundaryArc).fallbackEdge f),
        e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
          ∃ g ∈ peelFaces,
            (interiorDualSpanningForest emb.faceBoundary emb.faces).Adj f g ∧
            e ∈ emb.faceBoundary g.1 ∧
            (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                f
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                  (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                    boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
                  hcoverRoots hsepRoots f) <
              (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                g
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                  (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                    boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
                  hcoverRoots hsepRoots g),
      HasUnblockedInteriorEndpoint emb) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb := by
  rcases h with
    ⟨emb, boundaryData, dartCycles, hselectedBoundaryArc, hcurrent, C₀, a, b, faceBoundary, hv23,
      peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover, hchildren,
      hEndpoint⟩
  exact
    ⟨emb,
      theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint
        boundaryData dartCycles hselectedBoundaryArc hcurrent C₀ hv23 peelFaces hunique
        hcoverRoots hsepRoots hpeelInterior hcover hchildren hEndpoint⟩

/-- Graph-level current-boundary remainder closure for the exact one-collar/v23 successor-cycle
rooted-cover shell. -/
theorem
    exists_embedding_currentBoundaryRemainders_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint_via_residualBoundary
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
        (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            boundaryData.toPlanarBoundaryAnnulusBoundaryData,
      ∃ C₀ : G.EdgeColoring Color,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      ∃ peelFaces : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots,
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots,
      ∃ _hpeelInterior : ∀ f ∈ peelFaces,
          Disjoint (emb.faceBoundary f.1)
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces),
      ∃ _hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
              hcoverRoots hsepRoots)
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hselectedBoundaryArc).fallbackEdge),
      ∃ _hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
              hcoverRoots hsepRoots)
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hselectedBoundaryArc).fallbackEdge f),
        e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
          ∃ g ∈ peelFaces,
            (interiorDualSpanningForest emb.faceBoundary emb.faces).Adj f g ∧
            e ∈ emb.faceBoundary g.1 ∧
            (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                f
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                  (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                    boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
                  hcoverRoots hsepRoots f) <
              (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                g
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                  (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                    boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
                  hcoverRoots hsepRoots g),
      HasUnblockedInteriorEndpoint emb) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb,
      ∃ i : Fin data.numLayers, ∃ f ∈ data.layerFaces i,
        ∀ e ∈ (emb.faceBoundary f.1).erase (data.witnessEdge f), e ∈ data.currentBoundary i := by
  rcases h with
    ⟨emb, boundaryData, dartCycles, hselectedBoundaryArc, hcurrent, C₀, a, b, faceBoundary, hv23,
      peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover, hchildren,
      hEndpoint⟩
  rcases
    theorem49CurrentBoundaryRemainders_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint_via_residualBoundary
      boundaryData dartCycles hselectedBoundaryArc hcurrent C₀ hv23 peelFaces hunique hcoverRoots
      hsepRoots hpeelInterior hcover hchildren hEndpoint with
    ⟨i, f, hf, hremainders⟩
  exact
    ⟨emb,
      (residualBoundarySelectorData_of_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData
        boundaryData.toPlanarBoundaryAnnulusBoundaryData
        (interiorDualBoundaryRootAdjDistancePeelData_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover
          boundaryData dartCycles hselectedBoundaryArc peelFaces hunique hcoverRoots hsepRoots
          hpeelInterior hcover hchildren)).toResidualBoundaryLayerFacePeelWitnessData,
      i, f, hf, hremainders⟩

/-- Residual/current-boundary positive geometry is already immediate on the exact v23/v23.5
one-collar shell once that shell carries generic boundary-root adjacency-distance data together
with a surviving purified endpoint witness. -/
theorem
    theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          source.toPlanarBoundaryAnnulusBoundaryData)
    (_C₀ : G.EdgeColoring Color)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState _C₀ a b faceBoundary))
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb := by
  exact
    theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint
      source.toPlanarBoundaryAnnulusBoundaryData interiorData hEndpoint

/-- Successor-cycle form of the same residual/current-boundary lowering on the exact one-collar
v23/v23.5 shell. -/
theorem
    theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (_dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (_hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
      (_dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (_C₀ : G.EdgeColoring Color)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState _C₀ a b faceBoundary))
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb := by
  exact
    theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint
      boundaryData.toPlanarBoundaryAnnulusBoundaryData interiorData hEndpoint

/-- Exact-v23/v23.5 current-boundary remainder witness on the honest closed-walk one-collar
shell once generic boundary-root adjacency-distance data and an unblocked interior endpoint are
available on the same embedding. -/
theorem
    theorem49CurrentBoundaryRemainders_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint_via_residualBoundary
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          source.toPlanarBoundaryAnnulusBoundaryData)
    (_C₀ : G.EdgeColoring Color)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState _C₀ a b faceBoundary))
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    ∃ i : Fin
        ((residualBoundarySelectorData_of_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData
          source.toPlanarBoundaryAnnulusBoundaryData
          interiorData).toResidualBoundaryLayerFacePeelWitnessData.numLayers),
      ∃ f ∈
          (residualBoundarySelectorData_of_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData
            source.toPlanarBoundaryAnnulusBoundaryData
            interiorData).toResidualBoundaryLayerFacePeelWitnessData.layerFaces i,
        ∀ e ∈ (emb.faceBoundary f.1).erase
            ((residualBoundarySelectorData_of_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData
              source.toPlanarBoundaryAnnulusBoundaryData
              interiorData).toResidualBoundaryLayerFacePeelWitnessData.witnessEdge f),
          e ∈
            (residualBoundarySelectorData_of_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData
              source.toPlanarBoundaryAnnulusBoundaryData
              interiorData).toResidualBoundaryLayerFacePeelWitnessData.currentBoundary i := by
  exact
    theorem49CurrentBoundaryRemainders_of_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint
      source.toPlanarBoundaryAnnulusBoundaryData interiorData hEndpoint

/-- Successor-cycle form of the same exact-v23/v23.5 residual/current-boundary remainder witness
theorem. -/
theorem
    theorem49CurrentBoundaryRemainders_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint_via_residualBoundary
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (_dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (_hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
      (_dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (_C₀ : G.EdgeColoring Color)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState _C₀ a b faceBoundary))
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    ∃ i : Fin
        ((residualBoundarySelectorData_of_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData
          boundaryData.toPlanarBoundaryAnnulusBoundaryData
          interiorData).toResidualBoundaryLayerFacePeelWitnessData.numLayers),
      ∃ f ∈
          (residualBoundarySelectorData_of_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData
            boundaryData.toPlanarBoundaryAnnulusBoundaryData
            interiorData).toResidualBoundaryLayerFacePeelWitnessData.layerFaces i,
        ∀ e ∈ (emb.faceBoundary f.1).erase
            ((residualBoundarySelectorData_of_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData.toPlanarBoundaryAnnulusBoundaryData
              interiorData).toResidualBoundaryLayerFacePeelWitnessData.witnessEdge f),
          e ∈
            (residualBoundarySelectorData_of_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData.toPlanarBoundaryAnnulusBoundaryData
              interiorData).toResidualBoundaryLayerFacePeelWitnessData.currentBoundary i := by
  exact
    theorem49CurrentBoundaryRemainders_of_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint
      boundaryData.toPlanarBoundaryAnnulusBoundaryData interiorData hEndpoint

/-- Graph-level residual-positive closure for the exact one-collar/v23 closed-walk shell carrying
same-embedding generic boundary-root adjacency-distance data. -/
theorem
    exists_embedding_residualBoundaryPositiveProjectedGeometryOn_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            source.toPlanarBoundaryAnnulusBoundaryData,
      ∃ C₀ : G.EdgeColoring Color,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      ∃ _interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
        HasUnblockedInteriorEndpoint emb) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb := by
  rcases h with ⟨emb, source, hcurrent, C₀, a, b, faceBoundary, hv23, interiorData, hEndpoint⟩
  exact
    ⟨emb,
      theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint
        source hcurrent C₀ hv23 interiorData hEndpoint⟩

/-- Graph-level current-boundary remainder closure for the exact one-collar/v23 closed-walk shell
carrying same-embedding generic boundary-root adjacency-distance data. -/
theorem
    exists_embedding_currentBoundaryRemainders_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint_via_residualBoundary
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            source.toPlanarBoundaryAnnulusBoundaryData,
      ∃ C₀ : G.EdgeColoring Color,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      ∃ _interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
        HasUnblockedInteriorEndpoint emb) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb,
      ∃ i : Fin data.numLayers, ∃ f ∈ data.layerFaces i,
        ∀ e ∈ (emb.faceBoundary f.1).erase (data.witnessEdge f), e ∈ data.currentBoundary i := by
  rcases h with ⟨emb, source, hcurrent, C₀, a, b, faceBoundary, hv23, interiorData, hEndpoint⟩
  rcases
    theorem49CurrentBoundaryRemainders_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint_via_residualBoundary
      source hcurrent C₀ hv23 interiorData hEndpoint with
    ⟨i, f, hf, hremainders⟩
  exact
    ⟨emb,
      (residualBoundarySelectorData_of_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData
        source.toPlanarBoundaryAnnulusBoundaryData
        interiorData).toResidualBoundaryLayerFacePeelWitnessData,
      i, f, hf, hremainders⟩

/-- Graph-level residual-positive closure for the exact one-collar/v23 successor-cycle shell
carrying same-embedding generic boundary-root adjacency-distance data. -/
theorem
    exists_embedding_residualBoundaryPositiveProjectedGeometryOn_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
        (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            boundaryData.toPlanarBoundaryAnnulusBoundaryData,
      ∃ C₀ : G.EdgeColoring Color,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      ∃ _interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
        HasUnblockedInteriorEndpoint emb) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb := by
  rcases h with
    ⟨emb, boundaryData, dartCycles, hselectedBoundaryArc, hcurrent, C₀, a, b, faceBoundary, hv23,
      interiorData, hEndpoint⟩
  exact
    ⟨emb,
      theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint
        boundaryData dartCycles hselectedBoundaryArc hcurrent C₀ hv23 interiorData hEndpoint⟩

/-- Graph-level current-boundary remainder closure for the exact one-collar/v23 successor-cycle
shell carrying same-embedding generic boundary-root adjacency-distance data. -/
theorem
    exists_embedding_currentBoundaryRemainders_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint_via_residualBoundary
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
        (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            boundaryData.toPlanarBoundaryAnnulusBoundaryData,
      ∃ C₀ : G.EdgeColoring Color,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      ∃ _interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
        HasUnblockedInteriorEndpoint emb) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb,
      ∃ i : Fin data.numLayers, ∃ f ∈ data.layerFaces i,
        ∀ e ∈ (emb.faceBoundary f.1).erase (data.witnessEdge f), e ∈ data.currentBoundary i := by
  rcases h with
    ⟨emb, boundaryData, dartCycles, hselectedBoundaryArc, hcurrent, C₀, a, b, faceBoundary, hv23,
      interiorData, hEndpoint⟩
  rcases
    theorem49CurrentBoundaryRemainders_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint_via_residualBoundary
      boundaryData dartCycles hselectedBoundaryArc hcurrent C₀ hv23 interiorData hEndpoint with
    ⟨i, f, hf, hremainders⟩
  exact
    ⟨emb,
      (residualBoundarySelectorData_of_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData
        boundaryData.toPlanarBoundaryAnnulusBoundaryData
        interiorData).toResidualBoundaryLayerFacePeelWitnessData,
      i, f, hf, hremainders⟩

/-- Repaired exact-v23/v23.5 closed-walk route: if the one-collar current-boundary shell already
carries annulus-root parent peel data on the same boundary split, then the remaining local
endpoint witness is enough to reach the projected Theorem 4.9 synthesis endpoint.  The exact
residual state is recorded explicitly so this theorem can serve as the current strongest sound
replacement for the obstructed one-collar implication. -/
theorem
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          source.toPlanarBoundaryAnnulusBoundaryData)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary))
    (parentData : PlanarBoundaryAnnulusRootParentPeelData emb)
    (_hparentBoundary :
      parentData.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C₀ := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint_via_residualBoundary
      parentData hEndpoint C₀ hC₀

/-- Successor-cycle form of the same repaired exact-v23/v23.5 route.  Once the actual
boundary-order shell carries one-collar current-boundary data, the exact residual state, and a
same-split annulus-root parent peel package, the local endpoint witness closes the route to the
projected Theorem 4.9 synthesis endpoint. -/
theorem
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (_hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary))
    (parentData : PlanarBoundaryAnnulusRootParentPeelData emb)
    (_hparentBoundary :
      parentData.boundaryData = boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C₀ := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint_via_residualBoundary
      parentData hEndpoint C₀ hC₀

/-- Exact-v23/v23.5 closed-walk synthesis closure under the honest local facewise at-most-one
criterion.  On this branch the one-collar residual shell already has enough geometry to build a
canonical witness choice directly, so the remaining burden is the facewise interior-edge bound
itself rather than generic witness-assignment packaging. -/
theorem
    theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_facewiseAtMostOneInteriorEdge
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          source.toPlanarBoundaryAnnulusBoundaryData)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary))
    (h_at_most_one_interior :
      ∀ f : AmbientFace emb.faces,
        ((emb.faceBoundary f.1).filter
            (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
          (1 : ℕ)) :
    Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases
    exists_planarBoundaryCanonicalWitnessChoice_of_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge
      source h_at_most_one_interior with
    ⟨choice⟩
  exact
    theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusWitnessAssignment
      (G := G) choice.toPlanarBoundaryAnnulusWitnessAssignment C₀ hC₀

/-- Successor-cycle form of the same exact-v23/v23.5 closure.  If the live boundary-order shell
already satisfies the honest facewise at-most-one condition, then the exact one-collar residual
package closes directly to full theorem-4.9 synthesis on that embedding. -/
theorem
    theorem49BoundaryRootSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_facewiseAtMostOneInteriorEdge
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary))
    (h_at_most_one_interior :
      ∀ f : AmbientFace emb.faces,
        ((emb.faceBoundary f.1).filter
            (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
          (1 : ℕ)) :
    Theorem49BoundaryRootSynthesis emb C₀ := by
  let source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hselectedBoundaryArc
  have hcurrent' :
      ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            source.toPlanarBoundaryAnnulusBoundaryData := by
    simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
      PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
      PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
      _hcurrent
  exact
    theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_facewiseAtMostOneInteriorEdge
      source hcurrent' C₀ hC₀ _hv23 h_at_most_one_interior

/-- Existential closed-walk exact-v23 one-collar shells carrying the honest facewise at-most-one
bound already export the full theorem-4.9 synthesis endpoint at graph level for any supplied
Tait coloring. -/
theorem
    exists_theorem49BoundaryRootSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_facewiseAtMostOneInteriorEdge_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            source.toPlanarBoundaryAnnulusBoundaryData,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      (∀ f : AmbientFace emb.faces,
        ((emb.faceBoundary f.1).filter
            (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
          (1 : ℕ))) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases h with
    ⟨emb, source, hcurrent, a, b, faceBoundary, hv23, hAtMostOneInterior⟩
  exact
    ⟨emb,
      theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_facewiseAtMostOneInteriorEdge
        source hcurrent C₀ hC₀ hv23 hAtMostOneInterior⟩

/-- Successor-cycle form of the same exact-v23 one-collar graph-level facewise at-most-one
synthesis closure. -/
theorem
    exists_theorem49BoundaryRootSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_facewiseAtMostOneInteriorEdge_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
        (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            boundaryData.toPlanarBoundaryAnnulusBoundaryData,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      (∀ f : AmbientFace emb.faces,
        ((emb.faceBoundary f.1).filter
            (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
          (1 : ℕ))) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases h with
    ⟨emb, boundaryData, dartCycles, hselectedBoundaryArc, hcurrent, a, b, faceBoundary, hv23,
      hAtMostOneInterior⟩
  exact
    ⟨emb,
      theorem49BoundaryRootSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_facewiseAtMostOneInteriorEdge
        boundaryData dartCycles hselectedBoundaryArc hcurrent C₀ hC₀ hv23
        hAtMostOneInterior⟩

/-- On the exact v23/v23.5 honest-source facewise-at-most-one branch, the local endpoint witness
is impossible regardless of the residual seed or Tait coloring.  So the branch that already
closes to full theorem-4.9 synthesis remains vacuous on the current live endpoint shell. -/
theorem
    not_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_facewiseAtMostOneInteriorEdge
    {G : SimpleGraph V} (emb : PlaneEmbeddingWithBoundary G) :
    ¬ ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            source.toPlanarBoundaryAnnulusBoundaryData) ∧
      ∃ C₀ : G.EdgeColoring Color,
        IsTaitEdgeColoring G C₀ ∧
          ∃ a b : Color,
            ∃ faceBoundary : Finset G.edgeSet,
              Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary) ∧
                (∀ f : AmbientFace emb.faces,
                  ((emb.faceBoundary f.1).filter
                      (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                    (1 : ℕ)) ∧
                  HasUnblockedInteriorEndpoint emb := by
  rintro ⟨source, hcurrent, C₀, _hC₀, a, b, faceBoundary, _hv23, hAtMostOneInterior, hEndpoint⟩
  exact
    not_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_facewiseAtMostOneInteriorEdge_and_hasUnblockedInteriorEndpoint
      emb
      ⟨source, hcurrent, hAtMostOneInterior, hEndpoint⟩

/-- The same exact-v23/v23.5 endpoint obstruction holds on the route-facing successor-cycle shell
itself.  The residual seed does not rescue the live endpoint semantics once facewise at-most-one
is imposed. -/
theorem
    not_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_facewiseAtMostOneInteriorEdge
    {G : SimpleGraph V} (emb : PlaneEmbeddingWithBoundary G) :
    ¬ ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C₀ : G.EdgeColoring Color,
          IsTaitEdgeColoring G C₀ ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary) ∧
                  (∀ f : AmbientFace emb.faces,
                    ((emb.faceBoundary f.1).filter
                        (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                      (1 : ℕ)) ∧
                    HasUnblockedInteriorEndpoint emb := by
  rintro ⟨boundaryData, dartCycles, hselectedBoundaryArc, hcurrent, C₀, _hC₀, a, b, faceBoundary,
    _hv23, hAtMostOneInterior, hEndpoint⟩
  exact
    not_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_facewiseAtMostOneInteriorEdge_and_hasUnblockedInteriorEndpoint
      emb
      ⟨boundaryData, dartCycles, hselectedBoundaryArc, hcurrent, hAtMostOneInterior, hEndpoint⟩

/-- Even on the repaired exact-v23/v23.5 honest-source shell, facewise at-most-one still rules
out the projected nonempty theorem-4.9 endpoint: the same branch closes to full synthesis but
cannot carry the present nonempty carrier semantics. -/
theorem
    not_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_theorem49BoundaryRootNonemptyProjectedSynthesis_and_v23ResidualBoundaryInitialState_and_facewiseAtMostOneInteriorEdge
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) :
    ¬ ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            source.toPlanarBoundaryAnnulusBoundaryData) ∧
      ∃ C₀ : G.EdgeColoring Color,
        IsTaitEdgeColoring G C₀ ∧
          ∃ a b : Color,
            ∃ faceBoundary : Finset G.edgeSet,
              Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary) ∧
                (∀ f : AmbientFace emb.faces,
                  ((emb.faceBoundary f.1).filter
                      (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                    (1 : ℕ)) ∧
                  Theorem49BoundaryRootNonemptyProjectedSynthesis emb C₀ := by
  rintro ⟨source, hcurrent, C₀, _hC₀, a, b, faceBoundary, _hv23, hAtMostOneInterior,
    hProjected⟩
  exact
    not_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_facewiseAtMostOneInteriorEdge_and_theorem49BoundaryRootNonemptyProjectedSynthesis
      emb
      ⟨source, hcurrent, hAtMostOneInterior, C₀, hProjected⟩

/-- The exact-v23/v23.5 successor-cycle facewise-at-most-one shell likewise cannot reach the
projected nonempty theorem-4.9 endpoint on the same embedding. -/
theorem
    not_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_theorem49BoundaryRootNonemptyProjectedSynthesis_and_v23ResidualBoundaryInitialState_and_facewiseAtMostOneInteriorEdge
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) :
    ¬ ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
        ∃ C₀ : G.EdgeColoring Color,
          IsTaitEdgeColoring G C₀ ∧
            ∃ a b : Color,
              ∃ faceBoundary : Finset G.edgeSet,
                Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary) ∧
                  (∀ f : AmbientFace emb.faces,
                    ((emb.faceBoundary f.1).filter
                        (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                      (1 : ℕ)) ∧
                    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C₀ := by
  rintro ⟨boundaryData, dartCycles, hselectedBoundaryArc, hcurrent, C₀, _hC₀, a, b, faceBoundary,
    _hv23, hAtMostOneInterior, hProjected⟩
  exact
    not_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_facewiseAtMostOneInteriorEdge_and_theorem49BoundaryRootNonemptyProjectedSynthesis
      emb
      ⟨boundaryData, dartCycles, hselectedBoundaryArc, hcurrent, hAtMostOneInterior, C₀,
        hProjected⟩

/-- Exact Step 2 residual seed on one peeled face of the explicit-Tait diamond benchmark.  This
shows the repaired exact-v23 shell is genuinely inhabited on the same fixed embedding where the
honest facewise-at-most-one route already closes to full theorem-4.9 synthesis. -/
theorem nonempty_diamondWithTriangleFace0_v23ResidualBoundaryInitialState :
    Nonempty
      (V23ResidualBoundaryInitialState diamondWithTriangleTaitEdgeColoring red blue
        (diamondWithTriangleEmbedding.faceBoundary diamondWithTriangleFace0.1)) := by
  exact
    ⟨residualBoundaryInitialState_of_sum_v23_single_component_purifications_eq_boundaryOnlyGenerator
      diamondWithTriangleTaitEdgeColoring red blue
      (diamondWithTriangleEmbedding.faceBoundary diamondWithTriangleFace0.1)⟩

/-- The explicit-Tait diamond benchmark concretely inhabits the repaired exact-v23 honest-source
facewise-at-most-one branch.  On that same fixed embedding the branch reaches full
`Theorem49BoundaryRootSynthesis`, but still cannot carry either the current endpoint witness or
the projected nonempty theorem-4.9 endpoint. -/
theorem
    diamondWithTriangle_closedWalkSource_tait_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_facewiseAtMostOneInteriorEdge_and_theorem49BoundaryRootSynthesis_without_hasUnblockedInteriorEndpoint_or_projectedEndpoint
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData diamondWithTriangleEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            diamondWithTriangleClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData) ∧
      IsTaitEdgeColoring diamondWithTriangleGraph diamondWithTriangleTaitEdgeColoring ∧
      Nonempty
        (V23ResidualBoundaryInitialState diamondWithTriangleTaitEdgeColoring red blue
          (diamondWithTriangleEmbedding.faceBoundary diamondWithTriangleFace0.1)) ∧
      (∀ f : AmbientFace diamondWithTriangleEmbedding.faces,
        ((diamondWithTriangleEmbedding.faceBoundary f.1).filter
            (· ∈ interiorEdgeSupport diamondWithTriangleEmbedding.faceBoundary
              diamondWithTriangleEmbedding.faces)).card ≤
          (1 : ℕ)) ∧
      Theorem49BoundaryRootSynthesis diamondWithTriangleEmbedding
        diamondWithTriangleTaitEdgeColoring ∧
      ¬ HasUnblockedInteriorEndpoint diamondWithTriangleEmbedding ∧
      ¬ Theorem49BoundaryRootNonemptyProjectedSynthesis diamondWithTriangleEmbedding
          diamondWithTriangleTaitEdgeColoring := by
  have hcurrent :
      ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData diamondWithTriangleEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            diamondWithTriangleClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData := by
    exact
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge
        diamondWithTriangleClosedWalkAnnulusBoundarySource
        diamondWithTriangle_atMostOneInteriorEdgePerFace
  have hNoEndpoint :
      ¬ HasUnblockedInteriorEndpoint diamondWithTriangleEmbedding := by
    exact
      not_hasUnblockedInteriorEndpoint_of_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge
        diamondWithTriangleClosedWalkAnnulusBoundarySource
        diamondWithTriangle_atMostOneInteriorEdgePerFace
  have hNoProjected :
      ¬ Theorem49BoundaryRootNonemptyProjectedSynthesis diamondWithTriangleEmbedding
          diamondWithTriangleTaitEdgeColoring := by
    exact
      not_theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge
        diamondWithTriangleClosedWalkAnnulusBoundarySource
        diamondWithTriangle_atMostOneInteriorEdgePerFace
        diamondWithTriangleTaitEdgeColoring
  exact
    ⟨⟨diamondWithTriangleClosedWalkAnnulusBoundarySource⟩,
      hcurrent,
      diamondWithTriangleTaitEdgeColoring_isTait,
      nonempty_diamondWithTriangleFace0_v23ResidualBoundaryInitialState,
      diamondWithTriangle_atMostOneInteriorEdgePerFace,
      diamondWithTriangleEmbedding_theorem49BoundaryRootSynthesis_for_explicitTaitColoring_via_atMostOneInteriorEdgePerFace,
      hNoEndpoint,
      hNoProjected⟩

/-- The same exact-v23 calibration also lives on the explicit boundary-order successor-cycle shell
of the diamond benchmark.  So the split between algebraic sufficiency and endpoint vacuity is not
peculiar to the honest closed-walk presentation. -/
theorem
    diamondWithTriangle_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_facewiseAtMostOneInteriorEdge_and_theorem49BoundaryRootSynthesis_without_hasUnblockedInteriorEndpoint_or_projectedEndpoint
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryDartSuccessorCycleEmbeddingData diamondWithTriangleEmbedding) ∧
      (∀ f : AmbientFace diamondWithTriangleEmbedding.faces,
        (diamondWithTriangleDartSuccessorCycleGeometry.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
      (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData diamondWithTriangleEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            diamondWithTriangleAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData) ∧
      IsTaitEdgeColoring diamondWithTriangleGraph diamondWithTriangleTaitEdgeColoring ∧
      Nonempty
        (V23ResidualBoundaryInitialState diamondWithTriangleTaitEdgeColoring red blue
          (diamondWithTriangleEmbedding.faceBoundary diamondWithTriangleFace0.1)) ∧
      (∀ f : AmbientFace diamondWithTriangleEmbedding.faces,
        ((diamondWithTriangleEmbedding.faceBoundary f.1).filter
            (· ∈ interiorEdgeSupport diamondWithTriangleEmbedding.faceBoundary
              diamondWithTriangleEmbedding.faces)).card ≤
          (1 : ℕ)) ∧
      Theorem49BoundaryRootSynthesis diamondWithTriangleEmbedding
        diamondWithTriangleTaitEdgeColoring ∧
      ¬ HasUnblockedInteriorEndpoint diamondWithTriangleEmbedding ∧
      ¬ Theorem49BoundaryRootNonemptyProjectedSynthesis diamondWithTriangleEmbedding
          diamondWithTriangleTaitEdgeColoring := by
  have hcurrent :
      ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData diamondWithTriangleEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            diamondWithTriangleAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData := by
    exact
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge
        diamondWithTriangleClosedWalkAnnulusBoundarySource
        diamondWithTriangle_atMostOneInteriorEdgePerFace
  have hNoEndpoint :
      ¬ HasUnblockedInteriorEndpoint diamondWithTriangleEmbedding := by
    exact
      not_hasUnblockedInteriorEndpoint_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_facewiseAtMostOneInteriorEdge
        diamondWithTriangleAnnulusBoundaryReachabilityData
        diamondWithTriangleDartSuccessorCycleGeometry
        diamondWithTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
        diamondWithTriangle_atMostOneInteriorEdgePerFace
  have hNoProjected :
      ¬ Theorem49BoundaryRootNonemptyProjectedSynthesis diamondWithTriangleEmbedding
          diamondWithTriangleTaitEdgeColoring := by
    exact
      not_theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_facewiseAtMostOneInteriorEdge
        diamondWithTriangleAnnulusBoundaryReachabilityData
        diamondWithTriangleDartSuccessorCycleGeometry
        diamondWithTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
        diamondWithTriangle_atMostOneInteriorEdgePerFace
        diamondWithTriangleTaitEdgeColoring
  exact
    ⟨⟨diamondWithTriangleAnnulusBoundaryReachabilityData⟩,
      ⟨diamondWithTriangleDartSuccessorCycleGeometry⟩,
      diamondWithTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      hcurrent,
      diamondWithTriangleTaitEdgeColoring_isTait,
      nonempty_diamondWithTriangleFace0_v23ResidualBoundaryInitialState,
      diamondWithTriangle_atMostOneInteriorEdgePerFace,
      diamondWithTriangleEmbedding_theorem49BoundaryRootSynthesis_for_explicitTaitColoring_via_atMostOneInteriorEdgePerFace,
      hNoEndpoint,
      hNoProjected⟩

/-- The repaired exact-v23 honest-source facewise-at-most-one diamond shell is not blocked at
witness ownership either.  On the same fixed embedding, the canonical one-collar annulus witness
assignment is already nonempty before the branch runs into the live endpoint impossibility. -/
theorem
    diamondWithTriangle_closedWalkSource_tait_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_facewiseAtMostOneInteriorEdge_and_annulusWitnessAssignment_and_theorem49BoundaryRootSynthesis_without_hasUnblockedInteriorEndpoint_or_projectedEndpoint
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData diamondWithTriangleEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            diamondWithTriangleClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData) ∧
      IsTaitEdgeColoring diamondWithTriangleGraph diamondWithTriangleTaitEdgeColoring ∧
      Nonempty
        (V23ResidualBoundaryInitialState diamondWithTriangleTaitEdgeColoring red blue
          (diamondWithTriangleEmbedding.faceBoundary diamondWithTriangleFace0.1)) ∧
      (∀ f : AmbientFace diamondWithTriangleEmbedding.faces,
        ((diamondWithTriangleEmbedding.faceBoundary f.1).filter
            (· ∈ interiorEdgeSupport diamondWithTriangleEmbedding.faceBoundary
              diamondWithTriangleEmbedding.faces)).card ≤
          (1 : ℕ)) ∧
      Nonempty
        (PlanarBoundaryAnnulusWitnessAssignment
          (planarBoundaryAnnulusDecomposition_of_boundaryData
            diamondWithTriangleClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData)) ∧
      Theorem49BoundaryRootSynthesis diamondWithTriangleEmbedding
        diamondWithTriangleTaitEdgeColoring ∧
      ¬ HasUnblockedInteriorEndpoint diamondWithTriangleEmbedding ∧
      ¬ Theorem49BoundaryRootNonemptyProjectedSynthesis diamondWithTriangleEmbedding
          diamondWithTriangleTaitEdgeColoring := by
  rcases
    diamondWithTriangle_closedWalkSource_tait_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_facewiseAtMostOneInteriorEdge_and_theorem49BoundaryRootSynthesis_without_hasUnblockedInteriorEndpoint_or_projectedEndpoint
      with
    ⟨hSource, hcurrent, hTait, hv23, hAtMostOne, hSynth, hNoEndpoint, hNoProjected⟩
  have hwitness :
      Nonempty
        (PlanarBoundaryAnnulusWitnessAssignment
          (planarBoundaryAnnulusDecomposition_of_boundaryData
            diamondWithTriangleClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData)) := by
    rcases
      diamondWithTriangleClosedWalkAnnulusBoundarySource_hasCanonicalWitnessChoice_via_atMostOneInteriorEdgePerFace with
      ⟨choice⟩
    exact ⟨choice.toPlanarBoundaryAnnulusWitnessAssignment⟩
  exact
    ⟨hSource, hcurrent, hTait, hv23, hAtMostOne, hwitness, hSynth, hNoEndpoint, hNoProjected⟩

/-- The same exact-v23 witness-ownership upgrade also lives on the explicit successor-cycle shell
of the diamond benchmark.  So on this repaired at-most-one branch, the route is not blocked at
same-embedding annulus witness assignment either. -/
theorem
    diamondWithTriangle_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_facewiseAtMostOneInteriorEdge_and_annulusWitnessAssignment_and_theorem49BoundaryRootSynthesis_without_hasUnblockedInteriorEndpoint_or_projectedEndpoint
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryDartSuccessorCycleEmbeddingData diamondWithTriangleEmbedding) ∧
      (∀ f : AmbientFace diamondWithTriangleEmbedding.faces,
        (diamondWithTriangleDartSuccessorCycleGeometry.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
      (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData diamondWithTriangleEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            diamondWithTriangleAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData) ∧
      IsTaitEdgeColoring diamondWithTriangleGraph diamondWithTriangleTaitEdgeColoring ∧
      Nonempty
        (V23ResidualBoundaryInitialState diamondWithTriangleTaitEdgeColoring red blue
          (diamondWithTriangleEmbedding.faceBoundary diamondWithTriangleFace0.1)) ∧
      (∀ f : AmbientFace diamondWithTriangleEmbedding.faces,
        ((diamondWithTriangleEmbedding.faceBoundary f.1).filter
            (· ∈ interiorEdgeSupport diamondWithTriangleEmbedding.faceBoundary
              diamondWithTriangleEmbedding.faces)).card ≤
          (1 : ℕ)) ∧
      Nonempty
        (PlanarBoundaryAnnulusWitnessAssignment
          (planarBoundaryAnnulusDecomposition_of_boundaryData
            diamondWithTriangleAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData)) ∧
      Theorem49BoundaryRootSynthesis diamondWithTriangleEmbedding
        diamondWithTriangleTaitEdgeColoring ∧
      ¬ HasUnblockedInteriorEndpoint diamondWithTriangleEmbedding ∧
      ¬ Theorem49BoundaryRootNonemptyProjectedSynthesis diamondWithTriangleEmbedding
          diamondWithTriangleTaitEdgeColoring := by
  rcases
    diamondWithTriangle_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_facewiseAtMostOneInteriorEdge_and_theorem49BoundaryRootSynthesis_without_hasUnblockedInteriorEndpoint_or_projectedEndpoint
      with
    ⟨hBoundaryData, hDarts, hArc, hcurrent, hTait, hv23, hAtMostOne, hSynth, hNoEndpoint,
      hNoProjected⟩
  have hwitness :
      Nonempty
        (PlanarBoundaryAnnulusWitnessAssignment
          (planarBoundaryAnnulusDecomposition_of_boundaryData
            diamondWithTriangleAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData)) := by
    rcases
      diamondWithTriangleClosedWalkAnnulusBoundarySource_hasCanonicalWitnessChoice_via_atMostOneInteriorEdgePerFace with
      ⟨choice⟩
    exact ⟨choice.toPlanarBoundaryAnnulusWitnessAssignment⟩
  exact
    ⟨hBoundaryData, hDarts, hArc, hcurrent, hTait, hv23, hAtMostOne, hwitness, hSynth,
      hNoEndpoint, hNoProjected⟩

/-- The explicit-Tait diamond benchmark shows that the repaired exact-v23 honest-source
facewise-at-most-one branch remains strictly weaker than the heavier annulus-root peel packages.
On the same fixed embedding it reaches full `Theorem49BoundaryRootSynthesis`, but still fails the
interior-dual adj-distance, annulus-root adj-distance, and annulus-root parent-peel targets. -/
theorem diamondWithTriangle_closedWalkSource_exactV23_facewiseAtMostOne_consolidatedRouteDiagnosis
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData diamondWithTriangleEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            diamondWithTriangleClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData) ∧
      IsTaitEdgeColoring diamondWithTriangleGraph diamondWithTriangleTaitEdgeColoring ∧
      Nonempty
        (V23ResidualBoundaryInitialState diamondWithTriangleTaitEdgeColoring red blue
          (diamondWithTriangleEmbedding.faceBoundary diamondWithTriangleFace0.1)) ∧
      (∀ f : AmbientFace diamondWithTriangleEmbedding.faces,
        ((diamondWithTriangleEmbedding.faceBoundary f.1).filter
            (· ∈ interiorEdgeSupport diamondWithTriangleEmbedding.faceBoundary
              diamondWithTriangleEmbedding.faces)).card ≤
          (1 : ℕ)) ∧
      Theorem49BoundaryRootSynthesis diamondWithTriangleEmbedding
        diamondWithTriangleTaitEdgeColoring ∧
      ¬ HasUnblockedInteriorEndpoint diamondWithTriangleEmbedding ∧
      ¬ Theorem49BoundaryRootNonemptyProjectedSynthesis diamondWithTriangleEmbedding
          diamondWithTriangleTaitEdgeColoring ∧
      ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData
        diamondWithTriangleEmbedding.faces diamondWithTriangleEmbedding.faceBoundary) ∧
      ¬ Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData diamondWithTriangleEmbedding) ∧
      ¬ Nonempty (PlanarBoundaryAnnulusRootParentPeelData diamondWithTriangleEmbedding) := by
  rcases
    diamondWithTriangle_closedWalkSource_tait_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_facewiseAtMostOneInteriorEdge_and_theorem49BoundaryRootSynthesis_without_hasUnblockedInteriorEndpoint_or_projectedEndpoint
      with
  ⟨hSource, hcurrent, hTait, hv23, hAtMostOne, hSynth, hNoEndpoint, hNoProjected⟩
  have hNoInteriorDual :
      ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData
        diamondWithTriangleEmbedding.faces diamondWithTriangleEmbedding.faceBoundary) := by
    simpa using
      (diamondWithTriangle_explicitTait_synthesis_without_interiorDualBoundaryRootAdjDistancePeelData).2.2
  have hNoAdjDistance :
      ¬ Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData diamondWithTriangleEmbedding) := by
    simpa using
      (diamondWithTriangle_explicitTait_synthesis_without_planarBoundaryAnnulusRootAdjDistancePeelData).2.2
  have hNoParentPeel :
      ¬ Nonempty (PlanarBoundaryAnnulusRootParentPeelData diamondWithTriangleEmbedding) := by
    simpa using
      (diamondWithTriangle_explicitTait_synthesis_without_planarBoundaryAnnulusRootParentPeelData).2.2
  exact
    ⟨hSource, hcurrent, hTait, hv23, hAtMostOne, hSynth, hNoEndpoint, hNoProjected,
      hNoInteriorDual, hNoAdjDistance, hNoParentPeel⟩

/-- The same strengthened diagnosis also holds on the explicit successor-cycle presentation of the
diamond benchmark.  So these heavier annulus-root peel targets are not rescued by passing from
the honest closed-walk source to the boundary-order route shell. -/
theorem diamondWithTriangle_successorCycle_exactV23_facewiseAtMostOne_consolidatedRouteDiagnosis
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryDartSuccessorCycleEmbeddingData diamondWithTriangleEmbedding) ∧
      (∀ f : AmbientFace diamondWithTriangleEmbedding.faces,
        (diamondWithTriangleDartSuccessorCycleGeometry.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
      (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData diamondWithTriangleEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            diamondWithTriangleAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData) ∧
      IsTaitEdgeColoring diamondWithTriangleGraph diamondWithTriangleTaitEdgeColoring ∧
      Nonempty
        (V23ResidualBoundaryInitialState diamondWithTriangleTaitEdgeColoring red blue
          (diamondWithTriangleEmbedding.faceBoundary diamondWithTriangleFace0.1)) ∧
      (∀ f : AmbientFace diamondWithTriangleEmbedding.faces,
        ((diamondWithTriangleEmbedding.faceBoundary f.1).filter
            (· ∈ interiorEdgeSupport diamondWithTriangleEmbedding.faceBoundary
              diamondWithTriangleEmbedding.faces)).card ≤
          (1 : ℕ)) ∧
      Theorem49BoundaryRootSynthesis diamondWithTriangleEmbedding
        diamondWithTriangleTaitEdgeColoring ∧
      ¬ HasUnblockedInteriorEndpoint diamondWithTriangleEmbedding ∧
      ¬ Theorem49BoundaryRootNonemptyProjectedSynthesis diamondWithTriangleEmbedding
          diamondWithTriangleTaitEdgeColoring ∧
      ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData
        diamondWithTriangleEmbedding.faces diamondWithTriangleEmbedding.faceBoundary) ∧
      ¬ Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData diamondWithTriangleEmbedding) ∧
      ¬ Nonempty (PlanarBoundaryAnnulusRootParentPeelData diamondWithTriangleEmbedding) := by
  rcases
    diamondWithTriangle_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_facewiseAtMostOneInteriorEdge_and_theorem49BoundaryRootSynthesis_without_hasUnblockedInteriorEndpoint_or_projectedEndpoint
      with
  ⟨hBoundaryData, hDarts, hArc, hcurrent, hTait, hv23, hAtMostOne, hSynth, hNoEndpoint,
    hNoProjected⟩
  have hNoInteriorDual :
      ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData
        diamondWithTriangleEmbedding.faces diamondWithTriangleEmbedding.faceBoundary) := by
    simpa using
      (diamondWithTriangle_explicitTait_synthesis_without_interiorDualBoundaryRootAdjDistancePeelData).2.2
  have hNoAdjDistance :
      ¬ Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData diamondWithTriangleEmbedding) := by
    simpa using
      (diamondWithTriangle_explicitTait_synthesis_without_planarBoundaryAnnulusRootAdjDistancePeelData).2.2
  have hNoParentPeel :
      ¬ Nonempty (PlanarBoundaryAnnulusRootParentPeelData diamondWithTriangleEmbedding) := by
    simpa using
      (diamondWithTriangle_explicitTait_synthesis_without_planarBoundaryAnnulusRootParentPeelData).2.2
  exact
    ⟨hBoundaryData, hDarts, hArc, hcurrent, hTait, hv23, hAtMostOne, hSynth, hNoEndpoint,
      hNoProjected, hNoInteriorDual, hNoAdjDistance, hNoParentPeel⟩

/-- Closed-walk exact-shell parent-peel route: the same repaired exact-v23/v23.5 shell also
reaches the raw quotient/error endpoint for every Kirchhoff chain on the resulting purified
carrier. -/
theorem
    theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          source.toPlanarBoundaryAnnulusBoundaryData)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary))
    (parentData : PlanarBoundaryAnnulusRootParentPeelData emb)
    (_hparentBoundary :
      parentData.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C₀ x := by
  exact
    theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusRootParentPositiveProjectedGeometryOn
      (theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint
        source _hcurrent C₀ _hv23 parentData _hparentBoundary hEndpoint)
      C₀ hC₀ hx

/-- Successor-cycle form of the same exact-shell parent-peel raw quotient/error closure. -/
theorem
    theorem49BoundaryRawQuotientErrorPackage_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (_hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary))
    (parentData : PlanarBoundaryAnnulusRootParentPeelData emb)
    (_hparentBoundary :
      parentData.boundaryData = boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C₀ x := by
  exact
    theorem49BoundaryRawQuotientErrorPackage_of_successorCycleAnnulusRootParentPositiveProjectedGeometryOn
      (theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint
        boundaryData dartCycles _hselectedBoundaryArc _hcurrent C₀ _hv23 parentData
        _hparentBoundary hEndpoint)
      C₀ hC₀ hx

/-- Closed-walk exact-shell adj-distance route: once the repaired one-collar v23/v23.5 shell
already carries generic boundary-root adjacency-distance data and an unblocked endpoint, the
projected theorem-4.9 endpoint is immediate. -/
theorem
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          source.toPlanarBoundaryAnnulusBoundaryData)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary))
    (peelFaces : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces source.boundaryFaceRoots
          hcoverRoots hsepRoots)
        source.fallbackEdge))
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
        (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
            source.boundaryFaceRoots hcoverRoots hsepRoots)
          source.fallbackEdge f),
      e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
        ∃ g ∈ peelFaces,
          (interiorDualSpanningForest emb.faceBoundary emb.faces).Adj f g ∧
          e ∈ emb.faceBoundary g.1 ∧
          (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
              f
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                source.boundaryFaceRoots hcoverRoots hsepRoots f) <
            (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
              g
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                source.boundaryFaceRoots hcoverRoots hsepRoots g))
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C₀ := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn
      (theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint
        source _hcurrent C₀ _hv23 peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover
        hchildren hEndpoint)
      C₀ hC₀

/-- Successor-cycle form of the same exact-shell rooted-cover projected endpoint closure. -/
theorem
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary))
    (peelFaces : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
          hcoverRoots hsepRoots)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hselectedBoundaryArc).fallbackEdge))
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
        (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
            hcoverRoots hsepRoots)
          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hselectedBoundaryArc).fallbackEdge f),
      e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
        ∃ g ∈ peelFaces,
          (interiorDualSpanningForest emb.faceBoundary emb.faces).Adj f g ∧
          e ∈ emb.faceBoundary g.1 ∧
          (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
              f
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                  boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
                hcoverRoots hsepRoots f) <
            (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
              g
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                  boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
                hcoverRoots hsepRoots g))
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C₀ := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_successorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn
      (theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint
        boundaryData dartCycles hselectedBoundaryArc _hcurrent C₀ _hv23 peelFaces hunique
        hcoverRoots hsepRoots hpeelInterior hcover hchildren hEndpoint)
      C₀ hC₀

/-- Closed-walk exact-shell adj-distance route: once the repaired one-collar v23/v23.5 shell
already carries generic boundary-root adjacency-distance data and an unblocked endpoint, the
projected theorem-4.9 endpoint is immediate. -/
theorem
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          source.toPlanarBoundaryAnnulusBoundaryData)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary))
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C₀ := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn
      (theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint
        source _hcurrent C₀ _hv23 interiorData hEndpoint)
      C₀ hC₀

/-- Successor-cycle form of the same exact-shell adj-distance projected endpoint closure. -/
theorem
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (_hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary))
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C₀ := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_successorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn
      (theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint
        boundaryData dartCycles _hselectedBoundaryArc _hcurrent C₀ _hv23 interiorData
        hEndpoint)
      C₀ hC₀

/-- Closed-walk exact-shell adj-distance route: the same repaired one-collar shell also reaches
the raw quotient/error endpoint for every Kirchhoff chain on the resulting purified carrier. -/
theorem
    theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          source.toPlanarBoundaryAnnulusBoundaryData)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary))
    (peelFaces : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces source.boundaryFaceRoots
          hcoverRoots hsepRoots)
        source.fallbackEdge))
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
        (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
            source.boundaryFaceRoots hcoverRoots hsepRoots)
          source.fallbackEdge f),
      e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
        ∃ g ∈ peelFaces,
          (interiorDualSpanningForest emb.faceBoundary emb.faces).Adj f g ∧
          e ∈ emb.faceBoundary g.1 ∧
          (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
              f
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                source.boundaryFaceRoots hcoverRoots hsepRoots f) <
            (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
              g
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                source.boundaryFaceRoots hcoverRoots hsepRoots g))
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C₀ x := by
  exact
    theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn
      (theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint
        source _hcurrent C₀ _hv23 peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover
        hchildren hEndpoint)
      C₀ hC₀ hx

/-- Successor-cycle form of the same exact-shell rooted-cover raw quotient/error closure. -/
theorem
    theorem49BoundaryRawQuotientErrorPackage_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary))
    (peelFaces : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
          hcoverRoots hsepRoots)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hselectedBoundaryArc).fallbackEdge))
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
        (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
            hcoverRoots hsepRoots)
          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hselectedBoundaryArc).fallbackEdge f),
      e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
        ∃ g ∈ peelFaces,
          (interiorDualSpanningForest emb.faceBoundary emb.faces).Adj f g ∧
          e ∈ emb.faceBoundary g.1 ∧
          (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
              f
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                  boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
                hcoverRoots hsepRoots f) <
            (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
              g
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                  boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
                hcoverRoots hsepRoots g))
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C₀ x := by
  exact
    theorem49BoundaryRawQuotientErrorPackage_of_successorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn
      (theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint
        boundaryData dartCycles hselectedBoundaryArc _hcurrent C₀ _hv23 peelFaces hunique
        hcoverRoots hsepRoots hpeelInterior hcover hchildren hEndpoint)
      C₀ hC₀ hx

/-- Closed-walk exact-shell adj-distance route: the same repaired one-collar shell also reaches
the raw quotient/error endpoint for every Kirchhoff chain on the resulting purified carrier. -/
theorem
    theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          source.toPlanarBoundaryAnnulusBoundaryData)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary))
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C₀ x := by
  exact
    theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn
      (theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint
        source _hcurrent C₀ _hv23 interiorData hEndpoint)
      C₀ hC₀ hx

/-- Successor-cycle form of the same exact-shell adj-distance raw quotient/error closure. -/
theorem
    theorem49BoundaryRawQuotientErrorPackage_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (_hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (_hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (_hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary))
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C₀ x := by
  exact
    theorem49BoundaryRawQuotientErrorPackage_of_successorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn
      (theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint
        boundaryData dartCycles _hselectedBoundaryArc _hcurrent C₀ _hv23 interiorData
        hEndpoint)
      C₀ hC₀ hx

/-- Existential closed-walk exact-shell rooted-cover data reaches the graph-level projected
theorem-4.9 endpoint for any supplied Tait coloring. -/
theorem
    exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            source.toPlanarBoundaryAnnulusBoundaryData,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      ∃ peelFaces : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        source.boundaryFaceRoots,
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        source.boundaryFaceRoots,
      ∃ _hpeelInterior : ∀ f ∈ peelFaces,
          Disjoint (emb.faceBoundary f.1)
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces),
      ∃ _hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces source.boundaryFaceRoots
              hcoverRoots hsepRoots)
            source.fallbackEdge),
      ∃ _hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              source.boundaryFaceRoots hcoverRoots hsepRoots)
            source.fallbackEdge f),
        e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
          ∃ g ∈ peelFaces,
            (interiorDualSpanningForest emb.faceBoundary emb.faces).Adj f g ∧
            e ∈ emb.faceBoundary g.1 ∧
            (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                f
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                  source.boundaryFaceRoots hcoverRoots hsepRoots f) <
              (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                g
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                  source.boundaryFaceRoots hcoverRoots hsepRoots g),
      HasUnblockedInteriorEndpoint emb)
     :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C₀ := by
  rcases h with
    ⟨emb, source, hcurrent, a, b, faceBoundary, hv23, peelFaces, hunique, hcoverRoots,
      hsepRoots, hpeelInterior, hcover, hchildren, hEndpoint⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint
        source hcurrent C₀ hC₀ hv23 peelFaces hunique hcoverRoots hsepRoots hpeelInterior
        hcover hchildren hEndpoint⟩

/-- Successor-cycle exact-shell rooted-cover data reaches the graph-level projected theorem-4.9
endpoint for any supplied Tait coloring. -/
theorem
    exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
        (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            boundaryData.toPlanarBoundaryAnnulusBoundaryData,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      ∃ peelFaces : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots,
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots,
      ∃ _hpeelInterior : ∀ f ∈ peelFaces,
          Disjoint (emb.faceBoundary f.1)
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces),
      ∃ _hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
              hcoverRoots hsepRoots)
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hselectedBoundaryArc).fallbackEdge),
      ∃ _hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
              hcoverRoots hsepRoots)
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hselectedBoundaryArc).fallbackEdge f),
        e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
          ∃ g ∈ peelFaces,
            (interiorDualSpanningForest emb.faceBoundary emb.faces).Adj f g ∧
            e ∈ emb.faceBoundary g.1 ∧
            (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                f
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                  (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                    boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
                  hcoverRoots hsepRoots f) <
              (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                g
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                  (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                    boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
                  hcoverRoots hsepRoots g),
      HasUnblockedInteriorEndpoint emb)
     :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C₀ := by
  rcases h with
    ⟨emb, boundaryData, dartCycles, hselectedBoundaryArc, hcurrent, a, b, faceBoundary, hv23,
      peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover, hchildren,
      hEndpoint⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint
        boundaryData dartCycles hselectedBoundaryArc hcurrent C₀ hC₀ hv23 peelFaces hunique
        hcoverRoots hsepRoots hpeelInterior hcover hchildren hEndpoint⟩

/-- Existential closed-walk exact-shell rooted-cover data and a Kirchhoff chain on the same
embedding reach the graph-level raw theorem-4.9 quotient/error endpoint. -/
theorem
    exists_theorem49BoundaryRawQuotientErrorPackage_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {x : G.edgeSet → Color}
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            source.toPlanarBoundaryAnnulusBoundaryData,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      ∃ peelFaces : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        source.boundaryFaceRoots,
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        source.boundaryFaceRoots,
      ∃ _hpeelInterior : ∀ f ∈ peelFaces,
          Disjoint (emb.faceBoundary f.1)
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces),
      ∃ _hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces source.boundaryFaceRoots
              hcoverRoots hsepRoots)
            source.fallbackEdge),
      ∃ _hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              source.boundaryFaceRoots hcoverRoots hsepRoots)
            source.fallbackEdge f),
        e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
          ∃ g ∈ peelFaces,
            (interiorDualSpanningForest emb.faceBoundary emb.faces).Adj f g ∧
            e ∈ emb.faceBoundary g.1 ∧
            (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                f
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                  source.boundaryFaceRoots hcoverRoots hsepRoots f) <
              (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                g
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                  source.boundaryFaceRoots hcoverRoots hsepRoots g),
      HasUnblockedInteriorEndpoint emb ∧
        x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb))
     :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRawQuotientErrorPackage emb C₀ x := by
  rcases h with
    ⟨emb, source, hcurrent, a, b, faceBoundary, hv23, peelFaces, hunique, hcoverRoots,
      hsepRoots, hpeelInterior, hcover, hchildren, hEndpoint, hx⟩
  exact
    ⟨emb,
      theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint
        source hcurrent C₀ hC₀ hv23 peelFaces hunique hcoverRoots hsepRoots hpeelInterior
        hcover hchildren hEndpoint hx⟩

/-- Successor-cycle exact-shell rooted-cover data and a Kirchhoff chain on the same embedding
reach the graph-level raw theorem-4.9 quotient/error endpoint. -/
theorem
    exists_theorem49BoundaryRawQuotientErrorPackage_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {x : G.edgeSet → Color}
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
        (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            boundaryData.toPlanarBoundaryAnnulusBoundaryData,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      ∃ peelFaces : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots,
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots,
      ∃ _hpeelInterior : ∀ f ∈ peelFaces,
          Disjoint (emb.faceBoundary f.1)
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces),
      ∃ _hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
              hcoverRoots hsepRoots)
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hselectedBoundaryArc).fallbackEdge),
      ∃ _hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
              hcoverRoots hsepRoots)
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hselectedBoundaryArc).fallbackEdge f),
        e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
          ∃ g ∈ peelFaces,
            (interiorDualSpanningForest emb.faceBoundary emb.faces).Adj f g ∧
            e ∈ emb.faceBoundary g.1 ∧
            (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                f
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                  (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                    boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
                  hcoverRoots hsepRoots f) <
              (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                g
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                  (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                    boundaryData dartCycles hselectedBoundaryArc).boundaryFaceRoots
                  hcoverRoots hsepRoots g),
      HasUnblockedInteriorEndpoint emb ∧
        x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb))
     :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRawQuotientErrorPackage emb C₀ x := by
  rcases h with
    ⟨emb, boundaryData, dartCycles, hselectedBoundaryArc, hcurrent, a, b, faceBoundary, hv23,
      peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover, hchildren,
      hEndpoint, hx⟩
  exact
    ⟨emb,
      theorem49BoundaryRawQuotientErrorPackage_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint
        boundaryData dartCycles hselectedBoundaryArc hcurrent C₀ hC₀ hv23 peelFaces hunique
        hcoverRoots hsepRoots hpeelInterior hcover hchildren hEndpoint hx⟩

/-- Existential closed-walk exact-shell parent-peel data reaches the graph-level projected
theorem-4.9 endpoint for any supplied Tait coloring. -/
theorem
    exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            source.toPlanarBoundaryAnnulusBoundaryData,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      ∃ parentData : PlanarBoundaryAnnulusRootParentPeelData emb,
        parentData.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData ∧
          HasUnblockedInteriorEndpoint emb)
     :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C₀ := by
  rcases h with
    ⟨emb, source, hcurrent, a, b, faceBoundary, hv23, parentData, hparentBoundary, hEndpoint⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint
        source hcurrent C₀ hC₀ hv23 parentData hparentBoundary hEndpoint⟩

/-- Successor-cycle exact-shell parent-peel data reaches the graph-level projected theorem-4.9
endpoint for any supplied Tait coloring. -/
theorem
    exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
        (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            boundaryData.toPlanarBoundaryAnnulusBoundaryData,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      ∃ parentData : PlanarBoundaryAnnulusRootParentPeelData emb,
        parentData.boundaryData = boundaryData.toPlanarBoundaryAnnulusBoundaryData ∧
          HasUnblockedInteriorEndpoint emb)
     :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C₀ := by
  rcases h with
    ⟨emb, boundaryData, dartCycles, hselectedBoundaryArc, hcurrent, a, b, faceBoundary, hv23,
      parentData, hparentBoundary, hEndpoint⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint
        boundaryData dartCycles hselectedBoundaryArc hcurrent C₀ hC₀ hv23 parentData
        hparentBoundary hEndpoint⟩

/-- Existential closed-walk exact-shell parent-peel data and a Kirchhoff chain on the same
embedding reach the graph-level raw theorem-4.9 quotient/error endpoint. -/
theorem
    exists_theorem49BoundaryRawQuotientErrorPackage_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {x : G.edgeSet → Color}
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            source.toPlanarBoundaryAnnulusBoundaryData,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      ∃ parentData : PlanarBoundaryAnnulusRootParentPeelData emb,
        parentData.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData ∧
          HasUnblockedInteriorEndpoint emb ∧
          x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb))
     :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRawQuotientErrorPackage emb C₀ x := by
  rcases h with
    ⟨emb, source, hcurrent, a, b, faceBoundary, hv23, parentData, hparentBoundary, hEndpoint,
      hx⟩
  exact
    ⟨emb,
      theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint
        source hcurrent C₀ hC₀ hv23 parentData hparentBoundary hEndpoint hx⟩

/-- Successor-cycle exact-shell parent-peel data and a Kirchhoff chain on the same embedding
reach the graph-level raw theorem-4.9 quotient/error endpoint. -/
theorem
    exists_theorem49BoundaryRawQuotientErrorPackage_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {x : G.edgeSet → Color}
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
        (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            boundaryData.toPlanarBoundaryAnnulusBoundaryData,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      ∃ parentData : PlanarBoundaryAnnulusRootParentPeelData emb,
        parentData.boundaryData = boundaryData.toPlanarBoundaryAnnulusBoundaryData ∧
          HasUnblockedInteriorEndpoint emb ∧
          x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb))
     :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRawQuotientErrorPackage emb C₀ x := by
  rcases h with
    ⟨emb, boundaryData, dartCycles, hselectedBoundaryArc, hcurrent, a, b, faceBoundary, hv23,
      parentData, hparentBoundary, hEndpoint, hx⟩
  exact
    ⟨emb,
      theorem49BoundaryRawQuotientErrorPackage_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint
        boundaryData dartCycles hselectedBoundaryArc hcurrent C₀ hC₀ hv23 parentData
        hparentBoundary hEndpoint hx⟩

/-- Existential closed-walk exact-shell adj-distance data reaches the graph-level projected
theorem-4.9 endpoint for any supplied Tait coloring. -/
theorem
    exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            source.toPlanarBoundaryAnnulusBoundaryData,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      ∃ _interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
        HasUnblockedInteriorEndpoint emb)
     :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C₀ := by
  rcases h with ⟨emb, source, hcurrent, a, b, faceBoundary, hv23, interiorData, hEndpoint⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint
        source hcurrent C₀ hC₀ hv23 interiorData hEndpoint⟩

/-- Successor-cycle exact-shell adj-distance data reaches the graph-level projected theorem-4.9
endpoint for any supplied Tait coloring. -/
theorem
    exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
        (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            boundaryData.toPlanarBoundaryAnnulusBoundaryData,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      ∃ _interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
        HasUnblockedInteriorEndpoint emb)
     :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C₀ := by
  rcases h with
    ⟨emb, boundaryData, dartCycles, hselectedBoundaryArc, hcurrent, a, b, faceBoundary, hv23,
      interiorData, hEndpoint⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint
        boundaryData dartCycles hselectedBoundaryArc hcurrent C₀ hC₀ hv23 interiorData
        hEndpoint⟩

/-- Existential closed-walk exact-shell adj-distance data and a Kirchhoff chain on the same
embedding reach the graph-level raw theorem-4.9 quotient/error endpoint. -/
theorem
    exists_theorem49BoundaryRawQuotientErrorPackage_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {x : G.edgeSet → Color}
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            source.toPlanarBoundaryAnnulusBoundaryData,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      ∃ _interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
        HasUnblockedInteriorEndpoint emb ∧
          x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb))
     :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRawQuotientErrorPackage emb C₀ x := by
  rcases h with
    ⟨emb, source, hcurrent, a, b, faceBoundary, hv23, interiorData, hEndpoint, hx⟩
  exact
    ⟨emb,
      theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint
        source hcurrent C₀ hC₀ hv23 interiorData hEndpoint hx⟩

/-- Successor-cycle exact-shell adj-distance data and a Kirchhoff chain on the same embedding
reach the graph-level raw theorem-4.9 quotient/error endpoint. -/
theorem
    exists_theorem49BoundaryRawQuotientErrorPackage_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {x : G.edgeSet → Color}
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _hselectedBoundaryArc : ∀ f : AmbientFace emb.faces,
        (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ _hcurrent : ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            boundaryData.toPlanarBoundaryAnnulusBoundaryData,
      ∃ a b : Color,
      ∃ faceBoundary : Finset G.edgeSet,
      ∃ _hv23 : Nonempty (V23ResidualBoundaryInitialState C₀ a b faceBoundary),
      ∃ _interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
        HasUnblockedInteriorEndpoint emb ∧
          x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb))
     :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRawQuotientErrorPackage emb C₀ x := by
  rcases h with
    ⟨emb, boundaryData, dartCycles, hselectedBoundaryArc, hcurrent, a, b, faceBoundary, hv23,
      interiorData, hEndpoint, hx⟩
  exact
    ⟨emb,
      theorem49BoundaryRawQuotientErrorPackage_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint
        boundaryData dartCycles hselectedBoundaryArc hcurrent C₀ hC₀ hv23 interiorData
        hEndpoint hx⟩

theorem
    exists_theorem49BoundaryRootSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_residualBoundaryLayerFacePeelWitnessData_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
        Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb))
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases hG with ⟨emb, ⟨source⟩, ⟨data⟩⟩
  exact
    ⟨emb,
      theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_residualBoundaryLayerFacePeelWitnessData
        source data C₀ hC₀⟩

theorem
    exists_theorem49BoundaryRootSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_residualBoundaryLayerFacePeelWitnessData_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
        ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
            Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb))
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases hG with ⟨emb, ⟨boundaryData⟩, dartCycles, hselectedBoundaryArc, ⟨data⟩⟩
  exact
    ⟨emb,
      theorem49BoundaryRootSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_residualBoundaryLayerFacePeelWitnessData
        boundaryData dartCycles hselectedBoundaryArc data C₀ hC₀⟩

theorem
    exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
        Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∧
          HasUnblockedInteriorEndpoint emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C₀ := by
  rcases hG with ⟨emb, ⟨source⟩, ⟨data⟩, hEndpoint⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
        source data hEndpoint C₀ hC₀⟩

theorem
    exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
        ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
            Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∧
              HasUnblockedInteriorEndpoint emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C₀ := by
  rcases hG with
    ⟨emb, ⟨boundaryData⟩, dartCycles, hselectedBoundaryArc, ⟨data⟩, hEndpoint⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
        boundaryData dartCycles hselectedBoundaryArc data hEndpoint C₀ hC₀⟩

theorem
    exists_theorem49BoundaryRawQuotientErrorPackage_of_exists_closedWalkAnnulusBoundarySource_and_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {x : G.edgeSet → Color}
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
        Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∧
          HasUnblockedInteriorEndpoint emb ∧
            x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRawQuotientErrorPackage emb C₀ x := by
  rcases hG with ⟨emb, ⟨source⟩, ⟨data⟩, hEndpoint, hx⟩
  exact
    ⟨emb,
      theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusBoundarySource_and_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
        source data hEndpoint C₀ hC₀ hx⟩

theorem
    exists_theorem49BoundaryRawQuotientErrorPackage_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {x : G.edgeSet → Color}
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
        ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
            Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∧
              HasUnblockedInteriorEndpoint emb ∧
                x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRawQuotientErrorPackage emb C₀ x := by
  rcases hG with
    ⟨emb, ⟨boundaryData⟩, dartCycles, hselectedBoundaryArc, ⟨data⟩, hEndpoint, hx⟩
  exact
    ⟨emb,
      theorem49BoundaryRawQuotientErrorPackage_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
        boundaryData dartCycles hselectedBoundaryArc data hEndpoint C₀ hC₀ hx⟩

theorem
    exists_theorem49BoundaryRootSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_residualBoundarySelectorData_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
        Nonempty (ResidualBoundarySelectorData emb))
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases hG with ⟨emb, ⟨source⟩, ⟨data⟩⟩
  exact
    ⟨emb,
      theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_residualBoundarySelectorData
        source data C₀ hC₀⟩

theorem
    exists_theorem49BoundaryRootSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_residualBoundarySelectorData_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
        ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
            Nonempty (ResidualBoundarySelectorData emb))
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases hG with ⟨emb, ⟨boundaryData⟩, dartCycles, hselectedBoundaryArc, ⟨data⟩⟩
  exact
    ⟨emb,
      theorem49BoundaryRootSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_residualBoundarySelectorData
        boundaryData dartCycles hselectedBoundaryArc data C₀ hC₀⟩

theorem
    exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_residualBoundarySelectorData_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
        Nonempty (ResidualBoundarySelectorData emb) ∧
          HasUnblockedInteriorEndpoint emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C₀ := by
  rcases hG with ⟨emb, ⟨source⟩, ⟨data⟩, hEndpoint⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_residualBoundarySelectorData_and_hasUnblockedInteriorEndpoint
        source data hEndpoint C₀ hC₀⟩

theorem
    exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_residualBoundarySelectorData_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
        ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
            Nonempty (ResidualBoundarySelectorData emb) ∧
              HasUnblockedInteriorEndpoint emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C₀ := by
  rcases hG with
    ⟨emb, ⟨boundaryData⟩, dartCycles, hselectedBoundaryArc, ⟨data⟩, hEndpoint⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_residualBoundarySelectorData_and_hasUnblockedInteriorEndpoint
        boundaryData dartCycles hselectedBoundaryArc data hEndpoint C₀ hC₀⟩

theorem
    exists_theorem49BoundaryRawQuotientErrorPackage_of_exists_closedWalkAnnulusBoundarySource_and_residualBoundarySelectorData_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {x : G.edgeSet → Color}
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
        Nonempty (ResidualBoundarySelectorData emb) ∧
          HasUnblockedInteriorEndpoint emb ∧
            x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRawQuotientErrorPackage emb C₀ x := by
  rcases hG with ⟨emb, ⟨source⟩, ⟨data⟩, hEndpoint, hx⟩
  exact
    ⟨emb,
      theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusBoundarySource_and_residualBoundarySelectorData_and_hasUnblockedInteriorEndpoint
        source data hEndpoint C₀ hC₀ hx⟩

theorem
    exists_theorem49BoundaryRawQuotientErrorPackage_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_residualBoundarySelectorData_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {x : G.edgeSet → Color}
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
        ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
            Nonempty (ResidualBoundarySelectorData emb) ∧
              HasUnblockedInteriorEndpoint emb ∧
                x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRawQuotientErrorPackage emb C₀ x := by
  rcases hG with
    ⟨emb, ⟨boundaryData⟩, dartCycles, hselectedBoundaryArc, ⟨data⟩, hEndpoint, hx⟩
  exact
    ⟨emb,
      theorem49BoundaryRawQuotientErrorPackage_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_residualBoundarySelectorData_and_hasUnblockedInteriorEndpoint
        boundaryData dartCycles hselectedBoundaryArc data hEndpoint C₀ hC₀ hx⟩

theorem
    exists_embedding_residualBoundaryPositiveProjectedGeometryOn_of_exists_closedWalkAnnulusBoundarySource_and_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
        Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∧
          HasUnblockedInteriorEndpoint emb) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb := by
  rcases hG with ⟨emb, ⟨source⟩, ⟨data⟩, hEndpoint⟩
  exact
    ⟨emb,
      theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
        source data hEndpoint⟩

theorem
    exists_embedding_residualBoundaryPositiveProjectedGeometryOn_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
        ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
            Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∧
              HasUnblockedInteriorEndpoint emb) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb := by
  rcases hG with
    ⟨emb, ⟨boundaryData⟩, dartCycles, hselectedBoundaryArc, ⟨data⟩, hEndpoint⟩
  exact
    ⟨emb,
      theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
        boundaryData dartCycles hselectedBoundaryArc data hEndpoint⟩

theorem
    exists_embedding_currentBoundaryRemainders_of_exists_closedWalkAnnulusBoundarySource_and_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint_via_residualBoundary
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
        Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∧
          HasUnblockedInteriorEndpoint emb) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb,
      ∃ i : Fin data.numLayers, ∃ f ∈ data.layerFaces i,
        ∀ e ∈ (emb.faceBoundary f.1).erase (data.witnessEdge f), e ∈ data.currentBoundary i := by
  rcases hG with ⟨emb, ⟨source⟩, ⟨data⟩, hEndpoint⟩
  rcases
    theorem49CurrentBoundaryRemainders_of_closedWalkAnnulusBoundarySource_and_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint_via_residualBoundary
      source data hEndpoint with
    ⟨i, f, hf, hremainders⟩
  exact ⟨emb, data, i, f, hf, hremainders⟩

theorem
    exists_embedding_currentBoundaryRemainders_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint_via_residualBoundary
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
        ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
            Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∧
              HasUnblockedInteriorEndpoint emb) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb,
      ∃ i : Fin data.numLayers, ∃ f ∈ data.layerFaces i,
        ∀ e ∈ (emb.faceBoundary f.1).erase (data.witnessEdge f), e ∈ data.currentBoundary i := by
  rcases hG with
    ⟨emb, ⟨boundaryData⟩, dartCycles, hselectedBoundaryArc, ⟨data⟩, hEndpoint⟩
  rcases
    theorem49CurrentBoundaryRemainders_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint_via_residualBoundary
      boundaryData dartCycles hselectedBoundaryArc data hEndpoint with
    ⟨i, f, hf, hremainders⟩
  exact ⟨emb, data, i, f, hf, hremainders⟩

theorem
    exists_embedding_residualBoundaryPositiveProjectedGeometryOn_of_exists_closedWalkAnnulusBoundarySource_and_residualBoundarySelectorData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
        Nonempty (ResidualBoundarySelectorData emb) ∧
          HasUnblockedInteriorEndpoint emb) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb := by
  rcases hG with ⟨emb, ⟨source⟩, ⟨data⟩, hEndpoint⟩
  exact
    ⟨emb,
      theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_residualBoundarySelectorData_and_hasUnblockedInteriorEndpoint
        source data hEndpoint⟩

theorem
    exists_embedding_residualBoundaryPositiveProjectedGeometryOn_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_residualBoundarySelectorData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
        ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
            Nonempty (ResidualBoundarySelectorData emb) ∧
              HasUnblockedInteriorEndpoint emb) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb := by
  rcases hG with
    ⟨emb, ⟨boundaryData⟩, dartCycles, hselectedBoundaryArc, ⟨data⟩, hEndpoint⟩
  exact
    ⟨emb,
      theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_residualBoundarySelectorData_and_hasUnblockedInteriorEndpoint
        boundaryData dartCycles hselectedBoundaryArc data hEndpoint⟩

theorem
    exists_embedding_currentBoundaryRemainders_of_exists_closedWalkAnnulusBoundarySource_and_residualBoundarySelectorData_and_hasUnblockedInteriorEndpoint_via_residualBoundary
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
        Nonempty (ResidualBoundarySelectorData emb) ∧
          HasUnblockedInteriorEndpoint emb) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb,
      ∃ i : Fin data.numLayers, ∃ f ∈ data.layerFaces i,
        ∀ e ∈ (emb.faceBoundary f.1).erase (data.witnessEdge f), e ∈ data.currentBoundary i := by
  rcases hG with ⟨emb, ⟨source⟩, ⟨data⟩, hEndpoint⟩
  rcases
    theorem49CurrentBoundaryRemainders_of_closedWalkAnnulusBoundarySource_and_residualBoundarySelectorData_and_hasUnblockedInteriorEndpoint_via_residualBoundary
      source data hEndpoint with
    ⟨i, f, hf, hremainders⟩
  exact
    ⟨emb, data.toResidualBoundaryLayerFacePeelWitnessData, i, f, hf, hremainders⟩

theorem
    exists_embedding_currentBoundaryRemainders_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_residualBoundarySelectorData_and_hasUnblockedInteriorEndpoint_via_residualBoundary
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
        ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
            Nonempty (ResidualBoundarySelectorData emb) ∧
              HasUnblockedInteriorEndpoint emb) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb,
      ∃ i : Fin data.numLayers, ∃ f ∈ data.layerFaces i,
        ∀ e ∈ (emb.faceBoundary f.1).erase (data.witnessEdge f), e ∈ data.currentBoundary i := by
  rcases hG with
    ⟨emb, ⟨boundaryData⟩, dartCycles, hselectedBoundaryArc, ⟨data⟩, hEndpoint⟩
  rcases
    theorem49CurrentBoundaryRemainders_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_residualBoundarySelectorData_and_hasUnblockedInteriorEndpoint_via_residualBoundary
      boundaryData dartCycles hselectedBoundaryArc data hEndpoint with
    ⟨i, f, hf, hremainders⟩
  exact
    ⟨emb, data.toResidualBoundaryLayerFacePeelWitnessData, i, f, hf, hremainders⟩

namespace Theorem49ResidualBoundaryRoute

open Theorem49PositiveGeometricSourceConstruction

theorem counterEmbedding_residualBoundaryPositiveProjectedGeometryOn :
    Theorem49ResidualBoundaryPositiveProjectedGeometryOn
      Theorem49PlanarBoundaryAnnulusGeometryRegression.counterEmbedding := by
  exact
    theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
      Theorem49PlanarBoundaryAnnulusGeometryRegression.counterCollarGeometry
      counterEmbedding_hasUnblockedInteriorEndpoint

theorem counterEmbedding_boundaryRootNonemptyProjectedSynthesis_via_residualBoundary
    [Fintype Theorem49PlanarBoundaryAnnulusGeometryRegression.counterGraph.edgeSet]
    [FiniteDimensional F2
      (Theorem49PlanarBoundaryAnnulusGeometryRegression.counterGraph.edgeSet → Color)] :
    Theorem49BoundaryRootNonemptyProjectedSynthesis
      Theorem49PlanarBoundaryAnnulusGeometryRegression.counterEmbedding
      counterGraphTaitEdgeColoring := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint_via_residualBoundary
      Theorem49PlanarBoundaryAnnulusGeometryRegression.counterCollarGeometry
      counterEmbedding_hasUnblockedInteriorEndpoint
      counterGraphTaitEdgeColoring counterGraphTaitEdgeColoring_isTait

/-- Stronger calibration of the two-collar positive benchmark: the residual/current-boundary
positive shell already reaches the nonempty projected theorem-4.9 endpoint on the same
embedding, while a forcing interior edge still blocks both the selector and construction
face-layer shells there. -/
theorem
    counterEmbedding_residualBoundaryPositiveProjectedGeometryOn_and_boundaryRootNonemptyProjectedSynthesis_and_forcingInteriorEdgeWitness_without_boundaryFreeSelector_or_planarBoundaryAnnulusConstructionFaceLayerData
    [Fintype Theorem49PlanarBoundaryAnnulusGeometryRegression.counterGraph.edgeSet]
    [FiniteDimensional F2
      (Theorem49PlanarBoundaryAnnulusGeometryRegression.counterGraph.edgeSet → Color)] :
    Theorem49ResidualBoundaryPositiveProjectedGeometryOn
        Theorem49PlanarBoundaryAnnulusGeometryRegression.counterEmbedding ∧
      Theorem49BoundaryRootNonemptyProjectedSynthesis
        Theorem49PlanarBoundaryAnnulusGeometryRegression.counterEmbedding
        counterGraphTaitEdgeColoring ∧
      Nonempty
        (ForcingInteriorEdgeWitness
          Theorem49PlanarBoundaryAnnulusGeometryRegression.counterEmbedding) ∧
      ¬ Nonempty
        (BoundaryFreeIncidentFaceSelector
          Theorem49PlanarBoundaryAnnulusGeometryRegression.counterEmbedding) ∧
      ¬ Nonempty
        (PlanarBoundaryAnnulusConstructionFaceLayerData
          Theorem49PlanarBoundaryAnnulusGeometryRegression.counterEmbedding) := by
  exact
    ⟨counterEmbedding_residualBoundaryPositiveProjectedGeometryOn,
      counterEmbedding_boundaryRootNonemptyProjectedSynthesis_via_residualBoundary,
      nonempty_forcingInteriorEdgeWitness_counterEmbedding,
      not_nonempty_boundaryFreeIncidentFaceSelector_counterEmbedding,
      not_nonempty_planarBoundaryAnnulusConstructionFaceLayerData
        (emb := Theorem49PlanarBoundaryAnnulusGeometryRegression.counterEmbedding)
        counterEmbeddingForcingInteriorEdgeWitness⟩

/-- The two-collar positive benchmark already inhabits the residual/current-boundary positive
shell while still failing both the boundary-free selector shell and the downstream construction
face-layer shell on the same embedding.  So the residual wrapper itself does not repair that
selector/construction gap. -/
theorem
    counterEmbedding_residualBoundaryPositiveProjectedGeometryOn_without_boundaryFreeSelector_or_planarBoundaryAnnulusConstructionFaceLayerData
    :
    Theorem49ResidualBoundaryPositiveProjectedGeometryOn
        Theorem49PlanarBoundaryAnnulusGeometryRegression.counterEmbedding ∧
      ¬ Nonempty
        (BoundaryFreeIncidentFaceSelector
          Theorem49PlanarBoundaryAnnulusGeometryRegression.counterEmbedding) ∧
      ¬ Nonempty
        (PlanarBoundaryAnnulusConstructionFaceLayerData
          Theorem49PlanarBoundaryAnnulusGeometryRegression.counterEmbedding) := by
  exact
    ⟨counterEmbedding_residualBoundaryPositiveProjectedGeometryOn,
      not_nonempty_boundaryFreeIncidentFaceSelector_counterEmbedding,
      not_nonempty_planarBoundaryAnnulusConstructionFaceLayerData
        (emb := Theorem49PlanarBoundaryAnnulusGeometryRegression.counterEmbedding)
        counterEmbeddingForcingInteriorEdgeWitness⟩

/-- Residual/current-boundary positive geometry does not universally produce a boundary-free
incident-face selector on the same embedding.  The two-collar positive benchmark already carries
the residual shell while its forcing edge blocks every selector. -/
theorem
    not_forall_nonempty_boundaryFreeIncidentFaceSelector_of_theorem49ResidualBoundaryPositiveProjectedGeometryOn_counterGraph
    :
    ¬ ∀ {emb :
          PlaneEmbeddingWithBoundary
            Theorem49PlanarBoundaryAnnulusGeometryRegression.counterGraph},
        Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb →
          Nonempty (BoundaryFreeIncidentFaceSelector emb) := by
  intro h
  exact
    not_nonempty_boundaryFreeIncidentFaceSelector_counterEmbedding
      (h (emb := Theorem49PlanarBoundaryAnnulusGeometryRegression.counterEmbedding)
        counterEmbedding_residualBoundaryPositiveProjectedGeometryOn)

/-- The same residual/current-boundary positive shell also does not universally produce the
downstream construction face-layer package on the same embedding.  So even after passing through
the residual wrapper, the selector/construction burden remains genuinely open. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_theorem49ResidualBoundaryPositiveProjectedGeometryOn_counterGraph
    :
    ¬ ∀ {emb :
          PlaneEmbeddingWithBoundary
            Theorem49PlanarBoundaryAnnulusGeometryRegression.counterGraph},
        Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb →
          Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb) := by
  intro h
  exact
    not_nonempty_planarBoundaryAnnulusConstructionFaceLayerData
        (emb := Theorem49PlanarBoundaryAnnulusGeometryRegression.counterEmbedding)
        counterEmbeddingForcingInteriorEdgeWitness
      (h (emb := Theorem49PlanarBoundaryAnnulusGeometryRegression.counterEmbedding)
        counterEmbedding_residualBoundaryPositiveProjectedGeometryOn)

/-- Graph-level classification of the same two-collar benchmark: for the explicit constant Tait
coloring, the residual/current-boundary positive shell and the projected theorem-4.9 endpoint
already coexist on one embedding with a forcing interior edge and failure of both the selector
and construction face-layer shells. -/
theorem
    counterGraph_explicitTait_residualBoundaryPositiveProjectedGeometry_and_boundaryRootNonemptyProjectedSynthesis_with_forcingInteriorEdgeWitness_without_boundaryFreeSelector_or_planarBoundaryAnnulusConstructionFaceLayerData
    [Fintype Theorem49PlanarBoundaryAnnulusGeometryRegression.counterGraph.edgeSet]
    [FiniteDimensional F2
      (Theorem49PlanarBoundaryAnnulusGeometryRegression.counterGraph.edgeSet → Color)] :
    IsTaitEdgeColoring
        Theorem49PlanarBoundaryAnnulusGeometryRegression.counterGraph
        counterGraphTaitEdgeColoring ∧
      (∃ emb :
          PlaneEmbeddingWithBoundary
            Theorem49PlanarBoundaryAnnulusGeometryRegression.counterGraph,
        Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb ∧
          Theorem49BoundaryRootNonemptyProjectedSynthesis
            emb counterGraphTaitEdgeColoring ∧
          Nonempty (ForcingInteriorEdgeWitness emb) ∧
          ¬ Nonempty (BoundaryFreeIncidentFaceSelector emb) ∧
          ¬ Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb)) := by
  exact
    ⟨counterGraphTaitEdgeColoring_isTait,
      ⟨Theorem49PlanarBoundaryAnnulusGeometryRegression.counterEmbedding,
        counterEmbedding_residualBoundaryPositiveProjectedGeometryOn_and_boundaryRootNonemptyProjectedSynthesis_and_forcingInteriorEdgeWitness_without_boundaryFreeSelector_or_planarBoundaryAnnulusConstructionFaceLayerData⟩⟩

end Theorem49ResidualBoundaryRoute

end Mettapedia.GraphTheory.FourColor
