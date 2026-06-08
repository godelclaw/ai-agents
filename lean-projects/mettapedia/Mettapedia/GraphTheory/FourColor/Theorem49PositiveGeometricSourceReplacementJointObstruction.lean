import Mettapedia.GraphTheory.FourColor.Theorem49PositiveGeometricSourceReplacementRoute
import Mettapedia.GraphTheory.FourColor.Theorem49ForcingInteriorEdgeObstruction

/-!
# Joint obstruction profile for constructive positive route packages

This file records a lasting structural burden on the current constructive positive route
packages.  Once a source-side positive package carries both a surviving purified selected-boundary
carrier and enough parent/root data to exclude forcing interior edges, the same embedding must
simultaneously:

1. contain a face boundary with two distinct interior edges; and
2. avoid any forcing interior-edge witness.

These theorems package both constraints together on the named route-facing positive surfaces.
-/

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open Theorem49ForcingInteriorEdgeObstruction

variable {V : Type*} [DecidableEq V]

/-- The closed-walk root-parent positive route package simultaneously forces a face boundary with
two distinct interior edges and excludes forcing interior-edge witnesses on the same embedding. -/
theorem
    exists_two_distinct_interior_edges_on_faceBoundary_and_not_nonempty_forcingInteriorEdgeWitness_of_closedWalkAnnulusRootParentPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometryOn emb) :
    (∃ f : AmbientFace emb.faces,
      ∃ e₁ : G.edgeSet,
        e₁ ∈ emb.faceBoundary f.1 ∧
          e₁ ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∧
            ∃ e₂ : G.edgeSet,
              e₂ ∈ emb.faceBoundary f.1 ∧
                e₂ ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∧ e₁ ≠ e₂) ∧
      ¬ Nonempty (ForcingInteriorEdgeWitness emb) := by
  rcases geom with ⟨source, interiorData, hCarrier⟩
  refine ⟨?_, ?_⟩
  · exact
      exists_two_distinct_interior_edges_on_faceBoundary_of_closedWalkEmbeddingData_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
        emb source.closedWalks hCarrier
  · exact
      not_nonempty_forcingInteriorEdgeWitness_of_interiorDualBoundaryRootParentPeelData
        interiorData

theorem
    not_nonempty_forcingInteriorEdgeWitness_of_closedWalkAnnulusRootParentPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometryOn emb) :
    ¬ Nonempty (ForcingInteriorEdgeWitness emb) :=
  (exists_two_distinct_interior_edges_on_faceBoundary_and_not_nonempty_forcingInteriorEdgeWitness_of_closedWalkAnnulusRootParentPositiveProjectedGeometryOn
    geom).2

theorem
    everyInteriorEdgeHasBoundaryFreeIncidentFace_of_closedWalkAnnulusRootParentPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometryOn emb) :
    EveryInteriorEdgeHasBoundaryFreeIncidentFace emb :=
  everyInteriorEdgeHasBoundaryFreeIncidentFace_of_not_nonempty_forcingInteriorEdgeWitness
    (not_nonempty_forcingInteriorEdgeWitness_of_closedWalkAnnulusRootParentPositiveProjectedGeometryOn
      geom)

theorem
    nonempty_boundaryFreeIncidentFaceSelector_of_closedWalkAnnulusRootParentPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometryOn emb) :
    Nonempty (BoundaryFreeIncidentFaceSelector emb) :=
  (nonempty_boundaryFreeIncidentFaceSelector_iff_not_nonempty_forcingInteriorEdgeWitness).2
    (not_nonempty_forcingInteriorEdgeWitness_of_closedWalkAnnulusRootParentPositiveProjectedGeometryOn
      geom)

noncomputable def
    boundaryFreeIncidentFaceSelector_of_closedWalkAnnulusRootParentPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometryOn emb) :
    BoundaryFreeIncidentFaceSelector emb :=
  Classical.choice
    (nonempty_boundaryFreeIncidentFaceSelector_of_closedWalkAnnulusRootParentPositiveProjectedGeometryOn
      geom)

/-- The successor-cycle root-parent positive route package carries the same joint obstruction
profile as its closed-walk lowering. -/
theorem
    exists_two_distinct_interior_edges_on_faceBoundary_and_not_nonempty_forcingInteriorEdgeWitness_of_successorCycleAnnulusRootParentPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometryOn emb) :
    (∃ f : AmbientFace emb.faces,
      ∃ e₁ : G.edgeSet,
        e₁ ∈ emb.faceBoundary f.1 ∧
          e₁ ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∧
            ∃ e₂ : G.edgeSet,
              e₂ ∈ emb.faceBoundary f.1 ∧
                e₂ ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∧ e₁ ≠ e₂) ∧
      ¬ Nonempty (ForcingInteriorEdgeWitness emb) := by
  exact
    exists_two_distinct_interior_edges_on_faceBoundary_and_not_nonempty_forcingInteriorEdgeWitness_of_closedWalkAnnulusRootParentPositiveProjectedGeometryOn
      (theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometryOn_of_successorCycleAnnulusRootParentPositiveProjectedGeometryOn
        geom)

theorem
    not_nonempty_forcingInteriorEdgeWitness_of_successorCycleAnnulusRootParentPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometryOn emb) :
    ¬ Nonempty (ForcingInteriorEdgeWitness emb) :=
  (exists_two_distinct_interior_edges_on_faceBoundary_and_not_nonempty_forcingInteriorEdgeWitness_of_successorCycleAnnulusRootParentPositiveProjectedGeometryOn
    geom).2

theorem
    everyInteriorEdgeHasBoundaryFreeIncidentFace_of_successorCycleAnnulusRootParentPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometryOn emb) :
    EveryInteriorEdgeHasBoundaryFreeIncidentFace emb :=
  everyInteriorEdgeHasBoundaryFreeIncidentFace_of_not_nonempty_forcingInteriorEdgeWitness
    (not_nonempty_forcingInteriorEdgeWitness_of_successorCycleAnnulusRootParentPositiveProjectedGeometryOn
      geom)

theorem
    nonempty_boundaryFreeIncidentFaceSelector_of_successorCycleAnnulusRootParentPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometryOn emb) :
    Nonempty (BoundaryFreeIncidentFaceSelector emb) :=
  (nonempty_boundaryFreeIncidentFaceSelector_iff_not_nonempty_forcingInteriorEdgeWitness).2
    (not_nonempty_forcingInteriorEdgeWitness_of_successorCycleAnnulusRootParentPositiveProjectedGeometryOn
      geom)

noncomputable def
    boundaryFreeIncidentFaceSelector_of_successorCycleAnnulusRootParentPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometryOn emb) :
    BoundaryFreeIncidentFaceSelector emb :=
  Classical.choice
    (nonempty_boundaryFreeIncidentFaceSelector_of_successorCycleAnnulusRootParentPositiveProjectedGeometryOn
      geom)

/-- The closed-walk root-distance positive route package also forces the same pair of local
burdens: some face boundary contains two distinct interior edges, yet no forcing interior edge is
allowed on the same embedding. -/
theorem
    exists_two_distinct_interior_edges_on_faceBoundary_and_not_nonempty_forcingInteriorEdgeWitness_of_closedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn emb) :
    (∃ f : AmbientFace emb.faces,
      ∃ e₁ : G.edgeSet,
        e₁ ∈ emb.faceBoundary f.1 ∧
          e₁ ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∧
            ∃ e₂ : G.edgeSet,
              e₂ ∈ emb.faceBoundary f.1 ∧
                e₂ ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∧ e₁ ≠ e₂) ∧
      ¬ Nonempty (ForcingInteriorEdgeWitness emb) := by
  rcases geom with ⟨source, interiorData, hCarrier⟩
  refine ⟨?_, ?_⟩
  · exact
      exists_two_distinct_interior_edges_on_faceBoundary_of_closedWalkEmbeddingData_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
        emb source.closedWalks hCarrier
  · exact
      not_nonempty_forcingInteriorEdgeWitness_of_interiorDualBoundaryRootAdjDistancePeelData
        interiorData

theorem
    not_nonempty_forcingInteriorEdgeWitness_of_closedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn emb) :
    ¬ Nonempty (ForcingInteriorEdgeWitness emb) :=
  (exists_two_distinct_interior_edges_on_faceBoundary_and_not_nonempty_forcingInteriorEdgeWitness_of_closedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn
    geom).2

theorem
    everyInteriorEdgeHasBoundaryFreeIncidentFace_of_closedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn emb) :
    EveryInteriorEdgeHasBoundaryFreeIncidentFace emb :=
  everyInteriorEdgeHasBoundaryFreeIncidentFace_of_not_nonempty_forcingInteriorEdgeWitness
    (not_nonempty_forcingInteriorEdgeWitness_of_closedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn
      geom)

theorem
    nonempty_boundaryFreeIncidentFaceSelector_of_closedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn emb) :
    Nonempty (BoundaryFreeIncidentFaceSelector emb) :=
  (nonempty_boundaryFreeIncidentFaceSelector_iff_not_nonempty_forcingInteriorEdgeWitness).2
    (not_nonempty_forcingInteriorEdgeWitness_of_closedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn
      geom)

noncomputable def
    boundaryFreeIncidentFaceSelector_of_closedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn emb) :
    BoundaryFreeIncidentFaceSelector emb :=
  Classical.choice
    (nonempty_boundaryFreeIncidentFaceSelector_of_closedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn
      geom)

/-- The successor-cycle root-distance positive route package inherits the same joint obstruction
profile from its closed-walk lowering. -/
theorem
    exists_two_distinct_interior_edges_on_faceBoundary_and_not_nonempty_forcingInteriorEdgeWitness_of_successorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn emb) :
    (∃ f : AmbientFace emb.faces,
      ∃ e₁ : G.edgeSet,
        e₁ ∈ emb.faceBoundary f.1 ∧
          e₁ ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∧
            ∃ e₂ : G.edgeSet,
              e₂ ∈ emb.faceBoundary f.1 ∧
                e₂ ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∧ e₁ ≠ e₂) ∧
      ¬ Nonempty (ForcingInteriorEdgeWitness emb) := by
  exact
    exists_two_distinct_interior_edges_on_faceBoundary_and_not_nonempty_forcingInteriorEdgeWitness_of_closedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn
      (theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn_of_successorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn
        geom)

theorem
    not_nonempty_forcingInteriorEdgeWitness_of_successorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn emb) :
    ¬ Nonempty (ForcingInteriorEdgeWitness emb) :=
  (exists_two_distinct_interior_edges_on_faceBoundary_and_not_nonempty_forcingInteriorEdgeWitness_of_successorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn
    geom).2

theorem
    everyInteriorEdgeHasBoundaryFreeIncidentFace_of_successorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn emb) :
    EveryInteriorEdgeHasBoundaryFreeIncidentFace emb :=
  everyInteriorEdgeHasBoundaryFreeIncidentFace_of_not_nonempty_forcingInteriorEdgeWitness
    (not_nonempty_forcingInteriorEdgeWitness_of_successorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn
      geom)

theorem
    nonempty_boundaryFreeIncidentFaceSelector_of_successorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn emb) :
    Nonempty (BoundaryFreeIncidentFaceSelector emb) :=
  (nonempty_boundaryFreeIncidentFaceSelector_iff_not_nonempty_forcingInteriorEdgeWitness).2
    (not_nonempty_forcingInteriorEdgeWitness_of_successorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn
      geom)

noncomputable def
    boundaryFreeIncidentFaceSelector_of_successorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn emb) :
    BoundaryFreeIncidentFaceSelector emb :=
  Classical.choice
    (nonempty_boundaryFreeIncidentFaceSelector_of_successorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn
      geom)

namespace Theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometry

theorem not_nonempty_forcingInteriorEdgeWitness
    {G : SimpleGraph V}
    (geom : Theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometry G) :
    ¬ Nonempty (ForcingInteriorEdgeWitness geom.emb) :=
  not_nonempty_forcingInteriorEdgeWitness_of_closedWalkAnnulusRootParentPositiveProjectedGeometryOn
    geom.on

theorem everyInteriorEdgeHasBoundaryFreeIncidentFace
    {G : SimpleGraph V}
    (geom : Theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometry G) :
    EveryInteriorEdgeHasBoundaryFreeIncidentFace geom.emb :=
  everyInteriorEdgeHasBoundaryFreeIncidentFace_of_closedWalkAnnulusRootParentPositiveProjectedGeometryOn
    geom.on

theorem nonempty_boundaryFreeIncidentFaceSelector
    {G : SimpleGraph V}
    (geom : Theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometry G) :
    Nonempty (BoundaryFreeIncidentFaceSelector geom.emb) :=
  nonempty_boundaryFreeIncidentFaceSelector_of_closedWalkAnnulusRootParentPositiveProjectedGeometryOn
    geom.on

noncomputable def boundaryFreeIncidentFaceSelector
    {G : SimpleGraph V}
    (geom : Theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometry G) :
    BoundaryFreeIncidentFaceSelector geom.emb :=
  Classical.choice geom.nonempty_boundaryFreeIncidentFaceSelector

end Theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometry

namespace Theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometry

theorem not_nonempty_forcingInteriorEdgeWitness
    {G : SimpleGraph V}
    (geom : Theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometry G) :
    ¬ Nonempty (ForcingInteriorEdgeWitness geom.emb) :=
  not_nonempty_forcingInteriorEdgeWitness_of_successorCycleAnnulusRootParentPositiveProjectedGeometryOn
    geom.on

theorem everyInteriorEdgeHasBoundaryFreeIncidentFace
    {G : SimpleGraph V}
    (geom : Theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometry G) :
    EveryInteriorEdgeHasBoundaryFreeIncidentFace geom.emb :=
  everyInteriorEdgeHasBoundaryFreeIncidentFace_of_successorCycleAnnulusRootParentPositiveProjectedGeometryOn
    geom.on

theorem nonempty_boundaryFreeIncidentFaceSelector
    {G : SimpleGraph V}
    (geom : Theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometry G) :
    Nonempty (BoundaryFreeIncidentFaceSelector geom.emb) :=
  nonempty_boundaryFreeIncidentFaceSelector_of_successorCycleAnnulusRootParentPositiveProjectedGeometryOn
    geom.on

noncomputable def boundaryFreeIncidentFaceSelector
    {G : SimpleGraph V}
    (geom : Theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometry G) :
    BoundaryFreeIncidentFaceSelector geom.emb :=
  Classical.choice geom.nonempty_boundaryFreeIncidentFaceSelector

end Theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometry

namespace Theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometry

theorem not_nonempty_forcingInteriorEdgeWitness
    {G : SimpleGraph V}
    (geom : Theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometry G) :
    ¬ Nonempty (ForcingInteriorEdgeWitness geom.emb) :=
  not_nonempty_forcingInteriorEdgeWitness_of_closedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn
    geom.on

theorem everyInteriorEdgeHasBoundaryFreeIncidentFace
    {G : SimpleGraph V}
    (geom : Theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometry G) :
    EveryInteriorEdgeHasBoundaryFreeIncidentFace geom.emb :=
  everyInteriorEdgeHasBoundaryFreeIncidentFace_of_closedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn
    geom.on

theorem nonempty_boundaryFreeIncidentFaceSelector
    {G : SimpleGraph V}
    (geom : Theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometry G) :
    Nonempty (BoundaryFreeIncidentFaceSelector geom.emb) :=
  nonempty_boundaryFreeIncidentFaceSelector_of_closedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn
    geom.on

noncomputable def boundaryFreeIncidentFaceSelector
    {G : SimpleGraph V}
    (geom : Theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometry G) :
    BoundaryFreeIncidentFaceSelector geom.emb :=
  Classical.choice geom.nonempty_boundaryFreeIncidentFaceSelector

end Theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometry

namespace Theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometry

theorem not_nonempty_forcingInteriorEdgeWitness
    {G : SimpleGraph V}
    (geom : Theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometry G) :
    ¬ Nonempty (ForcingInteriorEdgeWitness geom.emb) :=
  not_nonempty_forcingInteriorEdgeWitness_of_successorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn
    geom.on

theorem everyInteriorEdgeHasBoundaryFreeIncidentFace
    {G : SimpleGraph V}
    (geom : Theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometry G) :
    EveryInteriorEdgeHasBoundaryFreeIncidentFace geom.emb :=
  everyInteriorEdgeHasBoundaryFreeIncidentFace_of_successorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn
    geom.on

theorem nonempty_boundaryFreeIncidentFaceSelector
    {G : SimpleGraph V}
    (geom : Theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometry G) :
    Nonempty (BoundaryFreeIncidentFaceSelector geom.emb) :=
  nonempty_boundaryFreeIncidentFaceSelector_of_successorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn
    geom.on

noncomputable def boundaryFreeIncidentFaceSelector
    {G : SimpleGraph V}
    (geom : Theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometry G) :
    BoundaryFreeIncidentFaceSelector geom.emb :=
  Classical.choice geom.nonempty_boundaryFreeIncidentFaceSelector

end Theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometry

end Mettapedia.GraphTheory.FourColor
