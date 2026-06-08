import Mettapedia.GraphTheory.FourColor.Theorem49InteriorVertices
import Mettapedia.GraphTheory.FourColor.PlanarBoundaryAnnulusConstruction
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryAnnulusRootInteriorDual

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- The finite vertex carrier touched by all peeled-face boundaries in an annulus construction. -/
def PlanarBoundaryAnnulusConstruction.peelFaceBoundaryEndpointSupport
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb) : Finset V :=
  data.peelFaces.biUnion fun f => edgeEndpointSupport (emb.faceBoundary f.1)

theorem PlanarBoundaryAnnulusConstruction.mem_peelFaceBoundaryEndpointSupport_iff
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb) {v : V} :
    v ∈ data.peelFaceBoundaryEndpointSupport ↔
      ∃ f ∈ data.peelFaces, v ∈ edgeEndpointSupport (emb.faceBoundary f.1) := by
  simp [PlanarBoundaryAnnulusConstruction.peelFaceBoundaryEndpointSupport]

/-- A finite-support version of the peeled-face endpoint no-touch condition.  This is the exact
endpoint-level strengthening of the existing peeled-face edge-disjointness field. -/
def PlanarBoundaryAnnulusConstruction.peelFacesEndpointDisjointSelectedBoundarySupport
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb) : Prop :=
  Disjoint data.peelFaceBoundaryEndpointSupport
    (edgeEndpointSupport
      (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))

theorem
    PlanarBoundaryAnnulusConstruction.peelFacesEndpointDisjointSelectedBoundarySupport_iff
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb) :
    data.peelFacesEndpointDisjointSelectedBoundarySupport ↔
      ∀ f ∈ data.peelFaces,
        Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
          (edgeEndpointSupport
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) := by
  unfold PlanarBoundaryAnnulusConstruction.peelFacesEndpointDisjointSelectedBoundarySupport
  rw [Finset.disjoint_left]
  constructor
  · intro h f hf
    rw [Finset.disjoint_left]
    intro v hvFace hvBoundary
    exact h ((data.mem_peelFaceBoundaryEndpointSupport_iff).2
      ⟨f, hf, hvFace⟩) hvBoundary
  · intro h v hvPeel hvBoundary
    rcases (data.mem_peelFaceBoundaryEndpointSupport_iff).1 hvPeel with
      ⟨f, hf, hvFace⟩
    exact (Finset.disjoint_left.mp (h f hf)) hvFace hvBoundary

/-- Every raw face-incidence interior-edge endpoint lies on some peeled-face boundary endpoint.
This is the finite-support content of the annulus construction's witness-edge cover. -/
theorem PlanarBoundaryAnnulusConstruction.interiorEdgeEndpointSupport_subset_peelFaceBoundaryEndpointSupport
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb) :
    interiorEdgeEndpointSupport emb ⊆ data.peelFaceBoundaryEndpointSupport := by
  intro v hv
  rcases (mem_interiorEdgeEndpointSupport_iff emb).1 hv with
    ⟨eInterior, heInterior, hvInterior⟩
  have heCovered : eInterior ∈ data.peelFaces.image data.witnessEdge :=
    data.hcover heInterior
  rcases Finset.mem_image.1 heCovered with ⟨f, hfPeel, hWitness⟩
  have hvWitness : v ∈ (data.witnessEdge f : Sym2 V) := by
    simpa [hWitness] using hvInterior
  have hvFaceBoundaryEndpoint : v ∈ edgeEndpointSupport (emb.faceBoundary f.1) :=
    (mem_edgeEndpointSupport_iff (emb.faceBoundary f.1)).2
      ⟨data.witnessEdge f, data.hwitness f hfPeel, hvWitness⟩
  exact (data.mem_peelFaceBoundaryEndpointSupport_iff).2
    ⟨f, hfPeel, hvFaceBoundaryEndpoint⟩

/-- If the aggregate peeled-face endpoint carrier avoids selected-boundary endpoints, then the
raw interior-edge endpoint carrier avoids selected-boundary endpoints as well. -/
theorem
    PlanarBoundaryAnnulusConstruction.endpointSupport_disjoint_of_peelFaceBoundaryEndpointSupport_disjoint_selectedBoundarySupport
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hNoTouch : data.peelFacesEndpointDisjointSelectedBoundarySupport) :
    Disjoint (interiorEdgeEndpointSupport emb)
      (edgeEndpointSupport
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) := by
  rw [PlanarBoundaryAnnulusConstruction.peelFacesEndpointDisjointSelectedBoundarySupport,
    Finset.disjoint_left] at hNoTouch
  rw [Finset.disjoint_left]
  intro v hvInterior hvBoundary
  exact hNoTouch (data.interiorEdgeEndpointSupport_subset_peelFaceBoundaryEndpointSupport
    hvInterior) hvBoundary

/-- A peeled-face endpoint no-touch condition discharges the raw endpoint-separation obligation.
The proof uses the annulus construction's cover of every face-incidence interior edge by a peeled
face witness edge: any endpoint of an interior edge is therefore an endpoint of some peeled face
boundary, so peeled-face endpoint disjointness from the selected boundary forbids selected-boundary
incidence at that vertex. -/
theorem
    PlanarBoundaryAnnulusConstruction.endpointSupport_disjoint_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hPeelNoTouch : ∀ f ∈ data.peelFaces,
      Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
        (edgeEndpointSupport
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))) :
    Disjoint (interiorEdgeEndpointSupport emb)
      (edgeEndpointSupport
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) := by
  exact data.endpointSupport_disjoint_of_peelFaceBoundaryEndpointSupport_disjoint_selectedBoundarySupport
    ((data.peelFacesEndpointDisjointSelectedBoundarySupport_iff).2 hPeelNoTouch)

/-- The same peeled-face endpoint no-touch condition is exactly enough to make selected-boundary
purification leave the raw interior-edge endpoint carrier unchanged. -/
theorem
    PlanarBoundaryAnnulusConstruction.selectedBoundaryInteriorEdgeEndpointVertices_eq_interiorEdgeEndpointSupport_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hPeelNoTouch : ∀ f ∈ data.peelFaces,
      Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
        (edgeEndpointSupport
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))) :
    selectedBoundaryInteriorEdgeEndpointVertices emb = interiorEdgeEndpointSupport emb :=
  (selectedBoundaryInteriorEdgeEndpointVertices_eq_interiorEdgeEndpointSupport_iff_endpointSupport_disjoint
    emb).2
    (data.endpointSupport_disjoint_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
      hPeelNoTouch)

/-- Construction-level peeled-face endpoint no-touch plus a nonempty raw interior-edge endpoint
carrier produces the named local unblocked endpoint witness. -/
theorem
    PlanarBoundaryAnnulusConstruction.hasUnblockedInteriorEndpoint_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hPeelNoTouch : ∀ f ∈ data.peelFaces,
      Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
        (edgeEndpointSupport
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty) :
    HasUnblockedInteriorEndpoint emb :=
  hasUnblockedInteriorEndpoint_of_endpointSupport_disjoint_and_nonempty
    (data.endpointSupport_disjoint_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
      hPeelNoTouch)
    hRawCarrier

/-- Collar geometry inherits endpoint separation from peeled-face endpoint no-touch on its
canonical annulus construction. -/
theorem
    PlanarBoundaryAnnulusCollarGeometry.endpointSupport_disjoint_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hPeelNoTouch : ∀ f ∈
      (planarBoundaryAnnulusConstruction_of_annulusCollarGeometry data).peelFaces,
      Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
        (edgeEndpointSupport
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))) :
    Disjoint (interiorEdgeEndpointSupport emb)
      (edgeEndpointSupport
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) :=
  (planarBoundaryAnnulusConstruction_of_annulusCollarGeometry
    data).endpointSupport_disjoint_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
    hPeelNoTouch

/-- Collar geometry inherits lossless selected-boundary purification from peeled-face endpoint
no-touch on its canonical annulus construction. -/
theorem
    PlanarBoundaryAnnulusCollarGeometry.selectedBoundaryInteriorEdgeEndpointVertices_eq_interiorEdgeEndpointSupport_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hPeelNoTouch : ∀ f ∈
      (planarBoundaryAnnulusConstruction_of_annulusCollarGeometry data).peelFaces,
      Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
        (edgeEndpointSupport
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))) :
    selectedBoundaryInteriorEdgeEndpointVertices emb = interiorEdgeEndpointSupport emb :=
  (planarBoundaryAnnulusConstruction_of_annulusCollarGeometry
    data).selectedBoundaryInteriorEdgeEndpointVertices_eq_interiorEdgeEndpointSupport_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
    hPeelNoTouch

/-- Collar geometry plus peeled-face endpoint no-touch on its canonical annulus construction
produces the local unblocked endpoint witness consumed by the positive route. -/
theorem
    PlanarBoundaryAnnulusCollarGeometry.hasUnblockedInteriorEndpoint_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hPeelNoTouch : ∀ f ∈
      (planarBoundaryAnnulusConstruction_of_annulusCollarGeometry data).peelFaces,
      Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
        (edgeEndpointSupport
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty) :
    HasUnblockedInteriorEndpoint emb :=
  (planarBoundaryAnnulusConstruction_of_annulusCollarGeometry
    data).hasUnblockedInteriorEndpoint_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
    hPeelNoTouch hRawCarrier

/-- Direct same-embedding construction from the two-sided annulus-root data.  The annulus-root
package stores exactly the annulus boundary split and generic interior-dual adjacency-distance
data needed by the BFS construction layer, without imposing the impossible all-outer-root
localization. -/
noncomputable def
    planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootAdjDistancePeelData emb) :
    PlanarBoundaryAnnulusConstruction emb :=
  planarBoundaryAnnulusConstruction_of_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData
    data.boundaryData data.interiorData

/-- Two-sided annulus-root data inherits the construction-level endpoint-separation proof from
peeled-face endpoint no-touch. -/
theorem
    PlanarBoundaryAnnulusRootAdjDistancePeelData.endpointSupport_disjoint_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootAdjDistancePeelData emb)
    (hPeelNoTouch : ∀ f ∈
      (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootAdjDistancePeelData
        data).peelFaces,
      Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
        (edgeEndpointSupport
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))) :
    Disjoint (interiorEdgeEndpointSupport emb)
      (edgeEndpointSupport
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) :=
  (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootAdjDistancePeelData
    data).endpointSupport_disjoint_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
    hPeelNoTouch

/-- Two-sided annulus-root data inherits lossless selected-boundary purification from peeled-face
endpoint no-touch. -/
theorem
    PlanarBoundaryAnnulusRootAdjDistancePeelData.selectedBoundaryInteriorEdgeEndpointVertices_eq_interiorEdgeEndpointSupport_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootAdjDistancePeelData emb)
    (hPeelNoTouch : ∀ f ∈
      (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootAdjDistancePeelData
        data).peelFaces,
      Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
        (edgeEndpointSupport
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))) :
    selectedBoundaryInteriorEdgeEndpointVertices emb = interiorEdgeEndpointSupport emb :=
  (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootAdjDistancePeelData
    data).selectedBoundaryInteriorEdgeEndpointVertices_eq_interiorEdgeEndpointSupport_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
    hPeelNoTouch

/-- Two-sided annulus-root data inherits the local unblocked endpoint witness from peeled-face
endpoint no-touch and nonempty raw interior-edge endpoint support. -/
theorem
    PlanarBoundaryAnnulusRootAdjDistancePeelData.hasUnblockedInteriorEndpoint_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootAdjDistancePeelData emb)
    (hPeelNoTouch : ∀ f ∈
      (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootAdjDistancePeelData
        data).peelFaces,
      Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
        (edgeEndpointSupport
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty) :
    HasUnblockedInteriorEndpoint emb :=
  (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootAdjDistancePeelData
    data).hasUnblockedInteriorEndpoint_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
    hPeelNoTouch hRawCarrier

/-- Outer-boundary-rooted annulus route data inherits the construction-level proof that
selected-boundary purification is lossless under peeled-face endpoint no-touch. -/
theorem
    PlanarBoundaryOuterBoundaryRootAdjDistancePeelData.selectedBoundaryInteriorEdgeEndpointVertices_eq_interiorEdgeEndpointSupport_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb)
    (hPeelNoTouch : ∀ f ∈
      (planarBoundaryAnnulusConstruction_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
        data).peelFaces,
      Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
        (edgeEndpointSupport
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))) :
    selectedBoundaryInteriorEdgeEndpointVertices emb = interiorEdgeEndpointSupport emb :=
  (planarBoundaryAnnulusConstruction_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
    data).selectedBoundaryInteriorEdgeEndpointVertices_eq_interiorEdgeEndpointSupport_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
    hPeelNoTouch

/-- Outer-boundary-rooted annulus route data inherits the local unblocked endpoint witness from
peeled-face endpoint no-touch and nonempty raw interior-edge endpoint support. -/
theorem
    PlanarBoundaryOuterBoundaryRootAdjDistancePeelData.hasUnblockedInteriorEndpoint_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb)
    (hPeelNoTouch : ∀ f ∈
      (planarBoundaryAnnulusConstruction_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
        data).peelFaces,
      Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
        (edgeEndpointSupport
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty) :
    HasUnblockedInteriorEndpoint emb :=
  (planarBoundaryAnnulusConstruction_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
    data).hasUnblockedInteriorEndpoint_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
    hPeelNoTouch hRawCarrier

/-- Package the construction-level peeled-face no-touch obligation as the endpoint-separation
route data consumed by the raw interior-edge endpoint version of Theorem 4.9. -/
noncomputable def
    PlanarBoundaryOuterBoundaryRootAdjDistancePeelData.withEndpointSeparationOfPeelFacesEndpointDisjoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb)
    (hPeelNoTouch : ∀ f ∈
      (planarBoundaryAnnulusConstruction_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
        data).peelFaces,
      Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
        (edgeEndpointSupport
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))) :
    PlanarBoundaryOuterBoundaryRootAdjDistancePeelDataWithEndpointSeparation emb where
  routeData := data
  hEndpointDisjoint :=
    (planarBoundaryAnnulusConstruction_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
      data).endpointSupport_disjoint_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
      hPeelNoTouch

/-- Graph-level constructor for the endpoint-separation route package from a peeled-face no-touch
proof on each admitted outer-boundary-rooted annulus datum. -/
theorem
    admitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelDataWithEndpointSeparation_of_admitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData G)
    (hPeelNoTouchOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb,
        ∀ f ∈
          (planarBoundaryAnnulusConstruction_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
            data).peelFaces,
          Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
            (edgeEndpointSupport
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))) :
    AdmitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelDataWithEndpointSeparation G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨
    data.withEndpointSeparationOfPeelFacesEndpointDisjoint
      (hPeelNoTouchOf emb data)⟩⟩

/-- Graph-level lossless-purification consequence of peeled-face endpoint no-touch.  This is the
exact bridge saying that the selected-boundary purification agrees with the raw face-incidence
interior-edge endpoint carrier for the admitted annulus datum. -/
theorem
    exists_selectedBoundaryInteriorEdgeEndpointVertices_eq_interiorEdgeEndpointSupport_of_admitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData G)
    (hPeelNoTouchOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb,
        ∀ f ∈
          (planarBoundaryAnnulusConstruction_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
            data).peelFaces,
          Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
            (edgeEndpointSupport
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb,
        selectedBoundaryInteriorEdgeEndpointVertices emb = interiorEdgeEndpointSupport emb := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data,
    data.selectedBoundaryInteriorEdgeEndpointVertices_eq_interiorEdgeEndpointSupport_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
      (hPeelNoTouchOf emb data)⟩

/-- Annulus-route raw-carrier theorem with endpoint separation discharged from the construction
level no-touch condition on peeled faces.  This is the route-facing bridge from a geometric
annulus construction obligation to the unpurified `interiorEdgeEndpointSupport` version of
Theorem 4.9. -/
theorem
    theorem49BoundaryZeroKirchhoffSubspace_interiorEdgeEndpointSupport_image_and_separation_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (hPeelNoTouch : ∀ f ∈
      (planarBoundaryAnnulusConstruction_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
        data).peelFaces,
      Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
        (edgeEndpointSupport
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))) :
    theorem49BoundaryZeroKirchhoffSubspace emb (interiorEdgeEndpointSupport emb) =
        Submodule.map
          (boundaryZeroProjection
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
          (kirchhoffSubmodule G (interiorEdgeEndpointSupport emb)) ∧
      ∀ z : theorem49BoundaryZeroKirchhoffSubspace emb
          (interiorEdgeEndpointSupport emb),
        (∀ p ∈ projectedKempeClosureGeneratorSubspace emb C₀,
          chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) = 0) ↔
          z = 0 := by
  have hEndpointDisjoint :
      Disjoint (interiorEdgeEndpointSupport emb)
        (edgeEndpointSupport
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) :=
    (planarBoundaryAnnulusConstruction_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
      data).endpointSupport_disjoint_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
      hPeelNoTouch
  exact
    theorem49BoundaryZeroKirchhoffSubspace_interiorEdgeEndpointSupport_image_and_separation_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData_of_endpointSupport_disjoint
      (G := G) data C₀ hC₀ hEndpointDisjoint

/-- Graph-level raw-carrier Theorem 4.9 endpoint with endpoint separation discharged from a
peeled-face no-touch proof for every admitted outer-boundary-rooted annulus datum. -/
theorem
    exists_theorem49BoundaryZeroKirchhoffSubspace_interiorEdgeEndpointSupport_image_and_separation_of_admitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (hPeelNoTouchOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb,
        ∀ f ∈
          (planarBoundaryAnnulusConstruction_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
            data).peelFaces,
          Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
            (edgeEndpointSupport
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb,
        theorem49BoundaryZeroKirchhoffSubspace emb (interiorEdgeEndpointSupport emb) =
            Submodule.map
              (boundaryZeroProjection
                (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
              (kirchhoffSubmodule G (interiorEdgeEndpointSupport emb)) ∧
          ∀ z : theorem49BoundaryZeroKirchhoffSubspace emb
              (interiorEdgeEndpointSupport emb),
            (∀ p ∈ projectedKempeClosureGeneratorSubspace emb C₀,
              chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) = 0) ↔
              z = 0 := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data,
    theorem49BoundaryZeroKirchhoffSubspace_interiorEdgeEndpointSupport_image_and_separation_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
      (G := G) data C₀ hC₀ (hPeelNoTouchOf emb data)⟩

end Mettapedia.GraphTheory.FourColor
