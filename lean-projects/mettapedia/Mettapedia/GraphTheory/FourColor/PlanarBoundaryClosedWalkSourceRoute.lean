import Mettapedia.GraphTheory.FourColor.PlanarBoundaryAnnulusConstruction
import Mettapedia.GraphTheory.FourColor.PlanarBoundaryClosedWalkSource
import Mettapedia.GraphTheory.FourColor.Theorem49KempeGeneratorSpan
import Mettapedia.GraphTheory.FourColor.Theorem49Synthesis

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- Direct graph-level lowering from the explicit closed-walk annulus-boundary source to the
annulus BFS construction target. The source package supplies the same-embedding boundary
reachability, honest facial closed walks, and selected-boundary arc contiguity fields; the
remaining assumptions are exactly the construction-side frontier/contact obligations already
present in the existing theorem surface. -/
theorem
    admitsPlanarBoundaryAnnulusConstruction_of_exists_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
        (∀ f : AmbientFace emb.faces,
          f ∉
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                source.boundaryReachability interiorData).peelFaces →
            ∃ e ∈ emb.faceBoundary f.1,
              e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) ∧
        (∀ i :
            Fin
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                source.boundaryReachability interiorData).numCollars,
          0 < i.1 →
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                source.boundaryReachability interiorData).currentOuterBoundary i).Nonempty) ∧
        (∀ {i j :
            Fin
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                source.boundaryReachability interiorData).numCollars},
          0 < i.1 → 0 < j.1 → i ≠ j →
            Disjoint
              ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  source.boundaryReachability interiorData).currentOuterBoundary i)
              ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  source.boundaryReachability interiorData).currentOuterBoundary j))) :
    AdmitsPlanarBoundaryAnnulusConstruction G := by
  rcases hG with
    ⟨emb, source, interiorData, hnonPeelSelectedBoundary,
      hcurrentOuterBoundaryNonempty, hcurrentOuterBoundaryDisjoint⟩
  exact
    admitsPlanarBoundaryAnnulusConstruction_of_exists_boundaryReachabilityData_and_closedWalkEmbeddingData_and_selectedBoundaryArcOnFace_and_interiorDualBoundaryRootAdjDistancePeelData
      ⟨emb, source.boundaryReachability, interiorData, source.closedWalks,
        source.selectedBoundaryArc, hnonPeelSelectedBoundary, hcurrentOuterBoundaryNonempty,
        hcurrentOuterBoundaryDisjoint⟩

/-- Direct theorem-4.9-facing lowering from the explicit closed-walk annulus-boundary source to
the well-founded face-peel witness target, with the existing peeled-parent repair kept explicit.
-/
theorem
    admitsPlanarBoundaryWellFoundedFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_and_parentInPeelFaces
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
        (∀ f : AmbientFace emb.faces,
          f ∉
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                source.boundaryReachability interiorData).peelFaces →
            ∃ e ∈ emb.faceBoundary f.1,
              e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) ∧
        (∀ i :
            Fin
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                source.boundaryReachability interiorData).numCollars,
          0 < i.1 →
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                source.boundaryReachability interiorData).currentOuterBoundary i).Nonempty) ∧
        (∀ {i j :
            Fin
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                source.boundaryReachability interiorData).numCollars},
          0 < i.1 → 0 < j.1 → i ≠ j →
            Disjoint
              ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  source.boundaryReachability interiorData).currentOuterBoundary i)
              ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  source.boundaryReachability interiorData).currentOuterBoundary j)) ∧
        (∀ g ∈ interiorData.peelFaces,
          ∃ p ∈ interiorData.peelFaces,
            parentTowardsRoot
                (interiorDualSpanningForest emb.faceBoundary emb.faces)
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces interiorData.roots
                  interiorData.hcoverRoots interiorData.hsepRoots)
                g = some p)) :
    AdmitsPlanarBoundaryWellFoundedFacePeelWitnessData G := by
  rcases hG with
    ⟨emb, source, interiorData, hnonPeelSelectedBoundary,
      hcurrentOuterBoundaryNonempty, hcurrentOuterBoundaryDisjoint, hparent⟩
  exact
    admitsPlanarBoundaryWellFoundedFacePeelWitnessData_of_exists_boundaryReachabilityData_and_closedWalkEmbeddingData_and_selectedBoundaryArcOnFace_and_interiorDualBoundaryRootAdjDistancePeelData_and_parentInPeelFaces
      ⟨emb, source.boundaryReachability, interiorData, source.closedWalks,
        source.selectedBoundaryArc, hnonPeelSelectedBoundary, hcurrentOuterBoundaryNonempty,
        hcurrentOuterBoundaryDisjoint, hparent⟩

/-- Annulus-source version of the route-facing annihilator theorem. Orthogonality to the
Definition 4.8 Kempe-closure generator family supplies the local face-generator equations used by
the parent-oriented annulus peel. -/
theorem
    zero_on_allEdges_of_exists_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_and_parentInPeelFaces_of_annihilatesKempeClosureGeneratorFamily
    {G : SimpleGraph V}
    (C₀ C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C)
    (hC : C ∈ G.EdgeKempeClosure C₀) (z : G.edgeSet → Color)
    (hdata : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _ : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
        (∀ g ∈ interiorData.peelFaces,
          ∃ p ∈ interiorData.peelFaces,
            parentTowardsRoot
                (interiorDualSpanningForest emb.faceBoundary emb.faces)
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces interiorData.roots
                  interiorData.hcoverRoots interiorData.hsepRoots)
                g = some p) ∧
        (∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0) ∧
        AnnihilatesKempeClosureGeneratorFamily emb.faceBoundary C₀ z) :
    ∀ e, z e = 0 := by
  rcases hdata with ⟨emb, source, interiorData, hparent, hzeroBoundary, hgen⟩
  let data :=
    planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
      source.boundaryReachability interiorData
  exact
    zero_on_allEdges_of_exists_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_and_parentInPeelFaces
      (C := C) (htait := htait) (z := z)
      ⟨emb, source.boundaryReachability, interiorData, hparent, hzeroBoundary, by
        intro f hf γ hγ0 hγne
        simpa [data] using
          localOrthogonality_of_annihilatesKempeClosureGeneratorFamily
            (faceBoundary := emb.faceBoundary) (hC := hC) hgen
            (f := f.1) (e := data.witnessEdge f) (htait (data.witnessEdge f))
            γ hγ0 hγne⟩

/-- Ground-up annulus annihilator route from the honest closed-walk source together with a
same-embedding weak annulus collar geometry. This bypasses the interior-dual package entirely:
once the explicit annulus geometry itself is available on the source embedding, the direct
annulus-collar annihilator theorem finishes the Step 2 vanishing argument. -/
theorem
    admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_direct
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
        Nonempty (PlanarBoundaryAnnulusCollarGeometry emb)) :
    AdmitsPlanarBoundaryCollarLayerFacePeelWitnessData G := by
  rcases hG with ⟨emb, _, ⟨data⟩⟩
  exact ⟨emb, ⟨data.toPlanarBoundaryCollarLayerFacePeelWitnessData⟩⟩

/-- The honest closed-walk annulus-boundary source shell reaches the boundary-aware
height-ordered witness-cover surface as soon as the same embedding carries annulus collar
geometry. This isolates the remaining route burden to constructing the geometric shell itself. -/
theorem
    admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_direct
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
        Nonempty (PlanarBoundaryAnnulusCollarGeometry emb)) :
    AdmitsPlanarBoundaryHeightOrderedFacePeelWitnessData G := by
  rcases hG with ⟨emb, _, ⟨data⟩⟩
  exact ⟨emb, ⟨data.toPlanarBoundaryHeightOrderedFacePeelWitnessData⟩⟩

/-- Direct same-embedding annulus-geometry construction from the honest closed-walk source plus a
canonical one-collar facewise witness choice on the source boundary split. This isolates a
concrete upstream geometric burden: it is enough to choose, for each ambient face, one boundary
edge covering all interior edges such that every non-witness edge already lies on the two ambient
annulus boundaries. The canonical decomposition then upgrades automatically to weak collar
geometry. -/
theorem
    admitsPlanarBoundaryAnnulusCollarGeometry_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_direct
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        Nonempty
          (PlanarBoundaryCanonicalWitnessChoice
            source.toPlanarBoundaryAnnulusBoundaryData)) :
    AdmitsPlanarBoundaryAnnulusCollarGeometry G := by
  rcases hG with ⟨emb, source, ⟨data⟩⟩
  exact
    admitsPlanarBoundaryAnnulusCollarGeometry_of_admitsPlanarBoundaryAnnulusWitnessAssignment
      ⟨emb,
        planarBoundaryAnnulusDecomposition_of_boundaryData
          source.toPlanarBoundaryAnnulusBoundaryData,
        ⟨data.toPlanarBoundaryAnnulusWitnessAssignment⟩⟩

/-- Adding the repaired witness-on-current-boundary placement to the same-embedding annulus
collar geometry lands the honest closed-walk source directly on the well-founded peel-witness
surface. This is the geometric endpoint needed for the repaired theorem-4.9 route. -/
theorem
    admitsPlanarBoundaryWellFoundedFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_witnessOnCurrentBoundary_direct
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
        ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
          data.WitnessOnCurrentBoundary) :
    AdmitsPlanarBoundaryWellFoundedFacePeelWitnessData G := by
  rcases hG with ⟨emb, _, data, hdata⟩
  exact
    admitsPlanarBoundaryWellFoundedFacePeelWitnessData_of_exists_planarBoundaryAnnulusCollarGeometry_and_witnessOnCurrentBoundary
      ⟨emb, data, hdata⟩

/-- Ground-up annulus annihilator route from the honest closed-walk source together with a
same-embedding weak annulus collar geometry. This bypasses the interior-dual package entirely:
once the explicit annulus geometry itself is available on the source embedding, the direct
annulus-collar annihilator theorem finishes the Step 2 vanishing argument. -/
theorem
    zero_on_allEdges_of_exists_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_direct_of_annihilatesKempeClosureGeneratorFamily
    {G : SimpleGraph V}
    (C₀ C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C)
    (hC : C ∈ G.EdgeKempeClosure C₀) (z : G.edgeSet → Color)
    (hdata : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _ : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _ : PlanarBoundaryAnnulusCollarGeometry emb,
        (∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0) ∧
        AnnihilatesKempeClosureGeneratorFamily emb.faceBoundary C₀ z) :
    ∀ e, z e = 0 := by
  rcases hdata with ⟨emb, _source, data, hzeroBoundary, hgen⟩
  exact
    zero_on_allEdges_of_planarBoundaryAnnulusCollarGeometry
      (emb := emb) (C := C) (htait := htait) (z := z) (data := data)
      (hzeroBoundary := hzeroBoundary) (horth := by
        intro i f hf γ hγ0 hγne
        simpa using
          localOrthogonality_of_annihilatesKempeClosureGeneratorFamily
            (faceBoundary := emb.faceBoundary) (hC := hC) hgen
            (f := f.1) (e := data.witnessEdge f) (htait (data.witnessEdge f))
            γ hγ0 hγne)

/-- Ground-up annulus annihilator route from the honest closed-walk source together with
same-embedding boundary-aware height-ordered witness-cover data. This moves the algebraic Step 2
boundary earlier than explicit annulus geometry: once the source embedding already carries the
height-sorted witness-cover package, the global vanishing argument is automatic. -/
theorem
    zero_on_allEdges_of_exists_closedWalkAnnulusBoundarySource_and_heightOrderedFacePeelWitnessData_direct_of_annihilatesKempeClosureGeneratorFamily
    {G : SimpleGraph V}
    (C₀ C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C)
    (hC : C ∈ G.EdgeKempeClosure C₀) (z : G.edgeSet → Color)
    (hdata : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _ : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _ : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        (∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0) ∧
        AnnihilatesKempeClosureGeneratorFamily emb.faceBoundary C₀ z) :
    ∀ e, z e = 0 := by
  rcases hdata with ⟨emb, _source, data, hzeroBoundary, hgen⟩
  exact
    zero_on_allEdges_of_planarBoundaryHeightOrderedFacePeelWitnessData
      (emb := emb) (C := C) (htait := htait) (z := z) (data := data)
      (hzeroBoundary := hzeroBoundary) (horth := by
        intro f hf γ hγ0 hγne
        simpa using
          localOrthogonality_of_annihilatesKempeClosureGeneratorFamily
            (faceBoundary := emb.faceBoundary) (hC := hC) hgen
            (f := f.1) (e := data.witnessEdge f) (htait (data.witnessEdge f))
            γ hγ0 hγne)

/-- Ground-up annulus annihilator route from the honest closed-walk source together with
same-embedding finite collar-layer witness-cover data. This is the paper-facing finite-collar
version of the previous theorem: once the source shell reaches a layered witness package, no
explicit annulus-geometry bookkeeping remains in the vanishing proof. -/
theorem
    zero_on_allEdges_of_exists_closedWalkAnnulusBoundarySource_and_collarLayerFacePeelWitnessData_direct_of_annihilatesKempeClosureGeneratorFamily
    {G : SimpleGraph V}
    (C₀ C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C)
    (hC : C ∈ G.EdgeKempeClosure C₀) (z : G.edgeSet → Color)
    (hdata : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _ : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _ : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        (∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0) ∧
        AnnihilatesKempeClosureGeneratorFamily emb.faceBoundary C₀ z) :
    ∀ e, z e = 0 := by
  rcases hdata with ⟨emb, _source, data, hzeroBoundary, hgen⟩
  exact
    zero_on_allEdges_of_planarBoundaryCollarLayerFacePeelWitnessData
      (emb := emb) (C := C) (htait := htait) (z := z) (data := data)
      (hzeroBoundary := hzeroBoundary) (horth := by
        intro i f hf γ hγ0 hγne
        simpa using
          localOrthogonality_of_annihilatesKempeClosureGeneratorFamily
            (faceBoundary := emb.faceBoundary) (hC := hC) hgen
            (f := f.1) (e := data.witnessEdge f) (htait (data.witnessEdge f))
            γ hγ0 hγne)

/-- Direct theorem-4.9 synthesis endpoint from the honest closed-walk annulus-boundary source
plus same-embedding weak annulus collar geometry. No previous-boundary witness placement,
parent-orientation, or interior-dual package remains once this geometric shell is available. -/
theorem
    exists_theorem49BoundaryRootSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
        Nonempty (PlanarBoundaryAnnulusCollarGeometry emb))
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases hG with ⟨emb, ⟨_source⟩, ⟨data⟩⟩
  exact ⟨emb,
    theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusCollarGeometry
      (G := G) data C₀ hC₀⟩

/-- Direct theorem-4.9 synthesis endpoint from the honest closed-walk annulus-boundary source
plus same-embedding boundary-aware height-ordered witness-cover data. This moves the positive
route boundary earlier than explicit annulus remainder bookkeeping: once the source embedding
carries a height-sorted witness-cover package, the theorem-4.9 synthesis is automatic. -/
theorem
    exists_theorem49BoundaryRootSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_heightOrderedFacePeelWitnessData_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
        Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb))
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases hG with ⟨emb, ⟨_source⟩, ⟨data⟩⟩
  exact ⟨emb,
    theorem49BoundaryRootSynthesis_of_planarBoundaryHeightOrderedFacePeelWitnessData
      (G := G) data C₀ hC₀⟩

/-- Direct theorem-4.9 synthesis endpoint from the honest closed-walk annulus-boundary source
plus same-embedding finite collar-layer witness-cover data. This is earlier than the explicit
remainder and annulus-decomposition packages: the source shell only needs the finite collar-layer
peeling interface itself. -/
theorem
    exists_theorem49BoundaryRootSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_collarLayerFacePeelWitnessData_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
        Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb))
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases hG with ⟨emb, ⟨_source⟩, ⟨data⟩⟩
  exact ⟨emb,
    theorem49BoundaryRootSynthesis_of_planarBoundaryCollarLayerFacePeelWitnessData
      (G := G) data C₀ hC₀⟩

/-- Direct theorem-4.9 synthesis endpoint from the honest closed-walk annulus-boundary source
plus a same-embedding split annulus decomposition with witness ownership. This moves the route
boundary one shell earlier than bundled collar geometry: once the source embedding carries pure
annulus geometry together with witness-edge ownership, no further theorem-4.9 algebra remains. -/
theorem
    exists_theorem49BoundaryRootSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_annulusWitnessAssignment_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
        ∃ decomp : PlanarBoundaryAnnulusDecomposition emb,
          Nonempty (PlanarBoundaryAnnulusWitnessAssignment decomp))
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases hG with ⟨emb, ⟨_source⟩, decomp, ⟨data⟩⟩
  exact ⟨emb,
    theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusWitnessAssignment
      (G := G) data C₀ hC₀⟩

/-- Direct theorem-4.9 synthesis endpoint from the honest closed-walk annulus-boundary source
plus a canonical facewise witness choice on the source boundary split.  The canonical one-collar
decomposition extracted from the source boundary data supplies the split annulus witness
assignment consumed by the synthesis layer. -/
theorem
    exists_theorem49BoundaryRootSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        Nonempty
          (PlanarBoundaryCanonicalWitnessChoice
            source.toPlanarBoundaryAnnulusBoundaryData))
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases hG with ⟨emb, _source, ⟨data⟩⟩
  exact ⟨emb,
    theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusWitnessAssignment
      (G := G) data.toPlanarBoundaryAnnulusWitnessAssignment C₀ hC₀⟩

/-- Non-vacuous theorem-4.9 synthesis from canonical facewise witness choice on a fixed honest
closed-walk source.  The only extra datum beyond the synthesis route is nonemptiness of the
selected-boundary-purified interior-edge endpoint carrier. -/
theorem
    theorem49BoundaryRootNonemptySynthesis_of_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hchoice :
      Nonempty
        (PlanarBoundaryCanonicalWitnessChoice
          source.toPlanarBoundaryAnnulusBoundaryData))
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Theorem49BoundaryRootNonemptySynthesis emb C₀ := by
  rcases hchoice with ⟨choice⟩
  exact
    { synthesis :=
        theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusWitnessAssignment
          (G := G) choice.toPlanarBoundaryAnnulusWitnessAssignment C₀ hC₀
      carrier_nonempty := hCarrier }

/-- Graph-level non-vacuous theorem-4.9 endpoint from an honest closed-walk source with canonical
witness choice and a nonempty purified endpoint carrier. -/
theorem
    exists_theorem49BoundaryRootNonemptySynthesis_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_with_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        Nonempty
          (PlanarBoundaryCanonicalWitnessChoice
            source.toPlanarBoundaryAnnulusBoundaryData) ∧
          (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptySynthesis emb C₀ := by
  rcases hG with ⟨emb, source, hchoice, hCarrier⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptySynthesis_of_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_direct
        source hchoice hCarrier C₀ hC₀⟩

/-- Canonical facewise witness choice on the honest source boundary split reaches the repaired
previous-boundary witness surface through the direct canonical-choice repair. -/
theorem
    admitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_direct
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        Nonempty
          (PlanarBoundaryCanonicalWitnessChoice
            source.toPlanarBoundaryAnnulusBoundaryData)) :
    AdmitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry G := by
  rcases
    exists_planarBoundaryAnnulusPreviousBoundaryWitnessGeometry_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice
      hG with
    ⟨emb, _source, hgeom⟩
  exact ⟨emb, hgeom⟩

/-- Height-ordered witness data follows from canonical source witness choice through the repaired
one-collar previous-boundary surface. -/
theorem
    admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_direct
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        Nonempty
          (PlanarBoundaryCanonicalWitnessChoice
            source.toPlanarBoundaryAnnulusBoundaryData)) :
    AdmitsPlanarBoundaryHeightOrderedFacePeelWitnessData G :=
  admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_of_admitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry
    (admitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_direct
      hG)

/-- Collar-layer witness data follows from canonical source witness choice through the same
repaired one-collar previous-boundary surface. -/
theorem
    admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_direct
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        Nonempty
          (PlanarBoundaryCanonicalWitnessChoice
            source.toPlanarBoundaryAnnulusBoundaryData)) :
    AdmitsPlanarBoundaryCollarLayerFacePeelWitnessData G :=
  admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_admitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry
    (admitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_direct
      hG)

/-- Canonical Definition 4.8 generator-subspace spanning from canonical source witness choice,
via the height-ordered repaired-witness route. -/
theorem
    exists_theorem49_kempeGeneratorSubspace_spanning_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_heightOrdered_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        Nonempty
          (PlanarBoundaryCanonicalWitnessChoice
            source.toPlanarBoundaryAnnulusBoundaryData))
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (differenceSubspaceOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryHeightOrderedFacePeelWitnessData emb → Submodule F2 (G.edgeSet → Color))
    (hle : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        kempeClosureGeneratorSubspace emb.faceBoundary C₀ ≤ differenceSubspaceOf emb data)
    (hboundary : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        ∀ ⦃z : G.edgeSet → Color⦄,
          z ∈ differenceSubspaceOf emb data →
            ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        kempeClosureGeneratorSubspace emb.faceBoundary C₀ = differenceSubspaceOf emb data := by
  exact
    exists_theorem49_kempeGeneratorSubspace_spanning_of_admitsPlanarBoundaryHeightOrderedFacePeelWitnessData
      (admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_direct
        hG)
      C₀ hC₀ differenceSubspaceOf hle hboundary

/-- Collar-layer version of the canonical-generator spanning bridge from canonical source
witness choice. -/
theorem
    exists_theorem49_kempeGeneratorSubspace_spanning_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_collarLayer_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        Nonempty
          (PlanarBoundaryCanonicalWitnessChoice
            source.toPlanarBoundaryAnnulusBoundaryData))
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (differenceSubspaceOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryCollarLayerFacePeelWitnessData emb → Submodule F2 (G.edgeSet → Color))
    (hle : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        kempeClosureGeneratorSubspace emb.faceBoundary C₀ ≤ differenceSubspaceOf emb data)
    (hboundary : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        ∀ ⦃z : G.edgeSet → Color⦄,
          z ∈ differenceSubspaceOf emb data →
            ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        kempeClosureGeneratorSubspace emb.faceBoundary C₀ = differenceSubspaceOf emb data := by
  exact
    exists_theorem49_kempeGeneratorSubspace_spanning_of_admitsPlanarBoundaryCollarLayerFacePeelWitnessData
      (admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_direct
        hG)
      C₀ hC₀ differenceSubspaceOf hle hboundary

/-- Canonical facewise witness choice from honest closed-walk source data plus the local
cardinality form of the at-most-one-interior-edge premise.

The hypotheses match the finite regression packages: a fallback boundary edge is available on
each face, each face boundary contains at most one interior edge, and every non-interior
face-boundary edge already lies on the source's ambient annulus boundary. -/
theorem
    exists_planarBoundaryCanonicalWitnessChoice_of_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (fallbackEdge : AmbientFace emb.faces → G.edgeSet)
    (hfallback : ∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1)
    (h_at_most_one_interior :
      ∀ f : AmbientFace emb.faces,
        ((emb.faceBoundary f.1).filter
            (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
          (1 : ℕ))
    (h_nonInterior_on_ambient :
      ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
        e ∈ emb.faceBoundary f.1 →
          e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
          e ∈
            source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
              source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary) :
    Nonempty
      (PlanarBoundaryCanonicalWitnessChoice source.toPlanarBoundaryAnnulusBoundaryData) := by
  classical
  have huniqueInterior :
      ∀ (f : AmbientFace emb.faces) {e₁ e₂ : G.edgeSet},
        e₁ ∈ emb.faceBoundary f.1 →
          e₂ ∈ emb.faceBoundary f.1 →
            e₁ ∈ interiorEdgeSupport emb.faceBoundary emb.faces →
              e₂ ∈ interiorEdgeSupport emb.faceBoundary emb.faces →
                e₁ = e₂ := by
    intro f e₁ e₂ he₁ he₂ hi₁ hi₂
    by_contra hne
    have he₁Filter :
        e₁ ∈ (emb.faceBoundary f.1).filter
          (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces) :=
      Finset.mem_filter.2 ⟨he₁, hi₁⟩
    have he₂Filter :
        e₂ ∈ (emb.faceBoundary f.1).filter
          (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces) :=
      Finset.mem_filter.2 ⟨he₂, hi₂⟩
    have hgt :
        1 <
          ((emb.faceBoundary f.1).filter
            (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card :=
      Finset.one_lt_card.2 ⟨e₁, he₁Filter, e₂, he₂Filter, hne⟩
    exact Nat.not_lt_of_ge (h_at_most_one_interior f) hgt
  exact
    ⟨PlanarBoundaryCanonicalWitnessChoice.of_atMostOneInteriorEdgePerFace
      (boundaryData := source.toPlanarBoundaryAnnulusBoundaryData)
      fallbackEdge hfallback huniqueInterior h_nonInterior_on_ambient⟩

/-- Honest-source version of the local at-most-one criterion. The closed walks provide the
fallback boundary edge on every face, while the annulus boundary split puts every non-interior
face-boundary edge on the outer or inner ambient boundary. Thus the only remaining local input is
the facewise cardinality bound on interior boundary edges. -/
theorem
    exists_planarBoundaryCanonicalWitnessChoice_of_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (h_at_most_one_interior :
      ∀ f : AmbientFace emb.faces,
        ((emb.faceBoundary f.1).filter
            (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
          (1 : ℕ)) :
    Nonempty
      (PlanarBoundaryCanonicalWitnessChoice source.toPlanarBoundaryAnnulusBoundaryData) := by
  exact
    exists_planarBoundaryCanonicalWitnessChoice_of_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace
      source source.fallbackEdge source.fallbackEdge_mem_faceBoundary h_at_most_one_interior
      (by
        intro f e heFace heNotInterior
        exact
          source.toPlanarBoundaryAnnulusBoundaryData
            |>.mem_outerAmbientBoundary_union_innerAmbientBoundary_of_mem_faceBoundary_of_not_mem_interiorEdgeSupport
              heFace heNotInterior)

/-- The honest closed-walk annulus source plus canonical witness choice already reaches the split
annulus witness-ownership surface itself, before any theorem-4.9 synthesis packaging. -/
theorem
    admitsPlanarBoundaryAnnulusWitnessAssignment_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_direct
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        Nonempty
          (PlanarBoundaryCanonicalWitnessChoice
            source.toPlanarBoundaryAnnulusBoundaryData)) :
    AdmitsPlanarBoundaryAnnulusWitnessAssignment G := by
  rcases hG with ⟨emb, source, ⟨choice⟩⟩
  exact
    ⟨emb,
      planarBoundaryAnnulusDecomposition_of_boundaryData
        source.toPlanarBoundaryAnnulusBoundaryData,
      ⟨choice.toPlanarBoundaryAnnulusWitnessAssignment⟩⟩

/-- The exact source-side facewise at-most-one condition already reaches the split annulus
witness-ownership surface.  The closed walks provide the fallback edge and the annulus boundary
split provides the non-interior boundary-rest clause, so the only remaining local burden is the
facewise cardinality bound itself. -/
theorem
    admitsPlanarBoundaryAnnulusWitnessAssignment_of_exists_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge_direct
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∀ f : AmbientFace emb.faces,
          ((emb.faceBoundary f.1).filter
              (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
            (1 : ℕ)) :
    AdmitsPlanarBoundaryAnnulusWitnessAssignment G := by
  rcases hG with ⟨emb, source, hAtMost⟩
  rcases
    exists_planarBoundaryCanonicalWitnessChoice_of_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge
      source hAtMost with
    ⟨choice⟩
  exact
    admitsPlanarBoundaryAnnulusWitnessAssignment_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_direct
      ⟨emb, source, ⟨choice⟩⟩

/-- Direct theorem-4.9 synthesis endpoint from an honest closed-walk annulus-boundary source
whose face-local interior-edge data satisfies the at-most-one sufficient condition.  This exposes
the local criterion as an endpoint theorem, rather than stopping at canonical witness choice or
weak collar geometry. -/
theorem
    exists_theorem49BoundaryRootSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
          (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
            (∀ f : AmbientFace emb.faces,
              ((emb.faceBoundary f.1).filter
                  (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                (1 : ℕ)) ∧
              ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
                e ∈ emb.faceBoundary f.1 →
                  e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                  e ∈
                    source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                      source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases hG with ⟨emb, source, fallbackEdge, hfallback, hatMost, hboundaryRest⟩
  exact
    exists_theorem49BoundaryRootSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_direct
      ⟨emb, source,
        exists_planarBoundaryCanonicalWitnessChoice_of_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace
          source fallbackEdge hfallback hatMost hboundaryRest⟩ C₀ hC₀

/-- Direct theorem-4.9 synthesis endpoint from an honest closed-walk annulus-boundary source once
the facewise interior boundary edge set has cardinality at most one. Compared with the older
at-most-one wrapper, the honest source itself supplies fallback edges and the non-interior
boundary-rest clause. -/
theorem
    exists_theorem49BoundaryRootSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∀ f : AmbientFace emb.faces,
          ((emb.faceBoundary f.1).filter
              (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
            (1 : ℕ))
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases hG with ⟨emb, source, hatMost⟩
  exact
    exists_theorem49BoundaryRootSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_direct
      ⟨emb, source,
        exists_planarBoundaryCanonicalWitnessChoice_of_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge
          source hatMost⟩ C₀ hC₀

/-- The local cardinality form of the at-most-one source criterion reaches the repaired
previous-boundary witness geometry.  The canonical witness choice builds a one-collar geometry,
and the previous-boundary obligation is vacuous for a single collar. -/
theorem
    admitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_direct
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
          (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
            (∀ f : AmbientFace emb.faces,
              ((emb.faceBoundary f.1).filter
                  (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                (1 : ℕ)) ∧
              ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
                e ∈ emb.faceBoundary f.1 →
                  e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                  e ∈
                    source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                      source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary) :
    AdmitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry G := by
  rcases hG with ⟨emb, source, fallbackEdge, hfallback, hatMost, hboundaryRest⟩
  rcases
    exists_planarBoundaryCanonicalWitnessChoice_of_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace
      source fallbackEdge hfallback hatMost hboundaryRest with
    ⟨choice⟩
  exact
    ⟨emb,
      ⟨choice.toPlanarBoundaryAnnulusCollarGeometry
        |>.toPreviousBoundaryWitnessGeometry_of_numCollars_eq_one
          choice.toPlanarBoundaryAnnulusCollarGeometry_numCollars⟩⟩

/-- Honest-source version of the repaired previous-boundary witness criterion. Closed-walk
nonemptiness and the annulus boundary split discharge the fallback and boundary-rest fields, so
the remaining local assumption is only the facewise at-most-one interior-edge bound. -/
theorem
    admitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry_of_exists_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge_direct
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∀ f : AmbientFace emb.faces,
          ((emb.faceBoundary f.1).filter
              (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
            (1 : ℕ)) :
    AdmitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry G := by
  rcases hG with ⟨emb, source, hatMost⟩
  rcases
    exists_planarBoundaryCanonicalWitnessChoice_of_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge
      source hatMost with
    ⟨choice⟩
  exact
    ⟨emb,
      ⟨choice.toPlanarBoundaryAnnulusCollarGeometry
        |>.toPreviousBoundaryWitnessGeometry_of_numCollars_eq_one
          choice.toPlanarBoundaryAnnulusCollarGeometry_numCollars⟩⟩

/-- Height-ordered witness data follows from the at-most-one honest-source criterion through the
repaired one-collar annulus surface. -/
theorem
    admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_direct
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
          (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
            (∀ f : AmbientFace emb.faces,
              ((emb.faceBoundary f.1).filter
                  (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                (1 : ℕ)) ∧
              ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
                e ∈ emb.faceBoundary f.1 →
                  e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                  e ∈
                    source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                      source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary) :
    AdmitsPlanarBoundaryHeightOrderedFacePeelWitnessData G :=
  admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_of_admitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry
    (admitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_direct
      hG)

/-- Collar-layer witness data follows from the same at-most-one honest-source criterion. -/
theorem
    admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_direct
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
          (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
            (∀ f : AmbientFace emb.faces,
              ((emb.faceBoundary f.1).filter
                  (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                (1 : ℕ)) ∧
              ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
                e ∈ emb.faceBoundary f.1 →
                  e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                  e ∈
                    source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                      source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary) :
    AdmitsPlanarBoundaryCollarLayerFacePeelWitnessData G :=
  admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_admitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry
    (admitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_direct
      hG)

/-- Canonical Definition 4.8 generator-subspace spanning from the local at-most-one honest-source
criterion via the height-ordered witness route.  The remaining inputs are exactly the target
subspace, generator containment, and boundary-zero interpretation required by the submodule
duality bridge. -/
theorem
    exists_theorem49_kempeGeneratorSubspace_spanning_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_heightOrdered_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
          (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
            (∀ f : AmbientFace emb.faces,
              ((emb.faceBoundary f.1).filter
                  (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                (1 : ℕ)) ∧
              ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
                e ∈ emb.faceBoundary f.1 →
                  e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                  e ∈
                    source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                      source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (differenceSubspaceOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryHeightOrderedFacePeelWitnessData emb → Submodule F2 (G.edgeSet → Color))
    (hle : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        kempeClosureGeneratorSubspace emb.faceBoundary C₀ ≤ differenceSubspaceOf emb data)
    (hboundary : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        ∀ ⦃z : G.edgeSet → Color⦄,
          z ∈ differenceSubspaceOf emb data →
            ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        kempeClosureGeneratorSubspace emb.faceBoundary C₀ = differenceSubspaceOf emb data := by
  exact
    exists_theorem49_kempeGeneratorSubspace_spanning_of_admitsPlanarBoundaryHeightOrderedFacePeelWitnessData
      (admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_direct
        hG)
      C₀ hC₀ differenceSubspaceOf hle hboundary

/-- Collar-layer version of the direct canonical-generator spanning bridge from the local
at-most-one honest-source criterion. -/
theorem
    exists_theorem49_kempeGeneratorSubspace_spanning_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_collarLayer_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
          (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
            (∀ f : AmbientFace emb.faces,
              ((emb.faceBoundary f.1).filter
                  (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                (1 : ℕ)) ∧
              ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
                e ∈ emb.faceBoundary f.1 →
                  e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                  e ∈
                    source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                      source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (differenceSubspaceOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryCollarLayerFacePeelWitnessData emb → Submodule F2 (G.edgeSet → Color))
    (hle : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        kempeClosureGeneratorSubspace emb.faceBoundary C₀ ≤ differenceSubspaceOf emb data)
    (hboundary : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        ∀ ⦃z : G.edgeSet → Color⦄,
          z ∈ differenceSubspaceOf emb data →
            ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        kempeClosureGeneratorSubspace emb.faceBoundary C₀ = differenceSubspaceOf emb data := by
  exact
    exists_theorem49_kempeGeneratorSubspace_spanning_of_admitsPlanarBoundaryCollarLayerFacePeelWitnessData
      (admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_direct
        hG)
      C₀ hC₀ differenceSubspaceOf hle hboundary

/-- Non-vacuous theorem-4.9 synthesis from the local at-most-one-interior-edge criterion on a
fixed honest closed-walk source.  The added hypothesis is exactly the remaining non-vacuity
burden: the selected-boundary-purified interior-edge endpoint carrier must contain a vertex. -/
theorem
    theorem49BoundaryRootNonemptySynthesis_of_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (fallbackEdge : AmbientFace emb.faces → G.edgeSet)
    (hfallback : ∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1)
    (h_at_most_one_interior :
      ∀ f : AmbientFace emb.faces,
        ((emb.faceBoundary f.1).filter
            (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
          (1 : ℕ))
    (h_nonInterior_on_ambient :
      ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
        e ∈ emb.faceBoundary f.1 →
          e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
          e ∈
            source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
              source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Theorem49BoundaryRootNonemptySynthesis emb C₀ := by
  rcases
    exists_planarBoundaryCanonicalWitnessChoice_of_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace
      source fallbackEdge hfallback h_at_most_one_interior h_nonInterior_on_ambient
    with ⟨choice⟩
  exact
    { synthesis :=
        theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusWitnessAssignment
          (G := G) choice.toPlanarBoundaryAnnulusWitnessAssignment C₀ hC₀
      carrier_nonempty := hCarrier }

/-- Graph-level non-vacuous theorem-4.9 endpoint from an honest closed-walk source satisfying
the local at-most-one-interior-edge criterion and a nonempty purified carrier.  This isolates the
current positive burden: find a Tait-colorable honest source whose local annulus geometry passes
the at-most-one test and whose selected-boundary purification does not delete all interior-edge
endpoints. -/
theorem
    exists_theorem49BoundaryRootNonemptySynthesis_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_with_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
          (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
            (∀ f : AmbientFace emb.faces,
              ((emb.faceBoundary f.1).filter
                  (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                (1 : ℕ)) ∧
              (∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
                e ∈ emb.faceBoundary f.1 →
                  e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                  e ∈
                    source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                      source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary) ∧
                (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptySynthesis emb C₀ := by
  rcases hG with
    ⟨emb, source, fallbackEdge, hfallback, hatMost, hboundaryRest, hCarrier⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptySynthesis_of_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_direct
        source fallbackEdge hfallback hatMost hboundaryRest hCarrier C₀ hC₀⟩

/-- Non-vacuous theorem-4.9 synthesis from an honest closed-walk source whose facewise interior
boundary-edge set has cardinality at most one.  The honest source supplies the fallback edge and
the non-interior boundary-rest clause; the extra hypothesis is the existing nonempty purified
endpoint carrier. -/
theorem
    theorem49BoundaryRootNonemptySynthesis_of_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (h_at_most_one_interior :
      ∀ f : AmbientFace emb.faces,
        ((emb.faceBoundary f.1).filter
            (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
          (1 : ℕ))
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Theorem49BoundaryRootNonemptySynthesis emb C₀ := by
  exact
    theorem49BoundaryRootNonemptySynthesis_of_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_direct
      source source.fallbackEdge source.fallbackEdge_mem_faceBoundary h_at_most_one_interior
      (by
        intro f e heFace heNotInterior
        exact
          source.toPlanarBoundaryAnnulusBoundaryData
            |>.mem_outerAmbientBoundary_union_innerAmbientBoundary_of_mem_faceBoundary_of_not_mem_interiorEdgeSupport
              heFace heNotInterior)
      hCarrier C₀ hC₀

/-- Graph-level non-vacuous theorem-4.9 endpoint from an honest closed-walk source with the
facewise cardinal at-most-one condition and a nonempty purified endpoint carrier, with no
caller-supplied fallback or boundary-rest data. -/
theorem
    exists_theorem49BoundaryRootNonemptySynthesis_of_exists_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge_with_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∀ f : AmbientFace emb.faces,
          ((emb.faceBoundary f.1).filter
              (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
            (1 : ℕ)) ∧
          (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptySynthesis emb C₀ := by
  rcases hG with ⟨emb, source, hatMost, hCarrier⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptySynthesis_of_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge_direct
        source hatMost hCarrier C₀ hC₀⟩

/-- Direct theorem-4.9 synthesis endpoint from the honest closed-walk annulus-boundary source
plus same-boundary one-collar annulus collar geometry.  The one-collar geometry first yields the
canonical witness choice on the source boundary split; that canonical witness choice then feeds
the split annulus witness-assignment synthesis route. -/
theorem
    exists_theorem49BoundaryRootSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases hG with ⟨emb, source, data, hnum, hboundary⟩
  let choice :
      PlanarBoundaryCanonicalWitnessChoice
        source.toPlanarBoundaryAnnulusBoundaryData :=
    data.toPlanarBoundaryCanonicalWitnessChoice_of_numCollars_eq_one hnum hboundary
  exact ⟨emb,
    theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusWitnessAssignment
      (G := G) choice.toPlanarBoundaryAnnulusWitnessAssignment C₀ hC₀⟩

/-- Non-vacuous theorem-4.9 synthesis from same-boundary one-collar geometry on a fixed honest
closed-walk source.  The one-collar geometry canonically gives the witness choice; nonemptiness
of the purified endpoint carrier is recorded separately. -/
theorem
    theorem49BoundaryRootNonemptySynthesis_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hnum : data.numCollars = 1)
    (hboundary :
      data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
        source.toPlanarBoundaryAnnulusBoundaryData)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Theorem49BoundaryRootNonemptySynthesis emb C₀ := by
  let choice :
      PlanarBoundaryCanonicalWitnessChoice
        source.toPlanarBoundaryAnnulusBoundaryData :=
    data.toPlanarBoundaryCanonicalWitnessChoice_of_numCollars_eq_one hnum hboundary
  exact
    { synthesis :=
        theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusWitnessAssignment
          (G := G) choice.toPlanarBoundaryAnnulusWitnessAssignment C₀ hC₀
      carrier_nonempty := hCarrier }

/-- Graph-level non-vacuous theorem-4.9 endpoint from an honest closed-walk source with
same-boundary one-collar geometry and a nonempty purified endpoint carrier. -/
theorem
    exists_theorem49BoundaryRootNonemptySynthesis_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData ∧
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptySynthesis emb C₀ := by
  rcases hG with ⟨emb, source, data, hnum, hboundary, hCarrier⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptySynthesis_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_direct
        source data hnum hboundary hCarrier C₀ hC₀⟩

/-- Same-boundary one-collar source geometry reaches the repaired previous-boundary witness
surface.  The source-boundary equality is retained in the hypothesis for upstream compatibility;
the repaired witness itself only needs the one-collar count. -/
theorem
    admitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_direct
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) :
    AdmitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry G := by
  rcases hG with ⟨emb, _source, data, hnum, _hboundary⟩
  exact
    admitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry_of_exists_oneCollarAnnulusCollarGeometry
      ⟨emb, data, hnum⟩

/-- Height-ordered witness data follows directly from same-boundary one-collar source geometry
through the repaired previous-boundary surface. -/
theorem
    admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_direct
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) :
    AdmitsPlanarBoundaryHeightOrderedFacePeelWitnessData G :=
  admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_of_admitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry
    (admitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_direct
      hG)

/-- Collar-layer witness data follows directly from same-boundary one-collar source geometry. -/
theorem
    admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_direct
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) :
    AdmitsPlanarBoundaryCollarLayerFacePeelWitnessData G :=
  admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_admitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry
    (admitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_direct
      hG)

/-- Canonical Definition 4.8 generator-subspace spanning from same-boundary one-collar source
geometry, via the height-ordered repaired-witness route. -/
theorem
    exists_theorem49_kempeGeneratorSubspace_spanning_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_heightOrdered_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (differenceSubspaceOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryHeightOrderedFacePeelWitnessData emb → Submodule F2 (G.edgeSet → Color))
    (hle : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        kempeClosureGeneratorSubspace emb.faceBoundary C₀ ≤ differenceSubspaceOf emb data)
    (hboundary : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        ∀ ⦃z : G.edgeSet → Color⦄,
          z ∈ differenceSubspaceOf emb data →
            ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        kempeClosureGeneratorSubspace emb.faceBoundary C₀ = differenceSubspaceOf emb data := by
  exact
    exists_theorem49_kempeGeneratorSubspace_spanning_of_admitsPlanarBoundaryHeightOrderedFacePeelWitnessData
      (admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_direct
        hG)
      C₀ hC₀ differenceSubspaceOf hle hboundary

/-- Collar-layer version of the canonical-generator spanning bridge from same-boundary
one-collar source geometry. -/
theorem
    exists_theorem49_kempeGeneratorSubspace_spanning_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_collarLayer_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (differenceSubspaceOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryCollarLayerFacePeelWitnessData emb → Submodule F2 (G.edgeSet → Color))
    (hle : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        kempeClosureGeneratorSubspace emb.faceBoundary C₀ ≤ differenceSubspaceOf emb data)
    (hboundary : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        ∀ ⦃z : G.edgeSet → Color⦄,
          z ∈ differenceSubspaceOf emb data →
            ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        kempeClosureGeneratorSubspace emb.faceBoundary C₀ = differenceSubspaceOf emb data := by
  exact
    exists_theorem49_kempeGeneratorSubspace_spanning_of_admitsPlanarBoundaryCollarLayerFacePeelWitnessData
      (admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_direct
        hG)
      C₀ hC₀ differenceSubspaceOf hle hboundary

/-- Direct graph-level lowering from successor-based facial dart cycles, same-embedding boundary
reachability, and selected-boundary arc contiguity to the annulus BFS construction target. The
facial closed walks are obtained from the successor-cycle source by the checked lowering in
`PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields`. -/
theorem
    admitsPlanarBoundaryAnnulusConstruction_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∀ f : AmbientFace emb.faces,
          f ∉
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).peelFaces →
            ∃ e ∈ emb.faceBoundary f.1,
              e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) ∧
        (∀ i :
            Fin
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).numCollars,
          0 < i.1 →
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary i).Nonempty) ∧
        (∀ {i j :
            Fin
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).numCollars},
          0 < i.1 → 0 < j.1 → i ≠ j →
            Disjoint
              ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).currentOuterBoundary i)
              ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).currentOuterBoundary j))) :
    AdmitsPlanarBoundaryAnnulusConstruction G := by
  rcases hG with
    ⟨emb, boundaryData, interiorData, dartCycles, hboundaryArc, hnonPeelSelectedBoundary,
      hcurrentOuterBoundaryNonempty, hcurrentOuterBoundaryDisjoint⟩
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    admitsPlanarBoundaryAnnulusConstruction_of_exists_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData
      ⟨emb, source, interiorData, hnonPeelSelectedBoundary, hcurrentOuterBoundaryNonempty,
        hcurrentOuterBoundaryDisjoint⟩

/-- The successor-cycle source reaches the theorem-4.9 well-founded face-peel witness surface
once the existing construction-side frontier/contact obligations and peeled-parent repair are
available on the same embedding. -/
theorem
    admitsPlanarBoundaryWellFoundedFacePeelWitnessData_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootAdjDistancePeelData_and_parentInPeelFaces
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∀ f : AmbientFace emb.faces,
          f ∉
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).peelFaces →
            ∃ e ∈ emb.faceBoundary f.1,
              e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) ∧
        (∀ i :
            Fin
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).numCollars,
          0 < i.1 →
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary i).Nonempty) ∧
        (∀ {i j :
            Fin
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).numCollars},
          0 < i.1 → 0 < j.1 → i ≠ j →
            Disjoint
              ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).currentOuterBoundary i)
              ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).currentOuterBoundary j)) ∧
        (∀ g ∈ interiorData.peelFaces,
          ∃ p ∈ interiorData.peelFaces,
            parentTowardsRoot
                (interiorDualSpanningForest emb.faceBoundary emb.faces)
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces interiorData.roots
                  interiorData.hcoverRoots interiorData.hsepRoots)
                g = some p)) :
    AdmitsPlanarBoundaryWellFoundedFacePeelWitnessData G := by
  rcases hG with
    ⟨emb, boundaryData, interiorData, dartCycles, hboundaryArc, hnonPeelSelectedBoundary,
      hcurrentOuterBoundaryNonempty, hcurrentOuterBoundaryDisjoint, hparent⟩
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    admitsPlanarBoundaryWellFoundedFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_and_parentInPeelFaces
      ⟨emb, source, interiorData, hnonPeelSelectedBoundary, hcurrentOuterBoundaryNonempty,
        hcurrentOuterBoundaryDisjoint, hparent⟩

/-- Route-facing annihilator theorem with the successor-based facial dart-cycle source as the
explicit boundary-walk input. The theorem keeps the true geometric obligations separate:
boundary reachability, selected-boundary contiguity on the induced closed walks, peeled-parent
orientation, boundary vanishing, and annihilation of the Definition 4.8 generator family. -/
theorem
    zero_on_allEdges_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootAdjDistancePeelData_and_parentInPeelFaces_of_annihilatesKempeClosureGeneratorFamily
    {G : SimpleGraph V}
    (C₀ C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C)
    (hC : C ∈ G.EdgeKempeClosure C₀) (z : G.edgeSet → Color)
    (hdata : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _ : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∀ g ∈ interiorData.peelFaces,
          ∃ p ∈ interiorData.peelFaces,
            parentTowardsRoot
                (interiorDualSpanningForest emb.faceBoundary emb.faces)
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces interiorData.roots
                  interiorData.hcoverRoots interiorData.hsepRoots)
                g = some p) ∧
        (∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0) ∧
        AnnihilatesKempeClosureGeneratorFamily emb.faceBoundary C₀ z) :
    ∀ e, z e = 0 := by
  rcases hdata with
    ⟨emb, boundaryData, interiorData, dartCycles, hboundaryArc, hparent, hzeroBoundary, hgen⟩
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    zero_on_allEdges_of_exists_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_and_parentInPeelFaces_of_annihilatesKempeClosureGeneratorFamily
      (C₀ := C₀) (C := C) (htait := htait) (hC := hC) (z := z)
      ⟨emb, source, interiorData, hparent, hzeroBoundary, hgen⟩

/-- Root-distance route from the explicit closed-walk annulus-boundary source. The source is
used only for its same-embedding boundary reachability field here; the facial closed walks and
selected-boundary arc fields remain available to downstream consumers without restating the older
shifted-frontier obligations on this theorem surface. -/
theorem
    admitsPlanarBoundaryAnnulusConstruction_of_exists_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_direct
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
        Nonempty (InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)) :
    AdmitsPlanarBoundaryAnnulusConstruction G := by
  rcases hG with ⟨emb, ⟨source⟩, ⟨interiorData⟩⟩
  exact
    admitsPlanarBoundaryAnnulusConstruction_of_exists_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
      ⟨emb, ⟨source.boundaryReachability⟩, ⟨interiorData⟩⟩

/-- Same-embedding parent-witness orientation theorem on the honest closed-walk annulus-boundary
source shell. The source contributes the required boundary-reachability data, and the
root-distance annulus construction supplies the orientation directly from the generic rooted
interior-dual peel data. -/
theorem
    parentWitnessOrientation_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_rootDistance
    {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) :
    (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_rootDistance
      source.boundaryReachability interiorData).ParentWitnessOrientation :=
  parentWitnessOrientation_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_rootDistance
    source.boundaryReachability interiorData

/-- Fixed-embedding well-founded witness-cover data from the honest closed-walk annulus-boundary
source and generic boundary-root interior-dual adjacency-distance data.  This packages the
root-distance annulus construction and its parent-witness orientation as an explicit acyclic
parent witness-cover datum on the original source embedding. -/
noncomputable def
    planarBoundaryWellFoundedFacePeelWitnessData_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) :
    PlanarBoundaryWellFoundedFacePeelWitnessData emb :=
  (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_rootDistance
    source.boundaryReachability interiorData).toPlanarBoundaryWellFoundedFacePeelWitnessData_of_parentWitness
      (parentWitnessOrientation_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_rootDistance
        source interiorData)

/-- Fixed-embedding height-ordered witness-cover data from the honest closed-walk source plus
generic boundary-root interior-dual adjacency-distance data.  This is the source-facing
acyclic witness-cover object itself: the root-distance construction first supplies a
well-founded parent witness, and the canonical parent-height rank turns that parent order into
the height-ordered witness-cover interface. -/
noncomputable def
    planarBoundaryHeightOrderedFacePeelWitnessData_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) :
    PlanarBoundaryHeightOrderedFacePeelWitnessData emb :=
  (planarBoundaryWellFoundedFacePeelWitnessData_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData
    source interiorData).toPlanarBoundaryHeightOrderedFacePeelWitnessData

/-- Graph-level parent-witness orientation theorem on the honest closed-walk annulus-boundary
source shell. This exposes the repaired route at the actual annulus-construction orientation
surface, one layer earlier than the well-founded peel witness target. -/
theorem
    admitsPlanarBoundaryAnnulusConstructionParentWitnessOrientation_of_exists_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_direct
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
        Nonempty (InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)) :
    AdmitsPlanarBoundaryAnnulusConstructionParentWitnessOrientation G := by
  rcases hG with ⟨emb, ⟨source⟩, ⟨interiorData⟩⟩
  refine
    ⟨emb,
      planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_rootDistance
        source.boundaryReachability interiorData,
      ?_⟩
  exact
    parentWitnessOrientation_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_rootDistance
      source interiorData

/-- Root-distance theorem-4.9 continuation from the explicit closed-walk annulus-boundary source.
This records that the parent-orientation repair is already supplied by the root-distance
construction once the same embedding carries boundary reachability and interior-dual
boundary-root adjacency-distance data. -/
theorem
    admitsPlanarBoundaryWellFoundedFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_direct
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
        Nonempty (InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)) :
    AdmitsPlanarBoundaryWellFoundedFacePeelWitnessData G := by
  exact
    admitsPlanarBoundaryWellFoundedFacePeelWitnessData_of_admitsPlanarBoundaryAnnulusConstructionParentWitnessOrientation
      (admitsPlanarBoundaryAnnulusConstructionParentWitnessOrientation_of_exists_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_direct
        hG)

/-- Source-level acyclic witness-cover theorem: an honest closed-walk annulus-boundary source plus
generic boundary-root interior-dual adjacency-distance data directly supplies height-ordered
witness-cover data on the same embedding.  Thus the remaining source-level gap is upstream of
this theorem: construct the interior-dual boundary-root distance data, or an equivalent
cycle-breaking parent witness, from the geometric source hypotheses. -/
theorem
    admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_direct
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
        Nonempty (InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)) :
    AdmitsPlanarBoundaryHeightOrderedFacePeelWitnessData G := by
  rcases hG with ⟨emb, ⟨source⟩, ⟨interiorData⟩⟩
  exact
    ⟨emb,
      ⟨planarBoundaryHeightOrderedFacePeelWitnessData_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData
        source interiorData⟩⟩

/-- The honest closed-walk annulus-boundary source shell already reaches the boundary-aware
attached certificate endpoint as soon as the same embedding carries the generic boundary-root
interior-dual adjacency-distance data. This now factors through the root-distance
parent-orientation shell and the induced certificate surface. -/
theorem
    admitsPlanarBoundaryAttachedRootedFacePeelCertificate_of_exists_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_direct
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
        Nonempty (InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)) :
    AdmitsPlanarBoundaryAttachedRootedFacePeelCertificate G := by
  exact
    admitsPlanarBoundaryAttachedRootedFacePeelCertificate_of_admitsPlanarBoundaryAnnulusConstructionParentWitnessOrientation
      (admitsPlanarBoundaryAnnulusConstructionParentWitnessOrientation_of_exists_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_direct
        hG)

/-- Direct boundary-root synthesis endpoint from the honest closed-walk annulus-boundary source
shell. The explicit boundary-order data is preserved on the theorem surface, but the actual
synthesis conclusion is now obtained through the attached certificate surface, reflecting that no
further theorem-4.9 algebra remains once that certificate data exists. -/
theorem
    exists_theorem49BoundaryRootSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
        Nonempty (InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary))
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ :=
  exists_theorem49BoundaryRootSynthesis_of_admitsPlanarBoundaryAttachedRootedFacePeelCertificate
    (admitsPlanarBoundaryAttachedRootedFacePeelCertificate_of_exists_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_direct
      hG)
    C₀ hC₀

/-- Honest closed-walk annulus-boundary source route to the repaired non-vacuous outer-root
synthesis surface. Besides the source and live interior-dual data, the theorem asks only for the
geometric root-localization witness that puts every chosen root face on the extracted outer
ambient boundary, the peeled-face endpoint no-touch condition, and nonemptiness of the raw
interior-edge endpoint carrier. -/
theorem
    theorem49OuterBoundaryRootNonemptySynthesis_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_of_rootsOuterAmbientBoundary_and_peelFaces_endpoint_disjoint_selectedBoundarySupport
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hrootsOuterBoundary : ∀ r ∈ interiorData.roots,
      ∃ e ∈ emb.faceBoundary r.1,
        e ∈ source.boundaryReachability.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (hPeelNoTouch : ∀ f ∈
      (planarBoundaryAnnulusConstruction_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
        (planarBoundaryOuterBoundaryRootAdjDistancePeelData_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_of_rootsOuterAmbientBoundary
          source.boundaryReachability interiorData hrootsOuterBoundary)).peelFaces,
      Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
        (edgeEndpointSupport
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty) :
    Theorem49OuterBoundaryRootNonemptySynthesis emb
        (planarBoundaryOuterBoundaryRootAdjDistancePeelData_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_of_rootsOuterAmbientBoundary
          source.boundaryReachability interiorData hrootsOuterBoundary)
        C₀ := by
  let data :=
    planarBoundaryOuterBoundaryRootAdjDistancePeelData_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_of_rootsOuterAmbientBoundary
      source.boundaryReachability interiorData hrootsOuterBoundary
  exact
    theorem49OuterBoundaryRootNonemptySynthesis_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
      (G := G) data C₀ hC₀ hPeelNoTouch hRawCarrier

/-- Graph-level non-vacuous outer-root synthesis route from the honest closed-walk annulus source
shell. This is the current positive endpoint-separation repair theorem at the actual source-facing
surface: if the same embedding supplies the outer-root localization witness, peeled-face endpoint
no-touch, and a nonempty raw interior-edge endpoint carrier, then the route reaches the
outer-boundary-root non-vacuous synthesis endpoint. -/
theorem
    exists_theorem49OuterBoundaryRootNonemptySynthesis_of_exists_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_and_rootsOuterAmbientBoundary_and_peelFaces_endpoint_disjoint_selectedBoundarySupport_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
      ∃ hrootsOuterBoundary : ∀ r ∈ interiorData.roots,
        ∃ e ∈ emb.faceBoundary r.1,
          e ∈ source.boundaryReachability.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary,
        let data :=
          planarBoundaryOuterBoundaryRootAdjDistancePeelData_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_of_rootsOuterAmbientBoundary
            source.boundaryReachability interiorData hrootsOuterBoundary
        (∀ f ∈
          (planarBoundaryAnnulusConstruction_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
            data).peelFaces,
          Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
            (edgeEndpointSupport
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))) ∧
        (interiorEdgeEndpointSupport emb).Nonempty)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb,
        Theorem49OuterBoundaryRootNonemptySynthesis emb data C₀ := by
  rcases hG with ⟨emb, source, interiorData, hrootsOuterBoundary, hPeelNoTouch, hRawCarrier⟩
  let data :=
    planarBoundaryOuterBoundaryRootAdjDistancePeelData_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_of_rootsOuterAmbientBoundary
      source.boundaryReachability interiorData hrootsOuterBoundary
  have hPeelNoTouch' : ∀ f ∈
      (planarBoundaryAnnulusConstruction_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
        data).peelFaces,
      Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
        (edgeEndpointSupport
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) := by
    simpa [data] using hPeelNoTouch
  exact
    ⟨emb, data,
      theorem49OuterBoundaryRootNonemptySynthesis_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
        (G := G) data C₀ hC₀ hPeelNoTouch' hRawCarrier⟩

/-- Honest closed-walk source route to the non-vacuous two-sided annulus-root synthesis surface.
After dropping the impossible all-outer-root requirement, the remaining geometric burden is only
endpoint-support disjointness between raw interior-edge endpoints and the selected boundary,
together with nonemptiness of the raw carrier. -/
theorem
    theorem49AnnulusRootNonemptySynthesis_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_of_endpointSupport_disjoint
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (hEndpointDisjoint : Disjoint (interiorEdgeEndpointSupport emb)
      (edgeEndpointSupport
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty) :
    Theorem49AnnulusRootNonemptySynthesis emb
        (planarBoundaryAnnulusRootAdjDistancePeelData_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData
          source interiorData)
        C₀ := by
  exact
    theorem49AnnulusRootNonemptySynthesis_of_planarBoundaryAnnulusRootAdjDistancePeelData_of_endpointSupport_disjoint
      (G := G)
      (planarBoundaryAnnulusRootAdjDistancePeelData_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData
        source interiorData)
      C₀ hC₀ hEndpointDisjoint hRawCarrier

/-- Honest closed-walk source route to the non-vacuous two-sided annulus-root synthesis surface,
with raw endpoint separation discharged from the canonical annulus construction's peeled-face
endpoint no-touch condition. This keeps the remaining burden on a facewise construction statement
instead of asking directly for global endpoint-support disjointness. -/
theorem
    theorem49AnnulusRootNonemptySynthesis_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (hPeelNoTouch : ∀ f ∈
      (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
        source.boundaryReachability interiorData).peelFaces,
      Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
        (edgeEndpointSupport
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty) :
    Theorem49AnnulusRootNonemptySynthesis emb
        (planarBoundaryAnnulusRootAdjDistancePeelData_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData
          source interiorData)
        C₀ := by
  let construction :=
    planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
      source.boundaryReachability interiorData
  have hPeelNoTouch' : ∀ f ∈ construction.peelFaces,
      Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
        (edgeEndpointSupport
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) := by
    simpa [construction] using hPeelNoTouch
  have hEndpointDisjoint :
      Disjoint (interiorEdgeEndpointSupport emb)
        (edgeEndpointSupport
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) :=
    construction.endpointSupport_disjoint_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
      hPeelNoTouch'
  exact
    theorem49AnnulusRootNonemptySynthesis_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_of_endpointSupport_disjoint
      (G := G) source interiorData C₀ hC₀ hEndpointDisjoint hRawCarrier

/-- Graph-level non-vacuous two-sided annulus-root synthesis route from the honest closed-walk
source shell. This is the first non-vacuous source-facing theorem on a boundary-root surface that
avoids the vacuous all-roots-outer hypothesis. -/
theorem
    exists_theorem49AnnulusRootNonemptySynthesis_of_exists_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_with_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
        let _data :=
          planarBoundaryAnnulusRootAdjDistancePeelData_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData
            source interiorData
        Disjoint (interiorEdgeEndpointSupport emb)
          (edgeEndpointSupport
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
        (interiorEdgeEndpointSupport emb).Nonempty)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryAnnulusRootAdjDistancePeelData emb,
        Theorem49AnnulusRootNonemptySynthesis emb data C₀ := by
  rcases hG with ⟨emb, source, interiorData, hEndpointDisjoint, hRawCarrier⟩
  let data :=
    planarBoundaryAnnulusRootAdjDistancePeelData_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData
      source interiorData
  exact
    ⟨emb, data,
      theorem49AnnulusRootNonemptySynthesis_of_planarBoundaryAnnulusRootAdjDistancePeelData_of_endpointSupport_disjoint
        (G := G) data C₀ hC₀ hEndpointDisjoint hRawCarrier⟩

/-- Graph-level non-vacuous two-sided annulus-root synthesis route from the honest closed-walk
source shell, using the canonical annulus construction's peeled-face endpoint no-touch condition
as the explicit geometric repair obligation. -/
theorem
    exists_theorem49AnnulusRootNonemptySynthesis_of_exists_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_with_peelFaces_endpoint_disjoint_selectedBoundarySupport_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
        let construction :=
          planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
            source.boundaryReachability interiorData
        (∀ f ∈ construction.peelFaces,
          Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
            (edgeEndpointSupport
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))) ∧
        (interiorEdgeEndpointSupport emb).Nonempty)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryAnnulusRootAdjDistancePeelData emb,
        Theorem49AnnulusRootNonemptySynthesis emb data C₀ := by
  rcases hG with ⟨emb, source, interiorData, hPeelNoTouch, hRawCarrier⟩
  let data :=
    planarBoundaryAnnulusRootAdjDistancePeelData_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData
      source interiorData
  exact
    ⟨emb, data,
      theorem49AnnulusRootNonemptySynthesis_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
        (G := G) source interiorData C₀ hC₀ hPeelNoTouch hRawCarrier⟩

/-- The explicit closed-walk annulus-boundary source and generic boundary-root interior-dual data
already feed the two-sided annulus-root Theorem 4.9 synthesis surface. This records the current
positive route endpoint after the all-outer-root obstruction has been removed. -/
theorem
    theorem49AnnulusRootSynthesis_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Theorem49AnnulusRootSynthesis emb
        (planarBoundaryAnnulusRootAdjDistancePeelData_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData
          source interiorData)
        C₀ :=
  theorem49AnnulusRootSynthesis_of_planarBoundaryAnnulusRootAdjDistancePeelData
    (G := G)
    (planarBoundaryAnnulusRootAdjDistancePeelData_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData
      source interiorData)
    C₀ hC₀

/-- Graph-level synthesis endpoint from the explicit closed-walk annulus-boundary source and
generic boundary-root interior-dual data on one embedding. -/
theorem
    exists_theorem49AnnulusRootSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        Nonempty (InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary))
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryAnnulusRootAdjDistancePeelData emb,
        Theorem49AnnulusRootSynthesis emb data C₀ := by
  rcases hG with ⟨emb, source, ⟨interiorData⟩⟩
  let data :=
    planarBoundaryAnnulusRootAdjDistancePeelData_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData
      source interiorData
  exact ⟨emb, data,
    theorem49AnnulusRootSynthesis_of_planarBoundaryAnnulusRootAdjDistancePeelData
      (G := G) data C₀ hC₀⟩

/-- Direct graph-level synthesis endpoint from the explicit closed-walk annulus-boundary source
and generic boundary-root interior-dual data. This matches the existing direct construction and
well-founded-witness wrappers in this file. -/
theorem
    exists_theorem49AnnulusRootSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
        Nonempty (InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary))
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryAnnulusRootAdjDistancePeelData emb,
        Theorem49AnnulusRootSynthesis emb data C₀ := by
  rcases hG with ⟨emb, ⟨source⟩, ⟨interiorData⟩⟩
  exact
    exists_theorem49AnnulusRootSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData
      (G := G) ⟨emb, source, ⟨interiorData⟩⟩ C₀ hC₀

/-- Live successor-cycle-shell obstruction inherited from the honest closed-walk source: if one
source-extracted outer boundary face reaches one source-extracted inner boundary face in the
interior dual graph, then the same embedding cannot satisfy the source boundary-face root
separation premise. This isolates the exact rooted-cover failure before any generic interior-dual
payload or theorem-4.9 packaging is introduced. -/
theorem
    not_rootSetSeparated_boundaryFaceRoots_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_reachable_outerBoundaryFace_innerBoundaryFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    {fo fi : AmbientFace emb.faces}
    (hfo : fo ∈
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hboundaryArc).toPlanarBoundaryAnnulusBoundaryData.outerBoundaryFaces)
    (hfi : fi ∈
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hboundaryArc).toPlanarBoundaryAnnulusBoundaryData.innerBoundaryFaces)
    (hreach : (interiorDualGraph emb.faceBoundary emb.faces).Reachable fo fi) :
    ¬ RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots) := by
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  have hfo' : fo ∈ source.toPlanarBoundaryAnnulusBoundaryData.outerBoundaryFaces := by
    simpa [source] using hfo
  have hfi' : fi ∈ source.toPlanarBoundaryAnnulusBoundaryData.innerBoundaryFaces := by
    simpa [source] using hfi
  exact
    source.not_rootSetSeparated_boundaryFaceRoots_of_reachable_outerBoundaryFace_innerBoundaryFace
      hfo' hfi' hreach

/-- Graph-level no-coexistence form of the same live successor-cycle-shell root-separation
obstruction. If the source-extracted annulus boundary split still has an outer-to-inner
interior-dual path, then the route already fails at the source boundary-face root separation
premise, before any rooted shared-edge cover or generic interior-dual payload is added. -/
theorem
    not_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_rootSetSeparated_boundaryFaceRoots_and_reachable_outerBoundaryFace_innerBoundaryFace
    {G : SimpleGraph V} :
    ¬ (∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hboundaryArc : ∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ _hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
          ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hboundaryArc).boundaryFaceRoots),
      ∃ fo fi : AmbientFace emb.faces,
        fo ∈
          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hboundaryArc).toPlanarBoundaryAnnulusBoundaryData.outerBoundaryFaces ∧
        fi ∈
          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hboundaryArc).toPlanarBoundaryAnnulusBoundaryData.innerBoundaryFaces ∧
        (interiorDualGraph emb.faceBoundary emb.faces).Reachable fo fi) := by
  rintro ⟨emb, boundaryData, dartCycles, hboundaryArc, hsepRoots, fo, fi, hfo, hfi, hreach⟩
  exact
    not_rootSetSeparated_boundaryFaceRoots_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_reachable_outerBoundaryFace_innerBoundaryFace
      boundaryData dartCycles hboundaryArc hfo hfi hreach hsepRoots

/-- Live successor-cycle-shell obstruction inherited from the honest closed-walk source: if one
source-extracted outer boundary face reaches one source-extracted inner boundary face in the
interior dual graph, then the same embedding cannot carry generic boundary-root adjacency-distance
peel data. This marks a genuine upstream failure point before any rooted-cover or theorem-4.9
packaging is attempted. -/
theorem
    not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_reachable_outerBoundaryFace_innerBoundaryFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    {fo fi : AmbientFace emb.faces}
    (hfo : fo ∈
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hboundaryArc).toPlanarBoundaryAnnulusBoundaryData.outerBoundaryFaces)
    (hfi : fi ∈
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hboundaryArc).toPlanarBoundaryAnnulusBoundaryData.innerBoundaryFaces)
    (hreach : (interiorDualGraph emb.faceBoundary emb.faces).Reachable fo fi) :
    ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) := by
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  have hfo' : fo ∈ source.toPlanarBoundaryAnnulusBoundaryData.outerBoundaryFaces := by
    simpa [source] using hfo
  have hfi' : fi ∈ source.toPlanarBoundaryAnnulusBoundaryData.innerBoundaryFaces := by
    simpa [source] using hfi
  exact
    source.not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_of_reachable_outerBoundaryFace_innerBoundaryFace
      hfo' hfi' hreach

/-- Graph-level no-coexistence form of the same live successor-cycle-shell obstruction. Any
candidate route instance that still has an interior-dual path from a source-extracted outer
boundary face to a source-extracted inner boundary face already fails before the rooted-cover
IDBRAD bridge can even be used. -/
theorem
    not_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootAdjDistancePeelData_and_reachable_outerBoundaryFace_innerBoundaryFace
    {G : SimpleGraph V} :
    ¬ (∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hboundaryArc : ∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ _interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
      ∃ fo fi : AmbientFace emb.faces,
        fo ∈
          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hboundaryArc).toPlanarBoundaryAnnulusBoundaryData.outerBoundaryFaces ∧
        fi ∈
          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hboundaryArc).toPlanarBoundaryAnnulusBoundaryData.innerBoundaryFaces ∧
        (interiorDualGraph emb.faceBoundary emb.faces).Reachable fo fi) := by
  rintro ⟨emb, boundaryData, dartCycles, hboundaryArc, interiorData, fo, fi, hfo, hfi, hreach⟩
  exact
    not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_reachable_outerBoundaryFace_innerBoundaryFace
      boundaryData dartCycles hboundaryArc hfo hfi hreach ⟨interiorData⟩

/-- Direct theorem-4.9 boundary-root synthesis endpoint from the honest closed-walk source shell
once the source-fixed rooted shared-edge face-membership package on the extracted boundary-face
roots has been built.  This is the sharp closed-walk analogue of the live successor-cycle
theorem below: once that concrete rooted-cover payload exists, no further theorem-4.9-side
repackaging remains below it. -/
theorem
    exists_theorem49BoundaryRootSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
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
                    source.boundaryFaceRoots hcoverRoots hsepRoots g)))
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases hG with
    ⟨emb, source, peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover, hchildren⟩
  exact
    ⟨emb,
      theorem49BoundaryRootSynthesis_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
        (G := G)
        (interiorDualBoundaryRootAdjDistancePeelDataOfClosedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover
          source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover hchildren)
        C₀ hC₀⟩

/-- Source-fixed successor-cycle constructor for the generic interior-dual boundary-root
adjacency-distance package. The live boundary-order shell contributes the honest closed-walk
annulus source on the same embedding, so the remaining burden is exactly the source boundary-face
root cover/separation, boundary-free peeled-face, rooted shared-edge coverage, and strict
root-distance child-membership package. -/
noncomputable def
    interiorDualBoundaryRootAdjDistancePeelData_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (peelFaces : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots))
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots))
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
          ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hboundaryArc).boundaryFaceRoots)
          hcoverRoots hsepRoots)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).fallbackEdge))
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
        (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
            ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                boundaryData dartCycles hboundaryArc).boundaryFaceRoots)
            hcoverRoots hsepRoots)
          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hboundaryArc).fallbackEdge f),
      e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
        ∃ g ∈ peelFaces,
          (interiorDualSpanningForest emb.faceBoundary emb.faces).Adj f g ∧
          e ∈ emb.faceBoundary g.1 ∧
          (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
              f
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                    boundaryData dartCycles hboundaryArc).boundaryFaceRoots)
                hcoverRoots hsepRoots f) <
            (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
              g
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                    boundaryData dartCycles hboundaryArc).boundaryFaceRoots)
                hcoverRoots hsepRoots g)) :
    InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary :=
  by
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    interiorDualBoundaryRootAdjDistancePeelDataOfClosedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover
      source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover hchildren

/-- The live successor-cycle rooted shared-edge face-membership burden already contradicts any
source-extracted outer-to-inner interior-dual path. Once that concrete source-fixed rooted-cover
package is present, the existing constructor yields generic IDBRAD data on the same embedding,
so a reachable outer/inner boundary-face pair kills the route before any theorem-4.9 endpoint
packaging is relevant. -/
theorem
    false_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_reachable_outerBoundaryFace_innerBoundaryFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (peelFaces : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots))
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots))
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
          ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hboundaryArc).boundaryFaceRoots)
          hcoverRoots hsepRoots)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).fallbackEdge))
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
        (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
            ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                boundaryData dartCycles hboundaryArc).boundaryFaceRoots)
            hcoverRoots hsepRoots)
          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hboundaryArc).fallbackEdge f),
      e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
        ∃ g ∈ peelFaces,
          (interiorDualSpanningForest emb.faceBoundary emb.faces).Adj f g ∧
          e ∈ emb.faceBoundary g.1 ∧
          (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
              f
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                    boundaryData dartCycles hboundaryArc).boundaryFaceRoots)
                hcoverRoots hsepRoots f) <
            (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
              g
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                    boundaryData dartCycles hboundaryArc).boundaryFaceRoots)
                hcoverRoots hsepRoots g))
    {fo fi : AmbientFace emb.faces}
    (hfo : fo ∈
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hboundaryArc).toPlanarBoundaryAnnulusBoundaryData.outerBoundaryFaces)
    (hfi : fi ∈
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hboundaryArc).toPlanarBoundaryAnnulusBoundaryData.innerBoundaryFaces)
    (hreach : (interiorDualGraph emb.faceBoundary emb.faces).Reachable fo fi) :
    False := by
  have hnot :
      ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) :=
    not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_reachable_outerBoundaryFace_innerBoundaryFace
      boundaryData dartCycles hboundaryArc hfo hfi hreach
  exact
    hnot ⟨
      interiorDualBoundaryRootAdjDistancePeelData_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover
        boundaryData dartCycles hboundaryArc peelFaces hunique hcoverRoots hsepRoots
        hpeelInterior hcover hchildren⟩

/-- Graph-level no-coexistence form of the same rooted shared-edge face-membership obstruction.
If a live successor-cycle shell still extracts an outer boundary face that reaches an inner
boundary face in the interior dual, then no source-fixed rooted shared-edge cover package can
exist on that shell. -/
theorem
    not_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_reachable_outerBoundaryFace_innerBoundaryFace
    {G : SimpleGraph V} :
    ¬ (∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hboundaryArc : ∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ peelFaces : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
          ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hboundaryArc).boundaryFaceRoots),
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
          ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hboundaryArc).boundaryFaceRoots),
        (∀ f ∈ peelFaces,
          Disjoint (emb.faceBoundary f.1)
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
        interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                  boundaryData dartCycles hboundaryArc).boundaryFaceRoots)
              hcoverRoots hsepRoots)
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hboundaryArc).fallbackEdge) ∧
        (∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
            (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                    boundaryData dartCycles hboundaryArc).boundaryFaceRoots)
                hcoverRoots hsepRoots)
              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                boundaryData dartCycles hboundaryArc).fallbackEdge f),
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
            ∃ g ∈ peelFaces,
              (interiorDualSpanningForest emb.faceBoundary emb.faces).Adj f g ∧
              e ∈ emb.faceBoundary g.1 ∧
              (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                  f
                  (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                    ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                        boundaryData dartCycles hboundaryArc).boundaryFaceRoots)
                    hcoverRoots hsepRoots f) <
                (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                  g
                  (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                    ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                        boundaryData dartCycles hboundaryArc).boundaryFaceRoots)
                    hcoverRoots hsepRoots g)) ∧
        ∃ fo fi : AmbientFace emb.faces,
          fo ∈
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hboundaryArc).toPlanarBoundaryAnnulusBoundaryData.outerBoundaryFaces ∧
          fi ∈
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hboundaryArc).toPlanarBoundaryAnnulusBoundaryData.innerBoundaryFaces ∧
          (interiorDualGraph emb.faceBoundary emb.faces).Reachable fo fi) := by
  rintro ⟨emb, boundaryData, dartCycles, hboundaryArc, peelFaces, hunique, hcoverRoots, hsepRoots,
    hpeelInterior, hcover, hchildren, fo, fi, hfo, hfi, hreach⟩
  exact
    false_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_reachable_outerBoundaryFace_innerBoundaryFace
      boundaryData dartCycles hboundaryArc peelFaces hunique hcoverRoots hsepRoots
      hpeelInterior hcover hchildren hfo hfi hreach

/-- Graph-level successor-cycle route to the generic interior-dual boundary-root
adjacency-distance package through the source-fixed canonical rooted shared-edge cover shell.
This turns the current live boundary-order burden into the explicit source boundary-face root
cover/separation and rooted shared-edge child-membership package, with no extra repackaging step
below the successor-cycle shell. -/
theorem
    admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hboundaryArc : ∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ peelFaces : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
          ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hboundaryArc).boundaryFaceRoots),
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
          ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hboundaryArc).boundaryFaceRoots),
        (∀ f ∈ peelFaces,
          Disjoint (emb.faceBoundary f.1)
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
        interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                  boundaryData dartCycles hboundaryArc).boundaryFaceRoots)
              hcoverRoots hsepRoots)
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hboundaryArc).fallbackEdge) ∧
        (∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
            (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                    boundaryData dartCycles hboundaryArc).boundaryFaceRoots)
                hcoverRoots hsepRoots)
              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                boundaryData dartCycles hboundaryArc).fallbackEdge f),
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
            ∃ g ∈ peelFaces,
              (interiorDualSpanningForest emb.faceBoundary emb.faces).Adj f g ∧
              e ∈ emb.faceBoundary g.1 ∧
              (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                  f
                  (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                    ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                        boundaryData dartCycles hboundaryArc).boundaryFaceRoots)
                    hcoverRoots hsepRoots f) <
                (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                  g
                  (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                    ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                        boundaryData dartCycles hboundaryArc).boundaryFaceRoots)
                    hcoverRoots hsepRoots g))) :
    AdmitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData G := by
  rcases hG with
    ⟨emb, boundaryData, dartCycles, hboundaryArc, peelFaces, hunique, hcoverRoots, hsepRoots,
      hpeelInterior, hcover, hchildren⟩
  exact
    ⟨emb, ⟨
      interiorDualBoundaryRootAdjDistancePeelData_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover
        boundaryData dartCycles hboundaryArc peelFaces hunique hcoverRoots hsepRoots
        hpeelInterior hcover hchildren⟩⟩

/-- Direct theorem-4.9 boundary-root synthesis endpoint from the successor-cycle boundary-order
shell once the source-fixed rooted shared-edge face-membership package has been built. This
records that no additional theorem-4.9-side repackaging remains below that concrete source-facing
IDBRAD surface. -/
theorem
    exists_theorem49BoundaryRootSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hboundaryArc : ∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ peelFaces : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
          ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hboundaryArc).boundaryFaceRoots),
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
          ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hboundaryArc).boundaryFaceRoots),
        (∀ f ∈ peelFaces,
          Disjoint (emb.faceBoundary f.1)
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
        interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                  boundaryData dartCycles hboundaryArc).boundaryFaceRoots)
              hcoverRoots hsepRoots)
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hboundaryArc).fallbackEdge) ∧
        (∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
            (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                    boundaryData dartCycles hboundaryArc).boundaryFaceRoots)
                hcoverRoots hsepRoots)
              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                boundaryData dartCycles hboundaryArc).fallbackEdge f),
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
            ∃ g ∈ peelFaces,
              (interiorDualSpanningForest emb.faceBoundary emb.faces).Adj f g ∧
              e ∈ emb.faceBoundary g.1 ∧
              (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                  f
                  (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                    ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                        boundaryData dartCycles hboundaryArc).boundaryFaceRoots)
                    hcoverRoots hsepRoots f) <
                (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                  g
                  (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                    ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                        boundaryData dartCycles hboundaryArc).boundaryFaceRoots)
                    hcoverRoots hsepRoots g)))
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ :=
  exists_theorem49BoundaryRootSynthesis_of_admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    (admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover
      hG)
    C₀ hC₀

/-- Direct successor-cycle source route to the annulus construction through the root-distance
continuation theorem. The successor-cycle data earns the existing closed-walk annulus-boundary
source, while the construction endpoint only needs the same-embedding reachability and
interior-dual data. -/
theorem
    admitsPlanarBoundaryAnnulusConstruction_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootAdjDistancePeelData_direct
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _ : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ _ : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        ∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) :
    AdmitsPlanarBoundaryAnnulusConstruction G := by
  rcases hG with ⟨emb, boundaryData, interiorData, dartCycles, hboundaryArc⟩
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    admitsPlanarBoundaryAnnulusConstruction_of_exists_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_direct
      ⟨emb, ⟨source⟩, ⟨interiorData⟩⟩

/-- Graph-level parent-witness orientation theorem on the successor-cycle source shell. The
successor cycles first produce the honest closed-walk annulus source, and then the same
root-distance construction yields the parent-oriented annulus peel. -/
theorem
    admitsPlanarBoundaryAnnulusConstructionParentWitnessOrientation_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootAdjDistancePeelData_direct
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _ : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ _ : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        ∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) :
    AdmitsPlanarBoundaryAnnulusConstructionParentWitnessOrientation G := by
  rcases hG with ⟨emb, boundaryData, interiorData, dartCycles, hboundaryArc⟩
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    admitsPlanarBoundaryAnnulusConstructionParentWitnessOrientation_of_exists_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_direct
      ⟨emb, ⟨source⟩, ⟨interiorData⟩⟩

/-- Direct successor-cycle source route to the well-founded peel witness target through the
root-distance continuation theorem. This version avoids restating the shifted-frontier
nonemptiness/disjointness and parent-in-peel obligations that belong only to the older shifted
construction surface. -/
theorem
    admitsPlanarBoundaryWellFoundedFacePeelWitnessData_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootAdjDistancePeelData_direct
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _ : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ _ : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        ∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) :
    AdmitsPlanarBoundaryWellFoundedFacePeelWitnessData G := by
  exact
    admitsPlanarBoundaryWellFoundedFacePeelWitnessData_of_admitsPlanarBoundaryAnnulusConstructionParentWitnessOrientation
      (admitsPlanarBoundaryAnnulusConstructionParentWitnessOrientation_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootAdjDistancePeelData_direct
        hG)

/-- Successor-cycle source route to the attached certificate endpoint. The extra closed-walk and
selected-boundary-arc fields are honest source-side structure, but once boundary reachability and
boundary-root interior-dual adjacency-distance data are present on the same embedding, the route
to certificates now factors through the same parent-orientation surface used by the honest
closed-walk source. -/
theorem
    admitsPlanarBoundaryAttachedRootedFacePeelCertificate_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootAdjDistancePeelData_direct
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _ : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ _ : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        ∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) :
    AdmitsPlanarBoundaryAttachedRootedFacePeelCertificate G := by
  exact
    admitsPlanarBoundaryAttachedRootedFacePeelCertificate_of_admitsPlanarBoundaryAnnulusConstructionParentWitnessOrientation
      (admitsPlanarBoundaryAnnulusConstructionParentWitnessOrientation_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootAdjDistancePeelData_direct
        hG)

/-- Direct boundary-root synthesis endpoint from the successor-cycle source shell. This is the
certificate-side route statement: the successor cycles and selected-boundary arcs remain as honest
source hypotheses, but the synthesis endpoint itself is now reached through the attached
certificate surface. -/
theorem
    exists_theorem49BoundaryRootSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootAdjDistancePeelData_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _ : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ _ : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        ∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ :=
  exists_theorem49BoundaryRootSynthesis_of_admitsPlanarBoundaryAttachedRootedFacePeelCertificate
    (admitsPlanarBoundaryAttachedRootedFacePeelCertificate_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootAdjDistancePeelData_direct
      hG)
    C₀ hC₀

/-- Direct successor-cycle source route to the annulus-root Theorem 4.9 synthesis endpoint. The
successor-cycle data first earns the explicit closed-walk annulus-boundary source, and then the
two-sided annulus-root package feeds the generic synthesis core. -/
theorem
    exists_theorem49AnnulusRootSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootAdjDistancePeelData_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _ : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ _ : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        ∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryAnnulusRootAdjDistancePeelData emb,
        Theorem49AnnulusRootSynthesis emb data C₀ := by
  rcases hG with ⟨emb, boundaryData, interiorData, dartCycles, hboundaryArc⟩
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    exists_theorem49AnnulusRootSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_direct
      (G := G) ⟨emb, ⟨source⟩, ⟨interiorData⟩⟩ C₀ hC₀

/-- Successor-cycle source route to the non-vacuous two-sided annulus-root synthesis surface.
Lowering to the induced honest closed-walk source keeps the remaining burden exactly on the
canonical annulus construction's peeled-face endpoint no-touch condition together with a nonempty
raw interior-edge endpoint carrier. -/
theorem
    theorem49AnnulusRootNonemptySynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootAdjDistancePeelData_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (hPeelNoTouch : ∀ f ∈
      (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
        boundaryData interiorData).peelFaces,
      Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
        (edgeEndpointSupport
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty) :
    Theorem49AnnulusRootNonemptySynthesis emb
        (planarBoundaryAnnulusRootAdjDistancePeelData_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData
          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hboundaryArc)
          interiorData)
        C₀ := by
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    theorem49AnnulusRootNonemptySynthesis_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
      (G := G) source interiorData C₀ hC₀
      (by
        simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
          PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields] using hPeelNoTouch)
      hRawCarrier

/-- Graph-level successor-cycle boundary-order route to the non-vacuous two-sided annulus-root
synthesis surface. The live source shell reaches this endpoint as soon as the same embedding
supplies generic boundary-root interior-dual data, peeled-face endpoint no-touch, and a nonempty
raw interior-edge endpoint carrier. -/
theorem
    exists_theorem49AnnulusRootNonemptySynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootAdjDistancePeelData_with_peelFaces_endpoint_disjoint_selectedBoundarySupport_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∀ f ∈
          (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
            boundaryData interiorData).peelFaces,
          Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
            (edgeEndpointSupport
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))) ∧
        (interiorEdgeEndpointSupport emb).Nonempty)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryAnnulusRootAdjDistancePeelData emb,
        Theorem49AnnulusRootNonemptySynthesis emb data C₀ := by
  rcases hG with ⟨emb, boundaryData, interiorData, dartCycles, hboundaryArc, hPeelNoTouch, hRawCarrier⟩
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  let data :=
    planarBoundaryAnnulusRootAdjDistancePeelData_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData
      source interiorData
  exact
    ⟨emb, data,
      by
        simpa [data, source] using
          theorem49AnnulusRootNonemptySynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootAdjDistancePeelData_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
            (G := G) boundaryData interiorData dartCycles hboundaryArc C₀ hC₀
            hPeelNoTouch hRawCarrier⟩

/-- Successor-cycle boundary-order route to the source-fixed canonical-parent face-membership
cover shell. The successor cycles contribute the honest closed-walk annulus source on the same
embedding, so the remaining hypotheses are exactly the rooted shared-edge cover, root
cover/separation, and canonical parent child-membership fields on the source boundary-face roots.
-/
theorem
    admitsPlanarBoundaryInteriorDualBoundaryRootParentPeelData_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hboundaryArc : ∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ peelFaces : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
          ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hboundaryArc).boundaryFaceRoots),
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
          ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hboundaryArc).boundaryFaceRoots),
        (∀ f ∈ peelFaces,
          Disjoint (emb.faceBoundary f.1)
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
        interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                boundaryData dartCycles hboundaryArc).boundaryFaceRoots
              hcoverRoots hsepRoots)
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hboundaryArc).fallbackEdge) ∧
        (∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
            (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                  boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                hcoverRoots hsepRoots)
              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                boundaryData dartCycles hboundaryArc).fallbackEdge f),
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
            ∃ g ∈ peelFaces,
              parentTowardsRoot (interiorDualSpanningForest emb.faceBoundary emb.faces)
                  (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                    (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                      boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                    hcoverRoots hsepRoots) g = some f ∧
              e ∈ emb.faceBoundary g.1)) :
    AdmitsPlanarBoundaryInteriorDualBoundaryRootParentPeelData G := by
  rcases hG with
    ⟨emb, boundaryData, dartCycles, hboundaryArc, peelFaces, hunique, hcoverRoots, hsepRoots,
      hpeelInterior, hcover, hchildren⟩
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    admitsPlanarBoundaryInteriorDualBoundaryRootParentPeelData_of_exists_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover
      ⟨emb, source, peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover,
        hchildren⟩

/-- Successor-cycle boundary-order route to the raw source-fixed canonical-parent shared-edge
cover shell. The local parent child-membership condition is still derived internally from the
cover, so this is the sharper route-facing constructor when only the raw rooted shared-edge cover
is available. -/
theorem
    admitsPlanarBoundaryInteriorDualBoundaryRootParentPeelData_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hboundaryArc : ∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ peelFaces : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
          ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hboundaryArc).boundaryFaceRoots),
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
          ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hboundaryArc).boundaryFaceRoots),
        (∀ f ∈ peelFaces,
          Disjoint (emb.faceBoundary f.1)
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
        interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                boundaryData dartCycles hboundaryArc).boundaryFaceRoots
              hcoverRoots hsepRoots)
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hboundaryArc).fallbackEdge)) :
    AdmitsPlanarBoundaryInteriorDualBoundaryRootParentPeelData G := by
  rcases hG with
    ⟨emb, boundaryData, dartCycles, hboundaryArc, peelFaces, hunique, hcoverRoots, hsepRoots,
      hpeelInterior, hcover⟩
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    admitsPlanarBoundaryInteriorDualBoundaryRootParentPeelData_of_exists_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
      ⟨emb, source, peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover⟩

/-- Direct theorem-4.9 synthesis endpoint from the successor-cycle boundary-order shell once the
source-fixed canonical-parent face-membership cover data has been built. This records the live
route fact that no additional theorem-4.9 algebra remains below that concrete parent-cover
package. -/
theorem
    exists_theorem49BoundaryRootSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hboundaryArc : ∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ peelFaces : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
          ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hboundaryArc).boundaryFaceRoots),
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
          ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hboundaryArc).boundaryFaceRoots),
        (∀ f ∈ peelFaces,
          Disjoint (emb.faceBoundary f.1)
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
        interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                boundaryData dartCycles hboundaryArc).boundaryFaceRoots
              hcoverRoots hsepRoots)
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hboundaryArc).fallbackEdge) ∧
        (∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
            (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                  boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                hcoverRoots hsepRoots)
              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                boundaryData dartCycles hboundaryArc).fallbackEdge f),
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
            ∃ g ∈ peelFaces,
              parentTowardsRoot (interiorDualSpanningForest emb.faceBoundary emb.faces)
                  (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                    (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                      boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                    hcoverRoots hsepRoots) g = some f ∧
              e ∈ emb.faceBoundary g.1))
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ :=
  exists_theorem49BoundaryRootSynthesis_of_admitsPlanarBoundaryInteriorDualBoundaryRootParentPeelData
    (admitsPlanarBoundaryInteriorDualBoundaryRootParentPeelData_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover
      hG)
    C₀ hC₀

/-- Direct theorem-4.9 synthesis endpoint from the successor-cycle boundary-order shell already
at the raw source-fixed canonical-parent shared-edge cover surface. The child-membership field is
reconstructed internally, so this is the sharper live route endpoint for parent-cover data coming
from actual boundary-order geometry. -/
theorem
    exists_theorem49BoundaryRootSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hboundaryArc : ∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ peelFaces : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
          ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hboundaryArc).boundaryFaceRoots),
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
          ((PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hboundaryArc).boundaryFaceRoots),
        (∀ f ∈ peelFaces,
          Disjoint (emb.faceBoundary f.1)
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
        interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                boundaryData dartCycles hboundaryArc).boundaryFaceRoots
              hcoverRoots hsepRoots)
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hboundaryArc).fallbackEdge))
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ :=
  exists_theorem49BoundaryRootSynthesis_of_admitsPlanarBoundaryInteriorDualBoundaryRootParentPeelData
    (admitsPlanarBoundaryInteriorDualBoundaryRootParentPeelData_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover
      hG)
    C₀ hC₀

/-- Root-distance annihilator route from the explicit closed-walk annulus-boundary source. Unlike
the shifted construction surface, this theorem does not ask for a separate peeled-parent repair:
the parent-witness orientation is supplied by the root-distance annulus construction on the same
boundary reachability and interior-dual data. -/
theorem
    zero_on_allEdges_of_exists_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_direct_of_annihilatesKempeClosureGeneratorFamily
    {G : SimpleGraph V}
    (C₀ C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C)
    (hC : C ∈ G.EdgeKempeClosure C₀) (z : G.edgeSet → Color)
    (hdata : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _ : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _ : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
        (∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0) ∧
        AnnihilatesKempeClosureGeneratorFamily emb.faceBoundary C₀ z) :
    ∀ e, z e = 0 := by
  rcases hdata with ⟨emb, source, interiorData, hzeroBoundary, hgen⟩
  let data :=
    planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_rootDistance
      source.boundaryReachability interiorData
  have horient : data.ParentWitnessOrientation :=
    parentWitnessOrientation_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_rootDistance
      source.boundaryReachability interiorData
  exact
    zero_on_allEdges_of_planarBoundaryAnnulusConstruction_of_parentWitness
      (emb := emb) (data := data) (hparentWitness := horient)
      (C := C) (htait := htait) (z := z)
      (hzeroBoundary := hzeroBoundary) (horth := by
        intro f _hf γ hγ0 hγne
        simpa [data] using
          localOrthogonality_of_annihilatesKempeClosureGeneratorFamily
            (faceBoundary := emb.faceBoundary) (hC := hC) hgen
            (f := f.1) (e := data.witnessEdge f) (htait (data.witnessEdge f))
            γ hγ0 hγne)

/-- Root-distance annihilator route from the successor-based facial dart-cycle source. The
successor cycles first earn the existing closed-walk annulus-boundary source, and then the
root-distance construction supplies parent orientation internally. -/
theorem
    zero_on_allEdges_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootAdjDistancePeelData_direct_of_annihilatesKempeClosureGeneratorFamily
    {G : SimpleGraph V}
    (C₀ C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C)
    (hC : C ∈ G.EdgeKempeClosure C₀) (z : G.edgeSet → Color)
    (hdata : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _ : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ _ : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0) ∧
        AnnihilatesKempeClosureGeneratorFamily emb.faceBoundary C₀ z) :
    ∀ e, z e = 0 := by
  rcases hdata with
    ⟨emb, boundaryData, interiorData, dartCycles, hboundaryArc, hzeroBoundary, hgen⟩
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    zero_on_allEdges_of_exists_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_direct_of_annihilatesKempeClosureGeneratorFamily
      (C₀ := C₀) (C := C) (htait := htait) (hC := hC) (z := z)
      ⟨emb, source, interiorData, hzeroBoundary, hgen⟩

/-- Ground-up annulus annihilator route from the successor-cycle source shell. The successor data
first yields the honest closed-walk annulus-boundary source on the same embedding, and the
same-embedding weak annulus collar geometry then feeds the direct annulus-collar annihilator
theorem without using the interior-dual package. -/
theorem
    admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_annulusCollarGeometry_direct
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _ : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _ : PlanarBoundaryAnnulusCollarGeometry emb,
        ∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) :
    AdmitsPlanarBoundaryCollarLayerFacePeelWitnessData G := by
  rcases hG with ⟨emb, boundaryData, dartCycles, data, hboundaryArc⟩
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_direct
      ⟨emb, ⟨source⟩, ⟨data⟩⟩

/-- The successor-cycle source shell also lands directly on the boundary-aware height-ordered
witness-cover surface once the same embedding carries annulus collar geometry. Lowering through
the honest closed-walk source is enough; no later annulus bookkeeping remains. -/
theorem
    admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_annulusCollarGeometry_direct
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _ : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _ : PlanarBoundaryAnnulusCollarGeometry emb,
        ∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) :
    AdmitsPlanarBoundaryHeightOrderedFacePeelWitnessData G := by
  rcases hG with ⟨emb, boundaryData, dartCycles, data, hboundaryArc⟩
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_direct
      ⟨emb, ⟨source⟩, ⟨data⟩⟩

/-- If the successor-cycle source shell carries annulus collar geometry together with the repaired
witness-on-current-boundary placement, then it already reaches the well-founded peel-witness
surface through the honest closed-walk source lowering. -/
theorem
    admitsPlanarBoundaryWellFoundedFacePeelWitnessData_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_annulusCollarGeometry_and_witnessOnCurrentBoundary_direct
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _ : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          data.WitnessOnCurrentBoundary) :
    AdmitsPlanarBoundaryWellFoundedFacePeelWitnessData G := by
  rcases hG with ⟨emb, boundaryData, dartCycles, data, hboundaryArc, hwitness⟩
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    admitsPlanarBoundaryWellFoundedFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_witnessOnCurrentBoundary_direct
      ⟨emb, ⟨source⟩, data, hwitness⟩

/-- Ground-up annulus annihilator route from the successor-cycle source shell. The successor data
first yields the honest closed-walk annulus-boundary source on the same embedding, and the
same-embedding weak annulus collar geometry then feeds the direct annulus-collar annihilator
theorem without using the interior-dual package. -/
theorem
    zero_on_allEdges_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_annulusCollarGeometry_direct_of_annihilatesKempeClosureGeneratorFamily
    {G : SimpleGraph V}
    (C₀ C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C)
    (hC : C ∈ G.EdgeKempeClosure C₀) (z : G.edgeSet → Color)
    (hdata : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _ : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _ : PlanarBoundaryAnnulusCollarGeometry emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0) ∧
        AnnihilatesKempeClosureGeneratorFamily emb.faceBoundary C₀ z) :
    ∀ e, z e = 0 := by
  rcases hdata with ⟨emb, boundaryData, dartCycles, data, hboundaryArc, hzeroBoundary, hgen⟩
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    zero_on_allEdges_of_exists_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_direct_of_annihilatesKempeClosureGeneratorFamily
      (C₀ := C₀) (C := C) (htait := htait) (hC := hC) (z := z)
      ⟨emb, source, data, hzeroBoundary, hgen⟩

/-- Ground-up annulus annihilator route from the successor-cycle source shell plus same-embedding
boundary-aware height-ordered witness-cover data. Once successor cycles are lowered to the honest
closed-walk source, the height-sorted witness-cover package already closes the Step 2 vanishing
argument. -/
theorem
    zero_on_allEdges_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_heightOrderedFacePeelWitnessData_direct_of_annihilatesKempeClosureGeneratorFamily
    {G : SimpleGraph V}
    (C₀ C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C)
    (hC : C ∈ G.EdgeKempeClosure C₀) (z : G.edgeSet → Color)
    (hdata : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _ : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _ : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0) ∧
        AnnihilatesKempeClosureGeneratorFamily emb.faceBoundary C₀ z) :
    ∀ e, z e = 0 := by
  rcases hdata with ⟨emb, boundaryData, dartCycles, data, hboundaryArc, hzeroBoundary, hgen⟩
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    zero_on_allEdges_of_exists_closedWalkAnnulusBoundarySource_and_heightOrderedFacePeelWitnessData_direct_of_annihilatesKempeClosureGeneratorFamily
      (C₀ := C₀) (C := C) (htait := htait) (hC := hC) (z := z)
      ⟨emb, source, data, hzeroBoundary, hgen⟩

/-- Ground-up annulus annihilator route from the successor-cycle source shell plus same-embedding
finite collar-layer witness-cover data. This matches the paper's finite nested-collar phrasing
without going back through the later annulus-geometry wrappers. -/
theorem
    zero_on_allEdges_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_collarLayerFacePeelWitnessData_direct_of_annihilatesKempeClosureGeneratorFamily
    {G : SimpleGraph V}
    (C₀ C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C)
    (hC : C ∈ G.EdgeKempeClosure C₀) (z : G.edgeSet → Color)
    (hdata : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _ : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _ : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0) ∧
        AnnihilatesKempeClosureGeneratorFamily emb.faceBoundary C₀ z) :
    ∀ e, z e = 0 := by
  rcases hdata with ⟨emb, boundaryData, dartCycles, data, hboundaryArc, hzeroBoundary, hgen⟩
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    zero_on_allEdges_of_exists_closedWalkAnnulusBoundarySource_and_collarLayerFacePeelWitnessData_direct_of_annihilatesKempeClosureGeneratorFamily
      (C₀ := C₀) (C := C) (htait := htait) (hC := hC) (z := z)
      ⟨emb, source, data, hzeroBoundary, hgen⟩

/-- Direct theorem-4.9 synthesis endpoint from the successor-cycle source shell plus same-
embedding weak annulus collar geometry. Once the successor data yields the honest closed-walk
source and the same embedding carries collar geometry, the remaining synthesis package is
automatic. -/
theorem
    exists_theorem49BoundaryRootSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_annulusCollarGeometry_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _ : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _ : PlanarBoundaryAnnulusCollarGeometry emb,
        ∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases hG with ⟨emb, _boundaryData, _dartCycles, data, _hboundaryArc⟩
  exact ⟨emb,
    theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusCollarGeometry
      (G := G) data C₀ hC₀⟩

/-- Direct theorem-4.9 synthesis endpoint from the successor-cycle source shell plus same-
embedding boundary-aware height-ordered witness-cover data. After lowering successor cycles to
the honest source shell, this is already enough to finish theorem-4.9 synthesis. -/
theorem
    exists_theorem49BoundaryRootSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_heightOrderedFacePeelWitnessData_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _ : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _ : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        ∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases hG with ⟨emb, _boundaryData, _dartCycles, data, _hboundaryArc⟩
  exact ⟨emb,
    theorem49BoundaryRootSynthesis_of_planarBoundaryHeightOrderedFacePeelWitnessData
      (G := G) data C₀ hC₀⟩

/-- Direct theorem-4.9 synthesis endpoint from the successor-cycle source shell plus same-
embedding finite collar-layer witness-cover data. This is earlier than the explicit remainder and
annulus-decomposition surfaces on the positive route. -/
theorem
    exists_theorem49BoundaryRootSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_collarLayerFacePeelWitnessData_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _ : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _ : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        ∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases hG with ⟨emb, _boundaryData, _dartCycles, data, _hboundaryArc⟩
  exact ⟨emb,
    theorem49BoundaryRootSynthesis_of_planarBoundaryCollarLayerFacePeelWitnessData
      (G := G) data C₀ hC₀⟩

/-- Direct theorem-4.9 synthesis endpoint from the successor-cycle source shell plus a same-
embedding split annulus decomposition with witness ownership. The successor data first supplies
the honest closed-walk source shell, while the split annulus witness package is already enough to
finish the theorem-4.9 synthesis. -/
theorem
    exists_theorem49BoundaryRootSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_annulusWitnessAssignment_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _ : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ decomp : PlanarBoundaryAnnulusDecomposition emb,
      ∃ _ : PlanarBoundaryAnnulusWitnessAssignment decomp,
        ∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases hG with ⟨emb, _boundaryData, _dartCycles, _decomp, data, _hboundaryArc⟩
  exact ⟨emb,
    theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusWitnessAssignment
      (G := G) data C₀ hC₀⟩

/-- Direct theorem-4.9 synthesis endpoint from the successor-cycle source shell plus canonical
facewise witness choice on the extracted annulus split.  The successor cycles first lower to the
honest closed-walk source package; the canonical witness then feeds the existing split-annulus
witness-assignment synthesis route. -/
theorem
    exists_theorem49BoundaryRootSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_canonicalWitnessChoice_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          Nonempty
            (PlanarBoundaryCanonicalWitnessChoice
              boundaryData.toPlanarBoundaryAnnulusBoundaryData))
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases hG with ⟨emb, boundaryData, dartCycles, hboundaryArc, hchoice⟩
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    exists_theorem49BoundaryRootSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_direct
      (G := G) ⟨emb, source, by
        simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
          PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
          PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
          hchoice⟩ C₀ hC₀

/-- The live successor-cycle shell plus canonical witness choice already reaches the split
annulus witness-ownership surface itself, before any theorem-4.9 coloring algebra is used. -/
theorem
    admitsPlanarBoundaryAnnulusWitnessAssignment_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_canonicalWitnessChoice_direct
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          Nonempty
            (PlanarBoundaryCanonicalWitnessChoice
              boundaryData.toPlanarBoundaryAnnulusBoundaryData)) :
    AdmitsPlanarBoundaryAnnulusWitnessAssignment G := by
  rcases hG with ⟨emb, boundaryData, dartCycles, hboundaryArc, hchoice⟩
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    admitsPlanarBoundaryAnnulusWitnessAssignment_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_direct
      ⟨emb, source, by
        simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
          PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
          PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
          hchoice⟩

/-- Non-vacuous theorem-4.9 synthesis endpoint from the successor-cycle source shell plus
canonical witness choice and a nonempty purified endpoint carrier. -/
theorem
    exists_theorem49BoundaryRootNonemptySynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_canonicalWitnessChoice_with_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          Nonempty
            (PlanarBoundaryCanonicalWitnessChoice
              boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
          (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptySynthesis emb C₀ := by
  rcases hG with ⟨emb, boundaryData, dartCycles, hboundaryArc, hchoice, hCarrier⟩
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    exists_theorem49BoundaryRootNonemptySynthesis_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_with_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_direct
      (G := G) ⟨emb, source, by
        simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
          PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
          PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
          hchoice, hCarrier⟩ C₀ hC₀

/-- Direct theorem-4.9 synthesis endpoint from the successor-cycle source shell plus the local
at-most-one-interior-edge criterion.  This is the route-facing version of the closed-walk
at-most-one theorem: the successor-cycle boundary data supplies the honest source, and the
face-local cardinality package supplies canonical witness choice. -/
theorem
    exists_theorem49BoundaryRootSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
            (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
              (∀ f : AmbientFace emb.faces,
                ((emb.faceBoundary f.1).filter
                    (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                  (1 : ℕ)) ∧
                ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
                  e ∈ emb.faceBoundary f.1 →
                    e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                    e ∈
                      boundaryData.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                        boundaryData.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases hG with
    ⟨emb, boundaryData, dartCycles, hboundaryArc, fallbackEdge, hfallback,
      hatMost, hboundaryRest⟩
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    exists_theorem49BoundaryRootSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_direct
      (G := G) ⟨emb, source, fallbackEdge, hfallback, hatMost, by
        intro f e he hi
        simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
          PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
          PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
          hboundaryRest f he hi⟩ C₀ hC₀

/-- Direct theorem-4.9 synthesis endpoint from the successor-cycle source shell with only the
facewise cardinal at-most-one interior-edge condition.  The successor-cycle fields lower to an
honest closed-walk source, whose facial closed walks supply fallback edges and whose annulus split
supplies the non-interior boundary-rest clause. -/
theorem
    exists_theorem49BoundaryRootSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_facewiseAtMostOneInteriorEdge_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          ∀ f : AmbientFace emb.faces,
            ((emb.faceBoundary f.1).filter
                (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
              (1 : ℕ))
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases hG with ⟨emb, boundaryData, dartCycles, hboundaryArc, hatMost⟩
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    exists_theorem49BoundaryRootSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge_direct
      (G := G) ⟨emb, source, hatMost⟩ C₀ hC₀

/-- The live successor-cycle shell also reaches the split annulus witness-ownership surface from
the facewise cardinal at-most-one condition alone.  The successor-cycle data lower to the honest
closed-walk source, which supplies the fallback facial edge and the ambient boundary-rest clause. -/
theorem
    admitsPlanarBoundaryAnnulusWitnessAssignment_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_facewiseAtMostOneInteriorEdge_direct
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          ∀ f : AmbientFace emb.faces,
            ((emb.faceBoundary f.1).filter
                (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
              (1 : ℕ)) :
    AdmitsPlanarBoundaryAnnulusWitnessAssignment G := by
  rcases hG with ⟨emb, boundaryData, dartCycles, hboundaryArc, hAtMost⟩
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    admitsPlanarBoundaryAnnulusWitnessAssignment_of_exists_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge_direct
      ⟨emb, source, hAtMost⟩

/-- Non-vacuous theorem-4.9 synthesis from the route-facing successor-cycle source shell with the
local at-most-one criterion.  The extra hypothesis is exactly nonemptiness of the purified
selected-boundary interior-edge endpoint carrier on the same embedding. -/
theorem
    exists_theorem49BoundaryRootNonemptySynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace_with_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
            (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
              (∀ f : AmbientFace emb.faces,
                ((emb.faceBoundary f.1).filter
                    (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                  (1 : ℕ)) ∧
                (∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
                  e ∈ emb.faceBoundary f.1 →
                    e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                    e ∈
                      boundaryData.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                        boundaryData.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary) ∧
                  (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptySynthesis emb C₀ := by
  rcases hG with
    ⟨emb, boundaryData, dartCycles, hboundaryArc, fallbackEdge, hfallback,
      hatMost, hboundaryRest, hCarrier⟩
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    exists_theorem49BoundaryRootNonemptySynthesis_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_with_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_direct
      (G := G) ⟨emb, source, fallbackEdge, hfallback, hatMost, by
        intro f e he hi
        simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
          PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
          PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
          hboundaryRest f he hi, hCarrier⟩ C₀ hC₀

/-- Non-vacuous theorem-4.9 synthesis endpoint from the successor-cycle source shell with only the
facewise cardinal at-most-one condition, plus the existing nonempty purified endpoint carrier.
The explicit fallback and boundary-rest fields are supplied by the lowered honest source. -/
theorem
    exists_theorem49BoundaryRootNonemptySynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_facewiseAtMostOneInteriorEdge_with_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (∀ f : AmbientFace emb.faces,
            ((emb.faceBoundary f.1).filter
                (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
              (1 : ℕ)) ∧
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptySynthesis emb C₀ := by
  rcases hG with ⟨emb, boundaryData, dartCycles, hboundaryArc, hatMost, hCarrier⟩
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    exists_theorem49BoundaryRootNonemptySynthesis_of_exists_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge_with_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_direct
      (G := G) ⟨emb, source, hatMost, hCarrier⟩ C₀ hC₀

/-- Direct theorem-4.9 synthesis endpoint from the successor-cycle source shell plus a
same-boundary one-collar annulus geometry.  This keeps the source-boundary equality explicit,
then reuses the closed-walk one-collar synthesis bridge. -/
theorem
    exists_theorem49BoundaryRootSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases hG with ⟨emb, boundaryData, dartCycles, data, hboundaryArc, hnum, hboundary⟩
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    exists_theorem49BoundaryRootSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData
      (G := G) ⟨emb, source, data, hnum, by
        simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
          PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
          PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
          hboundary⟩ C₀ hC₀

/-- Non-vacuous theorem-4.9 synthesis endpoint from the successor-cycle source shell plus
same-boundary one-collar geometry and a nonempty purified endpoint carrier. -/
theorem
    exists_theorem49BoundaryRootNonemptySynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData ∧
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptySynthesis emb C₀ := by
  rcases hG with
    ⟨emb, boundaryData, dartCycles, data, hboundaryArc, hnum, hboundary, hCarrier⟩
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    exists_theorem49BoundaryRootNonemptySynthesis_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_direct
      (G := G) ⟨emb, source, data, hnum, by
        simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
          PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
          PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
          hboundary, hCarrier⟩ C₀ hC₀

/-- Route-facing successor-cycle version of the canonical Definition 4.8 raw generator-spanning
bridge from canonical witness choice, through the height-ordered repaired-witness route.  The
successor-cycle fields lower to the honest closed-walk source, and the remaining target-side
obligations are exactly the same subspace, containment, and boundary-zero interpretation used by
the closed-walk theorem. -/
theorem
    exists_theorem49_kempeGeneratorSubspace_spanning_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_canonicalWitnessChoice_heightOrdered_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          Nonempty
            (PlanarBoundaryCanonicalWitnessChoice
              boundaryData.toPlanarBoundaryAnnulusBoundaryData))
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (differenceSubspaceOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryHeightOrderedFacePeelWitnessData emb → Submodule F2 (G.edgeSet → Color))
    (hle : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        kempeClosureGeneratorSubspace emb.faceBoundary C₀ ≤ differenceSubspaceOf emb data)
    (hboundary : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        ∀ ⦃z : G.edgeSet → Color⦄,
          z ∈ differenceSubspaceOf emb data →
            ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        kempeClosureGeneratorSubspace emb.faceBoundary C₀ = differenceSubspaceOf emb data := by
  rcases hG with ⟨emb, boundaryData, dartCycles, hboundaryArc, hchoice⟩
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    exists_theorem49_kempeGeneratorSubspace_spanning_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_heightOrdered_direct
      (G := G) ⟨emb, source, by
        simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
          PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
          PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
          hchoice⟩ C₀ hC₀ differenceSubspaceOf hle hboundary

/-- Collar-layer version of the successor-cycle canonical-witness raw generator-spanning bridge. -/
theorem
    exists_theorem49_kempeGeneratorSubspace_spanning_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_canonicalWitnessChoice_collarLayer_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          Nonempty
            (PlanarBoundaryCanonicalWitnessChoice
              boundaryData.toPlanarBoundaryAnnulusBoundaryData))
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (differenceSubspaceOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryCollarLayerFacePeelWitnessData emb → Submodule F2 (G.edgeSet → Color))
    (hle : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        kempeClosureGeneratorSubspace emb.faceBoundary C₀ ≤ differenceSubspaceOf emb data)
    (hboundary : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        ∀ ⦃z : G.edgeSet → Color⦄,
          z ∈ differenceSubspaceOf emb data →
            ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        kempeClosureGeneratorSubspace emb.faceBoundary C₀ = differenceSubspaceOf emb data := by
  rcases hG with ⟨emb, boundaryData, dartCycles, hboundaryArc, hchoice⟩
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    exists_theorem49_kempeGeneratorSubspace_spanning_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_collarLayer_direct
      (G := G) ⟨emb, source, by
        simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
          PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
          PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
          hchoice⟩ C₀ hC₀ differenceSubspaceOf hle hboundary

/-- Route-facing successor-cycle version of the raw generator-spanning bridge from the local
at-most-one source criterion, through height-ordered witness data. -/
theorem
    exists_theorem49_kempeGeneratorSubspace_spanning_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace_heightOrdered_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
            (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
              (∀ f : AmbientFace emb.faces,
                ((emb.faceBoundary f.1).filter
                    (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                  (1 : ℕ)) ∧
                ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
                  e ∈ emb.faceBoundary f.1 →
                    e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                    e ∈
                      boundaryData.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                        boundaryData.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (differenceSubspaceOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryHeightOrderedFacePeelWitnessData emb → Submodule F2 (G.edgeSet → Color))
    (hle : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        kempeClosureGeneratorSubspace emb.faceBoundary C₀ ≤ differenceSubspaceOf emb data)
    (hboundary : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        ∀ ⦃z : G.edgeSet → Color⦄,
          z ∈ differenceSubspaceOf emb data →
            ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        kempeClosureGeneratorSubspace emb.faceBoundary C₀ = differenceSubspaceOf emb data := by
  rcases hG with
    ⟨emb, boundaryData, dartCycles, hboundaryArc, fallbackEdge, hfallback,
      hatMost, hboundaryRest⟩
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    exists_theorem49_kempeGeneratorSubspace_spanning_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_heightOrdered_direct
      (G := G) ⟨emb, source, fallbackEdge, hfallback, hatMost, by
        intro f e he hi
        simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
          PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
          PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
          hboundaryRest f he hi⟩ C₀ hC₀ differenceSubspaceOf hle hboundary

/-- Collar-layer version of the successor-cycle at-most-one raw generator-spanning bridge. -/
theorem
    exists_theorem49_kempeGeneratorSubspace_spanning_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace_collarLayer_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
            (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
              (∀ f : AmbientFace emb.faces,
                ((emb.faceBoundary f.1).filter
                    (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                  (1 : ℕ)) ∧
                ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
                  e ∈ emb.faceBoundary f.1 →
                    e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                    e ∈
                      boundaryData.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                        boundaryData.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (differenceSubspaceOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryCollarLayerFacePeelWitnessData emb → Submodule F2 (G.edgeSet → Color))
    (hle : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        kempeClosureGeneratorSubspace emb.faceBoundary C₀ ≤ differenceSubspaceOf emb data)
    (hboundary : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        ∀ ⦃z : G.edgeSet → Color⦄,
          z ∈ differenceSubspaceOf emb data →
            ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        kempeClosureGeneratorSubspace emb.faceBoundary C₀ = differenceSubspaceOf emb data := by
  rcases hG with
    ⟨emb, boundaryData, dartCycles, hboundaryArc, fallbackEdge, hfallback,
      hatMost, hboundaryRest⟩
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    exists_theorem49_kempeGeneratorSubspace_spanning_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_collarLayer_direct
      (G := G) ⟨emb, source, fallbackEdge, hfallback, hatMost, by
        intro f e he hi
        simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
          PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
          PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
          hboundaryRest f he hi⟩ C₀ hC₀ differenceSubspaceOf hle hboundary

/-- Route-facing successor-cycle version of the raw generator-spanning bridge from same-boundary
one-collar source geometry, through height-ordered witness data. -/
theorem
    exists_theorem49_kempeGeneratorSubspace_spanning_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_heightOrdered_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (differenceSubspaceOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryHeightOrderedFacePeelWitnessData emb → Submodule F2 (G.edgeSet → Color))
    (hle : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        kempeClosureGeneratorSubspace emb.faceBoundary C₀ ≤ differenceSubspaceOf emb data)
    (hboundary : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        ∀ ⦃z : G.edgeSet → Color⦄,
          z ∈ differenceSubspaceOf emb data →
            ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        kempeClosureGeneratorSubspace emb.faceBoundary C₀ = differenceSubspaceOf emb data := by
  rcases hG with ⟨emb, boundaryData, dartCycles, data, hboundaryArc, hnum, hboundaryEq⟩
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    exists_theorem49_kempeGeneratorSubspace_spanning_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_heightOrdered_direct
      (G := G) ⟨emb, source, data, hnum, by
        simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
          PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
          PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
          hboundaryEq⟩ C₀ hC₀ differenceSubspaceOf hle hboundary

/-- Collar-layer version of the successor-cycle same-boundary one-collar raw generator-spanning
bridge. -/
theorem
    exists_theorem49_kempeGeneratorSubspace_spanning_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_collarLayer_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (differenceSubspaceOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryCollarLayerFacePeelWitnessData emb → Submodule F2 (G.edgeSet → Color))
    (hle : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        kempeClosureGeneratorSubspace emb.faceBoundary C₀ ≤ differenceSubspaceOf emb data)
    (hboundary : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        ∀ ⦃z : G.edgeSet → Color⦄,
          z ∈ differenceSubspaceOf emb data →
            ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        kempeClosureGeneratorSubspace emb.faceBoundary C₀ = differenceSubspaceOf emb data := by
  rcases hG with ⟨emb, boundaryData, dartCycles, data, hboundaryArc, hnum, hboundaryEq⟩
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    exists_theorem49_kempeGeneratorSubspace_spanning_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_collarLayer_direct
      (G := G) ⟨emb, source, data, hnum, by
        simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
          PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
          PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
          hboundaryEq⟩ C₀ hC₀ differenceSubspaceOf hle hboundary

end Mettapedia.GraphTheory.FourColor
