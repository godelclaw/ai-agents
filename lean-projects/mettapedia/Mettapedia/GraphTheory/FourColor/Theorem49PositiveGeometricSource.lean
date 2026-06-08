import Mettapedia.GraphTheory.FourColor.PlanarBoundaryClosedWalkSourceProjection

/-!
# Positive geometric source packages for Theorem 4.9

This file records the current constructive source-side targets for the non-vacuous
theorem-4.9 route.  The packages keep the geometric hypotheses explicit and then lower them to
the same-embedding `Theorem49BoundaryRootNonemptyProjectedSynthesis` endpoint.
-/

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- Fixed-embedding form of the closed-walk canonical positive package.  This is useful for
calibrating concrete embeddings before existentially packaging the graph-level source. -/
def Theorem49ClosedWalkCanonicalPositiveGeometryOn {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) : Prop :=
  ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
    Nonempty
      (PlanarBoundaryCanonicalWitnessChoice
        source.toPlanarBoundaryAnnulusBoundaryData) ∧
      (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty

/-- A fixed-embedding closed-walk canonical package gives the positive projected synthesis
endpoint on that same embedding. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkCanonicalPositiveGeometryOn
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ClosedWalkCanonicalPositiveGeometryOn emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases geom with ⟨source, hchoice, hCarrier⟩
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_direct
      source hchoice hCarrier C0 hC0

/-- Honest closed-walk source data with a canonical witness choice and a nonempty purified
selected-boundary carrier.  This is the direct closed-walk positive source package for the
current non-vacuous projected synthesis endpoint. -/
structure Theorem49ClosedWalkCanonicalPositiveGeometry (G : SimpleGraph V) where
  emb : PlaneEmbeddingWithBoundary G
  source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb
  canonicalWitnessChoice :
    Nonempty
      (PlanarBoundaryCanonicalWitnessChoice
        source.toPlanarBoundaryAnnulusBoundaryData)
  carrier_nonempty : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty

namespace Theorem49ClosedWalkCanonicalPositiveGeometry

/-- Forget the graph-level package to its fixed-embedding predicate. -/
theorem on
    {G : SimpleGraph V} (geom : Theorem49ClosedWalkCanonicalPositiveGeometry G) :
    Theorem49ClosedWalkCanonicalPositiveGeometryOn geom.emb := by
  exact ⟨geom.source, geom.canonicalWitnessChoice, geom.carrier_nonempty⟩

/-- The graph-level package is exactly existence of the fixed-embedding predicate. -/
theorem nonempty_iff_exists_on
    {G : SimpleGraph V} :
    Nonempty (Theorem49ClosedWalkCanonicalPositiveGeometry G) ↔
      ∃ emb : PlaneEmbeddingWithBoundary G,
        Theorem49ClosedWalkCanonicalPositiveGeometryOn emb := by
  constructor
  · rintro ⟨geom⟩
    exact ⟨geom.emb, geom.on⟩
  · rintro ⟨emb, source, hchoice, hCarrier⟩
    exact
      ⟨{ emb := emb,
          source := source,
          canonicalWitnessChoice := hchoice,
          carrier_nonempty := hCarrier }⟩

/-- The closed-walk canonical positive package reaches the current non-vacuous projected
theorem-4.9 synthesis endpoint. -/
theorem exists_nonemptyProjectedSynthesis
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49ClosedWalkCanonicalPositiveGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 :=
  exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_with_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_direct
    ⟨geom.emb, geom.source, geom.canonicalWitnessChoice, geom.carrier_nonempty⟩ C0 hC0

end Theorem49ClosedWalkCanonicalPositiveGeometry

/-- Fixed-embedding form of the closed-walk same-boundary one-collar positive package. -/
def Theorem49ClosedWalkOneCollarPositiveGeometryOn {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) : Prop :=
  ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
    ∃ collar : PlanarBoundaryAnnulusCollarGeometry emb,
      collar.numCollars = 1 ∧
        collar.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
          source.toPlanarBoundaryAnnulusBoundaryData ∧
        (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty

/-- A fixed-embedding same-boundary one-collar package gives the positive projected synthesis
endpoint on that same embedding. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkOneCollarPositiveGeometryOn
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ClosedWalkOneCollarPositiveGeometryOn emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases geom with ⟨source, collar, hnum, hboundary, hCarrier⟩
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_direct
      source collar hnum hboundary hCarrier C0 hC0

/-- Honest closed-walk source data with a one-collar geometry preserving the source boundary
split and a nonempty purified selected-boundary carrier.  This is the collar-geometric positive
source package that avoids relying on an arbitrary weak collar. -/
structure Theorem49ClosedWalkOneCollarPositiveGeometry (G : SimpleGraph V) where
  emb : PlaneEmbeddingWithBoundary G
  source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb
  collar : PlanarBoundaryAnnulusCollarGeometry emb
  collar_numCollars : collar.numCollars = 1
  collar_boundaryData :
    collar.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
      source.toPlanarBoundaryAnnulusBoundaryData
  carrier_nonempty : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty

namespace Theorem49ClosedWalkOneCollarPositiveGeometry

/-- Forget the graph-level one-collar package to its fixed-embedding predicate. -/
theorem on
    {G : SimpleGraph V} (geom : Theorem49ClosedWalkOneCollarPositiveGeometry G) :
    Theorem49ClosedWalkOneCollarPositiveGeometryOn geom.emb := by
  exact
    ⟨geom.source, geom.collar, geom.collar_numCollars, geom.collar_boundaryData,
      geom.carrier_nonempty⟩

/-- The graph-level one-collar package is exactly existence of the fixed-embedding predicate. -/
theorem nonempty_iff_exists_on
    {G : SimpleGraph V} :
    Nonempty (Theorem49ClosedWalkOneCollarPositiveGeometry G) ↔
      ∃ emb : PlaneEmbeddingWithBoundary G,
        Theorem49ClosedWalkOneCollarPositiveGeometryOn emb := by
  constructor
  · rintro ⟨geom⟩
    exact ⟨geom.emb, geom.on⟩
  · rintro ⟨emb, source, collar, hnum, hboundary, hCarrier⟩
    exact
      ⟨{ emb := emb,
          source := source,
          collar := collar,
          collar_numCollars := hnum,
          collar_boundaryData := hboundary,
          carrier_nonempty := hCarrier }⟩

/-- The closed-walk same-boundary one-collar positive package reaches the current non-vacuous
projected theorem-4.9 synthesis endpoint. -/
theorem exists_nonemptyProjectedSynthesis
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49ClosedWalkOneCollarPositiveGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 :=
  exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_direct
    ⟨geom.emb, geom.source, geom.collar, geom.collar_numCollars, geom.collar_boundaryData,
      geom.carrier_nonempty⟩
    C0 hC0

end Theorem49ClosedWalkOneCollarPositiveGeometry

/-- Fixed-embedding form of the route-facing successor-cycle canonical positive package. -/
def Theorem49SuccessorCycleCanonicalPositiveGeometryOn {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) : Prop :=
  ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
    ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      (∀ f : AmbientFace emb.faces,
        (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        Nonempty
          (PlanarBoundaryCanonicalWitnessChoice
            boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
          (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty

/-- A fixed-embedding successor-cycle canonical package gives the positive projected synthesis
endpoint on that same embedding, after lowering the successor-cycle data to the closed-walk
source surface. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_successorCycleCanonicalPositiveGeometryOn
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleCanonicalPositiveGeometryOn emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases geom with ⟨boundaryData, dartCycles, hselected, hchoice, hCarrier⟩
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hselected
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_direct
      source
      (by
        simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
          PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
          PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
          hchoice)
      hCarrier C0 hC0

/-- Route-facing successor-cycle data with canonical witness choice and a nonempty purified
selected-boundary carrier.  The successor-cycle shell is lowered to the honest closed-walk
source package before applying the projected synthesis endpoint. -/
structure Theorem49SuccessorCycleCanonicalPositiveGeometry (G : SimpleGraph V) where
  emb : PlaneEmbeddingWithBoundary G
  boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb
  dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb
  selectedBoundaryArc :
    ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f
  canonicalWitnessChoice :
    Nonempty
      (PlanarBoundaryCanonicalWitnessChoice
        boundaryData.toPlanarBoundaryAnnulusBoundaryData)
  carrier_nonempty : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty

namespace Theorem49SuccessorCycleCanonicalPositiveGeometry

/-- Forget the graph-level successor-cycle canonical package to its fixed-embedding predicate. -/
theorem on
    {G : SimpleGraph V} (geom : Theorem49SuccessorCycleCanonicalPositiveGeometry G) :
    Theorem49SuccessorCycleCanonicalPositiveGeometryOn geom.emb := by
  exact
    ⟨geom.boundaryData, geom.dartCycles, geom.selectedBoundaryArc,
      geom.canonicalWitnessChoice, geom.carrier_nonempty⟩

/-- The graph-level successor-cycle canonical package is exactly existence of its fixed-embedding
predicate. -/
theorem nonempty_iff_exists_on
    {G : SimpleGraph V} :
    Nonempty (Theorem49SuccessorCycleCanonicalPositiveGeometry G) ↔
      ∃ emb : PlaneEmbeddingWithBoundary G,
        Theorem49SuccessorCycleCanonicalPositiveGeometryOn emb := by
  constructor
  · rintro ⟨geom⟩
    exact ⟨geom.emb, geom.on⟩
  · rintro ⟨emb, boundaryData, dartCycles, hselected, hchoice, hCarrier⟩
    exact
      ⟨{ emb := emb,
          boundaryData := boundaryData,
          dartCycles := dartCycles,
          selectedBoundaryArc := hselected,
          canonicalWitnessChoice := hchoice,
          carrier_nonempty := hCarrier }⟩

/-- Lower the route-facing successor-cycle package to the honest closed-walk positive package. -/
def toClosedWalkCanonicalPositiveGeometry
    {G : SimpleGraph V}
    (geom : Theorem49SuccessorCycleCanonicalPositiveGeometry G) :
    Theorem49ClosedWalkCanonicalPositiveGeometry G where
  emb := geom.emb
  source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      geom.boundaryData geom.dartCycles geom.selectedBoundaryArc
  canonicalWitnessChoice := by
    simpa [PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
      PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
      PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData]
      using geom.canonicalWitnessChoice
  carrier_nonempty := geom.carrier_nonempty

/-- The successor-cycle canonical positive package reaches the current non-vacuous projected
theorem-4.9 synthesis endpoint. -/
theorem exists_nonemptyProjectedSynthesis
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49SuccessorCycleCanonicalPositiveGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 :=
  Theorem49ClosedWalkCanonicalPositiveGeometry.exists_nonemptyProjectedSynthesis
    geom.toClosedWalkCanonicalPositiveGeometry C0 hC0

end Theorem49SuccessorCycleCanonicalPositiveGeometry

/-- Fixed-embedding form of the route-facing successor-cycle same-boundary one-collar package. -/
def Theorem49SuccessorCycleOneCollarPositiveGeometryOn {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) : Prop :=
  ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
    ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ collar : PlanarBoundaryAnnulusCollarGeometry emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          collar.numCollars = 1 ∧
            collar.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData ∧
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty

/-- A fixed-embedding successor-cycle same-boundary one-collar package gives the positive
projected synthesis endpoint on that same embedding, after lowering the successor-cycle data to
the closed-walk source surface. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_successorCycleOneCollarPositiveGeometryOn
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleOneCollarPositiveGeometryOn emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases geom with
    ⟨boundaryData, dartCycles, collar, hselected, hnum, hboundary, hCarrier⟩
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hselected
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_direct
      source collar hnum
      (by
        simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
          PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
          PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
          hboundary)
      hCarrier C0 hC0

/-- Route-facing successor-cycle data with same-boundary one-collar geometry and a nonempty
purified selected-boundary carrier.  This is the current explicit annulus-construction target
for the positive non-vacuous route. -/
structure Theorem49SuccessorCycleOneCollarPositiveGeometry (G : SimpleGraph V) where
  emb : PlaneEmbeddingWithBoundary G
  boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb
  dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb
  collar : PlanarBoundaryAnnulusCollarGeometry emb
  selectedBoundaryArc :
    ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f
  collar_numCollars : collar.numCollars = 1
  collar_boundaryData :
    collar.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
      boundaryData.toPlanarBoundaryAnnulusBoundaryData
  carrier_nonempty : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty

namespace Theorem49SuccessorCycleOneCollarPositiveGeometry

/-- Forget the graph-level successor-cycle one-collar package to its fixed-embedding predicate. -/
theorem on
    {G : SimpleGraph V} (geom : Theorem49SuccessorCycleOneCollarPositiveGeometry G) :
    Theorem49SuccessorCycleOneCollarPositiveGeometryOn geom.emb := by
  exact
    ⟨geom.boundaryData, geom.dartCycles, geom.collar, geom.selectedBoundaryArc,
      geom.collar_numCollars, geom.collar_boundaryData, geom.carrier_nonempty⟩

/-- The graph-level successor-cycle one-collar package is exactly existence of its
fixed-embedding predicate. -/
theorem nonempty_iff_exists_on
    {G : SimpleGraph V} :
    Nonempty (Theorem49SuccessorCycleOneCollarPositiveGeometry G) ↔
      ∃ emb : PlaneEmbeddingWithBoundary G,
        Theorem49SuccessorCycleOneCollarPositiveGeometryOn emb := by
  constructor
  · rintro ⟨geom⟩
    exact ⟨geom.emb, geom.on⟩
  · rintro ⟨emb, boundaryData, dartCycles, collar, hselected, hnum, hboundary, hCarrier⟩
    exact
      ⟨{ emb := emb,
          boundaryData := boundaryData,
          dartCycles := dartCycles,
          collar := collar,
          selectedBoundaryArc := hselected,
          collar_numCollars := hnum,
          collar_boundaryData := hboundary,
          carrier_nonempty := hCarrier }⟩

/-- Lower the route-facing successor-cycle one-collar package to the honest closed-walk positive
package. -/
def toClosedWalkOneCollarPositiveGeometry
    {G : SimpleGraph V}
    (geom : Theorem49SuccessorCycleOneCollarPositiveGeometry G) :
    Theorem49ClosedWalkOneCollarPositiveGeometry G where
  emb := geom.emb
  source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      geom.boundaryData geom.dartCycles geom.selectedBoundaryArc
  collar := geom.collar
  collar_numCollars := geom.collar_numCollars
  collar_boundaryData := by
    simpa [PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
      PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
      PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData]
      using geom.collar_boundaryData
  carrier_nonempty := geom.carrier_nonempty

/-- The successor-cycle same-boundary one-collar positive package reaches the current
non-vacuous projected theorem-4.9 synthesis endpoint. -/
theorem exists_nonemptyProjectedSynthesis
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49SuccessorCycleOneCollarPositiveGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 :=
  Theorem49ClosedWalkOneCollarPositiveGeometry.exists_nonemptyProjectedSynthesis
    geom.toClosedWalkOneCollarPositiveGeometry C0 hC0

end Theorem49SuccessorCycleOneCollarPositiveGeometry

end Mettapedia.GraphTheory.FourColor
