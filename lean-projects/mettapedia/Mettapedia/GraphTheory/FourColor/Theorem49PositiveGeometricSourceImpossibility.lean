import Mettapedia.GraphTheory.FourColor.Theorem49PositiveGeometricSource
import Mettapedia.GraphTheory.FourColor.Theorem49AtMostOneNonemptyCarrierImpossibility

/-!
# Impossibility of the current positive geometric source packages

The current positive package surfaces combine honest closed-walk facial data, a canonical or
one-collar witness geometry, and a nonempty purified selected-boundary interior-edge carrier.
This file proves that this combination is inconsistent.  A canonical witness choice rules out
two distinct interior edges on any face, hence gives the facewise at-most-one condition; the
existing closed-walk obstruction then forces the purified carrier to be empty.  A same-boundary
one-collar geometry is no escape, because it induces the corresponding canonical witness choice.
-/

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- A canonical facewise witness choice forces at most one interior edge on every face. -/
theorem facewiseAtMostOneInteriorEdge_of_planarBoundaryCanonicalWitnessChoice
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {boundaryData : PlanarBoundaryAnnulusBoundaryData emb}
    (hchoice : Nonempty (PlanarBoundaryCanonicalWitnessChoice boundaryData)) :
    ∀ f : AmbientFace emb.faces,
      ((emb.faceBoundary f.1).filter
        (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1 := by
  intro f
  by_contra hle
  have hgt :
      1 <
        ((emb.faceBoundary f.1).filter
          (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card :=
    Nat.lt_of_not_ge hle
  rw [Finset.one_lt_card] at hgt
  rcases hgt with ⟨e₁, he₁, e₂, he₂, hne⟩
  rcases Finset.mem_filter.1 he₁ with ⟨he₁Face, he₁Interior⟩
  rcases Finset.mem_filter.1 he₂ with ⟨he₂Face, he₂Interior⟩
  exact
    not_nonempty_planarBoundaryCanonicalWitnessChoice_of_exists_two_distinct_interior_edges_on_faceBoundary
      boundaryData
      ⟨f, e₁, he₁Face, e₂, he₂Face, hne, he₁Interior, he₂Interior⟩
      hchoice

/-- Honest closed-walk source data plus a canonical witness choice empties the purified
selected-boundary interior-edge endpoint carrier. -/
theorem selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_of_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hchoice :
      Nonempty
        (PlanarBoundaryCanonicalWitnessChoice
          source.toPlanarBoundaryAnnulusBoundaryData)) :
    selectedBoundaryInteriorEdgeEndpointVertices emb = ∅ := by
  exact
    selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_of_closedWalkEmbeddingData_and_facewiseAtMostOneInteriorEdge
      emb source.closedWalks
      (facewiseAtMostOneInteriorEdge_of_planarBoundaryCanonicalWitnessChoice hchoice)

/-- Canonical witness choice also rules out the named local endpoint witness.  This is the
carrier-collapse theorem above restated on the route's current first-order carrier predicate. -/
theorem not_hasUnblockedInteriorEndpoint_of_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hchoice :
      Nonempty
        (PlanarBoundaryCanonicalWitnessChoice
          source.toPlanarBoundaryAnnulusBoundaryData)) :
    ¬ HasUnblockedInteriorEndpoint emb := by
  intro hEndpoint
  have hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty :=
    (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
      emb).1 hEndpoint
  have hempty :=
    selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_of_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice
      source hchoice
  rw [hempty] at hCarrier
  rcases hCarrier with ⟨v, hv⟩
  simp at hv

/-- A source-preserving one-collar geometry rules out the named local endpoint witness, because
it induces the corresponding canonical witness choice. -/
theorem not_hasUnblockedInteriorEndpoint_of_closedWalkAnnulusBoundarySource_and_oneCollarGeometry_with_sourceBoundaryData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (collar : PlanarBoundaryAnnulusCollarGeometry emb)
    (hnum : collar.numCollars = 1)
    (hboundary :
      collar.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
        source.toPlanarBoundaryAnnulusBoundaryData) :
    ¬ HasUnblockedInteriorEndpoint emb := by
  exact
    not_hasUnblockedInteriorEndpoint_of_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice
      source
      ⟨collar.toPlanarBoundaryCanonicalWitnessChoice_of_numCollars_eq_one hnum hboundary⟩

/-- Live-endpoint form of the canonical-choice obstruction.  Once an honest closed-walk source
has the current unblocked endpoint witness, the necessary two-interior-edge face rules out a
canonical facewise witness choice on the source boundary split. -/
theorem not_nonempty_planarBoundaryCanonicalWitnessChoice_of_closedWalkAnnulusBoundarySource_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    ¬ Nonempty
      (PlanarBoundaryCanonicalWitnessChoice
        source.toPlanarBoundaryAnnulusBoundaryData) := by
  intro hchoice
  exact
    not_hasUnblockedInteriorEndpoint_of_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice
      source hchoice hEndpoint

/-- Live-endpoint form of the source-preserving one-collar obstruction.  A one-collar geometry
with the same boundary split would induce the canonical witness choice forbidden above. -/
theorem not_exists_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_of_closedWalkAnnulusBoundarySource_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    ¬ ∃ collar : PlanarBoundaryAnnulusCollarGeometry emb,
      collar.numCollars = 1 ∧
        collar.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
          source.toPlanarBoundaryAnnulusBoundaryData := by
  rintro ⟨collar, hnum, hboundary⟩
  exact
    not_hasUnblockedInteriorEndpoint_of_closedWalkAnnulusBoundarySource_and_oneCollarGeometry_with_sourceBoundaryData
      source collar hnum hboundary hEndpoint

/-- Closed-walk source data, canonical witness choice, and nonempty purified carrier cannot
coexist on one embedding. -/
theorem not_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {G : SimpleGraph V} (emb : PlaneEmbeddingWithBoundary G) :
    ¬ ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      Nonempty
        (PlanarBoundaryCanonicalWitnessChoice
          source.toPlanarBoundaryAnnulusBoundaryData) ∧
        (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty := by
  rintro ⟨source, hchoice, hCarrier⟩
  have hempty :=
    selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_of_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice
      source hchoice
  rw [hempty] at hCarrier
  rcases hCarrier with ⟨v, hv⟩
  simp at hv

/-- Same-boundary one-collar geometry also cannot coexist with closed-walk source data and a
nonempty purified carrier, because the one-collar geometry induces a canonical witness choice. -/
theorem not_exists_closedWalkAnnulusBoundarySource_and_oneCollarGeometry_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {G : SimpleGraph V} (emb : PlaneEmbeddingWithBoundary G) :
    ¬ ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ collar : PlanarBoundaryAnnulusCollarGeometry emb,
        collar.numCollars = 1 ∧
          collar.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
            source.toPlanarBoundaryAnnulusBoundaryData ∧
          (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty := by
  rintro ⟨source, collar, hnum, hboundary, hCarrier⟩
  have hchoice :
      Nonempty
        (PlanarBoundaryCanonicalWitnessChoice
          source.toPlanarBoundaryAnnulusBoundaryData) :=
    ⟨collar.toPlanarBoundaryCanonicalWitnessChoice_of_numCollars_eq_one hnum hboundary⟩
  exact
    not_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
      emb ⟨source, hchoice, hCarrier⟩

/-- The closed-walk canonical positive package is structurally inconsistent on every embedding. -/
theorem not_theorem49ClosedWalkCanonicalPositiveGeometryOn_of_any_embedding
    {G : SimpleGraph V} (emb : PlaneEmbeddingWithBoundary G) :
    ¬ Theorem49ClosedWalkCanonicalPositiveGeometryOn emb := by
  rintro ⟨source, hchoice, hCarrier⟩
  exact
    not_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
      emb ⟨source, hchoice, hCarrier⟩

/-- The closed-walk one-collar positive package is structurally inconsistent on every embedding. -/
theorem not_theorem49ClosedWalkOneCollarPositiveGeometryOn_of_any_embedding
    {G : SimpleGraph V} (emb : PlaneEmbeddingWithBoundary G) :
    ¬ Theorem49ClosedWalkOneCollarPositiveGeometryOn emb := by
  rintro ⟨source, collar, hnum, hboundary, hCarrier⟩
  exact
    not_exists_closedWalkAnnulusBoundarySource_and_oneCollarGeometry_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
      emb ⟨source, collar, hnum, hboundary, hCarrier⟩

/-- The successor-cycle canonical positive package is structurally inconsistent on every
embedding after lowering successor-cycle data to the honest closed-walk source surface. -/
theorem not_theorem49SuccessorCycleCanonicalPositiveGeometryOn_of_any_embedding
    {G : SimpleGraph V} (emb : PlaneEmbeddingWithBoundary G) :
    ¬ Theorem49SuccessorCycleCanonicalPositiveGeometryOn emb := by
  rintro ⟨boundaryData, dartCycles, hselected, hchoice, hCarrier⟩
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hselected
  have hchoiceSource :
      Nonempty
        (PlanarBoundaryCanonicalWitnessChoice
          source.toPlanarBoundaryAnnulusBoundaryData) := by
    simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
      PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
      PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
      hchoice
  exact
    not_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
      emb ⟨source, hchoiceSource, hCarrier⟩

/-- The successor-cycle one-collar positive package is structurally inconsistent on every
embedding after lowering successor-cycle data to the honest closed-walk source surface. -/
theorem not_theorem49SuccessorCycleOneCollarPositiveGeometryOn_of_any_embedding
    {G : SimpleGraph V} (emb : PlaneEmbeddingWithBoundary G) :
    ¬ Theorem49SuccessorCycleOneCollarPositiveGeometryOn emb := by
  rintro ⟨boundaryData, dartCycles, collar, hselected, hnum, hboundary, hCarrier⟩
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hselected
  have hboundarySource :
      collar.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
        source.toPlanarBoundaryAnnulusBoundaryData := by
    simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
      PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
      PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
      hboundary
  exact
    not_exists_closedWalkAnnulusBoundarySource_and_oneCollarGeometry_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
      emb ⟨source, collar, hnum, hboundarySource, hCarrier⟩

/-- None of the current graph-level positive geometric source package structures can be
inhabited. -/
theorem not_nonempty_currentTheorem49PositiveGeometricSourcePackages
    {G : SimpleGraph V} :
    ¬ Nonempty (Theorem49ClosedWalkCanonicalPositiveGeometry G) ∧
      ¬ Nonempty (Theorem49ClosedWalkOneCollarPositiveGeometry G) ∧
      ¬ Nonempty (Theorem49SuccessorCycleCanonicalPositiveGeometry G) ∧
      ¬ Nonempty (Theorem49SuccessorCycleOneCollarPositiveGeometry G) := by
  constructor
  · rintro ⟨geom⟩
    exact not_theorem49ClosedWalkCanonicalPositiveGeometryOn_of_any_embedding geom.emb geom.on
  constructor
  · rintro ⟨geom⟩
    exact not_theorem49ClosedWalkOneCollarPositiveGeometryOn_of_any_embedding geom.emb geom.on
  constructor
  · rintro ⟨geom⟩
    exact not_theorem49SuccessorCycleCanonicalPositiveGeometryOn_of_any_embedding geom.emb geom.on
  · rintro ⟨geom⟩
    exact not_theorem49SuccessorCycleOneCollarPositiveGeometryOn_of_any_embedding geom.emb geom.on

end Mettapedia.GraphTheory.FourColor
