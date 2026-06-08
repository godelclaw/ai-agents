import Mettapedia.GraphTheory.FourColor.Theorem49HonestSourceConnectivityInvestigation
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryAnnulusHonestGeometryRegression
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryAnnulusHonestWitnessRegression
import Mettapedia.GraphTheory.FourColor.PlanarBoundaryClosedWalkSource

/-!
# Honest sources and arbitrary collars do not force previous-boundary witness

This file records the repaired status of the previous-boundary witness question.  For a fixed
weak collar geometry, extending that very collar to the repaired surface is exactly the
`WitnessOnCurrentBoundary` obligation.  A connected chained-diamonds source then shows that an
honest closed-walk source, even with source-side at-most-one and canonical witness data, does not
force this obligation for a separately supplied weak two-collar geometry.

## Background

From the investigation documented in `Theorem49HonestSourceConnectivityInvestigation.lean`:
- The `counterCollarGeometry` obstruction (which has collar geometry but violates previous-boundary
  witness) cannot support honest sources because its underlying graph is disconnected
- Honest sources require facial closed walks, which require graph connectivity

From `Theorem49PlanarBoundaryAnnulusHonestWitnessRegression.lean`:
- The `sharedInteriorPair` model shows that honest sources alone do NOT force previous-boundary
  witness (it has honest source but no collar geometry at all)

The live positive route is therefore narrower: build the one-collar geometry from the source-side
canonical witness choice, or carry `WitnessOnCurrentBoundary` explicitly for the supplied collar.

-/

namespace Mettapedia.GraphTheory.FourColor

open Theorem49PlanarBoundaryAnnulusWitnessRegression
open Theorem49PlanarBoundaryAnnulusHonestGeometryRegression
open Theorem49PlanarBoundaryAnnulusHonestWitnessRegression

variable {V : Type*} [DecidableEq V]

/-!
## Preliminary observations

Let's first establish what we know about the counterexample and positive examples.
-/

/-- The known counterexample to "collar geometry → previous-boundary witness" cannot carry
honest sources (proved in `Theorem49HonestSourceConnectivityInvestigation.lean`). -/
example : ¬ Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource counterEmbedding) :=
  not_admits_honestSource_counterCollarGeometry

/-- The sharedInteriorPair model has honest source but no collar geometry, so it doesn't help
us understand the honest source + collar geometry combination. -/
example :
    Nonempty
      (PlanarBoundaryClosedWalkAnnulusBoundarySource
        sharedInteriorPairAnnulusEmbedding) :=
  ⟨sharedInteriorPairClosedWalkAnnulusBoundarySource⟩

example :
    ¬ Nonempty
        (PlanarBoundaryAnnulusCollarGeometry
          sharedInteriorPairAnnulusEmbedding) :=
  not_nonempty_planarBoundaryAnnulusCollarGeometry_sharedInteriorPair

/-!
## A connected honest-source counterexample to the naive implication

The closed-walk source does not constrain an arbitrary weak collar geometry to use the same
outer/inner split extracted from that source.  On the existing connected chained-diamonds source,
we can choose a two-collar geometry whose terminal triangular face chooses a selected boundary
edge as its witness.  The weak collar fields accept this because the other two selected boundary
edges lie on the terminal inner ambient boundary; the repaired previous/current-boundary witness
condition rejects it because the witness is not on the previous intermediate boundary `Γ₁`.
-/

def chainedDiamondsBadTwoCollarOuterAmbientBoundary :
    Finset chainedDiamondsWithTriangleGraph.edgeSet :=
  {cdt02, cdt13, cdt23, cdt35, cdt34, cdt01}

def chainedDiamondsBadTwoCollarInnerAmbientBoundary :
    Finset chainedDiamondsWithTriangleGraph.edgeSet :=
  {cdt46, cdt56, cdt89, cdt97, cdt78}

def chainedDiamondsBadTwoCollarBoundaryData :
    PlanarBoundaryAnnulusBoundaryData chainedDiamondsWithTriangleEmbedding := by
  refine
    { outerAmbientBoundary := chainedDiamondsBadTwoCollarOuterAmbientBoundary
      innerAmbientBoundary := chainedDiamondsBadTwoCollarInnerAmbientBoundary
      houterAmbientBoundaryNonempty := by decide
      hinnerAmbientBoundaryNonempty := by decide
      houterAmbientBoundarySubset := by decide
      hinnerAmbientBoundarySubset := by decide
      hambientBoundaryCover := by decide
      hambientBoundaryDisjoint := by decide }

def chainedDiamondsBadTwoCollarFaces :
    Fin 2 → Finset (AmbientFace chainedDiamondsWithTriangleEmbedding.faces)
  | ⟨0, _⟩ => {chainedDiamondsFace0, chainedDiamondsFace1, chainedDiamondsFace2}
  | ⟨1, _⟩ => {chainedDiamondsFace3, chainedDiamondsFace4}

def chainedDiamondsBadTwoCollarBoundaryCycle :
    Fin 3 → Finset chainedDiamondsWithTriangleGraph.edgeSet
  | ⟨0, _⟩ => chainedDiamondsBadTwoCollarOuterAmbientBoundary
  | ⟨1, _⟩ => {cdt45}
  | ⟨2, _⟩ => chainedDiamondsBadTwoCollarInnerAmbientBoundary

def chainedDiamondsBadTwoCollarDecomposition :
    PlanarBoundaryAnnulusDecomposition chainedDiamondsWithTriangleEmbedding := by
  refine
    { toPlanarBoundaryAnnulusBoundaryData := chainedDiamondsBadTwoCollarBoundaryData
      numCollars := 2
      collarFaces := chainedDiamondsBadTwoCollarFaces
      remainderFaces := laterLayerFaces chainedDiamondsBadTwoCollarFaces
      boundaryCycle := chainedDiamondsBadTwoCollarBoundaryCycle
      hfaceCover := by decide
      hdisjoint := by decide
      hremainder := by
        intro i
        rfl
      houterBoundary := by decide
      hinnerBoundary := by decide
      hcurrentBoundaryCover := by decide
      hremainderBoundaryCover := by decide
      hcurrentInnerAmbientBoundary := by decide
      hremainderInnerAmbientBoundary := by decide
      hintermediateBoundaryInterior := by decide
      hintermediateBoundaryNonempty := by decide
      hboundaryCycleDisjoint := by decide
      hambientOuterBoundary := by decide
      hambientInnerBoundary := by decide }

def chainedDiamondsBadTwoCollarWitnessEdge :
    AmbientFace chainedDiamondsWithTriangleEmbedding.faces →
      chainedDiamondsWithTriangleGraph.edgeSet
  | ⟨⟨0, _⟩, _⟩ => cdt12
  | ⟨⟨1, _⟩, _⟩ => cdt12
  | ⟨⟨2, _⟩, _⟩ => cdt35
  | ⟨⟨3, _⟩, _⟩ => cdt45
  | ⟨⟨4, _⟩, _⟩ => cdt97

/-- A two-collar weak annulus geometry on the connected chained-diamonds embedding.  It is a
valid weak collar geometry, but its terminal triangular face witnesses on a selected boundary edge
instead of on the previous intermediate boundary. -/
def chainedDiamondsBadTwoCollarGeometry :
    PlanarBoundaryAnnulusCollarGeometry chainedDiamondsWithTriangleEmbedding := by
  refine
    { toPlanarBoundaryAnnulusDecomposition := chainedDiamondsBadTwoCollarDecomposition
      witnessEdge := chainedDiamondsBadTwoCollarWitnessEdge
      hcover := by decide
      hwitness := by decide
      hrest := by decide
      hfrontier := by decide }

def chainedDiamondsBadTwoCollarPositiveIndex :
    Fin chainedDiamondsBadTwoCollarGeometry.numCollars := ⟨1, by decide⟩

def chainedDiamondsBadTwoCollarBadFace :
    AmbientFace chainedDiamondsWithTriangleEmbedding.faces :=
  chainedDiamondsFace4

theorem chainedDiamondsBadTwoCollarBadFace_mem_positiveCollar :
    chainedDiamondsBadTwoCollarBadFace ∈
      chainedDiamondsBadTwoCollarGeometry.collarFaces
        chainedDiamondsBadTwoCollarPositiveIndex := by
  decide

theorem chainedDiamondsBadTwoCollarBadFace_witness_not_mem_previousBoundaryCycle :
    chainedDiamondsBadTwoCollarGeometry.witnessEdge chainedDiamondsBadTwoCollarBadFace ∉
      chainedDiamondsBadTwoCollarGeometry.boundaryCycle
        (Fin.castSucc chainedDiamondsBadTwoCollarPositiveIndex) := by
  decide

theorem chainedDiamondsBadTwoCollarBadFace_witness_not_mem_currentBoundary :
    chainedDiamondsBadTwoCollarGeometry.witnessEdge chainedDiamondsBadTwoCollarBadFace ∉
      (chainedDiamondsBadTwoCollarGeometry.toPlanarBoundaryAnnulusCurrentBoundaryData
        |>.currentBoundary chainedDiamondsBadTwoCollarPositiveIndex) := by
  simpa [PlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusCurrentBoundaryData] using
    chainedDiamondsBadTwoCollarBadFace_witness_not_mem_previousBoundaryCycle

theorem not_witnessOnCurrentBoundary_chainedDiamondsBadTwoCollarGeometry :
    ¬ chainedDiamondsBadTwoCollarGeometry.WitnessOnCurrentBoundary := by
  intro h
  exact chainedDiamondsBadTwoCollarBadFace_witness_not_mem_currentBoundary
    (h chainedDiamondsBadTwoCollarBadFace_mem_positiveCollar (by decide))

theorem
    exists_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_without_witnessOnCurrentBoundary_chainedDiamonds :
    ∃ _source :
        PlanarBoundaryClosedWalkAnnulusBoundarySource chainedDiamondsWithTriangleEmbedding,
      ∃ data : PlanarBoundaryAnnulusCollarGeometry chainedDiamondsWithTriangleEmbedding,
        ¬ data.WitnessOnCurrentBoundary := by
  exact
    ⟨chainedDiamondsClosedWalkAnnulusBoundarySource,
      chainedDiamondsBadTwoCollarGeometry,
      not_witnessOnCurrentBoundary_chainedDiamondsBadTwoCollarGeometry⟩

/-- Even with the fixed honest source present on the same connected embedding, an arbitrary weak
collar geometry need not satisfy the repaired previous/current-boundary witness condition. -/
theorem not_forall_honest_source_plus_collar_geometry_forces_previous_boundary_witness :
    ¬ (∀
        (_source :
          PlanarBoundaryClosedWalkAnnulusBoundarySource chainedDiamondsWithTriangleEmbedding)
        (data : PlanarBoundaryAnnulusCollarGeometry chainedDiamondsWithTriangleEmbedding),
          data.WitnessOnCurrentBoundary) := by
  intro h
  exact not_witnessOnCurrentBoundary_chainedDiamondsBadTwoCollarGeometry
    (h chainedDiamondsClosedWalkAnnulusBoundarySource chainedDiamondsBadTwoCollarGeometry)

/-- The arbitrary-collar failure survives the local at-most-one source package.  The same
chained-diamonds honest source has a valid fallback edge, at most one interior edge per face, and
all non-interior face-boundary edges on the extracted annulus boundary, but a separately chosen
weak two-collar geometry still fails the repaired current-boundary witness condition. -/
theorem
    exists_atMostOne_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_without_witnessOnCurrentBoundary_chainedDiamonds :
    ∃ emb : PlaneEmbeddingWithBoundary chainedDiamondsWithTriangleGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ fallbackEdge : AmbientFace emb.faces →
            chainedDiamondsWithTriangleGraph.edgeSet,
          (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
            (∀ f : AmbientFace emb.faces,
              ((emb.faceBoundary f.1).filter
                  (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                (1 : ℕ)) ∧
              ∀ (f : AmbientFace emb.faces) {e : chainedDiamondsWithTriangleGraph.edgeSet},
                e ∈ emb.faceBoundary f.1 →
                  e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                  e ∈
                    source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                      source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary) ∧
          ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
            ¬ data.WitnessOnCurrentBoundary := by
  exact
    ⟨chainedDiamondsWithTriangleEmbedding, chainedDiamondsClosedWalkAnnulusBoundarySource,
      ⟨chainedDiamondsCanonicalWitnessEdge, chainedDiamondsCanonicalWitnessEdge_mem,
        chainedDiamondsWithTriangle_atMostOneInteriorEdgePerFace,
        chainedDiamonds_nonInteriorOnAmbient⟩,
      chainedDiamondsBadTwoCollarGeometry,
      not_witnessOnCurrentBoundary_chainedDiamondsBadTwoCollarGeometry⟩

/-- Even adding the at-most-one source-side local criterion does not make an arbitrary
same-embedding weak collar satisfy the repaired current-boundary witness condition. -/
theorem
    not_forall_atMostOne_source_plus_collar_geometry_forces_previous_boundary_witness :
    ¬ (∀
        (source :
          PlanarBoundaryClosedWalkAnnulusBoundarySource chainedDiamondsWithTriangleEmbedding),
        (∃ fallbackEdge : AmbientFace chainedDiamondsWithTriangleEmbedding.faces →
            chainedDiamondsWithTriangleGraph.edgeSet,
          (∀ f : AmbientFace chainedDiamondsWithTriangleEmbedding.faces,
              fallbackEdge f ∈ chainedDiamondsWithTriangleEmbedding.faceBoundary f.1) ∧
            (∀ f : AmbientFace chainedDiamondsWithTriangleEmbedding.faces,
              ((chainedDiamondsWithTriangleEmbedding.faceBoundary f.1).filter
                  (· ∈ interiorEdgeSupport chainedDiamondsWithTriangleEmbedding.faceBoundary
                    chainedDiamondsWithTriangleEmbedding.faces)).card ≤
                (1 : ℕ)) ∧
              ∀ (f : AmbientFace chainedDiamondsWithTriangleEmbedding.faces)
                  {e : chainedDiamondsWithTriangleGraph.edgeSet},
                e ∈ chainedDiamondsWithTriangleEmbedding.faceBoundary f.1 →
                  e ∉ interiorEdgeSupport chainedDiamondsWithTriangleEmbedding.faceBoundary
                    chainedDiamondsWithTriangleEmbedding.faces →
                  e ∈
                    source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                      source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary) →
        ∀ data : PlanarBoundaryAnnulusCollarGeometry chainedDiamondsWithTriangleEmbedding,
          data.WitnessOnCurrentBoundary) := by
  intro h
  exact not_witnessOnCurrentBoundary_chainedDiamondsBadTwoCollarGeometry
    (h chainedDiamondsClosedWalkAnnulusBoundarySource
      ⟨chainedDiamondsCanonicalWitnessEdge, chainedDiamondsCanonicalWitnessEdge_mem,
        chainedDiamondsWithTriangle_atMostOneInteriorEdgePerFace,
        chainedDiamonds_nonInteriorOnAmbient⟩
      chainedDiamondsBadTwoCollarGeometry)

/-- Canonical witness choice for the honest source also does not constrain a separately supplied
weak collar geometry.  The corrected positive route must use the collar built from the choice (or
an explicit repaired-witness hypothesis), not merely the existence of such a choice somewhere on
the same embedding. -/
theorem
    not_forall_canonicalWitnessChoice_source_plus_collar_geometry_forces_previous_boundary_witness :
    ¬ (∀
        (source :
          PlanarBoundaryClosedWalkAnnulusBoundarySource chainedDiamondsWithTriangleEmbedding),
        Nonempty
          (PlanarBoundaryCanonicalWitnessChoice
            source.toPlanarBoundaryAnnulusBoundaryData) →
        ∀ data : PlanarBoundaryAnnulusCollarGeometry chainedDiamondsWithTriangleEmbedding,
          data.WitnessOnCurrentBoundary) := by
  intro h
  exact not_witnessOnCurrentBoundary_chainedDiamondsBadTwoCollarGeometry
    (h chainedDiamondsClosedWalkAnnulusBoundarySource
      chainedDiamondsClosedWalkAnnulusBoundarySource_hasCanonicalWitnessChoice
      chainedDiamondsBadTwoCollarGeometry)

theorem not_nonempty_previousBoundaryWitnessGeometry_extending_chainedDiamondsBadTwoCollarGeometry :
    ¬ Nonempty
        { data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry
            chainedDiamondsWithTriangleEmbedding //
          data.toPlanarBoundaryAnnulusCollarGeometry =
            chainedDiamondsBadTwoCollarGeometry } := by
  rintro ⟨data, hdata⟩
  have hwitnessData :
      data.toPlanarBoundaryAnnulusCollarGeometry.WitnessOnCurrentBoundary := by
    exact
      (data.toPlanarBoundaryAnnulusCollarGeometry
        |>.witnessOnCurrentBoundary_iff_previousBoundaryWitness).2
          (@data.hwitnessPrev)
  have hwitness :
      chainedDiamondsBadTwoCollarGeometry.WitnessOnCurrentBoundary := by
    rw [hdata] at hwitnessData
    exact hwitnessData
  exact not_witnessOnCurrentBoundary_chainedDiamondsBadTwoCollarGeometry hwitness

/-- Universal failed-theorem form of the connected counterexample.  There is no theorem saying
that an honest source and an arbitrary same-embedding weak collar can always upgrade that supplied
collar to the repaired previous-boundary witness surface. -/
theorem
    not_forall_honest_source_plus_collar_geometry_forces_extending_previous_boundary_witness :
    ¬ (∀ {G : SimpleGraph (Fin 10)} {emb : PlaneEmbeddingWithBoundary G},
          PlanarBoundaryClosedWalkAnnulusBoundarySource emb →
            (collarGeom : PlanarBoundaryAnnulusCollarGeometry emb) →
              Nonempty
                { data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb //
                  data.toPlanarBoundaryAnnulusCollarGeometry = collarGeom }) := by
  intro h
  exact
    not_nonempty_previousBoundaryWitnessGeometry_extending_chainedDiamondsBadTwoCollarGeometry
      (h (G := chainedDiamondsWithTriangleGraph)
        (emb := chainedDiamondsWithTriangleEmbedding)
        chainedDiamondsClosedWalkAnnulusBoundarySource
        chainedDiamondsBadTwoCollarGeometry)

/-!
## Resolved fixed-collar question

The older connectivity hypothesis is false.  The disconnected `counterCollarGeometry`
explained why the first obstruction lacked an honest source, but the connected chained-diamonds
model above shows that facial closed walks do not force the supplied weak collar's witness edge
onto the previous boundary.  The exact fixed-collar upgrade is therefore the explicit
`WitnessOnCurrentBoundary` obligation proved below.

-/

/-- For a fixed weak collar geometry, the exact repaired-surface obligation is the
current-boundary witness placement property for that same collar geometry. The honest source is
kept in the statement to record the investigated route shape, but no source field currently
changes the fixed-collar upgrade obligation. -/
theorem
    honest_source_plus_collar_geometry_extending_previous_boundary_witness_iff_witnessOnCurrentBoundary
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (_source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (collarGeom : PlanarBoundaryAnnulusCollarGeometry emb) :
    Nonempty
        { data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb //
          data.toPlanarBoundaryAnnulusCollarGeometry = collarGeom } ↔
      collarGeom.WitnessOnCurrentBoundary := by
  constructor
  · rintro ⟨data, hdata⟩
    subst collarGeom
    exact
      (data.toPlanarBoundaryAnnulusCollarGeometry
        |>.witnessOnCurrentBoundary_iff_previousBoundaryWitness).2
          (@data.hwitnessPrev)
  · intro hwitnessCurrent
    let data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb :=
      { toPlanarBoundaryAnnulusCollarGeometry := collarGeom
        hwitnessPrev :=
          (collarGeom.witnessOnCurrentBoundary_iff_previousBoundaryWitness).1
            hwitnessCurrent }
    exact Nonempty.intro ⟨data, rfl⟩

/-- Source plus weak collar geometry upgrades to the repaired previous-boundary surface once the
fixed collar's current-boundary witness placement has been proved. -/
def PlanarBoundaryAnnulusCollarGeometry.toPreviousBoundaryWitnessGeometry_of_honestSource
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (collarGeom : PlanarBoundaryAnnulusCollarGeometry emb)
    (_source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hwitnessCurrent : collarGeom.WitnessOnCurrentBoundary) :
    PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb :=
  planarBoundaryAnnulusPreviousBoundaryWitnessGeometry_of_collarGeometry collarGeom
    ((collarGeom.witnessOnCurrentBoundary_iff_previousBoundaryWitness).1 hwitnessCurrent)

end Mettapedia.GraphTheory.FourColor
