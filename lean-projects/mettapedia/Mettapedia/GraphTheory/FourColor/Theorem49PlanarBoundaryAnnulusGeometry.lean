import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryAnnulusWitness

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- Geometry-plus-witness data for Step 2 over a boundary-aware plane embedding. This extends the
pure annulus decomposition by adding the witness-edge ownership needed by the current Theorem 4.9
annihilator route. -/
structure PlanarBoundaryAnnulusCollarGeometry {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G)
    extends PlanarBoundaryAnnulusDecomposition emb where
  witnessEdge : AmbientFace emb.faces → G.edgeSet
  hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆
    (Finset.univ.biUnion collarFaces).image witnessEdge
  hwitness : ∀ i f, f ∈ collarFaces i → witnessEdge f ∈ emb.faceBoundary f.1
  hrest : ∀ i f, f ∈ collarFaces i → ∀ e ∈ (emb.faceBoundary f.1).erase (witnessEdge f),
    (i.1 = 0 ∧ e ∈ outerAmbientBoundary) ∨
      (∃ _hi : i.1 + 1 < numCollars, e ∈ boundaryCycle (Fin.succ i)) ∨
        (i.1 + 1 = numCollars ∧ e ∈ innerAmbientBoundary)
  hfrontier : ∀ i (_hi : i.1 + 1 < numCollars) e, e ∈ boundaryCycle (Fin.succ i) →
    ∃ j : Fin numCollars, i < j ∧ ∃ g ∈ collarFaces j, witnessEdge g = e

/-- Minimal repaired annulus geometry surface for the current Theorem 4.9 route. The regression
counterexample shows the weaker `PlanarBoundaryAnnulusCollarGeometry` fields do not force witness
edges of positive collars onto the previous annulus boundary cycle, so that extra geometric fact
must be carried explicitly when one wants the well-founded parent-peeling endpoint. -/
structure PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G)
    extends PlanarBoundaryAnnulusCollarGeometry emb where
  hwitnessPrev : ∀ {j : Fin numCollars} {g : AmbientFace emb.faces},
    g ∈ collarFaces j → 0 < j.1 →
      witnessEdge g ∈ boundaryCycle (Fin.castSucc j)

/-- Equivalent current-boundary formulation of the repaired witness-placement hypothesis. This
states the missing geometric seam directly on the concrete current outer frontier at collar stage
`j`, rather than via the primitive cycle notation `Γ_j`. -/
def PlanarBoundaryAnnulusCollarGeometry.WitnessOnCurrentBoundary
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb) : Prop :=
  ∀ {j : Fin data.numCollars} {g : AmbientFace emb.faces},
    g ∈ data.collarFaces j → 0 < j.1 →
      data.witnessEdge g ∈
        (data.toPlanarBoundaryAnnulusCurrentBoundaryData.currentBoundary j)

theorem PlanarBoundaryAnnulusCollarGeometry.witnessOnCurrentBoundary_iff_previousBoundaryWitness
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb) :
    data.WitnessOnCurrentBoundary ↔
      ∀ {j : Fin data.numCollars} {g : AmbientFace emb.faces},
        g ∈ data.collarFaces j → 0 < j.1 →
          data.witnessEdge g ∈ data.boundaryCycle (Fin.castSucc j) := by
  constructor
  · intro h j g hgj hjpos
    unfold PlanarBoundaryAnnulusCollarGeometry.WitnessOnCurrentBoundary at h
    simpa [PlanarBoundaryAnnulusCollarGeometry.WitnessOnCurrentBoundary,
      PlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusCurrentBoundaryData] using
      h hgj hjpos
  · intro h
    unfold PlanarBoundaryAnnulusCollarGeometry.WitnessOnCurrentBoundary
    intro j g hgj hjpos
    simpa [PlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusCurrentBoundaryData] using
      h hgj hjpos

/-- In a one-collar annulus geometry, the repaired previous/current-boundary witness condition is
vacuous: there are no positive collar indices. -/
theorem PlanarBoundaryAnnulusCollarGeometry.witnessOnCurrentBoundary_of_numCollars_eq_one
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hnum : data.numCollars = 1) :
    data.WitnessOnCurrentBoundary := by
  intro j _g _hgj hjpos
  have hjlt : j.1 < 1 := by
    simpa [hnum] using j.isLt
  omega

/-- A one-collar weak annulus geometry canonically upgrades to the repaired
previous-boundary-witness surface, because the only missing condition has no positive collar to
check. -/
def PlanarBoundaryAnnulusCollarGeometry.toPreviousBoundaryWitnessGeometry_of_numCollars_eq_one
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hnum : data.numCollars = 1) :
    PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb :=
  { toPlanarBoundaryAnnulusCollarGeometry := data
    hwitnessPrev :=
      (data.witnessOnCurrentBoundary_iff_previousBoundaryWitness).1
        (data.witnessOnCurrentBoundary_of_numCollars_eq_one hnum) }

/-- Graph-level existence form of the geometry-facing annulus collar target. -/
def AdmitsPlanarBoundaryAnnulusCollarGeometry (G : SimpleGraph V) : Prop :=
  ∃ emb : PlaneEmbeddingWithBoundary G,
    Nonempty (PlanarBoundaryAnnulusCollarGeometry emb)

/-- Graph-level existence form of the repaired annulus collar target that carries the minimal
previous-boundary witness placement hypothesis needed by the current theorem-4.9 route. -/
def AdmitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry (G : SimpleGraph V) : Prop :=
  ∃ emb : PlaneEmbeddingWithBoundary G,
    Nonempty (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb)

/-- Any annulus collar geometry already determines the weaker concrete current-boundary package on
the same embedding by forgetting witness ownership and retaining the annulus decomposition's live
current frontiers. -/
theorem nonempty_planarBoundaryAnnulusCurrentBoundaryData_of_annulusCollarGeometry
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb) :
    Nonempty (PlanarBoundaryAnnulusCurrentBoundaryData emb) := by
  exact ⟨data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusCurrentBoundaryData⟩

/-- Any annulus collar geometry also determines the weaker concrete current-boundary package on
the same embedding with exactly the same extracted annulus boundary split. -/
theorem exists_planarBoundaryAnnulusCurrentBoundaryData_of_annulusCollarGeometry
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb) :
    ∃ currentData : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      currentData.toPlanarBoundaryAnnulusBoundaryData =
        data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData := by
  exact
    ⟨data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusCurrentBoundaryData, rfl⟩

/-- The same canonical lowering preserves the collar count as well, since both shells are read
from the same annulus decomposition. -/
theorem
    exists_planarBoundaryAnnulusCurrentBoundaryData_of_annulusCollarGeometry_preserving_numCollars
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb) :
    ∃ currentData : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      currentData.numCollars = data.numCollars ∧
        currentData.toPlanarBoundaryAnnulusBoundaryData =
          data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData := by
  refine
    ⟨data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusCurrentBoundaryData,
      ?_, rfl⟩
  rfl

/-- A one-collar annulus collar geometry canonically lowers to a one-collar concrete
current-boundary package on the same embedding, preserving the extracted annulus boundary split.
-/
theorem exists_oneCollarAnnulusCurrentBoundaryData_of_oneCollarAnnulusCollarGeometry
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hnum : data.numCollars = 1) :
    ∃ currentData : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      currentData.numCollars = 1 ∧
        currentData.toPlanarBoundaryAnnulusBoundaryData =
          data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData := by
  rcases
    exists_planarBoundaryAnnulusCurrentBoundaryData_of_annulusCollarGeometry_preserving_numCollars
      data with
    ⟨currentData, hcurrentNum, hboundary⟩
  exact ⟨currentData, by simpa [hnum] using hcurrentNum, hboundary⟩

/-- The weak current-boundary shell is already inhabited by any honest annulus source: the
source's extracted boundary split canonically yields the degenerate one-collar annulus
decomposition, and that decomposition lowers directly to one-collar current-boundary data. -/
theorem
    exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb) :
    ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          source.toPlanarBoundaryAnnulusBoundaryData := by
  let decomp :=
    planarBoundaryAnnulusDecomposition_of_boundaryData
      source.toPlanarBoundaryAnnulusBoundaryData
  let data := decomp.toPlanarBoundaryAnnulusCurrentBoundaryData
  refine ⟨data, ?_, ?_⟩
  · change decomp.numCollars = 1
    simp [decomp, planarBoundaryAnnulusDecomposition_of_boundaryData]
  · rfl

/-- Fixed-embedding nonempty form of the weak current-boundary shell. Any honest annulus source
already carries concrete current-boundary data on the same embedding. -/
theorem nonempty_planarBoundaryAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb) :
    Nonempty (PlanarBoundaryAnnulusCurrentBoundaryData emb) := by
  rcases exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource source with
    ⟨data, _hnum, _hboundary⟩
  exact ⟨data⟩

/-- Graph-level source-preserving existence form of the weak one-collar current shell. Any
honest closed-walk annulus source already carries same-embedding one-collar current-boundary data
with the same extracted annulus boundary split. -/
theorem
    exists_oneCollarAnnulusCurrentBoundaryData_with_sourceBoundaryData_of_exists_closedWalkAnnulusBoundarySource
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData := by
  rcases hG with ⟨emb, ⟨source⟩⟩
  rcases exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource source with
    ⟨data, hnum, hboundary⟩
  exact ⟨emb, source, data, hnum, hboundary⟩

/-- Honest annulus source data cannot witness failure of the source-preserving current-boundary
shell: the extracted annulus boundary split itself already builds one-collar current-boundary data
on the same embedding. -/
theorem not_exists_embedding_closedWalkAnnulusBoundarySource_without_currentBoundaryData
    {G : SimpleGraph V} :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary G,
        ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          ¬ ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
              data.toPlanarBoundaryAnnulusBoundaryData =
                source.toPlanarBoundaryAnnulusBoundaryData := by
  intro h
  rcases h with ⟨emb, source, hno⟩
  rcases exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource source with
    ⟨data, _hnum, hboundary⟩
  exact hno ⟨data, hboundary⟩

theorem admitsPlanarBoundaryAnnulusDecomposition_of_admitsPlanarBoundaryAnnulusCollarGeometry
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryAnnulusCollarGeometry G) :
    AdmitsPlanarBoundaryAnnulusDecomposition G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.toPlanarBoundaryAnnulusDecomposition⟩⟩

theorem exists_planarBoundaryAnnulusCurrentBoundaryData_of_admitsPlanarBoundaryAnnulusCollarGeometry
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryAnnulusCollarGeometry G) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryAnnulusCurrentBoundaryData emb) := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, nonempty_planarBoundaryAnnulusCurrentBoundaryData_of_annulusCollarGeometry data⟩

theorem
    admitsPlanarBoundaryAnnulusCollarGeometry_of_admitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry G) :
    AdmitsPlanarBoundaryAnnulusCollarGeometry G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.toPlanarBoundaryAnnulusCollarGeometry⟩⟩

theorem PlanarBoundaryAnnulusCollarGeometry.numCollars_le_card_faces
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb) :
    data.numCollars ≤ emb.faces.card := by
  simpa using data.toPlanarBoundaryAnnulusDecomposition.numCollars_le_card_faces

/-- Recombine a pure annulus decomposition and a witness assignment into the bundled
geometry-plus-witness package. This shows the split introduced for Step 2 is exact rather than a
weakening. -/
def planarBoundaryAnnulusCollarGeometry_of_decomposition_and_witnessAssignment
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (decomp : PlanarBoundaryAnnulusDecomposition emb)
    (data : PlanarBoundaryAnnulusWitnessAssignment decomp) :
    PlanarBoundaryAnnulusCollarGeometry emb := by
  refine
    { toPlanarBoundaryAnnulusDecomposition := decomp
      witnessEdge := data.witnessEdge
      hcover := data.hcover
      hwitness := data.hwitness
      hrest := ?_
      hfrontier := data.hfrontier }
  intro i f hf e he
  rcases data.hrest i f hf e he with houter | hinner | hterminal
  · exact Or.inl houter
  · exact Or.inr <| Or.inl hinner
  · exact Or.inr <| Or.inr hterminal

/-- Forget the bundled geometry fields and retain only the witness assignment over the underlying
pure annulus decomposition. -/
def PlanarBoundaryAnnulusCollarGeometry.toWitnessAssignment
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb) :
    PlanarBoundaryAnnulusWitnessAssignment data.toPlanarBoundaryAnnulusDecomposition := by
  refine
    { witnessEdge := data.witnessEdge
      hcover := data.hcover
      hwitness := data.hwitness
      hrest := ?_
      hfrontier := data.hfrontier }
  · intro i f hf e he
    rcases data.hrest i f hf e he with houter | hinner | hterminal
    · exact Or.inl houter
    · exact Or.inr <| Or.inl hinner
    · exact Or.inr <| Or.inr hterminal

/-- A canonical facewise witness choice on an annulus boundary split builds genuine one-collar
annulus collar geometry on the same embedding.  The pure collar part is the canonical
one-collar decomposition extracted from the boundary split; the witness part is exactly the
given canonical witness choice. -/
def PlanarBoundaryCanonicalWitnessChoice.toPlanarBoundaryAnnulusCollarGeometry
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {boundaryData : PlanarBoundaryAnnulusBoundaryData emb}
    (data : PlanarBoundaryCanonicalWitnessChoice boundaryData) :
    PlanarBoundaryAnnulusCollarGeometry emb :=
  planarBoundaryAnnulusCollarGeometry_of_decomposition_and_witnessAssignment
    (planarBoundaryAnnulusDecomposition_of_boundaryData boundaryData)
    data.toPlanarBoundaryAnnulusWitnessAssignment

theorem PlanarBoundaryCanonicalWitnessChoice.toPlanarBoundaryAnnulusCollarGeometry_numCollars
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {boundaryData : PlanarBoundaryAnnulusBoundaryData emb}
    (data : PlanarBoundaryCanonicalWitnessChoice boundaryData) :
    data.toPlanarBoundaryAnnulusCollarGeometry.numCollars = 1 := by
  rfl

theorem
    PlanarBoundaryCanonicalWitnessChoice.toPlanarBoundaryAnnulusCollarGeometry_boundaryData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {boundaryData : PlanarBoundaryAnnulusBoundaryData emb}
    (data : PlanarBoundaryCanonicalWitnessChoice boundaryData) :
    data.toPlanarBoundaryAnnulusCollarGeometry.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
      boundaryData := by
  rfl

/-- A canonical facewise witness choice lands directly on the repaired previous-boundary
witness surface. The intermediate weak collar geometry has a single collar, so the repaired
positive-collar witness condition is vacuous. -/
def PlanarBoundaryCanonicalWitnessChoice.toPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {boundaryData : PlanarBoundaryAnnulusBoundaryData emb}
    (data : PlanarBoundaryCanonicalWitnessChoice boundaryData) :
    PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb :=
  data.toPlanarBoundaryAnnulusCollarGeometry.toPreviousBoundaryWitnessGeometry_of_numCollars_eq_one
    data.toPlanarBoundaryAnnulusCollarGeometry_numCollars

/-- A one-collar annulus collar geometry whose boundary split is a given annulus boundary split
already contains the canonical facewise witness choice on that split.  The single collar covers
every ambient face, and with no intermediate frontier every non-witness edge is forced onto one
of the two ambient annulus boundaries. -/
def PlanarBoundaryAnnulusCollarGeometry.toPlanarBoundaryCanonicalWitnessChoice_of_numCollars_eq_one
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {boundaryData : PlanarBoundaryAnnulusBoundaryData emb}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hnum : data.numCollars = 1)
    (hboundary :
      data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
        boundaryData) :
    PlanarBoundaryCanonicalWitnessChoice boundaryData := by
  let i : Fin data.numCollars := ⟨0, by omega⟩
  refine
    { witnessEdge := data.witnessEdge
      hcover := ?_
      hwitness := ?_
      hrest := ?_ }
  · intro e he
    rcases Finset.mem_image.1 (data.hcover he) with ⟨f, _hf, hfe⟩
    exact Finset.mem_image.2 ⟨f, by simp, hfe⟩
  · intro f
    rcases data.toPlanarBoundaryAnnulusDecomposition.exists_mem_collarFaces f with ⟨j, hfj⟩
    have hj0 : j.1 = 0 := by
      have hjlt : j.1 < 1 := by omega
      exact Nat.lt_one_iff.mp hjlt
    have hji : j = i := by
      apply Fin.ext
      simpa [i] using hj0
    have hfi : f ∈ data.collarFaces i := by
      simpa [hji] using hfj
    exact data.hwitness i f hfi
  · intro f e he
    rcases data.toPlanarBoundaryAnnulusDecomposition.exists_mem_collarFaces f with ⟨j, hfj⟩
    have hj0 : j.1 = 0 := by
      have hjlt : j.1 < 1 := by omega
      exact Nat.lt_one_iff.mp hjlt
    have hji : j = i := by
      apply Fin.ext
      simpa [i] using hj0
    have hfi : f ∈ data.collarFaces i := by
      simpa [hji] using hfj
    have hrest := data.hrest i f hfi e he
    rw [← hboundary]
    rcases hrest with houter | hmiddle | hterminal
    · exact Finset.mem_union.2 (Or.inl houter.2)
    · rcases hmiddle with ⟨hi, _⟩
      omega
    · exact Finset.mem_union.2 (Or.inr hterminal.2)

/-- Source-facing existence form of the preceding construction: one-collar collar geometry on the
boundary split extracted from an honest closed-walk source canonically supplies the explicit
facewise witness-choice package for that source. -/
theorem exists_planarBoundaryCanonicalWitnessChoice_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        Nonempty
          (PlanarBoundaryCanonicalWitnessChoice
            source.toPlanarBoundaryAnnulusBoundaryData) := by
  rcases hG with ⟨emb, source, data, hnum, hboundary⟩
  exact
    ⟨emb, source,
      ⟨data.toPlanarBoundaryCanonicalWitnessChoice_of_numCollars_eq_one hnum hboundary⟩⟩

/-- Source-facing one-collar geometry construction from a canonical facewise witness choice on
the source boundary split.  This is the broad positive construction surface behind the finite
diamond instance: any honest closed-walk source whose extracted boundary split carries a
canonical witness choice yields same-embedding one-collar collar geometry preserving that split.
-/
theorem
    exists_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        Nonempty
          (PlanarBoundaryCanonicalWitnessChoice
            source.toPlanarBoundaryAnnulusBoundaryData)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData := by
  rcases hG with ⟨emb, source, ⟨choice⟩⟩
  exact
    ⟨emb, source, choice.toPlanarBoundaryAnnulusCollarGeometry,
      choice.toPlanarBoundaryAnnulusCollarGeometry_numCollars,
      choice.toPlanarBoundaryAnnulusCollarGeometry_boundaryData⟩

/-- Source-facing one-collar current-boundary package extracted from same-embedding one-collar
collar geometry. This is the concrete annulus-shell form of the one-collar positive route, with
the collar count and boundary split preserved exactly. -/
theorem
    exists_oneCollarAnnulusCurrentBoundaryData_with_sourceBoundaryData_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData := by
  rcases hG with ⟨emb, source, data, hnum, hboundary⟩
  rcases
    exists_oneCollarAnnulusCurrentBoundaryData_of_oneCollarAnnulusCollarGeometry data hnum with
    ⟨currentData, hcurrentNum, hcurrentBoundary⟩
  exact
    ⟨emb, source, currentData, hcurrentNum, hcurrentBoundary.trans hboundary⟩

/-- Direct repaired-geometry route from an honest closed-walk source whose extracted annulus
boundary split carries a canonical facewise witness choice. This avoids treating the intermediate
one-collar collar geometry as a separate obligation: the canonical choice already builds the
one-collar geometry, and the repaired previous-boundary witness condition is vacuous there. -/
theorem exists_planarBoundaryAnnulusPreviousBoundaryWitnessGeometry_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        Nonempty
          (PlanarBoundaryCanonicalWitnessChoice
            source.toPlanarBoundaryAnnulusBoundaryData)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        Nonempty (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) := by
  rcases hG with ⟨emb, source, ⟨choice⟩⟩
  exact
    ⟨emb, source,
      ⟨choice.toPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry⟩⟩

/-- Source-facing one-collar geometry construction from local facewise hypotheses.  It is enough
to supply a fallback boundary edge on every ambient face, prove that each face has at most one
interior boundary edge, and prove that all non-interior face-boundary edges lie on the source's
outer or inner ambient annulus boundary.  The canonical witness-choice constructor then builds
same-embedding one-collar collar geometry preserving the source boundary split. -/
theorem
    exists_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
          (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
            (∀ (f : AmbientFace emb.faces) {e₁ e₂ : G.edgeSet},
              e₁ ∈ emb.faceBoundary f.1 →
                e₂ ∈ emb.faceBoundary f.1 →
                  e₁ ∈ interiorEdgeSupport emb.faceBoundary emb.faces →
                    e₂ ∈ interiorEdgeSupport emb.faceBoundary emb.faces →
                      e₁ = e₂) ∧
            (∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
              e ∈ emb.faceBoundary f.1 →
                e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                  e ∈
                    source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                      source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData := by
  rcases hG with
    ⟨emb, source, fallbackEdge, hfallback, huniqueInterior, hboundaryRest⟩
  let choice :
      PlanarBoundaryCanonicalWitnessChoice
        source.toPlanarBoundaryAnnulusBoundaryData :=
    PlanarBoundaryCanonicalWitnessChoice.of_atMostOneInteriorEdgePerFace
      (boundaryData := source.toPlanarBoundaryAnnulusBoundaryData)
      fallbackEdge hfallback huniqueInterior hboundaryRest
  exact
    ⟨emb, source, choice.toPlanarBoundaryAnnulusCollarGeometry,
      choice.toPlanarBoundaryAnnulusCollarGeometry_numCollars,
      choice.toPlanarBoundaryAnnulusCollarGeometry_boundaryData⟩

/-- Source-facing one-collar geometry construction with the boundary-rest condition discharged
from the source's annulus boundary split.  The remaining local burden is a fallback edge on each
ambient face and the assertion that each face has at most one interior boundary edge. -/
theorem
    exists_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_of_exists_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
          (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
            (∀ (f : AmbientFace emb.faces) {e₁ e₂ : G.edgeSet},
              e₁ ∈ emb.faceBoundary f.1 →
                e₂ ∈ emb.faceBoundary f.1 →
                  e₁ ∈ interiorEdgeSupport emb.faceBoundary emb.faces →
                    e₂ ∈ interiorEdgeSupport emb.faceBoundary emb.faces →
                      e₁ = e₂)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData := by
  rcases hG with ⟨emb, source, fallbackEdge, hfallback, huniqueInterior⟩
  exact
    exists_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace
      ⟨emb, source, fallbackEdge, hfallback, huniqueInterior,
        by
          intro f e heFace heNotInterior
          exact
            source.toPlanarBoundaryAnnulusBoundaryData
              |>.mem_outerAmbientBoundary_union_innerAmbientBoundary_of_mem_faceBoundary_of_not_mem_interiorEdgeSupport
                heFace heNotInterior⟩

/-- Honest closed-walk source variant of the one-collar construction.  The source supplies the
fallback boundary edge on every face from its nonempty facial boundary walks, and the annulus
boundary split supplies the non-interior boundary-rest clause; the only remaining local
geometric input is uniqueness of the interior boundary edge on each face. -/
theorem
    exists_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_of_exists_closedWalkAnnulusBoundarySource_and_facewiseUniqueInteriorEdge
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∀ (f : AmbientFace emb.faces) {e₁ e₂ : G.edgeSet},
          e₁ ∈ emb.faceBoundary f.1 →
            e₂ ∈ emb.faceBoundary f.1 →
              e₁ ∈ interiorEdgeSupport emb.faceBoundary emb.faces →
                e₂ ∈ interiorEdgeSupport emb.faceBoundary emb.faces →
                  e₁ = e₂) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData := by
  rcases hG with ⟨emb, source, huniqueInterior⟩
  exact
    exists_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_of_exists_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge
      ⟨emb, source, source.fallbackEdge, source.fallbackEdge_mem_faceBoundary,
        huniqueInterior⟩

/-- Fixed-embedding honest-source version of the one-collar construction.  The source supplies
fallback boundary edges from honest facial closed walks, and its annulus boundary split puts all
non-interior face-boundary edges on the ambient annulus boundary.  Thus the only extra local
hypothesis is the facewise cardinal bound saying that a face boundary contains at most one
interior edge. -/
theorem
    exists_oneCollarAnnulusCollarGeometry_of_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (h_at_most_one_interior :
      ∀ f : AmbientFace emb.faces,
        ((emb.faceBoundary f.1).filter
            (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
          (1 : ℕ)) :
    ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
          source.toPlanarBoundaryAnnulusBoundaryData := by
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
  let choice :
      PlanarBoundaryCanonicalWitnessChoice
        source.toPlanarBoundaryAnnulusBoundaryData :=
    PlanarBoundaryCanonicalWitnessChoice.of_atMostOneInteriorEdgePerFace
      (boundaryData := source.toPlanarBoundaryAnnulusBoundaryData)
      source.fallbackEdge source.fallbackEdge_mem_faceBoundary huniqueInterior
      (by
        intro f e heFace heNotInterior
        exact
          source.toPlanarBoundaryAnnulusBoundaryData
            |>.mem_outerAmbientBoundary_union_innerAmbientBoundary_of_mem_faceBoundary_of_not_mem_interiorEdgeSupport
              heFace heNotInterior)
  exact
    ⟨choice.toPlanarBoundaryAnnulusCollarGeometry,
      choice.toPlanarBoundaryAnnulusCollarGeometry_numCollars,
      choice.toPlanarBoundaryAnnulusCollarGeometry_boundaryData⟩

/-- Fixed-embedding honest-source version of the same one-collar current-boundary endpoint. The
source and the facewise cardinal at-most-one interior-edge criterion already force a concrete
one-collar annulus current-boundary package on the same embedding with the same boundary split. -/
theorem
    exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (h_at_most_one_interior :
      ∀ f : AmbientFace emb.faces,
        ((emb.faceBoundary f.1).filter
            (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
          (1 : ℕ)) :
    ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
      data.numCollars = 1 ∧
        data.toPlanarBoundaryAnnulusBoundaryData =
          source.toPlanarBoundaryAnnulusBoundaryData := by
  rcases
    exists_oneCollarAnnulusCollarGeometry_of_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge
      source h_at_most_one_interior with
    ⟨collarData, hnum, hboundary⟩
  rcases
    exists_oneCollarAnnulusCurrentBoundaryData_of_oneCollarAnnulusCollarGeometry collarData hnum with
    ⟨currentData, hcurrentNum, hcurrentBoundary⟩
  exact ⟨currentData, hcurrentNum, hcurrentBoundary.trans hboundary⟩

/-- Graph-level honest-source cardinal version of the one-collar construction.  This is the
source-facing geometric endpoint: an embedding carrying an honest closed-walk annulus-boundary
source and the facewise cardinal at-most-one interior-edge bound carries a source-preserving
one-collar annulus collar geometry on that same embedding. -/
theorem
    exists_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_of_exists_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdgeCardinality
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∀ f : AmbientFace emb.faces,
          ((emb.faceBoundary f.1).filter
              (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
            (1 : ℕ)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData := by
  rcases hG with ⟨emb, source, h_at_most_one_interior⟩
  rcases
    exists_oneCollarAnnulusCollarGeometry_of_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge
      source h_at_most_one_interior with
    ⟨data, hnum, hboundary⟩
  exact ⟨emb, source, data, hnum, hboundary⟩

/-- Graph-level honest-source cardinal version of the one-collar current-boundary endpoint. This
packages the concrete annulus shell reached from the same facewise cardinal criterion. -/
theorem
    exists_oneCollarAnnulusCurrentBoundaryData_with_sourceBoundaryData_of_exists_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdgeCardinality
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∀ f : AmbientFace emb.faces,
          ((emb.faceBoundary f.1).filter
              (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
            (1 : ℕ)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData := by
  rcases hG with ⟨emb, source, h_at_most_one_interior⟩
  rcases
    exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge
      source h_at_most_one_interior with
    ⟨data, hnum, hboundary⟩
  exact ⟨emb, source, data, hnum, hboundary⟩

/-- Any graph-level one-collar annulus collar geometry automatically inhabits the repaired
previous-boundary witness surface.  This packages the vacuity of the positive-collar witness
condition in the form used by upstream source constructors. -/
theorem
    admitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry_of_exists_oneCollarAnnulusCollarGeometry
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
        data.numCollars = 1) :
    AdmitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry G := by
  rcases hG with ⟨emb, data, hnum⟩
  exact ⟨emb, ⟨data.toPreviousBoundaryWitnessGeometry_of_numCollars_eq_one hnum⟩⟩

/-- Source-facing one-collar repair: if the honest closed-walk source already carries a
same-boundary one-collar collar geometry, then it carries the corrected previous-boundary witness
geometry on the same embedding. -/
theorem
    exists_planarBoundaryAnnulusPreviousBoundaryWitnessGeometry_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        Nonempty (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) := by
  rcases hG with ⟨emb, source, data, hnum, _hboundary⟩
  exact
    ⟨emb, source, ⟨data.toPreviousBoundaryWitnessGeometry_of_numCollars_eq_one hnum⟩⟩

/-- The at-most-one-interior-edge source criterion reaches the corrected previous-boundary
witness geometry, not only the weak one-collar collar geometry. -/
theorem
    admitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
          (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
            (∀ (f : AmbientFace emb.faces) {e₁ e₂ : G.edgeSet},
              e₁ ∈ emb.faceBoundary f.1 →
                e₂ ∈ emb.faceBoundary f.1 →
                  e₁ ∈ interiorEdgeSupport emb.faceBoundary emb.faces →
                    e₂ ∈ interiorEdgeSupport emb.faceBoundary emb.faces →
                      e₁ = e₂) ∧
            (∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
              e ∈ emb.faceBoundary f.1 →
                e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                  e ∈
                    source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                      source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)) :
    AdmitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry G := by
  rcases
    exists_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace
      hG with
    ⟨emb, _source, data, hnum, _hboundary⟩
  exact
    admitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry_of_exists_oneCollarAnnulusCollarGeometry
      ⟨emb, data, hnum⟩

/-- Honest closed-walk source variant of the corrected previous-boundary witness criterion.  The
source and its annulus boundary split discharge fallback and boundary-rest; the remaining
geometric input is facewise uniqueness of interior boundary edges. -/
theorem
    admitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry_of_exists_closedWalkAnnulusBoundarySource_and_facewiseUniqueInteriorEdge
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∀ (f : AmbientFace emb.faces) {e₁ e₂ : G.edgeSet},
          e₁ ∈ emb.faceBoundary f.1 →
            e₂ ∈ emb.faceBoundary f.1 →
              e₁ ∈ interiorEdgeSupport emb.faceBoundary emb.faces →
                e₂ ∈ interiorEdgeSupport emb.faceBoundary emb.faces →
                  e₁ = e₂) :
    AdmitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry G := by
  rcases
    exists_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_of_exists_closedWalkAnnulusBoundarySource_and_facewiseUniqueInteriorEdge
      hG with
    ⟨emb, _source, data, hnum, _hboundary⟩
  exact
    admitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry_of_exists_oneCollarAnnulusCollarGeometry
      ⟨emb, data, hnum⟩

/-- Boundary-rest-automatic variant of the at-most-one-interior-edge source criterion for the
corrected previous-boundary witness geometry. -/
theorem
    admitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry_of_exists_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
          (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
            (∀ (f : AmbientFace emb.faces) {e₁ e₂ : G.edgeSet},
              e₁ ∈ emb.faceBoundary f.1 →
                e₂ ∈ emb.faceBoundary f.1 →
                  e₁ ∈ interiorEdgeSupport emb.faceBoundary emb.faces →
                    e₂ ∈ interiorEdgeSupport emb.faceBoundary emb.faces →
                      e₁ = e₂)) :
    AdmitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry G := by
  rcases
    exists_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_of_exists_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge
      hG with
    ⟨emb, _source, data, hnum, _hboundary⟩
  exact
    admitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry_of_exists_oneCollarAnnulusCollarGeometry
      ⟨emb, data, hnum⟩

/-- Repackage a weak annulus collar geometry together with the repaired previous-boundary witness
condition into the corrected theorem surface. -/
def planarBoundaryAnnulusPreviousBoundaryWitnessGeometry_of_collarGeometry
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hwitnessPrev : ∀ {j : Fin data.numCollars} {g : AmbientFace emb.faces},
      g ∈ data.collarFaces j → 0 < j.1 →
        data.witnessEdge g ∈ data.boundaryCycle (Fin.castSucc j)) :
    PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb := by
  exact
    { toPlanarBoundaryAnnulusCollarGeometry := data
      hwitnessPrev := hwitnessPrev }

/-- For a fixed embedding, the bundled annulus collar geometry is equivalent to the split theorem
surface consisting of a pure annulus decomposition together with a witness assignment on that
decomposition. -/
theorem
    nonempty_planarBoundaryAnnulusCollarGeometry_iff_exists_planarBoundaryAnnulusDecomposition_and_witnessAssignment
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} :
    Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) ↔
      ∃ decomp : PlanarBoundaryAnnulusDecomposition emb,
        Nonempty (PlanarBoundaryAnnulusWitnessAssignment decomp) := by
  constructor
  · rintro ⟨data⟩
    exact ⟨data.toPlanarBoundaryAnnulusDecomposition, ⟨data.toWitnessAssignment⟩⟩
  · rintro ⟨decomp, ⟨data⟩⟩
    exact ⟨
      planarBoundaryAnnulusCollarGeometry_of_decomposition_and_witnessAssignment decomp data⟩

/-- A face carrying two distinct interior edges blocks every one-collar weak annulus geometry on
the same embedding. This is stronger than the canonical-decomposition obstruction: the failure is
not tied to a particular recovered decomposition, but to the whole `numCollars = 1` collar-geometry
surface. -/
theorem
    not_exists_planarBoundaryAnnulusCollarGeometry_of_numCollars_eq_one_and_exists_two_distinct_interior_edges_on_faceBoundary
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (hex :
      ∃ f : AmbientFace emb.faces,
        ∃ e₁ ∈ emb.faceBoundary f.1,
          ∃ e₂ ∈ emb.faceBoundary f.1,
            e₁ ≠ e₂ ∧
              e₁ ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∧
                e₂ ∈ interiorEdgeSupport emb.faceBoundary emb.faces) :
    ¬ ∃ data : PlanarBoundaryAnnulusCollarGeometry emb, data.numCollars = 1 := by
  rintro ⟨data, hnum⟩
  exact
    not_nonempty_planarBoundaryAnnulusWitnessAssignment_of_numCollars_eq_one_and_exists_two_distinct_interior_edges_on_faceBoundary
      hnum hex ⟨data.toWitnessAssignment⟩

/-- Any obstruction to a fixed-size current-boundary package on an embedding already obstructs the
same-size weak annulus collar geometry on that embedding, since collar geometry lowers
canonically to the current-boundary shell through the intermediate annulus decomposition. -/
theorem
    not_exists_planarBoundaryAnnulusCollarGeometry_of_not_exists_planarBoundaryAnnulusCurrentBoundaryData_of_numCollars_eq
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} {n : ℕ}
    (hcurrent :
      ¬ ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb, data.numCollars = n) :
    ¬ ∃ data : PlanarBoundaryAnnulusCollarGeometry emb, data.numCollars = n := by
  rintro ⟨data, hnum⟩
  exact
    hcurrent
      ⟨data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusCurrentBoundaryData, by
        simpa using hnum⟩

/-- The same bridge can be stated with the ambient annulus boundary split fixed. This is the form
used by honest-source regressions: if no `numCollars = n` current-boundary package exists with a
given boundary split, then no `numCollars = n` weak collar geometry exists with that same split. -/
theorem
    not_exists_planarBoundaryAnnulusCollarGeometry_of_not_exists_planarBoundaryAnnulusCurrentBoundaryData_of_numCollars_eq_and_boundaryData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {boundaryData : PlanarBoundaryAnnulusBoundaryData emb} {n : ℕ}
    (hcurrent :
      ¬ ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = n ∧ data.toPlanarBoundaryAnnulusBoundaryData = boundaryData) :
    ¬ ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
        data.numCollars = n ∧
          data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
            boundaryData := by
  rintro ⟨data, hnum, hboundary⟩
  exact
    hcurrent
      ⟨data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusCurrentBoundaryData, by
          simpa using hnum, by
          simpa using hboundary⟩

/-- Any explicit same-embedding witness carrying the honest closed-walk annulus source but no
weak annulus collar geometry preserving that source's extracted boundary split refutes a universal
same-embedding derivation theorem from the source package to weak collar geometry on that split.
This blocks the common repair move "recover some collar geometry later on the same source
embedding" unless the proof route changes the boundary split or strengthens the target surface. -/
theorem
    not_forall_exists_planarBoundaryAnnulusCollarGeometry_with_sourceBoundaryData_of_exists_embedding_closedWalkAnnulusBoundarySource_without_annulusCollarGeometry
    {G : SimpleGraph V}
    (hWitness :
      ∃ emb : PlaneEmbeddingWithBoundary G,
        ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          ¬ ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
              data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
                source.toPlanarBoundaryAnnulusBoundaryData) :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary G,
        ∀ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
            data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData := by
  exact
    not_forall_target_of_exists_embedding_closedWalkAnnulusBoundarySource_without_target
      (Target := fun emb source =>
        ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
          data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
            source.toPlanarBoundaryAnnulusBoundaryData)
      hWitness

/-- Exact-count failed converse for the honest closed-walk annulus source at the weak collar
geometry shell. -/
theorem
    not_forall_exists_planarBoundaryAnnulusCollarGeometry_with_sourceBoundaryData_and_numCollars_eq_of_exists_embedding_closedWalkAnnulusBoundarySource_without_annulusCollarGeometry
    {G : SimpleGraph V} {n : ℕ}
    (hWitness :
      ∃ emb : PlaneEmbeddingWithBoundary G,
        ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          ¬ ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
              data.numCollars = n ∧
                data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
                  source.toPlanarBoundaryAnnulusBoundaryData) :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary G,
        ∀ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
            data.numCollars = n ∧
              data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
                source.toPlanarBoundaryAnnulusBoundaryData := by
  exact
    not_forall_target_of_exists_embedding_closedWalkAnnulusBoundarySource_without_target
      (Target := fun emb source =>
        ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
          data.numCollars = n ∧
            data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData)
      hWitness

/-- The same source-preserving bridge holds one shell lower: same-embedding annulus collar
geometry with the source's extracted boundary split already yields concrete annulus
current-boundary data with that same split. -/
theorem
    exists_planarBoundaryAnnulusCurrentBoundaryData_with_sourceBoundaryData_of_exists_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
          data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
            source.toPlanarBoundaryAnnulusBoundaryData) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.toPlanarBoundaryAnnulusBoundaryData =
            source.toPlanarBoundaryAnnulusBoundaryData := by
  rcases hG with ⟨emb, source, data, hboundary⟩
  rcases exists_planarBoundaryAnnulusCurrentBoundaryData_of_annulusCollarGeometry data with
    ⟨currentData, hcurrentBoundary⟩
  exact ⟨emb, source, currentData, hcurrentBoundary.trans hboundary⟩

/-- Exact-count source-preserving version of the same current-boundary lowering. -/
theorem
    exists_planarBoundaryAnnulusCurrentBoundaryData_with_sourceBoundaryData_and_numCollars_eq_of_exists_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry
    {G : SimpleGraph V} {n : ℕ}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
          data.numCollars = n ∧
            data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = n ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData := by
  rcases hG with ⟨emb, source, data, hnum, hboundary⟩
  rcases
    exists_planarBoundaryAnnulusCurrentBoundaryData_of_annulusCollarGeometry_preserving_numCollars
      data with
    ⟨currentData, hcurrentNum, hcurrentBoundary⟩
  exact ⟨emb, source, currentData, hcurrentNum.trans hnum, hcurrentBoundary.trans hboundary⟩

/-- Any explicit same-embedding witness carrying the honest closed-walk annulus source but no
concrete current-boundary package preserving that source's extracted boundary split refutes a
universal same-embedding derivation theorem from the source package to the current-boundary
shell on that split. -/
theorem
    not_forall_exists_planarBoundaryAnnulusCurrentBoundaryData_with_sourceBoundaryData_of_exists_embedding_closedWalkAnnulusBoundarySource_without_currentBoundaryData
    {G : SimpleGraph V}
    (hWitness :
      ∃ emb : PlaneEmbeddingWithBoundary G,
        ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          ¬ ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
              data.toPlanarBoundaryAnnulusBoundaryData =
                source.toPlanarBoundaryAnnulusBoundaryData) :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary G,
        ∀ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData := by
  exact
    not_forall_target_of_exists_embedding_closedWalkAnnulusBoundarySource_without_target
      (Target := fun emb source =>
        ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.toPlanarBoundaryAnnulusBoundaryData =
            source.toPlanarBoundaryAnnulusBoundaryData)
      hWitness

/-- The exact one-collar source-preserving current-boundary shell cannot fail on an honest
closed-walk annulus source, because that shell is already built canonically from the source's
extracted annulus boundary split. -/
theorem
    not_exists_embedding_closedWalkAnnulusBoundarySource_without_oneCollarAnnulusCurrentBoundaryData_with_sourceBoundaryData
    {G : SimpleGraph V} :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary G,
        ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          ¬ ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
              data.numCollars = 1 ∧
                data.toPlanarBoundaryAnnulusBoundaryData =
                  source.toPlanarBoundaryAnnulusBoundaryData := by
  intro h
  rcases h with ⟨emb, source, hno⟩
  rcases exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource source with
    ⟨data, hnum, hboundary⟩
  exact hno ⟨data, hnum, hboundary⟩

/-- Exact-count failed converse for the honest closed-walk source shell. -/
theorem
    not_forall_exists_planarBoundaryAnnulusCurrentBoundaryData_with_sourceBoundaryData_and_numCollars_eq_of_exists_embedding_closedWalkAnnulusBoundarySource_without_currentBoundaryData
    {G : SimpleGraph V} {n : ℕ}
    (hWitness :
      ∃ emb : PlaneEmbeddingWithBoundary G,
        ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          ¬ ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
              data.numCollars = n ∧
                data.toPlanarBoundaryAnnulusBoundaryData =
                  source.toPlanarBoundaryAnnulusBoundaryData) :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary G,
        ∀ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = n ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                source.toPlanarBoundaryAnnulusBoundaryData := by
  exact
    not_forall_target_of_exists_embedding_closedWalkAnnulusBoundarySource_without_target
      (Target := fun emb source =>
        ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = n ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData)
      hWitness

/-- Any explicit same-embedding witness carrying the honest closed-walk annulus source but no
attached-face certificate refutes a universal same-embedding derivation theorem from that source
package to the raw certificate surface consumed by the current synthesis layer. -/
theorem
    not_forall_exists_attachedBoundaryRootedFacePeelCertificate_of_exists_embedding_closedWalkAnnulusBoundarySource_without_attachedBoundaryRootedFacePeelCertificate
    {G : SimpleGraph V}
    (hWitness :
      ∃ emb : PlaneEmbeddingWithBoundary G,
        ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          ¬ Nonempty
            (BoundaryRootedFacePeelCertificate emb.faces.attach
              (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary))) :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary G,
        ∀ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          Nonempty
            (BoundaryRootedFacePeelCertificate emb.faces.attach
              (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) := by
  exact
    not_forall_target_of_exists_embedding_closedWalkAnnulusBoundarySource_without_target
      (Target := fun emb _source =>
        Nonempty
          (BoundaryRootedFacePeelCertificate emb.faces.attach
            (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)))
      hWitness

/-- Any explicit same-embedding witness carrying the honest closed-walk annulus source but no
height-ordered witness-cover data refutes a universal same-embedding derivation theorem from that
source package to the height-ordered witness surface. -/
theorem
    not_forall_exists_planarBoundaryHeightOrderedFacePeelWitnessData_of_exists_embedding_closedWalkAnnulusBoundarySource_without_heightOrderedFacePeelWitnessData
    {G : SimpleGraph V}
    (hWitness :
      ∃ emb : PlaneEmbeddingWithBoundary G,
        ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          ¬ Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb)) :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary G,
        ∀ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) := by
  exact
    not_forall_target_of_exists_embedding_closedWalkAnnulusBoundarySource_without_target
      (Target := fun emb _source =>
        Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb))
      hWitness

/-- Any explicit same-embedding witness carrying the honest closed-walk annulus source but no
collar-layer witness-cover data refutes a universal same-embedding derivation theorem from that
source package to the collar-layer witness surface. -/
theorem
    not_forall_exists_planarBoundaryCollarLayerFacePeelWitnessData_of_exists_embedding_closedWalkAnnulusBoundarySource_without_collarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    (hWitness :
      ∃ emb : PlaneEmbeddingWithBoundary G,
        ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          ¬ Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb)) :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary G,
        ∀ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) := by
  exact
    not_forall_target_of_exists_embedding_closedWalkAnnulusBoundarySource_without_target
      (Target := fun emb _source =>
        Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb))
      hWitness

/-- Any explicit same-embedding witness carrying the honest closed-walk annulus source but no
well-founded witness data refutes a universal same-embedding derivation theorem from that source
package to the well-founded parent-peeling surface. -/
theorem
    not_forall_exists_planarBoundaryWellFoundedFacePeelWitnessData_of_exists_embedding_closedWalkAnnulusBoundarySource_without_wellFoundedFacePeelWitnessData
    {G : SimpleGraph V}
    (hWitness :
      ∃ emb : PlaneEmbeddingWithBoundary G,
        ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          ¬ Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb)) :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary G,
        ∀ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) := by
  exact
    not_forall_target_of_exists_embedding_closedWalkAnnulusBoundarySource_without_target
      (Target := fun emb _source =>
        Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb))
      hWitness

/-- Any same-embedding honest closed-walk source whose embedding already carries annulus collar
geometry also carries the weaker concrete annulus current-boundary data on that same embedding. -/
theorem exists_planarBoundaryAnnulusCurrentBoundaryData_of_exists_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        Nonempty (PlanarBoundaryAnnulusCollarGeometry emb)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        Nonempty (PlanarBoundaryAnnulusCurrentBoundaryData emb) := by
  rcases hG with ⟨emb, source, ⟨data⟩⟩
  exact
    ⟨emb, source,
      nonempty_planarBoundaryAnnulusCurrentBoundaryData_of_annulusCollarGeometry data⟩

/-- Any explicit same-embedding witness carrying the honest closed-walk annulus source but no
concrete annulus current-boundary data refutes a universal same-embedding derivation theorem from
that source package to the current-boundary shell. -/
theorem
    not_forall_exists_planarBoundaryAnnulusCurrentBoundaryData_of_exists_embedding_closedWalkAnnulusBoundarySource_without_currentBoundaryData
    {G : SimpleGraph V}
    (hWitness :
      ∃ emb : PlaneEmbeddingWithBoundary G,
        ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          ¬ Nonempty (PlanarBoundaryAnnulusCurrentBoundaryData emb)) :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary G,
        ∀ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          Nonempty (PlanarBoundaryAnnulusCurrentBoundaryData emb) := by
  exact
    not_forall_target_of_exists_embedding_closedWalkAnnulusBoundarySource_without_target
      (Target := fun emb _source =>
        Nonempty (PlanarBoundaryAnnulusCurrentBoundaryData emb))
      hWitness

/-- Any explicit same-embedding witness carrying the honest closed-walk annulus source but no
weak annulus collar geometry refutes a universal same-embedding derivation theorem from that
source package to weak collar geometry on the same embedding. -/
theorem
    not_forall_exists_planarBoundaryAnnulusCollarGeometry_of_exists_embedding_closedWalkAnnulusBoundarySource_without_annulusCollarGeometry
    {G : SimpleGraph V}
    (hWitness :
      ∃ emb : PlaneEmbeddingWithBoundary G,
        ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          ¬ Nonempty (PlanarBoundaryAnnulusCollarGeometry emb)) :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary G,
        ∀ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) := by
  exact
    not_forall_target_of_exists_embedding_closedWalkAnnulusBoundarySource_without_target
      (Target := fun emb _source =>
        Nonempty (PlanarBoundaryAnnulusCollarGeometry emb))
      hWitness

/-- Any explicit same-embedding successor-dart source whose embedding carries no attached-face
certificate refutes a universal derivation theorem from the successor-dart source fields to that
certificate on the same embedding. -/
theorem
    not_forall_exists_attachedBoundaryRootedFacePeelCertificate_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_without_attachedBoundaryRootedFacePeelCertificate
    {G : SimpleGraph V}
    (hWitness :
      ∃ emb : PlaneEmbeddingWithBoundary G,
        ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
            ¬ Nonempty
              (BoundaryRootedFacePeelCertificate emb.faces.attach
                (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary))) :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary G,
        ∀ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
            Nonempty
              (BoundaryRootedFacePeelCertificate emb.faces.attach
                (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) := by
  exact
    not_forall_target_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_without_target
      (Target := fun emb =>
        Nonempty
          (BoundaryRootedFacePeelCertificate emb.faces.attach
            (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)))
      hWitness

/-- Any explicit same-embedding successor-dart source whose embedding carries no height-ordered
witness data refutes a universal derivation theorem from those source fields to height-ordered
witness data on the same embedding. -/
theorem
    not_forall_exists_planarBoundaryHeightOrderedFacePeelWitnessData_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_without_heightOrderedFacePeelWitnessData
    {G : SimpleGraph V}
    (hWitness :
      ∃ emb : PlaneEmbeddingWithBoundary G,
        ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
            ¬ Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb)) :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary G,
        ∀ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
            Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) := by
  exact
    not_forall_target_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_without_target
      (Target := fun emb =>
        Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb))
      hWitness

/-- Any explicit same-embedding successor-dart source whose embedding carries no collar-layer
witness data refutes a universal derivation theorem from those source fields to collar-layer
witness data on the same embedding. -/
theorem
    not_forall_exists_planarBoundaryCollarLayerFacePeelWitnessData_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_without_collarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    (hWitness :
      ∃ emb : PlaneEmbeddingWithBoundary G,
        ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
            ¬ Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb)) :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary G,
        ∀ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
            Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) := by
  exact
    not_forall_target_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_without_target
      (Target := fun emb =>
        Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb))
      hWitness

/-- Any explicit same-embedding successor-dart source whose embedding carries no well-founded
face-peeling witness data refutes a universal derivation theorem from those source fields to the
well-founded witness package on the same embedding. -/
theorem
    not_forall_exists_planarBoundaryWellFoundedFacePeelWitnessData_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_without_wellFoundedFacePeelWitnessData
    {G : SimpleGraph V}
    (hWitness :
      ∃ emb : PlaneEmbeddingWithBoundary G,
        ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
            ¬ Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb)) :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary G,
        ∀ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
            Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) := by
  exact
    not_forall_target_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_without_target
      (Target := fun emb =>
        Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb))
      hWitness

/-- Any same-embedding successor-dart source whose embedding already carries annulus collar
geometry also carries the weaker concrete annulus current-boundary data on that same embedding. -/
theorem
    exists_planarBoundaryAnnulusCurrentBoundaryData_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_annulusCollarGeometry
    {G : SimpleGraph V}
    (hG :
      ∃ emb : PlaneEmbeddingWithBoundary G,
        ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
            Nonempty (PlanarBoundaryAnnulusCollarGeometry emb)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          Nonempty (PlanarBoundaryAnnulusCurrentBoundaryData emb) := by
  rcases hG with ⟨emb, boundaryData, dartCycles, hboundaryArc, ⟨data⟩⟩
  exact
    ⟨emb, boundaryData, dartCycles, hboundaryArc,
      nonempty_planarBoundaryAnnulusCurrentBoundaryData_of_annulusCollarGeometry data⟩

/-- Successor-cycle source version of the source-preserving current-boundary lowering: if the
same embedding already carries annulus collar geometry with the boundary split extracted from the
boundary reachability data, then it also carries concrete current-boundary data with that same
boundary split. -/
theorem
    exists_planarBoundaryAnnulusCurrentBoundaryData_with_sourceBoundaryData_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_annulusCollarGeometry
    {G : SimpleGraph V}
    (hG :
      ∃ emb : PlaneEmbeddingWithBoundary G,
        ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
            ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
              data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.toPlanarBoundaryAnnulusBoundaryData =
              boundaryData.toPlanarBoundaryAnnulusBoundaryData := by
  rcases hG with ⟨emb, boundaryData, dartCycles, hboundaryArc, data, hboundary⟩
  rcases exists_planarBoundaryAnnulusCurrentBoundaryData_of_annulusCollarGeometry data with
    ⟨currentData, hcurrentBoundary⟩
  exact
    ⟨emb, boundaryData, dartCycles, hboundaryArc,
      currentData, hcurrentBoundary.trans hboundary⟩

/-- Successor-cycle source version of the weak one-collar current shell. The extracted annulus
boundary split itself already yields one-collar current-boundary data on the same embedding. -/
theorem
    exists_oneCollarAnnulusCurrentBoundaryData_with_sourceBoundaryData_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc
    {G : SimpleGraph V}
    (hG :
      ∃ emb : PlaneEmbeddingWithBoundary G,
        ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          ∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData := by
  rcases hG with ⟨emb, boundaryData, dartCycles, hboundaryArc⟩
  let source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  rcases exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource source with
    ⟨data, hnum, hboundary⟩
  exact
    ⟨emb, boundaryData, dartCycles, hboundaryArc, data, hnum, by
      simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
        hboundary⟩

/-- Fixed-embedding nonempty form of the weak current-boundary shell for the successor-cycle
boundary-order source surface. -/
theorem
    nonempty_planarBoundaryAnnulusCurrentBoundaryData_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) :
    Nonempty (PlanarBoundaryAnnulusCurrentBoundaryData emb) := by
  let source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact nonempty_planarBoundaryAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource source

/-- The successor-cycle boundary-order source shell also cannot witness failure of the
source-preserving current-boundary package: lowering to the honest closed-walk source already
builds one-collar current-boundary data on the same embedding. -/
theorem
    not_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_without_currentBoundaryData
    {G : SimpleGraph V} :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary G,
        ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
            ¬ ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
                data.toPlanarBoundaryAnnulusBoundaryData =
                  boundaryData.toPlanarBoundaryAnnulusBoundaryData := by
  intro h
  rcases h with ⟨emb, boundaryData, dartCycles, hboundaryArc, hno⟩
  let source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  rcases exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource source with
    ⟨data, _hnum, hboundary⟩
  have hboundary' :
      data.toPlanarBoundaryAnnulusBoundaryData =
        boundaryData.toPlanarBoundaryAnnulusBoundaryData := by
    simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
      PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
      PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
      hboundary
  exact hno ⟨data, hboundary'⟩

/-- Successor-cycle exact-count source-preserving current-boundary lowering. -/
theorem
    exists_planarBoundaryAnnulusCurrentBoundaryData_with_sourceBoundaryData_and_numCollars_eq_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_annulusCollarGeometry
    {G : SimpleGraph V} {n : ℕ}
    (hG :
      ∃ emb : PlaneEmbeddingWithBoundary G,
        ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
            ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
              data.numCollars = n ∧
                data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
                  boundaryData.toPlanarBoundaryAnnulusBoundaryData) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = n ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData := by
  rcases hG with ⟨emb, boundaryData, dartCycles, hboundaryArc, data, hnum, hboundary⟩
  rcases
    exists_planarBoundaryAnnulusCurrentBoundaryData_of_annulusCollarGeometry_preserving_numCollars
      data with
    ⟨currentData, hcurrentNum, hcurrentBoundary⟩
  exact
    ⟨emb, boundaryData, dartCycles, hboundaryArc, currentData,
      hcurrentNum.trans hnum, hcurrentBoundary.trans hboundary⟩

/-- Successor-cycle source version of the one-collar current-boundary endpoint. The same
facewise cardinal at-most-one interior-edge criterion reaches a concrete one-collar annulus
current-boundary package preserving the annulus boundary split extracted from the boundary
reachability data. -/
theorem
    exists_oneCollarAnnulusCurrentBoundaryData_with_sourceBoundaryData_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_facewiseAtMostOneInteriorEdgeCardinality
    {G : SimpleGraph V}
    (hG :
      ∃ emb : PlaneEmbeddingWithBoundary G,
        ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
            ∀ f : AmbientFace emb.faces,
              ((emb.faceBoundary f.1).filter
                  (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                (1 : ℕ)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData := by
  rcases hG with ⟨emb, boundaryData, dartCycles, hboundaryArc, h_at_most_one_interior⟩
  let source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  rcases
    exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge
      source h_at_most_one_interior with
    ⟨data, hnum, hboundary⟩
  exact
    ⟨emb, boundaryData, dartCycles, hboundaryArc, data, hnum, by
      simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
        hboundary⟩

/-- Any explicit same-embedding successor-dart source whose embedding carries no concrete annulus
current-boundary data refutes a universal derivation theorem from those source fields to the
current-boundary shell on the same embedding. -/
theorem
    not_forall_exists_planarBoundaryAnnulusCurrentBoundaryData_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_without_currentBoundaryData
    {G : SimpleGraph V}
    (hWitness :
      ∃ emb : PlaneEmbeddingWithBoundary G,
        ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
            ¬ Nonempty (PlanarBoundaryAnnulusCurrentBoundaryData emb)) :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary G,
        ∀ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
            Nonempty (PlanarBoundaryAnnulusCurrentBoundaryData emb) := by
  exact
    not_forall_target_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_without_target
      (Target := fun emb =>
        Nonempty (PlanarBoundaryAnnulusCurrentBoundaryData emb))
      hWitness

/-- Successor-cycle exact-count failed converse for the source-preserving current-boundary shell.
-/
theorem
    not_forall_exists_planarBoundaryAnnulusCurrentBoundaryData_with_sourceBoundaryData_and_numCollars_eq_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_without_currentBoundaryData
    {G : SimpleGraph V} {n : ℕ}
    (hWitness :
      ∃ emb : PlaneEmbeddingWithBoundary G,
        ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
            ¬ ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
                data.numCollars = n ∧
                  data.toPlanarBoundaryAnnulusBoundaryData =
                    boundaryData.toPlanarBoundaryAnnulusBoundaryData) :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary G,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
            ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
              data.numCollars = n ∧
                data.toPlanarBoundaryAnnulusBoundaryData =
                  boundaryData.toPlanarBoundaryAnnulusBoundaryData := by
  intro h
  rcases hWitness with ⟨emb, boundaryData, dartCycles, hArc, hno⟩
  exact hno (h emb boundaryData dartCycles hArc)

/-- The exact one-collar source-preserving current-boundary shell also cannot fail on the
successor-cycle boundary-order source surface, because lowering to the honest closed-walk source
canonically builds it on the same embedding. -/
theorem
    not_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_without_oneCollarAnnulusCurrentBoundaryData_with_sourceBoundaryData
    {G : SimpleGraph V} :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary G,
        ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
            ¬ ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
                data.numCollars = 1 ∧
                  data.toPlanarBoundaryAnnulusBoundaryData =
                    boundaryData.toPlanarBoundaryAnnulusBoundaryData := by
  intro h
  rcases h with ⟨emb, boundaryData, dartCycles, hboundaryArc, hno⟩
  let source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  rcases exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource source with
    ⟨data, hnum, hboundary⟩
  have hboundary' :
      data.toPlanarBoundaryAnnulusBoundaryData =
        boundaryData.toPlanarBoundaryAnnulusBoundaryData := by
    simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
      PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
      PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
      hboundary
  exact hno ⟨data, hnum, hboundary'⟩

/-- Any explicit same-embedding successor-dart source whose embedding carries no annulus collar
geometry refutes a universal derivation theorem from those source fields to weak collar geometry
on the same embedding. -/
theorem
    not_forall_exists_planarBoundaryAnnulusCollarGeometry_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_without_annulusCollarGeometry
    {G : SimpleGraph V}
    (hWitness :
      ∃ emb : PlaneEmbeddingWithBoundary G,
        ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
            ¬ Nonempty (PlanarBoundaryAnnulusCollarGeometry emb)) :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary G,
        ∀ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
            Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) := by
  exact
    not_forall_target_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_without_target
      (Target := fun emb =>
        Nonempty (PlanarBoundaryAnnulusCollarGeometry emb))
      hWitness

/-- Exact-count failed converse for the successor-cycle source fields at the weak annulus collar
geometry shell. -/
theorem
    not_forall_exists_planarBoundaryAnnulusCollarGeometry_with_sourceBoundaryData_and_numCollars_eq_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_without_annulusCollarGeometry
    {G : SimpleGraph V} {n : ℕ}
    (hWitness :
      ∃ emb : PlaneEmbeddingWithBoundary G,
        ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
            ¬ ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
                data.numCollars = n ∧
                  data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
                    boundaryData.toPlanarBoundaryAnnulusBoundaryData) :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary G,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
            ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
              data.numCollars = n ∧
                data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
                  boundaryData.toPlanarBoundaryAnnulusBoundaryData := by
  intro h
  rcases hWitness with ⟨emb, boundaryData, dartCycles, hArc, hno⟩
  exact hno (h emb boundaryData dartCycles hArc)

/-- The corrected annulus geometry surface is exactly the weaker collar geometry plus the explicit
previous-boundary witness placement property isolated by the regression obstruction. -/
theorem
    nonempty_planarBoundaryAnnulusPreviousBoundaryWitnessGeometry_iff_exists_planarBoundaryAnnulusCollarGeometry_and_previousBoundaryWitness
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} :
    Nonempty (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) ↔
      ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
        ∀ {j : Fin data.numCollars} {g : AmbientFace emb.faces},
          g ∈ data.collarFaces j → 0 < j.1 →
            data.witnessEdge g ∈ data.boundaryCycle (Fin.castSucc j) := by
  constructor
  · rintro ⟨data⟩
    exact ⟨data.toPlanarBoundaryAnnulusCollarGeometry, @data.hwitnessPrev⟩
  · rintro ⟨data, hwitnessPrev⟩
    exact ⟨
      planarBoundaryAnnulusPreviousBoundaryWitnessGeometry_of_collarGeometry data
        hwitnessPrev⟩

/-- The corrected annulus geometry surface can also be stated as the weaker collar geometry plus
the exact same witness-placement property phrased on current outer boundaries. -/
theorem
    nonempty_planarBoundaryAnnulusPreviousBoundaryWitnessGeometry_iff_exists_planarBoundaryAnnulusCollarGeometry_and_witnessOnCurrentBoundary
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} :
    Nonempty (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) ↔
      ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
        data.WitnessOnCurrentBoundary := by
  rw [nonempty_planarBoundaryAnnulusPreviousBoundaryWitnessGeometry_iff_exists_planarBoundaryAnnulusCollarGeometry_and_previousBoundaryWitness]
  constructor
  · rintro ⟨data, hdata⟩
    exact ⟨data, (data.witnessOnCurrentBoundary_iff_previousBoundaryWitness).2 hdata⟩
  · rintro ⟨data, hdata⟩
    exact ⟨data, (data.witnessOnCurrentBoundary_iff_previousBoundaryWitness).1 hdata⟩

theorem
    admitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry_iff_exists_planarBoundaryAnnulusCollarGeometry_and_witnessOnCurrentBoundary
    {G : SimpleGraph V} :
    AdmitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry G ↔
      ∃ emb : PlaneEmbeddingWithBoundary G,
        ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
          data.WitnessOnCurrentBoundary := by
  constructor
  · rintro ⟨emb, ⟨data⟩⟩
    let c : PlanarBoundaryAnnulusCollarGeometry emb := data.toPlanarBoundaryAnnulusCollarGeometry
    exact ⟨emb, c, (c.witnessOnCurrentBoundary_iff_previousBoundaryWitness).2 (@data.hwitnessPrev)⟩
  · rintro ⟨emb, data, hdata⟩
    exact ⟨emb, ⟨
      planarBoundaryAnnulusPreviousBoundaryWitnessGeometry_of_collarGeometry data
        ((data.witnessOnCurrentBoundary_iff_previousBoundaryWitness).1 hdata)⟩⟩

/-- A geometry-facing annulus collar decomposition canonically yields the weaker local
explicit-remainder theorem-layer package on the same embedding. This is the direct bridge from the
paper-shaped nested boundary cycles `Γ_t` to the current live Step 2 endpoint. -/
def PlanarBoundaryAnnulusCollarGeometry.toLocalRemainderBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb) :
    PlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData emb :=
  data.toWitnessAssignment.toLocalRemainderBoundaryCollarLayerFacePeelWitnessData

/-- A geometry-facing annulus collar decomposition already determines the finite collar-layer
witness-cover package on the same embedding. This makes the current witness-cover target an
honest geometric consequence of the nested boundary-cycle shell, not a separate algebraic add-on.
-/
noncomputable def PlanarBoundaryAnnulusCollarGeometry.toPlanarBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb) :
    PlanarBoundaryCollarLayerFacePeelWitnessData emb :=
  planarBoundaryCollarLayerFacePeelWitnessData_of_genericLocalRemainderBoundaryCollarLayerFacePeelWitnessData
    data.toLocalRemainderBoundaryCollarLayerFacePeelWitnessData

/-- The same collar geometry also determines the weaker boundary-aware height-ordered witness-cover
package by forgetting the finite collar indexing down to its induced height order. -/
noncomputable def PlanarBoundaryAnnulusCollarGeometry.toPlanarBoundaryHeightOrderedFacePeelWitnessData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb) :
    PlanarBoundaryHeightOrderedFacePeelWitnessData emb :=
  data.toPlanarBoundaryCollarLayerFacePeelWitnessData.toHeightOrderedFacePeelWitnessData

theorem admitsPlanarBoundaryAnnulusWitnessAssignment_of_admitsPlanarBoundaryAnnulusCollarGeometry
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryAnnulusCollarGeometry G) :
    AdmitsPlanarBoundaryAnnulusWitnessAssignment G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data.toPlanarBoundaryAnnulusDecomposition, ⟨data.toWitnessAssignment⟩⟩

theorem admitsPlanarBoundaryAnnulusCollarGeometry_of_admitsPlanarBoundaryAnnulusWitnessAssignment
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryAnnulusWitnessAssignment G) :
    AdmitsPlanarBoundaryAnnulusCollarGeometry G := by
  rcases hG with ⟨emb, decomp, ⟨data⟩⟩
  exact ⟨emb, ⟨
    planarBoundaryAnnulusCollarGeometry_of_decomposition_and_witnessAssignment decomp data⟩⟩

/-- The bundled geometry-facing annulus target and the split decomposition-plus-witness target are
equivalent graph-level theorem surfaces. -/
theorem admitsPlanarBoundaryAnnulusCollarGeometry_iff_admitsPlanarBoundaryAnnulusWitnessAssignment
    {G : SimpleGraph V} :
    AdmitsPlanarBoundaryAnnulusCollarGeometry G ↔
      AdmitsPlanarBoundaryAnnulusWitnessAssignment G := by
  constructor
  · exact admitsPlanarBoundaryAnnulusWitnessAssignment_of_admitsPlanarBoundaryAnnulusCollarGeometry
  · exact admitsPlanarBoundaryAnnulusCollarGeometry_of_admitsPlanarBoundaryAnnulusWitnessAssignment

theorem
    admitsPlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData_of_admitsPlanarBoundaryAnnulusCollarGeometry
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryAnnulusCollarGeometry G) :
    AdmitsPlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.toLocalRemainderBoundaryCollarLayerFacePeelWitnessData⟩⟩

theorem
    admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_admitsPlanarBoundaryAnnulusCollarGeometry
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryAnnulusCollarGeometry G) :
    AdmitsPlanarBoundaryCollarLayerFacePeelWitnessData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.toPlanarBoundaryCollarLayerFacePeelWitnessData⟩⟩

theorem
    admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_of_admitsPlanarBoundaryAnnulusCollarGeometry
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryAnnulusCollarGeometry G) :
    AdmitsPlanarBoundaryHeightOrderedFacePeelWitnessData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.toPlanarBoundaryHeightOrderedFacePeelWitnessData⟩⟩

/-- Even the weaker annulus collar geometry already yields the boundary-aware attached-face
certificate package on the same embedding: the local explicit-remainder collar witness data is
enough to build the boundary-rooted certificate, without any previous-boundary witness
orientation hypothesis. -/
noncomputable def
    PlanarBoundaryAnnulusCollarGeometry.toPlanarBoundaryAttachedRootedFacePeelCertificate
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb) :
    PlanarBoundaryAttachedRootedFacePeelCertificate G := by
  let cert :
      BoundaryRootedFacePeelCertificate emb.faces.attach
        (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary) :=
    LocalRemainderBoundaryCollarLayerFacePeelWitnessData.toBoundaryRootedFacePeelCertificate
      (data := data.toLocalRemainderBoundaryCollarLayerFacePeelWitnessData)
  exact
    { embedding := emb
      certificate := cert }

theorem
    admitsPlanarBoundaryAttachedRootedFacePeelCertificate_of_admitsPlanarBoundaryAnnulusCollarGeometry
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryAnnulusCollarGeometry G) :
    AdmitsPlanarBoundaryAttachedRootedFacePeelCertificate G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨data.toPlanarBoundaryAttachedRootedFacePeelCertificate⟩

/-- The corrected annulus geometry surface canonically yields the boundary-aware well-founded
parent-peeling package actually needed by the repaired theorem-4.9 route. -/
noncomputable def
    PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry.toPlanarBoundaryWellFoundedFacePeelWitnessData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) :
    PlanarBoundaryWellFoundedFacePeelWitnessData emb :=
  PlanarBoundaryAnnulusWitnessAssignment.toPlanarBoundaryWellFoundedFacePeelWitnessData_of_previousBoundaryWitness
    data.toPlanarBoundaryAnnulusCollarGeometry.toWitnessAssignment
    data.hwitnessPrev

/-- The repaired previous-boundary witness surface already determines the finite collar-layer
witness-cover package on the same embedding. -/
noncomputable def
    PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry.toPlanarBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) :
    PlanarBoundaryCollarLayerFacePeelWitnessData emb :=
  data.toPlanarBoundaryAnnulusCollarGeometry.toPlanarBoundaryCollarLayerFacePeelWitnessData

/-- Forgetting the repaired previous-boundary witness package further yields the weaker
height-ordered witness-cover interface. -/
noncomputable def
    PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry.toPlanarBoundaryHeightOrderedFacePeelWitnessData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) :
    PlanarBoundaryHeightOrderedFacePeelWitnessData emb :=
  data.toPlanarBoundaryCollarLayerFacePeelWitnessData.toHeightOrderedFacePeelWitnessData

theorem
    admitsPlanarBoundaryWellFoundedFacePeelWitnessData_of_admitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry G) :
    AdmitsPlanarBoundaryWellFoundedFacePeelWitnessData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.toPlanarBoundaryWellFoundedFacePeelWitnessData⟩⟩

theorem
    admitsPlanarBoundaryWellFoundedFacePeelWitnessData_of_exists_planarBoundaryAnnulusCollarGeometry_and_witnessOnCurrentBoundary
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
        data.WitnessOnCurrentBoundary) :
    AdmitsPlanarBoundaryWellFoundedFacePeelWitnessData G := by
  have hGeom : AdmitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry G :=
    (admitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry_iff_exists_planarBoundaryAnnulusCollarGeometry_and_witnessOnCurrentBoundary).2
      hG
  exact
    admitsPlanarBoundaryWellFoundedFacePeelWitnessData_of_admitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry
      hGeom

/-- The repaired annulus geometry surface canonically yields the boundary-aware attached-face
certificate package on the same embedding. This is the exact graph-level theorem endpoint reached
once the missing previous-boundary witness placement is made explicit. -/
noncomputable def
    PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry.toPlanarBoundaryAttachedRootedFacePeelCertificate
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) :
    PlanarBoundaryAttachedRootedFacePeelCertificate G := by
  exact
    PlanarBoundaryWellFoundedFacePeelWitnessData.toPlanarBoundaryAttachedRootedFacePeelCertificate
      data.toPlanarBoundaryWellFoundedFacePeelWitnessData

theorem
    admitsPlanarBoundaryAttachedRootedFacePeelCertificate_of_admitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry G) :
    AdmitsPlanarBoundaryAttachedRootedFacePeelCertificate G := by
  exact
    admitsPlanarBoundaryAttachedRootedFacePeelCertificate_of_admitsPlanarBoundaryAnnulusCollarGeometry
      (admitsPlanarBoundaryAnnulusCollarGeometry_of_admitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry
        hG)

theorem
    admitsPlanarBoundaryAttachedRootedFacePeelCertificate_of_exists_planarBoundaryAnnulusCollarGeometry_and_witnessOnCurrentBoundary
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
        data.WitnessOnCurrentBoundary) :
    AdmitsPlanarBoundaryAttachedRootedFacePeelCertificate G := by
  rcases hG with ⟨emb, data, _⟩
  exact
    admitsPlanarBoundaryAttachedRootedFacePeelCertificate_of_admitsPlanarBoundaryAnnulusCollarGeometry
      ⟨emb, ⟨data⟩⟩

theorem
    admitsPlanarBoundaryAnnulusWitnessAssignment_of_admitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry G) :
    AdmitsPlanarBoundaryAnnulusWitnessAssignment G := by
  exact
    admitsPlanarBoundaryAnnulusWitnessAssignment_of_admitsPlanarBoundaryAnnulusCollarGeometry
      (admitsPlanarBoundaryAnnulusCollarGeometry_of_admitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry
        hG)

theorem
    admitsPlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData_of_admitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry G) :
    AdmitsPlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData G := by
  exact
    admitsPlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData_of_admitsPlanarBoundaryAnnulusCollarGeometry
      (admitsPlanarBoundaryAnnulusCollarGeometry_of_admitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry
        hG)

theorem
    admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_admitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry G) :
    AdmitsPlanarBoundaryCollarLayerFacePeelWitnessData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.toPlanarBoundaryCollarLayerFacePeelWitnessData⟩⟩

theorem
    admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_of_admitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry G) :
    AdmitsPlanarBoundaryHeightOrderedFacePeelWitnessData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.toPlanarBoundaryHeightOrderedFacePeelWitnessData⟩⟩

theorem
    admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_of_exists_planarBoundaryAnnulusCollarGeometry_and_witnessOnCurrentBoundary
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
        data.WitnessOnCurrentBoundary) :
    AdmitsPlanarBoundaryHeightOrderedFacePeelWitnessData G := by
  have hGeom : AdmitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry G :=
    (admitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry_iff_exists_planarBoundaryAnnulusCollarGeometry_and_witnessOnCurrentBoundary).2
      hG
  exact
    admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_of_admitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry
      hGeom

/-- If every positive-index collar face chooses its witness edge on the previous annulus boundary
cycle, then the bundled geometry-facing annulus package already determines the boundary-aware
well-founded parent-peeling data needed by the Theorem 4.9 annihilator route. -/
noncomputable def
    PlanarBoundaryAnnulusCollarGeometry.toPlanarBoundaryWellFoundedFacePeelWitnessData_of_previousBoundaryWitness
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hwitnessPrev : ∀ {j : Fin data.numCollars} {g : AmbientFace emb.faces},
      g ∈ data.collarFaces j → 0 < j.1 →
        data.witnessEdge g ∈ data.boundaryCycle (Fin.castSucc j)) :
    PlanarBoundaryWellFoundedFacePeelWitnessData emb :=
  data.toWitnessAssignment.toPlanarBoundaryWellFoundedFacePeelWitnessData_of_previousBoundaryWitness
    hwitnessPrev

/-- Current-boundary version of the repaired annulus-to-peeling bridge. This is equivalent to the
previous-boundary-cycle formulation, but closer to the concrete frontier shell used elsewhere in
the development. -/
noncomputable def
    PlanarBoundaryAnnulusCollarGeometry.toPlanarBoundaryWellFoundedFacePeelWitnessData_of_witnessOnCurrentBoundary
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hwitnessCurrent : data.WitnessOnCurrentBoundary) :
    PlanarBoundaryWellFoundedFacePeelWitnessData emb :=
  data.toPlanarBoundaryWellFoundedFacePeelWitnessData_of_previousBoundaryWitness
    ((data.witnessOnCurrentBoundary_iff_previousBoundaryWitness).1 hwitnessCurrent)

/-- Direct annulus-shaped annihilator theorem from the geometry-facing collar decomposition, once
positive collar faces place their witness edges on the previous annulus boundary cycle. This keeps
the live extra burden on the paper-facing geometry surface rather than on the split witness layer.
-/
theorem zero_on_allEdges_of_planarBoundaryAnnulusCollarGeometry_of_previousBoundaryWitness
    {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G)
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hwitnessPrev : ∀ {j : Fin data.numCollars} {g : AmbientFace emb.faces},
      g ∈ data.collarFaces j → 0 < j.1 →
        data.witnessEdge g ∈ data.boundaryCycle (Fin.castSucc j))
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0)
    (horth : ∀ i f, f ∈ data.collarFaces i →
      ∀ γ, γ ≠ 0 → γ ≠ C (data.witnessEdge f) →
        chainDot
            (boundaryBicoloredEdges C
              (C (data.witnessEdge f))
              (C (data.witnessEdge f) + γ)
              (emb.faceBoundary f.1))
            z
            (polarizedFaceGenerator C
              (C (data.witnessEdge f))
              (C (data.witnessEdge f) + γ)
              (emb.faceBoundary f.1)) = 0) :
    ∀ e, z e = 0 := by
  exact zero_on_allEdges_of_planarBoundaryWellFoundedFacePeelWitnessData
    (emb := emb) (C := C) (htait := htait) (z := z)
    (data := data.toPlanarBoundaryWellFoundedFacePeelWitnessData_of_previousBoundaryWitness
      hwitnessPrev)
    (hzeroBoundary := hzeroBoundary)
    (horth := by
      intro f hf
      rcases Finset.mem_biUnion.1 hf with ⟨i, -, hfi⟩
      exact horth i f hfi)

/-- Current-boundary version of the repaired annulus annihilator theorem. This exposes the exact
missing seam directly on the concrete current outer frontier of each positive collar stage. -/
theorem zero_on_allEdges_of_planarBoundaryAnnulusCollarGeometry_of_witnessOnCurrentBoundary
    {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G)
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hwitnessCurrent : data.WitnessOnCurrentBoundary)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0)
    (horth : ∀ i f, f ∈ data.collarFaces i →
      ∀ γ, γ ≠ 0 → γ ≠ C (data.witnessEdge f) →
        chainDot
            (boundaryBicoloredEdges C
              (C (data.witnessEdge f))
              (C (data.witnessEdge f) + γ)
              (emb.faceBoundary f.1))
            z
            (polarizedFaceGenerator C
              (C (data.witnessEdge f))
              (C (data.witnessEdge f) + γ)
              (emb.faceBoundary f.1)) = 0) :
    ∀ e, z e = 0 := by
  exact zero_on_allEdges_of_planarBoundaryAnnulusCollarGeometry_of_previousBoundaryWitness
    (emb := emb) (C := C) (htait := htait) (z := z) (data := data)
    (hwitnessPrev := (data.witnessOnCurrentBoundary_iff_previousBoundaryWitness).1 hwitnessCurrent)
    (hzeroBoundary := hzeroBoundary) (horth := horth)

/-- Direct annulus-shaped annihilator theorem from the repaired annulus geometry surface. This is
the clean theorem endpoint after promoting the checked missing hypothesis into the data itself. -/
theorem zero_on_allEdges_of_planarBoundaryAnnulusPreviousBoundaryWitnessGeometry
    {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G)
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0)
    (horth : ∀ i f, f ∈ data.collarFaces i →
      ∀ γ, γ ≠ 0 → γ ≠ C (data.witnessEdge f) →
        chainDot
            (boundaryBicoloredEdges C
              (C (data.witnessEdge f))
              (C (data.witnessEdge f) + γ)
              (emb.faceBoundary f.1))
            z
            (polarizedFaceGenerator C
              (C (data.witnessEdge f))
              (C (data.witnessEdge f) + γ)
              (emb.faceBoundary f.1)) = 0) :
    ∀ e, z e = 0 := by
  exact zero_on_allEdges_of_planarBoundaryAnnulusCollarGeometry_of_previousBoundaryWitness
    (emb := emb) (C := C) (htait := htait) (z := z)
    (data := data.toPlanarBoundaryAnnulusCollarGeometry)
    (hwitnessPrev := data.hwitnessPrev)
    (hzeroBoundary := hzeroBoundary)
    (horth := horth)

/-- Direct annulus-shaped annihilator theorem from the geometry-facing collar decomposition. Once
the actual planar annulus geometry has been constructed with explicit boundary cycles `Γ_t`, the
current local explicit-remainder theorem layer finishes the Step 2 vanishing argument. -/
theorem zero_on_allEdges_of_planarBoundaryAnnulusCollarGeometry
    {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G)
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0)
    (horth : ∀ i f, f ∈ data.collarFaces i →
      ∀ γ, γ ≠ 0 → γ ≠ C (data.witnessEdge f) →
        chainDot
            (boundaryBicoloredEdges C
              (C (data.witnessEdge f))
              (C (data.witnessEdge f) + γ)
              (emb.faceBoundary f.1))
            z
            (polarizedFaceGenerator C
              (C (data.witnessEdge f))
              (C (data.witnessEdge f) + γ)
              (emb.faceBoundary f.1)) = 0) :
    ∀ e, z e = 0 := by
  exact zero_on_allEdges_of_planarBoundaryAnnulusWitnessAssignment
    (emb := emb)
    (decomp := data.toPlanarBoundaryAnnulusDecomposition)
    (data := data.toWitnessAssignment)
    (C := C) (htait := htait) (z := z)
    (hzeroBoundary := hzeroBoundary) (horth := horth)

/-- Existential graph-level annihilator form of the geometry-facing annulus collar target. -/
theorem zero_on_allEdges_of_exists_planarBoundaryAnnulusCollarGeometry
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (hdata : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
        (∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0) ∧
        (∀ i f, f ∈ data.collarFaces i →
          ∀ γ, γ ≠ 0 → γ ≠ C (data.witnessEdge f) →
            chainDot
                (boundaryBicoloredEdges C
                  (C (data.witnessEdge f))
                  (C (data.witnessEdge f) + γ)
                  (emb.faceBoundary f.1))
                z
                (polarizedFaceGenerator C
                  (C (data.witnessEdge f))
                  (C (data.witnessEdge f) + γ)
                  (emb.faceBoundary f.1)) = 0)) :
    ∀ e, z e = 0 := by
  rcases hdata with ⟨emb, data, hzeroBoundary, horth⟩
  exact zero_on_allEdges_of_planarBoundaryAnnulusCollarGeometry
    (emb := emb) (C := C) (htait := htait) (z := z) (data := data)
    (hzeroBoundary := hzeroBoundary) (horth := horth)

/-- Existential graph-level annihilator form of the repaired annulus geometry surface carrying the
minimal previous-boundary witness hypothesis. -/
theorem zero_on_allEdges_of_exists_planarBoundaryAnnulusPreviousBoundaryWitnessGeometry
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (hdata : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb,
        (∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0) ∧
        (∀ i f, f ∈ data.collarFaces i →
          ∀ γ, γ ≠ 0 → γ ≠ C (data.witnessEdge f) →
            chainDot
                (boundaryBicoloredEdges C
                  (C (data.witnessEdge f))
                  (C (data.witnessEdge f) + γ)
                  (emb.faceBoundary f.1))
                z
                (polarizedFaceGenerator C
                  (C (data.witnessEdge f))
                  (C (data.witnessEdge f) + γ)
                  (emb.faceBoundary f.1)) = 0)) :
    ∀ e, z e = 0 := by
  rcases hdata with ⟨emb, data, hzeroBoundary, horth⟩
  exact zero_on_allEdges_of_planarBoundaryAnnulusPreviousBoundaryWitnessGeometry
    (emb := emb) (C := C) (htait := htait) (z := z) (data := data)
    (hzeroBoundary := hzeroBoundary) (horth := horth)

theorem zero_on_allEdges_of_exists_planarBoundaryAnnulusCollarGeometry_and_witnessOnCurrentBoundary
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (hdata : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
        data.WitnessOnCurrentBoundary ∧
        (∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0) ∧
        (∀ i f, f ∈ data.collarFaces i →
          ∀ γ, γ ≠ 0 → γ ≠ C (data.witnessEdge f) →
            chainDot
                (boundaryBicoloredEdges C
                  (C (data.witnessEdge f))
                  (C (data.witnessEdge f) + γ)
                  (emb.faceBoundary f.1))
                z
                (polarizedFaceGenerator C
                  (C (data.witnessEdge f))
                  (C (data.witnessEdge f) + γ)
                  (emb.faceBoundary f.1)) = 0)) :
    ∀ e, z e = 0 := by
  rcases hdata with ⟨emb, data, hwitnessCurrent, hzeroBoundary, horth⟩
  exact zero_on_allEdges_of_planarBoundaryAnnulusCollarGeometry_of_witnessOnCurrentBoundary
    (emb := emb) (C := C) (htait := htait) (z := z) (data := data)
    (hwitnessCurrent := hwitnessCurrent)
    (hzeroBoundary := hzeroBoundary) (horth := horth)

end Mettapedia.GraphTheory.FourColor
