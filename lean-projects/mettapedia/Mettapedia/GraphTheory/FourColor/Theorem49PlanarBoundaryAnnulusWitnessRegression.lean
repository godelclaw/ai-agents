import Mettapedia.GraphTheory.FourColor.PlanarBoundaryAnnulusConstruction
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryAnnulusWitness
import Mathlib.Tactic

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

namespace Theorem49PlanarBoundaryAnnulusWitnessRegression

/-- A finite disconnected graph carrying eight distinct edges. This is enough to realize a purely
combinatorial annulus collar geometry under the current weak `PlaneEmbeddingWithBoundary` API,
without forcing the witness edge of every positive collar face onto the previous annulus boundary
cycle. -/
def counterGraph : SimpleGraph (Fin 16) :=
  SimpleGraph.fromEdgeSet
    ({s(0, 1), s(2, 3), s(4, 5), s(6, 7), s(8, 9), s(10, 11), s(12, 13), s(14, 15)} :
      Set (Sym2 (Fin 16)))

def eo : counterGraph.edgeSet := ⟨s(0, 1), by simp [counterGraph]⟩
def ep : counterGraph.edgeSet := ⟨s(2, 3), by simp [counterGraph]⟩
def eqEdge : counterGraph.edgeSet := ⟨s(4, 5), by simp [counterGraph]⟩
def er1 : counterGraph.edgeSet := ⟨s(6, 7), by simp [counterGraph]⟩
def er2 : counterGraph.edgeSet := ⟨s(8, 9), by simp [counterGraph]⟩
def eiq : counterGraph.edgeSet := ⟨s(10, 11), by simp [counterGraph]⟩
def ei1 : counterGraph.edgeSet := ⟨s(12, 13), by simp [counterGraph]⟩
def ei2 : counterGraph.edgeSet := ⟨s(14, 15), by simp [counterGraph]⟩

theorem edge_eq_cases (e : counterGraph.edgeSet) :
    e = eo ∨ e = ep ∨ e = eqEdge ∨ e = er1 ∨
      e = er2 ∨ e = eiq ∨ e = ei1 ∨ e = ei2 := by
  have h :
      (e.1 = s(0, 1) ∨ e.1 = s(2, 3) ∨ e.1 = s(4, 5) ∨ e.1 = s(6, 7) ∨
        e.1 = s(8, 9) ∨ e.1 = s(10, 11) ∨ e.1 = s(12, 13) ∨ e.1 = s(14, 15)) ∧
        ¬ e.1.IsDiag := by
    simpa [counterGraph] using e.2
  rcases h.1 with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · exact Or.inl (Subtype.ext h0)
  · exact Or.inr <| Or.inl (Subtype.ext h1)
  · exact Or.inr <| Or.inr <| Or.inl (Subtype.ext h2)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext h3)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext h4)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext h5)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      (Subtype.ext h6)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      (Subtype.ext h7)

abbrev CounterFace := Fin 6

def counterFaces : Finset CounterFace := Finset.univ

def counterFaceBoundary : CounterFace → Finset counterGraph.edgeSet
  | ⟨0, _⟩ => {eo, ep}
  | ⟨1, _⟩ => {ep, er1}
  | ⟨2, _⟩ => {eqEdge, er2}
  | ⟨3, _⟩ => {eqEdge, eiq}
  | ⟨4, _⟩ => {er1, ei1}
  | ⟨5, _⟩ => {er2, ei2}

/-- A boundary-aware embedding satisfying the current API. The face boundaries are arranged so that
the outer collar face shares one edge with the next collar, two positive-collar faces share
separate edges with the terminal collar, and all remaining edges are boundary edges. -/
def counterEmbedding : PlaneEmbeddingWithBoundary counterGraph where
  Face := CounterFace
  faceDecidableEq := inferInstance
  faces := counterFaces
  faceBoundary := counterFaceBoundary
  edge_mem_faceSupport := by
    intro e
    rcases edge_eq_cases e with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide
  edge_one_or_two_faces := by
    intro e _he
    rcases edge_eq_cases e with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide

def f0 : CounterFace := ⟨0, by decide⟩
def f1 : CounterFace := ⟨1, by decide⟩
def f2 : CounterFace := ⟨2, by decide⟩
def f3 : CounterFace := ⟨3, by decide⟩
def f4 : CounterFace := ⟨4, by decide⟩
def f5 : CounterFace := ⟨5, by decide⟩

def fa : AmbientFace counterEmbedding.faces := ⟨f0, by simp [counterEmbedding, counterFaces, f0]⟩
def fbPrev : AmbientFace counterEmbedding.faces := ⟨f1, by simp [counterEmbedding, counterFaces, f1]⟩
def fbBad : AmbientFace counterEmbedding.faces := ⟨f2, by simp [counterEmbedding, counterFaces, f2]⟩
def fcq : AmbientFace counterEmbedding.faces := ⟨f3, by simp [counterEmbedding, counterFaces, f3]⟩
def fcr1 : AmbientFace counterEmbedding.faces := ⟨f4, by simp [counterEmbedding, counterFaces, f4]⟩
def fcr2 : AmbientFace counterEmbedding.faces := ⟨f5, by simp [counterEmbedding, counterFaces, f5]⟩

theorem ambientFace_eq_cases (f : AmbientFace counterEmbedding.faces) :
    f = fa ∨ f = fbPrev ∨ f = fbBad ∨ f = fcq ∨ f = fcr1 ∨ f = fcr2 := by
  rcases f with ⟨f, hf⟩
  change CounterFace at f
  fin_cases f <;>
    simp [fa, fbPrev, fbBad, fcq, fcr1, fcr2, f0, f1, f2, f3, f4, f5,
      counterEmbedding, counterFaces] at *

def counterOuterAmbientBoundary : Finset counterGraph.edgeSet := {eo}
def counterInnerAmbientBoundary : Finset counterGraph.edgeSet := {eiq, ei1, ei2}

def counterCollarFaces : Fin 3 → Finset (AmbientFace counterEmbedding.faces)
  | ⟨0, _⟩ => {fa}
  | ⟨1, _⟩ => {fbPrev, fbBad}
  | ⟨2, _⟩ => {fcq, fcr1, fcr2}

def counterBoundaryCycle : Fin 4 → Finset counterGraph.edgeSet
  | ⟨0, _⟩ => {eo}
  | ⟨1, _⟩ => {ep}
  | ⟨2, _⟩ => {eqEdge, er1, er2}
  | ⟨3, _⟩ => {eiq, ei1, ei2}

def counterBoundaryData : PlanarBoundaryAnnulusBoundaryData counterEmbedding := by
  refine
    { outerAmbientBoundary := counterOuterAmbientBoundary
      innerAmbientBoundary := counterInnerAmbientBoundary
      houterAmbientBoundaryNonempty := by decide
      hinnerAmbientBoundaryNonempty := by decide
      houterAmbientBoundarySubset := by decide
      hinnerAmbientBoundarySubset := by decide
      hambientBoundaryCover := by decide
      hambientBoundaryDisjoint := by decide }

def counterDecomp : PlanarBoundaryAnnulusDecomposition counterEmbedding := by
  refine
    { toPlanarBoundaryAnnulusBoundaryData := counterBoundaryData
      numCollars := 3
      collarFaces := counterCollarFaces
      remainderFaces := laterLayerFaces counterCollarFaces
      boundaryCycle := counterBoundaryCycle
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

def counterWitnessEdge : AmbientFace counterEmbedding.faces → counterGraph.edgeSet
  | ⟨⟨0, _⟩, _⟩ => eo
  | ⟨⟨1, _⟩, _⟩ => ep
  | ⟨⟨2, _⟩, _⟩ => eqEdge
  | ⟨⟨3, _⟩, _⟩ => eqEdge
  | ⟨⟨4, _⟩, _⟩ => er1
  | ⟨⟨5, _⟩, _⟩ => er2

/-- A valid annulus collar geometry whose second collar contains a face with witness edge `eqEdge`.
That edge lies on the later boundary cycle `Γ₂`, but not on the previous cycle `Γ₁`. -/
def counterCollarGeometry : PlanarBoundaryAnnulusCollarGeometry counterEmbedding := by
  refine
    { toPlanarBoundaryAnnulusDecomposition := counterDecomp
      witnessEdge := counterWitnessEdge
      hcover := by decide
      hwitness := by decide
      hrest := by decide
      hfrontier := by decide }

def counterMiddleIndex : Fin counterCollarGeometry.numCollars := ⟨1, by decide⟩
def counterBadFace : AmbientFace counterEmbedding.faces := fbBad

theorem counterBadFace_mem_middleCollar :
    counterBadFace ∈ counterCollarGeometry.collarFaces counterMiddleIndex := by
  decide

theorem counterBadFace_witness_not_mem_previousBoundaryCycle :
    counterCollarGeometry.witnessEdge counterBadFace ∉
      counterCollarGeometry.boundaryCycle (Fin.castSucc counterMiddleIndex) := by
  decide

theorem counterBadFace_witness_not_mem_currentBoundary :
    counterCollarGeometry.witnessEdge counterBadFace ∉
      counterCollarGeometry.toPlanarBoundaryAnnulusCurrentBoundaryData.currentBoundary
        counterMiddleIndex := by
  simpa [PlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusCurrentBoundaryData] using
    counterBadFace_witness_not_mem_previousBoundaryCycle

/-- The current annulus collar geometry axioms do not imply that every positive-collar witness edge
lies on the previous annulus boundary cycle. The explicit counterexample `counterCollarGeometry`
satisfies all present fields while violating that extra property on the middle collar face
`fbBad`. -/
theorem not_forall_previousBoundaryWitness_counterCollarGeometry :
    ¬ (∀ {j : Fin counterCollarGeometry.numCollars} {g : AmbientFace counterEmbedding.faces},
      g ∈ counterCollarGeometry.collarFaces j → 0 < j.1 →
        counterCollarGeometry.witnessEdge g ∈
          counterCollarGeometry.boundaryCycle (Fin.castSucc j)) := by
  intro h
  exact counterBadFace_witness_not_mem_previousBoundaryCycle
    (h counterBadFace_mem_middleCollar (by decide))

/-- Current-boundary-shell form of the same obstruction: even phrased directly on the concrete
current outer frontier at collar stage `j`, the missing witness-placement property is not implied
by the present collar geometry axioms. -/
theorem not_witnessOnCurrentBoundary_counterCollarGeometry :
    ¬ PlanarBoundaryAnnulusCollarGeometry.WitnessOnCurrentBoundary counterCollarGeometry := by
  intro h
  exact counterBadFace_witness_not_mem_currentBoundary
    (h counterBadFace_mem_middleCollar (by decide))

/-- The concrete weak collar geometry lowers to the BFS-style annulus construction layer. -/
noncomputable def counterAnnulusConstruction :
    PlanarBoundaryAnnulusConstruction counterEmbedding :=
  planarBoundaryAnnulusConstruction_of_annulusCollarGeometry counterCollarGeometry

theorem counterBadFace_mem_counterAnnulusConstruction_peelFaces :
    counterBadFace ∈ counterAnnulusConstruction.peelFaces := by
  decide

theorem counterAnnulusConstruction_faceDistance_fa :
    counterAnnulusConstruction.faceDistance fa = 0 := by
  rfl

theorem counterAnnulusConstruction_faceDistance_fbPrev :
    counterAnnulusConstruction.faceDistance fbPrev = 1 := by
  rfl

theorem counterAnnulusConstruction_faceDistance_fbBad :
    counterAnnulusConstruction.faceDistance fbBad = 1 := by
  rfl

theorem counterAnnulusConstruction_faceDistance_counterBadFace :
    counterAnnulusConstruction.faceDistance counterBadFace = 1 := by
  rfl

theorem counterAnnulusConstruction_faceDistance_fcq :
    counterAnnulusConstruction.faceDistance fcq = 2 := by
  rfl

theorem counterAnnulusConstruction_faceDistance_fcr1 :
    counterAnnulusConstruction.faceDistance fcr1 = 2 := by
  rfl

theorem counterAnnulusConstruction_faceDistance_fcr2 :
    counterAnnulusConstruction.faceDistance fcr2 = 2 := by
  rfl

theorem counterAnnulusConstruction_witness_counterBadFace :
    counterAnnulusConstruction.witnessEdge counterBadFace = eqEdge := by
  rfl

theorem eqEdge_not_mem_fa_boundary :
    eqEdge ∉ counterEmbedding.faceBoundary fa.1 := by
  decide

/-- Lowering a weak collar geometry to the construction layer still does not supply the strict
parent-witness orientation needed by the well-founded annulus route.  The bad middle-collar face
has witness edge `eqEdge`; the only lower-distance face has boundary `{eo, ep}`, while every face
that actually contains `eqEdge` has distance at least as large as the bad face. -/
theorem not_parentWitnessOrientation_counterAnnulusConstruction :
    ¬ counterAnnulusConstruction.ParentWitnessOrientation := by
  intro h
  rcases h counterBadFace counterBadFace_mem_counterAnnulusConstruction_peelFaces with
    ⟨p, hp, hlt⟩
  rw [counterAnnulusConstruction_witness_counterBadFace] at hp
  rcases ambientFace_eq_cases p with rfl | rfl | rfl | rfl | rfl | rfl
  · exact eqEdge_not_mem_fa_boundary hp
  · rw [counterAnnulusConstruction_faceDistance_fbPrev,
      counterAnnulusConstruction_faceDistance_counterBadFace] at hlt
    omega
  · rw [counterAnnulusConstruction_faceDistance_fbBad,
      counterAnnulusConstruction_faceDistance_counterBadFace] at hlt
    omega
  · rw [counterAnnulusConstruction_faceDistance_fcq,
      counterAnnulusConstruction_faceDistance_counterBadFace] at hlt
    omega
  · rw [counterAnnulusConstruction_faceDistance_fcr1,
      counterAnnulusConstruction_faceDistance_counterBadFace] at hlt
    omega
  · rw [counterAnnulusConstruction_faceDistance_fcr2,
      counterAnnulusConstruction_faceDistance_counterBadFace] at hlt
    omega

/-- The collar-geometry counterexample survives the canonical lowering to the annulus
construction layer: the present collar axioms do not imply parent-witness orientation. -/
theorem collarGeometry_does_not_imply_parentWitnessOrientation_counterexample :
    Nonempty (PlanarBoundaryAnnulusCollarGeometry counterEmbedding) ∧
      ¬ counterAnnulusConstruction.ParentWitnessOrientation := by
  exact ⟨⟨counterCollarGeometry⟩, not_parentWitnessOrientation_counterAnnulusConstruction⟩

/-- Existential form of the checked obstruction: there is a concrete bundled annulus collar
geometry satisfying the current API but failing the proposed previous-boundary witness property. -/
theorem exists_planarBoundaryAnnulusCollarGeometry_without_previousBoundaryWitness :
    ∃ emb : PlaneEmbeddingWithBoundary counterGraph,
      ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
        ¬ (∀ {j : Fin data.numCollars} {g : AmbientFace emb.faces},
          g ∈ data.collarFaces j → 0 < j.1 →
            data.witnessEdge g ∈ data.boundaryCycle (Fin.castSucc j)) := by
  refine ⟨counterEmbedding, counterCollarGeometry, ?_⟩
  exact not_forall_previousBoundaryWitness_counterCollarGeometry

theorem exists_planarBoundaryAnnulusCollarGeometry_without_witnessOnCurrentBoundary :
    ∃ emb : PlaneEmbeddingWithBoundary counterGraph,
      ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
        ¬ PlanarBoundaryAnnulusCollarGeometry.WitnessOnCurrentBoundary data := by
  refine ⟨counterEmbedding, counterCollarGeometry, ?_⟩
  exact not_witnessOnCurrentBoundary_counterCollarGeometry

theorem exists_planarBoundaryAnnulusConstruction_without_parentWitnessOrientation :
    ∃ emb : PlaneEmbeddingWithBoundary counterGraph,
      ∃ data : PlanarBoundaryAnnulusConstruction emb,
        ¬ data.ParentWitnessOrientation := by
  exact ⟨counterEmbedding, counterAnnulusConstruction,
    not_parentWitnessOrientation_counterAnnulusConstruction⟩

/-- A three-face annulus boundary model whose middle face has two interior edges. The ambient
boundary split is valid, so the canonical one-collar decomposition exists, but that particular
decomposition cannot carry any witness assignment because the middle face has no way to leave all
non-witness edges on ambient boundaries. -/
def canonicalWitnessCounterGraph : SimpleGraph (Fin 8) :=
  SimpleGraph.fromEdgeSet
    ({s(0, 1), s(2, 3), s(4, 5), s(6, 7)} : Set (Sym2 (Fin 8)))

def cwo : canonicalWitnessCounterGraph.edgeSet := ⟨s(0, 1), by simp [canonicalWitnessCounterGraph]⟩
def cwi₁ : canonicalWitnessCounterGraph.edgeSet := ⟨s(2, 3), by simp [canonicalWitnessCounterGraph]⟩
def cwi₂ : canonicalWitnessCounterGraph.edgeSet := ⟨s(4, 5), by simp [canonicalWitnessCounterGraph]⟩
def cwi : canonicalWitnessCounterGraph.edgeSet := ⟨s(6, 7), by simp [canonicalWitnessCounterGraph]⟩

theorem canonicalWitnessCounter_edge_eq_cases (e : canonicalWitnessCounterGraph.edgeSet) :
    e = cwo ∨ e = cwi₁ ∨ e = cwi₂ ∨ e = cwi := by
  have h :
      (e.1 = s(0, 1) ∨ e.1 = s(2, 3) ∨ e.1 = s(4, 5) ∨ e.1 = s(6, 7)) ∧
        ¬ e.1.IsDiag := by
    simpa [canonicalWitnessCounterGraph] using e.2
  rcases h.1 with h0 | h1 | h2 | h3
  · exact Or.inl (Subtype.ext h0)
  · exact Or.inr <| Or.inl (Subtype.ext h1)
  · exact Or.inr <| Or.inr <| Or.inl (Subtype.ext h2)
  · exact Or.inr <| Or.inr <| Or.inr (Subtype.ext h3)

abbrev CanonicalWitnessCounterFace := Fin 3

def canonicalWitnessCounterFaces : Finset CanonicalWitnessCounterFace := Finset.univ

def canonicalWitnessCounterFaceBoundary :
    CanonicalWitnessCounterFace → Finset canonicalWitnessCounterGraph.edgeSet
  | ⟨0, _⟩ => {cwo, cwi₁}
  | ⟨1, _⟩ => {cwi₁, cwi₂}
  | ⟨2, _⟩ => {cwi₂, cwi}

def canonicalWitnessCounterEmbedding : PlaneEmbeddingWithBoundary canonicalWitnessCounterGraph where
  Face := CanonicalWitnessCounterFace
  faceDecidableEq := inferInstance
  faces := canonicalWitnessCounterFaces
  faceBoundary := canonicalWitnessCounterFaceBoundary
  edge_mem_faceSupport := by
    intro e
    rcases canonicalWitnessCounter_edge_eq_cases e with rfl | rfl | rfl | rfl <;>
      decide
  edge_one_or_two_faces := by
    intro e _he
    rcases canonicalWitnessCounter_edge_eq_cases e with rfl | rfl | rfl | rfl <;>
      decide

def cwf0 : CanonicalWitnessCounterFace := ⟨0, by decide⟩
def cwf1 : CanonicalWitnessCounterFace := ⟨1, by decide⟩
def cwf2 : CanonicalWitnessCounterFace := ⟨2, by decide⟩

def cwOuterFace : AmbientFace canonicalWitnessCounterEmbedding.faces :=
  ⟨cwf0, by simp [canonicalWitnessCounterEmbedding, canonicalWitnessCounterFaces, cwf0]⟩

def cwMiddleFace : AmbientFace canonicalWitnessCounterEmbedding.faces :=
  ⟨cwf1, by simp [canonicalWitnessCounterEmbedding, canonicalWitnessCounterFaces, cwf1]⟩

def cwInnerFace : AmbientFace canonicalWitnessCounterEmbedding.faces :=
  ⟨cwf2, by simp [canonicalWitnessCounterEmbedding, canonicalWitnessCounterFaces, cwf2]⟩

def canonicalWitnessCounterBoundaryData :
    PlanarBoundaryAnnulusBoundaryData canonicalWitnessCounterEmbedding := by
  refine
    { outerAmbientBoundary := {cwo}
      innerAmbientBoundary := {cwi}
      houterAmbientBoundaryNonempty := by decide
      hinnerAmbientBoundaryNonempty := by decide
      houterAmbientBoundarySubset := by decide
      hinnerAmbientBoundarySubset := by decide
      hambientBoundaryCover := by decide
      hambientBoundaryDisjoint := by decide }

def canonicalWitnessCounterCanonicalDecomposition :
    PlanarBoundaryAnnulusDecomposition canonicalWitnessCounterEmbedding :=
  planarBoundaryAnnulusDecomposition_of_boundaryData canonicalWitnessCounterBoundaryData

theorem cwMiddleFace_mem_canonicalWitnessCounterCanonicalDecomposition_collarFaces :
    cwMiddleFace ∈
      canonicalWitnessCounterCanonicalDecomposition.collarFaces ⟨0, by decide⟩ := by
  simp [canonicalWitnessCounterCanonicalDecomposition,
    planarBoundaryAnnulusDecomposition_of_boundaryData, cwMiddleFace,
    canonicalWitnessCounterEmbedding, canonicalWitnessCounterFaces]

theorem exists_two_distinct_interior_edges_on_cwMiddleFace_boundary :
    ∃ e₁ ∈ canonicalWitnessCounterEmbedding.faceBoundary cwMiddleFace.1,
      ∃ e₂ ∈ canonicalWitnessCounterEmbedding.faceBoundary cwMiddleFace.1,
        e₁ ≠ e₂ ∧
          e₁ ∈ interiorEdgeSupport
            canonicalWitnessCounterEmbedding.faceBoundary canonicalWitnessCounterEmbedding.faces ∧
            e₂ ∈ interiorEdgeSupport
              canonicalWitnessCounterEmbedding.faceBoundary canonicalWitnessCounterEmbedding.faces := by
  refine ⟨cwi₁, ?_, cwi₂, ?_, ?_, ?_, ?_⟩ <;> decide

theorem not_nonempty_planarBoundaryAnnulusWitnessAssignment_canonicalWitnessCounterCanonicalDecomposition :
    ¬ Nonempty
      (PlanarBoundaryAnnulusWitnessAssignment
        canonicalWitnessCounterCanonicalDecomposition) := by
  exact
    not_nonempty_planarBoundaryAnnulusWitnessAssignment_of_exists_two_distinct_interior_edges_on_faceBoundary_of_canonicalDecomposition
      canonicalWitnessCounterBoundaryData
      ⟨cwMiddleFace, exists_two_distinct_interior_edges_on_cwMiddleFace_boundary⟩

theorem not_nonempty_planarBoundaryCanonicalWitnessChoice_canonicalWitnessCounterBoundaryData :
    ¬ Nonempty
      (PlanarBoundaryCanonicalWitnessChoice canonicalWitnessCounterBoundaryData) := by
  exact
    not_nonempty_planarBoundaryCanonicalWitnessChoice_of_exists_two_distinct_interior_edges_on_faceBoundary
      canonicalWitnessCounterBoundaryData
      ⟨cwMiddleFace, exists_two_distinct_interior_edges_on_cwMiddleFace_boundary⟩

/-- The canonical one-collar decomposition built from annulus boundary data does not, in general,
already carry the witness-edge ownership needed for Step 2. The countermodel above has valid
annulus boundary data, but its canonical decomposition admits no witness assignment at all. -/
theorem
    exists_planarBoundaryAnnulusBoundaryData_whose_canonicalDecomposition_has_noWitnessAssignment :
    ∃ emb : PlaneEmbeddingWithBoundary canonicalWitnessCounterGraph,
      ∃ data : PlanarBoundaryAnnulusBoundaryData emb,
        ¬ Nonempty (PlanarBoundaryAnnulusWitnessAssignment
          (planarBoundaryAnnulusDecomposition_of_boundaryData data)) := by
  exact ⟨canonicalWitnessCounterEmbedding, canonicalWitnessCounterBoundaryData,
    not_nonempty_planarBoundaryAnnulusWitnessAssignment_canonicalWitnessCounterCanonicalDecomposition⟩

/-- The stronger explicit repair surface also fails on the same boundary data: there is no
canonical facewise witness choice whose upgrade could produce witness ownership. -/
theorem
    exists_planarBoundaryAnnulusBoundaryData_whose_has_noCanonicalWitnessChoice :
    ∃ emb : PlaneEmbeddingWithBoundary canonicalWitnessCounterGraph,
      ∃ data : PlanarBoundaryAnnulusBoundaryData emb,
        ¬ Nonempty (PlanarBoundaryCanonicalWitnessChoice data) := by
  exact ⟨canonicalWitnessCounterEmbedding, canonicalWitnessCounterBoundaryData,
    not_nonempty_planarBoundaryCanonicalWitnessChoice_canonicalWitnessCounterBoundaryData⟩

/-- Universal failed-converse form of the same obstruction: no theorem can derive witness-edge
ownership for the canonical one-collar decomposition from arbitrary annulus boundary data alone. -/
theorem
    not_forall_planarBoundaryAnnulusBoundaryData_implies_nonempty_witnessAssignment_on_canonicalDecomposition :
    ¬ (∀ {G : SimpleGraph (Fin 8)} {emb : PlaneEmbeddingWithBoundary G}
        (data : PlanarBoundaryAnnulusBoundaryData emb),
        Nonempty (PlanarBoundaryAnnulusWitnessAssignment
          (planarBoundaryAnnulusDecomposition_of_boundaryData data))) := by
  intro h
  exact
    not_nonempty_planarBoundaryAnnulusWitnessAssignment_canonicalWitnessCounterCanonicalDecomposition
      (h canonicalWitnessCounterBoundaryData)

/-- Universal failed-converse form for the newer explicit repair theorem: arbitrary annulus
boundary data does not force a canonical facewise witness choice. -/
theorem
    not_forall_planarBoundaryAnnulusBoundaryData_implies_nonempty_canonicalWitnessChoice :
    ¬ (∀ {G : SimpleGraph (Fin 8)} {emb : PlaneEmbeddingWithBoundary G}
        (data : PlanarBoundaryAnnulusBoundaryData emb),
        Nonempty (PlanarBoundaryCanonicalWitnessChoice data)) := by
  intro h
  exact
    not_nonempty_planarBoundaryCanonicalWitnessChoice_canonicalWitnessCounterBoundaryData
      (h canonicalWitnessCounterBoundaryData)

end Theorem49PlanarBoundaryAnnulusWitnessRegression

end Mettapedia.GraphTheory.FourColor
