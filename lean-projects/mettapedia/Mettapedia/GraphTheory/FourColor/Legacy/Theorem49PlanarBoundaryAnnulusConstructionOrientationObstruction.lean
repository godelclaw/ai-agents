import Mettapedia.GraphTheory.FourColor.PlanarBoundaryAnnulusConstruction
import Mathlib.Tactic

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

namespace Theorem49PlanarBoundaryAnnulusConstructionOrientationObstruction

variable {V : Type*} [DecidableEq V]

/-- A tiny disconnected graph with five distinct edges. This supports a construction-side annulus
counterexample where current-frontier witness membership still does not force lower-distance
parent orientation. -/
def counterGraph : SimpleGraph (Fin 10) :=
  SimpleGraph.fromEdgeSet
    ({s(0, 1), s(2, 3), s(4, 5), s(6, 7), s(8, 9)} : Set (Sym2 (Fin 10)))

def eo : counterGraph.edgeSet := ⟨s(0, 1), by simp [counterGraph]⟩
def eqEdge : counterGraph.edgeSet := ⟨s(2, 3), by simp [counterGraph]⟩
def er : counterGraph.edgeSet := ⟨s(4, 5), by simp [counterGraph]⟩
def eu : counterGraph.edgeSet := ⟨s(6, 7), by simp [counterGraph]⟩
def ei : counterGraph.edgeSet := ⟨s(8, 9), by simp [counterGraph]⟩

theorem edge_eq_cases (e : counterGraph.edgeSet) :
    e = eo ∨ e = eqEdge ∨ e = er ∨ e = eu ∨ e = ei := by
  have h :
      (e.1 = s(0, 1) ∨ e.1 = s(2, 3) ∨ e.1 = s(4, 5) ∨ e.1 = s(6, 7) ∨
        e.1 = s(8, 9)) ∧
        ¬ e.1.IsDiag := by
    simpa [counterGraph] using e.2
  rcases h.1 with h0 | h1 | h2 | h3 | h4
  · exact Or.inl (Subtype.ext h0)
  · exact Or.inr <| Or.inl (Subtype.ext h1)
  · exact Or.inr <| Or.inr <| Or.inl (Subtype.ext h2)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext h3)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr (Subtype.ext h4)

abbrev CounterFace := Fin 5

def counterFaces : Finset CounterFace := Finset.univ

def counterFaceBoundary : CounterFace → Finset counterGraph.edgeSet
  | ⟨0, _⟩ => {eo, eqEdge}
  | ⟨1, _⟩ => {eqEdge, er}
  | ⟨2, _⟩ => {er}
  | ⟨3, _⟩ => {eu}
  | ⟨4, _⟩ => {eu, ei}

def counterEmbedding : PlaneEmbeddingWithBoundary counterGraph where
  Face := CounterFace
  faceDecidableEq := inferInstance
  faces := counterFaces
  faceBoundary := counterFaceBoundary
  edge_mem_faceSupport := by
    intro e
    rcases edge_eq_cases e with rfl | rfl | rfl | rfl | rfl <;> decide
  edge_one_or_two_faces := by
    intro e _he
    rcases edge_eq_cases e with rfl | rfl | rfl | rfl | rfl <;> decide

def f0 : CounterFace := ⟨0, by decide⟩
def f1 : CounterFace := ⟨1, by decide⟩
def f2 : CounterFace := ⟨2, by decide⟩
def f3 : CounterFace := ⟨3, by decide⟩
def f4 : CounterFace := ⟨4, by decide⟩

def fo : AmbientFace counterEmbedding.faces := ⟨f0, by simp [counterEmbedding, counterFaces, f0]⟩
def fg : AmbientFace counterEmbedding.faces := ⟨f1, by simp [counterEmbedding, counterFaces, f1]⟩
def fh : AmbientFace counterEmbedding.faces := ⟨f2, by simp [counterEmbedding, counterFaces, f2]⟩
def fd : AmbientFace counterEmbedding.faces := ⟨f3, by simp [counterEmbedding, counterFaces, f3]⟩
def fi : AmbientFace counterEmbedding.faces := ⟨f4, by simp [counterEmbedding, counterFaces, f4]⟩

/-- The construction-side annulus object. The peeled faces form two strata:
`fg` at height `0`, and `fh`, `fd` at height `1`. The bad witness is `eqEdge` on `fg`, which lies
on the first positive current outer frontier but can only see the outer-boundary face `fo`. -/
def counterConstruction : PlanarBoundaryAnnulusConstruction counterEmbedding := by
  refine
    { outerAmbientBoundary := {eo}
      innerAmbientBoundary := {ei}
      houterAmbientBoundaryNonempty := by decide
      hinnerAmbientBoundaryNonempty := by decide
      houterAmbientBoundarySubset := by decide
      hinnerAmbientBoundarySubset := by decide
      hambientBoundaryCover := by decide
      hambientBoundaryDisjoint := by decide
      peelFaces := {fg, fh, fd}
      witnessEdge := fun f =>
        if f = fg then eqEdge else if f = fh then er else eu
      faceDistance := fun f =>
        if f = fg then 0 else if f = fh then 1 else if f = fd then 1 else 0
      hcover := by decide
      hwitness := by decide
      hrest := by decide }

def counterBadFace : AmbientFace counterEmbedding.faces := fg

def counterBadStratum : Fin counterConstruction.numStrata := ⟨0, by decide⟩

def counterBadStage : Fin counterConstruction.numCollars :=
  counterConstruction.stratumStage counterBadStratum

theorem counterBadFace_mem_peelFaces :
    counterBadFace ∈ counterConstruction.peelFaces := by
  decide

theorem counterBadFace_mem_badStage :
    counterBadFace ∈ counterConstruction.collarFaces counterBadStage := by
  decide

theorem counterBadStage_pos :
    0 < counterBadStage.1 := by
  decide

theorem counterBadFace_witness_mem_currentOuterBoundary :
    counterConstruction.witnessEdge counterBadFace ∈
      counterConstruction.currentOuterBoundary counterBadStage := by
  decide

theorem counterBadFace_no_parentWitness :
    ¬ ∃ p : AmbientFace counterEmbedding.faces,
      counterConstruction.witnessEdge counterBadFace ∈ counterEmbedding.faceBoundary p.1 ∧
        counterConstruction.faceDistance p < counterConstruction.faceDistance counterBadFace := by
  intro h
  rcases h with ⟨p, _, hp⟩
  have hbad : counterConstruction.faceDistance counterBadFace = 0 := by
    simp [counterConstruction, counterBadFace, fg]
  rw [hbad] at hp
  omega

theorem not_counterConstructionParentWitnessOrientation :
    ¬ counterConstruction.ParentWitnessOrientation := by
  intro horient
  exact counterBadFace_no_parentWitness (horient counterBadFace counterBadFace_mem_peelFaces)

/-- A variant of the counterconstruction where every peeled face has positive stored
face-distance.  The bad witness on `fg` still only sees faces of distance `1`, so positivity of
peeled strata alone is not parent orientation. -/
def counterPositiveDistanceConstruction : PlanarBoundaryAnnulusConstruction counterEmbedding := by
  refine
    { outerAmbientBoundary := {eo}
      innerAmbientBoundary := {ei}
      houterAmbientBoundaryNonempty := by decide
      hinnerAmbientBoundaryNonempty := by decide
      houterAmbientBoundarySubset := by decide
      hinnerAmbientBoundarySubset := by decide
      hambientBoundaryCover := by decide
      hambientBoundaryDisjoint := by decide
      peelFaces := {fg, fh, fd}
      witnessEdge := fun f =>
        if f = fg then eqEdge else if f = fh then er else eu
      faceDistance := fun f =>
        if f = fg then 1 else if f = fh then 2 else if f = fd then 1 else if f = fo then 1 else 0
      hcover := by decide
      hwitness := by decide
      hrest := by decide }

theorem counterPositiveDistance_all_peelFaces_positive :
    ∀ g ∈ counterPositiveDistanceConstruction.peelFaces,
      0 < counterPositiveDistanceConstruction.faceDistance g := by
  decide

theorem counterPositiveDistanceBadFace_no_parentWitness :
    ¬ ∃ p : AmbientFace counterEmbedding.faces,
      counterPositiveDistanceConstruction.witnessEdge counterBadFace ∈
          counterEmbedding.faceBoundary p.1 ∧
        counterPositiveDistanceConstruction.faceDistance p <
          counterPositiveDistanceConstruction.faceDistance counterBadFace := by
  decide

theorem not_counterPositiveDistanceConstructionParentWitnessOrientation :
    ¬ counterPositiveDistanceConstruction.ParentWitnessOrientation := by
  intro horient
  have hbad : counterBadFace ∈ counterPositiveDistanceConstruction.peelFaces := by
    decide
  exact counterPositiveDistanceBadFace_no_parentWitness (horient counterBadFace hbad)

/-- Positive stored distance for every peeled face is still not enough to force a
construction-level parent witness.  The missing datum is incidence with a strictly earlier face,
not merely a nonzero stratum index. -/
theorem
    not_forall_planarBoundaryAnnulusConstruction_positive_faceDistance_implies_parentWitnessOrientation :
    ¬ (∀ {emb : PlaneEmbeddingWithBoundary counterGraph},
        (data : PlanarBoundaryAnnulusConstruction emb) →
          (∀ g ∈ data.peelFaces, 0 < data.faceDistance g) →
            data.ParentWitnessOrientation) := by
  intro h
  have horient : counterPositiveDistanceConstruction.ParentWitnessOrientation :=
    h (emb := counterEmbedding) counterPositiveDistanceConstruction
      counterPositiveDistance_all_peelFaces_positive
  exact not_counterPositiveDistanceConstructionParentWitnessOrientation horient

theorem counterInteriorEdgeSupport_nonempty :
    (interiorEdgeSupport counterEmbedding.faceBoundary counterEmbedding.faces).Nonempty := by
  exact ⟨eqEdge, by decide⟩

/-- The terminal strict-dependency break is not a substitute for parent-witness orientation.
Even with live interior-edge support and a peeled face with no outgoing construction-level
`remainderDependency`, the construction-side parent-orientation surface can still fail. -/
theorem not_forall_live_planarBoundaryAnnulusConstruction_terminalNoDependency_implies_parentWitnessOrientation :
    ¬ (∀ {emb : PlaneEmbeddingWithBoundary counterGraph},
        (data : PlanarBoundaryAnnulusConstruction emb) →
          (interiorEdgeSupport emb.faceBoundary emb.faces).Nonempty →
            (∃ f ∈ data.peelFaces,
              ∀ g : AmbientFace emb.faces, ¬ data.remainderDependency f g) →
              data.ParentWitnessOrientation) := by
  intro h
  have hterminal :
      ∃ f ∈ counterConstruction.peelFaces,
        ∀ g : AmbientFace counterEmbedding.faces,
          ¬ counterConstruction.remainderDependency f g :=
    counterConstruction.exists_terminal_peelFace_no_remainderDependency
      (counterConstruction.peelFaces_nonempty_of_interiorEdgeSupport_nonempty
        counterInteriorEdgeSupport_nonempty)
  have horient : counterConstruction.ParentWitnessOrientation :=
    h (emb := counterEmbedding) counterConstruction counterInteriorEdgeSupport_nonempty hterminal
  exact not_counterConstructionParentWitnessOrientation horient

def counterFacePartitionData :
    PlanarBoundaryAnnulusConstructionFacePartitionData counterEmbedding := by
  refine
    { construction := counterConstruction
      hpeelInterior := by decide
      hfaceCover := by decide
      hboundaryFaceDisjoint := by decide
      hcurrentOuterBoundaryNonempty := by decide
      hcurrentOuterBoundaryDisjoint := by decide }

def counterPositiveFrontierData :
    PlanarBoundaryAnnulusConstructionPositiveFrontierData counterEmbedding :=
  counterFacePartitionData.toPositiveFrontierData

def counterBoundarySupportFaceData :
    PlanarBoundaryAnnulusConstructionBoundarySupportFaceData counterEmbedding :=
  counterFacePartitionData.toBoundarySupportFaceData

theorem exists_planarBoundaryAnnulusConstructionFacePartitionData_with_currentOuterBoundaryWitness_and_without_parentOrientation :
    ∃ emb : PlaneEmbeddingWithBoundary counterGraph,
      ∃ data : PlanarBoundaryAnnulusConstructionFacePartitionData emb,
        ∃ i : Fin data.construction.numCollars,
          ∃ g : AmbientFace emb.faces,
            0 < i.1 ∧
              g ∈ data.construction.collarFaces i ∧
              data.construction.witnessEdge g ∈ data.construction.currentOuterBoundary i ∧
              ¬ ∃ p : AmbientFace emb.faces,
                data.construction.witnessEdge g ∈ emb.faceBoundary p.1 ∧
                  data.construction.faceDistance p < data.construction.faceDistance g := by
  refine ⟨counterEmbedding, counterFacePartitionData, counterBadStage, counterBadFace, ?_⟩
  exact ⟨counterBadStage_pos, counterBadFace_mem_badStage,
    counterBadFace_witness_mem_currentOuterBoundary, counterBadFace_no_parentWitness⟩

theorem exists_planarBoundaryAnnulusConstructionFacePartitionData_without_parentOrientation :
    ∃ emb : PlaneEmbeddingWithBoundary counterGraph,
      ∃ data : PlanarBoundaryAnnulusConstructionFacePartitionData emb,
        ¬ data.construction.ParentWitnessOrientation := by
  refine ⟨counterEmbedding, counterFacePartitionData, ?_⟩
  exact not_counterConstructionParentWitnessOrientation

/-- Clean theorem-level impossibility statement: the present face-partition shell is insufficient
to force parent-witness orientation. -/
theorem not_forall_planarBoundaryAnnulusConstructionFacePartitionData_implies_parentWitnessOrientation :
    ¬ (∀ {emb : PlaneEmbeddingWithBoundary counterGraph},
        (data : PlanarBoundaryAnnulusConstructionFacePartitionData emb) →
          data.construction.ParentWitnessOrientation) := by
  intro h
  have horient : counterConstruction.ParentWitnessOrientation := by
    simpa [counterFacePartitionData] using
      h (emb := counterEmbedding) counterFacePartitionData
  exact not_counterConstructionParentWitnessOrientation horient

theorem exists_planarBoundaryAnnulusConstructionPositiveFrontierData_without_parentOrientation :
    ∃ emb : PlaneEmbeddingWithBoundary counterGraph,
      ∃ data : PlanarBoundaryAnnulusConstructionPositiveFrontierData emb,
        ¬ data.construction.ParentWitnessOrientation := by
  refine ⟨counterEmbedding, counterPositiveFrontierData, ?_⟩
  exact not_counterConstructionParentWitnessOrientation

/-- The reduced positive-frontier shell still does not force parent-witness orientation. -/
theorem not_forall_planarBoundaryAnnulusConstructionPositiveFrontierData_implies_parentWitnessOrientation :
    ¬ (∀ {emb : PlaneEmbeddingWithBoundary counterGraph},
        (data : PlanarBoundaryAnnulusConstructionPositiveFrontierData emb) →
          data.construction.ParentWitnessOrientation) := by
  intro h
  have horient : counterConstruction.ParentWitnessOrientation := by
    simpa [counterPositiveFrontierData, counterFacePartitionData,
      PlanarBoundaryAnnulusConstructionFacePartitionData.toPositiveFrontierData] using
      h (emb := counterEmbedding) counterPositiveFrontierData
  exact not_counterConstructionParentWitnessOrientation horient

theorem exists_planarBoundaryAnnulusConstructionBoundarySupportFaceData_without_parentOrientation :
    ∃ emb : PlaneEmbeddingWithBoundary counterGraph,
      ∃ data : PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb,
        ¬ data.construction.ParentWitnessOrientation := by
  refine ⟨counterEmbedding, counterBoundarySupportFaceData, ?_⟩
  exact not_counterConstructionParentWitnessOrientation

/-- The selected-boundary contact shell still does not force parent-witness orientation. -/
theorem not_forall_planarBoundaryAnnulusConstructionBoundarySupportFaceData_implies_parentWitnessOrientation :
    ¬ (∀ {emb : PlaneEmbeddingWithBoundary counterGraph},
        (data : PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb) →
          data.construction.ParentWitnessOrientation) := by
  intro h
  have horient : counterConstruction.ParentWitnessOrientation := by
    simpa [counterBoundarySupportFaceData, counterFacePartitionData,
      PlanarBoundaryAnnulusConstructionFacePartitionData.toBoundarySupportFaceData] using
      h (emb := counterEmbedding) counterBoundarySupportFaceData
  exact not_counterConstructionParentWitnessOrientation horient

theorem exists_planarBoundaryAnnulusConstructionFaceLayerData_without_parentOrientation :
    ∃ emb : PlaneEmbeddingWithBoundary counterGraph,
      ∃ data : PlanarBoundaryAnnulusConstructionFaceLayerData emb,
        ¬ data.construction.ParentWitnessOrientation := by
  refine ⟨counterEmbedding,
    counterFacePartitionData.toPlanarBoundaryAnnulusConstructionFaceLayerData, ?_⟩
  exact not_counterConstructionParentWitnessOrientation

/-- Clean theorem-level impossibility statement at the lowered face-layer shell as well. -/
theorem not_forall_planarBoundaryAnnulusConstructionFaceLayerData_implies_parentWitnessOrientation :
    ¬ (∀ {emb : PlaneEmbeddingWithBoundary counterGraph},
        (data : PlanarBoundaryAnnulusConstructionFaceLayerData emb) →
          data.construction.ParentWitnessOrientation) := by
  intro h
  have horient : counterConstruction.ParentWitnessOrientation := by
    simpa [counterFacePartitionData,
      PlanarBoundaryAnnulusConstructionFacePartitionData.toPlanarBoundaryAnnulusConstructionFaceLayerData,
      PlanarBoundaryAnnulusConstructionFacePartitionData.toPositiveFrontierData,
      PlanarBoundaryAnnulusConstructionPositiveFrontierData.toPlanarBoundaryAnnulusConstructionFaceLayerData] using
      h (emb := counterEmbedding)
        counterFacePartitionData.toPlanarBoundaryAnnulusConstructionFaceLayerData
  exact not_counterConstructionParentWitnessOrientation horient

end Theorem49PlanarBoundaryAnnulusConstructionOrientationObstruction

end Mettapedia.GraphTheory.FourColor
