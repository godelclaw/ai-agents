import Mettapedia.GraphTheory.FourColor.PlanarBoundaryAnnulusConstruction
import Mathlib.Tactic

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

namespace Theorem49PlanarBoundaryAnnulusGeometryRegression

variable {V : Type*} [DecidableEq V]

/-- A minimal two-face annulus geometry: one outer collar face and one inner collar face, sharing
exactly one intermediate boundary edge. This is enough to realize the repaired previous-boundary
witness geometry while still leaving the canonical annulus construction with a zero-distance first
collar face. -/
def counterGraph : SimpleGraph (Fin 6) :=
  SimpleGraph.fromEdgeSet
    ({s(0, 1), s(2, 3), s(4, 5)} : Set (Sym2 (Fin 6)))

def eo : counterGraph.edgeSet := ⟨s(0, 1), by simp [counterGraph]⟩
def em : counterGraph.edgeSet := ⟨s(2, 3), by simp [counterGraph]⟩
def ei : counterGraph.edgeSet := ⟨s(4, 5), by simp [counterGraph]⟩

theorem edge_eq_cases (e : counterGraph.edgeSet) :
    e = eo ∨ e = em ∨ e = ei := by
  have h : (e.1 = s(0, 1) ∨ e.1 = s(2, 3) ∨ e.1 = s(4, 5)) ∧ ¬ e.1.IsDiag := by
    simpa [counterGraph] using e.2
  rcases h.1 with h0 | h1 | h2
  · exact Or.inl (Subtype.ext h0)
  · exact Or.inr <| Or.inl (Subtype.ext h1)
  · exact Or.inr <| Or.inr (Subtype.ext h2)

abbrev CounterFace := Fin 2

def counterFaces : Finset CounterFace := Finset.univ

def counterFaceBoundary : CounterFace → Finset counterGraph.edgeSet
  | ⟨0, _⟩ => {eo, em}
  | ⟨1, _⟩ => {em, ei}

def counterEmbedding : PlaneEmbeddingWithBoundary counterGraph where
  Face := CounterFace
  faceDecidableEq := inferInstance
  faces := counterFaces
  faceBoundary := counterFaceBoundary
  edge_mem_faceSupport := by
    intro e
    rcases edge_eq_cases e with rfl | rfl | rfl <;> decide
  edge_one_or_two_faces := by
    intro e _he
    rcases edge_eq_cases e with rfl | rfl | rfl <;> decide

def fOuter : CounterFace := ⟨0, by decide⟩
def fInner : CounterFace := ⟨1, by decide⟩

def outerFace : AmbientFace counterEmbedding.faces :=
  ⟨fOuter, by simp [counterEmbedding, counterFaces, fOuter]⟩

def innerFace : AmbientFace counterEmbedding.faces :=
  ⟨fInner, by simp [counterEmbedding, counterFaces, fInner]⟩

def counterOuterAmbientBoundary : Finset counterGraph.edgeSet := {eo}
def counterInnerAmbientBoundary : Finset counterGraph.edgeSet := {ei}

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

def counterCollarFaces : Fin 2 → Finset (AmbientFace counterEmbedding.faces)
  | ⟨0, _⟩ => {outerFace}
  | ⟨1, _⟩ => {innerFace}

def counterBoundaryCycle : Fin 3 → Finset counterGraph.edgeSet
  | ⟨0, _⟩ => {eo}
  | ⟨1, _⟩ => {em}
  | ⟨2, _⟩ => {ei}

def counterDecomposition : PlanarBoundaryAnnulusDecomposition counterEmbedding := by
  refine
    { toPlanarBoundaryAnnulusBoundaryData := counterBoundaryData
      numCollars := 2
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
  | ⟨⟨1, _⟩, _⟩ => em

def counterCollarGeometry : PlanarBoundaryAnnulusCollarGeometry counterEmbedding := by
  refine
    { toPlanarBoundaryAnnulusDecomposition := counterDecomposition
      witnessEdge := counterWitnessEdge
      hcover := by decide
      hwitness := by decide
      hrest := by decide
      hfrontier := by decide }

def counterPreviousBoundaryWitnessGeometry :
    PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry counterEmbedding := by
  refine
    { toPlanarBoundaryAnnulusCollarGeometry := counterCollarGeometry
      hwitnessPrev := by decide }

theorem counterWitnessOnCurrentBoundary :
    counterCollarGeometry.WitnessOnCurrentBoundary := by
  exact
    (counterCollarGeometry.witnessOnCurrentBoundary_iff_previousBoundaryWitness).2
      counterPreviousBoundaryWitnessGeometry.hwitnessPrev

noncomputable def counterConstruction : PlanarBoundaryAnnulusConstruction counterEmbedding :=
  planarBoundaryAnnulusConstruction_of_annulusCollarGeometry counterCollarGeometry

theorem outerFace_mem_counterConstruction_peelFaces :
    outerFace ∈ counterConstruction.peelFaces := by
  decide

theorem counterConstruction_faceDistance_outerFace :
    counterConstruction.faceDistance outerFace = 0 := by
  rfl

theorem not_counterConstructionParentWitnessOrientation :
    ¬ counterConstruction.ParentWitnessOrientation := by
  intro horient
  rcases horient outerFace outerFace_mem_counterConstruction_peelFaces with ⟨p, _hp, hlt⟩
  rw [counterConstruction_faceDistance_outerFace] at hlt
  exact (Nat.not_lt_zero _ hlt).elim

theorem counterPreviousBoundaryWitnessGeometry_hasWellFoundedFacePeelWitnessData :
    Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData counterEmbedding) := by
  exact ⟨counterPreviousBoundaryWitnessGeometry.toPlanarBoundaryWellFoundedFacePeelWitnessData⟩

noncomputable def counterAttachedRootedFacePeelCertificate :
    PlanarBoundaryAttachedRootedFacePeelCertificate counterGraph :=
  counterPreviousBoundaryWitnessGeometry.toPlanarBoundaryAttachedRootedFacePeelCertificate

theorem counterPreviousBoundaryWitnessGeometry_hasAttachedRootedFacePeelCertificate :
    Nonempty
      (BoundaryRootedFacePeelCertificate counterEmbedding.faces.attach
        (ambientFaceBoundary (allFaces := counterEmbedding.faces)
          counterEmbedding.faceBoundary)) := by
  exact ⟨counterAttachedRootedFacePeelCertificate.certificate⟩

theorem counterGraph_admitsPlanarBoundaryAttachedRootedFacePeelCertificate :
    AdmitsPlanarBoundaryAttachedRootedFacePeelCertificate counterGraph := by
  exact ⟨counterAttachedRootedFacePeelCertificate⟩

/-- Same-embedding obstruction: even the repaired previous-boundary witness geometry does not
force the canonical annulus construction to satisfy the stricter construction-side parent-witness
orientation surface. The first collar face remains at distance `0`, so it can never own a strictly
earlier parent in the construction metric. -/
theorem previousBoundaryWitnessGeometry_does_not_imply_parentWitnessOrientation_counterexample :
    Nonempty (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry counterEmbedding) ∧
      ¬ counterConstruction.ParentWitnessOrientation := by
  exact ⟨⟨counterPreviousBoundaryWitnessGeometry⟩, not_counterConstructionParentWitnessOrientation⟩

/-- Current-boundary formulation of the same obstruction. The repaired witness-placement property
does hold on the explicit current outer frontier, but the canonical annulus construction still
fails parent-witness orientation on the same embedding. -/
theorem witnessOnCurrentBoundary_does_not_imply_parentWitnessOrientation_counterexample :
    Nonempty
        (PlanarBoundaryAnnulusCollarGeometry counterEmbedding) ∧
      counterCollarGeometry.WitnessOnCurrentBoundary ∧
      ¬ counterConstruction.ParentWitnessOrientation := by
  exact
    ⟨⟨counterCollarGeometry⟩,
      counterWitnessOnCurrentBoundary,
      not_counterConstructionParentWitnessOrientation⟩

theorem
    previousBoundaryWitnessGeometry_hasAttachedRootedFacePeelCertificate_without_parentWitnessOrientation :
    Nonempty (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry counterEmbedding) ∧
      Nonempty
        (BoundaryRootedFacePeelCertificate counterEmbedding.faces.attach
          (ambientFaceBoundary (allFaces := counterEmbedding.faces)
            counterEmbedding.faceBoundary)) ∧
      ¬ counterConstruction.ParentWitnessOrientation := by
  exact
    ⟨⟨counterPreviousBoundaryWitnessGeometry⟩,
      counterPreviousBoundaryWitnessGeometry_hasAttachedRootedFacePeelCertificate,
      not_counterConstructionParentWitnessOrientation⟩

theorem
    witnessOnCurrentBoundary_hasAttachedRootedFacePeelCertificate_without_parentWitnessOrientation :
    Nonempty
        (PlanarBoundaryAnnulusCollarGeometry counterEmbedding) ∧
      counterCollarGeometry.WitnessOnCurrentBoundary ∧
      Nonempty
        (BoundaryRootedFacePeelCertificate counterEmbedding.faces.attach
          (ambientFaceBoundary (allFaces := counterEmbedding.faces)
            counterEmbedding.faceBoundary)) ∧
      ¬ counterConstruction.ParentWitnessOrientation := by
  exact
    ⟨⟨counterCollarGeometry⟩,
      counterWitnessOnCurrentBoundary,
      counterPreviousBoundaryWitnessGeometry_hasAttachedRootedFacePeelCertificate,
      not_counterConstructionParentWitnessOrientation⟩

theorem
    exists_planarBoundaryAnnulusPreviousBoundaryWitnessGeometry_without_parentWitnessOrientation :
    ∃ emb : PlaneEmbeddingWithBoundary counterGraph,
      ∃ data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb,
        ¬ (planarBoundaryAnnulusConstruction_of_annulusCollarGeometry
              data.toPlanarBoundaryAnnulusCollarGeometry).ParentWitnessOrientation := by
  refine ⟨counterEmbedding, counterPreviousBoundaryWitnessGeometry, ?_⟩
  exact not_counterConstructionParentWitnessOrientation

theorem
    exists_planarBoundaryAnnulusCollarGeometry_and_witnessOnCurrentBoundary_without_parentWitnessOrientation :
    ∃ emb : PlaneEmbeddingWithBoundary counterGraph,
      ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
        data.WitnessOnCurrentBoundary ∧
          ¬ (planarBoundaryAnnulusConstruction_of_annulusCollarGeometry data).ParentWitnessOrientation := by
  refine
    ⟨counterEmbedding, counterCollarGeometry, counterWitnessOnCurrentBoundary, ?_⟩
  exact not_counterConstructionParentWitnessOrientation

theorem not_forall_planarBoundaryAnnulusPreviousBoundaryWitnessGeometry_implies_parentWitnessOrientation :
    ¬ (∀ {emb : PlaneEmbeddingWithBoundary counterGraph},
        (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) →
          (planarBoundaryAnnulusConstruction_of_annulusCollarGeometry
            data.toPlanarBoundaryAnnulusCollarGeometry).ParentWitnessOrientation) := by
  intro h
  exact
    not_counterConstructionParentWitnessOrientation
      (h counterPreviousBoundaryWitnessGeometry)

theorem not_forall_planarBoundaryAnnulusCollarGeometry_and_witnessOnCurrentBoundary_implies_parentWitnessOrientation :
    ¬ (∀ {emb : PlaneEmbeddingWithBoundary counterGraph}
        (data : PlanarBoundaryAnnulusCollarGeometry emb),
          data.WitnessOnCurrentBoundary →
            (planarBoundaryAnnulusConstruction_of_annulusCollarGeometry data).ParentWitnessOrientation) := by
  intro h
  exact
    not_counterConstructionParentWitnessOrientation
      (h counterCollarGeometry counterWitnessOnCurrentBoundary)

theorem
    exists_planarBoundaryAnnulusPreviousBoundaryWitnessGeometry_and_attachedRootedFacePeelCertificate_without_parentWitnessOrientation :
    ∃ emb : PlaneEmbeddingWithBoundary counterGraph,
      ∃ data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb,
        Nonempty
          (BoundaryRootedFacePeelCertificate emb.faces.attach
            (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) ∧
          ¬ (planarBoundaryAnnulusConstruction_of_annulusCollarGeometry
                data.toPlanarBoundaryAnnulusCollarGeometry).ParentWitnessOrientation := by
  refine
    ⟨counterEmbedding, counterPreviousBoundaryWitnessGeometry,
      counterPreviousBoundaryWitnessGeometry_hasAttachedRootedFacePeelCertificate, ?_⟩
  exact not_counterConstructionParentWitnessOrientation

theorem
    exists_planarBoundaryAnnulusCollarGeometry_and_witnessOnCurrentBoundary_and_attachedRootedFacePeelCertificate_without_parentWitnessOrientation :
    ∃ emb : PlaneEmbeddingWithBoundary counterGraph,
      ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
        data.WitnessOnCurrentBoundary ∧
          Nonempty
            (BoundaryRootedFacePeelCertificate emb.faces.attach
              (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) ∧
          ¬ (planarBoundaryAnnulusConstruction_of_annulusCollarGeometry data).ParentWitnessOrientation := by
  refine
    ⟨counterEmbedding, counterCollarGeometry,
      counterWitnessOnCurrentBoundary,
      counterPreviousBoundaryWitnessGeometry_hasAttachedRootedFacePeelCertificate, ?_⟩
  exact not_counterConstructionParentWitnessOrientation

end Theorem49PlanarBoundaryAnnulusGeometryRegression

end Mettapedia.GraphTheory.FourColor
