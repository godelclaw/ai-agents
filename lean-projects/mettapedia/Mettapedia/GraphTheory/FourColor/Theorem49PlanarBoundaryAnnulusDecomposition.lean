import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryAnnulusBoundary
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryCollarPeeling

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- Pure Step 2 annulus geometry over a boundary-aware plane embedding. This stores only the
outside-in collar decomposition itself: peeled collar face sets, deeper remainder face sets, and
the intermediate boundary cycles `Γ_t`, on top of a previously chosen outer/inner ambient
boundary split of the annulus. No witness-edge ownership or annihilator data is included here. -/
structure PlanarBoundaryAnnulusDecomposition {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) extends PlanarBoundaryAnnulusBoundaryData emb where
  numCollars : ℕ
  collarFaces : Fin numCollars → Finset (AmbientFace emb.faces)
  remainderFaces : Fin numCollars → Finset (AmbientFace emb.faces)
  boundaryCycle : Fin (numCollars + 1) → Finset G.edgeSet
  hfaceCover : emb.faces.attach ⊆ Finset.univ.biUnion collarFaces
  hdisjoint : ∀ {i j : Fin numCollars}, i ≠ j → Disjoint (collarFaces i) (collarFaces j)
  hremainder : ∀ i, remainderFaces i = laterLayerFaces collarFaces i
  houterBoundary : ∀ i : Fin numCollars,
    boundaryCycle (Fin.castSucc i) ⊆
      relativeBoundarySupport
        (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)
        (collarFaces i ∪ remainderFaces i)
  hinnerBoundary : ∀ i : Fin numCollars, i.1 + 1 < numCollars →
    boundaryCycle (Fin.succ i) ⊆
      relativeBoundarySupport
        (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)
        (remainderFaces i)
  hcurrentBoundaryCover : ∀ i : Fin numCollars,
    relativeBoundarySupport
        (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)
        (collarFaces i ∪ remainderFaces i) ⊆
      boundaryCycle (Fin.castSucc i) ∪
        boundaryCycle ⟨numCollars, Nat.lt_succ_self numCollars⟩
  hremainderBoundaryCover : ∀ i : Fin numCollars,
    relativeBoundarySupport
        (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)
        (remainderFaces i) ⊆
      boundaryCycle (Fin.succ i) ∪
        boundaryCycle ⟨numCollars, Nat.lt_succ_self numCollars⟩
  hcurrentInnerAmbientBoundary : ∀ i : Fin numCollars,
    innerAmbientBoundary ⊆
      relativeBoundarySupport
        (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)
        (collarFaces i ∪ remainderFaces i)
  hremainderInnerAmbientBoundary : ∀ i : Fin numCollars, i.1 + 1 < numCollars →
    innerAmbientBoundary ⊆
      relativeBoundarySupport
        (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)
        (remainderFaces i)
  hintermediateBoundaryInterior : ∀ i : Fin numCollars, i.1 + 1 < numCollars →
    boundaryCycle (Fin.succ i) ⊆ interiorEdgeSupport emb.faceBoundary emb.faces
  hintermediateBoundaryNonempty : ∀ i : Fin numCollars, i.1 + 1 < numCollars →
    (boundaryCycle (Fin.succ i)).Nonempty
  hboundaryCycleDisjoint : ∀ {i j : Fin (numCollars + 1)}, i ≠ j →
    Disjoint (boundaryCycle i) (boundaryCycle j)
  hambientOuterBoundary :
    boundaryCycle 0 = outerAmbientBoundary
  hambientInnerBoundary :
    boundaryCycle ⟨numCollars, Nat.lt_succ_self numCollars⟩ =
      innerAmbientBoundary

/-- The current annulus faces at stage `i`: the collar peeled at that stage together with the
deeper remainder that survives after removing it. -/
def PlanarBoundaryAnnulusDecomposition.currentFaces {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusDecomposition emb) (i : Fin data.numCollars) :
    Finset (AmbientFace emb.faces) :=
  data.collarFaces i ∪ data.remainderFaces i

theorem PlanarBoundaryAnnulusDecomposition.currentFaces_eq {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusDecomposition emb) (i : Fin data.numCollars) :
    data.currentFaces i = data.collarFaces i ∪ laterLayerFaces data.collarFaces i := by
  simp [PlanarBoundaryAnnulusDecomposition.currentFaces, data.hremainder i]

theorem PlanarBoundaryAnnulusDecomposition.collarFaces_disjoint_remainderFaces
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusDecomposition emb) (i : Fin data.numCollars) :
    Disjoint (data.collarFaces i) (data.remainderFaces i) := by
  rw [data.hremainder i, Finset.disjoint_left]
  intro f hfi hlater
  rcases (mem_laterLayerFaces_iff data.collarFaces i).1 hlater with ⟨j, hij, hfj⟩
  exact (Finset.disjoint_left.mp (data.hdisjoint (Fin.ne_of_lt hij))) hfi hfj

theorem PlanarBoundaryAnnulusDecomposition.remainderFaces_subset_currentFaces
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusDecomposition emb) (i : Fin data.numCollars) :
    data.remainderFaces i ⊆ data.currentFaces i := by
  intro f hf
  exact Finset.mem_union.2 <| Or.inr hf

theorem PlanarBoundaryAnnulusDecomposition.collarFaces_subset_remainderFaces_of_lt
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusDecomposition emb) {i j : Fin data.numCollars}
    (hij : i < j) :
    data.collarFaces j ⊆ data.remainderFaces i := by
  rw [data.hremainder i]
  exact layerFaces_subset_laterLayerFaces_of_lt data.collarFaces hij

/-- Every ambient face belongs to a unique collar layer of the annulus decomposition. -/
theorem PlanarBoundaryAnnulusDecomposition.exists_mem_collarFaces
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusDecomposition emb) (g : AmbientFace emb.faces) :
    ∃ j : Fin data.numCollars, g ∈ data.collarFaces j := by
  rcases Finset.mem_biUnion.1 (data.hfaceCover (by simp : g ∈ emb.faces.attach)) with
    ⟨j, -, hgj⟩
  exact ⟨j, hgj⟩

/-- Canonical collar index of an ambient face in the annulus decomposition. -/
noncomputable def PlanarBoundaryAnnulusDecomposition.layerOf
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusDecomposition emb) (g : AmbientFace emb.faces) :
    Fin data.numCollars :=
  Classical.choose (data.exists_mem_collarFaces g)

theorem PlanarBoundaryAnnulusDecomposition.mem_collarFaces_layerOf
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusDecomposition emb) (g : AmbientFace emb.faces) :
    g ∈ data.collarFaces (data.layerOf g) :=
  Classical.choose_spec (data.exists_mem_collarFaces g)

theorem PlanarBoundaryAnnulusDecomposition.layerOf_eq_of_mem
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusDecomposition emb)
    {g : AmbientFace emb.faces} {j : Fin data.numCollars}
    (hgj : g ∈ data.collarFaces j) :
    data.layerOf g = j := by
  by_cases hEq : data.layerOf g = j
  · exact hEq
  · exact False.elim ((Finset.disjoint_left.mp (data.hdisjoint hEq))
      (data.mem_collarFaces_layerOf g) hgj)

theorem PlanarBoundaryAnnulusDecomposition.remainderFaces_subset_remainderFaces_of_lt
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusDecomposition emb) {i j : Fin data.numCollars}
    (hij : i < j) :
    data.remainderFaces j ⊆ data.remainderFaces i := by
  rw [data.hremainder i, data.hremainder j]
  exact laterLayerFaces_subset_laterLayerFaces_of_lt data.collarFaces hij

theorem PlanarBoundaryAnnulusDecomposition.currentFaces_subset_remainderFaces_of_lt
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusDecomposition emb) {i j : Fin data.numCollars}
    (hij : i < j) :
    data.currentFaces j ⊆ data.remainderFaces i := by
  intro f hf
  rcases Finset.mem_union.1 (by simpa [PlanarBoundaryAnnulusDecomposition.currentFaces] using hf) with
    hfj | hfr
  · exact data.collarFaces_subset_remainderFaces_of_lt hij hfj
  · exact data.remainderFaces_subset_remainderFaces_of_lt hij hfr

theorem PlanarBoundaryAnnulusDecomposition.currentFaces_boundary_subset
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusDecomposition emb) (i : Fin data.numCollars) :
    relativeBoundarySupport
        (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)
        (data.currentFaces i) ⊆
      data.boundaryCycle (Fin.castSucc i) ∪
        data.boundaryCycle ⟨data.numCollars, Nat.lt_succ_self data.numCollars⟩ := by
  simpa [PlanarBoundaryAnnulusDecomposition.currentFaces] using data.hcurrentBoundaryCover i

theorem PlanarBoundaryAnnulusDecomposition.currentFaces_boundary_eq
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusDecomposition emb) (i : Fin data.numCollars) :
    relativeBoundarySupport
        (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)
        (data.currentFaces i) =
      data.boundaryCycle (Fin.castSucc i) ∪
        data.boundaryCycle ⟨data.numCollars, Nat.lt_succ_self data.numCollars⟩ := by
  apply Finset.Subset.antisymm
  · exact data.currentFaces_boundary_subset i
  · intro e he
    rcases Finset.mem_union.1 he with houter | hinner
    · exact data.houterBoundary i houter
    · rw [data.hambientInnerBoundary] at hinner
      simpa [PlanarBoundaryAnnulusDecomposition.currentFaces] using
        data.hcurrentInnerAmbientBoundary i hinner

theorem PlanarBoundaryAnnulusDecomposition.remainderFaces_boundary_subset
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusDecomposition emb) (i : Fin data.numCollars) :
    relativeBoundarySupport
        (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)
        (data.remainderFaces i) ⊆
      data.boundaryCycle (Fin.succ i) ∪
        data.boundaryCycle ⟨data.numCollars, Nat.lt_succ_self data.numCollars⟩ :=
  data.hremainderBoundaryCover i

theorem PlanarBoundaryAnnulusDecomposition.remainderFaces_boundary_eq
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusDecomposition emb) (i : Fin data.numCollars)
    (hi : i.1 + 1 < data.numCollars) :
    relativeBoundarySupport
        (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)
        (data.remainderFaces i) =
      data.boundaryCycle (Fin.succ i) ∪
        data.boundaryCycle ⟨data.numCollars, Nat.lt_succ_self data.numCollars⟩ := by
  apply Finset.Subset.antisymm
  · exact data.remainderFaces_boundary_subset i
  · intro e he
    rcases Finset.mem_union.1 he with hnext | hinner
    · exact data.hinnerBoundary i hi hnext
    · rw [data.hambientInnerBoundary] at hinner
      exact data.hremainderInnerAmbientBoundary i hi hinner

theorem PlanarBoundaryAnnulusDecomposition.boundaryCycle_zero_eq_outerAmbientBoundary
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusDecomposition emb) :
    data.boundaryCycle 0 = data.outerAmbientBoundary :=
  data.hambientOuterBoundary

theorem PlanarBoundaryAnnulusDecomposition.boundaryCycle_last_eq_innerAmbientBoundary
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusDecomposition emb) :
    data.boundaryCycle ⟨data.numCollars, Nat.lt_succ_self data.numCollars⟩ =
      data.innerAmbientBoundary :=
  data.hambientInnerBoundary

theorem PlanarBoundaryAnnulusDecomposition.boundaryCycle_disjoint_of_ne
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusDecomposition emb)
    {i j : Fin (data.numCollars + 1)} (hij : i ≠ j) :
    Disjoint (data.boundaryCycle i) (data.boundaryCycle j) :=
  data.hboundaryCycleDisjoint hij

theorem PlanarBoundaryAnnulusDecomposition.boundaryCycle_zero_nonempty
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusDecomposition emb) :
    (data.boundaryCycle 0).Nonempty := by
  simpa [data.boundaryCycle_zero_eq_outerAmbientBoundary] using
    data.houterAmbientBoundaryNonempty

theorem PlanarBoundaryAnnulusDecomposition.boundaryCycle_last_nonempty
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusDecomposition emb) :
    (data.boundaryCycle ⟨data.numCollars, Nat.lt_succ_self data.numCollars⟩).Nonempty := by
  simpa [data.boundaryCycle_last_eq_innerAmbientBoundary] using
    data.hinnerAmbientBoundaryNonempty

theorem PlanarBoundaryAnnulusDecomposition.totalIncidenceCount_eq_one_of_mem_boundaryCycle_zero
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusDecomposition emb) {e : G.edgeSet}
    (he : e ∈ data.boundaryCycle 0) :
    totalIncidenceCount emb.faceBoundary emb.faces e = 1 := by
  rw [data.boundaryCycle_zero_eq_outerAmbientBoundary] at he
  exact data.totalIncidenceCount_eq_one_of_mem_outerAmbientBoundary he

theorem PlanarBoundaryAnnulusDecomposition.totalIncidenceCount_eq_one_of_mem_boundaryCycle_last
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusDecomposition emb) {e : G.edgeSet}
    (he : e ∈ data.boundaryCycle ⟨data.numCollars, Nat.lt_succ_self data.numCollars⟩) :
    totalIncidenceCount emb.faceBoundary emb.faces e = 1 := by
  rw [data.boundaryCycle_last_eq_innerAmbientBoundary] at he
  exact data.totalIncidenceCount_eq_one_of_mem_innerAmbientBoundary he

theorem PlanarBoundaryAnnulusDecomposition.boundaryCycle_zero_disjoint_boundaryCycle_last
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusDecomposition emb) :
    Disjoint (data.boundaryCycle 0)
      (data.boundaryCycle ⟨data.numCollars, Nat.lt_succ_self data.numCollars⟩) := by
  simpa [data.boundaryCycle_zero_eq_outerAmbientBoundary,
    data.boundaryCycle_last_eq_innerAmbientBoundary] using data.hambientBoundaryDisjoint

theorem PlanarBoundaryAnnulusDecomposition.boundaryCycle_zero_ne_boundaryCycle_last
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusDecomposition emb) :
    data.boundaryCycle 0 ≠
      data.boundaryCycle ⟨data.numCollars, Nat.lt_succ_self data.numCollars⟩ := by
  intro hEq
  rcases data.boundaryCycle_zero_nonempty with ⟨e, he⟩
  have hlast : e ∈ data.boundaryCycle ⟨data.numCollars, Nat.lt_succ_self data.numCollars⟩ := by
    simpa [hEq] using he
  exact (Finset.disjoint_left.mp data.boundaryCycle_zero_disjoint_boundaryCycle_last) he hlast

theorem PlanarBoundaryAnnulusDecomposition.numCollars_pos
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusDecomposition emb) :
    0 < data.numCollars := by
  by_contra hpos
  have hzero : data.numCollars = 0 := Nat.eq_zero_of_not_pos hpos
  have hEq :
      data.boundaryCycle 0 =
        data.boundaryCycle ⟨data.numCollars, Nat.lt_succ_self data.numCollars⟩ := by
    simp [hzero]
  exact data.boundaryCycle_zero_ne_boundaryCycle_last hEq

theorem PlanarBoundaryAnnulusDecomposition.boundaryCycle_zero_disjoint_interiorEdgeSupport
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusDecomposition emb) :
    Disjoint (data.boundaryCycle 0)
      (interiorEdgeSupport emb.faceBoundary emb.faces) := by
  simpa [data.boundaryCycle_zero_eq_outerAmbientBoundary] using
    data.outerAmbientBoundary_disjoint_interiorEdgeSupport

theorem PlanarBoundaryAnnulusDecomposition.boundaryCycle_last_disjoint_interiorEdgeSupport
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusDecomposition emb) :
    Disjoint (data.boundaryCycle ⟨data.numCollars, Nat.lt_succ_self data.numCollars⟩)
      (interiorEdgeSupport emb.faceBoundary emb.faces) := by
  simpa [data.boundaryCycle_last_eq_innerAmbientBoundary] using
    data.innerAmbientBoundary_disjoint_interiorEdgeSupport

theorem PlanarBoundaryAnnulusDecomposition.boundaryCycle_intermediate_subset_interiorEdgeSupport
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusDecomposition emb) (i : Fin data.numCollars)
    (hi : i.1 + 1 < data.numCollars) :
    data.boundaryCycle (Fin.succ i) ⊆ interiorEdgeSupport emb.faceBoundary emb.faces :=
  data.hintermediateBoundaryInterior i hi

theorem PlanarBoundaryAnnulusDecomposition.boundaryCycle_intermediate_nonempty
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusDecomposition emb) (i : Fin data.numCollars)
    (hi : i.1 + 1 < data.numCollars) :
    (data.boundaryCycle (Fin.succ i)).Nonempty :=
  data.hintermediateBoundaryNonempty i hi

theorem PlanarBoundaryAnnulusDecomposition.boundaryCycle_intermediate_disjoint_selectedBoundarySupport
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusDecomposition emb) (i : Fin data.numCollars)
    (hi : i.1 + 1 < data.numCollars) :
    Disjoint (data.boundaryCycle (Fin.succ i))
      (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) := by
  rw [Finset.disjoint_left]
  intro e he hboundary
  have hinterior : e ∈ interiorEdgeSupport emb.faceBoundary emb.faces :=
    data.hintermediateBoundaryInterior i hi he
  exact (Finset.disjoint_left.mp
    (selectedBoundarySupport_disjoint_interiorEdgeSupport emb.faceBoundary emb.faces))
      hboundary hinterior

theorem PlanarBoundaryAnnulusDecomposition.totalIncidenceCount_eq_two_of_mem_boundaryCycle_intermediate
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusDecomposition emb) (i : Fin data.numCollars)
    (hi : i.1 + 1 < data.numCollars) {e : G.edgeSet}
    (he : e ∈ data.boundaryCycle (Fin.succ i)) :
    totalIncidenceCount emb.faceBoundary emb.faces e = 2 := by
  exact (mem_interiorEdgeSupport_iff emb.faceBoundary emb.faces).1
    (data.hintermediateBoundaryInterior i hi he) |>.2

theorem PlanarBoundaryAnnulusDecomposition.boundaryCycle_intermediate_disjoint_boundaryCycle_zero
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusDecomposition emb) (i : Fin data.numCollars)
    (hi : i.1 + 1 < data.numCollars) :
    Disjoint (data.boundaryCycle (Fin.succ i)) (data.boundaryCycle 0) := by
  rw [Finset.disjoint_left]
  intro e hintermediate hzero
  have hinterior : e ∈ interiorEdgeSupport emb.faceBoundary emb.faces :=
    data.hintermediateBoundaryInterior i hi hintermediate
  exact (Finset.disjoint_left.mp data.boundaryCycle_zero_disjoint_interiorEdgeSupport)
    hzero hinterior

theorem PlanarBoundaryAnnulusDecomposition.boundaryCycle_intermediate_disjoint_boundaryCycle_last
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusDecomposition emb) (i : Fin data.numCollars)
    (hi : i.1 + 1 < data.numCollars) :
    Disjoint (data.boundaryCycle (Fin.succ i))
      (data.boundaryCycle ⟨data.numCollars, Nat.lt_succ_self data.numCollars⟩) := by
  rw [Finset.disjoint_left]
  intro e hintermediate hlast
  have hinterior : e ∈ interiorEdgeSupport emb.faceBoundary emb.faces :=
    data.hintermediateBoundaryInterior i hi hintermediate
  exact (Finset.disjoint_left.mp data.boundaryCycle_last_disjoint_interiorEdgeSupport)
    hlast hinterior

theorem PlanarBoundaryAnnulusDecomposition.boundaryCycle_intermediate_ne_boundaryCycle_zero
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusDecomposition emb) (i : Fin data.numCollars)
    (hi : i.1 + 1 < data.numCollars) :
    data.boundaryCycle (Fin.succ i) ≠ data.boundaryCycle 0 := by
  intro hEq
  rcases data.boundaryCycle_zero_nonempty with ⟨e, he⟩
  have hintermediate : e ∈ data.boundaryCycle (Fin.succ i) := by
    simpa [hEq] using he
  exact (Finset.disjoint_left.mp
    (data.boundaryCycle_intermediate_disjoint_boundaryCycle_zero i hi))
      hintermediate he

theorem PlanarBoundaryAnnulusDecomposition.boundaryCycle_intermediate_ne_boundaryCycle_last
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusDecomposition emb) (i : Fin data.numCollars)
    (hi : i.1 + 1 < data.numCollars) :
    data.boundaryCycle (Fin.succ i) ≠
      data.boundaryCycle ⟨data.numCollars, Nat.lt_succ_self data.numCollars⟩ := by
  intro hEq
  rcases data.boundaryCycle_last_nonempty with ⟨e, he⟩
  have hintermediate : e ∈ data.boundaryCycle (Fin.succ i) := by
    simpa [hEq] using he
  exact (Finset.disjoint_left.mp
    (data.boundaryCycle_intermediate_disjoint_boundaryCycle_last i hi))
      hintermediate he

theorem PlanarBoundaryAnnulusDecomposition.boundaryCycle_intermediate_disjoint_boundaryCycle_intermediate
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusDecomposition emb)
    (i j : Fin data.numCollars)
    (_hi : i.1 + 1 < data.numCollars) (_hj : j.1 + 1 < data.numCollars)
    (hij : i ≠ j) :
    Disjoint (data.boundaryCycle (Fin.succ i)) (data.boundaryCycle (Fin.succ j)) := by
  apply data.boundaryCycle_disjoint_of_ne
  intro hEq
  apply hij
  apply Fin.ext
  exact Nat.succ.inj (congrArg Fin.val hEq)

theorem PlanarBoundaryAnnulusDecomposition.boundaryCycle_intermediate_ne_boundaryCycle_intermediate
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusDecomposition emb)
    (i j : Fin data.numCollars)
    (hi : i.1 + 1 < data.numCollars) (hj : j.1 + 1 < data.numCollars)
    (hij : i ≠ j) :
    data.boundaryCycle (Fin.succ i) ≠ data.boundaryCycle (Fin.succ j) := by
  intro hEq
  rcases data.boundaryCycle_intermediate_nonempty i hi with ⟨e, he⟩
  have hej : e ∈ data.boundaryCycle (Fin.succ j) := by
    simpa [hEq] using he
  exact (Finset.disjoint_left.mp
    (data.boundaryCycle_intermediate_disjoint_boundaryCycle_intermediate i j hi hj hij))
      he hej

theorem PlanarBoundaryAnnulusDecomposition.boundaryCycle_zero_subset_selectedBoundarySupport
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusDecomposition emb) :
    data.boundaryCycle 0 ⊆ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces :=
  by simpa [data.boundaryCycle_zero_eq_outerAmbientBoundary] using data.houterAmbientBoundarySubset

theorem PlanarBoundaryAnnulusDecomposition.boundaryCycle_last_subset_selectedBoundarySupport
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusDecomposition emb) :
    data.boundaryCycle ⟨data.numCollars, Nat.lt_succ_self data.numCollars⟩ ⊆
      selectedBoundarySupport emb.faceBoundary emb.faces emb.faces :=
  by
    simpa [data.boundaryCycle_last_eq_innerAmbientBoundary] using
      data.hinnerAmbientBoundarySubset

theorem PlanarBoundaryAnnulusDecomposition.boundaryCycle_nonempty
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusDecomposition emb)
    (k : Fin (data.numCollars + 1)) :
    (data.boundaryCycle k).Nonempty := by
  rcases Fin.eq_castSucc_or_eq_last k with ⟨i, rfl⟩ | ⟨rfl⟩
  · by_cases hi0 : i.1 = 0
    · have hcast0 : Fin.castSucc i = 0 := by
        apply Fin.ext
        simp [hi0]
      simpa [hcast0] using data.boundaryCycle_zero_nonempty
    · have hpos : 0 < i.1 := Nat.pos_of_ne_zero hi0
      let j : Fin data.numCollars := ⟨i.1 - 1, by
        have hiLt := i.isLt
        omega⟩
      have hj : j.1 + 1 < data.numCollars := by
        dsimp [j]
        omega
      have hcast : Fin.castSucc i = Fin.succ j := by
        apply Fin.ext
        dsimp [j]
        omega
      simpa [hcast] using data.boundaryCycle_intermediate_nonempty j hj
  · exact data.boundaryCycle_last_nonempty

theorem laterLayerFaces_eq_collarFaces_union_laterLayerFaces_next {F : Type*} [DecidableEq F]
    {n : ℕ} (layerFaces : Fin n → Finset F) (i : Fin n) (hi : i.1 + 1 < n) :
    laterLayerFaces layerFaces i =
      layerFaces ⟨i.1 + 1, hi⟩ ∪ laterLayerFaces layerFaces ⟨i.1 + 1, hi⟩ := by
  ext f
  constructor
  · intro hf
    rcases (mem_laterLayerFaces_iff layerFaces i).1 hf with ⟨j, hij, hfj⟩
    have hle : i.1 + 1 ≤ j.1 := Nat.succ_le_of_lt hij
    rcases eq_or_lt_of_le hle with hEq | hLt
    · have hj :
          j = ⟨i.1 + 1, hi⟩ := by
        apply Fin.ext
        exact hEq.symm
      subst hj
      exact Finset.mem_union.2 <| Or.inl hfj
    · exact Finset.mem_union.2 <| Or.inr <|
        (mem_laterLayerFaces_iff layerFaces ⟨i.1 + 1, hi⟩).2
          ⟨j, by simpa using hLt, hfj⟩
  · intro hf
    rcases Finset.mem_union.1 hf with hnext | hlater
    · exact (mem_laterLayerFaces_iff layerFaces i).2
        ⟨⟨i.1 + 1, hi⟩, by
          change i.1 < i.1 + 1
          omega, hnext⟩
    · rcases (mem_laterLayerFaces_iff layerFaces ⟨i.1 + 1, hi⟩).1 hlater with
        ⟨j, hj, hfj⟩
      exact (mem_laterLayerFaces_iff layerFaces i).2
        ⟨j, lt_trans (by
            change i.1 < i.1 + 1
            omega) hj, hfj⟩

/-- The current surviving face set at stage `i` for an outside-in collar layering: the collar
peeled at stage `i` together with all strictly later collars. -/
def annulusCurrentFaces {F : Type*} [DecidableEq F] {n : ℕ}
    (layerFaces : Fin n → Finset F) (i : Fin n) : Finset F :=
  layerFaces i ∪ laterLayerFaces layerFaces i

/-- Face-layer geometry for the annulus shell, stated directly in terms of the actual collar
partition of the embedding. The outer frontier at each stage is not stored separately: it is the
relative boundary of the current surviving faces after removing the distinguished inner ambient
boundary. This is a more concrete geometric target than `PlanarBoundaryAnnulusCurrentBoundaryData`
because it treats the frontiers as derived data. -/
structure PlanarBoundaryAnnulusFaceLayerData {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) extends PlanarBoundaryAnnulusBoundaryData emb where
  numCollars : ℕ
  hnumCollars_pos : 0 < numCollars
  collarFaces : Fin numCollars → Finset (AmbientFace emb.faces)
  hfaceCover : emb.faces.attach ⊆ Finset.univ.biUnion collarFaces
  hdisjoint : ∀ {i j : Fin numCollars}, i ≠ j → Disjoint (collarFaces i) (collarFaces j)
  hcurrentInnerAmbientBoundary :
    ∀ i : Fin numCollars,
      innerAmbientBoundary ⊆
        relativeBoundarySupport
          (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)
          (annulusCurrentFaces collarFaces i)
  hcurrentBoundaryZero :
    relativeBoundarySupport
        (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)
        (annulusCurrentFaces collarFaces ⟨0, hnumCollars_pos⟩) =
      outerAmbientBoundary ∪ innerAmbientBoundary
  hcurrentBoundaryInterior :
    ∀ i : Fin numCollars, 0 < i.1 →
      relativeBoundarySupport
          (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)
          (annulusCurrentFaces collarFaces i) ⊆
        interiorEdgeSupport emb.faceBoundary emb.faces ∪ innerAmbientBoundary
  hcurrentOuterBoundaryNonempty :
    ∀ i : Fin numCollars,
      (relativeBoundarySupport
          (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)
          (annulusCurrentFaces collarFaces i) \ innerAmbientBoundary).Nonempty
  hcurrentOuterBoundaryDisjoint :
    ∀ {i j : Fin numCollars}, i ≠ j →
      Disjoint
        (relativeBoundarySupport
            (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)
            (annulusCurrentFaces collarFaces i) \ innerAmbientBoundary)
        (relativeBoundarySupport
            (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)
            (annulusCurrentFaces collarFaces j) \ innerAmbientBoundary)

def PlanarBoundaryAnnulusFaceLayerData.currentFaces {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusFaceLayerData emb) (i : Fin data.numCollars) :
    Finset (AmbientFace emb.faces) :=
  annulusCurrentFaces data.collarFaces i

def PlanarBoundaryAnnulusFaceLayerData.currentOuterBoundary {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusFaceLayerData emb) (i : Fin data.numCollars) :
    Finset G.edgeSet :=
  relativeBoundarySupport
      (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)
      (data.currentFaces i) \ data.innerAmbientBoundary

theorem PlanarBoundaryAnnulusFaceLayerData.currentBoundary_eq_currentOuterBoundary_union_inner
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusFaceLayerData emb) (i : Fin data.numCollars) :
    data.currentOuterBoundary i ∪ data.innerAmbientBoundary =
      relativeBoundarySupport
          (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)
          (data.currentFaces i) := by
  unfold PlanarBoundaryAnnulusFaceLayerData.currentOuterBoundary
  unfold PlanarBoundaryAnnulusFaceLayerData.currentFaces
  simpa [annulusCurrentFaces] using
    (Finset.sdiff_union_of_subset (data.hcurrentInnerAmbientBoundary i))

theorem PlanarBoundaryAnnulusFaceLayerData.currentOuterBoundary_zero_eq_outerAmbientBoundary
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusFaceLayerData emb) :
    data.currentOuterBoundary ⟨0, data.hnumCollars_pos⟩ = data.outerAmbientBoundary := by
  ext e
  constructor
  · intro he
    have hmem :
        e ∈ data.outerAmbientBoundary ∪ data.innerAmbientBoundary := by
      have : e ∈
          relativeBoundarySupport
            (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)
            (annulusCurrentFaces data.collarFaces ⟨0, data.hnumCollars_pos⟩) := by
        exact (Finset.mem_sdiff.1 he).1
      simpa [PlanarBoundaryAnnulusFaceLayerData.currentOuterBoundary, data.hcurrentBoundaryZero] using this
    rcases Finset.mem_union.1 hmem with houter | hinner
    · exact houter
    · exact False.elim ((Finset.mem_sdiff.1 he).2 hinner)
  · intro he
    refine Finset.mem_sdiff.2 ?_
    constructor
    · rw [PlanarBoundaryAnnulusFaceLayerData.currentFaces, data.hcurrentBoundaryZero]
      exact Finset.mem_union.2 <| Or.inl he
    · intro hinner
      exact (Finset.disjoint_left.mp data.hambientBoundaryDisjoint) he hinner

/-- Concrete collar geometry over a boundary-aware plane embedding, stated using the actual face
layers and the outer frontier of each current stage instead of primitive boundary cycles `Γ_t`.
This is a closer geometric starting point for constructing Step 2 than the fully packaged annulus
decomposition: the current-stage outer boundaries are part of the data, while the full cycle list
is recovered canonically. -/
structure PlanarBoundaryAnnulusCurrentBoundaryData {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) extends PlanarBoundaryAnnulusBoundaryData emb where
  numCollars : ℕ
  hnumCollars_pos : 0 < numCollars
  collarFaces : Fin numCollars → Finset (AmbientFace emb.faces)
  currentBoundary : Fin numCollars → Finset G.edgeSet
  hfaceCover : emb.faces.attach ⊆ Finset.univ.biUnion collarFaces
  hdisjoint : ∀ {i j : Fin numCollars}, i ≠ j → Disjoint (collarFaces i) (collarFaces j)
  hcurrentBoundary :
    ∀ i : Fin numCollars,
      relativeBoundarySupport
          (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)
          (collarFaces i ∪ laterLayerFaces collarFaces i) =
        currentBoundary i ∪ innerAmbientBoundary
  hcurrentBoundaryZero :
    currentBoundary ⟨0, hnumCollars_pos⟩ = outerAmbientBoundary
  hcurrentBoundaryInterior :
    ∀ i : Fin numCollars, 0 < i.1 →
      currentBoundary i ⊆ interiorEdgeSupport emb.faceBoundary emb.faces
  hcurrentBoundaryNonempty : ∀ i : Fin numCollars, (currentBoundary i).Nonempty
  hcurrentBoundaryDisjoint :
    ∀ {i j : Fin numCollars}, i ≠ j →
      Disjoint (currentBoundary i) (currentBoundary j)
  hcurrentBoundaryDisjointInner :
    ∀ i : Fin numCollars, Disjoint (currentBoundary i) innerAmbientBoundary

def PlanarBoundaryAnnulusFaceLayerData.toPlanarBoundaryAnnulusCurrentBoundaryData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusFaceLayerData emb) :
    PlanarBoundaryAnnulusCurrentBoundaryData emb := by
  refine
    { toPlanarBoundaryAnnulusBoundaryData := data.toPlanarBoundaryAnnulusBoundaryData
      numCollars := data.numCollars
      hnumCollars_pos := data.hnumCollars_pos
      collarFaces := data.collarFaces
      currentBoundary := data.currentOuterBoundary
      hfaceCover := data.hfaceCover
      hdisjoint := data.hdisjoint
      hcurrentBoundary := ?_
      hcurrentBoundaryZero := ?_
      hcurrentBoundaryInterior := ?_
      hcurrentBoundaryNonempty := data.hcurrentOuterBoundaryNonempty
      hcurrentBoundaryDisjoint := data.hcurrentOuterBoundaryDisjoint
      hcurrentBoundaryDisjointInner := ?_ }
  · intro i
    exact (data.currentBoundary_eq_currentOuterBoundary_union_inner i).symm
  · simpa using data.currentOuterBoundary_zero_eq_outerAmbientBoundary
  · intro i hi e he
    have hmem :
        e ∈ relativeBoundarySupport
            (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)
            (data.currentFaces i) := by
      exact (Finset.mem_sdiff.1 he).1
    rcases Finset.mem_union.1 (data.hcurrentBoundaryInterior i hi hmem) with hinterior | hinner
    · exact hinterior
    · exact False.elim ((Finset.mem_sdiff.1 he).2 hinner)
  · intro i
    rw [Finset.disjoint_left]
    intro e he hinner
    exact (Finset.mem_sdiff.1 he).2 hinner

/-- Recover the paper-facing annulus decomposition from concrete face layers plus the outer
boundary of each current stage. The intermediate cycles `Γ_t` are reconstructed canonically from
the current-stage boundaries, with the final cycle fixed to the distinguished inner ambient
boundary. -/
def PlanarBoundaryAnnulusCurrentBoundaryData.toPlanarBoundaryAnnulusDecomposition
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCurrentBoundaryData emb) :
    PlanarBoundaryAnnulusDecomposition emb := by
  let boundaryCycle : Fin (data.numCollars + 1) → Finset G.edgeSet := fun k =>
    if hk : k.1 < data.numCollars then
      data.currentBoundary ⟨k.1, hk⟩
    else
      data.innerAmbientBoundary
  refine
    { toPlanarBoundaryAnnulusBoundaryData := data.toPlanarBoundaryAnnulusBoundaryData
      numCollars := data.numCollars
      collarFaces := data.collarFaces
      remainderFaces := laterLayerFaces data.collarFaces
      boundaryCycle := boundaryCycle
      hfaceCover := data.hfaceCover
      hdisjoint := data.hdisjoint
      hremainder := ?_
      houterBoundary := ?_
      hinnerBoundary := ?_
      hcurrentBoundaryCover := ?_
      hremainderBoundaryCover := ?_
      hcurrentInnerAmbientBoundary := ?_
      hremainderInnerAmbientBoundary := ?_
      hintermediateBoundaryInterior := ?_
      hintermediateBoundaryNonempty := ?_
      hboundaryCycleDisjoint := ?_
      hambientOuterBoundary := ?_
      hambientInnerBoundary := ?_ }
  · intro i
    rfl
  · intro i e he
    have hEq : boundaryCycle (Fin.castSucc i) = data.currentBoundary i := by
      simp [boundaryCycle, i.isLt]
    rw [hEq] at he
    rw [data.hcurrentBoundary i]
    exact Finset.mem_union.2 <| Or.inl he
  · intro i hi e he
    let j : Fin data.numCollars := ⟨i.1 + 1, hi⟩
    have hEqCycle : boundaryCycle (Fin.succ i) = data.currentBoundary j := by
      simp [boundaryCycle, hi, j]
    rw [hEqCycle] at he
    rw [laterLayerFaces_eq_collarFaces_union_laterLayerFaces_next data.collarFaces i hi,
      data.hcurrentBoundary j]
    exact Finset.mem_union.2 <| Or.inl he
  · intro i e he
    rw [data.hcurrentBoundary i] at he
    have hEqCurrent : boundaryCycle (Fin.castSucc i) = data.currentBoundary i := by
      simp [boundaryCycle, i.isLt]
    have hEqLast :
        boundaryCycle ⟨data.numCollars, Nat.lt_succ_self data.numCollars⟩ =
          data.innerAmbientBoundary := by
      simp [boundaryCycle]
    rw [hEqCurrent, hEqLast]
    exact he
  · intro i e he
    by_cases hi : i.1 + 1 < data.numCollars
    · let j : Fin data.numCollars := ⟨i.1 + 1, hi⟩
      rw [laterLayerFaces_eq_collarFaces_union_laterLayerFaces_next data.collarFaces i hi,
        data.hcurrentBoundary j] at he
      have hEqCurrent : boundaryCycle (Fin.succ i) = data.currentBoundary j := by
        simp [boundaryCycle, hi, j]
      have hEqLast :
          boundaryCycle ⟨data.numCollars, Nat.lt_succ_self data.numCollars⟩ =
            data.innerAmbientBoundary := by
        simp [boundaryCycle]
      rw [hEqCurrent, hEqLast]
      exact he
    · have hnoLater : ∀ j : Fin data.numCollars, ¬ i < j := by
        intro j hij
        omega
      have hremEmpty :
          laterLayerFaces data.collarFaces i = ∅ :=
        laterLayerFaces_eq_empty_of_forall_not_lt data.collarFaces i hnoLater
      have : False := by
        simp [hremEmpty, relativeBoundarySupport] at he
      exact False.elim this
  · intro i e he
    rw [data.hcurrentBoundary i]
    exact Finset.mem_union.2 <| Or.inr he
  · intro i hi e he
    let j : Fin data.numCollars := ⟨i.1 + 1, hi⟩
    rw [laterLayerFaces_eq_collarFaces_union_laterLayerFaces_next data.collarFaces i hi,
      data.hcurrentBoundary j]
    exact Finset.mem_union.2 <| Or.inr he
  · intro i hi e he
    let j : Fin data.numCollars := ⟨i.1 + 1, hi⟩
    have hEq : boundaryCycle (Fin.succ i) = data.currentBoundary j := by
      simp [boundaryCycle, hi, j]
    rw [hEq] at he
    have hjpos : 0 < j.1 := by
      dsimp [j]
      omega
    exact data.hcurrentBoundaryInterior j hjpos he
  · intro i hi
    let j : Fin data.numCollars := ⟨i.1 + 1, hi⟩
    have hEq : boundaryCycle (Fin.succ i) = data.currentBoundary j := by
      simp [boundaryCycle, hi, j]
    rw [hEq]
    exact data.hcurrentBoundaryNonempty j
  · intro i j hij
    by_cases hi : i.1 < data.numCollars
    · by_cases hj : j.1 < data.numCollars
      · have hEqI : boundaryCycle i = data.currentBoundary ⟨i.1, hi⟩ := by
          simp [boundaryCycle, hi]
        have hEqJ : boundaryCycle j = data.currentBoundary ⟨j.1, hj⟩ := by
          simp [boundaryCycle, hj]
        have hne :
            (⟨i.1, hi⟩ : Fin data.numCollars) ≠ ⟨j.1, hj⟩ := by
          intro hEq
          apply hij
          apply Fin.ext
          simpa using congrArg (fun x : Fin data.numCollars => x.1) hEq
        rw [hEqI, hEqJ]
        exact data.hcurrentBoundaryDisjoint hne
      · have hEqI : boundaryCycle i = data.currentBoundary ⟨i.1, hi⟩ := by
          simp [boundaryCycle, hi]
        have hEqJ : boundaryCycle j = data.innerAmbientBoundary := by
          simp [boundaryCycle, hj]
        rw [hEqI, hEqJ]
        exact data.hcurrentBoundaryDisjointInner ⟨i.1, hi⟩
    · by_cases hj : j.1 < data.numCollars
      · have hEqI : boundaryCycle i = data.innerAmbientBoundary := by
          simp [boundaryCycle, hi]
        have hEqJ : boundaryCycle j = data.currentBoundary ⟨j.1, hj⟩ := by
          simp [boundaryCycle, hj]
        rw [hEqI, hEqJ]
        exact (data.hcurrentBoundaryDisjointInner ⟨j.1, hj⟩).symm
      · exfalso
        apply hij
        apply Fin.ext
        omega
  · have hzero :
        boundaryCycle 0 =
          data.currentBoundary ⟨0, data.hnumCollars_pos⟩ := by
      simp [boundaryCycle, data.hnumCollars_pos]
    rw [hzero, data.hcurrentBoundaryZero]
  · simp [boundaryCycle]

def PlanarBoundaryAnnulusFaceLayerData.toPlanarBoundaryAnnulusDecomposition
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusFaceLayerData emb) :
    PlanarBoundaryAnnulusDecomposition emb :=
  data.toPlanarBoundaryAnnulusCurrentBoundaryData.toPlanarBoundaryAnnulusDecomposition

/-- A pure annulus decomposition already determines the concrete current-boundary shell: the
current outer frontier at stage `i` is exactly `Γ_i`, with the distinguished inner ambient
boundary kept separate as the final cycle `Γ_n`. This inverse lowering shows that once genuine
annulus geometry is available, no extra current-boundary hypotheses are needed. -/
def PlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusCurrentBoundaryData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusDecomposition emb) :
    PlanarBoundaryAnnulusCurrentBoundaryData emb := by
  refine
    { toPlanarBoundaryAnnulusBoundaryData := data.toPlanarBoundaryAnnulusBoundaryData
      numCollars := data.numCollars
      hnumCollars_pos := data.numCollars_pos
      collarFaces := data.collarFaces
      currentBoundary := fun i => data.boundaryCycle (Fin.castSucc i)
      hfaceCover := data.hfaceCover
      hdisjoint := data.hdisjoint
      hcurrentBoundary := ?_
      hcurrentBoundaryZero := ?_
      hcurrentBoundaryInterior := ?_
      hcurrentBoundaryNonempty := ?_
      hcurrentBoundaryDisjoint := ?_
      hcurrentBoundaryDisjointInner := ?_ }
  · intro i
    calc
      relativeBoundarySupport
          (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)
          (data.collarFaces i ∪ laterLayerFaces data.collarFaces i) =
        relativeBoundarySupport
            (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)
            (data.currentFaces i) := by
              simp [PlanarBoundaryAnnulusDecomposition.currentFaces, data.hremainder i]
      _ =
        data.boundaryCycle (Fin.castSucc i) ∪
          data.boundaryCycle ⟨data.numCollars, Nat.lt_succ_self data.numCollars⟩ := by
            exact data.currentFaces_boundary_eq i
      _ = data.boundaryCycle (Fin.castSucc i) ∪ data.innerAmbientBoundary := by
            rw [data.boundaryCycle_last_eq_innerAmbientBoundary]
  · simpa using data.boundaryCycle_zero_eq_outerAmbientBoundary
  · intro i hi
    let j : Fin data.numCollars := ⟨i.1 - 1, by
      have hiLt := i.isLt
      omega⟩
    have hj : j.1 + 1 < data.numCollars := by
      dsimp [j]
      omega
    have hcast : Fin.castSucc i = Fin.succ j := by
      apply Fin.ext
      dsimp [j]
      omega
    simpa [hcast] using data.boundaryCycle_intermediate_subset_interiorEdgeSupport j hj
  · intro i
    by_cases hi0 : i.1 = 0
    · have hzero : i = ⟨0, data.numCollars_pos⟩ := by
        apply Fin.ext
        simpa using hi0
      subst hzero
      simpa using data.boundaryCycle_zero_nonempty
    · let j : Fin data.numCollars := ⟨i.1 - 1, by
        have hiLt := i.isLt
        omega⟩
      have hj : j.1 + 1 < data.numCollars := by
        dsimp [j]
        omega
      have hcast : Fin.castSucc i = Fin.succ j := by
        apply Fin.ext
        dsimp [j]
        omega
      simpa [hcast] using data.boundaryCycle_intermediate_nonempty j hj
  · intro i j hij
    apply data.boundaryCycle_disjoint_of_ne
    intro hEq
    apply hij
    apply Fin.ext
    simpa using congrArg Fin.val hEq
  · intro i
    simpa [data.boundaryCycle_last_eq_innerAmbientBoundary] using
      data.boundaryCycle_disjoint_of_ne (i := Fin.castSucc i)
        (j := ⟨data.numCollars, Nat.lt_succ_self data.numCollars⟩)
        (by
          intro hEq
          have hVal : i.1 = data.numCollars := by
            simpa using congrArg Fin.val hEq
          exact Nat.ne_of_lt i.isLt hVal)

/-- Graph-level existence form of the pure annulus decomposition target. -/
def AdmitsPlanarBoundaryAnnulusDecomposition (G : SimpleGraph V) : Prop :=
  ∃ emb : PlaneEmbeddingWithBoundary G,
    Nonempty (PlanarBoundaryAnnulusDecomposition emb)

/-- Under the current weak boundary API, an annulus boundary split already yields a degenerate
one-collar annulus decomposition: every ambient face lies in the unique collar, the remainder is
empty, and the only boundary cycles are the given outer and inner ambient boundaries. This shows
that pure annulus decomposition itself carries no extra burden beyond the ambient boundary split.
-/
def planarBoundaryAnnulusDecomposition_of_boundaryData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryData emb) :
    PlanarBoundaryAnnulusDecomposition emb := by
  let collarFaces : Fin 1 → Finset (AmbientFace emb.faces) := fun _ => emb.faces.attach
  let remainderFaces : Fin 1 → Finset (AmbientFace emb.faces) := fun _ => ∅
  let boundaryCycle : Fin 2 → Finset G.edgeSet :=
    fun
      | ⟨0, _⟩ => data.outerAmbientBoundary
      | ⟨1, _⟩ => data.innerAmbientBoundary
  refine
    { toPlanarBoundaryAnnulusBoundaryData := data
      numCollars := 1
      collarFaces := collarFaces
      remainderFaces := remainderFaces
      boundaryCycle := boundaryCycle
      hfaceCover := ?_
      hdisjoint := ?_
      hremainder := ?_
      houterBoundary := ?_
      hinnerBoundary := ?_
      hcurrentBoundaryCover := ?_
      hremainderBoundaryCover := ?_
      hcurrentInnerAmbientBoundary := ?_
      hremainderInnerAmbientBoundary := ?_
      hintermediateBoundaryInterior := ?_
      hintermediateBoundaryNonempty := ?_
      hboundaryCycleDisjoint := ?_
      hambientOuterBoundary := ?_
      hambientInnerBoundary := ?_ }
  · intro f hf
    exact Finset.mem_biUnion.2 ⟨⟨0, by decide⟩, Finset.mem_univ _, by simp [collarFaces, hf]⟩
  · intro i j hij
    have hi0 : i.1 = 0 := Nat.lt_one_iff.mp i.isLt
    have hj0 : j.1 = 0 := Nat.lt_one_iff.mp j.isLt
    exact False.elim (hij (Fin.ext (hi0.trans hj0.symm)))
  · intro i
    symm
    apply laterLayerFaces_eq_empty_of_forall_not_lt
    intro j hij
    have hi0 : i.1 = 0 := Nat.lt_one_iff.mp i.isLt
    have hj0 : j.1 = 0 := Nat.lt_one_iff.mp j.isLt
    have : i.1 < j.1 := by
      exact hij
    rw [hi0, hj0] at this
    exact Nat.lt_irrefl 0 this
  · intro i e he
    have hi : i = ⟨0, by decide⟩ := Fin.ext (Nat.lt_one_iff.mp i.isLt)
    subst hi
    have heOuter : e ∈ data.outerAmbientBoundary := by
      simpa [boundaryCycle] using he
    have heSelected : e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces :=
      data.houterAmbientBoundarySubset heOuter
    simpa [collarFaces, remainderFaces, relativeBoundarySupport_eq_selectedBoundarySupport,
      selectedBoundarySupport_ambientFaceBoundary_eq (faceBoundary := emb.faceBoundary)
        (allFaces := emb.faces)] using heSelected
  · intro i hi
    have hi0 : i.1 = 0 := Nat.lt_one_iff.mp i.isLt
    omega
  · intro i e he
    have hi : i = ⟨0, by decide⟩ := Fin.ext (Nat.lt_one_iff.mp i.isLt)
    subst hi
    have heAmbient :
        e ∈ selectedBoundarySupport
          (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)
          emb.faces.attach emb.faces.attach := by
      simpa [collarFaces, remainderFaces, relativeBoundarySupport_eq_selectedBoundarySupport] using
        he
    have heSelected : e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces := by
      simpa [selectedBoundarySupport_ambientFaceBoundary_eq (faceBoundary := emb.faceBoundary)
        (allFaces := emb.faces)] using heAmbient
    rcases Finset.mem_union.1 (data.hambientBoundaryCover heSelected) with heOuter | heInner
    · exact Finset.mem_union.2 <| Or.inl <| by
        simpa [boundaryCycle] using heOuter
    · exact Finset.mem_union.2 <| Or.inr <| by
        simp [boundaryCycle]
        exact heInner
  · intro i e he
    simp [remainderFaces, relativeBoundarySupport] at he
  · intro i e heInner
    have hi : i = ⟨0, by decide⟩ := Fin.ext (Nat.lt_one_iff.mp i.isLt)
    subst hi
    have heSelected : e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces :=
      data.hinnerAmbientBoundarySubset heInner
    simpa [collarFaces, remainderFaces, relativeBoundarySupport_eq_selectedBoundarySupport,
      selectedBoundarySupport_ambientFaceBoundary_eq (faceBoundary := emb.faceBoundary)
        (allFaces := emb.faces)] using heSelected
  · intro i hi
    have hi0 : i.1 = 0 := Nat.lt_one_iff.mp i.isLt
    omega
  · intro i hi
    have hi0 : i.1 = 0 := Nat.lt_one_iff.mp i.isLt
    omega
  · intro i hi
    have hi0 : i.1 = 0 := Nat.lt_one_iff.mp i.isLt
    omega
  · intro i j hij
    by_cases hi0 : i.1 = 0
    · by_cases hj0 : j.1 = 0
      · exact False.elim (hij (Fin.ext (hi0.trans hj0.symm)))
      · have hi : i = ⟨0, by decide⟩ := Fin.ext hi0
        have hj1 : j.1 = 1 := by
          rcases Nat.lt_succ_iff_lt_or_eq.mp j.isLt with hlt | hEq
          · exact False.elim (hj0 (Nat.lt_one_iff.mp hlt))
          · exact hEq
        have hj : j = ⟨1, by decide⟩ := Fin.ext hj1
        subst hi
        subst hj
        simpa [boundaryCycle] using data.hambientBoundaryDisjoint
    · by_cases hj0 : j.1 = 0
      · have hi1 : i.1 = 1 := by
          rcases Nat.lt_succ_iff_lt_or_eq.mp i.isLt with hlt | hEq
          · exact False.elim (hi0 (Nat.lt_one_iff.mp hlt))
          · exact hEq
        have hi : i = ⟨1, by decide⟩ := Fin.ext hi1
        have hj : j = ⟨0, by decide⟩ := Fin.ext hj0
        subst hi
        subst hj
        rw [Finset.disjoint_left]
        intro e heInner heOuter
        exact (Finset.disjoint_left.mp data.hambientBoundaryDisjoint) heOuter heInner
      · have hi1 : i.1 = 1 := by
          rcases Nat.lt_succ_iff_lt_or_eq.mp i.isLt with hlt | hEq
          · exact False.elim (hi0 (Nat.lt_one_iff.mp hlt))
          · exact hEq
        have hj1 : j.1 = 1 := by
          rcases Nat.lt_succ_iff_lt_or_eq.mp j.isLt with hlt | hEq
          · exact False.elim (hj0 (Nat.lt_one_iff.mp hlt))
          · exact hEq
        exact False.elim (hij (Fin.ext (hi1.trans hj1.symm)))
  · simp [boundaryCycle]
  · simp [boundaryCycle]

theorem admitsPlanarBoundaryAnnulusDecomposition_of_admitsPlanarBoundaryAnnulusBoundaryData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryAnnulusBoundaryData G) :
    AdmitsPlanarBoundaryAnnulusDecomposition G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨planarBoundaryAnnulusDecomposition_of_boundaryData data⟩⟩

theorem admitsPlanarBoundaryAnnulusDecomposition_of_admitsPlanarBoundaryAnnulusFaceLayerData
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryAnnulusFaceLayerData emb)) :
    AdmitsPlanarBoundaryAnnulusDecomposition G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.toPlanarBoundaryAnnulusDecomposition⟩⟩

theorem admitsPlanarBoundaryAnnulusDecomposition_of_admitsPlanarBoundaryAnnulusCurrentBoundaryData
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryAnnulusCurrentBoundaryData emb)) :
    AdmitsPlanarBoundaryAnnulusDecomposition G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.toPlanarBoundaryAnnulusDecomposition⟩⟩

theorem admitsPlanarBoundaryAnnulusCurrentBoundaryData_of_admitsPlanarBoundaryAnnulusDecomposition
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryAnnulusDecomposition G) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryAnnulusCurrentBoundaryData emb) := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.toPlanarBoundaryAnnulusCurrentBoundaryData⟩⟩

theorem admitsPlanarBoundaryAnnulusBoundaryData_of_admitsPlanarBoundaryAnnulusDecomposition
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryAnnulusDecomposition G) :
    AdmitsPlanarBoundaryAnnulusBoundaryData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.toPlanarBoundaryAnnulusBoundaryData⟩⟩

theorem PlanarBoundaryAnnulusDecomposition.remainderFaces_eq_empty_of_forall_not_lt
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusDecomposition emb) {i : Fin data.numCollars}
    (hi : ∀ j : Fin data.numCollars, ¬ i < j) :
    data.remainderFaces i = ∅ := by
  rw [data.hremainder i]
  exact laterLayerFaces_eq_empty_of_forall_not_lt data.collarFaces i hi

theorem PlanarBoundaryAnnulusDecomposition.collarFaces_nonempty
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusDecomposition emb) (i : Fin data.numCollars) :
    (data.collarFaces i).Nonempty := by
  by_cases hi : i.1 + 1 < data.numCollars
  · by_contra hempty
    have hfaceEmpty : data.collarFaces i = ∅ := by
      by_contra hne
      exact hempty (Finset.nonempty_iff_ne_empty.mpr hne)
    have hcurrentEq : data.currentFaces i = data.remainderFaces i := by
      simp [PlanarBoundaryAnnulusDecomposition.currentFaces, hfaceEmpty]
    have hboundaryEq :
        data.boundaryCycle (Fin.castSucc i) ∪
            data.boundaryCycle ⟨data.numCollars, Nat.lt_succ_self data.numCollars⟩ =
          data.boundaryCycle (Fin.succ i) ∪
            data.boundaryCycle ⟨data.numCollars, Nat.lt_succ_self data.numCollars⟩ := by
      calc
        data.boundaryCycle (Fin.castSucc i) ∪
            data.boundaryCycle ⟨data.numCollars, Nat.lt_succ_self data.numCollars⟩ =
          relativeBoundarySupport
            (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)
            (data.currentFaces i) := by
              symm
              exact data.currentFaces_boundary_eq i
        _ =
          relativeBoundarySupport
            (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)
            (data.remainderFaces i) := by
              simp [hcurrentEq]
        _ =
          data.boundaryCycle (Fin.succ i) ∪
            data.boundaryCycle ⟨data.numCollars, Nat.lt_succ_self data.numCollars⟩ :=
              data.remainderFaces_boundary_eq i hi
    rcases data.boundaryCycle_nonempty (Fin.castSucc i) with ⟨e, he⟩
    have heUnion :
        e ∈ data.boundaryCycle (Fin.castSucc i) ∪
            data.boundaryCycle ⟨data.numCollars, Nat.lt_succ_self data.numCollars⟩ :=
      Finset.mem_union.2 <| Or.inl he
    rw [hboundaryEq] at heUnion
    have hnotInner :
        e ∉ data.boundaryCycle ⟨data.numCollars, Nat.lt_succ_self data.numCollars⟩ := by
      intro hinner
      exact (Finset.disjoint_left.mp
        (data.boundaryCycle_disjoint_of_ne (by
          intro hEq
          have := congrArg Fin.val hEq
          exact Nat.ne_of_lt i.isLt this))) he hinner
    have hnext : e ∈ data.boundaryCycle (Fin.succ i) := by
      rcases Finset.mem_union.1 heUnion with hnext | hinner
      · exact hnext
      · exact False.elim (hnotInner hinner)
    exact (Finset.disjoint_left.mp
      (data.boundaryCycle_disjoint_of_ne (by
        intro hEq
        have := congrArg Fin.val hEq
        exact Nat.ne_of_lt (Nat.lt_succ_self i.1) this))) he hnext
  · have hterminal : i.1 + 1 = data.numCollars := by
      omega
    by_contra hempty
    have hfaceEmpty : data.collarFaces i = ∅ := by
      by_contra hne
      exact hempty (Finset.nonempty_iff_ne_empty.mpr hne)
    have hnoLater : ∀ j : Fin data.numCollars, ¬ i < j := by
      intro j hij
      omega
    have hremEmpty : data.remainderFaces i = ∅ :=
      data.remainderFaces_eq_empty_of_forall_not_lt hnoLater
    have hcurrentEmpty : data.currentFaces i = ∅ := by
      simp [PlanarBoundaryAnnulusDecomposition.currentFaces, hfaceEmpty, hremEmpty]
    have hboundaryEmpty :
        relativeBoundarySupport
            (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)
            (data.currentFaces i) = ∅ := by
      simp [hcurrentEmpty, relativeBoundarySupport]
    rcases data.boundaryCycle_nonempty (Fin.castSucc i) with ⟨e, he⟩
    have hunion :
        (data.boundaryCycle (Fin.castSucc i) ∪
          data.boundaryCycle ⟨data.numCollars, Nat.lt_succ_self data.numCollars⟩).Nonempty :=
      ⟨e, Finset.mem_union.2 <| Or.inl he⟩
    have hEq := data.currentFaces_boundary_eq i
    rw [hboundaryEmpty] at hEq
    have : (∅ : Finset G.edgeSet).Nonempty := by
      simpa [hEq] using hunion
    simp at this

theorem PlanarBoundaryAnnulusDecomposition.numCollars_le_card_faces
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusDecomposition emb) :
    data.numCollars ≤ emb.faces.card := by
  classical
  let pickFace : Fin data.numCollars → AmbientFace emb.faces := fun i =>
    Classical.choose (data.collarFaces_nonempty i)
  have hpick :
      ∀ i : Fin data.numCollars, pickFace i ∈ data.collarFaces i := by
    intro i
    simpa [pickFace] using Classical.choose_spec (data.collarFaces_nonempty i)
  have hpick_injective : Function.Injective pickFace := by
    intro i j hij
    by_contra hne
    exact
      (Finset.disjoint_left.mp (data.hdisjoint hne))
        (hpick i) (by simpa [hij] using hpick j)
  have hcard :
      Fintype.card (Fin data.numCollars) ≤ Fintype.card (AmbientFace emb.faces) :=
    Fintype.card_le_of_injective pickFace hpick_injective
  simpa [Fintype.card_coe] using hcard

theorem PlanarBoundaryAnnulusDecomposition.remainderFaces_ssubset_currentFaces
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusDecomposition emb) (i : Fin data.numCollars) :
    data.remainderFaces i ⊂ data.currentFaces i := by
  apply ssubset_of_subset_of_ne
  · exact data.remainderFaces_subset_currentFaces i
  · intro hEq
    rcases data.collarFaces_nonempty i with ⟨f, hf⟩
    have hfCurrent : f ∈ data.currentFaces i := by
      exact Finset.mem_union.2 <| Or.inl hf
    have hfRemainder : f ∈ data.remainderFaces i := by
      simpa [hEq] using hfCurrent
    exact (Finset.disjoint_left.mp (data.collarFaces_disjoint_remainderFaces i)) hf hfRemainder

theorem PlanarBoundaryAnnulusDecomposition.currentFaces_nonempty
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusDecomposition emb) (i : Fin data.numCollars) :
    (data.currentFaces i).Nonempty := by
  rcases data.collarFaces_nonempty i with ⟨f, hf⟩
  exact ⟨f, by simp [PlanarBoundaryAnnulusDecomposition.currentFaces, hf]⟩

theorem PlanarBoundaryAnnulusCurrentBoundaryData.numCollars_le_card_faces
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCurrentBoundaryData emb) :
    data.numCollars ≤ emb.faces.card := by
  simpa using data.toPlanarBoundaryAnnulusDecomposition.numCollars_le_card_faces

theorem PlanarBoundaryAnnulusDecomposition.remainderFaces_nonempty
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusDecomposition emb) (i : Fin data.numCollars)
    (hi : i.1 + 1 < data.numCollars) :
    (data.remainderFaces i).Nonempty := by
  by_contra hempty
  have hremEmpty : data.remainderFaces i = ∅ := by
    by_contra hne
    exact hempty (Finset.nonempty_iff_ne_empty.mpr hne)
  have hboundaryEmpty :
      relativeBoundarySupport
          (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)
          (data.remainderFaces i) = ∅ := by
    simp [hremEmpty, relativeBoundarySupport]
  rcases data.boundaryCycle_intermediate_nonempty i hi with ⟨e, he⟩
  have hunion :
      (data.boundaryCycle (Fin.succ i) ∪
        data.boundaryCycle ⟨data.numCollars, Nat.lt_succ_self data.numCollars⟩).Nonempty :=
    ⟨e, Finset.mem_union.2 <| Or.inl he⟩
  have hEq := data.remainderFaces_boundary_eq i hi
  rw [hboundaryEmpty] at hEq
  have : (∅ : Finset G.edgeSet).Nonempty := by
    simpa [hEq] using hunion
  simp at this

theorem PlanarBoundaryAnnulusDecomposition.currentFaces_next_ssubset_currentFaces
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusDecomposition emb) (i : Fin data.numCollars)
    (hi : i.1 + 1 < data.numCollars) :
    data.currentFaces ⟨i.1 + 1, hi⟩ ⊂ data.currentFaces i := by
  let j : Fin data.numCollars := ⟨i.1 + 1, hi⟩
  have hij : i < j := by
    show i.1 < j.1
    dsimp [j]
    omega
  apply ssubset_of_subset_of_ne
  · exact (data.currentFaces_subset_remainderFaces_of_lt hij).trans
      (data.remainderFaces_subset_currentFaces i)
  · intro hEq
    rcases data.collarFaces_nonempty i with ⟨f, hf⟩
    have hfCurrent : f ∈ data.currentFaces i := by
      exact Finset.mem_union.2 <| Or.inl hf
    have hfNext : f ∈ data.currentFaces j := by
      simpa [j, hEq] using hfCurrent
    have hfRemainder : f ∈ data.remainderFaces i :=
      data.currentFaces_subset_remainderFaces_of_lt hij hfNext
    exact (Finset.disjoint_left.mp (data.collarFaces_disjoint_remainderFaces i)) hf hfRemainder

theorem PlanarBoundaryAnnulusDecomposition.currentFaces_subset_currentFaces_of_lt
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusDecomposition emb) {i j : Fin data.numCollars}
    (hij : i < j) :
    data.currentFaces j ⊆ data.currentFaces i :=
  (data.currentFaces_subset_remainderFaces_of_lt hij).trans
    (data.remainderFaces_subset_currentFaces i)

theorem PlanarBoundaryAnnulusDecomposition.currentFaces_ssubset_currentFaces_of_lt
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusDecomposition emb) {i j : Fin data.numCollars}
    (hij : i < j) :
    data.currentFaces j ⊂ data.currentFaces i := by
  apply ssubset_of_subset_of_ne
  · exact data.currentFaces_subset_currentFaces_of_lt hij
  · intro hEq
    rcases data.collarFaces_nonempty i with ⟨f, hf⟩
    have hfCurrent : f ∈ data.currentFaces i := by
      exact Finset.mem_union.2 <| Or.inl hf
    have hfLater : f ∈ data.currentFaces j := by
      simpa [hEq] using hfCurrent
    have hfRemainder : f ∈ data.remainderFaces i :=
      data.currentFaces_subset_remainderFaces_of_lt hij hfLater
    exact (Finset.disjoint_left.mp (data.collarFaces_disjoint_remainderFaces i)) hf hfRemainder

theorem PlanarBoundaryAnnulusDecomposition.remainderFaces_ssubset_remainderFaces_of_lt
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusDecomposition emb) {i j : Fin data.numCollars}
    (hij : i < j) :
    data.remainderFaces j ⊂ data.remainderFaces i := by
  apply ssubset_of_subset_of_ne
  · exact data.remainderFaces_subset_remainderFaces_of_lt hij
  · intro hEq
    rcases data.collarFaces_nonempty j with ⟨f, hf⟩
    have hfEarlier : f ∈ data.remainderFaces i :=
      data.collarFaces_subset_remainderFaces_of_lt hij hf
    have hfLater : f ∈ data.remainderFaces j := by
      simpa [hEq] using hfEarlier
    exact (Finset.disjoint_left.mp (data.collarFaces_disjoint_remainderFaces j)) hf hfLater

end Mettapedia.GraphTheory.FourColor
