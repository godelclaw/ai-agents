import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryPeeling
import Mettapedia.GraphTheory.FourColor.Theorem49LocalRemainderBoundaryCollar
import Mettapedia.GraphTheory.FourColor.Theorem49RelativeBoundaryCollar
import Mettapedia.GraphTheory.FourColor.Theorem49RemainderBoundaryCollar

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- Boundary-aware collar-layer witness-cover data for the Theorem 4.9 annihilator step. This
matches the paper's Step 2 more closely than an arbitrary height function: peeled faces are grouped
into a finite stack of layers, and every non-witness remainder edge on a face points either to the
selected annulus boundary support or to a witness edge in a strictly later layer. -/
structure PlanarBoundaryCollarLayerFacePeelWitnessData {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) where
  numLayers : ℕ
  layerFaces : Fin numLayers → Finset (AmbientFace emb.faces)
  witnessEdge : AmbientFace emb.faces → G.edgeSet
  hdisjoint : ∀ {i j : Fin numLayers}, i ≠ j → Disjoint (layerFaces i) (layerFaces j)
  hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆
    (Finset.univ.biUnion layerFaces).image witnessEdge
  hwitness : ∀ i f, f ∈ layerFaces i → witnessEdge f ∈ emb.faceBoundary f.1
  hrest : ∀ i f, f ∈ layerFaces i → ∀ e ∈ (emb.faceBoundary f.1).erase (witnessEdge f),
    e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
      ∃ j : Fin numLayers, i < j ∧ ∃ g ∈ layerFaces j, witnessEdge g = e

/-- Graph-level existence form of the finite collar-layer target for an annulus-shaped embedding
with boundary. -/
def AdmitsPlanarBoundaryCollarLayerFacePeelWitnessData
    (G : SimpleGraph V) : Prop :=
  ∃ emb : PlaneEmbeddingWithBoundary G,
    Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb)

/-- Geometry-facing annulus target that explicitly records the remainder face set after each
peeled collar, but only for the locally used later witness edges. This is weaker than the global
frontier-ownership package and matches the current well-founded interior-dual endpoint more
closely. -/
abbrev PlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) :=
  LocalRemainderBoundaryCollarLayerFacePeelWitnessData emb.faces.attach
    (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)

/-- Graph-level existence form of the weaker local explicit-remainder annulus target. -/
def AdmitsPlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
    (G : SimpleGraph V) : Prop :=
  ∃ emb : PlaneEmbeddingWithBoundary G,
    Nonempty (PlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData emb)

/-- The stronger geometry-facing annulus target phrased directly over a boundary-aware embedding:
the theorem-layer collar data whose remainder-frontier edges are tracked by relative boundary in
the deeper suffix of layers. -/
abbrev PlanarBoundaryRelativeBoundaryCollarLayerFacePeelWitnessData {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) :=
  RelativeBoundaryCollarLayerFacePeelWitnessData emb.faces.attach
    (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)

/-- Graph-level existence form of the stronger geometry-facing relative-boundary collar target. -/
def AdmitsPlanarBoundaryRelativeBoundaryCollarLayerFacePeelWitnessData
    (G : SimpleGraph V) : Prop :=
  ∃ emb : PlaneEmbeddingWithBoundary G,
    Nonempty (PlanarBoundaryRelativeBoundaryCollarLayerFacePeelWitnessData emb)

/-- Stronger geometry-facing annulus target that explicitly records the remainder face set after
each peeled collar. -/
abbrev PlanarBoundaryRemainderBoundaryCollarLayerFacePeelWitnessData {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) :=
  RemainderBoundaryCollarLayerFacePeelWitnessData emb.faces.attach
    (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)

/-- Graph-level existence form of the explicit-remainder annulus target. -/
def AdmitsPlanarBoundaryRemainderBoundaryCollarLayerFacePeelWitnessData
    (G : SimpleGraph V) : Prop :=
  ∃ emb : PlaneEmbeddingWithBoundary G,
    Nonempty (PlanarBoundaryRemainderBoundaryCollarLayerFacePeelWitnessData emb)

/-- The peeled faces covered by a collar-layer package. -/
def PlanarBoundaryCollarLayerFacePeelWitnessData.peelFaces {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryCollarLayerFacePeelWitnessData emb) :
    Finset (AmbientFace emb.faces) :=
  Finset.univ.biUnion data.layerFaces

theorem PlanarBoundaryCollarLayerFacePeelWitnessData.mem_peelFaces_iff {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryCollarLayerFacePeelWitnessData emb) {f : AmbientFace emb.faces} :
    f ∈ data.peelFaces ↔ ∃ i, f ∈ data.layerFaces i := by
  unfold PlanarBoundaryCollarLayerFacePeelWitnessData.peelFaces
  constructor
  · intro hf
    rcases Finset.mem_biUnion.1 hf with ⟨i, -, hfi⟩
    exact ⟨i, hfi⟩
  · rintro ⟨i, hfi⟩
    exact Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hfi⟩

/-- Canonical layer index attached to a collar-layer package. Since layers are pairwise disjoint,
this is the unique layer containing a peeled face, and `0` on faces outside the package. -/
noncomputable def PlanarBoundaryCollarLayerFacePeelWitnessData.layerHeight {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryCollarLayerFacePeelWitnessData emb) (f : AmbientFace emb.faces) : ℕ :=
  (Finset.univ.filter fun i : Fin data.numLayers => f ∈ data.layerFaces i).sup Fin.val

theorem PlanarBoundaryCollarLayerFacePeelWitnessData.layerHeight_eq_of_mem {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryCollarLayerFacePeelWitnessData emb)
    {i : Fin data.numLayers} {f : AmbientFace emb.faces} (hf : f ∈ data.layerFaces i) :
    data.layerHeight f = i.1 := by
  have hs :
      Finset.univ.filter (fun j : Fin data.numLayers => f ∈ data.layerFaces j) = {i} := by
    ext j
    constructor
    · intro hj
      have hfj : f ∈ data.layerFaces j := (Finset.mem_filter.1 hj).2
      by_cases hji : j = i
      · simp [hji]
      · exact False.elim <| (Finset.disjoint_left.1 (data.hdisjoint hji)) hfj hf
    · intro hj
      have hji : j = i := Finset.mem_singleton.1 hj
      subst hji
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hf⟩
  unfold PlanarBoundaryCollarLayerFacePeelWitnessData.layerHeight
  simp [hs]

theorem PlanarBoundaryCollarLayerFacePeelWitnessData.layerHeight_lt_of_mem_of_lt_of_mem
    {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryCollarLayerFacePeelWitnessData emb)
    {i j : Fin data.numLayers} {f g : AmbientFace emb.faces}
    (hf : f ∈ data.layerFaces i) (hij : i < j) (hg : g ∈ data.layerFaces j) :
    data.layerHeight f < data.layerHeight g := by
  rw [data.layerHeight_eq_of_mem hf, data.layerHeight_eq_of_mem hg]
  exact hij

/-- A finite collar-layer package canonically yields the weaker height-ordered witness-cover
interface by taking the unique layer index of each peeled face as its height. -/
noncomputable def
    PlanarBoundaryCollarLayerFacePeelWitnessData.toHeightOrderedFacePeelWitnessData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryCollarLayerFacePeelWitnessData emb) :
    PlanarBoundaryHeightOrderedFacePeelWitnessData emb := by
  refine
    { peelFaces := data.peelFaces
      witnessEdge := data.witnessEdge
      height := data.layerHeight
      hcover := ?_
      hwitness := ?_
      hrest := ?_ }
  · simpa [PlanarBoundaryCollarLayerFacePeelWitnessData.peelFaces] using data.hcover
  · intro f hf
    rcases (data.mem_peelFaces_iff).1 hf with ⟨i, hfi⟩
    exact data.hwitness i f hfi
  · intro f hf e he
    rcases (data.mem_peelFaces_iff).1 hf with ⟨i, hfi⟩
    rcases data.hrest i f hfi e he with hboundary | ⟨j, hij, g, hgj, hge⟩
    · exact Or.inl hboundary
    · refine Or.inr ⟨g, (data.mem_peelFaces_iff).2 ⟨j, hgj⟩, hge, ?_⟩
      exact data.layerHeight_lt_of_mem_of_lt_of_mem hfi hij hgj

/-- Canonical collar-layer decomposition of an existing height-ordered witness-cover package, by
grouping peeled faces according to their natural-valued height. This repackages the algebraic
peeling data in the paper's finite nested-collar form. -/
noncomputable def
    planarBoundaryCollarLayerFacePeelWitnessData_of_heightOrderedFacePeelWitnessData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb) :
    PlanarBoundaryCollarLayerFacePeelWitnessData emb := by
  let maxHeight : ℕ := data.peelFaces.sup data.height
  let layerFaces : Fin (maxHeight + 1) → Finset (AmbientFace emb.faces) :=
    fun i => data.peelFaces.filter fun f => data.height f = i.1
  refine
    { numLayers := maxHeight + 1
      layerFaces := layerFaces
      witnessEdge := data.witnessEdge
      hdisjoint := ?_
      hcover := ?_
      hwitness := ?_
      hrest := ?_ }
  · intro i j hij
    refine Finset.disjoint_left.2 ?_
    intro f hfi hfj
    have hfi' : data.height f = i.1 := (Finset.mem_filter.1 hfi).2
    have hfj' : data.height f = j.1 := (Finset.mem_filter.1 hfj).2
    apply hij
    exact Fin.ext <| hfi'.symm.trans hfj'
  · intro e he
    rcases Finset.mem_image.1 (data.hcover he) with ⟨f, hf, hfe⟩
    have hbound : data.height f < maxHeight + 1 := by
      exact Nat.lt_succ_of_le (Finset.le_sup hf)
    let i : Fin (maxHeight + 1) := ⟨data.height f, hbound⟩
    refine Finset.mem_image.2 ⟨f, ?_, hfe⟩
    exact Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, Finset.mem_filter.2 ⟨hf, rfl⟩⟩
  · intro i f hfi
    exact data.hwitness f (Finset.mem_filter.1 hfi).1
  · intro i f hfi e he
    rcases data.hrest f (Finset.mem_filter.1 hfi).1 e he with hboundary | ⟨g, hg, hge, hlt⟩
    · exact Or.inl hboundary
    · have hbound : data.height g < maxHeight + 1 := by
        exact Nat.lt_succ_of_le (Finset.le_sup hg)
      let j : Fin (maxHeight + 1) := ⟨data.height g, hbound⟩
      refine Or.inr ⟨j, ?_, g, Finset.mem_filter.2 ⟨hg, rfl⟩, hge⟩
      have hfiHeight : i.1 = data.height f := (Finset.mem_filter.1 hfi).2.symm
      exact hfiHeight.trans_lt hlt

theorem admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_exists_planarBoundaryHeightOrderedFacePeelWitnessData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryHeightOrderedFacePeelWitnessData G) :
    AdmitsPlanarBoundaryCollarLayerFacePeelWitnessData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨
    planarBoundaryCollarLayerFacePeelWitnessData_of_heightOrderedFacePeelWitnessData data⟩⟩

/-- The generic theorem-layer finite collar package on attached ambient faces canonically upgrades
to the boundary-aware planarity-side collar package for the same embedding. -/
noncomputable def
    planarBoundaryCollarLayerFacePeelWitnessData_of_genericCollarLayerFacePeelWitnessData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : CollarLayerFacePeelWitnessData emb.faces.attach
      (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) :
    PlanarBoundaryCollarLayerFacePeelWitnessData emb := by
  refine
    { numLayers := data.numLayers
      layerFaces := data.layerFaces
      witnessEdge := data.witnessEdge
      hdisjoint := data.hdisjoint
      hcover := ?_
      hwitness := ?_
      hrest := ?_ }
  · simpa [interiorEdgeSupport_ambientFaceBoundary_eq
      (faceBoundary := emb.faceBoundary) (allFaces := emb.faces)] using data.hcover
  · intro i f hfi
    simpa [ambientFaceBoundary] using data.hwitness i f hfi
  · intro i f hfi e he
    rcases data.hrest i f hfi e (by simpa [ambientFaceBoundary] using he) with
      hboundary | ⟨j, hij, g, hgj, hge⟩
    · exact Or.inl <| by
        simpa [selectedBoundarySupport_ambientFaceBoundary_eq
          (faceBoundary := emb.faceBoundary) (allFaces := emb.faces)] using hboundary
    · exact Or.inr ⟨j, hij, g, hgj, hge⟩

/-- The stronger theorem-layer collar package that uses relative boundaries of the deeper remainder
canonically lowers to the boundary-aware planarity-side collar package for the same embedding. -/
noncomputable def
    planarBoundaryCollarLayerFacePeelWitnessData_of_genericRelativeBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : RelativeBoundaryCollarLayerFacePeelWitnessData emb.faces.attach
      (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) :
    PlanarBoundaryCollarLayerFacePeelWitnessData emb :=
  planarBoundaryCollarLayerFacePeelWitnessData_of_genericCollarLayerFacePeelWitnessData
    data.toCollarLayerFacePeelWitnessData

/-- The weaker local explicit-remainder theorem-layer collar package canonically lowers to the
boundary-aware planarity-side collar package for the same embedding. -/
noncomputable def
    planarBoundaryCollarLayerFacePeelWitnessData_of_genericLocalRemainderBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : LocalRemainderBoundaryCollarLayerFacePeelWitnessData emb.faces.attach
      (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) :
    PlanarBoundaryCollarLayerFacePeelWitnessData emb :=
  planarBoundaryCollarLayerFacePeelWitnessData_of_genericCollarLayerFacePeelWitnessData
    data.toCollarLayerFacePeelWitnessData

theorem
    admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_exists_genericRelativeBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (RelativeBoundaryCollarLayerFacePeelWitnessData emb.faces.attach
        (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary))) :
    AdmitsPlanarBoundaryCollarLayerFacePeelWitnessData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨
    planarBoundaryCollarLayerFacePeelWitnessData_of_genericRelativeBoundaryCollarLayerFacePeelWitnessData
      data⟩⟩

theorem
    admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_admitsPlanarBoundaryRelativeBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryRelativeBoundaryCollarLayerFacePeelWitnessData G) :
    AdmitsPlanarBoundaryCollarLayerFacePeelWitnessData G :=
  admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_exists_genericRelativeBoundaryCollarLayerFacePeelWitnessData
    hG

theorem
    admitsPlanarBoundaryRelativeBoundaryCollarLayerFacePeelWitnessData_of_admitsPlanarBoundaryRemainderBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryRemainderBoundaryCollarLayerFacePeelWitnessData G) :
    AdmitsPlanarBoundaryRelativeBoundaryCollarLayerFacePeelWitnessData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.toRelativeBoundaryCollarLayerFacePeelWitnessData⟩⟩

theorem
    admitsPlanarBoundaryRemainderBoundaryCollarLayerFacePeelWitnessData_of_admitsPlanarBoundaryRelativeBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryRelativeBoundaryCollarLayerFacePeelWitnessData G) :
    AdmitsPlanarBoundaryRemainderBoundaryCollarLayerFacePeelWitnessData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.toRemainderBoundaryCollarLayerFacePeelWitnessData⟩⟩

theorem
    admitsPlanarBoundaryRemainderBoundaryCollarLayerFacePeelWitnessData_iff
    {G : SimpleGraph V} :
    AdmitsPlanarBoundaryRemainderBoundaryCollarLayerFacePeelWitnessData G ↔
      AdmitsPlanarBoundaryRelativeBoundaryCollarLayerFacePeelWitnessData G := by
  constructor
  · exact
      admitsPlanarBoundaryRelativeBoundaryCollarLayerFacePeelWitnessData_of_admitsPlanarBoundaryRemainderBoundaryCollarLayerFacePeelWitnessData
  · exact
      admitsPlanarBoundaryRemainderBoundaryCollarLayerFacePeelWitnessData_of_admitsPlanarBoundaryRelativeBoundaryCollarLayerFacePeelWitnessData

theorem
    admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_admitsPlanarBoundaryRemainderBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryRemainderBoundaryCollarLayerFacePeelWitnessData G) :
    AdmitsPlanarBoundaryCollarLayerFacePeelWitnessData G :=
  admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_admitsPlanarBoundaryRelativeBoundaryCollarLayerFacePeelWitnessData
    (admitsPlanarBoundaryRelativeBoundaryCollarLayerFacePeelWitnessData_of_admitsPlanarBoundaryRemainderBoundaryCollarLayerFacePeelWitnessData
      hG)

theorem
    admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_admitsPlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData G) :
    AdmitsPlanarBoundaryCollarLayerFacePeelWitnessData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨
    planarBoundaryCollarLayerFacePeelWitnessData_of_genericLocalRemainderBoundaryCollarLayerFacePeelWitnessData
      data⟩⟩

/-- The weakest current root-free interior-dual package canonically induces the finite collar-layer
interface directly, without first passing through a planarity-side well-founded witness wrapper. -/
noncomputable def
    planarBoundaryCollarLayerFacePeelWitnessData_of_interiorDualWellFoundedParentPeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : InteriorDualWellFoundedParentPeelData emb.faces emb.faceBoundary) :
    PlanarBoundaryCollarLayerFacePeelWitnessData emb :=
  planarBoundaryCollarLayerFacePeelWitnessData_of_genericCollarLayerFacePeelWitnessData
    data.toCollarLayerFacePeelWitnessData

/-- The weakest current root-free interior-dual package canonically yields the weaker local
explicit-remainder annulus target. -/
noncomputable def
    planarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData_of_interiorDualWellFoundedParentPeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : InteriorDualWellFoundedParentPeelData emb.faces emb.faceBoundary) :
    PlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData emb :=
  data.toLocalRemainderBoundaryCollarLayerFacePeelWitnessData

theorem
    witnessEdge_planarBoundaryCollarLayerFacePeelWitnessData_of_interiorDualWellFoundedParentPeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : InteriorDualWellFoundedParentPeelData emb.faces emb.faceBoundary)
    {f : AmbientFace emb.faces} :
    (planarBoundaryCollarLayerFacePeelWitnessData_of_interiorDualWellFoundedParentPeelData
      data).witnessEdge f =
      parentSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
        data.parentFace data.fallbackEdge data.hparentAdj f :=
  rfl

theorem admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_exists_interiorDualWellFoundedParentPeelData
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (InteriorDualWellFoundedParentPeelData emb.faces emb.faceBoundary)) :
    AdmitsPlanarBoundaryCollarLayerFacePeelWitnessData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨
    planarBoundaryCollarLayerFacePeelWitnessData_of_interiorDualWellFoundedParentPeelData
      data⟩⟩

theorem
    admitsPlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData_of_exists_interiorDualWellFoundedParentPeelData
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (InteriorDualWellFoundedParentPeelData emb.faces emb.faceBoundary)) :
    AdmitsPlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨
    planarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData_of_interiorDualWellFoundedParentPeelData
      data⟩⟩

/-- The strongest current boundary-root adjacency-distance interior-dual package canonically
induces the finite collar-layer witness-cover interface by grouping peeled faces according to their
interior-dual root distance while keeping the canonical rooted shared edge as witness. -/
noncomputable def
    planarBoundaryCollarLayerFacePeelWitnessData_of_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) :
    PlanarBoundaryCollarLayerFacePeelWitnessData emb :=
  planarBoundaryCollarLayerFacePeelWitnessData_of_heightOrderedFacePeelWitnessData
    (planarBoundaryHeightOrderedFacePeelWitnessData_of_interiorDualBoundaryRootAdjDistancePeelData
      data)

theorem admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_exists_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)) :
    AdmitsPlanarBoundaryCollarLayerFacePeelWitnessData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨
    planarBoundaryCollarLayerFacePeelWitnessData_of_interiorDualBoundaryRootAdjDistancePeelData
      data⟩⟩

/-- Boundary-aware global annihilator form of the finite collar-layer interface. This is the formal
counterpart of the paper's "peel the annulus into nested collars" step. -/
theorem zero_on_allEdges_of_planarBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G)
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (data : PlanarBoundaryCollarLayerFacePeelWitnessData emb)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0)
    (horth : ∀ i f, f ∈ data.layerFaces i →
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
  have horth' :
      ∀ f ∈ data.toHeightOrderedFacePeelWitnessData.peelFaces,
        ∀ γ, γ ≠ 0 → γ ≠ C (data.toHeightOrderedFacePeelWitnessData.witnessEdge f) →
          chainDot
              (boundaryBicoloredEdges C
                (C (data.toHeightOrderedFacePeelWitnessData.witnessEdge f))
                (C (data.toHeightOrderedFacePeelWitnessData.witnessEdge f) + γ)
                (emb.faceBoundary f.1))
              z
              (polarizedFaceGenerator C
                (C (data.toHeightOrderedFacePeelWitnessData.witnessEdge f))
                (C (data.toHeightOrderedFacePeelWitnessData.witnessEdge f) + γ)
                (emb.faceBoundary f.1)) = 0 := by
    intro f hf γ hγ0 hγd
    rcases (data.mem_peelFaces_iff).1 (by
      simpa [PlanarBoundaryCollarLayerFacePeelWitnessData.toHeightOrderedFacePeelWitnessData,
        PlanarBoundaryCollarLayerFacePeelWitnessData.peelFaces] using hf) with ⟨i, hfi⟩
    simpa [PlanarBoundaryCollarLayerFacePeelWitnessData.toHeightOrderedFacePeelWitnessData] using
      horth i f hfi γ hγ0 hγd
  exact zero_on_allEdges_of_planarBoundaryHeightOrderedFacePeelWitnessData
    (emb := emb) (C := C) (htait := htait) (z := z)
    (data := data.toHeightOrderedFacePeelWitnessData)
    (hzeroBoundary := hzeroBoundary) (horth := horth')

/-- Boundary-aware global annihilator form of the stronger relative-boundary collar target. This
is the planarity-side theorem whose hypotheses most closely match an actual outside-in peel of the
annulus into successive remainder collars. -/
theorem zero_on_allEdges_of_planarBoundaryRelativeBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G)
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (data : PlanarBoundaryRelativeBoundaryCollarLayerFacePeelWitnessData emb)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0)
    (horth : ∀ i f, f ∈ data.layerFaces i →
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
  exact zero_on_allEdges_of_planarBoundaryCollarLayerFacePeelWitnessData
    (emb := emb) (C := C) (htait := htait) (z := z)
    (data := planarBoundaryCollarLayerFacePeelWitnessData_of_genericRelativeBoundaryCollarLayerFacePeelWitnessData
      data)
    (hzeroBoundary := hzeroBoundary) (horth := horth)

/-- Boundary-aware global annihilator form of the explicit-remainder collar target. This is the
closest current planarity-side formulation to a literal sequence of remainder annuli. -/
theorem zero_on_allEdges_of_planarBoundaryRemainderBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G)
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (data : PlanarBoundaryRemainderBoundaryCollarLayerFacePeelWitnessData emb)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0)
    (horth : ∀ i f, f ∈ data.layerFaces i →
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
  exact zero_on_allEdges_of_planarBoundaryRelativeBoundaryCollarLayerFacePeelWitnessData
    (emb := emb) (C := C) (htait := htait) (z := z)
    (data := data.toRelativeBoundaryCollarLayerFacePeelWitnessData)
    (hzeroBoundary := hzeroBoundary) (horth := horth)

/-- Boundary-aware global annihilator form of the weaker local explicit-remainder collar target.
This is the first annulus-side collar formulation directly derivable from the current weakest
well-founded interior-dual endpoint while still naming the deeper remainder annulus explicitly. -/
theorem zero_on_allEdges_of_planarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G)
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (data : PlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData emb)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0)
    (horth : ∀ i f, f ∈ data.layerFaces i →
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
  exact zero_on_allEdges_of_planarBoundaryCollarLayerFacePeelWitnessData
    (emb := emb) (C := C) (htait := htait) (z := z)
    (data :=
      planarBoundaryCollarLayerFacePeelWitnessData_of_genericLocalRemainderBoundaryCollarLayerFacePeelWitnessData
        data)
    (hzeroBoundary := hzeroBoundary) (horth := horth)

/-- Definition 4.8 generator-family form of the weakest local explicit-remainder collar target.
The local orthogonality equations required by the collar peeling theorem are discharged directly
from membership of `C` in the Kempe closure of `C₀`. -/
theorem zero_on_allEdges_of_planarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData_of_annihilatesKempeClosureGeneratorFamily
    {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G)
    (C₀ C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C)
    (hC : C ∈ G.EdgeKempeClosure C₀) (z : G.edgeSet → Color)
    (data : PlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData emb)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0)
    (hgen : AnnihilatesKempeClosureGeneratorFamily emb.faceBoundary C₀ z) :
    ∀ e, z e = 0 := by
  exact
    zero_on_allEdges_of_planarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
      (emb := emb) (C := C) (htait := htait) (z := z) (data := data)
      (hzeroBoundary := hzeroBoundary)
      (horth := by
        intro i f _hfi γ hγ0 hγne
        exact
          localOrthogonality_of_annihilatesKempeClosureGeneratorFamily
            (faceBoundary := emb.faceBoundary) (hC := hC) hgen
            (f := f.1) (e := data.witnessEdge f) (htait (data.witnessEdge f))
            γ hγ0 hγne)

/-- Existential graph-level annihilator form of the finite collar-layer interface. -/
theorem zero_on_allEdges_of_exists_planarBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (hdata : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        (∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0) ∧
        (∀ i f, f ∈ data.layerFaces i →
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
  exact zero_on_allEdges_of_planarBoundaryCollarLayerFacePeelWitnessData
    (emb := emb) (C := C) (htait := htait) (z := z) (data := data)
    (hzeroBoundary := hzeroBoundary) (horth := horth)

/-- Existential graph-level annihilator form of the weaker local explicit-remainder annulus
target. This exposes the weakest explicit remainder geometry as a direct graph-level Step 2
endpoint, without first forgetting it to ordinary collar-layer data. -/
theorem zero_on_allEdges_of_exists_planarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (hdata : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData emb,
        (∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0) ∧
        (∀ i f, f ∈ data.layerFaces i →
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
  exact zero_on_allEdges_of_planarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
    (emb := emb) (C := C) (htait := htait) (z := z) (data := data)
    (hzeroBoundary := hzeroBoundary) (horth := horth)

/-- Existential graph-level generator-family annihilator form of the weaker local
explicit-remainder annulus target. This is the theorem-facing endpoint for the current
root-free local-remainder route. -/
theorem zero_on_allEdges_of_exists_planarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData_of_annihilatesKempeClosureGeneratorFamily
    {G : SimpleGraph V}
    (C₀ C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C)
    (hC : C ∈ G.EdgeKempeClosure C₀) (z : G.edgeSet → Color)
    (hdata : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData emb,
        (∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0) ∧
        AnnihilatesKempeClosureGeneratorFamily emb.faceBoundary C₀ z) :
    ∀ e, z e = 0 := by
  rcases hdata with ⟨emb, data, hzeroBoundary, hgen⟩
  exact
    zero_on_allEdges_of_planarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData_of_annihilatesKempeClosureGeneratorFamily
      (emb := emb) (C₀ := C₀) (C := C) (htait := htait) (hC := hC)
      (z := z) (data := data) (hzeroBoundary := hzeroBoundary) (hgen := hgen)

/-- Existential graph-level annihilator form of the stronger relative-boundary collar target. -/
theorem zero_on_allEdges_of_exists_planarBoundaryRelativeBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (hdata : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryRelativeBoundaryCollarLayerFacePeelWitnessData emb,
        (∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0) ∧
        (∀ i f, f ∈ data.layerFaces i →
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
  exact zero_on_allEdges_of_planarBoundaryRelativeBoundaryCollarLayerFacePeelWitnessData
    (emb := emb) (C := C) (htait := htait) (z := z) (data := data)
    (hzeroBoundary := hzeroBoundary) (horth := horth)

/-- Existential graph-level annihilator form of the explicit-remainder annulus target. -/
theorem zero_on_allEdges_of_exists_planarBoundaryRemainderBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (hdata : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryRemainderBoundaryCollarLayerFacePeelWitnessData emb,
        (∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0) ∧
        (∀ i f, f ∈ data.layerFaces i →
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
  exact zero_on_allEdges_of_planarBoundaryRemainderBoundaryCollarLayerFacePeelWitnessData
    (emb := emb) (C := C) (htait := htait) (z := z) (data := data)
    (hzeroBoundary := hzeroBoundary) (horth := horth)

end Mettapedia.GraphTheory.FourColor
