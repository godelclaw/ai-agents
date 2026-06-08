import Mettapedia.GraphTheory.FourColor.PlanarBoundaryFaceIncidence

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- The ambient boundary split of an annulus-shaped boundary-aware plane embedding: the full
ambient boundary support is partitioned into distinguished outer and inner boundary supports. This
is the part of Step 2 geometry that belongs to the embedding itself, before any collar peeling is
chosen. -/
structure PlanarBoundaryAnnulusBoundaryData {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) where
  outerAmbientBoundary : Finset G.edgeSet
  innerAmbientBoundary : Finset G.edgeSet
  houterAmbientBoundaryNonempty : outerAmbientBoundary.Nonempty
  hinnerAmbientBoundaryNonempty : innerAmbientBoundary.Nonempty
  houterAmbientBoundarySubset :
    outerAmbientBoundary ⊆ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces
  hinnerAmbientBoundarySubset :
    innerAmbientBoundary ⊆ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces
  hambientBoundaryCover :
    selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ⊆
      outerAmbientBoundary ∪ innerAmbientBoundary
  hambientBoundaryDisjoint :
    Disjoint outerAmbientBoundary innerAmbientBoundary

theorem PlanarBoundaryAnnulusBoundaryData.ambientBoundary_eq
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryData emb) :
    selectedBoundarySupport emb.faceBoundary emb.faces emb.faces =
      data.outerAmbientBoundary ∪ data.innerAmbientBoundary := by
  apply Finset.Subset.antisymm
  · exact data.hambientBoundaryCover
  · intro e he
    rcases Finset.mem_union.1 he with houter | hinner
    · exact data.houterAmbientBoundarySubset houter
    · exact data.hinnerAmbientBoundarySubset hinner

/-- In an annulus boundary split, every face-boundary edge that is not an interior edge is on one
of the two ambient annulus boundaries.  This is the geometric content behind the
`hboundaryRest` side condition in the source-tied one-collar construction. -/
theorem
    PlanarBoundaryAnnulusBoundaryData.mem_outerAmbientBoundary_union_innerAmbientBoundary_of_mem_faceBoundary_of_not_mem_interiorEdgeSupport
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryData emb) {f : AmbientFace emb.faces}
    {e : G.edgeSet}
    (heFace : e ∈ emb.faceBoundary f.1)
    (heNotInterior : e ∉ interiorEdgeSupport emb.faceBoundary emb.faces) :
    e ∈ data.outerAmbientBoundary ∪ data.innerAmbientBoundary := by
  have heAll : e ∈ emb.faces.biUnion emb.faceBoundary :=
    Finset.mem_biUnion.2 ⟨f.1, f.2, heFace⟩
  have hePartition :
      e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∪
        interiorEdgeSupport emb.faceBoundary emb.faces := by
    rw [←
      biUnion_eq_selectedBoundarySupport_union_interiorEdgeSupport_of_totalIncidenceCount_le_two
        emb.faceBoundary emb.faces (planeEmbeddingWithBoundary_totalIncidenceCount_le_two emb)]
    exact heAll
  rcases Finset.mem_union.1 hePartition with heSelected | heInterior
  · rwa [data.ambientBoundary_eq] at heSelected
  · exact False.elim (heNotInterior heInterior)

theorem PlanarBoundaryAnnulusBoundaryData.selectedBoundarySupport_nonempty
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryData emb) :
    (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces).Nonempty := by
  rcases data.houterAmbientBoundaryNonempty with ⟨e, he⟩
  exact ⟨e, data.houterAmbientBoundarySubset he⟩

theorem PlanarBoundaryAnnulusBoundaryData.totalIncidenceCount_eq_one_of_mem_outerAmbientBoundary
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryData emb) {e : G.edgeSet}
    (he : e ∈ data.outerAmbientBoundary) :
    totalIncidenceCount emb.faceBoundary emb.faces e = 1 := by
  exact (mem_selectedBoundarySupport_iff emb.faceBoundary emb.faces emb.faces).1
    (data.houterAmbientBoundarySubset he) |>.2

theorem PlanarBoundaryAnnulusBoundaryData.totalIncidenceCount_eq_one_of_mem_innerAmbientBoundary
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryData emb) {e : G.edgeSet}
    (he : e ∈ data.innerAmbientBoundary) :
    totalIncidenceCount emb.faceBoundary emb.faces e = 1 := by
  exact (mem_selectedBoundarySupport_iff emb.faceBoundary emb.faces emb.faces).1
    (data.hinnerAmbientBoundarySubset he) |>.2

theorem PlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary_ne_innerAmbientBoundary
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryData emb) :
    data.outerAmbientBoundary ≠ data.innerAmbientBoundary := by
  intro hEq
  rcases data.houterAmbientBoundaryNonempty with ⟨e, he⟩
  have hinner : e ∈ data.innerAmbientBoundary := hEq ▸ he
  exact (Finset.disjoint_left.mp data.hambientBoundaryDisjoint) he hinner

theorem PlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary_disjoint_interiorEdgeSupport
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryData emb) :
    Disjoint data.outerAmbientBoundary
      (interiorEdgeSupport emb.faceBoundary emb.faces) := by
  rw [Finset.disjoint_left]
  intro e heOuter heInterior
  have houter := data.totalIncidenceCount_eq_one_of_mem_outerAmbientBoundary heOuter
  have hinterior :=
    (mem_interiorEdgeSupport_iff emb.faceBoundary emb.faces).1 heInterior |>.2
  omega

theorem PlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary_disjoint_interiorEdgeSupport
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryData emb) :
    Disjoint data.innerAmbientBoundary
      (interiorEdgeSupport emb.faceBoundary emb.faces) := by
  rw [Finset.disjoint_left]
  intro e heInner heInterior
  have hinner := data.totalIncidenceCount_eq_one_of_mem_innerAmbientBoundary heInner
  have hinterior :=
    (mem_interiorEdgeSupport_iff emb.faceBoundary emb.faces).1 heInterior |>.2
  omega

/-- The ambient faces whose boundary meets a prescribed edge set. This is the face-level carrier
for turning an annulus boundary split into actual outer and inner boundary face layers. -/
def ambientFacesMeetingEdgeSet
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} (S : Finset G.edgeSet) :
    Finset (AmbientFace emb.faces) :=
  emb.faces.attach.filter fun f => ∃ e ∈ emb.faceBoundary f.1, e ∈ S

theorem mem_ambientFacesMeetingEdgeSet_iff
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} {S : Finset G.edgeSet}
    {f : AmbientFace emb.faces} :
    f ∈ ambientFacesMeetingEdgeSet (emb := emb) S ↔
      ∃ e ∈ emb.faceBoundary f.1, e ∈ S := by
  simp [ambientFacesMeetingEdgeSet]

theorem ambientFacesMeetingEdgeSet_nonempty_of_nonempty_boundarySubset
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} {S : Finset G.edgeSet}
    (hSnonempty : S.Nonempty)
    (hSsubset : S ⊆ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) :
    (ambientFacesMeetingEdgeSet (emb := emb) S).Nonempty := by
  rcases hSnonempty with ⟨e, he⟩
  have hmem :
      e ∈ emb.faces.biUnion emb.faceBoundary := by
    exact (mem_selectedBoundarySupport_iff emb.faceBoundary emb.faces emb.faces).1
      (hSsubset he) |>.1
  rcases Finset.mem_biUnion.1 hmem with ⟨f, hf, hef⟩
  refine ⟨⟨f, hf⟩, ?_⟩
  exact (mem_ambientFacesMeetingEdgeSet_iff (emb := emb)).2 ⟨e, hef, he⟩

theorem ambientFacesMeetingEdgeSet_union
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (S T : Finset G.edgeSet) :
    ambientFacesMeetingEdgeSet (emb := emb) (S ∪ T) =
      ambientFacesMeetingEdgeSet (emb := emb) S ∪
        ambientFacesMeetingEdgeSet (emb := emb) T := by
  ext f
  constructor
  · intro hf
    rcases (mem_ambientFacesMeetingEdgeSet_iff (emb := emb)).1 hf with ⟨e, hef, heST⟩
    rcases Finset.mem_union.1 heST with hS | hT
    · exact Finset.mem_union.2 <| Or.inl <|
        (mem_ambientFacesMeetingEdgeSet_iff (emb := emb)).2 ⟨e, hef, hS⟩
    · exact Finset.mem_union.2 <| Or.inr <|
        (mem_ambientFacesMeetingEdgeSet_iff (emb := emb)).2 ⟨e, hef, hT⟩
  · intro hf
    rcases Finset.mem_union.1 hf with hS | hT
    · rcases (mem_ambientFacesMeetingEdgeSet_iff (emb := emb)).1 hS with ⟨e, hef, heS⟩
      exact (mem_ambientFacesMeetingEdgeSet_iff (emb := emb)).2
        ⟨e, hef, Finset.mem_union.2 <| Or.inl heS⟩
    · rcases (mem_ambientFacesMeetingEdgeSet_iff (emb := emb)).1 hT with ⟨e, hef, heT⟩
      exact (mem_ambientFacesMeetingEdgeSet_iff (emb := emb)).2
        ⟨e, hef, Finset.mem_union.2 <| Or.inr heT⟩

/-- The ambient faces touching the distinguished outer ambient boundary support. -/
def PlanarBoundaryAnnulusBoundaryData.outerBoundaryFaces
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryData emb) :
    Finset (AmbientFace emb.faces) :=
  ambientFacesMeetingEdgeSet (emb := emb) data.outerAmbientBoundary

/-- The ambient faces touching the distinguished inner ambient boundary support. -/
def PlanarBoundaryAnnulusBoundaryData.innerBoundaryFaces
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryData emb) :
    Finset (AmbientFace emb.faces) :=
  ambientFacesMeetingEdgeSet (emb := emb) data.innerAmbientBoundary

theorem PlanarBoundaryAnnulusBoundaryData.mem_outerBoundaryFaces_iff
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryData emb) {f : AmbientFace emb.faces} :
    f ∈ data.outerBoundaryFaces ↔
      ∃ e ∈ emb.faceBoundary f.1, e ∈ data.outerAmbientBoundary := by
  exact mem_ambientFacesMeetingEdgeSet_iff (emb := emb)

theorem PlanarBoundaryAnnulusBoundaryData.mem_innerBoundaryFaces_iff
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryData emb) {f : AmbientFace emb.faces} :
    f ∈ data.innerBoundaryFaces ↔
      ∃ e ∈ emb.faceBoundary f.1, e ∈ data.innerAmbientBoundary := by
  exact mem_ambientFacesMeetingEdgeSet_iff (emb := emb)

theorem PlanarBoundaryAnnulusBoundaryData.outerBoundaryFaces_nonempty
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryData emb) :
    data.outerBoundaryFaces.Nonempty := by
  exact ambientFacesMeetingEdgeSet_nonempty_of_nonempty_boundarySubset
    (emb := emb) data.houterAmbientBoundaryNonempty data.houterAmbientBoundarySubset

theorem PlanarBoundaryAnnulusBoundaryData.innerBoundaryFaces_nonempty
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryData emb) :
    data.innerBoundaryFaces.Nonempty := by
  exact ambientFacesMeetingEdgeSet_nonempty_of_nonempty_boundarySubset
    (emb := emb) data.hinnerAmbientBoundaryNonempty data.hinnerAmbientBoundarySubset

theorem PlanarBoundaryAnnulusBoundaryData.ambientBoundaryFaces_eq
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryData emb) :
    ambientFacesMeetingEdgeSet (emb := emb)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) =
      data.outerBoundaryFaces ∪ data.innerBoundaryFaces := by
  rw [data.ambientBoundary_eq, ambientFacesMeetingEdgeSet_union]
  rfl

theorem PlanarBoundaryAnnulusBoundaryData.mem_outerBoundaryFaces_or_mem_innerBoundaryFaces_iff
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryData emb) {f : AmbientFace emb.faces} :
    f ∈ data.outerBoundaryFaces ∪ data.innerBoundaryFaces ↔
      ∃ e ∈ emb.faceBoundary f.1,
        e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces := by
  rw [← data.ambientBoundaryFaces_eq]
  exact mem_ambientFacesMeetingEdgeSet_iff (emb := emb)

theorem PlanarBoundaryAnnulusBoundaryData.mem_outerBoundaryFaces_or_mem_innerBoundaryFaces_of_mem_selectedBoundarySupport
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryData emb) {f : AmbientFace emb.faces}
    (hf : ∃ e ∈ emb.faceBoundary f.1,
      e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) :
    f ∈ data.outerBoundaryFaces ∪ data.innerBoundaryFaces :=
  (data.mem_outerBoundaryFaces_or_mem_innerBoundaryFaces_iff).2 hf

/-- Graph-level existence form of the ambient annulus-boundary split. -/
def AdmitsPlanarBoundaryAnnulusBoundaryData (G : SimpleGraph V) : Prop :=
  ∃ emb : PlaneEmbeddingWithBoundary G,
    Nonempty (PlanarBoundaryAnnulusBoundaryData emb)

end Mettapedia.GraphTheory.FourColor
