import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryAnnulusBoundary
import Mettapedia.GraphTheory.FourColor.PlanarBoundaryAnnulusBoundaryConnectivity
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryAnnulusDecomposition
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryAnnulusGeometry
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryCollarPeeling
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryOuterBoundaryRootInteriorDual

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- Constructive Step 2 annulus data over a boundary-aware plane embedding, organized around a
boundary-root BFS-style face-distance stratification. Instead of storing explicit collars and
frontier cycles, this package keeps the annulus boundary split together with a peeled face set, a
witness edge on each peeled face, and a natural-valued face distance that forces every non-witness
remainder edge either onto the ambient annulus boundary or toward a strictly deeper face. -/
structure PlanarBoundaryAnnulusConstruction {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) extends PlanarBoundaryAnnulusBoundaryData emb where
  peelFaces : Finset (AmbientFace emb.faces)
  witnessEdge : AmbientFace emb.faces → G.edgeSet
  faceDistance : AmbientFace emb.faces → ℕ
  hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image witnessEdge
  hwitness : ∀ f ∈ peelFaces, witnessEdge f ∈ emb.faceBoundary f.1
  hrest : ∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase (witnessEdge f),
    e ∈ outerAmbientBoundary ∪ innerAmbientBoundary ∨
      ∃ g ∈ peelFaces, witnessEdge g = e ∧ faceDistance f < faceDistance g

/-- The construction cover is not merely a cardinality condition: if peeled faces avoid the
selected-boundary support, then every interior edge has an incident witness peeled face whose
whole boundary avoids that support. This is the positive invariant negated by forcing-edge
countermodels. -/
theorem PlanarBoundaryAnnulusConstruction.exists_peelFace_witnessEdge_eq_and_faceBoundary_disjoint_selectedBoundarySupport_of_mem_interiorEdgeSupport
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hpeelInterior : ∀ f ∈ data.peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    {e : G.edgeSet} (he : e ∈ interiorEdgeSupport emb.faceBoundary emb.faces) :
    ∃ f : AmbientFace emb.faces,
      f ∈ data.peelFaces ∧
        data.witnessEdge f = e ∧
        e ∈ emb.faceBoundary f.1 ∧
        Disjoint (emb.faceBoundary f.1)
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) := by
  rcases Finset.mem_image.1 (data.hcover he) with ⟨f, hf, hfe⟩
  refine ⟨f, hf, hfe, ?_, hpeelInterior f hf⟩
  simpa [hfe] using data.hwitness f hf

/-- Number of BFS strata in the current annulus construction, obtained from the maximal face
distance among peeled faces. -/
def PlanarBoundaryAnnulusConstruction.numStrata {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb) : ℕ :=
  data.peelFaces.sup data.faceDistance + 1

/-- The faces in BFS stratum `i`: exactly the peeled faces at distance `i`. -/
def PlanarBoundaryAnnulusConstruction.stratumFaces {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb) (i : Fin data.numStrata) :
    Finset (AmbientFace emb.faces) :=
  data.peelFaces.filter fun f => data.faceDistance f = i.1

/-- The concrete ambient faces touching the distinguished outer ambient boundary support. -/
def PlanarBoundaryAnnulusConstruction.outerBoundaryFaces {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb) :
    Finset (AmbientFace emb.faces) :=
  data.toPlanarBoundaryAnnulusBoundaryData.outerBoundaryFaces

/-- The concrete ambient faces touching the distinguished inner ambient boundary support. -/
def PlanarBoundaryAnnulusConstruction.innerBoundaryFaces {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb) :
    Finset (AmbientFace emb.faces) :=
  data.toPlanarBoundaryAnnulusBoundaryData.innerBoundaryFaces

/-- The union of all BFS strata. This is exactly the peeled interior face set. -/
def PlanarBoundaryAnnulusConstruction.strataUnion {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb) :
    Finset (AmbientFace emb.faces) :=
  Finset.univ.biUnion data.stratumFaces

theorem PlanarBoundaryAnnulusConstruction.mem_outerBoundaryFaces_iff {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb) {f : AmbientFace emb.faces} :
    f ∈ data.outerBoundaryFaces ↔
      ∃ e ∈ emb.faceBoundary f.1, e ∈ data.outerAmbientBoundary :=
  data.toPlanarBoundaryAnnulusBoundaryData.mem_outerBoundaryFaces_iff

theorem PlanarBoundaryAnnulusConstruction.mem_innerBoundaryFaces_iff {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb) {f : AmbientFace emb.faces} :
    f ∈ data.innerBoundaryFaces ↔
      ∃ e ∈ emb.faceBoundary f.1, e ∈ data.innerAmbientBoundary :=
  data.toPlanarBoundaryAnnulusBoundaryData.mem_innerBoundaryFaces_iff

theorem PlanarBoundaryAnnulusConstruction.mem_stratumFaces_iff {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb) {i : Fin data.numStrata}
    {f : AmbientFace emb.faces} :
    f ∈ data.stratumFaces i ↔ f ∈ data.peelFaces ∧ data.faceDistance f = i.1 := by
  simp [PlanarBoundaryAnnulusConstruction.stratumFaces]

theorem PlanarBoundaryAnnulusConstruction.strataUnion_subset_peelFaces {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb) :
    data.strataUnion ⊆ data.peelFaces := by
  intro f hf
  rcases Finset.mem_biUnion.1 hf with ⟨i, -, hfi⟩
  exact (data.mem_stratumFaces_iff).1 hfi |>.1

theorem PlanarBoundaryAnnulusConstruction.peelFaces_subset_strataUnion {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb) :
    data.peelFaces ⊆ data.strataUnion := by
  intro f hf
  have hbound : data.faceDistance f < data.numStrata := by
    unfold PlanarBoundaryAnnulusConstruction.numStrata
    exact Nat.lt_succ_of_le (Finset.le_sup hf)
  let i : Fin data.numStrata := ⟨data.faceDistance f, hbound⟩
  refine Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, ?_⟩
  exact (data.mem_stratumFaces_iff).2 ⟨hf, rfl⟩

theorem PlanarBoundaryAnnulusConstruction.strataUnion_eq_peelFaces {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb) :
    data.strataUnion = data.peelFaces := by
  exact Finset.Subset.antisymm data.strataUnion_subset_peelFaces data.peelFaces_subset_strataUnion

/-- The construction cover forces a peeled face as soon as there is an interior edge to cover. -/
theorem PlanarBoundaryAnnulusConstruction.peelFaces_nonempty_of_mem_interiorEdgeSupport
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    {e : G.edgeSet} (he : e ∈ interiorEdgeSupport emb.faceBoundary emb.faces) :
    data.peelFaces.Nonempty := by
  rcases Finset.mem_image.1 (data.hcover he) with ⟨f, hf, _hfe⟩
  exact ⟨f, hf⟩

/-- Nonempty interior-edge support forces a nonempty peeled-face set in any annulus
construction. -/
theorem PlanarBoundaryAnnulusConstruction.peelFaces_nonempty_of_interiorEdgeSupport_nonempty
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hInterior : (interiorEdgeSupport emb.faceBoundary emb.faces).Nonempty) :
    data.peelFaces.Nonempty := by
  rcases hInterior with ⟨e, he⟩
  exact data.peelFaces_nonempty_of_mem_interiorEdgeSupport he

/-- The construction-level strict remainder dependency.  A dependency `f → g` means that
`g`'s selected witness is a non-witness remainder edge on `f`, that edge is not on either ambient
annulus boundary, and the stored face-distance strictly increases from `f` to `g`. -/
def PlanarBoundaryAnnulusConstruction.remainderDependency
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    (f g : AmbientFace emb.faces) : Prop :=
  f ∈ data.peelFaces ∧
    g ∈ data.peelFaces ∧
      data.witnessEdge g ∈ (emb.faceBoundary f.1).erase (data.witnessEdge f) ∧
        data.witnessEdge g ∉ data.outerAmbientBoundary ∪ data.innerAmbientBoundary ∧
          data.faceDistance f < data.faceDistance g

theorem PlanarBoundaryAnnulusConstruction.faceDistance_lt_of_remainderDependency
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb) {f g : AmbientFace emb.faces}
    (hdep : data.remainderDependency f g) :
    data.faceDistance f < data.faceDistance g := by
  exact hdep.2.2.2.2

/-- Every non-boundary remainder produced by `hrest` selects a strict construction dependency. -/
theorem PlanarBoundaryAnnulusConstruction.exists_remainderDependency_of_nonboundary_remainder
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    {f : AmbientFace emb.faces} (hf : f ∈ data.peelFaces)
    {e : G.edgeSet} (he : e ∈ (emb.faceBoundary f.1).erase (data.witnessEdge f))
    (hnotBoundary : e ∉ data.outerAmbientBoundary ∪ data.innerAmbientBoundary) :
    ∃ g : AmbientFace emb.faces,
      data.remainderDependency f g ∧ data.witnessEdge g = e := by
  rcases data.hrest f hf e he with hboundary | ⟨g, hg, hge, hlt⟩
  · exact False.elim (hnotBoundary hboundary)
  · refine ⟨g, ?_, hge⟩
    exact ⟨hf, hg, by simpa [hge] using he, by simpa [hge] using hnotBoundary, hlt⟩

/-- A finite strict construction-dependency chain cannot close. -/
theorem PlanarBoundaryAnnulusConstruction.false_of_remainderDependency_cycle
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    {cycle : List (AmbientFace emb.faces)}
    (hne : cycle ≠ [])
    (hchain : List.IsChain data.remainderDependency cycle)
    (hloop : data.remainderDependency (cycle.getLast hne) (cycle.head hne)) :
    False := by
  have hheightChain :
      List.IsChain (fun f g => data.faceDistance f < data.faceDistance g) cycle := by
    exact hchain.imp (by
      intro f g hdep
      exact data.faceDistance_lt_of_remainderDependency hdep)
  have hloopHeight :
      data.faceDistance (cycle.getLast hne) < data.faceDistance (cycle.head hne) :=
    data.faceDistance_lt_of_remainderDependency hloop
  exact false_of_isChain_height_lt_and_getLast_lt_head data.faceDistance hne
    hheightChain hloopHeight

/-- A nonempty finite peeled set cannot have an outgoing strict remainder dependency from every
peeled face. -/
theorem PlanarBoundaryAnnulusConstruction.false_of_total_remainderDependency
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hne : data.peelFaces.Nonempty)
    (htotal : ∀ f ∈ data.peelFaces,
      ∃ g : AmbientFace emb.faces, data.remainderDependency f g) :
    False := by
  classical
  let heights := data.peelFaces.image data.faceDistance
  have hheights : heights.Nonempty := hne.image data.faceDistance
  rcases Finset.mem_image.1 (Finset.max'_mem heights hheights) with ⟨f, hf, hfmax⟩
  rcases htotal f hf with ⟨g, hdep⟩
  have hg : g ∈ data.peelFaces := hdep.2.1
  have hlt : data.faceDistance f < data.faceDistance g :=
    data.faceDistance_lt_of_remainderDependency hdep
  have hgmax : data.faceDistance g ≤ heights.max' hheights :=
    Finset.le_max' heights (data.faceDistance g) (Finset.mem_image.2 ⟨g, hg, rfl⟩)
  exact (not_lt_of_ge (by simpa [hfmax] using hgmax) hlt).elim

/-- Constructive-facing form of the strict-dependency obstruction: a nonempty construction has a
peeled face with no outgoing strict remainder dependency. -/
theorem PlanarBoundaryAnnulusConstruction.exists_terminal_peelFace_no_remainderDependency
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hne : data.peelFaces.Nonempty) :
    ∃ f ∈ data.peelFaces,
      ∀ g : AmbientFace emb.faces, ¬ data.remainderDependency f g := by
  classical
  by_contra hnone
  have htotal : ∀ f ∈ data.peelFaces,
      ∃ g : AmbientFace emb.faces, data.remainderDependency f g := by
    intro f hf
    by_contra hmissing
    exact hnone ⟨f, hf, by
      intro g hdep
      exact hmissing ⟨g, hdep⟩⟩
  exact data.false_of_total_remainderDependency hne htotal

/-- A peeled face with no outgoing strict construction dependency has only ambient-boundary
non-witness remainder edges. -/
theorem PlanarBoundaryAnnulusConstruction.boundary_remainders_of_no_remainderDependency
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    {f : AmbientFace emb.faces} (hf : f ∈ data.peelFaces)
    (hterminal : ∀ g : AmbientFace emb.faces, ¬ data.remainderDependency f g) :
    ∀ e ∈ (emb.faceBoundary f.1).erase (data.witnessEdge f),
      e ∈ data.outerAmbientBoundary ∪ data.innerAmbientBoundary := by
  intro e he
  rcases data.hrest f hf e he with hboundary | ⟨g, hg, hge, hlt⟩
  · exact hboundary
  · by_contra hnotBoundary
    exact (hterminal g ⟨hf, hg, by simpa [hge] using he,
      by simpa [hge] using hnotBoundary, hlt⟩).elim

/-- For a peeled face, having no outgoing strict construction dependency is equivalent to the
local terminal boundary-break condition. -/
theorem PlanarBoundaryAnnulusConstruction.no_remainderDependency_iff_boundary_remainders
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    {f : AmbientFace emb.faces} (hf : f ∈ data.peelFaces) :
    (∀ g : AmbientFace emb.faces, ¬ data.remainderDependency f g) ↔
      ∀ e ∈ (emb.faceBoundary f.1).erase (data.witnessEdge f),
        e ∈ data.outerAmbientBoundary ∪ data.innerAmbientBoundary := by
  constructor
  · intro hterminal
    exact data.boundary_remainders_of_no_remainderDependency hf hterminal
  · intro hboundary g hdep
    exact hdep.2.2.2.1 (hboundary (data.witnessEdge g) hdep.2.2.1)

/-- Any nonempty BFS-stratified annulus construction has a terminal peeled face: choose a
maximum-distance peeled face, and the strict-descent remainder condition forces every non-witness
remainder on that face to lie on the ambient annulus boundary split. -/
theorem PlanarBoundaryAnnulusConstruction.exists_terminal_peelFace_boundary_remainders
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hne : data.peelFaces.Nonempty) :
    ∃ f ∈ data.peelFaces,
      ∀ e ∈ (emb.faceBoundary f.1).erase (data.witnessEdge f),
        e ∈ data.outerAmbientBoundary ∪ data.innerAmbientBoundary := by
  rcases data.exists_terminal_peelFace_no_remainderDependency hne with ⟨f, hf, hterminal⟩
  exact ⟨f, hf, data.boundary_remainders_of_no_remainderDependency hf hterminal⟩

/-- Terminal boundary-break form using a live interior edge directly. -/
theorem PlanarBoundaryAnnulusConstruction.exists_terminal_peelFace_boundary_remainders_of_mem_interiorEdgeSupport
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    {e : G.edgeSet} (he : e ∈ interiorEdgeSupport emb.faceBoundary emb.faces) :
    ∃ f ∈ data.peelFaces,
      ∀ e' ∈ (emb.faceBoundary f.1).erase (data.witnessEdge f),
        e' ∈ data.outerAmbientBoundary ∪ data.innerAmbientBoundary := by
  exact data.exists_terminal_peelFace_boundary_remainders
    (data.peelFaces_nonempty_of_mem_interiorEdgeSupport he)

/-- Terminal boundary-break form using nonempty interior-edge support. -/
theorem PlanarBoundaryAnnulusConstruction.exists_terminal_peelFace_boundary_remainders_of_interiorEdgeSupport_nonempty
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hInterior : (interiorEdgeSupport emb.faceBoundary emb.faces).Nonempty) :
    ∃ f ∈ data.peelFaces,
      ∀ e ∈ (emb.faceBoundary f.1).erase (data.witnessEdge f),
        e ∈ data.outerAmbientBoundary ∪ data.innerAmbientBoundary := by
  exact data.exists_terminal_peelFace_boundary_remainders
    (data.peelFaces_nonempty_of_interiorEdgeSupport_nonempty hInterior)

theorem
    PlanarBoundaryAnnulusConstruction.outerBoundaryFaces_disjoint_peelFaces_of_hpeelInterior
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hpeelInterior : ∀ f ∈ data.peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) :
    Disjoint data.outerBoundaryFaces data.peelFaces := by
  rw [Finset.disjoint_left]
  intro f hfOuter hfPeel
  rcases (data.mem_outerBoundaryFaces_iff).1 hfOuter with ⟨e, hef, heOuter⟩
  exact (Finset.disjoint_left.mp (hpeelInterior f hfPeel)) hef
    (data.houterAmbientBoundarySubset heOuter)

theorem
    PlanarBoundaryAnnulusConstruction.innerBoundaryFaces_disjoint_peelFaces_of_hpeelInterior
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hpeelInterior : ∀ f ∈ data.peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) :
    Disjoint data.innerBoundaryFaces data.peelFaces := by
  rw [Finset.disjoint_left]
  intro f hfInner hfPeel
  rcases (data.mem_innerBoundaryFaces_iff).1 hfInner with ⟨e, hef, heInner⟩
  exact (Finset.disjoint_left.mp (hpeelInterior f hfPeel)) hef
    (data.hinnerAmbientBoundarySubset heInner)

theorem
    PlanarBoundaryAnnulusConstruction.outerBoundaryFaces_disjoint_innerBoundaryFaces_of_boundaryFaceSeparated
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hboundaryFaceSeparated : ∀ f : AmbientFace emb.faces,
      ¬ ((∃ e ∈ emb.faceBoundary f.1, e ∈ data.outerAmbientBoundary) ∧
          (∃ e ∈ emb.faceBoundary f.1, e ∈ data.innerAmbientBoundary))) :
    Disjoint data.outerBoundaryFaces data.innerBoundaryFaces := by
  rw [Finset.disjoint_left]
  intro f hfOuter hfInner
  exact hboundaryFaceSeparated f
    ⟨(data.mem_outerBoundaryFaces_iff).1 hfOuter, (data.mem_innerBoundaryFaces_iff).1 hfInner⟩

theorem
    PlanarBoundaryAnnulusConstruction.boundaryFaceSeparated_of_outerBoundaryFaces_disjoint_innerBoundaryFaces
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hdisjoint : Disjoint data.outerBoundaryFaces data.innerBoundaryFaces) :
    ∀ f : AmbientFace emb.faces,
      ¬ ((∃ e ∈ emb.faceBoundary f.1, e ∈ data.outerAmbientBoundary) ∧
          (∃ e ∈ emb.faceBoundary f.1, e ∈ data.innerAmbientBoundary)) := by
  intro f hmeet
  rcases hmeet with ⟨houter, hinner⟩
  exact (Finset.disjoint_left.mp hdisjoint)
    ((data.mem_outerBoundaryFaces_iff).2 houter)
    ((data.mem_innerBoundaryFaces_iff).2 hinner)

theorem
    PlanarBoundaryAnnulusConstruction.outerBoundaryFaces_disjoint_innerBoundaryFaces_iff_boundaryFaceSeparated
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb) :
    Disjoint data.outerBoundaryFaces data.innerBoundaryFaces ↔
      (∀ f : AmbientFace emb.faces,
        ¬ ((∃ e ∈ emb.faceBoundary f.1, e ∈ data.outerAmbientBoundary) ∧
            (∃ e ∈ emb.faceBoundary f.1, e ∈ data.innerAmbientBoundary))) := by
  constructor
  · exact
      data.boundaryFaceSeparated_of_outerBoundaryFaces_disjoint_innerBoundaryFaces
  · exact
      data.outerBoundaryFaces_disjoint_innerBoundaryFaces_of_boundaryFaceSeparated

theorem
    PlanarBoundaryAnnulusConstruction.outerBoundaryFaces_disjoint_strataUnion_of_hpeelInterior
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hpeelInterior : ∀ f ∈ data.peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) :
    Disjoint data.outerBoundaryFaces data.strataUnion := by
  rw [data.strataUnion_eq_peelFaces]
  exact data.outerBoundaryFaces_disjoint_peelFaces_of_hpeelInterior hpeelInterior

theorem
    PlanarBoundaryAnnulusConstruction.innerBoundaryFaces_disjoint_strataUnion_of_hpeelInterior
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hpeelInterior : ∀ f ∈ data.peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) :
    Disjoint data.innerBoundaryFaces data.strataUnion := by
  rw [data.strataUnion_eq_peelFaces]
  exact data.innerBoundaryFaces_disjoint_peelFaces_of_hpeelInterior hpeelInterior

theorem
    PlanarBoundaryAnnulusConstruction.faces_subset_outerBoundaryFaces_union_strataUnion_union_innerBoundaryFaces_of_nonPeelBoundary
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hnonPeelBoundary : ∀ f : AmbientFace emb.faces, f ∉ data.peelFaces →
      (∃ e ∈ emb.faceBoundary f.1, e ∈ data.outerAmbientBoundary) ∨
        (∃ e ∈ emb.faceBoundary f.1, e ∈ data.innerAmbientBoundary)) :
    emb.faces.attach ⊆
      data.outerBoundaryFaces ∪ data.strataUnion ∪ data.innerBoundaryFaces := by
  intro f _hf
  by_cases hpeel : f ∈ data.peelFaces
  · have hstrata : f ∈ data.strataUnion := data.peelFaces_subset_strataUnion hpeel
    exact Finset.mem_union.2 <| Or.inl <| Finset.mem_union.2 <| Or.inr hstrata
  · rcases hnonPeelBoundary f hpeel with houter | hinner
    · exact Finset.mem_union.2 <| Or.inl <| Finset.mem_union.2 <| Or.inl <|
        (data.mem_outerBoundaryFaces_iff).2 houter
    · exact Finset.mem_union.2 <| Or.inr <|
        (data.mem_innerBoundaryFaces_iff).2 hinner

theorem
    PlanarBoundaryAnnulusConstruction.faces_subset_outerBoundaryFaces_union_peelFaces_union_innerBoundaryFaces_of_nonPeelBoundary
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hnonPeelBoundary : ∀ f : AmbientFace emb.faces, f ∉ data.peelFaces →
      (∃ e ∈ emb.faceBoundary f.1, e ∈ data.outerAmbientBoundary) ∨
        (∃ e ∈ emb.faceBoundary f.1, e ∈ data.innerAmbientBoundary)) :
    emb.faces.attach ⊆ data.outerBoundaryFaces ∪ data.peelFaces ∪ data.innerBoundaryFaces := by
  simpa [data.strataUnion_eq_peelFaces] using
    data.faces_subset_outerBoundaryFaces_union_strataUnion_union_innerBoundaryFaces_of_nonPeelBoundary
      hnonPeelBoundary

theorem
    PlanarBoundaryAnnulusConstruction.nonPeelBoundary_of_faces_subset_outerBoundaryFaces_union_peelFaces_union_innerBoundaryFaces
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hcover :
      emb.faces.attach ⊆ data.outerBoundaryFaces ∪ data.peelFaces ∪ data.innerBoundaryFaces) :
    ∀ f : AmbientFace emb.faces, f ∉ data.peelFaces →
      (∃ e ∈ emb.faceBoundary f.1, e ∈ data.outerAmbientBoundary) ∨
        (∃ e ∈ emb.faceBoundary f.1, e ∈ data.innerAmbientBoundary) := by
  intro f hfNotPeel
  have hfAttach : f ∈ emb.faces.attach := by
    simp
  rcases Finset.mem_union.1 (hcover hfAttach) with houterOrPeel | hinner
  · rcases Finset.mem_union.1 houterOrPeel with houter | hpeel
    · exact Or.inl <| (data.mem_outerBoundaryFaces_iff).1 houter
    · exact False.elim (hfNotPeel hpeel)
  · exact Or.inr <| (data.mem_innerBoundaryFaces_iff).1 hinner

theorem
    PlanarBoundaryAnnulusConstruction.nonPeelBoundary_of_nonPeelSelectedBoundary
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hselected : ∀ f : AmbientFace emb.faces, f ∉ data.peelFaces →
      ∃ e ∈ emb.faceBoundary f.1,
        e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) :
    ∀ f : AmbientFace emb.faces, f ∉ data.peelFaces →
      (∃ e ∈ emb.faceBoundary f.1, e ∈ data.outerAmbientBoundary) ∨
        (∃ e ∈ emb.faceBoundary f.1, e ∈ data.innerAmbientBoundary) := by
  intro f hfNotPeel
  rcases hselected f hfNotPeel with ⟨e, hef, heSel⟩
  rcases Finset.mem_union.1 (data.hambientBoundaryCover heSel) with houter | hinner
  · exact Or.inl ⟨e, hef, houter⟩
  · exact Or.inr ⟨e, hef, hinner⟩

theorem
    PlanarBoundaryAnnulusConstruction.faces_subset_outerBoundaryFaces_union_strataUnion_union_innerBoundaryFaces_of_nonPeelSelectedBoundary
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hselected : ∀ f : AmbientFace emb.faces, f ∉ data.peelFaces →
      ∃ e ∈ emb.faceBoundary f.1,
        e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) :
    emb.faces.attach ⊆
      data.outerBoundaryFaces ∪ data.strataUnion ∪ data.innerBoundaryFaces := by
  exact
    data.faces_subset_outerBoundaryFaces_union_strataUnion_union_innerBoundaryFaces_of_nonPeelBoundary
      (data.nonPeelBoundary_of_nonPeelSelectedBoundary hselected)

theorem
    PlanarBoundaryAnnulusConstruction.faces_subset_outerBoundaryFaces_union_peelFaces_union_innerBoundaryFaces_of_nonPeelSelectedBoundary
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hselected : ∀ f : AmbientFace emb.faces, f ∉ data.peelFaces →
      ∃ e ∈ emb.faceBoundary f.1,
        e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) :
    emb.faces.attach ⊆ data.outerBoundaryFaces ∪ data.peelFaces ∪ data.innerBoundaryFaces := by
  exact
    data.faces_subset_outerBoundaryFaces_union_peelFaces_union_innerBoundaryFaces_of_nonPeelBoundary
      (data.nonPeelBoundary_of_nonPeelSelectedBoundary hselected)

theorem
    PlanarBoundaryAnnulusConstruction.nonPeelSelectedBoundary_of_faces_subset_outerBoundaryFaces_union_peelFaces_union_innerBoundaryFaces
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hcover :
      emb.faces.attach ⊆ data.outerBoundaryFaces ∪ data.peelFaces ∪ data.innerBoundaryFaces) :
    ∀ f : AmbientFace emb.faces, f ∉ data.peelFaces →
      ∃ e ∈ emb.faceBoundary f.1,
        e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces := by
  intro f hfNotPeel
  have hfAttach : f ∈ emb.faces.attach := by
    simp
  let boundaryData := data.toPlanarBoundaryAnnulusBoundaryData
  rcases Finset.mem_union.1 (hcover hfAttach) with houterOrPeel | hinner
  · rcases Finset.mem_union.1 houterOrPeel with houter | hpeel
    · exact
        (PlanarBoundaryAnnulusBoundaryData.mem_outerBoundaryFaces_or_mem_innerBoundaryFaces_iff
          (data := boundaryData) (f := f)).1
          (Finset.mem_union.2 <| Or.inl houter)
    · exact False.elim (hfNotPeel hpeel)
  · exact
      (PlanarBoundaryAnnulusBoundaryData.mem_outerBoundaryFaces_or_mem_innerBoundaryFaces_iff
        (data := boundaryData) (f := f)).1
        (Finset.mem_union.2 <| Or.inr hinner)

/-- Number of annulus collars obtained by adjoining the outer and inner boundary face layers to
the interior BFS strata. -/
def PlanarBoundaryAnnulusConstruction.numCollars {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb) : ℕ :=
  data.numStrata + 2

/-- Derived collar-face partition from concrete annulus geometry: the outer boundary-adjacent
faces, then the BFS strata, then the inner boundary-adjacent faces. -/
def PlanarBoundaryAnnulusConstruction.collarFaces {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb) (i : Fin data.numCollars) :
    Finset (AmbientFace emb.faces) :=
  if i.1 = 0 then
    data.outerBoundaryFaces
  else if hmid : i.1 - 1 < data.numStrata then
    data.stratumFaces ⟨i.1 - 1, hmid⟩
  else
    data.innerBoundaryFaces

/-- The collar-stage index corresponding to BFS stratum `i`. This is the positive collar whose
faces are exactly the stratum-`i` peeled faces. -/
def PlanarBoundaryAnnulusConstruction.stratumStage {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb) (i : Fin data.numStrata) :
    Fin data.numCollars :=
  ⟨i.1 + 1, by
    unfold PlanarBoundaryAnnulusConstruction.numCollars
    omega⟩

theorem PlanarBoundaryAnnulusConstruction.collarFaces_zero {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb) :
    data.collarFaces ⟨0, by
      unfold PlanarBoundaryAnnulusConstruction.numCollars
      omega⟩ = data.outerBoundaryFaces := by
  simp [PlanarBoundaryAnnulusConstruction.collarFaces]

theorem PlanarBoundaryAnnulusConstruction.collarFaces_succ {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb) (i : Fin data.numStrata) :
    data.collarFaces ⟨i.1 + 1, by
      unfold PlanarBoundaryAnnulusConstruction.numCollars
      omega⟩ = data.stratumFaces i := by
  simp [PlanarBoundaryAnnulusConstruction.collarFaces, i.isLt]

theorem PlanarBoundaryAnnulusConstruction.collarFaces_stratumStage {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb) (i : Fin data.numStrata) :
    data.collarFaces (data.stratumStage i) = data.stratumFaces i := by
  simpa [PlanarBoundaryAnnulusConstruction.stratumStage] using data.collarFaces_succ i

theorem PlanarBoundaryAnnulusConstruction.collarFaces_last {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb) :
    data.collarFaces ⟨data.numStrata + 1, by
      unfold PlanarBoundaryAnnulusConstruction.numCollars
      omega⟩ = data.innerBoundaryFaces := by
  simp [PlanarBoundaryAnnulusConstruction.collarFaces]

theorem PlanarBoundaryAnnulusConstruction.mem_collarFaces_iff {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    {i : Fin data.numCollars} {f : AmbientFace emb.faces} :
    f ∈ data.collarFaces i ↔
      (i.1 = 0 ∧ f ∈ data.outerBoundaryFaces) ∨
        (∃ j : Fin data.numStrata, i.1 = j.1 + 1 ∧ f ∈ data.stratumFaces j) ∨
          (i.1 = data.numStrata + 1 ∧ f ∈ data.innerBoundaryFaces) := by
  unfold PlanarBoundaryAnnulusConstruction.collarFaces
  by_cases h0 : i.1 = 0
  · constructor
    · intro hf
      exact Or.inl ⟨h0, by simpa [h0] using hf⟩
    · intro hf
      rcases hf with ⟨-, hfOuter⟩ | hmid | hlast
      · simpa [h0] using hfOuter
      · rcases hmid with ⟨j, hj, _⟩
        omega
      · omega
  · by_cases hmid : i.1 - 1 < data.numStrata
    · let j : Fin data.numStrata := ⟨i.1 - 1, hmid⟩
      have hi : i.1 = j.1 + 1 := by
        dsimp [j]
        omega
      constructor
      · intro hf
        exact Or.inr <| Or.inl ⟨j, hi, by simpa [h0, hmid, j] using hf⟩
      · intro hf
        rcases hf with hzero | hmid' | hlast
        · omega
        · rcases hmid' with ⟨k, hk, hfk⟩
          have hEq : k = j := by
            apply Fin.ext
            omega
          subst hEq
          simpa [h0, hmid, j] using hfk
        · omega
    · have hlast : i.1 = data.numStrata + 1 := by
        have hi_pos : 0 < i.1 := Nat.pos_of_ne_zero h0
        have hi_lt : i.1 < data.numStrata + 2 := by
          have hi_lt' := i.isLt
          change i.1 < data.numStrata + 2 at hi_lt'
          exact hi_lt'
        have hge : data.numStrata ≤ i.1 - 1 := Nat.le_of_not_lt hmid
        have hle : i.1 - 1 ≤ data.numStrata := by
          omega
        have hEqSub : i.1 - 1 = data.numStrata := le_antisymm hle hge
        calc
          i.1 = Nat.succ (i.1 - 1) := by
            simpa using (Nat.succ_pred_eq_of_pos hi_pos).symm
          _ = data.numStrata + 1 := by
            simp [hEqSub, Nat.succ_eq_add_one]
      constructor
      · intro hf
        exact Or.inr <| Or.inr ⟨hlast, by simpa [h0, hmid, hlast] using hf⟩
      · intro hf
        rcases hf with hzero | hmid' | hlast'
        · omega
        · rcases hmid' with ⟨j, hj, _⟩
          omega
        · rcases hlast' with ⟨_, hfInner⟩
          simpa [h0, hmid, hlast] using hfInner

theorem PlanarBoundaryAnnulusConstruction.stratumFaces_disjoint {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    {i j : Fin data.numStrata} (hij : i ≠ j) :
    Disjoint (data.stratumFaces i) (data.stratumFaces j) := by
  rw [Finset.disjoint_left]
  intro f hfi hfj
  have hfiHeight : data.faceDistance f = i.1 := (data.mem_stratumFaces_iff).1 hfi |>.2
  have hfjHeight : data.faceDistance f = j.1 := (data.mem_stratumFaces_iff).1 hfj |>.2
  apply hij
  exact Fin.ext (hfiHeight.symm.trans hfjHeight)

theorem PlanarBoundaryAnnulusConstruction.stratumFaces_subset_peelFaces {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb) (i : Fin data.numStrata) :
    data.stratumFaces i ⊆ data.peelFaces := by
  intro f hf
  exact (data.mem_stratumFaces_iff).1 hf |>.1

theorem
    PlanarBoundaryAnnulusConstruction.outerBoundaryFaces_disjoint_stratumFaces_of_hpeelInterior
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hpeelInterior : ∀ f ∈ data.peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (i : Fin data.numStrata) :
    Disjoint data.outerBoundaryFaces (data.stratumFaces i) := by
  rw [Finset.disjoint_left]
  intro f hfOuter hfStratum
  exact (Finset.disjoint_left.mp
    (data.outerBoundaryFaces_disjoint_peelFaces_of_hpeelInterior hpeelInterior))
      hfOuter (data.stratumFaces_subset_peelFaces i hfStratum)

theorem
    PlanarBoundaryAnnulusConstruction.innerBoundaryFaces_disjoint_stratumFaces_of_hpeelInterior
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hpeelInterior : ∀ f ∈ data.peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (i : Fin data.numStrata) :
    Disjoint data.innerBoundaryFaces (data.stratumFaces i) := by
  rw [Finset.disjoint_left]
  intro f hfInner hfStratum
  exact (Finset.disjoint_left.mp
    (data.innerBoundaryFaces_disjoint_peelFaces_of_hpeelInterior hpeelInterior))
      hfInner (data.stratumFaces_subset_peelFaces i hfStratum)

theorem
    PlanarBoundaryAnnulusConstruction.collarFaces_cover_of_facePartition
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hnonPeelBoundary : ∀ f : AmbientFace emb.faces, f ∉ data.peelFaces →
      (∃ e ∈ emb.faceBoundary f.1, e ∈ data.outerAmbientBoundary) ∨
        (∃ e ∈ emb.faceBoundary f.1, e ∈ data.innerAmbientBoundary)) :
    emb.faces.attach ⊆ Finset.univ.biUnion data.collarFaces := by
  intro f hf
  have hpartition :=
    data.faces_subset_outerBoundaryFaces_union_strataUnion_union_innerBoundaryFaces_of_nonPeelBoundary
      hnonPeelBoundary hf
  rcases Finset.mem_union.1 hpartition with houterOrStrata | hinner
  · rcases Finset.mem_union.1 houterOrStrata with houter | hstrata
    · refine Finset.mem_biUnion.2 ⟨⟨0, by
        unfold PlanarBoundaryAnnulusConstruction.numCollars
        omega⟩, Finset.mem_univ _, ?_⟩
      simpa [data.collarFaces_zero] using houter
    · rcases Finset.mem_biUnion.1 hstrata with ⟨i, -, hfi⟩
      refine Finset.mem_biUnion.2 ⟨⟨i.1 + 1, by
        unfold PlanarBoundaryAnnulusConstruction.numCollars
        omega⟩, Finset.mem_univ _, ?_⟩
      simpa [data.collarFaces_succ i] using hfi
  · refine Finset.mem_biUnion.2 ⟨⟨data.numStrata + 1, by
      unfold PlanarBoundaryAnnulusConstruction.numCollars
      omega⟩, Finset.mem_univ _, ?_⟩
    simpa [data.collarFaces_last] using hinner

theorem
    PlanarBoundaryAnnulusConstruction.collarFaces_disjoint_of_facePartition
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hpeelInterior : ∀ f ∈ data.peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hboundaryFaceSeparated : ∀ f : AmbientFace emb.faces,
      ¬ ((∃ e ∈ emb.faceBoundary f.1, e ∈ data.outerAmbientBoundary) ∧
          (∃ e ∈ emb.faceBoundary f.1, e ∈ data.innerAmbientBoundary))) :
    ∀ {i j : Fin data.numCollars}, i ≠ j →
      Disjoint (data.collarFaces i) (data.collarFaces j) := by
  intro i j hij
  rw [Finset.disjoint_left]
  intro f hfi hfj
  rcases (data.mem_collarFaces_iff).1 hfi with hOuter | hMid | hInner
  · rcases hOuter with ⟨hi0, hfOuter⟩
    rcases (data.mem_collarFaces_iff).1 hfj with hOuter' | hMid' | hInner'
    · rcases hOuter' with ⟨hj0, _⟩
      apply hij
      exact Fin.ext (by omega)
    · rcases hMid' with ⟨k, hk, hfStratum⟩
      exact (Finset.disjoint_left.mp
        (data.outerBoundaryFaces_disjoint_stratumFaces_of_hpeelInterior hpeelInterior k))
          hfOuter hfStratum
    · rcases hInner' with ⟨_, hfInner⟩
      exact (Finset.disjoint_left.mp
        (data.outerBoundaryFaces_disjoint_innerBoundaryFaces_of_boundaryFaceSeparated
          hboundaryFaceSeparated))
          hfOuter hfInner
  · rcases hMid with ⟨k, hk, hfStratum⟩
    rcases (data.mem_collarFaces_iff).1 hfj with hOuter' | hMid' | hInner'
    · rcases hOuter' with ⟨_, hfOuter⟩
      exact (Finset.disjoint_left.mp
        ((data.outerBoundaryFaces_disjoint_stratumFaces_of_hpeelInterior hpeelInterior k).symm))
          hfStratum hfOuter
    · rcases hMid' with ⟨l, hl, hfStratum'⟩
      have hkl : k ≠ l := by
        intro hEq
        apply hij
        exact Fin.ext (by omega)
      exact (Finset.disjoint_left.mp (data.stratumFaces_disjoint hkl)) hfStratum hfStratum'
    · rcases hInner' with ⟨_, hfInner⟩
      exact (Finset.disjoint_left.mp
        ((data.innerBoundaryFaces_disjoint_stratumFaces_of_hpeelInterior hpeelInterior k).symm))
          hfStratum hfInner
  · rcases hInner with ⟨hiLast, hfInner⟩
    rcases (data.mem_collarFaces_iff).1 hfj with hOuter' | hMid' | hInner'
    · rcases hOuter' with ⟨_, hfOuter⟩
      exact (Finset.disjoint_left.mp
        ((data.outerBoundaryFaces_disjoint_innerBoundaryFaces_of_boundaryFaceSeparated
          hboundaryFaceSeparated).symm))
          hfInner hfOuter
    · rcases hMid' with ⟨k, hk, hfStratum⟩
      exact (Finset.disjoint_left.mp
        (data.innerBoundaryFaces_disjoint_stratumFaces_of_hpeelInterior hpeelInterior k))
          hfInner hfStratum
    · rcases hInner' with ⟨hjLast, _⟩
      apply hij
      exact Fin.ext (by omega)

/-- The surviving face set after removing the first `i` derived annulus collars. -/
def PlanarBoundaryAnnulusConstruction.currentFaces {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb) (i : Fin data.numCollars) :
    Finset (AmbientFace emb.faces) :=
  annulusCurrentFaces data.collarFaces i

/-- The relative boundary of the current surviving face set, computed in the ambient attached-face
model. -/
def PlanarBoundaryAnnulusConstruction.currentBoundary {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb) (i : Fin data.numCollars) :
    Finset G.edgeSet :=
  relativeBoundarySupport
    (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)
    (data.currentFaces i)

/-- The outer frontier of the current surviving face set, obtained by removing the distinguished
inner ambient boundary from the full current relative boundary. -/
def PlanarBoundaryAnnulusConstruction.currentOuterBoundary {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb) (i : Fin data.numCollars) :
    Finset G.edgeSet :=
  data.currentBoundary i \ data.innerAmbientBoundary

theorem PlanarBoundaryAnnulusConstruction.currentFaces_eq_currentFaces_succ_of_collarFaces_eq_empty
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    {i : Fin data.numCollars} (hi : i.1 + 1 < data.numCollars)
    (hempty : data.collarFaces i = ∅) :
    data.currentFaces i = data.currentFaces ⟨i.1 + 1, hi⟩ := by
  calc
    data.currentFaces i = data.collarFaces i ∪ laterLayerFaces data.collarFaces i := by
      rfl
    _ = laterLayerFaces data.collarFaces i := by simp [hempty]
    _ = data.collarFaces ⟨i.1 + 1, hi⟩ ∪ laterLayerFaces data.collarFaces ⟨i.1 + 1, hi⟩ := by
      rw [laterLayerFaces_eq_collarFaces_union_laterLayerFaces_next data.collarFaces i hi]
    _ = data.currentFaces ⟨i.1 + 1, hi⟩ := by
      rfl

theorem PlanarBoundaryAnnulusConstruction.currentBoundary_eq_currentBoundary_succ_of_collarFaces_eq_empty
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    {i : Fin data.numCollars} (hi : i.1 + 1 < data.numCollars)
    (hempty : data.collarFaces i = ∅) :
    data.currentBoundary i = data.currentBoundary ⟨i.1 + 1, hi⟩ := by
  simp [PlanarBoundaryAnnulusConstruction.currentBoundary,
    data.currentFaces_eq_currentFaces_succ_of_collarFaces_eq_empty hi hempty]

theorem
    PlanarBoundaryAnnulusConstruction.currentOuterBoundary_eq_currentOuterBoundary_succ_of_collarFaces_eq_empty
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    {i : Fin data.numCollars} (hi : i.1 + 1 < data.numCollars)
    (hempty : data.collarFaces i = ∅) :
    data.currentOuterBoundary i = data.currentOuterBoundary ⟨i.1 + 1, hi⟩ := by
  simp [PlanarBoundaryAnnulusConstruction.currentOuterBoundary,
    data.currentBoundary_eq_currentBoundary_succ_of_collarFaces_eq_empty hi hempty]

theorem PlanarBoundaryAnnulusConstruction.mem_currentFaces_iff {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    {i : Fin data.numCollars} {f : AmbientFace emb.faces} :
    f ∈ data.currentFaces i ↔
      f ∈ data.collarFaces i ∨
        ∃ j : Fin data.numCollars, i < j ∧ f ∈ data.collarFaces j := by
  unfold PlanarBoundaryAnnulusConstruction.currentFaces annulusCurrentFaces
  constructor
  · intro hf
    rcases Finset.mem_union.1 hf with hnow | hlater
    · exact Or.inl hnow
    · rcases (mem_laterLayerFaces_iff data.collarFaces i).1 hlater with ⟨j, hij, hj⟩
      exact Or.inr ⟨j, hij, hj⟩
  · intro hf
    rcases hf with hnow | ⟨j, hij, hj⟩
    · exact Finset.mem_union.2 <| Or.inl hnow
    · exact Finset.mem_union.2 <| Or.inr <|
        (mem_laterLayerFaces_iff data.collarFaces i).2 ⟨j, hij, hj⟩

theorem PlanarBoundaryAnnulusConstruction.currentFaces_subset_currentFaces_of_lt
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb) {i j : Fin data.numCollars}
    (hij : i < j) :
    data.currentFaces j ⊆ data.currentFaces i := by
  intro f hf
  rcases (data.mem_currentFaces_iff (i := j)).1 hf with hnow | ⟨k, hjk, hk⟩
  · exact (data.mem_currentFaces_iff (i := i)).2 <| Or.inr ⟨j, hij, hnow⟩
  · exact (data.mem_currentFaces_iff (i := i)).2 <| Or.inr ⟨k, lt_trans hij hjk, hk⟩

theorem PlanarBoundaryAnnulusConstruction.stratumFaces_subset_strataUnion {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb) (i : Fin data.numStrata) :
    data.stratumFaces i ⊆ data.strataUnion := by
  intro f hf
  exact Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hf⟩

theorem PlanarBoundaryAnnulusConstruction.currentFaces_subset_faces {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb) (i : Fin data.numCollars) :
    data.currentFaces i ⊆ emb.faces.attach := by
  intro f _hf
  simp

theorem PlanarBoundaryAnnulusConstruction.currentFaces_zero_eq_collarFacesUnion
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb) :
    data.currentFaces ⟨0, by
      unfold PlanarBoundaryAnnulusConstruction.numCollars
      omega⟩ = Finset.univ.biUnion data.collarFaces := by
  let i0 : Fin data.numCollars := ⟨0, by
    unfold PlanarBoundaryAnnulusConstruction.numCollars
    omega⟩
  ext f
  constructor
  · intro hf
    rcases (data.mem_currentFaces_iff).1 hf with hnow | ⟨j, _, hj⟩
    · exact Finset.mem_biUnion.2 ⟨i0, Finset.mem_univ _, hnow⟩
    · exact Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, hj⟩
  · intro hf
    rcases Finset.mem_biUnion.1 hf with ⟨j, _, hj⟩
    by_cases hEq : j = i0
    · subst hEq
      exact (data.mem_currentFaces_iff).2 <| Or.inl hj
    · have hjPos : 0 < j.1 := by
        have hne : j.1 ≠ 0 := by
          intro hzero
          apply hEq
          exact Fin.ext hzero
        omega
      exact (data.mem_currentFaces_iff).2 <| Or.inr ⟨j, by simpa using hjPos, hj⟩

theorem PlanarBoundaryAnnulusConstruction.currentFaces_zero_eq_faces_of_facePartition
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hnonPeelBoundary : ∀ f : AmbientFace emb.faces, f ∉ data.peelFaces →
      (∃ e ∈ emb.faceBoundary f.1, e ∈ data.outerAmbientBoundary) ∨
        (∃ e ∈ emb.faceBoundary f.1, e ∈ data.innerAmbientBoundary)) :
    data.currentFaces ⟨0, by
      unfold PlanarBoundaryAnnulusConstruction.numCollars
      omega⟩ = emb.faces.attach := by
  apply Finset.Subset.antisymm
  · exact data.currentFaces_subset_faces ⟨0, by
      unfold PlanarBoundaryAnnulusConstruction.numCollars
      omega⟩
  · intro f hf
    have hcover := data.collarFaces_cover_of_facePartition hnonPeelBoundary hf
    rw [← data.currentFaces_zero_eq_collarFacesUnion] at hcover
    exact hcover

theorem PlanarBoundaryAnnulusConstruction.innerBoundaryFaces_subset_currentFaces
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb) (i : Fin data.numCollars) :
    data.innerBoundaryFaces ⊆ data.currentFaces i := by
  let ilast : Fin data.numCollars := ⟨data.numStrata + 1, by
    unfold PlanarBoundaryAnnulusConstruction.numCollars
    omega⟩
  intro f hfInner
  have hlast : f ∈ data.collarFaces ilast := by
    simpa [ilast, data.collarFaces_last] using hfInner
  by_cases hEq : i = ilast
  · subst hEq
    exact (data.mem_currentFaces_iff).2 <| Or.inl hlast
  · have hiLast : i < ilast := by
      have hiLt : i.1 < data.numStrata + 2 := by
        change i.1 < data.numStrata + 2
        exact i.isLt
      have hne : i.1 ≠ data.numStrata + 1 := by
        intro hiEq
        apply hEq
        exact Fin.ext hiEq
      have hiLastNat : i.1 < ilast.1 := by
        dsimp [ilast]
        omega
      exact hiLastNat
    exact (data.mem_currentFaces_iff).2 <| Or.inr ⟨ilast, hiLast, hlast⟩

theorem PlanarBoundaryAnnulusConstruction.currentFaces_nonempty
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb) (i : Fin data.numCollars) :
    (data.currentFaces i).Nonempty := by
  rcases data.toPlanarBoundaryAnnulusBoundaryData.innerBoundaryFaces_nonempty with ⟨f, hf⟩
  exact ⟨f, data.innerBoundaryFaces_subset_currentFaces i hf⟩

theorem
    PlanarBoundaryAnnulusConstruction.currentFaces_subset_strataUnion_union_innerBoundaryFaces_of_pos
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    {i : Fin data.numCollars} (hi : 0 < i.1) :
    data.currentFaces i ⊆ data.strataUnion ∪ data.innerBoundaryFaces := by
  intro f hf
  rcases (data.mem_currentFaces_iff).1 hf with hnow | ⟨j, hij, hj⟩
  · rcases (data.mem_collarFaces_iff).1 hnow with hzero | hmid | hlast
    · rcases hzero with ⟨hiZero, _⟩
      omega
    · rcases hmid with ⟨k, _, hk⟩
      exact Finset.mem_union.2 <| Or.inl <| data.stratumFaces_subset_strataUnion k hk
    · exact Finset.mem_union.2 <| Or.inr hlast.2
  · rcases (data.mem_collarFaces_iff).1 hj with hzero | hmid | hlast
    · rcases hzero with ⟨hjZero, _⟩
      omega
    · rcases hmid with ⟨k, _, hk⟩
      exact Finset.mem_union.2 <| Or.inl <| data.stratumFaces_subset_strataUnion k hk
    · exact Finset.mem_union.2 <| Or.inr hlast.2

theorem
    PlanarBoundaryAnnulusConstruction.faceBoundary_disjoint_outerAmbientBoundary_of_mem_innerBoundaryFaces_of_boundaryFaceSeparated
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hboundaryFaceSeparated : ∀ f : AmbientFace emb.faces,
      ¬ ((∃ e ∈ emb.faceBoundary f.1, e ∈ data.outerAmbientBoundary) ∧
          (∃ e ∈ emb.faceBoundary f.1, e ∈ data.innerAmbientBoundary)))
    {f : AmbientFace emb.faces} (hfInner : f ∈ data.innerBoundaryFaces) :
    Disjoint (emb.faceBoundary f.1) data.outerAmbientBoundary := by
  rw [Finset.disjoint_left]
  intro e hef heOuter
  exact hboundaryFaceSeparated f
    ⟨⟨e, hef, heOuter⟩, (data.mem_innerBoundaryFaces_iff).1 hfInner⟩

theorem
    PlanarBoundaryAnnulusConstruction.faceBoundary_disjoint_outerAmbientBoundary_of_mem_currentFaces_of_pos
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hpeelInterior : ∀ f ∈ data.peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hboundaryFaceSeparated : ∀ f : AmbientFace emb.faces,
      ¬ ((∃ e ∈ emb.faceBoundary f.1, e ∈ data.outerAmbientBoundary) ∧
          (∃ e ∈ emb.faceBoundary f.1, e ∈ data.innerAmbientBoundary)))
    {i : Fin data.numCollars} (hi : 0 < i.1)
    {f : AmbientFace emb.faces} (hf : f ∈ data.currentFaces i) :
    Disjoint (emb.faceBoundary f.1) data.outerAmbientBoundary := by
  have hclass :=
    data.currentFaces_subset_strataUnion_union_innerBoundaryFaces_of_pos hi hf
  rcases Finset.mem_union.1 hclass with hstrata | hinner
  · rw [data.strataUnion_eq_peelFaces] at hstrata
    rw [Finset.disjoint_left]
    intro e hef heOuter
    exact (Finset.disjoint_left.mp (hpeelInterior f hstrata)) hef
      (data.houterAmbientBoundarySubset heOuter)
  · exact data.faceBoundary_disjoint_outerAmbientBoundary_of_mem_innerBoundaryFaces_of_boundaryFaceSeparated
      hboundaryFaceSeparated hinner

theorem PlanarBoundaryAnnulusConstruction.innerAmbientBoundary_subset_currentBoundary
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb) (i : Fin data.numCollars) :
    data.innerAmbientBoundary ⊆ data.currentBoundary i := by
  intro e heInner
  have hboundary : e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces :=
    data.hinnerAmbientBoundarySubset heInner
  have hboundaryAmbient :
      e ∈ selectedBoundarySupport
        (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)
        emb.faces.attach emb.faces.attach := by
    simpa [selectedBoundarySupport_ambientFaceBoundary_eq
      (faceBoundary := emb.faceBoundary) (allFaces := emb.faces)] using hboundary
  have hfaceSupport : e ∈ emb.faces.biUnion emb.faceBoundary :=
    (mem_selectedBoundarySupport_iff emb.faceBoundary emb.faces emb.faces).1 hboundary |>.1
  rcases Finset.mem_biUnion.1 hfaceSupport with ⟨f, hf, hef⟩
  let af : AmbientFace emb.faces := ⟨f, hf⟩
  have hafInner : af ∈ data.innerBoundaryFaces := by
    exact (data.mem_innerBoundaryFaces_iff).2 ⟨e, by simpa [af] using hef, heInner⟩
  have hafCurrent : af ∈ data.currentFaces i :=
    data.innerBoundaryFaces_subset_currentFaces i hafInner
  have hcurrentSupport :
      e ∈ (data.currentFaces i).biUnion
        (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary) := by
    exact Finset.mem_biUnion.2 ⟨af, hafCurrent, by simpa [ambientFaceBoundary, af] using hef⟩
  exact mem_relativeBoundarySupport_of_mem_selectedBoundarySupport_of_mem_biUnion_of_subset
    (faceBoundary := ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)
    (allFaces := emb.faces.attach) (S := data.currentFaces i)
    (data.currentFaces_subset_faces i) hboundaryAmbient hcurrentSupport

theorem PlanarBoundaryAnnulusConstruction.currentBoundary_zero_eq_ambientBoundary_of_facePartition
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hnonPeelBoundary : ∀ f : AmbientFace emb.faces, f ∉ data.peelFaces →
      (∃ e ∈ emb.faceBoundary f.1, e ∈ data.outerAmbientBoundary) ∨
        (∃ e ∈ emb.faceBoundary f.1, e ∈ data.innerAmbientBoundary)) :
    data.currentBoundary ⟨0, by
      unfold PlanarBoundaryAnnulusConstruction.numCollars
      omega⟩ = data.outerAmbientBoundary ∪ data.innerAmbientBoundary := by
  calc
    data.currentBoundary ⟨0, by
        unfold PlanarBoundaryAnnulusConstruction.numCollars
        omega⟩ =
      relativeBoundarySupport
        (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)
        (data.currentFaces ⟨0, by
          unfold PlanarBoundaryAnnulusConstruction.numCollars
          omega⟩) := by
          rfl
    _ =
      relativeBoundarySupport
        (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)
        emb.faces.attach := by
          rw [data.currentFaces_zero_eq_faces_of_facePartition hnonPeelBoundary]
    _ =
      selectedBoundarySupport
        (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)
        emb.faces.attach emb.faces.attach := by
          simpa using
            relativeBoundarySupport_eq_selectedBoundarySupport
              (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)
              emb.faces.attach
    _ = selectedBoundarySupport emb.faceBoundary emb.faces emb.faces := by
          rw [selectedBoundarySupport_ambientFaceBoundary_eq
            (faceBoundary := emb.faceBoundary) (allFaces := emb.faces)]
    _ = data.outerAmbientBoundary ∪ data.innerAmbientBoundary := data.ambientBoundary_eq

theorem PlanarBoundaryAnnulusConstruction.outerAmbientBoundary_disjoint_currentBoundary_of_pos
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hpeelInterior : ∀ f ∈ data.peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hboundaryFaceSeparated : ∀ f : AmbientFace emb.faces,
      ¬ ((∃ e ∈ emb.faceBoundary f.1, e ∈ data.outerAmbientBoundary) ∧
          (∃ e ∈ emb.faceBoundary f.1, e ∈ data.innerAmbientBoundary)))
    {i : Fin data.numCollars} (hi : 0 < i.1) :
    Disjoint data.outerAmbientBoundary (data.currentBoundary i) := by
  rw [Finset.disjoint_left]
  intro e heOuter heCurrent
  rcases (mem_relativeBoundarySupport_iff
      (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)
      (data.currentFaces i)).1 heCurrent with ⟨hmem, _⟩
  rcases Finset.mem_biUnion.1 hmem with ⟨f, hfCurrent, hef⟩
  exact (Finset.disjoint_left.mp
    (data.faceBoundary_disjoint_outerAmbientBoundary_of_mem_currentFaces_of_pos
      hpeelInterior hboundaryFaceSeparated hi hfCurrent))
      (by simpa [ambientFaceBoundary] using hef) heOuter

theorem
    PlanarBoundaryAnnulusConstruction.currentBoundary_subset_interiorEdgeSupport_union_innerAmbientBoundary_of_pos
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hpeelInterior : ∀ f ∈ data.peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hboundaryFaceSeparated : ∀ f : AmbientFace emb.faces,
      ¬ ((∃ e ∈ emb.faceBoundary f.1, e ∈ data.outerAmbientBoundary) ∧
          (∃ e ∈ emb.faceBoundary f.1, e ∈ data.innerAmbientBoundary)))
    {i : Fin data.numCollars} (hi : 0 < i.1) :
    data.currentBoundary i ⊆
      interiorEdgeSupport emb.faceBoundary emb.faces ∪ data.innerAmbientBoundary := by
  intro e heCurrent
  have hmem :
      e ∈ (data.currentFaces i).biUnion
        (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary) :=
    (mem_relativeBoundarySupport_iff
      (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)
      (data.currentFaces i)).1 heCurrent |>.1
  rcases Finset.mem_biUnion.1 hmem with ⟨f, hfCurrent, hef⟩
  have hmemAll :
      e ∈ emb.faces.attach.biUnion
        (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary) := by
    exact Finset.mem_biUnion.2 ⟨f, data.currentFaces_subset_faces i hfCurrent, hef⟩
  have hallAmbient :
      ∀ e,
        totalIncidenceCount
            (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)
            emb.faces.attach e ≤ 2 := by
    intro e
    rw [totalIncidenceCount_ambientFaceBoundary_eq
      (faceBoundary := emb.faceBoundary) (allFaces := emb.faces)]
    exact planeEmbeddingWithBoundary_totalIncidenceCount_le_two emb e
  have hsupport :
      e ∈ selectedBoundarySupport
            (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)
            emb.faces.attach emb.faces.attach ∪
          interiorEdgeSupport
            (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)
            emb.faces.attach := by
    rw [← biUnion_eq_selectedBoundarySupport_union_interiorEdgeSupport_of_totalIncidenceCount_le_two
      (faceBoundary := ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)
      (allFaces := emb.faces.attach) hallAmbient]
    exact hmemAll
  rcases Finset.mem_union.1 hsupport with hboundary | hinterior
  · have hboundary' : e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces := by
      simpa [selectedBoundarySupport_ambientFaceBoundary_eq
        (faceBoundary := emb.faceBoundary) (allFaces := emb.faces)] using hboundary
    have hambient : e ∈ data.outerAmbientBoundary ∪ data.innerAmbientBoundary :=
      data.hambientBoundaryCover hboundary'
    rcases Finset.mem_union.1 hambient with houter | hinner
    · exact False.elim <|
        (Finset.disjoint_left.mp
          (data.outerAmbientBoundary_disjoint_currentBoundary_of_pos
            hpeelInterior hboundaryFaceSeparated hi))
          houter heCurrent
    · exact Finset.mem_union.2 <| Or.inr hinner
  · exact Finset.mem_union.2 <| Or.inl <| by
      simpa [interiorEdgeSupport_ambientFaceBoundary_eq
        (faceBoundary := emb.faceBoundary) (allFaces := emb.faces)] using hinterior

theorem PlanarBoundaryAnnulusConstruction.currentOuterBoundary_zero_eq_outerAmbientBoundary_of_facePartition
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hnonPeelBoundary : ∀ f : AmbientFace emb.faces, f ∉ data.peelFaces →
      (∃ e ∈ emb.faceBoundary f.1, e ∈ data.outerAmbientBoundary) ∨
        (∃ e ∈ emb.faceBoundary f.1, e ∈ data.innerAmbientBoundary)) :
    data.currentOuterBoundary ⟨0, by
      unfold PlanarBoundaryAnnulusConstruction.numCollars
      omega⟩ = data.outerAmbientBoundary := by
  ext e
  constructor
  · intro he
    have hmem :
        e ∈ data.currentBoundary ⟨0, by
          unfold PlanarBoundaryAnnulusConstruction.numCollars
          omega⟩ := (Finset.mem_sdiff.1 he).1
    rw [data.currentBoundary_zero_eq_ambientBoundary_of_facePartition hnonPeelBoundary] at hmem
    rcases Finset.mem_union.1 hmem with houter | hinner
    · exact houter
    · exact False.elim ((Finset.mem_sdiff.1 he).2 hinner)
  · intro he
    refine Finset.mem_sdiff.2 ?_
    constructor
    · rw [data.currentBoundary_zero_eq_ambientBoundary_of_facePartition hnonPeelBoundary]
      exact Finset.mem_union.2 <| Or.inl he
    · intro hinner
      exact (Finset.disjoint_left.mp data.hambientBoundaryDisjoint) he hinner

theorem PlanarBoundaryAnnulusConstruction.currentOuterBoundary_subset_interiorEdgeSupport_of_pos
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hpeelInterior : ∀ f ∈ data.peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hboundaryFaceSeparated : ∀ f : AmbientFace emb.faces,
      ¬ ((∃ e ∈ emb.faceBoundary f.1, e ∈ data.outerAmbientBoundary) ∧
          (∃ e ∈ emb.faceBoundary f.1, e ∈ data.innerAmbientBoundary)))
    {i : Fin data.numCollars} (hi : 0 < i.1) :
    data.currentOuterBoundary i ⊆ interiorEdgeSupport emb.faceBoundary emb.faces := by
  intro e he
  rcases Finset.mem_union.1
      (data.currentBoundary_subset_interiorEdgeSupport_union_innerAmbientBoundary_of_pos
        hpeelInterior hboundaryFaceSeparated hi (Finset.mem_sdiff.1 he).1) with
    hinterior | hinner
  · exact hinterior
  · exact False.elim ((Finset.mem_sdiff.1 he).2 hinner)

theorem PlanarBoundaryAnnulusConstruction.outerAmbientBoundary_disjoint_currentOuterBoundary_of_pos
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hpeelInterior : ∀ f ∈ data.peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hboundaryFaceSeparated : ∀ f : AmbientFace emb.faces,
      ¬ ((∃ e ∈ emb.faceBoundary f.1, e ∈ data.outerAmbientBoundary) ∧
          (∃ e ∈ emb.faceBoundary f.1, e ∈ data.innerAmbientBoundary)))
    {i : Fin data.numCollars} (hi : 0 < i.1) :
    Disjoint data.outerAmbientBoundary (data.currentOuterBoundary i) := by
  rw [Finset.disjoint_left]
  intro e heOuter heCurrent
  exact (Finset.disjoint_left.mp data.outerAmbientBoundary_disjoint_interiorEdgeSupport)
    heOuter
    (data.currentOuterBoundary_subset_interiorEdgeSupport_of_pos
      hpeelInterior hboundaryFaceSeparated hi heCurrent)

theorem
    PlanarBoundaryAnnulusConstruction.currentOuterBoundary_eq_empty_of_interiorEdgeSupport_eq_empty_of_pos
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hpeelInterior : ∀ f ∈ data.peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hboundaryFaceSeparated : ∀ f : AmbientFace emb.faces,
      ¬ ((∃ e ∈ emb.faceBoundary f.1, e ∈ data.outerAmbientBoundary) ∧
          (∃ e ∈ emb.faceBoundary f.1, e ∈ data.innerAmbientBoundary)))
    {i : Fin data.numCollars} (hi : 0 < i.1)
    (hnoInterior : interiorEdgeSupport emb.faceBoundary emb.faces = ∅) :
    data.currentOuterBoundary i = ∅ := by
  ext e
  constructor
  · intro he
    have hInterior :
        e ∈ interiorEdgeSupport emb.faceBoundary emb.faces :=
      data.currentOuterBoundary_subset_interiorEdgeSupport_of_pos
        hpeelInterior hboundaryFaceSeparated hi he
    simp [hnoInterior] at hInterior
  · intro he
    simp at he

/-- Concrete geometric precursor to the abstract annulus face-layer data: the collar partition is
not postulated but derived from outer-boundary faces, BFS strata, and inner-boundary faces. The
remaining assumptions are exactly the relative-boundary facts still needed to lower to the
paper-facing annulus decomposition. -/
structure PlanarBoundaryAnnulusConstructionFaceLayerData {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) where
  construction : PlanarBoundaryAnnulusConstruction emb
  hpeelInterior : ∀ f ∈ construction.peelFaces,
    Disjoint (emb.faceBoundary f.1)
      (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
  hboundaryFaceSeparated : ∀ f : AmbientFace emb.faces,
    ¬ ((∃ e ∈ emb.faceBoundary f.1, e ∈ construction.outerAmbientBoundary) ∧
        (∃ e ∈ emb.faceBoundary f.1, e ∈ construction.innerAmbientBoundary))
  hnonPeelBoundary : ∀ f : AmbientFace emb.faces, f ∉ construction.peelFaces →
    (∃ e ∈ emb.faceBoundary f.1, e ∈ construction.outerAmbientBoundary) ∨
      (∃ e ∈ emb.faceBoundary f.1, e ∈ construction.innerAmbientBoundary)
  hcurrentInnerAmbientBoundary :
    ∀ i : Fin construction.numCollars,
      construction.innerAmbientBoundary ⊆
        relativeBoundarySupport
          (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)
          (annulusCurrentFaces construction.collarFaces i)
  hcurrentBoundaryZero :
    relativeBoundarySupport
        (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)
        (annulusCurrentFaces construction.collarFaces
          ⟨0, by
            unfold PlanarBoundaryAnnulusConstruction.numCollars
            omega⟩) =
      construction.outerAmbientBoundary ∪ construction.innerAmbientBoundary
  hcurrentBoundaryInterior :
    ∀ i : Fin construction.numCollars, 0 < i.1 →
      relativeBoundarySupport
          (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)
          (annulusCurrentFaces construction.collarFaces i) ⊆
        interiorEdgeSupport emb.faceBoundary emb.faces ∪ construction.innerAmbientBoundary
  hcurrentOuterBoundaryNonempty :
    ∀ i : Fin construction.numCollars,
      (relativeBoundarySupport
          (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)
          (annulusCurrentFaces construction.collarFaces i) \
        construction.innerAmbientBoundary).Nonempty
  hcurrentOuterBoundaryDisjoint :
    ∀ {i j : Fin construction.numCollars}, i ≠ j →
      Disjoint
        (relativeBoundarySupport
            (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)
            (annulusCurrentFaces construction.collarFaces i) \
          construction.innerAmbientBoundary)
        (relativeBoundarySupport
            (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)
            (annulusCurrentFaces construction.collarFaces j) \
          construction.innerAmbientBoundary)

/-- Lower the concrete boundary-face-plus-BFS-strata annulus geometry to the abstract face-layer
package used by the current decomposition file. -/
def PlanarBoundaryAnnulusConstructionFaceLayerData.toPlanarBoundaryAnnulusFaceLayerData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstructionFaceLayerData emb) :
    PlanarBoundaryAnnulusFaceLayerData emb := by
  let c := data.construction
  refine
    { toPlanarBoundaryAnnulusBoundaryData := c.toPlanarBoundaryAnnulusBoundaryData
      numCollars := c.numCollars
      hnumCollars_pos := by
        unfold PlanarBoundaryAnnulusConstruction.numCollars
        omega
      collarFaces := c.collarFaces
      hfaceCover := ?_
      hdisjoint := ?_
      hcurrentInnerAmbientBoundary := data.hcurrentInnerAmbientBoundary
      hcurrentBoundaryZero := data.hcurrentBoundaryZero
      hcurrentBoundaryInterior := data.hcurrentBoundaryInterior
      hcurrentOuterBoundaryNonempty := data.hcurrentOuterBoundaryNonempty
      hcurrentOuterBoundaryDisjoint := data.hcurrentOuterBoundaryDisjoint }
  · exact c.collarFaces_cover_of_facePartition data.hnonPeelBoundary
  · exact c.collarFaces_disjoint_of_facePartition data.hpeelInterior data.hboundaryFaceSeparated

/-- A reduced geometric precursor to the annulus face-layer shell. The collar partition is still
derived from outer-boundary faces, BFS strata, and inner-boundary faces, but the current-boundary
facts forced by that partition are no longer assumed separately. Only the genuinely remaining
outer-frontier obligations on positive stages are kept as data. -/
structure PlanarBoundaryAnnulusConstructionPositiveFrontierData {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) where
  construction : PlanarBoundaryAnnulusConstruction emb
  hpeelInterior : ∀ f ∈ construction.peelFaces,
    Disjoint (emb.faceBoundary f.1)
      (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
  hboundaryFaceSeparated : ∀ f : AmbientFace emb.faces,
    ¬ ((∃ e ∈ emb.faceBoundary f.1, e ∈ construction.outerAmbientBoundary) ∧
        (∃ e ∈ emb.faceBoundary f.1, e ∈ construction.innerAmbientBoundary))
  hnonPeelBoundary : ∀ f : AmbientFace emb.faces, f ∉ construction.peelFaces →
    (∃ e ∈ emb.faceBoundary f.1, e ∈ construction.outerAmbientBoundary) ∨
      (∃ e ∈ emb.faceBoundary f.1, e ∈ construction.innerAmbientBoundary)
  hcurrentOuterBoundaryNonempty :
    ∀ i : Fin construction.numCollars, 0 < i.1 →
      (construction.currentOuterBoundary i).Nonempty
  hcurrentOuterBoundaryDisjoint :
    ∀ {i j : Fin construction.numCollars}, 0 < i.1 → 0 < j.1 → i ≠ j →
      Disjoint (construction.currentOuterBoundary i) (construction.currentOuterBoundary j)

/-- A more concrete geometric precursor to the positive-frontier shell. The remaining face-side
obligations are expressed purely as finite-set cover/disjointness statements for the ambient outer
boundary faces, peeled faces, and ambient inner boundary faces, rather than as quantified
face-by-face predicates. -/
structure PlanarBoundaryAnnulusConstructionFacePartitionData {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) where
  construction : PlanarBoundaryAnnulusConstruction emb
  hpeelInterior : ∀ f ∈ construction.peelFaces,
    Disjoint (emb.faceBoundary f.1)
      (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
  hfaceCover :
    emb.faces.attach ⊆
      construction.outerBoundaryFaces ∪ construction.peelFaces ∪ construction.innerBoundaryFaces
  hboundaryFaceDisjoint :
    Disjoint construction.outerBoundaryFaces construction.innerBoundaryFaces
  hcurrentOuterBoundaryNonempty :
    ∀ i : Fin construction.numCollars, 0 < i.1 →
      (construction.currentOuterBoundary i).Nonempty
  hcurrentOuterBoundaryDisjoint :
    ∀ {i j : Fin construction.numCollars}, 0 < i.1 → 0 < j.1 → i ≠ j →
      Disjoint (construction.currentOuterBoundary i) (construction.currentOuterBoundary j)

/-- A still more concrete precursor to the positive-frontier shell. Instead of directly assuming
that ambient faces are covered by outer-boundary faces, peeled faces, and inner-boundary faces,
it is enough to say that every non-peeled face meets the ambient selected boundary support. The
outer/inner cover is then recovered from the annulus boundary split itself. -/
structure PlanarBoundaryAnnulusConstructionBoundarySupportFaceData {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) where
  construction : PlanarBoundaryAnnulusConstruction emb
  hpeelInterior : ∀ f ∈ construction.peelFaces,
    Disjoint (emb.faceBoundary f.1)
      (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
  hnonPeelSelectedBoundary : ∀ f : AmbientFace emb.faces, f ∉ construction.peelFaces →
    ∃ e ∈ emb.faceBoundary f.1,
      e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces
  hboundaryFaceDisjoint :
    Disjoint construction.outerBoundaryFaces construction.innerBoundaryFaces
  hcurrentOuterBoundaryNonempty :
    ∀ i : Fin construction.numCollars, 0 < i.1 →
      (construction.currentOuterBoundary i).Nonempty
  hcurrentOuterBoundaryDisjoint :
    ∀ {i j : Fin construction.numCollars}, 0 < i.1 → 0 < j.1 → i ≠ j →
      Disjoint (construction.currentOuterBoundary i) (construction.currentOuterBoundary j)

/-- Graph-level existence form of the construction-side face-layer shell. -/
def AdmitsPlanarBoundaryAnnulusConstructionFaceLayerData (G : SimpleGraph V) : Prop :=
  ∃ emb : PlaneEmbeddingWithBoundary G,
    Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb)

/-- Graph-level existence form of the reduced positive-frontier shell. -/
def AdmitsPlanarBoundaryAnnulusConstructionPositiveFrontierData (G : SimpleGraph V) : Prop :=
  ∃ emb : PlaneEmbeddingWithBoundary G,
    Nonempty (PlanarBoundaryAnnulusConstructionPositiveFrontierData emb)

/-- Graph-level existence form of the explicit outer/peeled/inner face-partition shell. -/
def AdmitsPlanarBoundaryAnnulusConstructionFacePartitionData (G : SimpleGraph V) : Prop :=
  ∃ emb : PlaneEmbeddingWithBoundary G,
    Nonempty (PlanarBoundaryAnnulusConstructionFacePartitionData emb)

/-- Graph-level existence form of the selected-boundary contact shell for the annulus
construction route. -/
def AdmitsPlanarBoundaryAnnulusConstructionBoundarySupportFaceData (G : SimpleGraph V) : Prop :=
  ∃ emb : PlaneEmbeddingWithBoundary G,
    Nonempty (PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb)

theorem
    not_nonempty_planarBoundaryAnnulusConstructionPositiveFrontierData_of_interiorEdgeSupport_eq_empty
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (hnoInterior : interiorEdgeSupport emb.faceBoundary emb.faces = ∅) :
    ¬ Nonempty (PlanarBoundaryAnnulusConstructionPositiveFrontierData emb) := by
  intro h
  rcases h with ⟨data⟩
  let i : Fin data.construction.numCollars := ⟨1, by
    unfold PlanarBoundaryAnnulusConstruction.numCollars
    omega⟩
  have hi : 0 < i.1 := by
    simp [i]
  rcases data.hcurrentOuterBoundaryNonempty i hi with ⟨e, he⟩
  have hempty :
      data.construction.currentOuterBoundary i = ∅ :=
    data.construction.currentOuterBoundary_eq_empty_of_interiorEdgeSupport_eq_empty_of_pos
      data.hpeelInterior data.hboundaryFaceSeparated hi hnoInterior
  simp [hempty] at he

theorem
    not_nonempty_planarBoundaryAnnulusConstructionFacePartitionData_of_interiorEdgeSupport_eq_empty
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (hnoInterior : interiorEdgeSupport emb.faceBoundary emb.faces = ∅) :
    ¬ Nonempty (PlanarBoundaryAnnulusConstructionFacePartitionData emb) := by
  intro h
  rcases h with ⟨data⟩
  let positiveData : PlanarBoundaryAnnulusConstructionPositiveFrontierData emb :=
    { construction := data.construction
      hpeelInterior := data.hpeelInterior
      hboundaryFaceSeparated :=
        data.construction.boundaryFaceSeparated_of_outerBoundaryFaces_disjoint_innerBoundaryFaces
          data.hboundaryFaceDisjoint
      hnonPeelBoundary :=
        data.construction.nonPeelBoundary_of_faces_subset_outerBoundaryFaces_union_peelFaces_union_innerBoundaryFaces
          data.hfaceCover
      hcurrentOuterBoundaryNonempty := data.hcurrentOuterBoundaryNonempty
      hcurrentOuterBoundaryDisjoint := data.hcurrentOuterBoundaryDisjoint }
  exact
    (not_nonempty_planarBoundaryAnnulusConstructionPositiveFrontierData_of_interiorEdgeSupport_eq_empty
      (emb := emb) hnoInterior) ⟨positiveData⟩

theorem
    not_nonempty_planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_interiorEdgeSupport_eq_empty
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (hnoInterior : interiorEdgeSupport emb.faceBoundary emb.faces = ∅) :
    ¬ Nonempty (PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb) := by
  intro h
  rcases h with ⟨data⟩
  let facePartitionData : PlanarBoundaryAnnulusConstructionFacePartitionData emb :=
    { construction := data.construction
      hpeelInterior := data.hpeelInterior
      hfaceCover :=
        data.construction.faces_subset_outerBoundaryFaces_union_peelFaces_union_innerBoundaryFaces_of_nonPeelSelectedBoundary
          data.hnonPeelSelectedBoundary
      hboundaryFaceDisjoint := data.hboundaryFaceDisjoint
      hcurrentOuterBoundaryNonempty := data.hcurrentOuterBoundaryNonempty
      hcurrentOuterBoundaryDisjoint := data.hcurrentOuterBoundaryDisjoint }
  exact
    (not_nonempty_planarBoundaryAnnulusConstructionFacePartitionData_of_interiorEdgeSupport_eq_empty
      (emb := emb) hnoInterior) ⟨facePartitionData⟩

theorem
    not_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_interiorEdgeSupport_eq_empty
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (hnoInterior : interiorEdgeSupport emb.faceBoundary emb.faces = ∅) :
    ¬ Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb) := by
  intro h
  rcases h with ⟨data⟩
  let i : Fin data.construction.numCollars := ⟨1, by
    unfold PlanarBoundaryAnnulusConstruction.numCollars
    omega⟩
  have hi : 0 < i.1 := by
    simp [i]
  rcases data.hcurrentOuterBoundaryNonempty i with ⟨e, he⟩
  have heOuter : e ∈ data.construction.currentOuterBoundary i := by
    change e ∈ data.construction.currentBoundary i \ data.construction.innerAmbientBoundary
    exact he
  have hempty :
      data.construction.currentOuterBoundary i = ∅ :=
    data.construction.currentOuterBoundary_eq_empty_of_interiorEdgeSupport_eq_empty_of_pos
      data.hpeelInterior data.hboundaryFaceSeparated hi hnoInterior
  simp [hempty] at heOuter

/-- At least one currently formalized positive-stage annulus-construction shell exists on the
embedding.  This aggregates the route's present construction-side candidates into one disjunctive
surface. -/
def SomePositiveStageConstructionShell {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) : Prop :=
  Nonempty (PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb) ∨
    Nonempty (PlanarBoundaryAnnulusConstructionFacePartitionData emb) ∨
    Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb) ∨
    Nonempty (PlanarBoundaryAnnulusConstructionPositiveFrontierData emb)

/-- None of the currently formalized positive-stage annulus-construction shells exist on the
embedding. -/
def NoPositiveStageConstructionShells {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) : Prop :=
  ¬ Nonempty (PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb) ∧
    ¬ Nonempty (PlanarBoundaryAnnulusConstructionFacePartitionData emb) ∧
    ¬ Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb) ∧
    ¬ Nonempty (PlanarBoundaryAnnulusConstructionPositiveFrontierData emb)

/-- The negative bundle exactly rules out the disjunctive positive-stage construction surface. -/
theorem not_somePositiveStageConstructionShell_of_noPositiveStageConstructionShells
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (hNo : NoPositiveStageConstructionShells emb) :
    ¬ SomePositiveStageConstructionShell emb := by
  rcases hNo with ⟨hBoundarySupport, hFacePartition, hFaceLayer, hPositiveFrontier⟩
  intro hSome
  rcases hSome with hBoundarySupportData | hSome
  · exact hBoundarySupport hBoundarySupportData
  rcases hSome with hFacePartitionData | hSome
  · exact hFacePartition hFacePartitionData
  rcases hSome with hFaceLayerData | hPositiveFrontierData
  · exact hFaceLayer hFaceLayerData
  · exact hPositiveFrontier hPositiveFrontierData

/-- Empty interior-edge support already rules out every currently formalized positive-stage
annulus-construction shell at once. -/
theorem noPositiveStageConstructionShells_of_interiorEdgeSupport_eq_empty
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (hnoInterior : interiorEdgeSupport emb.faceBoundary emb.faces = ∅) :
    NoPositiveStageConstructionShells emb := by
  exact
    ⟨not_nonempty_planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_interiorEdgeSupport_eq_empty
        (emb := emb) hnoInterior,
      not_nonempty_planarBoundaryAnnulusConstructionFacePartitionData_of_interiorEdgeSupport_eq_empty
        (emb := emb) hnoInterior,
      not_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_interiorEdgeSupport_eq_empty
        (emb := emb) hnoInterior,
      not_nonempty_planarBoundaryAnnulusConstructionPositiveFrontierData_of_interiorEdgeSupport_eq_empty
        (emb := emb) hnoInterior⟩

/-- Lower the selected-boundary version of the concrete face data to the explicit outer/inner
face-partition shell. -/
def PlanarBoundaryAnnulusConstructionBoundarySupportFaceData.toFacePartitionData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb) :
    PlanarBoundaryAnnulusConstructionFacePartitionData emb := by
  let c := data.construction
  refine
    { construction := c
      hpeelInterior := data.hpeelInterior
      hfaceCover := ?_
      hboundaryFaceDisjoint := data.hboundaryFaceDisjoint
      hcurrentOuterBoundaryNonempty := data.hcurrentOuterBoundaryNonempty
      hcurrentOuterBoundaryDisjoint := data.hcurrentOuterBoundaryDisjoint }
  exact
    c.faces_subset_outerBoundaryFaces_union_peelFaces_union_innerBoundaryFaces_of_nonPeelSelectedBoundary
      data.hnonPeelSelectedBoundary

/-- The explicit outer/peeled/inner face-partition shell also recovers the selected-boundary
contact version directly: every non-peeled face lies on one of the two ambient boundary face
layers, hence meets the ambient selected boundary support. -/
def PlanarBoundaryAnnulusConstructionFacePartitionData.toBoundarySupportFaceData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstructionFacePartitionData emb) :
    PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb := by
  let c := data.construction
  refine
    { construction := c
      hpeelInterior := data.hpeelInterior
      hnonPeelSelectedBoundary := ?_
      hboundaryFaceDisjoint := data.hboundaryFaceDisjoint
      hcurrentOuterBoundaryNonempty := data.hcurrentOuterBoundaryNonempty
      hcurrentOuterBoundaryDisjoint := data.hcurrentOuterBoundaryDisjoint }
  exact
    c.nonPeelSelectedBoundary_of_faces_subset_outerBoundaryFaces_union_peelFaces_union_innerBoundaryFaces
      data.hfaceCover

/-- Lower the concrete face-partition package to the older positive-frontier shell by deriving
the remaining quantified face-side obligations from the finite-set cover and disjointness
statements. -/
def PlanarBoundaryAnnulusConstructionFacePartitionData.toPositiveFrontierData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstructionFacePartitionData emb) :
    PlanarBoundaryAnnulusConstructionPositiveFrontierData emb := by
  let c := data.construction
  refine
    { construction := c
      hpeelInterior := data.hpeelInterior
      hboundaryFaceSeparated := ?_
      hnonPeelBoundary := ?_
      hcurrentOuterBoundaryNonempty := data.hcurrentOuterBoundaryNonempty
      hcurrentOuterBoundaryDisjoint := data.hcurrentOuterBoundaryDisjoint }
  · exact
      c.boundaryFaceSeparated_of_outerBoundaryFaces_disjoint_innerBoundaryFaces
        data.hboundaryFaceDisjoint
  · exact
      c.nonPeelBoundary_of_faces_subset_outerBoundaryFaces_union_peelFaces_union_innerBoundaryFaces
        data.hfaceCover

/-- Lower the reduced positive-frontier package to the fuller construction-side face-layer package
by deriving the stage-`0`, inner-boundary, and interior-boundary facts from the concrete collar
partition itself. -/
def PlanarBoundaryAnnulusConstructionPositiveFrontierData.toPlanarBoundaryAnnulusConstructionFaceLayerData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstructionPositiveFrontierData emb) :
    PlanarBoundaryAnnulusConstructionFaceLayerData emb := by
  let c := data.construction
  let i0 : Fin c.numCollars := ⟨0, by
    unfold PlanarBoundaryAnnulusConstruction.numCollars
    omega⟩
  refine
    { construction := c
      hpeelInterior := data.hpeelInterior
      hboundaryFaceSeparated := data.hboundaryFaceSeparated
      hnonPeelBoundary := data.hnonPeelBoundary
      hcurrentInnerAmbientBoundary := c.innerAmbientBoundary_subset_currentBoundary
      hcurrentBoundaryZero := c.currentBoundary_zero_eq_ambientBoundary_of_facePartition
        data.hnonPeelBoundary
      hcurrentBoundaryInterior := by
        intro i hi
        exact c.currentBoundary_subset_interiorEdgeSupport_union_innerAmbientBoundary_of_pos
          data.hpeelInterior data.hboundaryFaceSeparated hi
      hcurrentOuterBoundaryNonempty := ?_
      hcurrentOuterBoundaryDisjoint := ?_ }
  · intro i
    by_cases hi : 0 < i.1
    · exact data.hcurrentOuterBoundaryNonempty i hi
    · have hEq : i = i0 := by
        apply Fin.ext
        have hVal : i.1 = 0 := by
          omega
        simpa [i0] using hVal
      subst hEq
      show (c.currentOuterBoundary i0).Nonempty
      rw [c.currentOuterBoundary_zero_eq_outerAmbientBoundary_of_facePartition
        data.hnonPeelBoundary]
      exact c.houterAmbientBoundaryNonempty
  · intro i j hij
    by_cases hi : 0 < i.1
    · by_cases hj : 0 < j.1
      · exact data.hcurrentOuterBoundaryDisjoint hi hj hij
      · have hEq : j = i0 := by
          apply Fin.ext
          have hVal : j.1 = 0 := by
            omega
          simpa [i0] using hVal
        subst hEq
        show Disjoint (c.currentOuterBoundary i) (c.currentOuterBoundary i0)
        rw [c.currentOuterBoundary_zero_eq_outerAmbientBoundary_of_facePartition
          data.hnonPeelBoundary]
        exact (c.outerAmbientBoundary_disjoint_currentOuterBoundary_of_pos
          data.hpeelInterior data.hboundaryFaceSeparated hi).symm
    · have hEq : i = i0 := by
        apply Fin.ext
        have hVal : i.1 = 0 := by
          omega
        simpa [i0] using hVal
      subst hEq
      show Disjoint (c.currentOuterBoundary i0) (c.currentOuterBoundary j)
      rw [c.currentOuterBoundary_zero_eq_outerAmbientBoundary_of_facePartition
        data.hnonPeelBoundary]
      by_cases hj : 0 < j.1
      · exact c.outerAmbientBoundary_disjoint_currentOuterBoundary_of_pos
          data.hpeelInterior data.hboundaryFaceSeparated hj
      · exfalso
        apply hij
        apply Fin.ext
        omega

/-- The reduced positive-frontier package also lowers directly to the abstract annulus face-layer
data used by the decomposition route. -/
def PlanarBoundaryAnnulusConstructionPositiveFrontierData.toPlanarBoundaryAnnulusFaceLayerData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstructionPositiveFrontierData emb) :
    PlanarBoundaryAnnulusFaceLayerData emb :=
  (data.toPlanarBoundaryAnnulusConstructionFaceLayerData).toPlanarBoundaryAnnulusFaceLayerData

/-- The concrete face-partition package also lowers directly to the fuller construction-side
face-layer shell. -/
def PlanarBoundaryAnnulusConstructionFacePartitionData.toPlanarBoundaryAnnulusConstructionFaceLayerData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstructionFacePartitionData emb) :
    PlanarBoundaryAnnulusConstructionFaceLayerData emb :=
  data.toPositiveFrontierData.toPlanarBoundaryAnnulusConstructionFaceLayerData

/-- The concrete face-partition package also lowers directly to the abstract annulus face-layer
data used by the decomposition route. -/
def PlanarBoundaryAnnulusConstructionFacePartitionData.toPlanarBoundaryAnnulusFaceLayerData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstructionFacePartitionData emb) :
    PlanarBoundaryAnnulusFaceLayerData emb :=
  data.toPlanarBoundaryAnnulusConstructionFaceLayerData.toPlanarBoundaryAnnulusFaceLayerData

/-- The selected-boundary version also lowers directly to the older positive-frontier shell. -/
def PlanarBoundaryAnnulusConstructionBoundarySupportFaceData.toPositiveFrontierData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb) :
    PlanarBoundaryAnnulusConstructionPositiveFrontierData emb :=
  data.toFacePartitionData.toPositiveFrontierData

/-- The selected-boundary version also lowers directly to the construction-side face-layer shell.
-/
def PlanarBoundaryAnnulusConstructionBoundarySupportFaceData.toPlanarBoundaryAnnulusConstructionFaceLayerData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb) :
    PlanarBoundaryAnnulusConstructionFaceLayerData emb :=
  data.toFacePartitionData.toPlanarBoundaryAnnulusConstructionFaceLayerData

/-- The selected-boundary version also lowers directly to the abstract annulus face-layer shell
used by the decomposition route. -/
def PlanarBoundaryAnnulusConstructionBoundarySupportFaceData.toPlanarBoundaryAnnulusFaceLayerData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb) :
    PlanarBoundaryAnnulusFaceLayerData emb :=
  data.toFacePartitionData.toPlanarBoundaryAnnulusFaceLayerData

theorem
    admitsPlanarBoundaryAnnulusConstructionPositiveFrontierData_of_admitsPlanarBoundaryAnnulusConstructionFacePartitionData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryAnnulusConstructionFacePartitionData G) :
    AdmitsPlanarBoundaryAnnulusConstructionPositiveFrontierData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.toPositiveFrontierData⟩⟩

theorem
    admitsPlanarBoundaryAnnulusConstructionFacePartitionData_of_admitsPlanarBoundaryAnnulusConstructionBoundarySupportFaceData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryAnnulusConstructionBoundarySupportFaceData G) :
    AdmitsPlanarBoundaryAnnulusConstructionFacePartitionData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.toFacePartitionData⟩⟩

theorem
    admitsPlanarBoundaryAnnulusConstructionFaceLayerData_of_admitsPlanarBoundaryAnnulusConstructionPositiveFrontierData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryAnnulusConstructionPositiveFrontierData G) :
    AdmitsPlanarBoundaryAnnulusConstructionFaceLayerData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.toPlanarBoundaryAnnulusConstructionFaceLayerData⟩⟩

theorem
    admitsPlanarBoundaryAnnulusConstructionFaceLayerData_of_admitsPlanarBoundaryAnnulusConstructionFacePartitionData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryAnnulusConstructionFacePartitionData G) :
    AdmitsPlanarBoundaryAnnulusConstructionFaceLayerData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.toPlanarBoundaryAnnulusConstructionFaceLayerData⟩⟩

theorem
    admitsPlanarBoundaryAnnulusConstructionFaceLayerData_of_admitsPlanarBoundaryAnnulusConstructionBoundarySupportFaceData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryAnnulusConstructionBoundarySupportFaceData G) :
    AdmitsPlanarBoundaryAnnulusConstructionFaceLayerData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.toPlanarBoundaryAnnulusConstructionFaceLayerData⟩⟩

theorem admitsPlanarBoundaryAnnulusDecomposition_of_admitsPlanarBoundaryAnnulusConstructionFaceLayerData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryAnnulusConstructionFaceLayerData G) :
    AdmitsPlanarBoundaryAnnulusDecomposition G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact
    admitsPlanarBoundaryAnnulusDecomposition_of_admitsPlanarBoundaryAnnulusFaceLayerData
      ⟨emb, ⟨data.toPlanarBoundaryAnnulusFaceLayerData⟩⟩

theorem
    admitsPlanarBoundaryAnnulusDecomposition_of_admitsPlanarBoundaryAnnulusConstructionPositiveFrontierData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryAnnulusConstructionPositiveFrontierData G) :
    AdmitsPlanarBoundaryAnnulusDecomposition G := by
  exact
    admitsPlanarBoundaryAnnulusDecomposition_of_admitsPlanarBoundaryAnnulusConstructionFaceLayerData
      (admitsPlanarBoundaryAnnulusConstructionFaceLayerData_of_admitsPlanarBoundaryAnnulusConstructionPositiveFrontierData
        hG)

theorem admitsPlanarBoundaryAnnulusDecomposition_of_admitsPlanarBoundaryAnnulusConstructionFacePartitionData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryAnnulusConstructionFacePartitionData G) :
    AdmitsPlanarBoundaryAnnulusDecomposition G := by
  exact
    admitsPlanarBoundaryAnnulusDecomposition_of_admitsPlanarBoundaryAnnulusConstructionFaceLayerData
      (admitsPlanarBoundaryAnnulusConstructionFaceLayerData_of_admitsPlanarBoundaryAnnulusConstructionFacePartitionData
        hG)

theorem
    admitsPlanarBoundaryAnnulusDecomposition_of_admitsPlanarBoundaryAnnulusConstructionBoundarySupportFaceData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryAnnulusConstructionBoundarySupportFaceData G) :
    AdmitsPlanarBoundaryAnnulusDecomposition G := by
  exact
    admitsPlanarBoundaryAnnulusDecomposition_of_admitsPlanarBoundaryAnnulusConstructionFaceLayerData
      (admitsPlanarBoundaryAnnulusConstructionFaceLayerData_of_admitsPlanarBoundaryAnnulusConstructionBoundarySupportFaceData
        hG)

theorem PlanarBoundaryAnnulusConstructionPositiveFrontierData.collarFaces_nonempty_of_pos_of_succ
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstructionPositiveFrontierData emb)
    {i : Fin data.construction.numCollars} (hi : 0 < i.1)
    (hsucc : i.1 + 1 < data.construction.numCollars) :
    (data.construction.collarFaces i).Nonempty := by
  let c := data.construction
  let j : Fin c.numCollars := ⟨i.1 + 1, hsucc⟩
  have hj : 0 < j.1 := by
    dsimp [j]
    omega
  by_contra hempty
  have hempty' : c.collarFaces i = ∅ := by
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    exact hempty
  have hij : i ≠ j := by
    intro hEq
    have hVal : i.1 = j.1 := congrArg Fin.val hEq
    dsimp [j] at hVal
    omega
  have hEqBoundary :
      c.currentOuterBoundary i = c.currentOuterBoundary j :=
    c.currentOuterBoundary_eq_currentOuterBoundary_succ_of_collarFaces_eq_empty hsucc hempty'
  rcases data.hcurrentOuterBoundaryNonempty i hi with ⟨e, he⟩
  have hdisj : Disjoint (c.currentOuterBoundary i) (c.currentOuterBoundary j) :=
    data.hcurrentOuterBoundaryDisjoint hi hj hij
  have hej : e ∈ c.currentOuterBoundary j := by
    rw [← hEqBoundary]
    exact he
  exact (Finset.disjoint_left.mp hdisj) he hej

theorem PlanarBoundaryAnnulusConstructionPositiveFrontierData.stratumFaces_nonempty
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstructionPositiveFrontierData emb)
    (i : Fin data.construction.numStrata) :
    (data.construction.stratumFaces i).Nonempty := by
  let c := data.construction
  let ci : Fin c.numCollars := ⟨i.1 + 1, by
    unfold PlanarBoundaryAnnulusConstruction.numCollars
    exact lt_trans (Nat.succ_lt_succ i.2) (Nat.lt_succ_self (c.numStrata + 1))⟩
  have hciPos : 0 < ci.1 := by
    dsimp [ci]
    omega
  have hciSucc : ci.1 + 1 < c.numCollars := by
    unfold PlanarBoundaryAnnulusConstruction.numCollars
    change i.1 + 2 < c.numStrata + 2
    exact Nat.add_lt_add_right i.2 2
  have hnonempty : (c.collarFaces ci).Nonempty :=
    data.collarFaces_nonempty_of_pos_of_succ hciPos hciSucc
  rwa [c.collarFaces_succ i] at hnonempty

/-- Positive-frontier data forces the first peeled stratum to be inhabited.  Consequently, this
shell cannot be repaired by requiring every peeled face to have positive stored distance: the
frontier axioms themselves make a zero-distance peeled face part of the data. -/
theorem PlanarBoundaryAnnulusConstructionPositiveFrontierData.exists_peelFace_faceDistance_zero
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstructionPositiveFrontierData emb) :
    ∃ g ∈ data.construction.peelFaces, data.construction.faceDistance g = 0 := by
  let c := data.construction
  let i0 : Fin c.numStrata := ⟨0, by
    unfold PlanarBoundaryAnnulusConstruction.numStrata
    omega⟩
  rcases data.stratumFaces_nonempty i0 with ⟨g, hg⟩
  have hg' : g ∈ c.peelFaces ∧ c.faceDistance g = i0.1 :=
    (c.mem_stratumFaces_iff).1 hg
  exact ⟨g, hg'.1, by simpa [i0] using hg'.2⟩

/-- No positive-frontier package can have all peeled faces at positive stored distance. -/
theorem PlanarBoundaryAnnulusConstructionPositiveFrontierData.not_forall_peelFaces_positive
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstructionPositiveFrontierData emb) :
    ¬ ∀ g ∈ data.construction.peelFaces, 0 < data.construction.faceDistance g := by
  rcases data.exists_peelFace_faceDistance_zero with ⟨g, hg, hzero⟩
  intro hpos
  have hbad : 0 < data.construction.faceDistance g := hpos g hg
  rw [hzero] at hbad
  exact (Nat.not_lt_zero 0 hbad).elim

theorem PlanarBoundaryAnnulusConstructionPositiveFrontierData.collarFaces_nonempty
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstructionPositiveFrontierData emb)
    (i : Fin data.construction.numCollars) :
    (data.construction.collarFaces i).Nonempty := by
  let c := data.construction
  by_cases h0 : i.1 = 0
  · have hEq : c.collarFaces i = c.outerBoundaryFaces := by
      simp [PlanarBoundaryAnnulusConstruction.collarFaces, h0]
    rw [hEq]
    exact c.toPlanarBoundaryAnnulusBoundaryData.outerBoundaryFaces_nonempty
  · by_cases hmid : i.1 - 1 < c.numStrata
    · let j : Fin c.numStrata := ⟨i.1 - 1, hmid⟩
      have hEq : c.collarFaces i = c.stratumFaces j := by
        simp [PlanarBoundaryAnnulusConstruction.collarFaces, h0, hmid, j]
      rw [hEq]
      exact data.stratumFaces_nonempty j
    · have hlast : i.1 = c.numStrata + 1 := by
        have hi_pos : 0 < i.1 := Nat.pos_of_ne_zero h0
        have hi_lt : i.1 < c.numStrata + 2 := by
          have hi_lt' := i.isLt
          change i.1 < c.numStrata + 2 at hi_lt'
          exact hi_lt'
        have hge : c.numStrata ≤ i.1 - 1 := Nat.le_of_not_lt hmid
        have hle : i.1 - 1 ≤ c.numStrata := by
          omega
        have hEqSub : i.1 - 1 = c.numStrata := le_antisymm hle hge
        calc
          i.1 = Nat.succ (i.1 - 1) := by
            simpa using (Nat.succ_pred_eq_of_pos hi_pos).symm
          _ = c.numStrata + 1 := by
            simp [hEqSub, Nat.succ_eq_add_one]
      have hEq : c.collarFaces i = c.innerBoundaryFaces := by
        simp [PlanarBoundaryAnnulusConstruction.collarFaces, hlast]
      rw [hEq]
      exact c.toPlanarBoundaryAnnulusBoundaryData.innerBoundaryFaces_nonempty

theorem PlanarBoundaryAnnulusConstructionPositiveFrontierData.collarFaces_disjoint_currentFaces_of_lt
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstructionPositiveFrontierData emb)
    {i j : Fin data.construction.numCollars} (hij : i < j) :
    Disjoint (data.construction.collarFaces i) (data.construction.currentFaces j) := by
  let c := data.construction
  rw [Finset.disjoint_left]
  intro f hfi hfj
  rcases (c.mem_currentFaces_iff (i := j)).1 hfj with hnow | ⟨k, hjk, hk⟩
  · exact (Finset.disjoint_left.mp
      (c.collarFaces_disjoint_of_facePartition
        data.hpeelInterior data.hboundaryFaceSeparated (ne_of_lt hij))) hfi hnow
  · have hik : i ≠ k := ne_of_lt (lt_trans hij hjk)
    exact (Finset.disjoint_left.mp
      (c.collarFaces_disjoint_of_facePartition
        data.hpeelInterior data.hboundaryFaceSeparated hik)) hfi hk

theorem PlanarBoundaryAnnulusConstructionPositiveFrontierData.currentFaces_ssubset_currentFaces_of_lt
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstructionPositiveFrontierData emb)
    {i j : Fin data.construction.numCollars} (hij : i < j) :
    data.construction.currentFaces j ⊂ data.construction.currentFaces i := by
  let c := data.construction
  apply ssubset_of_subset_of_ne
  · exact c.currentFaces_subset_currentFaces_of_lt hij
  · intro hEq
    rcases data.collarFaces_nonempty i with ⟨f, hf⟩
    have hfCurrent : f ∈ c.currentFaces i :=
      (c.mem_currentFaces_iff (i := i)).2 <| Or.inl hf
    have hfLater : f ∈ c.currentFaces j := by
      rw [hEq]
      exact hfCurrent
    exact (Finset.disjoint_left.mp
      (data.collarFaces_disjoint_currentFaces_of_lt hij)) hf hfLater

theorem PlanarBoundaryAnnulusConstructionPositiveFrontierData.currentFaces_card_lt_of_lt
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstructionPositiveFrontierData emb)
    {i j : Fin data.construction.numCollars} (hij : i < j) :
    (data.construction.currentFaces j).card <
      (data.construction.currentFaces i).card := by
  exact Finset.card_lt_card (data.currentFaces_ssubset_currentFaces_of_lt hij)

theorem PlanarBoundaryAnnulusConstructionPositiveFrontierData.currentFaces_next_ssubset_currentFaces
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstructionPositiveFrontierData emb)
    (i : Fin data.construction.numCollars)
    (hi : i.1 + 1 < data.construction.numCollars) :
    data.construction.currentFaces ⟨i.1 + 1, hi⟩ ⊂ data.construction.currentFaces i := by
  let j : Fin data.construction.numCollars := ⟨i.1 + 1, hi⟩
  have hij : i < j := by
    show i.1 < j.1
    dsimp [j]
    omega
  exact data.currentFaces_ssubset_currentFaces_of_lt hij

theorem PlanarBoundaryAnnulusConstructionPositiveFrontierData.currentFaces_next_card_lt_currentFaces
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstructionPositiveFrontierData emb)
    (i : Fin data.construction.numCollars)
    (hi : i.1 + 1 < data.construction.numCollars) :
    (data.construction.currentFaces ⟨i.1 + 1, hi⟩).card <
      (data.construction.currentFaces i).card := by
  let j : Fin data.construction.numCollars := ⟨i.1 + 1, hi⟩
  have hij : i < j := by
    show i.1 < j.1
    dsimp [j]
    omega
  exact data.currentFaces_card_lt_of_lt hij

theorem
    PlanarBoundaryAnnulusConstructionPositiveFrontierData.currentFaces_card_add_val_le_currentFaces_zero_card
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstructionPositiveFrontierData emb)
    (i : Fin data.construction.numCollars) :
    (data.construction.currentFaces i).card + i.1 ≤
      (data.construction.currentFaces ⟨0, by
        unfold PlanarBoundaryAnnulusConstruction.numCollars
        omega⟩).card := by
  let c := data.construction
  let i0 : Fin c.numCollars := ⟨0, by
    unfold PlanarBoundaryAnnulusConstruction.numCollars
    omega⟩
  change (c.currentFaces i).card + i.1 ≤ (c.currentFaces i0).card
  have hmain : ∀ n (hn : n < c.numCollars),
      (c.currentFaces ⟨n, hn⟩).card + n ≤ (c.currentFaces i0).card := by
    intro n
    induction n with
    | zero =>
        intro hn
        have hEq : (⟨0, hn⟩ : Fin c.numCollars) = i0 := Fin.ext rfl
        simp [hEq]
    | succ n ih =>
        intro hn
        have hnlt : n < c.numCollars := by omega
        have hstep :
            (c.currentFaces ⟨n + 1, hn⟩).card <
              (c.currentFaces ⟨n, hnlt⟩).card := by
          simpa using
            (data.currentFaces_next_card_lt_currentFaces ⟨n, hnlt⟩ hn)
        have hih := ih hnlt
        omega
  exact hmain i.1 i.2

theorem PlanarBoundaryAnnulusConstructionPositiveFrontierData.numCollars_le_faces_card
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstructionPositiveFrontierData emb) :
    data.construction.numCollars ≤ emb.faces.card := by
  let c := data.construction
  let i0 : Fin c.numCollars := ⟨0, by
    unfold PlanarBoundaryAnnulusConstruction.numCollars
    omega⟩
  let ilast : Fin c.numCollars := ⟨c.numCollars - 1, by
    unfold PlanarBoundaryAnnulusConstruction.numCollars
    omega⟩
  have hlastNonempty : (c.currentFaces ilast).Nonempty :=
    c.currentFaces_nonempty ilast
  have hlastCardPos : 0 < (c.currentFaces ilast).card :=
    Finset.card_pos.2 hlastNonempty
  have hle := data.currentFaces_card_add_val_le_currentFaces_zero_card ilast
  have hzero :
      c.currentFaces i0 = emb.faces.attach :=
    c.currentFaces_zero_eq_faces_of_facePartition data.hnonPeelBoundary
  have hcollarsPos : 0 < c.numCollars := by
    unfold PlanarBoundaryAnnulusConstruction.numCollars
    omega
  change (c.currentFaces ilast).card + ilast.1 ≤ (c.currentFaces i0).card at hle
  have hlastVal : ilast.1 = c.numCollars - 1 := rfl
  rw [hzero] at hle
  simp at hle
  change c.numCollars ≤ emb.faces.card
  omega

/-- Forget the annulus-specific boundary split and regard the BFS construction as a boundary-aware
height-ordered witness-cover package. -/
def PlanarBoundaryAnnulusConstruction.toPlanarBoundaryHeightOrderedFacePeelWitnessData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb) :
    PlanarBoundaryHeightOrderedFacePeelWitnessData emb := by
  refine
    { peelFaces := data.peelFaces
      witnessEdge := data.witnessEdge
      height := data.faceDistance
      hcover := data.hcover
      hwitness := data.hwitness
      hrest := ?_ }
  intro f hf e he
  rcases data.hrest f hf e he with hboundary | ⟨g, hg, hge, hlt⟩
  · exact Or.inl <| by
      simpa [data.ambientBoundary_eq] using hboundary
  · exact Or.inr ⟨g, hg, hge, hlt⟩

/-- Group the BFS face-distance construction into explicit finite layers. This is the first
construction-side bridge from an annulus boundary split to the current collar-peeling theorem
layer. -/
noncomputable def PlanarBoundaryAnnulusConstruction.toPlanarBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb) :
    PlanarBoundaryCollarLayerFacePeelWitnessData emb :=
  planarBoundaryCollarLayerFacePeelWitnessData_of_heightOrderedFacePeelWitnessData
    data.toPlanarBoundaryHeightOrderedFacePeelWitnessData

/-- Exact construction-side orientation condition needed to extract a well-founded parent map from
the annulus BFS witness ownership. This is now the honest strengthened hypothesis after the
construction/face-layer obstruction: weaker current-frontier data alone does not force it. -/
def PlanarBoundaryAnnulusConstruction.ParentWitnessOrientation
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb) : Prop :=
  ∀ g ∈ data.peelFaces,
    ∃ p : AmbientFace emb.faces,
      data.witnessEdge g ∈ emb.faceBoundary p.1 ∧
        data.faceDistance p < data.faceDistance g

theorem PlanarBoundaryAnnulusConstruction.faceDistance_pos_of_parentWitness
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hparentWitness : data.ParentWitnessOrientation)
    {g : AmbientFace emb.faces} (hg : g ∈ data.peelFaces) :
    0 < data.faceDistance g := by
  rcases hparentWitness g hg with ⟨p, _hp, hlt⟩
  refine Nat.pos_of_ne_zero ?_
  intro hz
  rw [hz] at hlt
  exact (Nat.not_lt_zero _ hlt).elim

/-- Strict parent-witness orientation leaves every zero-valued BFS stratum empty: a peeled face
in such a stratum would have a strictly earlier parent face, forcing positive stored distance. -/
theorem PlanarBoundaryAnnulusConstruction.stratumFaces_eq_empty_of_parentWitness_of_val_eq_zero
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hparentWitness : data.ParentWitnessOrientation)
    {i : Fin data.numStrata} (hi : i.1 = 0) :
    data.stratumFaces i = ∅ := by
  ext g
  constructor
  · intro hg
    have hg' : g ∈ data.peelFaces ∧ data.faceDistance g = i.1 :=
      (data.mem_stratumFaces_iff).1 hg
    have hpos : 0 < data.faceDistance g :=
      data.faceDistance_pos_of_parentWitness hparentWitness hg'.1
    rw [hg'.2, hi] at hpos
    exact (Nat.not_lt_zero 0 hpos).elim
  · intro hg
    simp at hg

/-- A parent-oriented construction cannot simultaneously have every BFS stratum inhabited,
because its zero stratum is forced empty. -/
theorem PlanarBoundaryAnnulusConstruction.not_forall_stratumFaces_nonempty_of_parentWitness
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hparentWitness : data.ParentWitnessOrientation) :
    ¬ ∀ i : Fin data.numStrata, (data.stratumFaces i).Nonempty := by
  intro hnonempty
  let i0 : Fin data.numStrata := ⟨0, by
    unfold PlanarBoundaryAnnulusConstruction.numStrata
    omega⟩
  have hempty : data.stratumFaces i0 = ∅ :=
    data.stratumFaces_eq_empty_of_parentWitness_of_val_eq_zero hparentWitness (by simp [i0])
  rcases hnonempty i0 with ⟨g, hg⟩
  rw [hempty] at hg
  simp at hg

/-- The current positive-frontier shell is incompatible with strict parent-witness orientation.
Its frontier axioms force a peeled face in stratum `0`, while parent orientation forces every
peeled face to have positive stored distance. -/
theorem PlanarBoundaryAnnulusConstructionPositiveFrontierData.not_parentWitnessOrientation
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstructionPositiveFrontierData emb) :
    ¬ data.construction.ParentWitnessOrientation := by
  intro horient
  exact
    data.construction.not_forall_stratumFaces_nonempty_of_parentWitness horient
      data.stratumFaces_nonempty

/-- The concrete face-partition shell inherits the same zero-stratum obstruction to strict
parent-witness orientation. -/
theorem PlanarBoundaryAnnulusConstructionFacePartitionData.not_parentWitnessOrientation
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstructionFacePartitionData emb) :
    ¬ data.construction.ParentWitnessOrientation := by
  exact data.toPositiveFrontierData.not_parentWitnessOrientation

/-- Adding selected-boundary support bookkeeping does not remove the zero-stratum obstruction to
strict parent-witness orientation. -/
theorem PlanarBoundaryAnnulusConstructionBoundarySupportFaceData.not_parentWitnessOrientation
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb) :
    ¬ data.construction.ParentWitnessOrientation := by
  exact data.toPositiveFrontierData.not_parentWitnessOrientation

/-- If every peeled face chooses its witness edge on some strictly earlier ambient face, then the
annulus BFS construction already determines a well-founded parent relation on the peeled faces.
This is the minimal orientation hypothesis needed to turn the construction-side witness ownership
into the boundary-aware Theorem 4.9 parent-peeling interface without passing through the stronger
interior-dual packages. -/
noncomputable def
    PlanarBoundaryAnnulusConstruction.toPlanarBoundaryWellFoundedFacePeelWitnessData_of_parentWitness
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hparentWitness : data.ParentWitnessOrientation) :
    PlanarBoundaryWellFoundedFacePeelWitnessData emb := by
  let parentFace : AmbientFace emb.faces → Option (AmbientFace emb.faces) := fun g =>
    if hg : g ∈ data.peelFaces then
      some (Classical.choose (hparentWitness g hg))
    else
      none
  have hWF : WellFounded (ParentRel parentFace) := by
    refine wellFounded_parentRel_of_lt_height parentFace data.faceDistance ?_
    intro g f hgf
    by_cases hg : g ∈ data.peelFaces
    · have hspec := Classical.choose_spec (hparentWitness g hg)
      simp [parentFace, hg] at hgf
      subst hgf
      exact hspec.2
    · simp [parentFace, hg] at hgf
  refine
    { peelFaces := data.peelFaces
      parentFace := parentFace
      witnessEdge := data.witnessEdge
      hWF := hWF
      hcover := data.hcover
      hwitness := data.hwitness
      hchildren := ?_ }
  intro f hf e he
  rcases data.hrest f hf e he with hboundary | ⟨g, hg, hge, _hlt⟩
  · rcases Finset.mem_union.1 hboundary with hOuter | hInner
    · exact Or.inl (data.houterAmbientBoundarySubset hOuter)
    · exact Or.inl (data.hinnerAmbientBoundarySubset hInner)
  · have hspec := Classical.choose_spec (hparentWitness g hg)
    let p : AmbientFace emb.faces := Classical.choose (hparentWitness g hg)
    have hpMem : data.witnessEdge g ∈ emb.faceBoundary p.1 := by
      simpa [p] using hspec.1
    have hpLt : data.faceDistance p < data.faceDistance g := by
      simpa [p] using hspec.2
    have hpg : p.1 ≠ g.1 := by
      intro hEq
      have hpEq : p = g := Subtype.ext hEq
      exact (ne_of_lt hpLt) <| by simp [hpEq]
    have hparentg : parentFace g = some p := by
      simp [parentFace, hg, p]
    have hef : e ∈ emb.faceBoundary f.1 := (Finset.mem_erase.1 he).2
    have hpe : e ∈ emb.faceBoundary p.1 := by
      simpa [hge] using hpMem
    have hgeFace : e ∈ emb.faceBoundary g.1 := by
      simpa [hge] using data.hwitness g hg
    have hfp_or_hfg :
        f.1 = p.1 ∨ f.1 = g.1 := by
      exact
        eq_or_eq_of_mem_faceBoundary_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
          emb.faceBoundary emb.faces
          (fun e' => planeEmbeddingWithBoundary_totalIncidenceCount_le_two emb e')
          p.2 g.2 f.2 hpg hpe hgeFace hef
    have hpf : p = f := by
      rcases hfp_or_hfg with hfp | hfg
      · exact Subtype.ext hfp.symm
      · have : f = g := Subtype.ext hfg
        subst this
        exact False.elim ((Finset.mem_erase.1 he).1 hge.symm)
    exact Or.inr ⟨g, hg, by simpa [hpf] using hparentg, hge⟩

/-- Direct boundary-aware annihilator theorem from annulus BFS construction once each peeled face
has an honestly oriented witness edge on some strictly earlier face. This isolates the remaining
geometric burden in the annulus route to witness-edge orientation, rather than to the older
interior-dual wrappers. -/
theorem zero_on_allEdges_of_planarBoundaryAnnulusConstruction_of_parentWitness
    {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hparentWitness : data.ParentWitnessOrientation)
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0)
    (horth : ∀ f ∈ data.peelFaces,
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
    (data :=
      data.toPlanarBoundaryWellFoundedFacePeelWitnessData_of_parentWitness hparentWitness)
    (hzeroBoundary := hzeroBoundary) (horth := horth)

/-- Graph-level existence form of the exact strengthened construction-side orientation surface. -/
def AdmitsPlanarBoundaryAnnulusConstructionParentWitnessOrientation (G : SimpleGraph V) : Prop :=
  ∃ emb : PlaneEmbeddingWithBoundary G,
    ∃ data : PlanarBoundaryAnnulusConstruction emb,
      data.ParentWitnessOrientation

theorem admitsPlanarBoundaryWellFoundedFacePeelWitnessData_of_admitsPlanarBoundaryAnnulusConstructionParentWitnessOrientation
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryAnnulusConstructionParentWitnessOrientation G) :
    AdmitsPlanarBoundaryWellFoundedFacePeelWitnessData G := by
  rcases hG with ⟨emb, data, horient⟩
  exact ⟨emb, ⟨data.toPlanarBoundaryWellFoundedFacePeelWitnessData_of_parentWitness horient⟩⟩

/-- Exact strengthened continuation theorem on the current concrete face-partition shell:
the existing face-partition data becomes sufficient for the theorem-4.9 route precisely after
adding the explicit parent-witness orientation property on the same construction. -/
theorem
    admitsPlanarBoundaryWellFoundedFacePeelWitnessData_of_exists_planarBoundaryAnnulusConstructionFacePartitionData_and_parentWitnessOrientation
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryAnnulusConstructionFacePartitionData emb,
        data.construction.ParentWitnessOrientation) :
    AdmitsPlanarBoundaryWellFoundedFacePeelWitnessData G := by
  rcases hG with ⟨emb, data, horient⟩
  exact ⟨emb, ⟨
    data.construction.toPlanarBoundaryWellFoundedFacePeelWitnessData_of_parentWitness
      horient⟩⟩

/-- Existential graph-level annihilator form of the exact strengthened construction-side witness
orientation surface. -/
theorem zero_on_allEdges_of_exists_planarBoundaryAnnulusConstruction_and_parentWitnessOrientation
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (hdata : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryAnnulusConstruction emb,
        data.ParentWitnessOrientation ∧
        (∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0) ∧
        (∀ f ∈ data.peelFaces,
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
  rcases hdata with ⟨emb, data, horient, hzeroBoundary, horth⟩
  exact zero_on_allEdges_of_planarBoundaryAnnulusConstruction_of_parentWitness
    (emb := emb) (data := data) (hparentWitness := horient)
    (C := C) (htait := htait) (z := z)
    (hzeroBoundary := hzeroBoundary) (horth := horth)

end Mettapedia.GraphTheory.FourColor
