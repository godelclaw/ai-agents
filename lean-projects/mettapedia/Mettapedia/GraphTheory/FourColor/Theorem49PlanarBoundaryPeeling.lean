import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryEmbedding
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryCertificate
import Mettapedia.GraphTheory.FourColor.Theorem49CertificateBuilder
import Mettapedia.GraphTheory.FourColor.Theorem49InteriorDualForest
import Mettapedia.GraphTheory.WalkPlanarEmbeddingWithBoundary

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- A directed dependency edge in the boundary-aware witness-cover interface.  The edge points from
a peeled face `f` to a peeled face `g` when the witness of `g` occurs as a non-boundary
non-witness remainder edge on `f`. -/
def PlanarBoundaryWitnessRemainderDependency {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G)
    (peelFaces : Finset (AmbientFace emb.faces))
    (witnessEdge : AmbientFace emb.faces → G.edgeSet)
    (f g : AmbientFace emb.faces) : Prop :=
  f ∈ peelFaces ∧
    g ∈ peelFaces ∧
      witnessEdge g ∈ (emb.faceBoundary f.1).erase (witnessEdge f) ∧
        witnessEdge g ∉ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces

/-- Boundary-aware well-founded-parent witness-cover data for the Theorem 4.9 annihilator step.
This removes the explicit numeric height parameter from the collar-peeling interface: it is enough
to specify peeled faces, a parent relation on those faces with no infinite descent, and witness
edges whose remainder edges point either to the ambient boundary support or to children in that
well-founded parent relation. -/
structure PlanarBoundaryWellFoundedFacePeelWitnessData {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) where
  peelFaces : Finset (AmbientFace emb.faces)
  parentFace : AmbientFace emb.faces → Option (AmbientFace emb.faces)
  witnessEdge : AmbientFace emb.faces → G.edgeSet
  hWF : WellFounded (ParentRel parentFace)
  hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image witnessEdge
  hwitness : ∀ f ∈ peelFaces, witnessEdge f ∈ emb.faceBoundary f.1
  hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase (witnessEdge f),
    e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
      ∃ g ∈ peelFaces, parentFace g = some f ∧ witnessEdge g = e

/-- In a well-founded witness-cover package, a non-boundary remainder edge whose value is the
witness edge of a peeled face identifies that peeled face as a child, provided the witness choice
is injective on peeled faces.  This extracts the real dependency relation hidden in `hchildren`. -/
theorem PlanarBoundaryWellFoundedFacePeelWitnessData.parentFace_eq_some_of_witnessEdge_mem_erase_of_not_selectedBoundarySupport
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryWellFoundedFacePeelWitnessData emb)
    (hinj : ∀ {u v : AmbientFace emb.faces}, u ∈ data.peelFaces → v ∈ data.peelFaces →
      data.witnessEdge u = data.witnessEdge v → u = v)
    {f g : AmbientFace emb.faces}
    (hf : f ∈ data.peelFaces) (hg : g ∈ data.peelFaces)
    (hmem : data.witnessEdge g ∈ (emb.faceBoundary f.1).erase (data.witnessEdge f))
    (hnotBoundary :
      data.witnessEdge g ∉ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) :
    data.parentFace g = some f := by
  rcases data.hchildren f hf (data.witnessEdge g) hmem with
    hboundary | ⟨u, hu, huf, hwu⟩
  · exact (hnotBoundary hboundary).elim
  · have hug : u = g := hinj hu hg hwu
    simpa [hug] using huf

/-- A two-cycle of non-boundary remainder-witness dependencies is incompatible with
well-founded parent witness-cover data when the witness choice is injective on peeled faces. -/
theorem PlanarBoundaryWellFoundedFacePeelWitnessData.false_of_witnessEdge_twoCycle_of_injective_witness
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryWellFoundedFacePeelWitnessData emb)
    (hinj : ∀ {u v : AmbientFace emb.faces}, u ∈ data.peelFaces → v ∈ data.peelFaces →
      data.witnessEdge u = data.witnessEdge v → u = v)
    {f g : AmbientFace emb.faces}
    (hf : f ∈ data.peelFaces) (hg : g ∈ data.peelFaces)
    (hfg : data.witnessEdge g ∈ (emb.faceBoundary f.1).erase (data.witnessEdge f))
    (hgf : data.witnessEdge f ∈ (emb.faceBoundary g.1).erase (data.witnessEdge g))
    (hfgNotBoundary :
      data.witnessEdge g ∉ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (hgfNotBoundary :
      data.witnessEdge f ∉ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) :
    False := by
  have hparentG : data.parentFace g = some f :=
    data.parentFace_eq_some_of_witnessEdge_mem_erase_of_not_selectedBoundarySupport
      hinj hf hg hfg hfgNotBoundary
  have hparentF : data.parentFace f = some g :=
    data.parentFace_eq_some_of_witnessEdge_mem_erase_of_not_selectedBoundarySupport
      hinj hg hf hgf hgfNotBoundary
  exact
    (not_wellFounded_parentRel_of_twoCycle data.parentFace hparentG hparentF)
      data.hWF

/-- A three-cycle of non-boundary remainder-witness dependencies is incompatible with
well-founded parent witness-cover data when the witness choice is injective on peeled faces.  This
is the generic form of the wheel-style obstruction: the dependencies force a strict cycle in the
canonical parent-height rank. -/
theorem PlanarBoundaryWellFoundedFacePeelWitnessData.false_of_witnessEdge_threeCycle_of_injective_witness
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryWellFoundedFacePeelWitnessData emb)
    (hinj : ∀ {u v : AmbientFace emb.faces}, u ∈ data.peelFaces → v ∈ data.peelFaces →
      data.witnessEdge u = data.witnessEdge v → u = v)
    {f0 f1 f2 : AmbientFace emb.faces}
    (hf0 : f0 ∈ data.peelFaces) (hf1 : f1 ∈ data.peelFaces) (hf2 : f2 ∈ data.peelFaces)
    (h01 : data.witnessEdge f1 ∈ (emb.faceBoundary f0.1).erase (data.witnessEdge f0))
    (h12 : data.witnessEdge f2 ∈ (emb.faceBoundary f1.1).erase (data.witnessEdge f1))
    (h20 : data.witnessEdge f0 ∈ (emb.faceBoundary f2.1).erase (data.witnessEdge f2))
    (h01NotBoundary :
      data.witnessEdge f1 ∉ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (h12NotBoundary :
      data.witnessEdge f2 ∉ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (h20NotBoundary :
      data.witnessEdge f0 ∉ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) :
    False := by
  have hp10 : data.parentFace f1 = some f0 :=
    data.parentFace_eq_some_of_witnessEdge_mem_erase_of_not_selectedBoundarySupport
      hinj hf0 hf1 h01 h01NotBoundary
  have hp21 : data.parentFace f2 = some f1 :=
    data.parentFace_eq_some_of_witnessEdge_mem_erase_of_not_selectedBoundarySupport
      hinj hf1 hf2 h12 h12NotBoundary
  have hp02 : data.parentFace f0 = some f2 :=
    data.parentFace_eq_some_of_witnessEdge_mem_erase_of_not_selectedBoundarySupport
      hinj hf2 hf0 h20 h20NotBoundary
  exact false_of_isChain_parentRel_and_getLast_parent_head
    data.parentFace data.hWF
    (cycle := [f0, f1, f2])
    (by simp)
    (by
      exact List.IsChain.cons_cons hp10
        (List.IsChain.cons_cons hp21 (by simp)))
    hp02

/-- Any nonempty finite cycle of non-boundary remainder-witness dependencies is incompatible with
well-founded parent witness-cover data when the witness choice is injective on peeled faces. -/
theorem PlanarBoundaryWellFoundedFacePeelWitnessData.false_of_witnessRemainderDependency_cycle_of_injective_witness
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryWellFoundedFacePeelWitnessData emb)
    (hinj : ∀ {u v : AmbientFace emb.faces}, u ∈ data.peelFaces → v ∈ data.peelFaces →
      data.witnessEdge u = data.witnessEdge v → u = v)
    {cycle : List (AmbientFace emb.faces)}
    (hne : cycle ≠ [])
    (hchain : List.IsChain
      (PlanarBoundaryWitnessRemainderDependency emb data.peelFaces data.witnessEdge) cycle)
    (hloop : PlanarBoundaryWitnessRemainderDependency emb data.peelFaces data.witnessEdge
      (cycle.getLast hne) (cycle.head hne)) :
    False := by
  have hparentChain : List.IsChain (ParentRel data.parentFace) cycle := by
    exact hchain.imp (by
      intro f g hdep
      rcases hdep with ⟨hf, hg, hmem, hnotBoundary⟩
      exact
        data.parentFace_eq_some_of_witnessEdge_mem_erase_of_not_selectedBoundarySupport
          hinj hf hg hmem hnotBoundary)
  rcases hloop with ⟨hlast, hhead, hmem, hnotBoundary⟩
  have hparentLoop : ParentRel data.parentFace (cycle.getLast hne) (cycle.head hne) :=
      data.parentFace_eq_some_of_witnessEdge_mem_erase_of_not_selectedBoundarySupport
        hinj hlast hhead hmem hnotBoundary
  exact false_of_isChain_parentRel_and_getLast_parent_head
    data.parentFace data.hWF hne hparentChain hparentLoop

/-- Graph-level existence form of the boundary-aware well-founded-parent witness-cover target. -/
def AdmitsPlanarBoundaryWellFoundedFacePeelWitnessData
    (G : SimpleGraph V) : Prop :=
  ∃ emb : PlaneEmbeddingWithBoundary G,
    Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb)

/-- A boundary-aware well-founded-parent witness-cover package canonically yields the attached-face
peel certificate consumed by the planarity-side Theorem 4.9 bridge. -/
noncomputable def
    PlanarBoundaryWellFoundedFacePeelWitnessData.toBoundaryRootedFacePeelCertificate
    {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryWellFoundedFacePeelWitnessData emb) :
    BoundaryRootedFacePeelCertificate emb.faces.attach
      (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary) := by
  let subBoundary : AmbientFace emb.faces → Finset G.edgeSet :=
    ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary
  exact boundaryRootedFacePeelCertificate_of_wellFounded_parentFacePeelWitnessCover
    (allFaces := emb.faces.attach) (peelFaces := data.peelFaces)
    (faceBoundary := subBoundary) (parentFace := data.parentFace)
    (witnessEdge := data.witnessEdge) (hWF := data.hWF)
    (hcover := by
      simpa [subBoundary, interiorEdgeSupport_ambientFaceBoundary_eq
        (faceBoundary := emb.faceBoundary) (allFaces := emb.faces)] using data.hcover)
    (hwitness := by
      intro f hf
      simpa [subBoundary, ambientFaceBoundary] using data.hwitness f hf)
    (hchildren := by
      intro f hf e he
      have he' : e ∈ (emb.faceBoundary f.1).erase (data.witnessEdge f) := by
        simpa [subBoundary, ambientFaceBoundary] using he
      rcases data.hchildren f hf e he' with hboundary | ⟨g, hg, hgf, hge⟩
      · exact Or.inl <| by
          simpa [subBoundary, selectedBoundarySupport_ambientFaceBoundary_eq
            (faceBoundary := emb.faceBoundary) (allFaces := emb.faces)] using hboundary
      · exact Or.inr ⟨g, hg, hgf, hge⟩)

/-- The weakest current boundary-aware well-founded-parent witness-cover package canonically
yields the graph-level attached-face certificate surface consumed by the boundary-aware Theorem 4.9
bridge. -/
noncomputable def
    PlanarBoundaryWellFoundedFacePeelWitnessData.toPlanarBoundaryAttachedRootedFacePeelCertificate
    {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryWellFoundedFacePeelWitnessData emb) :
    PlanarBoundaryAttachedRootedFacePeelCertificate G where
  embedding := emb
  certificate := data.toBoundaryRootedFacePeelCertificate

theorem
    admitsPlanarBoundaryAttachedRootedFacePeelCertificate_of_admitsPlanarBoundaryWellFoundedFacePeelWitnessData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryWellFoundedFacePeelWitnessData G) :
    AdmitsPlanarBoundaryAttachedRootedFacePeelCertificate G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨data.toPlanarBoundaryAttachedRootedFacePeelCertificate⟩

/-- Boundary-aware global annihilator form of the well-founded-parent witness-cover interface. -/
theorem zero_on_allEdges_of_planarBoundaryWellFoundedFacePeelWitnessData
    {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G)
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (data : PlanarBoundaryWellFoundedFacePeelWitnessData emb)
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
  let subBoundary : AmbientFace emb.faces → Finset G.edgeSet :=
    ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary
  have horth' :
      ∀ f ∈ data.peelFaces,
        ∀ γ, γ ≠ 0 → γ ≠ C (data.witnessEdge f) →
          chainDot
              (boundaryBicoloredEdges C
                (C (data.witnessEdge f))
                (C (data.witnessEdge f) + γ)
                (subBoundary f))
              z
              (polarizedFaceGenerator C
                (C (data.witnessEdge f))
                (C (data.witnessEdge f) + γ)
                (subBoundary f)) = 0 := by
    intro f hf γ hγ0 hγd
    simpa [subBoundary, ambientFaceBoundary] using horth f hf γ hγ0 hγd
  have hzeroSupport :
      ∀ e ∈ emb.faces.attach.biUnion subBoundary, z e = 0 := by
    refine zero_on_ambientFaceSupport_of_wellFounded_parentFacePeelWitnessCover
      (C := C) (htait := htait) (z := z)
      (allFaces := emb.faces.attach) (peelFaces := data.peelFaces)
      (faceBoundary := subBoundary) (parentFace := data.parentFace)
      (witnessEdge := data.witnessEdge) (hWF := data.hWF) ?_ ?_ ?_ ?_ ?_ horth'
    · simpa [subBoundary, interiorEdgeSupport_ambientFaceBoundary_eq
        (faceBoundary := emb.faceBoundary) (allFaces := emb.faces)] using data.hcover
    · intro f hf
      simpa [subBoundary, ambientFaceBoundary] using data.hwitness f hf
    · intro f hf e he
      have he' : e ∈ (emb.faceBoundary f.1).erase (data.witnessEdge f) := by
        simpa [subBoundary, ambientFaceBoundary] using he
      rcases data.hchildren f hf e he' with hboundary | ⟨g, hg, hgf, hge⟩
      · exact Or.inl <| by
          simpa [subBoundary, selectedBoundarySupport_ambientFaceBoundary_eq
            (faceBoundary := emb.faceBoundary) (allFaces := emb.faces)] using hboundary
      · exact Or.inr ⟨g, hg, hgf, hge⟩
    · intro e
      rw [totalIncidenceCount_ambientFaceBoundary_eq
        (faceBoundary := emb.faceBoundary) (allFaces := emb.faces)]
      exact planeEmbeddingWithBoundary_totalIncidenceCount_le_two emb e
    · intro e he
      rw [selectedBoundarySupport_ambientFaceBoundary_eq
        (faceBoundary := emb.faceBoundary) (allFaces := emb.faces)] at he
      exact hzeroBoundary e he
  intro e
  apply hzeroSupport e
  rw [biUnion_attach_ambientFaceBoundary_eq
    (faceBoundary := emb.faceBoundary) (allFaces := emb.faces)]
  simpa [PlaneEmbeddingWithBoundary.faceSupport] using emb.mem_faceSupport e

/-- Existential boundary-aware global annihilator form of the well-founded-parent witness-cover
interface. -/
theorem zero_on_allEdges_of_exists_planarBoundaryWellFoundedFacePeelWitnessData
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (hdata : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryWellFoundedFacePeelWitnessData emb,
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
  rcases hdata with ⟨emb, data, hzeroBoundary, horth⟩
  exact zero_on_allEdges_of_planarBoundaryWellFoundedFacePeelWitnessData
    (emb := emb) (C := C) (htait := htait) (z := z) (data := data)
    (hzeroBoundary := hzeroBoundary) (horth := horth)

/-- Boundary-aware height-sorted witness-cover data for the Theorem 4.9 annihilator step. This is
the planarity-side interface closest to the paper's outside-in collar peeling: one specifies only a
set of peeled ambient faces, a witness interior edge for each peeled face, and a height that makes
all non-witness remainder edges flow strictly toward higher layers. No explicit interior-dual root or
parent structure is required. -/
structure PlanarBoundaryHeightOrderedFacePeelWitnessData {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) where
  peelFaces : Finset (AmbientFace emb.faces)
  witnessEdge : AmbientFace emb.faces → G.edgeSet
  height : AmbientFace emb.faces → ℕ
  hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image witnessEdge
  hwitness : ∀ f ∈ peelFaces, witnessEdge f ∈ emb.faceBoundary f.1
  hrest : ∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase (witnessEdge f),
    e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
      ∃ g ∈ peelFaces, witnessEdge g = e ∧ height f < height g

/-- Any covered interior edge makes the finite peeled-face set nonempty. -/
theorem PlanarBoundaryHeightOrderedFacePeelWitnessData.peelFaces_nonempty_of_mem_interiorEdgeSupport
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb)
    {e : G.edgeSet} (he : e ∈ interiorEdgeSupport emb.faceBoundary emb.faces) :
    data.peelFaces.Nonempty := by
  rcases Finset.mem_image.1 (data.hcover he) with ⟨f, hf, _hfe⟩
  exact ⟨f, hf⟩

/-- Any nonempty height-ordered witness-cover package has a terminal peeled face: all
non-witness remainder edges of that face already lie on the selected boundary support. -/
theorem PlanarBoundaryHeightOrderedFacePeelWitnessData.exists_terminal_face_selectedBoundary_remainders
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb)
    (hne : data.peelFaces.Nonempty) :
    ∃ f ∈ data.peelFaces,
      ∀ e ∈ (emb.faceBoundary f.1).erase (data.witnessEdge f),
        e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces := by
  classical
  let heights := data.peelFaces.image data.height
  have hheights : heights.Nonempty := hne.image data.height
  rcases Finset.mem_image.1 (Finset.max'_mem heights hheights) with
    ⟨f, hf, hfmax⟩
  refine ⟨f, hf, ?_⟩
  intro e he
  rcases data.hrest f hf e he with hboundary | ⟨g, hg, _hge, hlt⟩
  · exact hboundary
  · have hgmax : data.height g ≤ heights.max' hheights :=
      Finset.le_max' heights (data.height g) (Finset.mem_image.2 ⟨g, hg, rfl⟩)
    exact False.elim ((not_lt_of_ge (by simpa [hfmax] using hgmax)) hlt)

/-- Interior-edge form of the terminal-face lemma. -/
theorem PlanarBoundaryHeightOrderedFacePeelWitnessData.exists_terminal_face_selectedBoundary_remainders_of_mem_interiorEdgeSupport
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb)
    {e : G.edgeSet} (he : e ∈ interiorEdgeSupport emb.faceBoundary emb.faces) :
    ∃ f ∈ data.peelFaces,
      ∀ e ∈ (emb.faceBoundary f.1).erase (data.witnessEdge f),
        e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces := by
  exact data.exists_terminal_face_selectedBoundary_remainders
    (data.peelFaces_nonempty_of_mem_interiorEdgeSupport he)

/-- Nonempty-interior-edge form of the terminal-face lemma. -/
theorem PlanarBoundaryHeightOrderedFacePeelWitnessData.exists_terminal_face_selectedBoundary_remainders_of_interiorEdgeSupport_nonempty
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb)
    (hInterior : (interiorEdgeSupport emb.faceBoundary emb.faces).Nonempty) :
    ∃ f ∈ data.peelFaces,
      ∀ e ∈ (emb.faceBoundary f.1).erase (data.witnessEdge f),
        e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces := by
  rcases hInterior with ⟨e, he⟩
  exact data.exists_terminal_face_selectedBoundary_remainders_of_mem_interiorEdgeSupport he

/-- In height-ordered witness-cover data, a non-boundary remainder edge whose value is the witness
edge of a peeled face must point to a strictly higher peeled face, provided witness choices are
injective on peeled faces. -/
theorem PlanarBoundaryHeightOrderedFacePeelWitnessData.height_lt_of_witnessEdge_mem_erase_of_not_selectedBoundarySupport
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb)
    (hinj : ∀ {u v : AmbientFace emb.faces}, u ∈ data.peelFaces → v ∈ data.peelFaces →
      data.witnessEdge u = data.witnessEdge v → u = v)
    {f g : AmbientFace emb.faces}
    (hf : f ∈ data.peelFaces) (hg : g ∈ data.peelFaces)
    (hmem : data.witnessEdge g ∈ (emb.faceBoundary f.1).erase (data.witnessEdge f))
    (hnotBoundary :
      data.witnessEdge g ∉ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) :
    data.height f < data.height g := by
  rcases data.hrest f hf (data.witnessEdge g) hmem with
    hboundary | ⟨u, hu, hwu, hlt⟩
  · exact (hnotBoundary hboundary).elim
  · have hug : u = g := hinj hu hg hwu
    simpa [hug] using hlt

/-- A two-cycle of non-boundary remainder-witness dependencies is incompatible with
height-ordered witness-cover data when the witness choice is injective on peeled faces. -/
theorem PlanarBoundaryHeightOrderedFacePeelWitnessData.false_of_witnessEdge_twoCycle_of_injective_witness
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb)
    (hinj : ∀ {u v : AmbientFace emb.faces}, u ∈ data.peelFaces → v ∈ data.peelFaces →
      data.witnessEdge u = data.witnessEdge v → u = v)
    {f g : AmbientFace emb.faces}
    (hf : f ∈ data.peelFaces) (hg : g ∈ data.peelFaces)
    (hfg : data.witnessEdge g ∈ (emb.faceBoundary f.1).erase (data.witnessEdge f))
    (hgf : data.witnessEdge f ∈ (emb.faceBoundary g.1).erase (data.witnessEdge g))
    (hfgNotBoundary :
      data.witnessEdge g ∉ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (hgfNotBoundary :
      data.witnessEdge f ∉ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) :
    False := by
  have hltFG : data.height f < data.height g :=
    data.height_lt_of_witnessEdge_mem_erase_of_not_selectedBoundarySupport
      hinj hf hg hfg hfgNotBoundary
  have hltGF : data.height g < data.height f :=
    data.height_lt_of_witnessEdge_mem_erase_of_not_selectedBoundarySupport
      hinj hg hf hgf hgfNotBoundary
  exact (not_lt_of_ge (le_of_lt hltGF)) hltFG

/-- A three-cycle of non-boundary remainder-witness dependencies is incompatible with
height-ordered witness-cover data when the witness choice is injective on peeled faces. -/
theorem PlanarBoundaryHeightOrderedFacePeelWitnessData.false_of_witnessEdge_threeCycle_of_injective_witness
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb)
    (hinj : ∀ {u v : AmbientFace emb.faces}, u ∈ data.peelFaces → v ∈ data.peelFaces →
      data.witnessEdge u = data.witnessEdge v → u = v)
    {f0 f1 f2 : AmbientFace emb.faces}
    (hf0 : f0 ∈ data.peelFaces) (hf1 : f1 ∈ data.peelFaces) (hf2 : f2 ∈ data.peelFaces)
    (h01 : data.witnessEdge f1 ∈ (emb.faceBoundary f0.1).erase (data.witnessEdge f0))
    (h12 : data.witnessEdge f2 ∈ (emb.faceBoundary f1.1).erase (data.witnessEdge f1))
    (h20 : data.witnessEdge f0 ∈ (emb.faceBoundary f2.1).erase (data.witnessEdge f2))
    (h01NotBoundary :
      data.witnessEdge f1 ∉ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (h12NotBoundary :
      data.witnessEdge f2 ∉ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (h20NotBoundary :
      data.witnessEdge f0 ∉ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) :
    False := by
  have hlt01 : data.height f0 < data.height f1 :=
    data.height_lt_of_witnessEdge_mem_erase_of_not_selectedBoundarySupport
      hinj hf0 hf1 h01 h01NotBoundary
  have hlt12 : data.height f1 < data.height f2 :=
    data.height_lt_of_witnessEdge_mem_erase_of_not_selectedBoundarySupport
      hinj hf1 hf2 h12 h12NotBoundary
  have hlt20 : data.height f2 < data.height f0 :=
    data.height_lt_of_witnessEdge_mem_erase_of_not_selectedBoundarySupport
      hinj hf2 hf0 h20 h20NotBoundary
  exact false_of_isChain_height_lt_and_getLast_lt_head
    data.height
    (cycle := [f0, f1, f2])
    (by simp)
    (by
      exact List.IsChain.cons_cons hlt01
        (List.IsChain.cons_cons hlt12 (by simp)))
    hlt20

/-- Any nonempty finite cycle of non-boundary remainder-witness dependencies is incompatible with
height-ordered witness-cover data when the witness choice is injective on peeled faces. -/
theorem PlanarBoundaryHeightOrderedFacePeelWitnessData.false_of_witnessRemainderDependency_cycle_of_injective_witness
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb)
    (hinj : ∀ {u v : AmbientFace emb.faces}, u ∈ data.peelFaces → v ∈ data.peelFaces →
      data.witnessEdge u = data.witnessEdge v → u = v)
    {cycle : List (AmbientFace emb.faces)}
    (hne : cycle ≠ [])
    (hchain : List.IsChain
      (PlanarBoundaryWitnessRemainderDependency emb data.peelFaces data.witnessEdge) cycle)
    (hloop : PlanarBoundaryWitnessRemainderDependency emb data.peelFaces data.witnessEdge
      (cycle.getLast hne) (cycle.head hne)) :
    False := by
  have hheightChain : List.IsChain (fun f g => data.height f < data.height g) cycle := by
    exact hchain.imp (by
      intro f g hdep
      rcases hdep with ⟨hf, hg, hmem, hnotBoundary⟩
      exact data.height_lt_of_witnessEdge_mem_erase_of_not_selectedBoundarySupport
        hinj hf hg hmem hnotBoundary)
  rcases hloop with ⟨hlast, hhead, hmem, hnotBoundary⟩
  have hloopHeight : data.height (cycle.getLast hne) < data.height (cycle.head hne) :=
    data.height_lt_of_witnessEdge_mem_erase_of_not_selectedBoundarySupport
      hinj hlast hhead hmem hnotBoundary
  exact false_of_isChain_height_lt_and_getLast_lt_head
    data.height hne hheightChain hloopHeight

/-- Graph-level existence form of the boundary-aware height-sorted witness-cover target. This is a
direct annulus-side planarity endpoint: if the geometry produces such layered witness data, the
current Theorem 4.9 machinery already closes the annihilator route. -/
def AdmitsPlanarBoundaryHeightOrderedFacePeelWitnessData
    (G : SimpleGraph V) : Prop :=
  ∃ emb : PlaneEmbeddingWithBoundary G,
    Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb)

/-- A well-founded parent witness-cover package already carries the acyclic height data needed by
the height-ordered interface.  The canonical height is the parent-map rank: every child has height
one more than its parent, so child witnesses sit at strictly larger height. -/
noncomputable def
    PlanarBoundaryWellFoundedFacePeelWitnessData.toPlanarBoundaryHeightOrderedFacePeelWitnessData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryWellFoundedFacePeelWitnessData emb) :
    PlanarBoundaryHeightOrderedFacePeelWitnessData emb := by
  refine
    { peelFaces := data.peelFaces
      witnessEdge := data.witnessEdge
      height := parentHeight data.parentFace data.hWF
      hcover := data.hcover
      hwitness := data.hwitness
      hrest := ?_ }
  intro f hf e he
  rcases data.hchildren f hf e he with hboundary | ⟨g, hg, hgf, hge⟩
  · exact Or.inl hboundary
  · exact Or.inr
      ⟨g, hg, hge, parentHeight_lt_of_parent data.parentFace data.hWF hgf⟩

/-- Graph-level form of the acyclic parent-to-height conversion.  Thus the well-founded
parent-peeling surface is not merely a separate synthesis route: it can also feed the direct
height-ordered replacement surface. -/
theorem admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_of_admitsPlanarBoundaryWellFoundedFacePeelWitnessData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryWellFoundedFacePeelWitnessData G) :
    AdmitsPlanarBoundaryHeightOrderedFacePeelWitnessData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.toPlanarBoundaryHeightOrderedFacePeelWitnessData⟩⟩

/-- A boundary-aware height-sorted witness-cover package canonically yields the attached-face peel
certificate consumed by the planarity-side Theorem 4.9 bridge. -/
noncomputable def PlanarBoundaryHeightOrderedFacePeelWitnessData.toBoundaryRootedFacePeelCertificate
    {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb) :
    BoundaryRootedFacePeelCertificate emb.faces.attach
      (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary) := by
  let subBoundary : AmbientFace emb.faces → Finset G.edgeSet :=
    ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary
  exact boundaryRootedFacePeelCertificate_of_heightOrdered_facePeelWitnessCover
    (allFaces := emb.faces.attach) (faceBoundary := subBoundary)
    (faceOrder := heightOrderedFaceOrder data.peelFaces data.height)
    (witnessEdge := data.witnessEdge) (height := data.height)
    (hcover := by
      intro e he
      have he' : e ∈ interiorEdgeSupport emb.faceBoundary emb.faces := by
        simpa [subBoundary, interiorEdgeSupport_ambientFaceBoundary_eq
          (faceBoundary := emb.faceBoundary) (allFaces := emb.faces)] using he
      rcases Finset.mem_image.1 (data.hcover he') with
        ⟨f, hf, rfl⟩
      exact (mem_facePeelWitnessSupport_iff _ _).2
        ⟨f, (mem_heightOrderedFaceOrder_iff data.peelFaces data.height).2 hf, rfl⟩)
    (horder := heightOrderedFaceOrder_order data.peelFaces data.height)
    (hwitness := by
      intro f hf
      simpa [subBoundary, ambientFaceBoundary] using
        data.hwitness f ((mem_heightOrderedFaceOrder_iff data.peelFaces data.height).1 hf))
    (hrest := by
      intro f hf e he
      have hf' : f ∈ data.peelFaces :=
        (mem_heightOrderedFaceOrder_iff data.peelFaces data.height).1 hf
      have he' : e ∈ (emb.faceBoundary f.1).erase (data.witnessEdge f) := by
        simpa [subBoundary, ambientFaceBoundary] using he
      rcases data.hrest f hf' e he' with hboundary | ⟨g, hg, hge, hlt⟩
      · exact Or.inl <| by
          simpa [subBoundary, selectedBoundarySupport_ambientFaceBoundary_eq
            (faceBoundary := emb.faceBoundary) (allFaces := emb.faces)] using hboundary
      · exact Or.inr
          ⟨g, (mem_heightOrderedFaceOrder_iff data.peelFaces data.height).2 hg, hge, hlt⟩)

/-- Boundary-aware global annihilator form of the height-sorted witness-cover interface. This is
the closest current formal theorem to the paper's collar-peeling proof sketch: if the annulus
geometry yields a layered witness-cover package and the target function vanishes on the selected
boundary support, then it vanishes on all graph edges. -/
theorem zero_on_allEdges_of_planarBoundaryHeightOrderedFacePeelWitnessData
    {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G)
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb)
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
  let subBoundary : AmbientFace emb.faces → Finset G.edgeSet :=
    ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary
  have horth' :
      ∀ f ∈ data.peelFaces,
        ∀ γ, γ ≠ 0 → γ ≠ C (data.witnessEdge f) →
          chainDot
              (boundaryBicoloredEdges C
                (C (data.witnessEdge f))
                (C (data.witnessEdge f) + γ)
                (subBoundary f))
              z
              (polarizedFaceGenerator C
                (C (data.witnessEdge f))
                (C (data.witnessEdge f) + γ)
                (subBoundary f)) = 0 := by
    intro f hf γ hγ0 hγd
    simpa [subBoundary, ambientFaceBoundary] using horth f hf γ hγ0 hγd
  have hzeroSupport :
      ∀ e ∈ emb.faces.attach.biUnion subBoundary, z e = 0 := by
    refine zero_on_ambientFaceSupport_of_sortedHeightOrdered_facePeelWitnessCover
      (C := C) (htait := htait) (z := z)
      (allFaces := emb.faces.attach) (peelFaces := data.peelFaces)
      (faceBoundary := subBoundary) (witnessEdge := data.witnessEdge)
      (height := data.height) ?_ ?_ ?_ ?_ ?_ horth'
    · simpa [subBoundary, interiorEdgeSupport_ambientFaceBoundary_eq
        (faceBoundary := emb.faceBoundary) (allFaces := emb.faces)] using data.hcover
    · intro f hf
      simpa [subBoundary, ambientFaceBoundary] using data.hwitness f hf
    · intro f hf e he
      have he' : e ∈ (emb.faceBoundary f.1).erase (data.witnessEdge f) := by
        simpa [subBoundary, ambientFaceBoundary] using he
      rcases data.hrest f hf e he' with hboundary | ⟨g, hg, hge, hlt⟩
      · exact Or.inl <| by
          simpa [subBoundary, selectedBoundarySupport_ambientFaceBoundary_eq
            (faceBoundary := emb.faceBoundary) (allFaces := emb.faces)] using hboundary
      · exact Or.inr ⟨g, hg, hge, hlt⟩
    · intro e
      rw [totalIncidenceCount_ambientFaceBoundary_eq
        (faceBoundary := emb.faceBoundary) (allFaces := emb.faces)]
      exact planeEmbeddingWithBoundary_totalIncidenceCount_le_two emb e
    · intro e he
      rw [selectedBoundarySupport_ambientFaceBoundary_eq
        (faceBoundary := emb.faceBoundary) (allFaces := emb.faces)] at he
      exact hzeroBoundary e he
  intro e
  apply hzeroSupport e
  rw [biUnion_attach_ambientFaceBoundary_eq
    (faceBoundary := emb.faceBoundary) (allFaces := emb.faces)]
  simpa [PlaneEmbeddingWithBoundary.faceSupport] using emb.mem_faceSupport e

/-- Existential boundary-aware global annihilator form of the height-sorted witness-cover
interface. -/
theorem zero_on_allEdges_of_exists_planarBoundaryHeightOrderedFacePeelWitnessData
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (hdata : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
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
  rcases hdata with ⟨emb, data, hzeroBoundary, horth⟩
  exact zero_on_allEdges_of_planarBoundaryHeightOrderedFacePeelWitnessData
    (emb := emb) (C := C) (htait := htait) (z := z) (data := data)
    (hzeroBoundary := hzeroBoundary) (horth := horth)

/-- The root-free interior-dual well-founded-parent package canonically lowers to the weaker
boundary-aware well-founded-parent witness-cover interface. This exposes the current interior-dual
endpoint directly at the generic planarity-side theorem layer, without passing back through an
explicit numeric height. -/
noncomputable def
    planarBoundaryWellFoundedFacePeelWitnessData_of_interiorDualWellFoundedParentPeelData
    {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (data : InteriorDualWellFoundedParentPeelData emb.faces emb.faceBoundary) :
    PlanarBoundaryWellFoundedFacePeelWitnessData emb := by
  let witnessEdge : AmbientFace emb.faces → G.edgeSet :=
    parentSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
      data.parentFace data.fallbackEdge data.hparentAdj
  refine
    { peelFaces := data.peelFaces
      parentFace := data.parentFace
      witnessEdge := witnessEdge
      hWF := data.hWF
      hcover := ?_
      hwitness := ?_
      hchildren := ?_ }
  · simpa [witnessEdge] using data.hcover
  · intro f hf
    rcases data.hparent f hf with ⟨p, hfp⟩
    simpa [witnessEdge] using
      parentSharedInteriorEdgeOfPairwiseUnique_mem_faceBoundary
        emb.faceBoundary emb.faces data.hunique data.parentFace
        data.fallbackEdge data.hparentAdj hfp
  · intro f hf e he
    have hef : e ∈ emb.faceBoundary f.1 := (Finset.mem_erase.1 he).2
    rcases data.hchildren f hf e (by simpa [witnessEdge] using he) with
      hboundary | ⟨g, hg, hgf, heg⟩
    · exact Or.inl hboundary
    · refine Or.inr ⟨g, hg, hgf, ?_⟩
      exact parentSharedInteriorEdgeOfPairwiseUnique_eq_of_mem_faceBoundary
        emb.faceBoundary emb.faces data.hunique data.parentFace
        data.fallbackEdge data.hparentAdj data.hall hgf heg hef

theorem
    witnessEdge_planarBoundaryWellFoundedFacePeelWitnessData_of_interiorDualWellFoundedParentPeelData
    {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (data : InteriorDualWellFoundedParentPeelData emb.faces emb.faceBoundary)
    {f : AmbientFace emb.faces} :
    (planarBoundaryWellFoundedFacePeelWitnessData_of_interiorDualWellFoundedParentPeelData
      data).witnessEdge f =
      parentSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
        data.parentFace data.fallbackEdge data.hparentAdj f :=
  rfl

/-- The existing interior-dual height-parent package canonically lowers to the weaker
boundary-aware well-founded-parent witness-cover interface by restricting the parent map to peeled
faces and using the supplied strict height decrease to prove well foundedness. -/
noncomputable def
    planarBoundaryWellFoundedFacePeelWitnessData_of_interiorDualHeightParentPeelData
    {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (data : InteriorDualHeightParentPeelData emb.faces emb.faceBoundary) :
    PlanarBoundaryWellFoundedFacePeelWitnessData emb := by
  let peelParentFace : AmbientFace emb.faces → Option (AmbientFace emb.faces) :=
    fun f => if hf : f ∈ data.peelFaces then data.parentFace f else none
  have hparentAdj :
      ∀ {f p : AmbientFace emb.faces}, peelParentFace f = some p →
        (interiorDualSpanningForest emb.faceBoundary emb.faces).Adj f p := by
    intro f p hfp
    by_cases hf : f ∈ data.peelFaces
    · have hfp' : data.parentFace f = some p := by
        simpa [peelParentFace, hf] using hfp
      exact data.hparentAdj hfp'
    · simp [peelParentFace, hf] at hfp
  let oldWitness : AmbientFace emb.faces → G.edgeSet :=
    parentSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
      data.parentFace data.fallbackEdge data.hparentAdj
  let witnessEdge : AmbientFace emb.faces → G.edgeSet :=
    parentSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
      peelParentFace data.fallbackEdge hparentAdj
  have hwitnessEq : ∀ f ∈ data.peelFaces, witnessEdge f = oldWitness f := by
    intro f hf
    simp [witnessEdge, oldWitness, parentSharedInteriorEdgeOfPairwiseUnique, peelParentFace, hf]
  have hWF : WellFounded (ParentRel peelParentFace) := by
    refine wellFounded_parentRel_of_lt_height peelParentFace data.height ?_
    intro g f hgf
    by_cases hg : g ∈ data.peelFaces
    · have hgf' : data.parentFace g = some f := by
        simpa [peelParentFace, hg] using hgf
      exact data.hheight g hg f hgf'
    · simp [peelParentFace, hg] at hgf
  refine
    { peelFaces := data.peelFaces
      parentFace := peelParentFace
      witnessEdge := witnessEdge
      hWF := hWF
      hcover := ?_
      hwitness := ?_
      hchildren := ?_ }
  · intro e he
    rcases Finset.mem_image.1 (data.hcover he) with ⟨f, hf, hfe⟩
    exact Finset.mem_image.2 ⟨f, hf, by
      rw [hwitnessEq f hf]
      exact hfe⟩
  · intro f hf
    rcases data.hparent f hf with ⟨p, hfp⟩
    rw [hwitnessEq f hf]
    exact
      parentSharedInteriorEdgeOfPairwiseUnique_mem_faceBoundary
        emb.faceBoundary emb.faces data.hunique data.parentFace
        data.fallbackEdge data.hparentAdj hfp
  · intro f hf e he
    have hef : e ∈ emb.faceBoundary f.1 := (Finset.mem_erase.1 he).2
    have he' : e ∈ (emb.faceBoundary f.1).erase
        (parentSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
          data.parentFace data.fallbackEdge data.hparentAdj f) := by
      rw [hwitnessEq f hf] at he
      exact he
    rcases data.hchildren f hf e he' with hboundary | ⟨g, hg, hgf, heg⟩
    · exact Or.inl hboundary
    · refine Or.inr ⟨g, hg, ?_, ?_⟩
      · simpa [peelParentFace, hg] using hgf
      · calc
          witnessEdge g = oldWitness g := hwitnessEq g hg
          _ = e := by
            exact parentSharedInteriorEdgeOfPairwiseUnique_eq_of_mem_faceBoundary
              emb.faceBoundary emb.faces data.hunique data.parentFace
              data.fallbackEdge data.hparentAdj data.hall hgf heg hef

theorem
    witnessEdge_planarBoundaryWellFoundedFacePeelWitnessData_of_interiorDualHeightParentPeelData
    {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (data : InteriorDualHeightParentPeelData emb.faces emb.faceBoundary)
    {f : AmbientFace emb.faces} (hf : f ∈ data.peelFaces) :
    (planarBoundaryWellFoundedFacePeelWitnessData_of_interiorDualHeightParentPeelData
      data).witnessEdge f =
      parentSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
        data.parentFace data.fallbackEdge data.hparentAdj f := by
  let peelParentFace : AmbientFace emb.faces → Option (AmbientFace emb.faces) :=
    fun f => if hmem : f ∈ data.peelFaces then data.parentFace f else none
  have hparentAdj :
      ∀ {u p : AmbientFace emb.faces}, peelParentFace u = some p →
        (interiorDualSpanningForest emb.faceBoundary emb.faces).Adj u p := by
    intro u p hup
    by_cases hu : u ∈ data.peelFaces
    · have hup' : data.parentFace u = some p := by
        simpa [peelParentFace, hu] using hup
      exact data.hparentAdj hup'
    · simp [peelParentFace, hu] at hup
  let oldWitness : AmbientFace emb.faces → G.edgeSet :=
    parentSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
      data.parentFace data.fallbackEdge data.hparentAdj
  let witnessEdge : AmbientFace emb.faces → G.edgeSet :=
    parentSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
      peelParentFace data.fallbackEdge hparentAdj
  have hwitnessEq : witnessEdge f = oldWitness f := by
    simp [witnessEdge, oldWitness, parentSharedInteriorEdgeOfPairwiseUnique, peelParentFace, hf]
  simpa [planarBoundaryWellFoundedFacePeelWitnessData_of_interiorDualHeightParentPeelData,
    oldWitness] using hwitnessEq

/-- The existing interior-dual height-parent package canonically lowers to the more primitive
boundary-aware height-sorted witness-cover interface. This shows the new annulus-side theorem
layer is genuinely weaker than the current interior-dual formulation. -/
noncomputable def
    planarBoundaryHeightOrderedFacePeelWitnessData_of_interiorDualHeightParentPeelData
    {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (data : InteriorDualHeightParentPeelData emb.faces emb.faceBoundary) :
    PlanarBoundaryHeightOrderedFacePeelWitnessData emb := by
  let witnessEdge : AmbientFace emb.faces → G.edgeSet :=
    parentSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
      data.parentFace data.fallbackEdge data.hparentAdj
  refine
    { peelFaces := data.peelFaces
      witnessEdge := witnessEdge
      height := data.height
      hcover := ?_
      hwitness := ?_
      hrest := ?_ }
  · simpa [witnessEdge] using data.hcover
  · intro f hf
    rcases data.hparent f hf with ⟨p, hfp⟩
    simpa [witnessEdge] using
      parentSharedInteriorEdgeOfPairwiseUnique_mem_faceBoundary
        emb.faceBoundary emb.faces data.hunique data.parentFace
        data.fallbackEdge data.hparentAdj hfp
  · intro f hf e he
    have hef : e ∈ emb.faceBoundary f.1 := (Finset.mem_erase.1 he).2
    rcases data.hchildren f hf e he with hboundary | ⟨g, hg, hgf, heg⟩
    · exact Or.inl hboundary
    · refine Or.inr ⟨g, hg, ?_, data.hheight g hg f hgf⟩
      exact parentSharedInteriorEdgeOfPairwiseUnique_eq_of_mem_faceBoundary
        emb.faceBoundary emb.faces data.hunique data.parentFace
        data.fallbackEdge data.hparentAdj data.hall hgf heg hef

theorem admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_of_exists_interiorDualHeightParentPeelData
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (InteriorDualHeightParentPeelData emb.faces emb.faceBoundary)) :
    AdmitsPlanarBoundaryHeightOrderedFacePeelWitnessData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨planarBoundaryHeightOrderedFacePeelWitnessData_of_interiorDualHeightParentPeelData
    data⟩⟩

theorem admitsPlanarBoundaryWellFoundedFacePeelWitnessData_of_exists_interiorDualHeightParentPeelData
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (InteriorDualHeightParentPeelData emb.faces emb.faceBoundary)) :
    AdmitsPlanarBoundaryWellFoundedFacePeelWitnessData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨planarBoundaryWellFoundedFacePeelWitnessData_of_interiorDualHeightParentPeelData
    data⟩⟩

theorem admitsPlanarBoundaryWellFoundedFacePeelWitnessData_of_exists_interiorDualWellFoundedParentPeelData
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (InteriorDualWellFoundedParentPeelData emb.faces emb.faceBoundary)) :
    AdmitsPlanarBoundaryWellFoundedFacePeelWitnessData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨
    planarBoundaryWellFoundedFacePeelWitnessData_of_interiorDualWellFoundedParentPeelData
      data⟩⟩

/-- The strongest current boundary-root adjacency-distance interior-dual package canonically
lowers directly to the boundary-aware height-ordered witness-cover interface, with witness edges
chosen as the rooted shared interior edges toward the separated boundary root set. This keeps the
paper's annulus-side root-distance layering visible on the planarity side instead of hiding it
behind a parent-based detour. -/
noncomputable def
    planarBoundaryHeightOrderedFacePeelWitnessData_of_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (data : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) :
    PlanarBoundaryHeightOrderedFacePeelWitnessData emb := by
  let T := interiorDualSpanningForest emb.faceBoundary emb.faces
  let rootFace : AmbientFace emb.faces → AmbientFace emb.faces :=
    interiorDualSpanningForestRoot emb.faceBoundary emb.faces data.roots
      data.hcoverRoots data.hsepRoots
  let witnessEdge : AmbientFace emb.faces → G.edgeSet :=
    rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
      rootFace data.fallbackEdge
  refine
    { peelFaces := data.peelFaces
      witnessEdge := witnessEdge
      height := fun f => T.dist f (rootFace f)
      hcover := ?_
      hwitness := ?_
      hrest := ?_ }
  · simpa [witnessEdge, rootFace] using data.hcover
  · intro f hf
    have hneq : f ≠ rootFace f :=
      ne_interiorDualSpanningForestRoot_of_mem_peelFaces_of_disjoint_roots
        emb.faceBoundary emb.faces data.peelFaces data.roots
        data.hcoverRoots data.hsepRoots
        (disjoint_peelFaces_roots_of_boundarySeparation
          emb.faceBoundary emb.faces data.peelFaces data.roots
          data.hpeelInterior data.hrootsBoundary)
        hf
    rcases parentTowardsRoot_spec_of_ne (T := T) (root := rootFace) (u := f)
        (h := reachable_interiorDualSpanningForestRoot
          emb.faceBoundary emb.faces data.roots data.hcoverRoots data.hsepRoots f)
        hneq with ⟨p, hfp, _hadj, _hdist⟩
    simpa [witnessEdge, rootFace] using
      rootedSharedInteriorEdgeOfPairwiseUnique_mem_faceBoundary
        emb.faceBoundary emb.faces data.hunique rootFace data.fallbackEdge hfp
  · intro f hf e he
    have hef : e ∈ emb.faceBoundary f.1 := (Finset.mem_erase.1 he).2
    rcases data.hchildren f hf e he with hboundary | ⟨g, hg, hadj, heg, hlt⟩
    · exact Or.inl hboundary
    · have hroot : rootFace f = rootFace g := by
        simpa [rootFace] using
          interiorDualSpanningForestRoot_eq_of_adj
            emb.faceBoundary emb.faces data.roots data.hcoverRoots data.hsepRoots hadj
      have hgf : parentTowardsRoot T rootFace g = some f := by
        exact parentTowardsRoot_eq_some_of_adj_of_lt_dist_of_componentConstantRoot
          T (interiorDualSpanningForest_isAcyclic emb.faceBoundary emb.faces)
          rootFace hadj
          (reachable_interiorDualSpanningForestRoot
            emb.faceBoundary emb.faces data.roots data.hcoverRoots data.hsepRoots f)
          (reachable_interiorDualSpanningForestRoot
            emb.faceBoundary emb.faces data.roots data.hcoverRoots data.hsepRoots g)
          hroot hlt
      refine Or.inr ⟨g, hg, ?_, hlt⟩
      exact rootedSharedInteriorEdgeOfPairwiseUnique_eq_of_mem_faceBoundary
        emb.faceBoundary emb.faces data.hunique rootFace data.fallbackEdge
        data.hall hgf heg hef

theorem admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_of_exists_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)) :
    AdmitsPlanarBoundaryHeightOrderedFacePeelWitnessData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨
    planarBoundaryHeightOrderedFacePeelWitnessData_of_interiorDualBoundaryRootAdjDistancePeelData
      data⟩⟩

/-- A nonempty boundary-root adjacency-distance IDBRAD package must contain a terminal peeled
face whose non-witness boundary is empty.  The proof is the height-terminal argument with the
IDBRAD boundary-freeness condition added: terminal remainders would have to be selected-boundary
edges, but peeled faces are disjoint from selected-boundary support. -/
theorem InteriorDualBoundaryRootAdjDistancePeelData.exists_terminal_peelFace_witness_erase_eq_empty_of_mem_interiorEdgeSupport
    {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (data : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    {e : G.edgeSet} (he : e ∈ interiorEdgeSupport emb.faceBoundary emb.faces) :
    ∃ f ∈ data.peelFaces,
      (emb.faceBoundary f.1).erase
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces data.roots
              data.hcoverRoots data.hsepRoots)
            data.fallbackEdge f) = ∅ := by
  let rootFace : AmbientFace emb.faces → AmbientFace emb.faces :=
    interiorDualSpanningForestRoot emb.faceBoundary emb.faces data.roots
      data.hcoverRoots data.hsepRoots
  let witnessEdge : AmbientFace emb.faces → G.edgeSet :=
    rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
      rootFace data.fallbackEdge
  let height : AmbientFace emb.faces → ℕ :=
    fun f => (interiorDualSpanningForest emb.faceBoundary emb.faces).dist f (rootFace f)
  have hne : data.peelFaces.Nonempty := by
    rcases
      (show ∃ f : AmbientFace emb.faces, f ∈ data.peelFaces ∧ witnessEdge f = e from by
        simpa [witnessEdge, rootFace] using data.hcover he) with
      ⟨f, hf, _hfe⟩
    exact ⟨f, hf⟩
  classical
  let heights := data.peelFaces.image height
  have hheights : heights.Nonempty := hne.image height
  rcases Finset.mem_image.1 (Finset.max'_mem heights hheights) with
    ⟨f, hf, hfmax⟩
  refine ⟨f, hf, ?_⟩
  ext e'
  constructor
  · intro he'
    have heFace : e' ∈ emb.faceBoundary f.1 := (Finset.mem_erase.1 he').2
    have hselected :
        e' ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces := by
      rcases data.hchildren f hf e' (by simpa [witnessEdge, rootFace] using he') with
        hboundary | ⟨g, hg, _hadj, _heg, hlt⟩
      · exact hboundary
      · have hgmax : height g ≤ heights.max' hheights :=
          Finset.le_max' heights (height g) (Finset.mem_image.2 ⟨g, hg, rfl⟩)
        exact False.elim ((not_lt_of_ge (by simpa [height, rootFace, hfmax] using hgmax)) hlt)
    exact False.elim
      ((Finset.disjoint_left.mp (data.hpeelInterior f hf)) heFace hselected)
  · intro he'
    simp at he'

/-- If an IDBRAD package covers at least one interior edge, then some peeled face has boundary
cardinality at most one.  Thus any source discipline forcing every peeled face to have at least
two boundary edges immediately refutes this IDBRAD construction. -/
theorem InteriorDualBoundaryRootAdjDistancePeelData.exists_peelFace_card_le_one_of_mem_interiorEdgeSupport
    {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (data : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    {e : G.edgeSet} (he : e ∈ interiorEdgeSupport emb.faceBoundary emb.faces) :
    ∃ f ∈ data.peelFaces, (emb.faceBoundary f.1).card ≤ 1 := by
  rcases
    data.exists_terminal_peelFace_witness_erase_eq_empty_of_mem_interiorEdgeSupport he with
    ⟨f, hf, herase⟩
  let rootFace : AmbientFace emb.faces → AmbientFace emb.faces :=
    interiorDualSpanningForestRoot emb.faceBoundary emb.faces data.roots
      data.hcoverRoots data.hsepRoots
  let witnessEdge : AmbientFace emb.faces → G.edgeSet :=
    rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
      rootFace data.fallbackEdge
  have hsubset : emb.faceBoundary f.1 ⊆ ({witnessEdge f} : Finset G.edgeSet) := by
    intro x hx
    by_cases hxw : x = witnessEdge f
    · simp [hxw]
    · have hxerase : x ∈ (emb.faceBoundary f.1).erase (witnessEdge f) :=
        Finset.mem_erase.2 ⟨hxw, hx⟩
      have herase' : (emb.faceBoundary f.1).erase (witnessEdge f) = ∅ := by
        simpa [witnessEdge, rootFace] using herase
      rw [herase'] at hxerase
      simp at hxerase
  refine ⟨f, hf, ?_⟩
  simpa using Finset.card_le_card hsubset

/-- Terminal-leaf obstruction in contradiction form: IDBRAD cannot cover an interior edge if
every peeled face has at least two boundary edges. -/
theorem InteriorDualBoundaryRootAdjDistancePeelData.false_of_mem_interiorEdgeSupport_of_forall_peelFace_two_le_faceBoundary_card
    {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (data : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    {e : G.edgeSet} (he : e ∈ interiorEdgeSupport emb.faceBoundary emb.faces)
    (hcard : ∀ f ∈ data.peelFaces, 2 ≤ (emb.faceBoundary f.1).card) :
    False := by
  rcases data.exists_peelFace_card_le_one_of_mem_interiorEdgeSupport he with
    ⟨f, hf, hle⟩
  exact
    (not_le_of_gt (Nat.lt_of_le_of_lt hle (by decide : (1 : ℕ) < 2)))
      (hcard f hf)

/-- Nonempty-interior-edge form of the terminal-leaf obstruction. -/
theorem InteriorDualBoundaryRootAdjDistancePeelData.false_of_interiorEdgeSupport_nonempty_of_forall_peelFace_two_le_faceBoundary_card
    {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (data : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hInterior : (interiorEdgeSupport emb.faceBoundary emb.faces).Nonempty)
    (hcard : ∀ f ∈ data.peelFaces, 2 ≤ (emb.faceBoundary f.1).card) :
    False := by
  rcases hInterior with ⟨e, he⟩
  exact
    data.false_of_mem_interiorEdgeSupport_of_forall_peelFace_two_le_faceBoundary_card
      he hcard

/-- Source-facing obstruction: if every ambient face is a genuine multi-edge face and there is
an interior edge to cover, no IDBRAD package can exist on this embedding. -/
theorem not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_of_interiorEdgeSupport_nonempty_of_forall_face_two_le_faceBoundary_card
    {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (hInterior : (interiorEdgeSupport emb.faceBoundary emb.faces).Nonempty)
    (hcard : ∀ f : AmbientFace emb.faces, 2 ≤ (emb.faceBoundary f.1).card) :
    ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) := by
  rintro ⟨data⟩
  exact
    data.false_of_interiorEdgeSupport_nonempty_of_forall_peelFace_two_le_faceBoundary_card
      hInterior (fun f _hf => hcard f)

/-- Named-edge form of the source-facing terminal-leaf obstruction. -/
theorem not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_of_mem_interiorEdgeSupport_of_forall_face_two_le_faceBoundary_card
    {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    {e : G.edgeSet} (he : e ∈ interiorEdgeSupport emb.faceBoundary emb.faces)
    (hcard : ∀ f : AmbientFace emb.faces, 2 ≤ (emb.faceBoundary f.1).card) :
    ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) := by
  exact
    not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_of_interiorEdgeSupport_nonempty_of_forall_face_two_le_faceBoundary_card
      ⟨e, he⟩ hcard

/-- Honest closed-walk face geometry instantiates the terminal-card obstruction for IDBRAD:
every face has at least three boundary edges, while a covered interior edge would force a peeled
face with at most one boundary edge. -/
theorem InteriorDualBoundaryRootAdjDistancePeelData.false_of_mem_interiorEdgeSupport_of_faceBoundaryClosedWalkGeometry
    {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (data : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (geom : PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalkGeometry emb)
    {e : G.edgeSet} (he : e ∈ interiorEdgeSupport emb.faceBoundary emb.faces) :
    False := by
  exact
    data.false_of_mem_interiorEdgeSupport_of_forall_peelFace_two_le_faceBoundary_card
      he (by
        intro f _hf
        exact
          Nat.le_trans (by decide : (2 : ℕ) ≤ 3)
            ((geom.faceBoundaryClosedWalk f).three_le_faceBoundary_card))

/-- Source-facing form: on an honest closed-walk embedding with nonempty interior support, no
boundary-root adjacent-distance peel package can satisfy the current boundary-free terminal
interface. -/
theorem not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_of_interiorEdgeSupport_nonempty_of_faceBoundaryClosedWalkGeometry
    {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (geom : PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalkGeometry emb)
    (hInterior : (interiorEdgeSupport emb.faceBoundary emb.faces).Nonempty) :
    ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) := by
  rintro ⟨data⟩
  rcases hInterior with ⟨e, he⟩
  exact data.false_of_mem_interiorEdgeSupport_of_faceBoundaryClosedWalkGeometry geom he

end Mettapedia.GraphTheory.FourColor
