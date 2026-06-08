import Mettapedia.GraphTheory.FourColor.PlanarBoundaryClosedWalkSource
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryAnnulusDecomposition

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- Witness-edge ownership data on top of a fixed annulus decomposition. This is the exact
algebraic payload still needed after the pure collar geometry `Γ_t`, collar faces, and remainders
have been constructed. -/
structure PlanarBoundaryAnnulusWitnessAssignment {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (decomp : PlanarBoundaryAnnulusDecomposition emb) where
  witnessEdge : AmbientFace emb.faces → G.edgeSet
  hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆
    (Finset.univ.biUnion decomp.collarFaces).image witnessEdge
  hwitness : ∀ i f, f ∈ decomp.collarFaces i → witnessEdge f ∈ emb.faceBoundary f.1
  hrest : ∀ i f, f ∈ decomp.collarFaces i → ∀ e ∈ (emb.faceBoundary f.1).erase (witnessEdge f),
    (i.1 = 0 ∧ e ∈ decomp.outerAmbientBoundary) ∨
      (∃ _hi : i.1 + 1 < decomp.numCollars, e ∈ decomp.boundaryCycle (Fin.succ i)) ∨
        (i.1 + 1 = decomp.numCollars ∧ e ∈ decomp.innerAmbientBoundary)
  hfrontier : ∀ i (_hi : i.1 + 1 < decomp.numCollars) e,
    e ∈ decomp.boundaryCycle (Fin.succ i) →
      ∃ j : Fin decomp.numCollars, i < j ∧ ∃ g ∈ decomp.collarFaces j, witnessEdge g = e

/-- Graph-level existence form of witness ownership over a pure annulus decomposition. -/
def AdmitsPlanarBoundaryAnnulusWitnessAssignment (G : SimpleGraph V) : Prop :=
  ∃ emb : PlaneEmbeddingWithBoundary G,
    ∃ decomp : PlanarBoundaryAnnulusDecomposition emb,
      Nonempty (PlanarBoundaryAnnulusWitnessAssignment decomp)

/-- Facewise witness-edge choices on the canonical one-collar decomposition extracted directly
from annulus boundary data. This is the exact extra geometric payload needed to upgrade the
boundary split to a full witness assignment without choosing deeper collar geometry: each ambient
face chooses one boundary edge as its witness, every interior edge is chosen by some face, and
every non-witness boundary edge already lies on one of the two ambient annulus boundaries. -/
structure PlanarBoundaryCanonicalWitnessChoice {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryData emb) where
  witnessEdge : AmbientFace emb.faces → G.edgeSet
  hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆
    emb.faces.attach.image witnessEdge
  hwitness : ∀ f, witnessEdge f ∈ emb.faceBoundary f.1
  hrest : ∀ f e, e ∈ (emb.faceBoundary f.1).erase (witnessEdge f) →
    e ∈ boundaryData.outerAmbientBoundary ∪ boundaryData.innerAmbientBoundary

/-- A canonical facewise witness choice on annulus boundary data upgrades the canonical one-collar
decomposition to a full annulus witness assignment on the same embedding. -/
def PlanarBoundaryCanonicalWitnessChoice.toPlanarBoundaryAnnulusWitnessAssignment
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {boundaryData : PlanarBoundaryAnnulusBoundaryData emb}
    (data : PlanarBoundaryCanonicalWitnessChoice boundaryData) :
    PlanarBoundaryAnnulusWitnessAssignment
      (planarBoundaryAnnulusDecomposition_of_boundaryData boundaryData) := by
  refine
    { witnessEdge := data.witnessEdge
      hcover := by
        intro e he
        rcases Finset.mem_image.1 (data.hcover he) with ⟨f, _hf, hfe⟩
        apply Finset.mem_image.2
        refine ⟨f, ?_, hfe⟩
        simp [planarBoundaryAnnulusDecomposition_of_boundaryData]
      hwitness := by
        intro i f _hf
        exact data.hwitness f
      hrest := by
        intro i f _hf e he
        have hi0 : i.1 = 0 := by
          have hi := i.isLt
          change i.1 < 1 at hi
          exact Nat.lt_one_iff.mp hi
        have hiLast :
            i.1 + 1 =
              (planarBoundaryAnnulusDecomposition_of_boundaryData boundaryData).numCollars := by
          simp [planarBoundaryAnnulusDecomposition_of_boundaryData]
        rcases Finset.mem_union.1 (data.hrest f e he) with houter | hinner
        · exact Or.inl ⟨hi0, houter⟩
        · exact Or.inr <| Or.inr ⟨hiLast, hinner⟩
      hfrontier := by
        intro i hi
        change i.1 + 1 < 1 at hi
        omega }

/-- Graph-level witness ownership already follows from a canonical facewise witness choice on the
boundary split, via the canonical one-collar annulus decomposition. -/
theorem admitsPlanarBoundaryAnnulusWitnessAssignment_of_exists_planarBoundaryCanonicalWitnessChoice
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryData emb,
        Nonempty (PlanarBoundaryCanonicalWitnessChoice boundaryData)) :
    AdmitsPlanarBoundaryAnnulusWitnessAssignment G := by
  rcases hG with ⟨emb, boundaryData, ⟨data⟩⟩
  exact
    ⟨emb, planarBoundaryAnnulusDecomposition_of_boundaryData boundaryData,
      ⟨data.toPlanarBoundaryAnnulusWitnessAssignment⟩⟩

/-- Construct the canonical facewise witness choice from a local single-interior-edge condition.
For each face, the constructor chooses the unique interior edge on that face when one exists;
otherwise it uses the supplied fallback boundary edge.  The hypotheses say precisely that this
choice covers every interior edge and that all remaining face-boundary edges already lie on the
outer or inner ambient annulus boundary. -/
noncomputable def PlanarBoundaryCanonicalWitnessChoice.of_atMostOneInteriorEdgePerFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {boundaryData : PlanarBoundaryAnnulusBoundaryData emb}
    (fallbackEdge : AmbientFace emb.faces → G.edgeSet)
    (hfallback : ∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1)
    (huniqueInterior :
      ∀ (f : AmbientFace emb.faces) {e₁ e₂ : G.edgeSet},
        e₁ ∈ emb.faceBoundary f.1 →
          e₂ ∈ emb.faceBoundary f.1 →
            e₁ ∈ interiorEdgeSupport emb.faceBoundary emb.faces →
              e₂ ∈ interiorEdgeSupport emb.faceBoundary emb.faces →
                e₁ = e₂)
    (hboundaryRest :
      ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
        e ∈ emb.faceBoundary f.1 →
          e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
            e ∈ boundaryData.outerAmbientBoundary ∪ boundaryData.innerAmbientBoundary) :
    PlanarBoundaryCanonicalWitnessChoice boundaryData := by
  classical
  let witnessEdge : AmbientFace emb.faces → G.edgeSet := fun f =>
    if h : ∃ e ∈ emb.faceBoundary f.1, e ∈ interiorEdgeSupport emb.faceBoundary emb.faces then
      Classical.choose h
    else
      fallbackEdge f
  refine
    { witnessEdge := witnessEdge
      hcover := ?_
      hwitness := ?_
      hrest := ?_ }
  · intro e heInterior
    rcases (mem_interiorEdgeSupport_iff emb.faceBoundary emb.faces).1 heInterior with
      ⟨heSupport, _hcount⟩
    rcases Finset.mem_biUnion.1 heSupport with ⟨f, hf, hef⟩
    let face : AmbientFace emb.faces := ⟨f, hf⟩
    have hface : ∃ e' ∈ emb.faceBoundary face.1,
        e' ∈ interiorEdgeSupport emb.faceBoundary emb.faces := ⟨e, hef, heInterior⟩
    have hchosen_mem :
        Classical.choose hface ∈ emb.faceBoundary face.1 :=
      (Classical.choose_spec hface).1
    have hchosen_interior :
        Classical.choose hface ∈ interiorEdgeSupport emb.faceBoundary emb.faces :=
      (Classical.choose_spec hface).2
    have hchosen_eq :
        Classical.choose hface = e :=
      huniqueInterior face hchosen_mem hef hchosen_interior heInterior
    refine Finset.mem_image.2 ⟨face, by simp, ?_⟩
    have hwitness : witnessEdge face = Classical.choose hface := by
      dsimp [witnessEdge]
      exact dif_pos hface
    exact hwitness.trans hchosen_eq
  · intro f
    by_cases h : ∃ e ∈ emb.faceBoundary f.1, e ∈ interiorEdgeSupport emb.faceBoundary emb.faces
    · have hchosen : Classical.choose h ∈ emb.faceBoundary f.1 :=
        (Classical.choose_spec h).1
      have hwitness : witnessEdge f = Classical.choose h := by
        dsimp [witnessEdge]
        exact dif_pos h
      rw [hwitness]
      exact hchosen
    · have hwitness : witnessEdge f = fallbackEdge f := by
        dsimp [witnessEdge]
        exact dif_neg h
      rw [hwitness]
      exact hfallback f
  · intro f e he
    have heFace : e ∈ emb.faceBoundary f.1 := (Finset.mem_erase.1 he).2
    by_cases h : ∃ e' ∈ emb.faceBoundary f.1,
        e' ∈ interiorEdgeSupport emb.faceBoundary emb.faces
    · have hchosen_mem :
          Classical.choose h ∈ emb.faceBoundary f.1 :=
        (Classical.choose_spec h).1
      have hchosen_interior :
          Classical.choose h ∈ interiorEdgeSupport emb.faceBoundary emb.faces :=
        (Classical.choose_spec h).2
      have heNotInterior : e ∉ interiorEdgeSupport emb.faceBoundary emb.faces := by
        intro heInterior
        have hchosen_eq :
            Classical.choose h = e :=
          huniqueInterior f hchosen_mem heFace hchosen_interior heInterior
        have heNe : e ≠ witnessEdge f := (Finset.mem_erase.1 he).1
        have hwitness : witnessEdge f = Classical.choose h := by
          dsimp [witnessEdge]
          exact dif_pos h
        exact heNe (by rw [hwitness, hchosen_eq])
      exact hboundaryRest f heFace heNotInterior
    · have heNotInterior : e ∉ interiorEdgeSupport emb.faceBoundary emb.faces := by
        intro heInterior
        exact h ⟨e, heFace, heInterior⟩
      exact hboundaryRest f heFace heNotInterior

/-- On the canonical one-collar decomposition produced directly from annulus boundary data, every
non-witness edge on a collar face must already lie on one of the two ambient annulus boundaries:
there is no intermediate frontier available. -/
theorem
    PlanarBoundaryAnnulusWitnessAssignment.mem_outerAmbientBoundary_or_mem_innerAmbientBoundary_of_mem_faceBoundary_erase_on_canonicalDecomposition
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryData emb)
    (data : PlanarBoundaryAnnulusWitnessAssignment
      (planarBoundaryAnnulusDecomposition_of_boundaryData boundaryData))
    {f : AmbientFace emb.faces} {e : G.edgeSet}
    (he : e ∈ (emb.faceBoundary f.1).erase (data.witnessEdge f)) :
    e ∈ boundaryData.outerAmbientBoundary ∪ boundaryData.innerAmbientBoundary := by
  let i : Fin (planarBoundaryAnnulusDecomposition_of_boundaryData boundaryData).numCollars :=
    ⟨0, by simp [planarBoundaryAnnulusDecomposition_of_boundaryData]⟩
  have hf :
      f ∈ (planarBoundaryAnnulusDecomposition_of_boundaryData boundaryData).collarFaces i := by
    simp [planarBoundaryAnnulusDecomposition_of_boundaryData, i]
  have hrest := data.hrest i f hf e he
  simpa [planarBoundaryAnnulusDecomposition_of_boundaryData, i] using hrest

/-- The canonical one-collar decomposition built directly from annulus boundary data cannot admit
any witness assignment if some ambient face boundary contains two distinct interior edges. The
reason is geometric rather than witness-specific: whichever interior edge is chosen as witness,
the other one would have to lie on an ambient annulus boundary, which interior edges never do. -/
theorem
    not_nonempty_planarBoundaryAnnulusWitnessAssignment_of_exists_two_distinct_interior_edges_on_faceBoundary_of_canonicalDecomposition
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryData emb)
    (hex :
      ∃ f : AmbientFace emb.faces,
        ∃ e₁ ∈ emb.faceBoundary f.1,
          ∃ e₂ ∈ emb.faceBoundary f.1,
            e₁ ≠ e₂ ∧
              e₁ ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∧
                e₂ ∈ interiorEdgeSupport emb.faceBoundary emb.faces) :
    ¬ Nonempty
      (PlanarBoundaryAnnulusWitnessAssignment
        (planarBoundaryAnnulusDecomposition_of_boundaryData boundaryData)) := by
  rintro ⟨data⟩
  rcases hex with ⟨f, e₁, he₁, e₂, he₂, hne, he₁Interior, he₂Interior⟩
  by_cases hw : data.witnessEdge f = e₁
  · have he₂erase : e₂ ∈ (emb.faceBoundary f.1).erase (data.witnessEdge f) := by
      refine Finset.mem_erase.2 ?_
      constructor
      · intro he₂eq
        exact hne (hw.symm.trans he₂eq.symm)
      · exact he₂
    have hboundary :
        e₂ ∈ boundaryData.outerAmbientBoundary ∪ boundaryData.innerAmbientBoundary :=
      PlanarBoundaryAnnulusWitnessAssignment.mem_outerAmbientBoundary_or_mem_innerAmbientBoundary_of_mem_faceBoundary_erase_on_canonicalDecomposition
        boundaryData data he₂erase
    rcases Finset.mem_union.1 hboundary with houter | hinner
    · exact
        (Finset.disjoint_left.mp
          boundaryData.outerAmbientBoundary_disjoint_interiorEdgeSupport) houter he₂Interior
    · exact
        (Finset.disjoint_left.mp
          boundaryData.innerAmbientBoundary_disjoint_interiorEdgeSupport) hinner he₂Interior
  · have he₁erase : e₁ ∈ (emb.faceBoundary f.1).erase (data.witnessEdge f) := by
      refine Finset.mem_erase.2 ?_
      constructor
      · simpa [eq_comm] using hw
      · exact he₁
    have hboundary :
        e₁ ∈ boundaryData.outerAmbientBoundary ∪ boundaryData.innerAmbientBoundary :=
      PlanarBoundaryAnnulusWitnessAssignment.mem_outerAmbientBoundary_or_mem_innerAmbientBoundary_of_mem_faceBoundary_erase_on_canonicalDecomposition
        boundaryData data he₁erase
    rcases Finset.mem_union.1 hboundary with houter | hinner
    · exact
        (Finset.disjoint_left.mp
          boundaryData.outerAmbientBoundary_disjoint_interiorEdgeSupport) houter he₁Interior
    · exact
        (Finset.disjoint_left.mp
          boundaryData.innerAmbientBoundary_disjoint_interiorEdgeSupport) hinner he₁Interior

/-- The same two-interior-edge obstruction blocks the canonical witness-choice repair itself.
Any such choice upgrades to a witness assignment on the canonical one-collar decomposition, so
the witness-assignment obstruction is already a direct obstruction to the proposed facewise
choice. -/
theorem
    not_nonempty_planarBoundaryCanonicalWitnessChoice_of_exists_two_distinct_interior_edges_on_faceBoundary
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryData emb)
    (hex :
      ∃ f : AmbientFace emb.faces,
        ∃ e₁ ∈ emb.faceBoundary f.1,
          ∃ e₂ ∈ emb.faceBoundary f.1,
            e₁ ≠ e₂ ∧
              e₁ ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∧
                e₂ ∈ interiorEdgeSupport emb.faceBoundary emb.faces) :
    ¬ Nonempty (PlanarBoundaryCanonicalWitnessChoice boundaryData) := by
  rintro ⟨data⟩
  exact
    not_nonempty_planarBoundaryAnnulusWitnessAssignment_of_exists_two_distinct_interior_edges_on_faceBoundary_of_canonicalDecomposition
      boundaryData hex ⟨data.toPlanarBoundaryAnnulusWitnessAssignment⟩

/-- The same obstruction applies directly to honest closed-walk annulus sources when the witness
assignment is taken on the canonical one-collar decomposition extracted from that source's
boundary-data field. If one ambient face already carries two distinct interior edges, canonical
witness ownership cannot be recovered from the source alone. -/
theorem
    not_nonempty_planarBoundaryAnnulusWitnessAssignment_of_exists_two_distinct_interior_edges_on_faceBoundary_of_closedWalkAnnulusBoundarySource
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hex :
      ∃ f : AmbientFace emb.faces,
        ∃ e₁ ∈ emb.faceBoundary f.1,
          ∃ e₂ ∈ emb.faceBoundary f.1,
            e₁ ≠ e₂ ∧
              e₁ ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∧
                e₂ ∈ interiorEdgeSupport emb.faceBoundary emb.faces) :
    ¬ Nonempty
      (PlanarBoundaryAnnulusWitnessAssignment
        (planarBoundaryAnnulusDecomposition_of_boundaryData
          source.toPlanarBoundaryAnnulusBoundaryData)) := by
  exact
    not_nonempty_planarBoundaryAnnulusWitnessAssignment_of_exists_two_distinct_interior_edges_on_faceBoundary_of_canonicalDecomposition
      source.toPlanarBoundaryAnnulusBoundaryData hex

/-- Honest closed-walk annulus sources do not by themselves repair the canonical witness-choice
obstruction: if a source face already carries two distinct interior edges, no facewise canonical
witness choice exists on the source boundary split. -/
theorem
    not_nonempty_planarBoundaryCanonicalWitnessChoice_of_exists_two_distinct_interior_edges_on_faceBoundary_of_closedWalkAnnulusBoundarySource
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hex :
      ∃ f : AmbientFace emb.faces,
        ∃ e₁ ∈ emb.faceBoundary f.1,
          ∃ e₂ ∈ emb.faceBoundary f.1,
            e₁ ≠ e₂ ∧
              e₁ ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∧
                e₂ ∈ interiorEdgeSupport emb.faceBoundary emb.faces) :
    ¬ Nonempty
      (PlanarBoundaryCanonicalWitnessChoice
        source.toPlanarBoundaryAnnulusBoundaryData) := by
  exact
    not_nonempty_planarBoundaryCanonicalWitnessChoice_of_exists_two_distinct_interior_edges_on_faceBoundary
      source.toPlanarBoundaryAnnulusBoundaryData hex

/-- The same two-interior-edge obstruction already blocks any one-collar witness assignment, not
just the canonical decomposition extracted from annulus boundary data. When `numCollars = 1`, the
sole collar face has no deeper frontier available, so every non-witness edge on its boundary must
lie on one of the two ambient annulus boundaries. A second interior edge on the same face is
therefore impossible. -/
theorem
    not_nonempty_planarBoundaryAnnulusWitnessAssignment_of_numCollars_eq_one_and_exists_two_distinct_interior_edges_on_faceBoundary
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {decomp : PlanarBoundaryAnnulusDecomposition emb}
    (hnum : decomp.numCollars = 1)
    (hex :
      ∃ f : AmbientFace emb.faces,
        ∃ e₁ ∈ emb.faceBoundary f.1,
          ∃ e₂ ∈ emb.faceBoundary f.1,
            e₁ ≠ e₂ ∧
              e₁ ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∧
                e₂ ∈ interiorEdgeSupport emb.faceBoundary emb.faces) :
    ¬ Nonempty (PlanarBoundaryAnnulusWitnessAssignment decomp) := by
  rintro ⟨data⟩
  let i : Fin decomp.numCollars := ⟨0, by omega⟩
  rcases hex with ⟨f, e₁, he₁, e₂, he₂, hne, he₁Interior, he₂Interior⟩
  rcases decomp.exists_mem_collarFaces f with ⟨j, hfj⟩
  have hj0 : j.1 = 0 := by
    have hjlt : j.1 < 1 := by
      omega
    exact Nat.lt_one_iff.mp hjlt
  have hji : j = i := by
    apply Fin.ext
    simpa [i] using hj0
  have hfi : f ∈ decomp.collarFaces i := by
    simpa [hji] using hfj
  by_cases hw : data.witnessEdge f = e₁
  · have he₂erase : e₂ ∈ (emb.faceBoundary f.1).erase (data.witnessEdge f) := by
      refine Finset.mem_erase.2 ?_
      constructor
      · intro he₂eq
        exact hne (hw.symm.trans he₂eq.symm)
      · exact he₂
    have hrest := data.hrest i f hfi e₂ he₂erase
    rcases hrest with houter | hinner | hterminal
    · exact
        (Finset.disjoint_left.mp
          decomp.outerAmbientBoundary_disjoint_interiorEdgeSupport) houter.2 he₂Interior
    · rcases hinner with ⟨hi, _⟩
      omega
    · exact
        (Finset.disjoint_left.mp
          decomp.innerAmbientBoundary_disjoint_interiorEdgeSupport) hterminal.2 he₂Interior
  · have he₁erase : e₁ ∈ (emb.faceBoundary f.1).erase (data.witnessEdge f) := by
      refine Finset.mem_erase.2 ?_
      constructor
      · simpa [eq_comm] using hw
      · exact he₁
    have hrest := data.hrest i f hfi e₁ he₁erase
    rcases hrest with houter | hinner | hterminal
    · exact
        (Finset.disjoint_left.mp
          decomp.outerAmbientBoundary_disjoint_interiorEdgeSupport) houter.2 he₁Interior
    · rcases hinner with ⟨hi, _⟩
      omega
    · exact
        (Finset.disjoint_left.mp
          decomp.innerAmbientBoundary_disjoint_interiorEdgeSupport) hterminal.2 he₁Interior

/-- A terminal collar face cannot carry two distinct interior edges. In the final collar there is
no deeper intermediate frontier available; after one interior witness edge is chosen, the other
interior edge would have to lie on an ambient annulus boundary, contradicting ambient/interior
disjointness. This is the terminal-layer form of the one-collar obstruction. -/
theorem
    false_of_mem_terminal_collarFaces_and_exists_two_distinct_interior_edges_on_faceBoundary
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {decomp : PlanarBoundaryAnnulusDecomposition emb}
    (data : PlanarBoundaryAnnulusWitnessAssignment decomp)
    {i : Fin decomp.numCollars}
    (hiLast : i.1 + 1 = decomp.numCollars)
    {f : AmbientFace emb.faces}
    (hf : f ∈ decomp.collarFaces i)
    (hex :
      ∃ e₁ ∈ emb.faceBoundary f.1,
        ∃ e₂ ∈ emb.faceBoundary f.1,
          e₁ ≠ e₂ ∧
            e₁ ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∧
              e₂ ∈ interiorEdgeSupport emb.faceBoundary emb.faces) :
    False := by
  rcases hex with ⟨e₁, he₁, e₂, he₂, hne, he₁Interior, he₂Interior⟩
  by_cases hw : data.witnessEdge f = e₁
  · have he₂erase : e₂ ∈ (emb.faceBoundary f.1).erase (data.witnessEdge f) := by
      refine Finset.mem_erase.2 ?_
      constructor
      · intro he₂eq
        exact hne (hw.symm.trans he₂eq.symm)
      · exact he₂
    have hrest := data.hrest i f hf e₂ he₂erase
    rcases hrest with houter | hmiddle | hterminal
    · exact
        (Finset.disjoint_left.mp
          decomp.outerAmbientBoundary_disjoint_interiorEdgeSupport) houter.2 he₂Interior
    · rcases hmiddle with ⟨hi, _⟩
      omega
    · exact
        (Finset.disjoint_left.mp
          decomp.innerAmbientBoundary_disjoint_interiorEdgeSupport) hterminal.2 he₂Interior
  · have he₁erase : e₁ ∈ (emb.faceBoundary f.1).erase (data.witnessEdge f) := by
      refine Finset.mem_erase.2 ?_
      constructor
      · simpa [eq_comm] using hw
      · exact he₁
    have hrest := data.hrest i f hf e₁ he₁erase
    rcases hrest with houter | hmiddle | hterminal
    · exact
        (Finset.disjoint_left.mp
          decomp.outerAmbientBoundary_disjoint_interiorEdgeSupport) houter.2 he₁Interior
    · rcases hmiddle with ⟨hi, _⟩
      omega
    · exact
        (Finset.disjoint_left.mp
          decomp.innerAmbientBoundary_disjoint_interiorEdgeSupport) hterminal.2 he₁Interior

/-- An interior edge incident to a given ambient face is also incident to some other ambient face
when the total ambient incidence count is exactly two. -/
theorem exists_other_ambientFace_of_totalIncidenceCount_eq_two
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {e : G.edgeSet} {g : AmbientFace emb.faces}
    (hcount : totalIncidenceCount emb.faceBoundary emb.faces e = 2) :
    ∃ p : AmbientFace emb.faces, p ≠ g ∧ e ∈ emb.faceBoundary p.1 := by
  have hcount' :
      totalIncidenceCount
          (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)
          emb.faces.attach e = 2 := by
    simpa [totalIncidenceCount_ambientFaceBoundary_eq
      (faceBoundary := emb.faceBoundary) (allFaces := emb.faces)] using hcount
  have hgt :
      1 <
        totalIncidenceCount
          (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)
          emb.faces.attach e := by
    omega
  unfold totalIncidenceCount at hgt
  rcases Finset.one_lt_card.1 hgt with ⟨f1, hf1, f2, hf2, hf12⟩
  by_cases hfg : f1 = g
  · refine ⟨f2, ?_, ?_⟩
    · intro hEq
      exact hf12 (hfg.trans hEq.symm)
    · simpa [ambientFaceBoundary] using (Finset.mem_filter.1 hf2).2
  · refine ⟨f1, hfg, ?_⟩
    simpa [ambientFaceBoundary] using (Finset.mem_filter.1 hf1).2

/-- A positive-index collar face whose witness edge lies on the previous annulus boundary already
has a parent-carrying adjacent ambient face in a strictly earlier collar layer. This is the core
annulus-geometry step hidden inside the previous-boundary witness route. -/
theorem PlanarBoundaryAnnulusWitnessAssignment.exists_parentFace_of_previousBoundaryWitness
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {decomp : PlanarBoundaryAnnulusDecomposition emb}
    (data : PlanarBoundaryAnnulusWitnessAssignment decomp)
    (hwitnessPrev : ∀ {j : Fin decomp.numCollars} {g : AmbientFace emb.faces},
      g ∈ decomp.collarFaces j → 0 < j.1 →
        data.witnessEdge g ∈ decomp.boundaryCycle (Fin.castSucc j))
    {j : Fin decomp.numCollars} {g : AmbientFace emb.faces}
    (hgj : g ∈ decomp.collarFaces j) (hjpos : 0 < j.1) :
    ∃ p : AmbientFace emb.faces,
      data.witnessEdge g ∈ emb.faceBoundary p.1 ∧
        decomp.layerOf p < j := by
  let i : Fin decomp.numCollars := ⟨j.1 - 1, by
    have hjLt := j.isLt
    omega⟩
  have hi : i.1 + 1 < decomp.numCollars := by
    dsimp [i]
    omega
  have hij : i < j := by
    show i.1 < j.1
    dsimp [i]
    omega
  have hcast : Fin.castSucc j = Fin.succ i := by
    apply Fin.ext
    dsimp [i]
    omega
  have hePrev : data.witnessEdge g ∈ decomp.boundaryCycle (Fin.succ i) := by
    simpa [hcast] using hwitnessPrev hgj hjpos
  have heg : data.witnessEdge g ∈ emb.faceBoundary g.1 := data.hwitness j g hgj
  have hcountTwo :
      totalIncidenceCount emb.faceBoundary emb.faces (data.witnessEdge g) = 2 :=
    decomp.totalIncidenceCount_eq_two_of_mem_boundaryCycle_intermediate i hi hePrev
  rcases exists_other_ambientFace_of_totalIncidenceCount_eq_two
      (g := g) hcountTwo with ⟨p, hpg, hep⟩
  have hrel :
      data.witnessEdge g ∈ relativeBoundarySupport
        (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)
        (decomp.remainderFaces i) :=
    decomp.hinnerBoundary i hi hePrev
  have hgRem : g ∈ decomp.remainderFaces i :=
    decomp.collarFaces_subset_remainderFaces_of_lt hij hgj
  have hpNotRem : p ∉ decomp.remainderFaces i := by
    intro hpRem
    have hsubsetOne :
        subsetIncidenceCount
            (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)
            (decomp.remainderFaces i)
            (data.witnessEdge g) = 1 :=
      (mem_relativeBoundarySupport_iff
        (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)
        (decomp.remainderFaces i)).1 hrel |>.2
    have hgt :
        1 <
          subsetIncidenceCount
            (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)
            (decomp.remainderFaces i)
            (data.witnessEdge g) := by
      unfold subsetIncidenceCount
      rw [Finset.one_lt_card]
      refine ⟨g, Finset.mem_filter.2 ⟨hgRem, by simpa [ambientFaceBoundary] using heg⟩,
        p, Finset.mem_filter.2 ⟨hpRem, by simpa [ambientFaceBoundary] using hep⟩,
        hpg.symm⟩
    omega
  have hlayerLe : (decomp.layerOf p).1 ≤ i.1 := by
    by_contra hlt
    have hilayer : i < decomp.layerOf p := by
      show i.1 < (decomp.layerOf p).1
      exact Nat.lt_of_not_ge hlt
    exact hpNotRem
      (decomp.collarFaces_subset_remainderFaces_of_lt hilayer
        (decomp.mem_collarFaces_layerOf p))
  have hltj : decomp.layerOf p < j := by
    show (decomp.layerOf p).1 < j.1
    dsimp [i] at hlayerLe
    omega
  exact ⟨p, hep, hltj⟩

/-- Canonical parent chosen from the previous-boundary witness placement geometry. Faces in the
first collar have no earlier parent layer, while every positive collar face chooses one. -/
noncomputable def PlanarBoundaryAnnulusWitnessAssignment.parentFaceOfPreviousBoundaryWitness
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {decomp : PlanarBoundaryAnnulusDecomposition emb}
    (data : PlanarBoundaryAnnulusWitnessAssignment decomp)
    (hwitnessPrev : ∀ {j : Fin decomp.numCollars} {g : AmbientFace emb.faces},
      g ∈ decomp.collarFaces j → 0 < j.1 →
        data.witnessEdge g ∈ decomp.boundaryCycle (Fin.castSucc j))
    (g : AmbientFace emb.faces) : Option (AmbientFace emb.faces) :=
  let j := decomp.layerOf g
  if hj0 : j.1 = 0 then
    none
  else
    some (Classical.choose
      (data.exists_parentFace_of_previousBoundaryWitness hwitnessPrev
        (decomp.mem_collarFaces_layerOf g) (Nat.pos_of_ne_zero hj0)))

theorem PlanarBoundaryAnnulusWitnessAssignment.parentFaceOfPreviousBoundaryWitness_eq_none_of_layerOf_eq_zero
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {decomp : PlanarBoundaryAnnulusDecomposition emb}
    (data : PlanarBoundaryAnnulusWitnessAssignment decomp)
    (hwitnessPrev : ∀ {j : Fin decomp.numCollars} {g : AmbientFace emb.faces},
      g ∈ decomp.collarFaces j → 0 < j.1 →
        data.witnessEdge g ∈ decomp.boundaryCycle (Fin.castSucc j))
    {g : AmbientFace emb.faces}
    (hgzero : (decomp.layerOf g).1 = 0) :
    data.parentFaceOfPreviousBoundaryWitness hwitnessPrev g = none := by
  simp [PlanarBoundaryAnnulusWitnessAssignment.parentFaceOfPreviousBoundaryWitness, hgzero]

theorem PlanarBoundaryAnnulusWitnessAssignment.parentFaceOfPreviousBoundaryWitness_spec
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {decomp : PlanarBoundaryAnnulusDecomposition emb}
    (data : PlanarBoundaryAnnulusWitnessAssignment decomp)
    (hwitnessPrev : ∀ {j : Fin decomp.numCollars} {g : AmbientFace emb.faces},
      g ∈ decomp.collarFaces j → 0 < j.1 →
        data.witnessEdge g ∈ decomp.boundaryCycle (Fin.castSucc j))
    {g : AmbientFace emb.faces}
    (hgpos : 0 < (decomp.layerOf g).1) :
    ∃ p : AmbientFace emb.faces,
      data.parentFaceOfPreviousBoundaryWitness hwitnessPrev g = some p ∧
      data.witnessEdge g ∈ emb.faceBoundary p.1 ∧
      decomp.layerOf p < decomp.layerOf g := by
  let p : AmbientFace emb.faces :=
    Classical.choose
      (data.exists_parentFace_of_previousBoundaryWitness hwitnessPrev
        (decomp.mem_collarFaces_layerOf g) hgpos)
  have hspec :=
    Classical.choose_spec
      (data.exists_parentFace_of_previousBoundaryWitness hwitnessPrev
        (decomp.mem_collarFaces_layerOf g) hgpos)
  refine ⟨p, ?_, hspec.1, hspec.2⟩
  simp [PlanarBoundaryAnnulusWitnessAssignment.parentFaceOfPreviousBoundaryWitness,
    Nat.ne_of_gt hgpos, p]

/-- If every positive-index collar face chooses its witness edge on the previous annulus boundary
cycle, then the annulus witness assignment already determines a well-founded parent-peeling
package on the same embedding. This is the direct bridge from explicit `Γ_t` geometry to the
boundary-aware Theorem 4.9 interface, without routing through the older interior-dual wrappers. -/
noncomputable def
    PlanarBoundaryAnnulusWitnessAssignment.toPlanarBoundaryWellFoundedFacePeelWitnessData_of_previousBoundaryWitness
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {decomp : PlanarBoundaryAnnulusDecomposition emb}
    (data : PlanarBoundaryAnnulusWitnessAssignment decomp)
    (hwitnessPrev : ∀ {j : Fin decomp.numCollars} {g : AmbientFace emb.faces},
      g ∈ decomp.collarFaces j → 0 < j.1 →
        data.witnessEdge g ∈ decomp.boundaryCycle (Fin.castSucc j)) :
    PlanarBoundaryWellFoundedFacePeelWitnessData emb := by
  let peelFaces : Finset (AmbientFace emb.faces) := Finset.univ.biUnion decomp.collarFaces
  let parentFace := data.parentFaceOfPreviousBoundaryWitness hwitnessPrev
  have hWF : WellFounded (ParentRel parentFace) := by
    refine wellFounded_parentRel_of_lt_height parentFace (fun g => (decomp.layerOf g).1) ?_
    intro g f hgf
    by_cases hgpos : 0 < (decomp.layerOf g).1
    · rcases data.parentFaceOfPreviousBoundaryWitness_spec hwitnessPrev hgpos with
        ⟨p, hparentg, _hpgEdge, hlt⟩
      have hgf' : data.parentFaceOfPreviousBoundaryWitness hwitnessPrev g = some f := by
        simpa [parentFace] using hgf
      rw [hparentg] at hgf'
      cases hgf'
      exact hlt
    · have hgzero : (decomp.layerOf g).1 = 0 := Nat.eq_zero_of_not_pos hgpos
      have hgf' : data.parentFaceOfPreviousBoundaryWitness hwitnessPrev g = some f := by
        simpa [parentFace] using hgf
      rw [data.parentFaceOfPreviousBoundaryWitness_eq_none_of_layerOf_eq_zero
        hwitnessPrev hgzero] at hgf'
      simp at hgf'
  refine
    { peelFaces := peelFaces
      parentFace := parentFace
      witnessEdge := data.witnessEdge
      hWF := hWF
      hcover := by simpa [peelFaces] using data.hcover
      hwitness := ?_
      hchildren := ?_ }
  · intro f hf
    rcases Finset.mem_biUnion.1 hf with ⟨i, -, hfi⟩
    exact data.hwitness i f hfi
  · intro f hf e he
    rcases Finset.mem_biUnion.1 hf with ⟨i, -, hfi⟩
    rcases data.hrest i f hfi e he with
      ⟨_, houter⟩ | ⟨hi, hnext⟩ | ⟨_, hterminal⟩
    · exact Or.inl (decomp.houterAmbientBoundarySubset houter)
    · rcases data.hfrontier i hi e hnext with ⟨j, hij, g, hgj, hge⟩
      have hjpos : 0 < j.1 := by
        omega
      have hgpos : 0 < (decomp.layerOf g).1 := by
        simpa [decomp.layerOf_eq_of_mem hgj] using hjpos
      rcases data.parentFaceOfPreviousBoundaryWitness_spec hwitnessPrev hgpos with
        ⟨p, hparentg, hpgEdge, hlt⟩
      have hpg : p ≠ g := by
        intro hEq
        simp [hEq] at hlt
      have hef : e ∈ emb.faceBoundary f.1 := (Finset.mem_erase.1 he).2
      have hpe : e ∈ emb.faceBoundary p.1 := by
        simpa [hge] using hpgEdge
      have hgeFace : e ∈ emb.faceBoundary g.1 := by
        simpa [hge] using data.hwitness j g hgj
      have hfp_or_hfg :
          f.1 = p.1 ∨ f.1 = g.1 := by
        exact
          eq_or_eq_of_mem_faceBoundary_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
            emb.faceBoundary emb.faces
            (fun e' => planeEmbeddingWithBoundary_totalIncidenceCount_le_two emb e')
            p.2 g.2 f.2
            (by
              intro hpEq
              exact hpg (Subtype.ext hpEq))
            hpe hgeFace hef
      have hgPeel : g ∈ peelFaces := Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, hgj⟩
      rcases hfp_or_hfg with hfp | hfg
      · have hpf : p = f := Subtype.ext hfp.symm
        exact Or.inr ⟨g, hgPeel, by simpa [hpf] using hparentg, hge⟩
      · have : f = g := Subtype.ext hfg
        subst this
        exact False.elim ((Finset.mem_erase.1 he).1 hge.symm)
    · exact Or.inl (decomp.hinnerAmbientBoundarySubset hterminal)

/-- Direct annihilator theorem from annulus decomposition plus witness assignment, once each
positive-index collar face chooses its witness edge on the previous annulus boundary cycle. This
isolates the remaining geometric burden in the annulus route to establishing that witness-edge
placement hypothesis. -/
theorem zero_on_allEdges_of_planarBoundaryAnnulusWitnessAssignment_of_previousBoundaryWitness
    {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G)
    (decomp : PlanarBoundaryAnnulusDecomposition emb)
    (data : PlanarBoundaryAnnulusWitnessAssignment decomp)
    (hwitnessPrev : ∀ {j : Fin decomp.numCollars} {g : AmbientFace emb.faces},
      g ∈ decomp.collarFaces j → 0 < j.1 →
        data.witnessEdge g ∈ decomp.boundaryCycle (Fin.castSucc j))
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0)
    (horth : ∀ i f, f ∈ decomp.collarFaces i →
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

/-- A witness assignment on a pure annulus decomposition canonically yields the current weakest
explicit-remainder annulus endpoint consumed by the Theorem 4.9 annihilator layer. -/
def PlanarBoundaryAnnulusWitnessAssignment.toLocalRemainderBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {decomp : PlanarBoundaryAnnulusDecomposition emb}
    (data : PlanarBoundaryAnnulusWitnessAssignment decomp) :
    PlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData emb := by
  refine
    { numLayers := decomp.numCollars
      layerFaces := decomp.collarFaces
      remainderFaces := decomp.remainderFaces
      witnessEdge := data.witnessEdge
      hlayerSubset := ?_
      hdisjoint := decomp.hdisjoint
      hcover := ?_
      hwitness := ?_
      hremainder := decomp.hremainder
      hrest := ?_ }
  · intro i f hf
    simp
  · simpa [interiorEdgeSupport_ambientFaceBoundary_eq
      (faceBoundary := emb.faceBoundary) (allFaces := emb.faces)] using data.hcover
  · intro i f hf
    simpa [ambientFaceBoundary] using data.hwitness i f hf
  · intro i f hf e he
    rcases data.hrest i f hf e he with
      ⟨_, houter⟩ | ⟨hi, hinner⟩ | ⟨_, hterminal⟩
    · exact Or.inl <| by
        exact (selectedBoundarySupport_ambientFaceBoundary_eq
          (faceBoundary := emb.faceBoundary) (allFaces := emb.faces)).symm ▸
          decomp.houterAmbientBoundarySubset houter
    · rcases data.hfrontier i hi e hinner with ⟨j, hij, g, hgj, hge⟩
      refine Or.inr ⟨j, hij, g, hgj, hge, ?_⟩
      exact decomp.hinnerBoundary i hi hinner
    · exact Or.inl <| by
        exact (selectedBoundarySupport_ambientFaceBoundary_eq
          (faceBoundary := emb.faceBoundary) (allFaces := emb.faces)).symm ▸
          decomp.hinnerAmbientBoundarySubset hterminal

theorem
    admitsPlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData_of_admitsPlanarBoundaryAnnulusWitnessAssignment
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryAnnulusWitnessAssignment G) :
    AdmitsPlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData G := by
  rcases hG with ⟨emb, decomp, ⟨data⟩⟩
  exact ⟨emb, ⟨data.toLocalRemainderBoundaryCollarLayerFacePeelWitnessData⟩⟩

/-- Direct annulus-shaped annihilator theorem from pure annulus geometry plus a witness
assignment. This is the clean split of the remaining Step 2 burden: geometry first, witness
assignment second. -/
theorem zero_on_allEdges_of_planarBoundaryAnnulusWitnessAssignment
    {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G)
    (decomp : PlanarBoundaryAnnulusDecomposition emb)
    (data : PlanarBoundaryAnnulusWitnessAssignment decomp)
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0)
    (horth : ∀ i f, f ∈ decomp.collarFaces i →
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
  exact zero_on_allEdges_of_planarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
    (emb := emb) (C := C) (htait := htait) (z := z)
    (data := data.toLocalRemainderBoundaryCollarLayerFacePeelWitnessData)
    (hzeroBoundary := hzeroBoundary) (horth := horth)

/-- Existential graph-level annihilator form of the split geometry-plus-witness annulus target. -/
theorem zero_on_allEdges_of_exists_planarBoundaryAnnulusWitnessAssignment
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (hdata : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ decomp : PlanarBoundaryAnnulusDecomposition emb,
      ∃ data : PlanarBoundaryAnnulusWitnessAssignment decomp,
        (∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0) ∧
        (∀ i f, f ∈ decomp.collarFaces i →
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
  rcases hdata with ⟨emb, decomp, data, hzeroBoundary, horth⟩
  exact zero_on_allEdges_of_planarBoundaryAnnulusWitnessAssignment
    (emb := emb) (decomp := decomp) (data := data)
    (C := C) (htait := htait) (z := z)
    (hzeroBoundary := hzeroBoundary) (horth := horth)

end Mettapedia.GraphTheory.FourColor
