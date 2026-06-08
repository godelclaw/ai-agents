import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Finset.Card

namespace Mettapedia.GraphTheory.FourColor

variable {F E : Type*} [DecidableEq F] [DecidableEq E]

/-- The total number of faces in the ambient face set whose boundary contains a given edge. -/
def totalIncidenceCount (faceBoundary : F → Finset E) (allFaces : Finset F) (e : E) : ℕ :=
  (allFaces.filter fun f => e ∈ faceBoundary f).card

/-- The number of selected faces in `S` whose boundary contains a given edge. This is the
face-incidence count relative to a chosen face subset, rather than the full ambient face set. -/
def subsetIncidenceCount (faceBoundary : F → Finset E) (S : Finset F) (e : E) : ℕ :=
  (S.filter fun f => e ∈ faceBoundary f).card

/-- The selected boundary-edge support: edges incident to exactly one ambient face and to a
selected face. -/
def selectedBoundarySupport (faceBoundary : F → Finset E)
    (allFaces S : Finset F) : Finset E :=
  (S.biUnion faceBoundary).filter fun e => totalIncidenceCount faceBoundary allFaces e = 1

/-- The boundary-edge support of a selected face subset computed relative to that subset itself.
This is the primitive needed to speak about the boundary of a remaining subannulus during
outside-in collar peeling. -/
def relativeBoundarySupport (faceBoundary : F → Finset E) (S : Finset F) : Finset E :=
  (S.biUnion faceBoundary).filter fun e => subsetIncidenceCount faceBoundary S e = 1

omit [DecidableEq F] in
theorem mem_selectedBoundarySupport_iff (faceBoundary : F → Finset E)
    (allFaces S : Finset F) {e : E} :
    e ∈ selectedBoundarySupport faceBoundary allFaces S ↔
      e ∈ S.biUnion faceBoundary ∧ totalIncidenceCount faceBoundary allFaces e = 1 := by
  simp [selectedBoundarySupport]

omit [DecidableEq F] in
theorem mem_relativeBoundarySupport_iff (faceBoundary : F → Finset E)
    (S : Finset F) {e : E} :
    e ∈ relativeBoundarySupport faceBoundary S ↔
      e ∈ S.biUnion faceBoundary ∧ subsetIncidenceCount faceBoundary S e = 1 := by
  simp [relativeBoundarySupport]

omit [DecidableEq F] in
theorem subsetIncidenceCount_eq_totalIncidenceCount (faceBoundary : F → Finset E)
    (allFaces : Finset F) (e : E) :
    subsetIncidenceCount faceBoundary allFaces e = totalIncidenceCount faceBoundary allFaces e :=
  rfl

omit [DecidableEq F] in
theorem relativeBoundarySupport_eq_selectedBoundarySupport (faceBoundary : F → Finset E)
    (allFaces : Finset F) :
    relativeBoundarySupport faceBoundary allFaces =
      selectedBoundarySupport faceBoundary allFaces allFaces := by
  ext e
  simp [relativeBoundarySupport, selectedBoundarySupport, subsetIncidenceCount, totalIncidenceCount]

omit [DecidableEq F] in
theorem mem_relativeBoundarySupport_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_mem_of_not_mem
    (faceBoundary : F → Finset E) (allFaces S : Finset F)
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2)
    (hS : S ⊆ allFaces)
    {f g : F} {e : E}
    (hf : f ∈ allFaces) (_hg : g ∈ allFaces) (_hfg : f ≠ g)
    (hef : e ∈ faceBoundary f) (heg : e ∈ faceBoundary g)
    (hgS : g ∈ S) (hfS : f ∉ S) :
    e ∈ relativeBoundarySupport faceBoundary S := by
  refine (mem_relativeBoundarySupport_iff faceBoundary S).2 ?_
  constructor
  · exact Finset.mem_biUnion.2 ⟨g, hgS, heg⟩
  · have hpos : 0 < subsetIncidenceCount faceBoundary S e := by
      unfold subsetIncidenceCount
      exact Finset.card_pos.2 ⟨g, Finset.mem_filter.2 ⟨hgS, heg⟩⟩
    have hle1 : subsetIncidenceCount faceBoundary S e ≤ 1 := by
      by_contra hle1
      have hgt1 : 1 < subsetIncidenceCount faceBoundary S e := Nat.lt_of_not_ge hle1
      unfold subsetIncidenceCount at hgt1
      rcases Finset.one_lt_card.1 hgt1 with ⟨g₁, hg₁, g₂, hg₂, hg₁₂⟩
      have hg₁S : g₁ ∈ S := (Finset.mem_filter.1 hg₁).1
      have hg₁e : e ∈ faceBoundary g₁ := (Finset.mem_filter.1 hg₁).2
      have hg₂S : g₂ ∈ S := (Finset.mem_filter.1 hg₂).1
      have hg₂e : e ∈ faceBoundary g₂ := (Finset.mem_filter.1 hg₂).2
      have hf_ne_g₁ : f ≠ g₁ := by
        intro h
        exact hfS (h ▸ hg₁S)
      have hf_ne_g₂ : f ≠ g₂ := by
        intro h
        exact hfS (h ▸ hg₂S)
      have hgt2 : 2 < totalIncidenceCount faceBoundary allFaces e := by
        unfold totalIncidenceCount
        rw [Finset.two_lt_card]
        refine ⟨f, Finset.mem_filter.2 ⟨hf, hef⟩,
          g₁, Finset.mem_filter.2 ⟨hS hg₁S, hg₁e⟩,
          g₂, Finset.mem_filter.2 ⟨hS hg₂S, hg₂e⟩,
          hf_ne_g₁, hf_ne_g₂, hg₁₂⟩
      exact Nat.not_lt_of_ge (hall e) hgt2
    omega

/-- The ambient face type used as the vertex set of the interior dual graph. -/
abbrev AmbientFace (allFaces : Finset F) := {f // f ∈ allFaces}

/-- Interior edges are the ambient edges incident to exactly two ambient faces. -/
def interiorEdgeSupport (faceBoundary : F → Finset E) (allFaces : Finset F) : Finset E :=
  (allFaces.biUnion faceBoundary).filter fun e => totalIncidenceCount faceBoundary allFaces e = 2

omit [DecidableEq F] in
theorem mem_interiorEdgeSupport_iff (faceBoundary : F → Finset E)
    (allFaces : Finset F) {e : E} :
    e ∈ interiorEdgeSupport faceBoundary allFaces ↔
      e ∈ allFaces.biUnion faceBoundary ∧ totalIncidenceCount faceBoundary allFaces e = 2 := by
  simp [interiorEdgeSupport]

omit [DecidableEq F] in
theorem selectedBoundarySupport_disjoint_interiorEdgeSupport
    (faceBoundary : F → Finset E) (allFaces : Finset F) :
    Disjoint (selectedBoundarySupport faceBoundary allFaces allFaces)
      (interiorEdgeSupport faceBoundary allFaces) := by
  rw [Finset.disjoint_left]
  intro e hboundary hinterior
  have hcountBoundary :=
    (mem_selectedBoundarySupport_iff faceBoundary allFaces allFaces).1 hboundary |>.2
  have hcountInterior := (mem_interiorEdgeSupport_iff faceBoundary allFaces).1 hinterior |>.2
  omega

omit [DecidableEq F] in
theorem totalIncidenceCount_pos_of_mem_biUnion (faceBoundary : F → Finset E)
    (allFaces : Finset F) {e : E} (he : e ∈ allFaces.biUnion faceBoundary) :
    0 < totalIncidenceCount faceBoundary allFaces e := by
  rcases Finset.mem_biUnion.1 he with ⟨f, hf, hfe⟩
  unfold totalIncidenceCount
  exact Finset.card_pos.2 ⟨f, Finset.mem_filter.2 ⟨hf, hfe⟩⟩

omit [DecidableEq F] in
theorem totalIncidenceCount_eq_zero_of_not_mem_biUnion (faceBoundary : F → Finset E)
    (allFaces : Finset F) {e : E} (he : e ∉ allFaces.biUnion faceBoundary) :
    totalIncidenceCount faceBoundary allFaces e = 0 := by
  unfold totalIncidenceCount
  have hfilter : allFaces.filter (fun f => e ∈ faceBoundary f) = ∅ := by
    ext f
    constructor
    · intro hf
      simpa using
        (he <| Finset.mem_biUnion.2
          ⟨f, (Finset.mem_filter.1 hf).1, (Finset.mem_filter.1 hf).2⟩)
    · intro hf
      simp at hf
  simp [hfilter]

omit [DecidableEq F] in
theorem totalIncidenceCount_le_of_boundary_subset
    (faceBoundary faceBoundary' : F → Finset E) (allFaces : Finset F)
    (hsub : ∀ f, faceBoundary f ⊆ faceBoundary' f) (e : E) :
    totalIncidenceCount faceBoundary allFaces e ≤
      totalIncidenceCount faceBoundary' allFaces e := by
  unfold totalIncidenceCount
  exact Finset.card_le_card <| by
    intro f hf
    exact Finset.mem_filter.2 ⟨
      (Finset.mem_filter.1 hf).1,
      hsub f (Finset.mem_filter.1 hf).2
    ⟩

omit [DecidableEq F] in
theorem subsetIncidenceCount_le_totalIncidenceCount_of_subset
    (faceBoundary : F → Finset E) {S allFaces : Finset F}
    (hS : S ⊆ allFaces) (e : E) :
    subsetIncidenceCount faceBoundary S e ≤ totalIncidenceCount faceBoundary allFaces e := by
  unfold subsetIncidenceCount totalIncidenceCount
  exact Finset.card_le_card <| by
    intro f hf
    exact Finset.mem_filter.2
      ⟨hS (Finset.mem_filter.1 hf).1, (Finset.mem_filter.1 hf).2⟩

omit [DecidableEq F] in
theorem mem_relativeBoundarySupport_of_mem_selectedBoundarySupport_of_mem_biUnion_of_subset
    (faceBoundary : F → Finset E) (allFaces S : Finset F)
    (hS : S ⊆ allFaces) {e : E}
    (heBoundary : e ∈ selectedBoundarySupport faceBoundary allFaces allFaces)
    (heS : e ∈ S.biUnion faceBoundary) :
    e ∈ relativeBoundarySupport faceBoundary S := by
  rcases (mem_selectedBoundarySupport_iff faceBoundary allFaces allFaces).1 heBoundary with
    ⟨_, hcount⟩
  refine (mem_relativeBoundarySupport_iff faceBoundary S).2 ?_
  constructor
  · exact heS
  · have hpos : 0 < subsetIncidenceCount faceBoundary S e := by
      unfold subsetIncidenceCount
      rcases Finset.mem_biUnion.1 heS with ⟨f, hf, hfe⟩
      exact Finset.card_pos.2 ⟨f, Finset.mem_filter.2 ⟨hf, hfe⟩⟩
    have hle :=
      subsetIncidenceCount_le_totalIncidenceCount_of_subset
        (faceBoundary := faceBoundary) hS e
    omega

omit [DecidableEq F] in
theorem selectedBoundarySupport_eq_empty_of_totalIncidenceCount_eq_two_on_biUnion
    (faceBoundary : F → Finset E) (allFaces S : Finset F)
    (hcount : ∀ e ∈ S.biUnion faceBoundary, totalIncidenceCount faceBoundary allFaces e = 2) :
    selectedBoundarySupport faceBoundary allFaces S = ∅ := by
  ext e
  constructor
  · intro he
    rcases (mem_selectedBoundarySupport_iff faceBoundary allFaces S).1 he with ⟨hmem, htot⟩
    rw [hcount e hmem] at htot
    omega
  · intro he
    simp at he

omit [DecidableEq F] in
theorem totalIncidenceCount_le_two_of_eq_two_on_biUnion (faceBoundary : F → Finset E)
    (allFaces : Finset F)
    (hcount : ∀ e ∈ allFaces.biUnion faceBoundary, totalIncidenceCount faceBoundary allFaces e = 2) :
    ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2 := by
  intro e
  by_cases he : e ∈ allFaces.biUnion faceBoundary
  · rw [hcount e he]
  · rw [totalIncidenceCount_eq_zero_of_not_mem_biUnion faceBoundary allFaces he]
    omega

omit [DecidableEq F] in
/-- When every ambient edge is incident to at most two ambient faces, the ambient face-edge support
decomposes into boundary edges (incidence count `1`) and interior edges (incidence count `2`). -/
theorem biUnion_eq_selectedBoundarySupport_union_interiorEdgeSupport_of_totalIncidenceCount_le_two
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2) :
    allFaces.biUnion faceBoundary =
      selectedBoundarySupport faceBoundary allFaces allFaces ∪
        interiorEdgeSupport faceBoundary allFaces := by
  ext e
  constructor
  · intro he
    have hpos : 0 < totalIncidenceCount faceBoundary allFaces e :=
      totalIncidenceCount_pos_of_mem_biUnion faceBoundary allFaces he
    have hcases : totalIncidenceCount faceBoundary allFaces e = 1 ∨
        totalIncidenceCount faceBoundary allFaces e = 2 := by
      have hle := hall e
      omega
    rcases hcases with hcount | hcount
    · exact Finset.mem_union.2 <| Or.inl <|
        (mem_selectedBoundarySupport_iff faceBoundary allFaces allFaces).2 ⟨he, hcount⟩
    · exact Finset.mem_union.2 <| Or.inr <|
        (mem_interiorEdgeSupport_iff faceBoundary allFaces).2 ⟨he, hcount⟩
  · intro he
    rcases Finset.mem_union.1 he with hboundary | hinterior
    · exact (mem_selectedBoundarySupport_iff faceBoundary allFaces allFaces).1 hboundary |>.1
    · exact (mem_interiorEdgeSupport_iff faceBoundary allFaces).1 hinterior |>.1

/-- The interior edges shared by two ambient faces. -/
def sharedInteriorEdges (faceBoundary : F → Finset E) (allFaces : Finset F) (f g : F) :
    Finset E :=
  (interiorEdgeSupport faceBoundary allFaces).filter fun e =>
    e ∈ faceBoundary f ∧ e ∈ faceBoundary g

omit [DecidableEq F] in
theorem mem_sharedInteriorEdges_iff (faceBoundary : F → Finset E)
    (allFaces : Finset F) {f g : F} {e : E} :
    e ∈ sharedInteriorEdges faceBoundary allFaces f g ↔
      e ∈ interiorEdgeSupport faceBoundary allFaces ∧
        e ∈ faceBoundary f ∧ e ∈ faceBoundary g := by
  simp [sharedInteriorEdges, and_left_comm]

/-- The abstract interior dual graph of a finite face-incidence model: vertices are ambient faces,
and two distinct faces are adjacent when they share an interior edge. This matches the graph used
in Goertzel v23 Lemma 4.6. -/
def interiorDualGraph (faceBoundary : F → Finset E) (allFaces : Finset F) :
    SimpleGraph (AmbientFace allFaces) where
  Adj f g := f.1 ≠ g.1 ∧
    ∃ e, e ∈ interiorEdgeSupport faceBoundary allFaces ∧
      e ∈ faceBoundary f.1 ∧ e ∈ faceBoundary g.1
  symm := by
    intro f g hfg
    rcases hfg with ⟨hneq, e, heint, hef, heg⟩
    exact ⟨hneq.symm, e, heint, heg, hef⟩
  loopless := ⟨by
    intro f hff
    exact hff.1 rfl
  ⟩

omit [DecidableEq F] in
theorem interiorDualGraph_adj_iff (faceBoundary : F → Finset E)
    (allFaces : Finset F) {f g : AmbientFace allFaces} :
    (interiorDualGraph faceBoundary allFaces).Adj f g ↔
      f.1 ≠ g.1 ∧
      ∃ e, e ∈ interiorEdgeSupport faceBoundary allFaces ∧
        e ∈ faceBoundary f.1 ∧ e ∈ faceBoundary g.1 := by
  rfl

omit [DecidableEq F] in
theorem totalIncidenceCount_eq_two_of_mem_faceBoundary_of_mem_faceBoundary_of_ne
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2)
    {f g : F} {e : E}
    (hf : f ∈ allFaces) (hg : g ∈ allFaces) (hfg : f ≠ g)
    (hef : e ∈ faceBoundary f) (heg : e ∈ faceBoundary g) :
    totalIncidenceCount faceBoundary allFaces e = 2 := by
  have hgt : 1 < totalIncidenceCount faceBoundary allFaces e := by
    unfold totalIncidenceCount
    rw [Finset.one_lt_card]
    exact ⟨f, Finset.mem_filter.2 ⟨hf, hef⟩, g, Finset.mem_filter.2 ⟨hg, heg⟩, hfg⟩
  have hle := hall e
  omega

omit [DecidableEq F] in
theorem eq_or_eq_of_mem_faceBoundary_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2)
    {f g h : F} {e : E}
    (hf : f ∈ allFaces) (hg : g ∈ allFaces) (hh : h ∈ allFaces)
    (hfg : f ≠ g)
    (hef : e ∈ faceBoundary f) (heg : e ∈ faceBoundary g) (heh : e ∈ faceBoundary h) :
    h = f ∨ h = g := by
  by_contra hneq
  have hhf : h ≠ f := by
    intro hh'
    exact hneq (Or.inl hh')
  have hhg : h ≠ g := by
    intro hh'
    exact hneq (Or.inr hh')
  have hgt : 2 < totalIncidenceCount faceBoundary allFaces e := by
    unfold totalIncidenceCount
    exact Finset.two_lt_card.2
      ⟨f, Finset.mem_filter.2 ⟨hf, hef⟩,
        g, Finset.mem_filter.2 ⟨hg, heg⟩,
        h, Finset.mem_filter.2 ⟨hh, heh⟩,
        hfg, hhf.symm, hhg.symm⟩
  exact (not_lt_of_ge (hall e)) hgt

omit [DecidableEq F] in
theorem interiorDualGraph_adj_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2)
    {f g : AmbientFace allFaces} {e : E}
    (hfg : f.1 ≠ g.1) (hef : e ∈ faceBoundary f.1) (heg : e ∈ faceBoundary g.1) :
    (interiorDualGraph faceBoundary allFaces).Adj f g := by
  refine (interiorDualGraph_adj_iff faceBoundary allFaces).2 ?_
  refine ⟨hfg, e, ?_, hef, heg⟩
  exact (mem_interiorEdgeSupport_iff faceBoundary allFaces).2
    ⟨Finset.mem_biUnion.2 ⟨f.1, f.2, hef⟩,
      totalIncidenceCount_eq_two_of_mem_faceBoundary_of_mem_faceBoundary_of_ne
        faceBoundary allFaces hall f.2 g.2 hfg hef heg⟩

omit [DecidableEq F] in
theorem interiorDualGraph_adj_iff_sharedInteriorEdges_nonempty
    (faceBoundary : F → Finset E) (allFaces : Finset F) {f g : AmbientFace allFaces} :
    (interiorDualGraph faceBoundary allFaces).Adj f g ↔
      f.1 ≠ g.1 ∧ (sharedInteriorEdges faceBoundary allFaces f.1 g.1).Nonempty := by
  constructor
  · intro hfg
    rcases (interiorDualGraph_adj_iff faceBoundary allFaces).1 hfg with ⟨hneq, e, heint, hef, heg⟩
    exact ⟨hneq, ⟨e, (mem_sharedInteriorEdges_iff faceBoundary allFaces).2 ⟨heint, hef, heg⟩⟩⟩
  · rintro ⟨hneq, ⟨e, he⟩⟩
    rcases (mem_sharedInteriorEdges_iff faceBoundary allFaces).1 he with ⟨heint, hef, heg⟩
    exact (interiorDualGraph_adj_iff faceBoundary allFaces).2 ⟨hneq, e, heint, hef, heg⟩

omit [DecidableEq F] in
theorem exists_mem_sharedInteriorEdges_of_adj (faceBoundary : F → Finset E)
    (allFaces : Finset F) {f g : AmbientFace allFaces}
    (hfg : (interiorDualGraph faceBoundary allFaces).Adj f g) :
    ∃ e, e ∈ sharedInteriorEdges faceBoundary allFaces f.1 g.1 := by
  exact (interiorDualGraph_adj_iff_sharedInteriorEdges_nonempty faceBoundary allFaces).1 hfg |>.2

/-- Pairwise uniqueness of shared interior edges. This is the extra incidence hypothesis needed
to recover a unique primal witness edge from an adjacency in the simple interior dual graph. -/
def PairwiseUniqueSharedInteriorEdges (faceBoundary : F → Finset E)
    (allFaces : Finset F) : Prop :=
  ∀ f ∈ allFaces, ∀ g ∈ allFaces, f ≠ g →
    (sharedInteriorEdges faceBoundary allFaces f g).card ≤ 1

omit [DecidableEq F] in
theorem pairwiseUniqueSharedInteriorEdges_of_interiorEdgeSupport_eq_empty
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (hnoInterior : interiorEdgeSupport faceBoundary allFaces = ∅) :
    PairwiseUniqueSharedInteriorEdges faceBoundary allFaces := by
  intro f _hf g _hg _hfg
  simp [sharedInteriorEdges, hnoInterior]

omit [DecidableEq F] in
theorem existsUnique_sharedInteriorEdge_of_adj_of_pairwiseUnique
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    {f g : AmbientFace allFaces}
    (hfg : (interiorDualGraph faceBoundary allFaces).Adj f g) :
    ∃! e, e ∈ sharedInteriorEdges faceBoundary allFaces f.1 g.1 := by
  rcases (interiorDualGraph_adj_iff_sharedInteriorEdges_nonempty faceBoundary allFaces).1 hfg with
    ⟨hneq, ⟨e, he⟩⟩
  refine ⟨e, he, ?_⟩
  intro e' he'
  exact (Finset.card_le_one_iff.1 (hunique f.1 f.2 g.1 g.2 hneq)) he' he

/-- The canonical primal interior edge attached to a dual adjacency, under pairwise uniqueness of
shared interior edges. -/
noncomputable def sharedInteriorEdgeOfAdjOfPairwiseUnique
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    {f g : AmbientFace allFaces}
    (hfg : (interiorDualGraph faceBoundary allFaces).Adj f g) : E :=
  Classical.choose <|
    existsUnique_sharedInteriorEdge_of_adj_of_pairwiseUnique
      faceBoundary allFaces hunique hfg

omit [DecidableEq F] in
theorem sharedInteriorEdgeOfAdjOfPairwiseUnique_mem_sharedInteriorEdges
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    {f g : AmbientFace allFaces}
    (hfg : (interiorDualGraph faceBoundary allFaces).Adj f g) :
    sharedInteriorEdgeOfAdjOfPairwiseUnique faceBoundary allFaces hunique hfg ∈
      sharedInteriorEdges faceBoundary allFaces f.1 g.1 := by
  exact (Classical.choose_spec <|
    existsUnique_sharedInteriorEdge_of_adj_of_pairwiseUnique faceBoundary allFaces hunique hfg
  ).1

omit [DecidableEq F] in
theorem sharedInteriorEdgeOfAdjOfPairwiseUnique_eq_of_mem_sharedInteriorEdges
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    {f g : AmbientFace allFaces}
    (hfg : (interiorDualGraph faceBoundary allFaces).Adj f g)
    {e : E} (he : e ∈ sharedInteriorEdges faceBoundary allFaces f.1 g.1) :
    sharedInteriorEdgeOfAdjOfPairwiseUnique faceBoundary allFaces hunique hfg = e := by
  have hneq : f.1 ≠ g.1 := (interiorDualGraph_adj_iff faceBoundary allFaces).1 hfg |>.1
  exact (hunique f.1 f.2 g.1 g.2 hneq |> Finset.card_le_one_iff.1)
    (sharedInteriorEdgeOfAdjOfPairwiseUnique_mem_sharedInteriorEdges faceBoundary allFaces hunique hfg) he

omit [DecidableEq F] in
theorem sharedInteriorEdgeOfAdjOfPairwiseUnique_mem_faceBoundary_left
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    {f g : AmbientFace allFaces}
    (hfg : (interiorDualGraph faceBoundary allFaces).Adj f g) :
    sharedInteriorEdgeOfAdjOfPairwiseUnique faceBoundary allFaces hunique hfg ∈ faceBoundary f.1 := by
  exact (mem_sharedInteriorEdges_iff faceBoundary allFaces).1
      (sharedInteriorEdgeOfAdjOfPairwiseUnique_mem_sharedInteriorEdges
        faceBoundary allFaces hunique hfg) |>.2.1

omit [DecidableEq F] in
theorem sharedInteriorEdgeOfAdjOfPairwiseUnique_mem_faceBoundary_right
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    {f g : AmbientFace allFaces}
    (hfg : (interiorDualGraph faceBoundary allFaces).Adj f g) :
    sharedInteriorEdgeOfAdjOfPairwiseUnique faceBoundary allFaces hunique hfg ∈ faceBoundary g.1 := by
  exact (mem_sharedInteriorEdges_iff faceBoundary allFaces).1
      (sharedInteriorEdgeOfAdjOfPairwiseUnique_mem_sharedInteriorEdges
        faceBoundary allFaces hunique hfg) |>.2.2

omit [DecidableEq F] in
/-- Abstract form of Goertzel v23 Lemma 4.6: the finite interior dual graph admits a spanning
forest. -/
theorem interiorDualGraph_exists_spanningForest
    (faceBoundary : F → Finset E) (allFaces : Finset F) :
    ∃ T ≤ interiorDualGraph faceBoundary allFaces,
      T.IsAcyclic ∧ T.Reachable = (interiorDualGraph faceBoundary allFaces).Reachable := by
  simpa using
    (interiorDualGraph faceBoundary allFaces).exists_isAcyclic_reachable_eq_le

end Mettapedia.GraphTheory.FourColor
