import Mettapedia.GraphTheory.FourColor.FaceIncidence
import Mettapedia.GraphTheory.FourColor.GoertzelLemma47

namespace Mettapedia.GraphTheory.FourColor

variable {F E : Type*} [DecidableEq F] [DecidableEq E]

/-- The face-cut support: edges incident to exactly two ambient faces and to exactly one selected
face. -/
def faceCutSupport (faceBoundary : F → Finset E)
    (allFaces S : Finset F) : Finset E :=
  (S.biUnion faceBoundary).filter fun e =>
    totalIncidenceCount faceBoundary allFaces e = 2 ∧
      selectedIncidenceCount faceBoundary S e = 1

omit [DecidableEq F] in
theorem selectedIncidenceCount_le_totalIncidenceCount
    (faceBoundary : F → Finset E) {S allFaces : Finset F} (hS : S ⊆ allFaces) (e : E) :
    selectedIncidenceCount faceBoundary S e ≤ totalIncidenceCount faceBoundary allFaces e := by
  unfold selectedIncidenceCount totalIncidenceCount
  exact Finset.card_le_card <| by
    intro f hf
    exact Finset.mem_filter.2 ⟨hS (Finset.mem_filter.1 hf).1, (Finset.mem_filter.1 hf).2⟩

omit [DecidableEq F] in
theorem selectedIncidenceCount_pos_of_mem_biUnion (faceBoundary : F → Finset E)
    {S : Finset F} {e : E} (he : e ∈ S.biUnion faceBoundary) :
    0 < selectedIncidenceCount faceBoundary S e := by
  rcases Finset.mem_biUnion.1 he with ⟨f, hfS, hfe⟩
  unfold selectedIncidenceCount
  exact Finset.card_pos.2 ⟨f, Finset.mem_filter.2 ⟨hfS, hfe⟩⟩

omit [DecidableEq F] in
theorem selectedIncidenceCount_eq_totalIncidenceCount (faceBoundary : F → Finset E)
    (allFaces : Finset F) (e : E) :
    selectedIncidenceCount faceBoundary allFaces e = totalIncidenceCount faceBoundary allFaces e := by
  simp [selectedIncidenceCount, totalIncidenceCount]

omit [DecidableEq F] in
theorem mem_faceCutSupport_iff (faceBoundary : F → Finset E)
    (allFaces S : Finset F) {e : E} :
    e ∈ faceCutSupport faceBoundary allFaces S ↔
      e ∈ S.biUnion faceBoundary ∧
      totalIncidenceCount faceBoundary allFaces e = 2 ∧
      selectedIncidenceCount faceBoundary S e = 1 := by
  simp [faceCutSupport]

omit [DecidableEq F] in
/-- If every ambient face is selected, there are no cut edges to a complementary face set. -/
theorem faceCutSupport_eq_empty_of_allFaces (faceBoundary : F → Finset E)
    (allFaces : Finset F) :
    faceCutSupport faceBoundary allFaces allFaces = ∅ := by
  ext e
  constructor
  · intro he
    rcases (mem_faceCutSupport_iff faceBoundary allFaces allFaces).1 he with ⟨_, htot, hsel⟩
    rw [selectedIncidenceCount_eq_totalIncidenceCount faceBoundary allFaces e] at hsel
    omega
  · intro he
    simp at he

omit [DecidableEq F] in
/-- Generic support decomposition for the combinatorial content of Goertzel v23 Lemma 4.7. -/
theorem cutParitySupport_eq_selectedBoundarySupport_union_faceCutSupport
    (faceBoundary : F → Finset E) (allFaces S : Finset F)
    (hS : S ⊆ allFaces)
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2) :
    cutParitySupport faceBoundary S =
      selectedBoundarySupport faceBoundary allFaces S ∪
        faceCutSupport faceBoundary allFaces S := by
  ext e
  constructor
  · intro he
    have hsel : selectedIncidenceCount faceBoundary S e = 1 :=
      (mem_cutParitySupport_iff faceBoundary S).1 he
    have hsel_le : selectedIncidenceCount faceBoundary S e ≤ totalIncidenceCount faceBoundary allFaces e :=
      selectedIncidenceCount_le_totalIncidenceCount faceBoundary hS e
    have htot_pos : 0 < totalIncidenceCount faceBoundary allFaces e := by
      omega
    have htot_cases : totalIncidenceCount faceBoundary allFaces e = 1 ∨
        totalIncidenceCount faceBoundary allFaces e = 2 := by
      have htot_le : totalIncidenceCount faceBoundary allFaces e ≤ 2 := hall e
      omega
    rcases htot_cases with htot | htot
    · exact Finset.mem_union.2 <| Or.inl <|
        (mem_selectedBoundarySupport_iff faceBoundary allFaces S).2 ⟨
          mem_biUnion_of_selectedIncidenceCount_eq_one faceBoundary S hsel,
          htot⟩
    · exact Finset.mem_union.2 <| Or.inr <|
        (mem_faceCutSupport_iff faceBoundary allFaces S).2 ⟨
          mem_biUnion_of_selectedIncidenceCount_eq_one faceBoundary S hsel,
          htot,
          hsel⟩
  · intro he
    rcases Finset.mem_union.1 he with hboundary | hcut
    · rcases (mem_selectedBoundarySupport_iff faceBoundary allFaces S).1 hboundary with ⟨hmem, htot⟩
      have hsel_pos : 0 < selectedIncidenceCount faceBoundary S e := by
        exact selectedIncidenceCount_pos_of_mem_biUnion faceBoundary hmem
      have hsel_le : selectedIncidenceCount faceBoundary S e ≤ totalIncidenceCount faceBoundary allFaces e :=
        selectedIncidenceCount_le_totalIncidenceCount faceBoundary hS e
      have hsel : selectedIncidenceCount faceBoundary S e = 1 := by
        omega
      exact (mem_cutParitySupport_iff faceBoundary S).2 hsel
    · rcases (mem_faceCutSupport_iff faceBoundary allFaces S).1 hcut with ⟨_, _, hsel⟩
      exact (mem_cutParitySupport_iff faceBoundary S).2 hsel

omit [DecidableEq F] in
/-- Full-face specialization of the Lemma 4.7 support decomposition: only ambient boundary edges
survive. -/
theorem cutParitySupport_eq_selectedBoundarySupport_of_allFaces
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2) :
    cutParitySupport faceBoundary allFaces =
      selectedBoundarySupport faceBoundary allFaces allFaces := by
  rw [cutParitySupport_eq_selectedBoundarySupport_union_faceCutSupport
    (faceBoundary := faceBoundary) (allFaces := allFaces) (S := allFaces) (by simp) hall]
  rw [faceCutSupport_eq_empty_of_allFaces]
  simp

omit [DecidableEq F] in
/-- If every ambient boundary edge is incident to exactly two ambient faces, the full-face boundary
support is empty. -/
theorem selectedBoundarySupport_eq_empty_of_allFaces_totalIncidenceCount_eq_two
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (hcount : ∀ e ∈ allFaces.biUnion faceBoundary, totalIncidenceCount faceBoundary allFaces e = 2) :
    selectedBoundarySupport faceBoundary allFaces allFaces = ∅ :=
  selectedBoundarySupport_eq_empty_of_totalIncidenceCount_eq_two_on_biUnion
    faceBoundary allFaces allFaces hcount

/-- Full-face cancellation: if every ambient boundary edge is incident to exactly two ambient
faces, the total boundary-indicator sum vanishes. -/
theorem boundaryIndicatorSum_eq_zero_of_allFaces_totalIncidenceCount_eq_two
    (γ : Color) (faceBoundary : F → Finset E) (allFaces : Finset F)
    (hcount : ∀ e ∈ allFaces.biUnion faceBoundary, totalIncidenceCount faceBoundary allFaces e = 2) :
    boundaryIndicatorSum γ faceBoundary allFaces = 0 := by
  have hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2 :=
    totalIncidenceCount_le_two_of_eq_two_on_biUnion faceBoundary allFaces hcount
  have hinc : ∀ e, selectedIncidenceCount faceBoundary allFaces e ≤ 2 := by
    intro e
    rw [selectedIncidenceCount_eq_totalIncidenceCount faceBoundary allFaces e]
    exact hall e
  rw [boundaryIndicatorSum_eq_indicatorChain_cutParitySupport
    (γ := γ) (faceBoundary := faceBoundary) (S := allFaces) hinc]
  rw [cutParitySupport_eq_selectedBoundarySupport_of_allFaces faceBoundary allFaces hall]
  rw [selectedBoundarySupport_eq_empty_of_allFaces_totalIncidenceCount_eq_two
    faceBoundary allFaces hcount]
  funext e
  simp [indicatorChain]

variable {V : Type*} [DecidableEq V]

omit [DecidableEq F] in
theorem totalIncidenceCount_boundaryBicoloredEdges_le {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (a b : Color)
    (faceBoundary : F → Finset G.edgeSet) (allFaces : Finset F) (e : G.edgeSet) :
    totalIncidenceCount (fun f => boundaryBicoloredEdges C a b (faceBoundary f)) allFaces e ≤
      totalIncidenceCount faceBoundary allFaces e := by
  exact totalIncidenceCount_le_of_boundary_subset
    (faceBoundary := fun f => boundaryBicoloredEdges C a b (faceBoundary f))
    (faceBoundary' := faceBoundary) allFaces
    (fun f e he => (mem_boundaryBicoloredEdges_iff C a b).1 he |>.1)
    e

theorem totalIncidenceCount_boundaryBicoloredEdges_eq_two_of_mem_biUnion_of_totalIncidenceCount_eq_two
    {G : SimpleGraph V} (C : G.EdgeColoring Color) (a b : Color)
    (faceBoundary : F → Finset G.edgeSet) (allFaces : Finset F)
    (hcount : ∀ e ∈ allFaces.biUnion faceBoundary, totalIncidenceCount faceBoundary allFaces e = 2)
    {e : G.edgeSet}
    (he : e ∈ allFaces.biUnion (fun f => boundaryBicoloredEdges C a b (faceBoundary f))) :
    totalIncidenceCount (fun f => boundaryBicoloredEdges C a b (faceBoundary f)) allFaces e = 2 := by
  rcases Finset.mem_biUnion.1 he with ⟨f, hf, hfe⟩
  rcases (mem_boundaryBicoloredEdges_iff C a b).1 hfe with ⟨hef, hcolor⟩
  have hcount_e : totalIncidenceCount faceBoundary allFaces e = 2 :=
    hcount e (Finset.mem_biUnion.2 ⟨f, hf, hef⟩)
  let s : Finset F := allFaces.filter fun g => e ∈ faceBoundary g
  have hs_card : s.card = 2 := by
    simpa [s, totalIncidenceCount] using hcount_e
  have hfmem : f ∈ s := by
    exact Finset.mem_filter.2 ⟨hf, hef⟩
  rcases Finset.card_eq_two.1 hs_card with ⟨u, v, huv, hs⟩
  have hfuv : f = u ∨ f = v := by
    simpa [s, hs, huv] using hfmem
  have hall : ∀ e', totalIncidenceCount faceBoundary allFaces e' ≤ 2 :=
    totalIncidenceCount_le_two_of_eq_two_on_biUnion faceBoundary allFaces hcount
  have hfiltered_le : ∀ e',
      totalIncidenceCount (fun g => boundaryBicoloredEdges C a b (faceBoundary g)) allFaces e' ≤ 2 := by
    intro e'
    exact le_trans
      (totalIncidenceCount_boundaryBicoloredEdges_le C a b faceBoundary allFaces e')
      (hall e')
  rcases hfuv with rfl | rfl
  · have hvmem : v ∈ s := by
      simp [s, hs]
    have hv : v ∈ allFaces := (Finset.mem_filter.1 hvmem).1
    have hev : e ∈ faceBoundary v := (Finset.mem_filter.1 hvmem).2
    have hve : e ∈ boundaryBicoloredEdges C a b (faceBoundary v) :=
      (mem_boundaryBicoloredEdges_iff C a b).2 ⟨hev, hcolor⟩
    exact totalIncidenceCount_eq_two_of_mem_faceBoundary_of_mem_faceBoundary_of_ne
      (faceBoundary := fun g => boundaryBicoloredEdges C a b (faceBoundary g))
      (allFaces := allFaces) hfiltered_le hf hv huv hfe hve
  · have humem : u ∈ s := by
      simp [s, hs]
    have hu : u ∈ allFaces := (Finset.mem_filter.1 humem).1
    have heu : e ∈ faceBoundary u := (Finset.mem_filter.1 humem).2
    have hue : e ∈ boundaryBicoloredEdges C a b (faceBoundary u) :=
      (mem_boundaryBicoloredEdges_iff C a b).2 ⟨heu, hcolor⟩
    exact totalIncidenceCount_eq_two_of_mem_faceBoundary_of_mem_faceBoundary_of_ne
      (faceBoundary := fun g => boundaryBicoloredEdges C a b (faceBoundary g))
      (allFaces := allFaces) hfiltered_le hf hu huv.symm hfe hue

/-- Route-facing restatement of Lemma 4.7 for the current boundary-only generators. -/
theorem sum_polarizedFaceGenerators_eq_indicatorChain_supportDecomposition {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (a b : Color)
    (faceBoundary : F → Finset G.edgeSet) (allFaces S : Finset F)
    (hS : S ⊆ allFaces)
    (hall : ∀ e,
      totalIncidenceCount (fun f => boundaryBicoloredEdges C a b (faceBoundary f)) allFaces e ≤ 2) :
    Finset.sum S (fun f => polarizedFaceGenerator C a b (faceBoundary f)) =
      indicatorChain (a + b)
        (selectedBoundarySupport
          (fun f => boundaryBicoloredEdges C a b (faceBoundary f)) allFaces S ∪
         faceCutSupport
          (fun f => boundaryBicoloredEdges C a b (faceBoundary f)) allFaces S) := by
  have hinc : ∀ e,
      selectedIncidenceCount (fun f => boundaryBicoloredEdges C a b (faceBoundary f)) S e ≤ 2 := by
    intro e
    exact le_trans
      (selectedIncidenceCount_le_totalIncidenceCount
        (faceBoundary := fun f => boundaryBicoloredEdges C a b (faceBoundary f)) hS e)
      (hall e)
  rw [sum_polarizedFaceGenerators_eq_indicatorChain_cutParitySupport
    (C := C) (a := a) (b := b) (faceBoundary := faceBoundary) (S := S) (hinc := hinc)]
  rw [cutParitySupport_eq_selectedBoundarySupport_union_faceCutSupport
    (faceBoundary := fun f => boundaryBicoloredEdges C a b (faceBoundary f))
    (allFaces := allFaces) (S := S) hS hall]

/-- Route-facing restatement of Lemma 4.7 for the current boundary-only generators, now using the
ambient at-most-two-faces incidence bound on the original face-boundary model. -/
theorem sum_polarizedFaceGenerators_eq_indicatorChain_supportDecomposition_of_totalIncidenceCount_le_two
    {G : SimpleGraph V} (C : G.EdgeColoring Color) (a b : Color)
    (faceBoundary : F → Finset G.edgeSet) (allFaces S : Finset F)
    (hS : S ⊆ allFaces)
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2) :
    Finset.sum S (fun f => polarizedFaceGenerator C a b (faceBoundary f)) =
      indicatorChain (a + b)
        (selectedBoundarySupport
          (fun f => boundaryBicoloredEdges C a b (faceBoundary f)) allFaces S ∪
         faceCutSupport
          (fun f => boundaryBicoloredEdges C a b (faceBoundary f)) allFaces S) := by
  apply sum_polarizedFaceGenerators_eq_indicatorChain_supportDecomposition
    (C := C) (a := a) (b := b) (faceBoundary := faceBoundary)
    (allFaces := allFaces) (S := S) hS
  intro e
  exact le_trans
    (totalIncidenceCount_boundaryBicoloredEdges_le C a b faceBoundary allFaces e)
    (hall e)

/-- Summing the current boundary-only generators over all ambient faces leaves only the selected
ambient boundary support. -/
theorem sum_polarizedFaceGenerators_eq_indicatorChain_selectedBoundarySupport_of_allFaces
    {G : SimpleGraph V} (C : G.EdgeColoring Color) (a b : Color)
    (faceBoundary : F → Finset G.edgeSet) (allFaces : Finset F)
    (hall : ∀ e,
      totalIncidenceCount (fun f => boundaryBicoloredEdges C a b (faceBoundary f)) allFaces e ≤ 2) :
    Finset.sum allFaces (fun f => polarizedFaceGenerator C a b (faceBoundary f)) =
      indicatorChain (a + b)
        (selectedBoundarySupport
          (fun f => boundaryBicoloredEdges C a b (faceBoundary f)) allFaces allFaces) := by
  rw [sum_polarizedFaceGenerators_eq_indicatorChain_supportDecomposition
    (C := C) (a := a) (b := b) (faceBoundary := faceBoundary)
    (allFaces := allFaces) (S := allFaces) (by simp) hall]
  rw [faceCutSupport_eq_empty_of_allFaces
    (faceBoundary := fun f => boundaryBicoloredEdges C a b (faceBoundary f))
    (allFaces := allFaces)]
  simp

/-- Full-face specialization of the filtered-support identity using only the original ambient
incidence bound. -/
theorem sum_polarizedFaceGenerators_eq_indicatorChain_selectedBoundarySupport_of_allFaces_of_totalIncidenceCount_le_two
    {G : SimpleGraph V} (C : G.EdgeColoring Color) (a b : Color)
    (faceBoundary : F → Finset G.edgeSet) (allFaces : Finset F)
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2) :
    Finset.sum allFaces (fun f => polarizedFaceGenerator C a b (faceBoundary f)) =
      indicatorChain (a + b)
        (selectedBoundarySupport
          (fun f => boundaryBicoloredEdges C a b (faceBoundary f)) allFaces allFaces) := by
  rw [sum_polarizedFaceGenerators_eq_indicatorChain_supportDecomposition_of_totalIncidenceCount_le_two
    (C := C) (a := a) (b := b) (faceBoundary := faceBoundary)
    (allFaces := allFaces) (S := allFaces) (by simp) hall]
  rw [faceCutSupport_eq_empty_of_allFaces
    (faceBoundary := fun f => boundaryBicoloredEdges C a b (faceBoundary f))
    (allFaces := allFaces)]
  simp

/-- If every selected boundary edge lies on two ambient faces, the full-face boundary-only
generator sum cancels identically. -/
theorem sum_polarizedFaceGenerators_eq_zero_of_allFaces_totalIncidenceCount_eq_two
    {G : SimpleGraph V} (C : G.EdgeColoring Color) (a b : Color)
    (faceBoundary : F → Finset G.edgeSet) (allFaces : Finset F)
    (hcount : ∀ e ∈ allFaces.biUnion (fun f => boundaryBicoloredEdges C a b (faceBoundary f)),
      totalIncidenceCount (fun f => boundaryBicoloredEdges C a b (faceBoundary f)) allFaces e = 2) :
    Finset.sum allFaces (fun f => polarizedFaceGenerator C a b (faceBoundary f)) = 0 := by
  funext e
  simpa [boundaryIndicatorSum, polarizedFaceGenerator] using
    congrArg (fun x => x e)
      (boundaryIndicatorSum_eq_zero_of_allFaces_totalIncidenceCount_eq_two
        (γ := a + b)
        (faceBoundary := fun f => boundaryBicoloredEdges C a b (faceBoundary f))
        (allFaces := allFaces)
        hcount)

/-- Full-face cancellation for the boundary-only generators using only the original ambient
incidence-`2` hypothesis on the underlying face-boundary model. -/
theorem sum_polarizedFaceGenerators_eq_zero_of_allFaces_ambientTotalIncidenceCount_eq_two
    {G : SimpleGraph V} (C : G.EdgeColoring Color) (a b : Color)
    (faceBoundary : F → Finset G.edgeSet) (allFaces : Finset F)
    (hcount : ∀ e ∈ allFaces.biUnion faceBoundary, totalIncidenceCount faceBoundary allFaces e = 2) :
    Finset.sum allFaces (fun f => polarizedFaceGenerator C a b (faceBoundary f)) = 0 := by
  apply sum_polarizedFaceGenerators_eq_zero_of_allFaces_totalIncidenceCount_eq_two
  intro e he
  exact totalIncidenceCount_boundaryBicoloredEdges_eq_two_of_mem_biUnion_of_totalIncidenceCount_eq_two
    C a b faceBoundary allFaces hcount he

/-- The same support decomposition for the literal finite component-sum generators from
Definition 4.8. -/
theorem sum_literalPolarizedFaceGenerators_eq_indicatorChain_supportDecomposition {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (a b : Color)
    (faceBoundary : F → Finset G.edgeSet) (allFaces S : Finset F)
    (hS : S ⊆ allFaces)
    (hall : ∀ e,
      totalIncidenceCount (fun f => boundaryBicoloredEdges C a b (faceBoundary f)) allFaces e ≤ 2) :
    Finset.sum S (fun f => literalPolarizedFaceGenerator C a b (faceBoundary f)) =
      indicatorChain (a + b)
        (selectedBoundarySupport
          (fun f => boundaryBicoloredEdges C a b (faceBoundary f)) allFaces S ∪
         faceCutSupport
          (fun f => boundaryBicoloredEdges C a b (faceBoundary f)) allFaces S) := by
  have hinc : ∀ e,
      selectedIncidenceCount (fun f => boundaryBicoloredEdges C a b (faceBoundary f)) S e ≤ 2 := by
    intro e
    exact le_trans
      (selectedIncidenceCount_le_totalIncidenceCount
        (faceBoundary := fun f => boundaryBicoloredEdges C a b (faceBoundary f)) hS e)
      (hall e)
  rw [sum_literalPolarizedFaceGenerators_eq_indicatorChain_cutParitySupport
    (C := C) (a := a) (b := b) (faceBoundary := faceBoundary) (S := S) (hinc := hinc)]
  rw [cutParitySupport_eq_selectedBoundarySupport_union_faceCutSupport
    (faceBoundary := fun f => boundaryBicoloredEdges C a b (faceBoundary f))
    (allFaces := allFaces) (S := S) hS hall]

/-- The same full-face support simplification for the literal finite component-sum generators from
Definition 4.8. -/
theorem sum_literalPolarizedFaceGenerators_eq_indicatorChain_selectedBoundarySupport_of_allFaces
    {G : SimpleGraph V} (C : G.EdgeColoring Color) (a b : Color)
    (faceBoundary : F → Finset G.edgeSet) (allFaces : Finset F)
    (hall : ∀ e,
      totalIncidenceCount (fun f => boundaryBicoloredEdges C a b (faceBoundary f)) allFaces e ≤ 2) :
    Finset.sum allFaces (fun f => literalPolarizedFaceGenerator C a b (faceBoundary f)) =
      indicatorChain (a + b)
        (selectedBoundarySupport
          (fun f => boundaryBicoloredEdges C a b (faceBoundary f)) allFaces allFaces) := by
  rw [sum_literalPolarizedFaceGenerators_eq_indicatorChain_supportDecomposition
    (C := C) (a := a) (b := b) (faceBoundary := faceBoundary)
    (allFaces := allFaces) (S := allFaces) (by simp) hall]
  rw [faceCutSupport_eq_empty_of_allFaces
    (faceBoundary := fun f => boundaryBicoloredEdges C a b (faceBoundary f))
    (allFaces := allFaces)]
  simp

/-- The same full-face support simplification for the literal finite component-sum generators,
using only the original ambient incidence bound. -/
theorem sum_literalPolarizedFaceGenerators_eq_indicatorChain_selectedBoundarySupport_of_allFaces_of_totalIncidenceCount_le_two
    {G : SimpleGraph V} (C : G.EdgeColoring Color) (a b : Color)
    (faceBoundary : F → Finset G.edgeSet) (allFaces : Finset F)
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2) :
    Finset.sum allFaces (fun f => literalPolarizedFaceGenerator C a b (faceBoundary f)) =
      indicatorChain (a + b)
        (selectedBoundarySupport
          (fun f => boundaryBicoloredEdges C a b (faceBoundary f)) allFaces allFaces) := by
  calc
    Finset.sum allFaces (fun f => literalPolarizedFaceGenerator C a b (faceBoundary f))
        = Finset.sum allFaces (fun f => polarizedFaceGenerator C a b (faceBoundary f)) := by
            refine Finset.sum_congr rfl ?_
            intro f hf
            exact literalPolarizedFaceGenerator_eq_polarizedFaceGenerator C a b (faceBoundary f)
    _ = indicatorChain (a + b)
          (selectedBoundarySupport
            (fun f => boundaryBicoloredEdges C a b (faceBoundary f)) allFaces allFaces) :=
        sum_polarizedFaceGenerators_eq_indicatorChain_selectedBoundarySupport_of_allFaces_of_totalIncidenceCount_le_two
          C a b faceBoundary allFaces hall

/-- The same full-face cancellation for the literal finite component-sum generators from
Definition 4.8. -/
theorem sum_literalPolarizedFaceGenerators_eq_zero_of_allFaces_totalIncidenceCount_eq_two
    {G : SimpleGraph V} (C : G.EdgeColoring Color) (a b : Color)
    (faceBoundary : F → Finset G.edgeSet) (allFaces : Finset F)
    (hcount : ∀ e ∈ allFaces.biUnion (fun f => boundaryBicoloredEdges C a b (faceBoundary f)),
      totalIncidenceCount (fun f => boundaryBicoloredEdges C a b (faceBoundary f)) allFaces e = 2) :
    Finset.sum allFaces (fun f => literalPolarizedFaceGenerator C a b (faceBoundary f)) = 0 := by
  calc
    Finset.sum allFaces (fun f => literalPolarizedFaceGenerator C a b (faceBoundary f))
        = Finset.sum allFaces (fun f => polarizedFaceGenerator C a b (faceBoundary f)) := by
            refine Finset.sum_congr rfl ?_
            intro f hf
            exact literalPolarizedFaceGenerator_eq_polarizedFaceGenerator C a b (faceBoundary f)
    _ = 0 := sum_polarizedFaceGenerators_eq_zero_of_allFaces_totalIncidenceCount_eq_two
      C a b faceBoundary allFaces hcount

/-- The same full-face cancellation for the literal finite component-sum generators, using only
the original ambient incidence-`2` hypothesis on the underlying face-boundary model. -/
theorem sum_literalPolarizedFaceGenerators_eq_zero_of_allFaces_ambientTotalIncidenceCount_eq_two
    {G : SimpleGraph V} (C : G.EdgeColoring Color) (a b : Color)
    (faceBoundary : F → Finset G.edgeSet) (allFaces : Finset F)
    (hcount : ∀ e ∈ allFaces.biUnion faceBoundary, totalIncidenceCount faceBoundary allFaces e = 2) :
    Finset.sum allFaces (fun f => literalPolarizedFaceGenerator C a b (faceBoundary f)) = 0 := by
  calc
    Finset.sum allFaces (fun f => literalPolarizedFaceGenerator C a b (faceBoundary f))
        = Finset.sum allFaces (fun f => polarizedFaceGenerator C a b (faceBoundary f)) := by
            refine Finset.sum_congr rfl ?_
            intro f hf
            exact literalPolarizedFaceGenerator_eq_polarizedFaceGenerator C a b (faceBoundary f)
    _ = 0 := sum_polarizedFaceGenerators_eq_zero_of_allFaces_ambientTotalIncidenceCount_eq_two
      C a b faceBoundary allFaces hcount

end Mettapedia.GraphTheory.FourColor
