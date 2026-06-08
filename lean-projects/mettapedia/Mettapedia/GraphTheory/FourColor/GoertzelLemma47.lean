import Mathlib.Data.Finset.Card
import Mettapedia.GraphTheory.FourColor.GoertzelDefinition48Literal

open scoped BigOperators

namespace Mettapedia.GraphTheory.FourColor

variable {F E : Type*} [DecidableEq F] [DecidableEq E]

/-- The number of selected faces whose boundary contains a given edge. -/
def selectedIncidenceCount (faceBoundary : F → Finset E) (S : Finset F) (e : E) : ℕ :=
  (S.filter fun f => e ∈ faceBoundary f).card

/-- The cut-parity support consists of the edges incident to exactly one selected face. -/
def cutParitySupport (faceBoundary : F → Finset E) (S : Finset F) : Finset E :=
  (S.biUnion faceBoundary).filter fun e => selectedIncidenceCount faceBoundary S e = 1

/-- Sum the constant boundary indicators over the selected face set. -/
def boundaryIndicatorSum (γ : Color) (faceBoundary : F → Finset E) (S : Finset F) : E → Color :=
  fun e => Finset.sum S (fun f => indicatorChain γ (faceBoundary f) e)

omit [DecidableEq F] in
theorem boundaryIndicatorSum_eq_incidenceFilterSum (γ : Color) (faceBoundary : F → Finset E)
    (S : Finset F) (e : E) :
    boundaryIndicatorSum γ faceBoundary S e =
      Finset.sum (S.filter (fun f => e ∈ faceBoundary f)) (fun _ => γ) := by
  calc
    boundaryIndicatorSum γ faceBoundary S e
        = Finset.sum S (fun f => if e ∈ faceBoundary f then γ else 0) := by
            simp [boundaryIndicatorSum, indicatorChain]
    _ = Finset.sum (S.filter (fun f => e ∈ faceBoundary f)) (fun _ => γ) := by
          rw [← Finset.sum_filter]

theorem sum_const_eq_ite_card_eq_one (γ : Color) {s : Finset F} (hs : s.card ≤ 2) :
    Finset.sum s (fun _ => γ) = if s.card = 1 then γ else 0 := by
  have hcases : s.card = 0 ∨ s.card = 1 ∨ s.card = 2 := by
    omega
  rcases hcases with h0 | h1 | h2
  · rcases Finset.card_eq_zero.mp h0 with rfl
    simp
  · rcases Finset.card_eq_one.mp h1 with ⟨a, rfl⟩
    simp
  · rcases Finset.card_eq_two.mp h2 with ⟨a, b, hab, rfl⟩
    calc
      Finset.sum ({a, b} : Finset F) (fun _ => γ) = 2 • γ := by
        simp [hab]
      _ = γ + γ := by rw [two_nsmul]
      _ = 0 := color_add_self γ
      _ = if ({a, b} : Finset F).card = 1 then γ else 0 := by
        simp [hab]

theorem boundaryIndicatorSum_eq_ite_selectedIncidenceCount_eq_one (γ : Color)
    (faceBoundary : F → Finset E) (S : Finset F)
    (hinc : ∀ e, selectedIncidenceCount faceBoundary S e ≤ 2) (e : E) :
    boundaryIndicatorSum γ faceBoundary S e =
      if selectedIncidenceCount faceBoundary S e = 1 then γ else 0 := by
  rw [boundaryIndicatorSum_eq_incidenceFilterSum, selectedIncidenceCount]
  exact sum_const_eq_ite_card_eq_one γ (hinc e)

omit [DecidableEq F] in
theorem mem_biUnion_of_selectedIncidenceCount_eq_one (faceBoundary : F → Finset E)
    (S : Finset F) {e : E} (he : selectedIncidenceCount faceBoundary S e = 1) :
    e ∈ S.biUnion faceBoundary := by
  have hcard : (S.filter fun f => e ∈ faceBoundary f).card = 1 := by
    simpa [selectedIncidenceCount] using he
  have hpos : 0 < (S.filter fun f => e ∈ faceBoundary f).card := by
    omega
  rcases Finset.card_pos.mp hpos with ⟨f, hf⟩
  exact Finset.mem_biUnion.2 ⟨f, (Finset.mem_filter.1 hf).1, (Finset.mem_filter.1 hf).2⟩

omit [DecidableEq F] in
theorem mem_cutParitySupport_iff (faceBoundary : F → Finset E) (S : Finset F) {e : E} :
    e ∈ cutParitySupport faceBoundary S ↔ selectedIncidenceCount faceBoundary S e = 1 := by
  constructor
  · intro he
    exact (Finset.mem_filter.1 he).2
  · intro he
    exact Finset.mem_filter.2 ⟨
      mem_biUnion_of_selectedIncidenceCount_eq_one faceBoundary S he,
      he⟩

/-- Abstract form of Goertzel v23 Lemma 4.7: if each edge is incident to at most two selected
face-boundary sets, then the sum of the boundary-only generators is exactly the indicator of the
edges incident to one selected face. -/
theorem boundaryIndicatorSum_eq_indicatorChain_cutParitySupport
    (γ : Color) (faceBoundary : F → Finset E) (S : Finset F)
    (hinc : ∀ e, selectedIncidenceCount faceBoundary S e ≤ 2) :
    boundaryIndicatorSum γ faceBoundary S = indicatorChain γ (cutParitySupport faceBoundary S) := by
  funext e
  rw [boundaryIndicatorSum_eq_ite_selectedIncidenceCount_eq_one γ faceBoundary S hinc]
  by_cases he : selectedIncidenceCount faceBoundary S e = 1
  · have hmem : e ∈ cutParitySupport faceBoundary S :=
      (mem_cutParitySupport_iff faceBoundary S).2 he
    simp [indicatorChain, hmem, he]
  · have hnot : e ∉ cutParitySupport faceBoundary S := by
      intro hmem
      exact he ((mem_cutParitySupport_iff faceBoundary S).1 hmem)
    simp [indicatorChain, hnot, he]

variable {V : Type*} [DecidableEq V]

/-- Route-specific specialization of the cut-parity identity to the boundary-only face generators
used in the Goertzel/Kauffman four-color route. -/
theorem sum_polarizedFaceGenerators_eq_indicatorChain_cutParitySupport {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (a b : Color)
    (faceBoundary : F → Finset G.edgeSet) (S : Finset F)
    (hinc : ∀ e,
      selectedIncidenceCount (fun f => boundaryBicoloredEdges C a b (faceBoundary f)) S e ≤ 2) :
    Finset.sum S (fun f => polarizedFaceGenerator C a b (faceBoundary f)) =
      indicatorChain (a + b)
        (cutParitySupport (fun f => boundaryBicoloredEdges C a b (faceBoundary f)) S) := by
  funext e
  simpa [boundaryIndicatorSum, polarizedFaceGenerator] using
    congrArg (fun x => x e)
      (boundaryIndicatorSum_eq_indicatorChain_cutParitySupport
        (γ := a + b)
        (faceBoundary := fun f => boundaryBicoloredEdges C a b (faceBoundary f))
        (S := S) hinc)

/-- The same cut-parity identity stated for the literal finite component-sum generator from
Definition 4.8, using the proven reduction to the simpler boundary-only form. -/
theorem sum_literalPolarizedFaceGenerators_eq_indicatorChain_cutParitySupport {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (a b : Color)
    (faceBoundary : F → Finset G.edgeSet) (S : Finset F)
    (hinc : ∀ e,
      selectedIncidenceCount (fun f => boundaryBicoloredEdges C a b (faceBoundary f)) S e ≤ 2) :
    Finset.sum S (fun f => literalPolarizedFaceGenerator C a b (faceBoundary f)) =
      indicatorChain (a + b)
        (cutParitySupport (fun f => boundaryBicoloredEdges C a b (faceBoundary f)) S) := by
  calc
    Finset.sum S (fun f => literalPolarizedFaceGenerator C a b (faceBoundary f))
        = Finset.sum S (fun f => polarizedFaceGenerator C a b (faceBoundary f)) := by
            refine Finset.sum_congr rfl ?_
            intro f hf
            exact literalPolarizedFaceGenerator_eq_polarizedFaceGenerator C a b (faceBoundary f)
    _ = indicatorChain (a + b)
          (cutParitySupport (fun f => boundaryBicoloredEdges C a b (faceBoundary f)) S) :=
        sum_polarizedFaceGenerators_eq_indicatorChain_cutParitySupport C a b faceBoundary S hinc

end Mettapedia.GraphTheory.FourColor
