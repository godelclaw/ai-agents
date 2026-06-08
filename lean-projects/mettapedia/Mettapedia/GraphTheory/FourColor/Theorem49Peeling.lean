import Mettapedia.GraphTheory.FourColor.Theorem49Step

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- Abstract iterative form of the local Theorem 4.9 edge-elimination step. A list `order`
describes a valid peel order relative to an initial cleared set `baseZero` if each edge in the list
admits a face boundary whose remaining edges lie in the already-cleared set `baseZero ∪ prefix`.
Orthogonality to the corresponding polarized face generators then forces vanishing on all edges in
the peel order. -/
theorem zero_on_peelOrder_from {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (baseZero : Finset G.edgeSet) :
    ∀ order : List G.edgeSet,
      (∀ e ∈ baseZero, z e = 0) →
      (∀ l₁ l₂ e, order = l₁ ++ e :: l₂ →
        ∃ faceBoundary : Finset G.edgeSet,
          e ∈ faceBoundary ∧ faceBoundary.erase e ⊆ baseZero ∪ l₁.toFinset) →
      (∀ e faceBoundary, e ∈ order.toFinset → e ∈ faceBoundary →
        ∀ γ, γ ≠ 0 → γ ≠ C e →
          chainDot (boundaryBicoloredEdges C (C e) (C e + γ) faceBoundary) z
            (polarizedFaceGenerator C (C e) (C e + γ) faceBoundary) = 0) →
      ∀ e ∈ order.toFinset, z e = 0
  | [], hzeroBase, _hstep, _horth => by
      intro e he
      simp at he
  | e :: es, hzeroBase, hstep, horth => by
      rcases hstep [] es e rfl with ⟨faceBoundary, heFace, hsubset⟩
      have hzeroe : z e = 0 := by
        apply edge_eq_zero_of_polarizedFaceGenerator_annihilation_of_subset_zero C z
        · exact htait e
        · exact heFace
        · exact hsubset
        · intro e' he'
          exact hzeroBase e' (by simpa using he')
        · intro γ hγ0 hγd
          exact horth e faceBoundary (by simp) heFace γ hγ0 hγd
      have hzeroBase' : ∀ e' ∈ insert e baseZero, z e' = 0 := by
        intro e' he'
        rcases Finset.mem_insert.1 he' with rfl | hmem
        · exact hzeroe
        · exact hzeroBase e' hmem
      have hstep' :
          ∀ l₁ l₂ e', es = l₁ ++ e' :: l₂ →
            ∃ faceBoundary : Finset G.edgeSet,
              e' ∈ faceBoundary ∧ faceBoundary.erase e' ⊆ insert e baseZero ∪ l₁.toFinset := by
        intro l₁ l₂ e' hs
        have hs' : e :: es = (e :: l₁) ++ e' :: l₂ := by
          simp [hs]
        rcases hstep (e :: l₁) l₂ e' hs' with ⟨faceBoundary, heFace', hsubset'⟩
        refine ⟨faceBoundary, heFace', ?_⟩
        intro x hx
        have hx' : x ∈ baseZero ∪ (e :: l₁).toFinset := hsubset' hx
        simpa [List.toFinset_cons, Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using hx'
      have horth' :
          ∀ e' faceBoundary, e' ∈ es.toFinset → e' ∈ faceBoundary →
            ∀ γ, γ ≠ 0 → γ ≠ C e' →
              chainDot (boundaryBicoloredEdges C (C e') (C e' + γ) faceBoundary) z
                (polarizedFaceGenerator C (C e') (C e' + γ) faceBoundary) = 0 := by
        intro e' faceBoundary he' hface γ hγ0 hγd
        exact horth e' faceBoundary (by simp [he']) hface γ hγ0 hγd
      have htail :
          ∀ e' ∈ es.toFinset, z e' = 0 :=
        zero_on_peelOrder_from C htait z (insert e baseZero) es hzeroBase' hstep' horth'
      intro x hx
      rcases (by simpa [List.toFinset_cons, Finset.mem_insert, Finset.mem_union] using hx :
          x = e ∨ x ∈ es.toFinset) with rfl | hxes
      · exact hzeroe
      · exact htail x hxes

end Mettapedia.GraphTheory.FourColor
