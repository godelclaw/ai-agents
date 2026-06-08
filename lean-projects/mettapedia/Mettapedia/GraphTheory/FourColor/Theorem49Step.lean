import Mettapedia.GraphTheory.FourColor.GoertzelDefinition48
import Mettapedia.GraphTheory.FourColor.Orthogonality

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- Route-facing annihilator hypothesis for the simplified boundary-only generator family from
Definition 4.8: every purified generator belonging to the edge-Kempe closure is orthogonal to
`z`, with the dot product restricted to its own bicolored boundary support. -/
def AnnihilatesKempeClosureGeneratorFamily {G : SimpleGraph V} {F : Type*}
    (faceBoundary : F → Finset G.edgeSet) (C₀ : G.EdgeColoring Color)
    (z : G.edgeSet → Color) : Prop :=
  ∀ C ∈ G.EdgeKempeClosure C₀, ∀ f : F, ∀ a b : Color,
    ValidColorPair a b →
      chainDot (boundaryBicoloredEdges C a b (faceBoundary f)) z
        (polarizedFaceGenerator C a b (faceBoundary f)) = 0

omit [DecidableEq V] in
theorem validColorPair_edgeColor_add_generator {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (e : G.edgeSet) {γ : Color}
    (hcolor : C e ≠ 0) (hγ0 : γ ≠ 0) (hγne : γ ≠ C e) :
    ValidColorPair (C e) (C e + γ) := by
  refine ⟨hcolor, ?_, ?_⟩
  · intro hsum
    have hceq : C e = γ := (add_eq_zero_iff_eq (C e) γ).1 hsum
    exact hγne hceq.symm
  · intro hsame
    exact add_ne_left_of_ne_zero (a := C e) hγ0 hsame.symm

/-- Orthogonality to the whole Definition 4.8 boundary-only generator family supplies the local
face-generator orthogonality hypothesis used by the current Theorem 4.9 peeling step. -/
theorem localOrthogonality_of_annihilatesKempeClosureGeneratorFamily {G : SimpleGraph V}
    {F : Type*} {faceBoundary : F → Finset G.edgeSet} {C₀ C : G.EdgeColoring Color}
    {z : G.edgeSet → Color} (hC : C ∈ G.EdgeKempeClosure C₀)
    (hgen : AnnihilatesKempeClosureGeneratorFamily faceBoundary C₀ z)
    {f : F} {e : G.edgeSet} (hcolor : C e ≠ 0) :
    ∀ γ, γ ≠ 0 → γ ≠ C e →
      chainDot (boundaryBicoloredEdges C (C e) (C e + γ) (faceBoundary f)) z
        (polarizedFaceGenerator C (C e) (C e + γ) (faceBoundary f)) = 0 := by
  intro γ hγ0 hγne
  exact hgen C hC f (C e) (C e + γ)
    (validColorPair_edgeColor_add_generator C e hcolor hγ0 hγne)

/-- For the pair `(d, d + γ)`, the third color used by the polarized face generator is exactly
`γ`. -/
theorem polarizedFaceGenerator_eq_indicatorChain_of_add_pair {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (d γ : Color) (faceBoundary : Finset G.edgeSet) :
    polarizedFaceGenerator C d (d + γ) faceBoundary =
      indicatorChain γ (boundaryBicoloredEdges C d (d + γ) faceBoundary) := by
  funext e
  by_cases he : e ∈ boundaryBicoloredEdges C d (d + γ) faceBoundary
  · have hthird : d + (d + γ) = γ := by
      calc
        d + (d + γ) = (d + d) + γ := by ac_rfl
        _ = γ := by simp
    simp [polarizedFaceGenerator, indicatorChain, he, hthird]
  · simp [polarizedFaceGenerator, indicatorChain, he]

/-- Route-facing local elimination step for Theorem 4.9. Fix a face boundary and an edge `e` on
that boundary whose base coloring is `d`. If, for every nonzero generator color `γ ≠ d`, the
corresponding purified generator support `boundaryBicoloredEdges C d (d + γ) faceBoundary`
contains no other nonzero contribution of `z`, and `z` is orthogonal to the associated indicator
chain, then `z` vanishes at `e`. -/
theorem edge_eq_zero_of_boundaryBicolored_annihilation {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (z : G.edgeSet → Color)
    {faceBoundary : Finset G.edgeSet} {e : G.edgeSet} {d : Color}
    (hd : d ≠ 0) (heFace : e ∈ faceBoundary) (hcolor : C e = d)
    (hzero : ∀ γ, γ ≠ 0 → γ ≠ d →
      ∀ e' ∈ (boundaryBicoloredEdges C d (d + γ) faceBoundary).erase e, z e' = 0)
    (horth : ∀ γ, γ ≠ 0 → γ ≠ d →
      chainDot (boundaryBicoloredEdges C d (d + γ) faceBoundary) z
        (indicatorChain γ (boundaryBicoloredEdges C d (d + γ) faceBoundary)) = 0) :
    z e = 0 := by
  apply edge_eq_zero_of_annihilates_other_nonzero_colors
    (support := fun γ => boundaryBicoloredEdges C d (d + γ) faceBoundary) (z := z) (d := d)
  · exact hd
  · intro γ hγ0 hγd
    exact (mem_boundaryBicoloredEdges_iff C d (d + γ)).2 ⟨heFace, Or.inl hcolor⟩
  · exact hzero
  · exact horth

/-- The same local elimination step, but stated using the more geometric hypothesis that every
other edge on the face boundary already has zero `z`-value. This is the form used directly in the
leaf-face peeling step of Theorem 4.9. -/
theorem edge_eq_zero_of_boundaryBicolored_annihilation_of_zero_off_edge {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (z : G.edgeSet → Color)
    {faceBoundary : Finset G.edgeSet} {e : G.edgeSet} {d : Color}
    (hd : d ≠ 0) (heFace : e ∈ faceBoundary) (hcolor : C e = d)
    (hzeroFace : ∀ e' ∈ faceBoundary.erase e, z e' = 0)
    (horth : ∀ γ, γ ≠ 0 → γ ≠ d →
      chainDot (boundaryBicoloredEdges C d (d + γ) faceBoundary) z
        (indicatorChain γ (boundaryBicoloredEdges C d (d + γ) faceBoundary)) = 0) :
    z e = 0 := by
  apply edge_eq_zero_of_boundaryBicolored_annihilation C z hd heFace hcolor
  · intro γ hγ0 hγd e' he'
    have he'ne : e' ≠ e := (Finset.mem_erase.1 he').1
    have hsupp : e' ∈ boundaryBicoloredEdges C d (d + γ) faceBoundary :=
      (Finset.mem_erase.1 he').2
    have hface : e' ∈ faceBoundary := (mem_boundaryBicoloredEdges_iff C d (d + γ)).1 hsupp |>.1
    exact hzeroFace e' (Finset.mem_erase.2 ⟨he'ne, hface⟩)
  · exact horth

/-- Edge-colored form of the same leaf-face elimination step: the distinguished color is taken to
be the actual edge color `C e`, so no extra color witness is required. -/
theorem edge_eq_zero_of_boundaryBicolored_annihilation_at_edge_color {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (z : G.edgeSet → Color)
    {faceBoundary : Finset G.edgeSet} {e : G.edgeSet}
    (hcolor : C e ≠ 0) (heFace : e ∈ faceBoundary)
    (hzeroFace : ∀ e' ∈ faceBoundary.erase e, z e' = 0)
    (horth : ∀ γ, γ ≠ 0 → γ ≠ C e →
      chainDot (boundaryBicoloredEdges C (C e) (C e + γ) faceBoundary) z
        (indicatorChain γ (boundaryBicoloredEdges C (C e) (C e + γ) faceBoundary)) = 0) :
    z e = 0 := by
  exact edge_eq_zero_of_boundaryBicolored_annihilation_of_zero_off_edge
    (C := C) (z := z) (d := C e) hcolor heFace rfl hzeroFace horth

/-- The same edge-colored local elimination step, now stated directly with orthogonality to the
actual polarized face generators from Definition 4.8. -/
theorem edge_eq_zero_of_polarizedFaceGenerator_annihilation_at_edge_color {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (z : G.edgeSet → Color)
    {faceBoundary : Finset G.edgeSet} {e : G.edgeSet}
    (hcolor : C e ≠ 0) (heFace : e ∈ faceBoundary)
    (hzeroFace : ∀ e' ∈ faceBoundary.erase e, z e' = 0)
    (horth : ∀ γ, γ ≠ 0 → γ ≠ C e →
      chainDot (boundaryBicoloredEdges C (C e) (C e + γ) faceBoundary) z
        (polarizedFaceGenerator C (C e) (C e + γ) faceBoundary) = 0) :
    z e = 0 := by
  apply edge_eq_zero_of_boundaryBicolored_annihilation_at_edge_color C z hcolor heFace hzeroFace
  intro γ hγ0 hγd
  simpa [polarizedFaceGenerator_eq_indicatorChain_of_add_pair C (C e) γ faceBoundary] using
    horth γ hγ0 hγd

/-- Cleared-set form of the local Theorem 4.9 step: if every other boundary edge of `f` lies in a
known-zero edge set, then orthogonality to the corresponding polarized face generators forces the
remaining edge to vanish. This is the form suited to iterative peeling arguments. -/
theorem edge_eq_zero_of_polarizedFaceGenerator_annihilation_of_subset_zero {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (z : G.edgeSet → Color)
    {faceBoundary cleared : Finset G.edgeSet} {e : G.edgeSet}
    (hcolor : C e ≠ 0) (heFace : e ∈ faceBoundary)
    (hsubset : faceBoundary.erase e ⊆ cleared)
    (hzeroCleared : ∀ e' ∈ cleared, z e' = 0)
    (horth : ∀ γ, γ ≠ 0 → γ ≠ C e →
      chainDot (boundaryBicoloredEdges C (C e) (C e + γ) faceBoundary) z
        (polarizedFaceGenerator C (C e) (C e + γ) faceBoundary) = 0) :
    z e = 0 := by
  apply edge_eq_zero_of_polarizedFaceGenerator_annihilation_at_edge_color C z hcolor heFace
  · intro e' he'
    exact hzeroCleared e' (hsubset he')
  · exact horth

end Mettapedia.GraphTheory.FourColor
