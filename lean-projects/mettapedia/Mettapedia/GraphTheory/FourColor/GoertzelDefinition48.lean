import Mettapedia.GraphTheory.EdgeColoring
import Mettapedia.GraphTheory.FourColor.ColorAlgebra

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

variable {V : Type*} [DecidableEq V]

/-- A valid Goertzel/Kauffman color pair consists of two distinct nonzero colors in `𝔽₂²`. -/
def ValidColorPair (a b : Color) : Prop :=
  a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b

/-- An edge coloring using the nonzero `𝔽₂²` colors. This is the Tait-world notion relevant to
Goertzel v23 Definition 4.8. -/
def IsTaitEdgeColoring (G : SimpleGraph V) (C : G.EdgeColoring Color) : Prop :=
  ∀ e, C e ≠ 0

/-- The boundary edges of a face carrying one of the selected colors.
This is the boundary support of the `(a,b)`-Kempe components meeting that face boundary. -/
def boundaryBicoloredEdges {G : SimpleGraph V} (C : G.EdgeColoring Color)
    (a b : Color) (faceBoundary : Finset G.edgeSet) : Finset G.edgeSet :=
  faceBoundary.filter fun e => C e = a ∨ C e = b

omit [DecidableEq V] in
@[simp] theorem mem_boundaryBicoloredEdges_iff {G : SimpleGraph V} (C : G.EdgeColoring Color)
    (a b : Color) {faceBoundary : Finset G.edgeSet} {e : G.edgeSet} :
    e ∈ boundaryBicoloredEdges C a b faceBoundary ↔
      e ∈ faceBoundary ∧ (C e = a ∨ C e = b) := by
  simp [boundaryBicoloredEdges]

/-- The purified boundary-only generator produced after the exact v23 Step 2 cancellation.
It records the full `(a,b)`-boundary support with coefficient `a + b`, rather than only the
`a`-colored half tracked by the exact v23 Step 1 generator. -/
def polarizedFaceGenerator {G : SimpleGraph V} (C : G.EdgeColoring Color)
    (a b : Color) (faceBoundary : Finset G.edgeSet) : G.edgeSet → Color :=
  indicatorChain (a + b) (boundaryBicoloredEdges C a b faceBoundary)

theorem polarizedFaceGenerator_eq_third_of_mem {G : SimpleGraph V} (C : G.EdgeColoring Color)
    {a b : Color} {faceBoundary : Finset G.edgeSet} {e : G.edgeSet}
    (he : e ∈ faceBoundary) (hcolor : C e = a ∨ C e = b) :
    polarizedFaceGenerator C a b faceBoundary e = a + b := by
  apply indicatorChain_apply_of_mem
  exact (mem_boundaryBicoloredEdges_iff C a b).2 ⟨he, hcolor⟩

theorem polarizedFaceGenerator_eq_zero_of_not_mem_boundary {G : SimpleGraph V}
    (C : G.EdgeColoring Color) {a b : Color} {faceBoundary : Finset G.edgeSet} {e : G.edgeSet}
    (he : e ∉ faceBoundary) :
    polarizedFaceGenerator C a b faceBoundary e = 0 := by
  apply indicatorChain_apply_of_not_mem
  intro hmem
  exact he ((mem_boundaryBicoloredEdges_iff C a b).1 hmem).1

theorem polarizedFaceGenerator_eq_zero_of_not_bicolored {G : SimpleGraph V}
    (C : G.EdgeColoring Color) {a b : Color} {faceBoundary : Finset G.edgeSet} {e : G.edgeSet}
    (hcolor : ¬ (C e = a ∨ C e = b)) :
    polarizedFaceGenerator C a b faceBoundary e = 0 := by
  by_cases he : e ∈ faceBoundary
  · apply indicatorChain_apply_of_not_mem
    intro hmem
    exact hcolor ((mem_boundaryBicoloredEdges_iff C a b).1 hmem).2
  · exact polarizedFaceGenerator_eq_zero_of_not_mem_boundary C he

theorem polarizedFaceGenerator_nonzero_weight {G : SimpleGraph V} (C : G.EdgeColoring Color)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (hab : ValidColorPair a b) :
    ∀ e ∈ boundaryBicoloredEdges C a b faceBoundary, polarizedFaceGenerator C a b faceBoundary e ≠ 0 := by
  intro e he
  rw [polarizedFaceGenerator_eq_third_of_mem C ((mem_boundaryBicoloredEdges_iff C a b).1 he).1
    ((mem_boundaryBicoloredEdges_iff C a b).1 he).2]
  exact (third_color_properties hab.1 hab.2.1 hab.2.2).1

/-- The simplified Kempe-closure generator family attached to a base coloring and a face-boundary
map. This packages the usable boundary-vector content of Definition 4.8. -/
def kempeClosureGeneratorFamily {G : SimpleGraph V} {F : Type*}
    (faceBoundary : F → Finset G.edgeSet) (C₀ : G.EdgeColoring Color) :
    Set (G.edgeSet → Color) :=
  {x | ∃ C ∈ G.EdgeKempeClosure C₀, ∃ f : F, ∃ a b : Color,
      ValidColorPair a b ∧ x = polarizedFaceGenerator C a b (faceBoundary f)}

theorem mem_kempeClosureGeneratorFamily_iff {G : SimpleGraph V} {F : Type*}
    (faceBoundary : F → Finset G.edgeSet) (C₀ : G.EdgeColoring Color) (x : G.edgeSet → Color) :
    x ∈ kempeClosureGeneratorFamily faceBoundary C₀ ↔
      ∃ C ∈ G.EdgeKempeClosure C₀, ∃ f : F, ∃ a b : Color,
        ValidColorPair a b ∧ x = polarizedFaceGenerator C a b (faceBoundary f) := by
  rfl

end Mettapedia.GraphTheory.FourColor
