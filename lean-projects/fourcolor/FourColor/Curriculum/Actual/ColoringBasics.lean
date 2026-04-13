import Mathlib.Combinatorics.SimpleGraph.Basic

namespace FourColor.Curriculum.Actual

variable {α : Type*}

/-- A vertex coloring of `G` with color type `κ`. -/
abbrev Coloring (κ : Type*) := α → κ

/-- A coloring is proper when adjacent vertices get distinct colors. -/
def IsProperColoring (G : SimpleGraph α) {κ : Type*} (c : Coloring (α := α) κ) : Prop :=
  ∀ ⦃u v : α⦄, G.Adj u v → c u ≠ c v

/-- Properness is preserved when restricting from a graph to a subgraph. -/
theorem isProperColoring_of_le {G H : SimpleGraph α} (hHG : H ≤ G) {κ : Type*}
    {c : Coloring (α := α) κ} (hproper : IsProperColoring G c) :
    IsProperColoring H c := by
  intro u v huv
  exact hproper (hHG huv)

/-- The same properness result in flipped argument order for rewriting convenience. -/
theorem isProperColoring_mono {G H : SimpleGraph α} {κ : Type*} {c : Coloring (α := α) κ}
    (hproper : IsProperColoring G c) (hHG : H ≤ G) :
    IsProperColoring H c :=
  isProperColoring_of_le hHG hproper

end FourColor.Curriculum.Actual
