import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mettapedia.GraphTheory.Kempe

namespace SimpleGraph

variable {V α : Type*}

/-- An edge coloring of `G` is a vertex coloring of the line graph of `G`. -/
abbrev EdgeColoring (G : SimpleGraph V) (α : Type*) := G.lineGraph.Coloring α

/-- `G` is edge-colorable with `n` colors if its line graph is vertex-colorable with `n` colors. -/
abbrev EdgeColorable (G : SimpleGraph V) (n : ℕ) : Prop := G.lineGraph.Colorable n

variable (G : SimpleGraph V) [DecidableEq α]

/-- One edge-Kempe move is one Kempe move in the line graph. -/
abbrev EdgeKempeStep : G.EdgeColoring α → G.EdgeColoring α → Prop :=
  G.lineGraph.KempeStep

/-- The edge-Kempe closure is the Kempe closure in the line graph. -/
abbrev EdgeKempeClosure (C₀ : G.EdgeColoring α) : Set (G.EdgeColoring α) :=
  G.lineGraph.KempeClosure C₀

variable {G}

theorem edgeKempeStep_swapOnKempeComponent (C : G.EdgeColoring α) (a b : α)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent) :
    G.EdgeKempeStep C (C.swapOnKempeComponent a b K) :=
  G.lineGraph.kempeStep_swapOnKempeComponent C a b K

theorem mem_edgeKempeClosure_self (C₀ : G.EdgeColoring α) :
    C₀ ∈ G.EdgeKempeClosure C₀ :=
  G.lineGraph.mem_kempeClosure_self C₀

theorem mem_edgeKempeClosure_of_step {C₀ C C' : G.EdgeColoring α}
    (hC : C ∈ G.EdgeKempeClosure C₀) (hstep : G.EdgeKempeStep C C') :
    C' ∈ G.EdgeKempeClosure C₀ :=
  G.lineGraph.mem_kempeClosure_of_step hC hstep

theorem mem_edgeKempeClosure_of_mem_of_step {C₀ C : G.EdgeColoring α}
    (hC : C ∈ G.EdgeKempeClosure C₀) (a b : α)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent) :
    C.swapOnKempeComponent a b K ∈ G.EdgeKempeClosure C₀ :=
  G.mem_edgeKempeClosure_of_step hC (G.edgeKempeStep_swapOnKempeComponent C a b K)

end SimpleGraph
