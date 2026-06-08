import Mettapedia.GraphTheory.Coloring

namespace Mettapedia.GraphTheory.ColoringRegression

open SimpleGraph

def K2 : SimpleGraph (Fin 2) := ⊤

def twoColoring : K2.Coloring (Fin 2) :=
  SimpleGraph.selfColoring K2

def twoComponent : (twoColoring.bicoloredSubgraph 0 1).ConnectedComponent :=
  (twoColoring.bicoloredSubgraph 0 1).connectedComponentMk
    ⟨0, by
      change ((0 : Fin 2) = 0 ∨ (0 : Fin 2) = 1)
      simp⟩

example : twoColoring.swapOnKempeComponent 0 1 twoComponent 0 = 1 := by
  have hmem : (0 : Fin 2) ∈ twoColoring.kempeComponentSet 0 1 twoComponent := by
    simpa [twoComponent] using
      (twoColoring.mem_kempeComponentSet_self
        (a := 0) (b := 1) (v := 0)
        (by
          change ((0 : Fin 2) = 0 ∨ (0 : Fin 2) = 1)
          simp :
          (0 : Fin 2) ∈ twoColoring.bicoloredSet 0 1))
  simpa [twoColoring] using
    (twoColoring.swapOnKempeComponent_apply_of_mem
      (a := 0) (b := 1) (K := twoComponent) hmem)

def K3 : SimpleGraph (Fin 3) := ⊤

def threeColoring : K3.Coloring (Fin 3) :=
  SimpleGraph.selfColoring K3

def threeComponent : (threeColoring.bicoloredSubgraph 0 1).ConnectedComponent :=
  (threeColoring.bicoloredSubgraph 0 1).connectedComponentMk
    ⟨0, by
      change ((0 : Fin 3) = 0 ∨ (0 : Fin 3) = 1)
      simp⟩

example : threeColoring.swapOnKempeComponent 0 1 threeComponent 2 = 2 := by
  have hnot : (2 : Fin 3) ∉ threeColoring.kempeComponentSet 0 1 threeComponent := by
    intro h
    have hpair :=
      threeColoring.mem_bicoloredSet_of_mem_kempeComponentSet (a := 0) (b := 1) h
    change ((2 : Fin 3) = 0 ∨ (2 : Fin 3) = 1) at hpair
    simp at hpair
  simpa [threeColoring] using
    (threeColoring.swapOnKempeComponent_apply_of_not_mem
      (a := 0) (b := 1) (K := threeComponent) hnot)

end Mettapedia.GraphTheory.ColoringRegression
