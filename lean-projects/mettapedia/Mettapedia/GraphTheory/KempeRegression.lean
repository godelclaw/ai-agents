import Mettapedia.GraphTheory.Kempe

namespace Mettapedia.GraphTheory.KempeRegression

open SimpleGraph

def K2 : SimpleGraph (Fin 2) := ⊤

def twoColoring : K2.Coloring (Fin 2) :=
  SimpleGraph.selfColoring K2

def twoComponent : (twoColoring.bicoloredSubgraph 0 1).ConnectedComponent :=
  (twoColoring.bicoloredSubgraph 0 1).connectedComponentMk
    ⟨0, by
      change ((0 : Fin 2) = 0 ∨ (0 : Fin 2) = 1)
      simp⟩

example : K2.KempeStep twoColoring (twoColoring.swapOnKempeComponent 0 1 twoComponent) :=
  K2.kempeStep_swapOnKempeComponent twoColoring 0 1 twoComponent

example : twoColoring ∈ K2.KempeClosure twoColoring :=
  K2.mem_kempeClosure_self twoColoring

example : twoColoring.swapOnKempeComponent 0 1 twoComponent ∈ K2.KempeClosure twoColoring :=
  K2.mem_kempeClosure_of_mem_of_step (K2.mem_kempeClosure_self twoColoring) 0 1 twoComponent

example :
    (twoColoring.swapOnKempeComponent 0 1 twoComponent).bicoloredSet 0 1 =
      twoColoring.bicoloredSet 0 1 :=
  twoColoring.bicoloredSet_swapOnKempeComponent 0 1 twoComponent

end Mettapedia.GraphTheory.KempeRegression
