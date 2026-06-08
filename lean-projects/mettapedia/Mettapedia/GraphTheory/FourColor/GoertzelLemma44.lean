import Mettapedia.GraphTheory.FourColor.GoertzelDefinition48Literal

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

variable {V : Type*} [DecidableEq V]

/-- The exact polarized face generator used in v23 Step 1: it marks only the `a`-colored half of
the selected boundary edges, with coefficient `a + b`.  This is stricter than the existing
boundary-only `polarizedFaceGenerator`, which corresponds to the purified Step 3 output. -/
def v23PolarizedFaceGenerator {G : SimpleGraph V} (C : G.EdgeColoring Color)
    (a b : Color) (faceBoundary : Finset G.edgeSet) : G.edgeSet → Color :=
  indicatorChain (a + b) (faceBoundary.filter fun e => C e = a)

theorem v23PolarizedFaceGenerator_eq_third_of_mem_boundary_of_eq_left {G : SimpleGraph V}
    (C : G.EdgeColoring Color) {a b : Color} {faceBoundary : Finset G.edgeSet} {e : G.edgeSet}
    (he : e ∈ faceBoundary) (hcolor : C e = a) :
    v23PolarizedFaceGenerator C a b faceBoundary e = a + b := by
  simp [v23PolarizedFaceGenerator, indicatorChain, he, hcolor]

theorem v23PolarizedFaceGenerator_eq_zero_of_not_mem_boundary {G : SimpleGraph V}
    (C : G.EdgeColoring Color) {a b : Color} {faceBoundary : Finset G.edgeSet} {e : G.edgeSet}
    (he : e ∉ faceBoundary) :
    v23PolarizedFaceGenerator C a b faceBoundary e = 0 := by
  simp [v23PolarizedFaceGenerator, indicatorChain, he]

theorem v23PolarizedFaceGenerator_eq_zero_of_ne_left {G : SimpleGraph V}
    (C : G.EdgeColoring Color) {a b : Color} {faceBoundary : Finset G.edgeSet} {e : G.edgeSet}
    (hcolor : C e ≠ a) :
    v23PolarizedFaceGenerator C a b faceBoundary e = 0 := by
  by_cases he : e ∈ faceBoundary
  · simp [v23PolarizedFaceGenerator, indicatorChain, he, hcolor]
  · exact v23PolarizedFaceGenerator_eq_zero_of_not_mem_boundary C he

/-- Exact formalization of v23 Step 2 for one boundary-hitting `(a,b)` Kempe component:
the XOR of the pre-switch and post-switch polarized generators is exactly the unpolarized
component boundary slice `c · 1_{D ∩ ∂f}`. -/
theorem v23_single_component_purification {G : SimpleGraph V} (C : G.EdgeColoring Color)
    (a b : Color) (faceBoundary : Finset G.edgeSet)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent) :
    v23PolarizedFaceGenerator C a b faceBoundary +
        v23PolarizedFaceGenerator (C.swapOnKempeComponent a b K) a b faceBoundary =
      componentBoundarySlice C a b faceBoundary K := by
  by_cases hab : a = b
  · subst hab
    funext e
    simp [v23PolarizedFaceGenerator, componentBoundarySlice, indicatorChain]
  · funext e
    by_cases hface : e ∈ faceBoundary
    · by_cases hK : e ∈ C.kempeComponentSet a b K
      · rcases C.mem_bicoloredSet_of_mem_kempeComponentSet hK with hca | hcb
        · have hfirst :
              v23PolarizedFaceGenerator C a b faceBoundary e = a + b := by
              exact v23PolarizedFaceGenerator_eq_third_of_mem_boundary_of_eq_left C hface hca
          have hswap : C.swapOnKempeComponent a b K e = b := by
            rw [C.swapOnKempeComponent_apply_of_mem hK, hca]
            simp
          have hsecond :
              v23PolarizedFaceGenerator (C.swapOnKempeComponent a b K) a b faceBoundary e = 0 := by
            apply v23PolarizedFaceGenerator_eq_zero_of_ne_left
            rw [hswap]
            intro hba
            exact hab hba.symm
          have hsliced : componentBoundarySlice C a b faceBoundary K e = a + b := by
            exact componentBoundarySlice_eq_third_of_mem C hface hK
          calc
            (v23PolarizedFaceGenerator C a b faceBoundary +
                v23PolarizedFaceGenerator (C.swapOnKempeComponent a b K) a b faceBoundary) e
                = v23PolarizedFaceGenerator C a b faceBoundary e +
                    v23PolarizedFaceGenerator (C.swapOnKempeComponent a b K) a b faceBoundary e := by
                    simp
            _ = (a + b) + 0 := by rw [hfirst, hsecond]
            _ = a + b := by simp
            _ = componentBoundarySlice C a b faceBoundary K e := hsliced.symm
        · have hfirst :
              v23PolarizedFaceGenerator C a b faceBoundary e = 0 := by
              apply v23PolarizedFaceGenerator_eq_zero_of_ne_left
              rw [hcb]
              intro hba
              exact hab hba.symm
          have hswap : C.swapOnKempeComponent a b K e = a := by
            rw [C.swapOnKempeComponent_apply_of_mem hK, hcb]
            simp
          have hsecond :
              v23PolarizedFaceGenerator (C.swapOnKempeComponent a b K) a b faceBoundary e = a + b := by
            exact v23PolarizedFaceGenerator_eq_third_of_mem_boundary_of_eq_left
              (C.swapOnKempeComponent a b K) hface hswap
          have hsliced : componentBoundarySlice C a b faceBoundary K e = a + b := by
            exact componentBoundarySlice_eq_third_of_mem C hface hK
          calc
            (v23PolarizedFaceGenerator C a b faceBoundary +
                v23PolarizedFaceGenerator (C.swapOnKempeComponent a b K) a b faceBoundary) e
                = v23PolarizedFaceGenerator C a b faceBoundary e +
                    v23PolarizedFaceGenerator (C.swapOnKempeComponent a b K) a b faceBoundary e := by
                    simp
            _ = 0 + (a + b) := by rw [hfirst, hsecond]
            _ = a + b := by simp
            _ = componentBoundarySlice C a b faceBoundary K e := hsliced.symm
      · by_cases hca : C e = a
        · simp [v23PolarizedFaceGenerator, componentBoundarySlice, indicatorChain,
            hface, hK, hca]
        · simp [v23PolarizedFaceGenerator, componentBoundarySlice, indicatorChain,
            hface, hK, hca]
    · simp [v23PolarizedFaceGenerator, componentBoundarySlice, indicatorChain, hface]

/-- Summing the exact v23 Step 2 purification equalities over all boundary-hitting Kempe
components recovers the literal boundary-only generator used in the existing finite component-sum
formalization. -/
theorem sum_v23_single_component_purifications_eq_literalPolarizedFaceGenerator
    {G : SimpleGraph V} (C : G.EdgeColoring Color)
    (a b : Color) (faceBoundary : Finset G.edgeSet) :
    Finset.sum (boundaryKempeComponents C a b faceBoundary)
      (fun K : (C.bicoloredSubgraph a b).ConnectedComponent =>
        v23PolarizedFaceGenerator C a b faceBoundary +
          (v23PolarizedFaceGenerator (C.swapOnKempeComponent a b K) a b faceBoundary :
            G.edgeSet → Color)) =
      literalPolarizedFaceGenerator C a b faceBoundary := by
  calc
    Finset.sum (boundaryKempeComponents C a b faceBoundary)
        (fun K : (C.bicoloredSubgraph a b).ConnectedComponent =>
          v23PolarizedFaceGenerator C a b faceBoundary +
            (v23PolarizedFaceGenerator (C.swapOnKempeComponent a b K) a b faceBoundary :
              G.edgeSet → Color))
        =
        Finset.sum (boundaryKempeComponents C a b faceBoundary)
          (fun K => componentBoundarySlice C a b faceBoundary K) := by
            refine Finset.sum_congr rfl ?_
            intro K hK
            exact v23_single_component_purification C a b faceBoundary K
    _ = literalPolarizedFaceGenerator C a b faceBoundary := by
          funext e
          simp [literalPolarizedFaceGenerator]

/-- Consequently, the finite sum of exact v23 Step 2 purification terms matches the simplified
boundary-only generator already used downstream in the theorem-4.9 files. -/
theorem sum_v23_single_component_purifications_eq_boundaryOnlyGenerator
    {G : SimpleGraph V} (C : G.EdgeColoring Color)
    (a b : Color) (faceBoundary : Finset G.edgeSet) :
    Finset.sum (boundaryKempeComponents C a b faceBoundary)
      (fun K : (C.bicoloredSubgraph a b).ConnectedComponent =>
        v23PolarizedFaceGenerator C a b faceBoundary +
          (v23PolarizedFaceGenerator (C.swapOnKempeComponent a b K) a b faceBoundary :
            G.edgeSet → Color)) =
      polarizedFaceGenerator C a b faceBoundary := by
  rw [sum_v23_single_component_purifications_eq_literalPolarizedFaceGenerator]
  exact literalPolarizedFaceGenerator_eq_polarizedFaceGenerator C a b faceBoundary

end Mettapedia.GraphTheory.FourColor
