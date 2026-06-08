import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mettapedia.GraphTheory.FourColor.GoertzelDefinition48

open scoped BigOperators
open SimpleGraph

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- The `(a,b)`-Kempe component determined by a boundary edge colored `a` or `b`. -/
noncomputable def boundaryKempeComponentOf {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (a b : Color) {faceBoundary : Finset G.edgeSet}
    {e : G.edgeSet} (he : e ∈ boundaryBicoloredEdges C a b faceBoundary) :
    (C.bicoloredSubgraph a b).ConnectedComponent :=
  (C.bicoloredSubgraph a b).connectedComponentMk
    ⟨e, ((mem_boundaryBicoloredEdges_iff C a b).1 he).2⟩

/-- The finite set of distinct `(a,b)`-Kempe components meeting the chosen face boundary. -/
noncomputable def boundaryKempeComponents {G : SimpleGraph V} (C : G.EdgeColoring Color)
    (a b : Color) (faceBoundary : Finset G.edgeSet) :
    Finset (C.bicoloredSubgraph a b).ConnectedComponent := by
  classical
  exact (boundaryBicoloredEdges C a b faceBoundary).attach.image fun e =>
    boundaryKempeComponentOf C a b e.2

/-- The literal Definition 4.8 slice attached to one boundary-hitting Kempe component. -/
noncomputable def componentBoundarySlice {G : SimpleGraph V} (C : G.EdgeColoring Color)
    (a b : Color) (faceBoundary : Finset G.edgeSet)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent) : G.edgeSet → Color := by
  classical
  exact indicatorChain (a + b) (faceBoundary.filter fun e => e ∈ C.kempeComponentSet a b K)

/-- A finite realization of the component-sum formula in Goertzel v23 Definition 4.8. -/
noncomputable def literalPolarizedFaceGenerator {G : SimpleGraph V} (C : G.EdgeColoring Color)
    (a b : Color) (faceBoundary : Finset G.edgeSet) : G.edgeSet → Color :=
  fun e =>
    Finset.sum (boundaryKempeComponents C a b faceBoundary)
      (fun K => componentBoundarySlice C a b faceBoundary K e)

omit [DecidableEq V] in
theorem boundaryKempeComponentOf_mem_boundaryKempeComponents {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (a b : Color) {faceBoundary : Finset G.edgeSet} {e : G.edgeSet}
    (he : e ∈ boundaryBicoloredEdges C a b faceBoundary) :
    boundaryKempeComponentOf C a b he ∈ boundaryKempeComponents C a b faceBoundary := by
  classical
  refine Finset.mem_image.2 ?_
  refine ⟨⟨e, he⟩, by simp, rfl⟩

omit [DecidableEq V] in
theorem mem_kempeComponentSet_boundaryKempeComponentOf {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (a b : Color) {faceBoundary : Finset G.edgeSet} {e : G.edgeSet}
    (he : e ∈ boundaryBicoloredEdges C a b faceBoundary) :
    e ∈ C.kempeComponentSet a b (boundaryKempeComponentOf C a b he) := by
  exact C.mem_kempeComponentSet_self ((mem_boundaryBicoloredEdges_iff C a b).1 he).2

omit [DecidableEq V] in
theorem kempeComponent_eq_of_mem {G : SimpleGraph V} (C : G.EdgeColoring Color) {a b : Color}
    {K L : (C.bicoloredSubgraph a b).ConnectedComponent} {e : G.edgeSet}
    (hK : e ∈ C.kempeComponentSet a b K) (hL : e ∈ C.kempeComponentSet a b L) :
    K = L := by
  rcases hK with ⟨heK, hK⟩
  rcases hL with ⟨heL, hL⟩
  have hsub : (⟨e, heK⟩ : ↥(C.bicoloredSet a b)) = ⟨e, heL⟩ := by
    ext
    rfl
  calc
    K = (C.bicoloredSubgraph a b).connectedComponentMk ⟨e, heK⟩ := by
      simpa using hK.symm
    _ = (C.bicoloredSubgraph a b).connectedComponentMk ⟨e, heL⟩ := by
      exact congrArg (C.bicoloredSubgraph a b).connectedComponentMk hsub
    _ = L := by
      simp [hL]

theorem componentBoundarySlice_eq_third_of_mem {G : SimpleGraph V} (C : G.EdgeColoring Color)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    {K : (C.bicoloredSubgraph a b).ConnectedComponent} {e : G.edgeSet}
    (he : e ∈ faceBoundary) (hK : e ∈ C.kempeComponentSet a b K) :
    componentBoundarySlice C a b faceBoundary K e = a + b := by
  classical
  simp [componentBoundarySlice, indicatorChain, he, hK]

theorem componentBoundarySlice_eq_zero_of_not_mem_component {G : SimpleGraph V}
    (C : G.EdgeColoring Color) {a b : Color} {faceBoundary : Finset G.edgeSet}
    {K : (C.bicoloredSubgraph a b).ConnectedComponent} {e : G.edgeSet}
    (hK : e ∉ C.kempeComponentSet a b K) :
    componentBoundarySlice C a b faceBoundary K e = 0 := by
  classical
  simp [componentBoundarySlice, indicatorChain, hK]

theorem componentBoundarySlice_eq_zero_of_not_mem_boundary {G : SimpleGraph V}
    (C : G.EdgeColoring Color) {a b : Color} {faceBoundary : Finset G.edgeSet}
    {K : (C.bicoloredSubgraph a b).ConnectedComponent} {e : G.edgeSet}
    (he : e ∉ faceBoundary) :
    componentBoundarySlice C a b faceBoundary K e = 0 := by
  classical
  simp [componentBoundarySlice, indicatorChain, he]

theorem componentBoundarySlice_eq_zero_of_not_mem_boundaryBicolored {G : SimpleGraph V}
    (C : G.EdgeColoring Color) {a b : Color} {faceBoundary : Finset G.edgeSet}
    {K : (C.bicoloredSubgraph a b).ConnectedComponent} {e : G.edgeSet}
    (he : e ∉ boundaryBicoloredEdges C a b faceBoundary) :
    componentBoundarySlice C a b faceBoundary K e = 0 := by
  classical
  by_cases hface : e ∈ faceBoundary
  · have hnotColor : ¬ (C e = a ∨ C e = b) := by
      intro hcolor
      exact he ((mem_boundaryBicoloredEdges_iff C a b).2 ⟨hface, hcolor⟩)
    have hnotK : e ∉ C.kempeComponentSet a b K := by
      intro hK
      exact hnotColor (C.mem_bicoloredSet_of_mem_kempeComponentSet hK)
    exact componentBoundarySlice_eq_zero_of_not_mem_component C hnotK
  · exact componentBoundarySlice_eq_zero_of_not_mem_boundary C hface

/-- The literal finite component-sum in Definition 4.8 agrees with the simpler boundary indicator
already formalized in `polarizedFaceGenerator`. -/
theorem literalPolarizedFaceGenerator_eq_polarizedFaceGenerator {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (a b : Color) (faceBoundary : Finset G.edgeSet) :
    literalPolarizedFaceGenerator C a b faceBoundary = polarizedFaceGenerator C a b faceBoundary := by
  classical
  funext e
  by_cases he : e ∈ boundaryBicoloredEdges C a b faceBoundary
  · let K₀ : (C.bicoloredSubgraph a b).ConnectedComponent := boundaryKempeComponentOf C a b he
    have hK₀mem : K₀ ∈ boundaryKempeComponents C a b faceBoundary := by
      exact boundaryKempeComponentOf_mem_boundaryKempeComponents C a b he
    have hK₀self : e ∈ C.kempeComponentSet a b K₀ := by
      exact mem_kempeComponentSet_boundaryKempeComponentOf C a b he
    have hsum :
        Finset.sum (boundaryKempeComponents C a b faceBoundary)
          (fun K => componentBoundarySlice C a b faceBoundary K e) =
          a + b := by
      rw [Finset.sum_eq_single K₀]
      · exact componentBoundarySlice_eq_third_of_mem C
          ((mem_boundaryBicoloredEdges_iff C a b).1 he).1 hK₀self
      · intro K hK hne
        have hnotK : e ∉ C.kempeComponentSet a b K := by
          intro hmem
          exact hne (kempeComponent_eq_of_mem C hmem hK₀self)
        exact componentBoundarySlice_eq_zero_of_not_mem_component C hnotK
      · intro hK₀not
        exact (hK₀not hK₀mem).elim
    calc
      literalPolarizedFaceGenerator C a b faceBoundary e =
          Finset.sum (boundaryKempeComponents C a b faceBoundary)
            (fun K => componentBoundarySlice C a b faceBoundary K e) := by
              simp [literalPolarizedFaceGenerator]
      _ = a + b := hsum
      _ = polarizedFaceGenerator C a b faceBoundary e := by
            symm
            exact polarizedFaceGenerator_eq_third_of_mem C
              ((mem_boundaryBicoloredEdges_iff C a b).1 he).1
              ((mem_boundaryBicoloredEdges_iff C a b).1 he).2
  · have hsum :
        Finset.sum (boundaryKempeComponents C a b faceBoundary)
          (fun K => componentBoundarySlice C a b faceBoundary K e) =
          0 := by
      refine Finset.sum_eq_zero ?_
      intro K hK
      exact componentBoundarySlice_eq_zero_of_not_mem_boundaryBicolored C he
    have hpolarized : polarizedFaceGenerator C a b faceBoundary e = 0 := by
      by_cases hface : e ∈ faceBoundary
      · have hnotColor : ¬ (C e = a ∨ C e = b) := by
          intro hcolor
          exact he ((mem_boundaryBicoloredEdges_iff C a b).2 ⟨hface, hcolor⟩)
        exact polarizedFaceGenerator_eq_zero_of_not_bicolored C hnotColor
      · exact polarizedFaceGenerator_eq_zero_of_not_mem_boundary C hface
    calc
      literalPolarizedFaceGenerator C a b faceBoundary e =
          Finset.sum (boundaryKempeComponents C a b faceBoundary)
            (fun K => componentBoundarySlice C a b faceBoundary K e) := by
              simp [literalPolarizedFaceGenerator]
      _ = 0 := hsum
      _ = polarizedFaceGenerator C a b faceBoundary e := by
            symm
            exact hpolarized

end Mettapedia.GraphTheory.FourColor
