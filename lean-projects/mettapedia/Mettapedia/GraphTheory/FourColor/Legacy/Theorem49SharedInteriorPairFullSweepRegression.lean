import Mettapedia.GraphTheory.FourColor.Legacy.Theorem49SharedInteriorPairEndpointRegression
import Mettapedia.GraphTheory.FourColor.Legacy.Theorem49SharedInteriorPairSecondClosureEndpointRegression
import Mettapedia.GraphTheory.FourColor.Theorem49BoundaryProjectionDetector
import Mettapedia.GraphTheory.FourColor.Theorem49SynthesisClosureInvariance
import Mathlib.Tactic

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open Theorem49PlanarBoundaryAnnulusHonestWitnessRegression
open Theorem49SharedInteriorPairEndpointRegression
open Theorem49SharedInteriorPairSecondClosureEndpointRegression

namespace Theorem49SharedInteriorPairFullSweepRegression

private theorem eq_third_color_of_ne_zero_ne_ne {a b c : Color}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    c = a + b := by
  rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero a ha with rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero b hb with rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero c hc with rfl | rfl | rfl <;>
    simp at hab hac hbc ⊢

private theorem eq_left_or_eq_add_of_ne_right {a b c : Color}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : a ≠ b) (hcb : c ≠ b) :
    c = a ∨ c = a + b := by
  rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero a ha with rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero b hb with rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero c hc with rfl | rfl | rfl <;>
    simp at hab hcb ⊢

private theorem eq_right_of_ne_left_ne_add {a b c : Color}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : a ≠ b) (hca : c ≠ a) (hcab : c ≠ a + b) :
    c = b := by
  rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero a ha with rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero b hb with rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero c hc with rfl | rfl | rfl <;>
    simp at hab hca hcab ⊢

private theorem validColorPair_symm {a b : Color} (hab : ValidColorPair a b) :
    ValidColorPair b a :=
  ⟨hab.2.1, hab.1, hab.2.2.symm⟩

private theorem validColorPair_third_left {a b : Color} (hab : ValidColorPair a b) :
    ValidColorPair (a + b) b := by
  rcases third_color_properties hab.1 hab.2.1 hab.2.2 with ⟨hab0, _, habb⟩
  exact ⟨hab0, hab.2.1, habb⟩

private theorem validColorPair_red_blue : ValidColorPair red blue :=
  ⟨red_ne_zero, blue_ne_zero, red_ne_blue⟩

private theorem validColorPair_blue_red : ValidColorPair blue red :=
  validColorPair_symm validColorPair_red_blue

private theorem validColorPair_purple_blue : ValidColorPair purple blue :=
  validColorPair_third_left validColorPair_red_blue

private theorem validColorPair_blue_purple : ValidColorPair blue purple :=
  validColorPair_symm validColorPair_purple_blue

private theorem validColorPair_purple_red : ValidColorPair purple red :=
  validColorPair_third_left validColorPair_blue_red

private theorem validColorPair_red_purple : ValidColorPair red purple :=
  validColorPair_symm validColorPair_purple_red

private theorem closure_eq_base_of_swap_ab_swap_aThird
    {X : Type*}
    (K : (a b : Color) → ValidColorPair a b → Set X)
    (h_ab : ∀ {a b : Color} (hab : ValidColorPair a b),
      K a b hab = K b a (validColorPair_symm hab))
    (h_aThird : ∀ {a b : Color} (hab : ValidColorPair a b),
      K a b hab = K (a + b) b (validColorPair_third_left hab))
    {a b : Color} (hab : ValidColorPair a b) :
    K a b hab = K red blue validColorPair_red_blue := by
  change K a b hab = K red blue validColorPair_red_blue
  rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero a hab.1 with rfl | rfl | rfl
  · rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero b hab.2.1 with rfl | rfl | rfl
    · exact False.elim (hab.2.2 rfl)
    · rfl
    · calc
        K red purple hab = K blue purple validColorPair_blue_purple := by
          simpa using (h_aThird (a := blue) (b := purple) validColorPair_blue_purple).symm
        _ = K purple blue validColorPair_purple_blue := by
          simpa using (h_ab (a := purple) (b := blue) validColorPair_purple_blue).symm
        _ = K red blue validColorPair_red_blue := by
          simpa using (h_aThird (a := red) (b := blue) validColorPair_red_blue).symm
  · rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero b hab.2.1 with rfl | rfl | rfl
    · simpa using (h_ab (a := red) (b := blue) validColorPair_red_blue).symm
    · exact False.elim (hab.2.2 rfl)
    · calc
        K blue purple hab = K purple blue validColorPair_purple_blue := by
          simpa using (h_ab (a := purple) (b := blue) validColorPair_purple_blue).symm
        _ = K red blue validColorPair_red_blue := by
          simpa using (h_aThird (a := red) (b := blue) validColorPair_red_blue).symm
  · rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero b hab.2.1 with rfl | rfl | rfl
    · calc
        K purple red hab = K blue red validColorPair_blue_red := by
          simpa using (h_aThird (a := blue) (b := red) validColorPair_blue_red).symm
        _ = K red blue validColorPair_red_blue := by
          simpa using (h_ab (a := red) (b := blue) validColorPair_red_blue).symm
    · simpa using (h_aThird (a := red) (b := blue) validColorPair_red_blue).symm
    · exact False.elim (hab.2.2 rfl)

private theorem sip01_adj_sip12 :
    sharedInteriorPairAnnulusGraph.lineGraph.Adj sip01 sip12 := by
  rw [SimpleGraph.lineGraph_adj_iff_exists]
  refine ⟨?_, (1 : Fin 8), ?_, ?_⟩
  · intro h
    have := congrArg Subtype.val h
    simp [sip01, sip12] at this
  · simp [sip01]
  · simp [sip12]

private theorem sip01_adj_sip30 :
    sharedInteriorPairAnnulusGraph.lineGraph.Adj sip01 sip30 := by
  rw [SimpleGraph.lineGraph_adj_iff_exists]
  refine ⟨?_, (0 : Fin 8), ?_, ?_⟩
  · intro h
    have := congrArg Subtype.val h
    simp [sip01, sip30] at this
  · simp [sip01]
  · simp [sip30]

private theorem sip01_adj_sip40 :
    sharedInteriorPairAnnulusGraph.lineGraph.Adj sip01 sip40 := by
  rw [SimpleGraph.lineGraph_adj_iff_exists]
  refine ⟨?_, (0 : Fin 8), ?_, ?_⟩
  · intro h
    have := congrArg Subtype.val h
    simp [sip01, sip40] at this
  · simp [sip01]
  · simp [sip40]

private theorem sip12_adj_sip23 :
    sharedInteriorPairAnnulusGraph.lineGraph.Adj sip12 sip23 := by
  rw [SimpleGraph.lineGraph_adj_iff_exists]
  refine ⟨?_, (2 : Fin 8), ?_, ?_⟩
  · intro h
    have := congrArg Subtype.val h
    simp [sip12, sip23] at this
  · simp [sip12]
  · simp [sip23]

private theorem sip12_adj_sip24 :
    sharedInteriorPairAnnulusGraph.lineGraph.Adj sip12 sip24 := by
  rw [SimpleGraph.lineGraph_adj_iff_exists]
  refine ⟨?_, (2 : Fin 8), ?_, ?_⟩
  · intro h
    have := congrArg Subtype.val h
    simp [sip12, sip24] at this
  · simp [sip12]
  · simp [sip24]

private theorem sip23_adj_sip24 :
    sharedInteriorPairAnnulusGraph.lineGraph.Adj sip23 sip24 := by
  rw [SimpleGraph.lineGraph_adj_iff_exists]
  refine ⟨?_, (2 : Fin 8), ?_, ?_⟩
  · intro h
    have := congrArg Subtype.val h
    simp [sip23, sip24] at this
  · simp [sip23]
  · simp [sip24]

private theorem sip23_adj_sip30 :
    sharedInteriorPairAnnulusGraph.lineGraph.Adj sip23 sip30 := by
  rw [SimpleGraph.lineGraph_adj_iff_exists]
  refine ⟨?_, (3 : Fin 8), ?_, ?_⟩
  · intro h
    have := congrArg Subtype.val h
    simp [sip23, sip30] at this
  · simp [sip23]
  · simp [sip30]

private theorem sip24_adj_sip40 :
    sharedInteriorPairAnnulusGraph.lineGraph.Adj sip24 sip40 := by
  rw [SimpleGraph.lineGraph_adj_iff_exists]
  refine ⟨?_, (4 : Fin 8), ?_, ?_⟩
  · intro h
    have := congrArg Subtype.val h
    simp [sip24, sip40] at this
  · simp [sip24]
  · simp [sip40]

private theorem sip30_adj_sip40 :
    sharedInteriorPairAnnulusGraph.lineGraph.Adj sip30 sip40 := by
  rw [SimpleGraph.lineGraph_adj_iff_exists]
  refine ⟨?_, (0 : Fin 8), ?_, ?_⟩
  · intro h
    have := congrArg Subtype.val h
    simp [sip30, sip40] at this
  · simp [sip30]
  · simp [sip40]

private theorem sip56_adj_sip67 :
    sharedInteriorPairAnnulusGraph.lineGraph.Adj sip56 sip67 := by
  rw [SimpleGraph.lineGraph_adj_iff_exists]
  refine ⟨?_, (6 : Fin 8), ?_, ?_⟩
  · intro h
    have := congrArg Subtype.val h
    simp [sip56, sip67] at this
  · simp [sip56]
  · simp [sip67]

private theorem sip56_adj_sip75 :
    sharedInteriorPairAnnulusGraph.lineGraph.Adj sip56 sip75 := by
  rw [SimpleGraph.lineGraph_adj_iff_exists]
  refine ⟨?_, (5 : Fin 8), ?_, ?_⟩
  · intro h
    have := congrArg Subtype.val h
    simp [sip56, sip75] at this
  · simp [sip56]
  · simp [sip75]

private theorem sip67_adj_sip75 :
    sharedInteriorPairAnnulusGraph.lineGraph.Adj sip67 sip75 := by
  rw [SimpleGraph.lineGraph_adj_iff_exists]
  refine ⟨?_, (7 : Fin 8), ?_, ?_⟩
  · intro h
    have := congrArg Subtype.val h
    simp [sip67, sip75] at this
  · simp [sip67]
  · simp [sip75]

private def sharedEdgeRegion (e : sharedInteriorPairAnnulusGraph.edgeSet) : Bool :=
  if e = sip56 ∨ e = sip67 ∨ e = sip75 then true else false

private theorem sharedEdgeRegion_eq_of_lineGraph_adj
    {e f : sharedInteriorPairAnnulusGraph.edgeSet}
    (hadj : sharedInteriorPairAnnulusGraph.lineGraph.Adj e f) :
    sharedEdgeRegion e = sharedEdgeRegion f := by
  rw [SimpleGraph.lineGraph_adj_iff_exists] at hadj
  rcases hadj with ⟨_, v, he, hf⟩
  fin_cases v
  · rcases sharedInteriorPair_edge_mem_zero he with rfl | rfl | rfl <;>
      rcases sharedInteriorPair_edge_mem_zero hf with rfl | rfl | rfl <;>
      decide
  · rcases sharedInteriorPair_edge_mem_one he with rfl | rfl <;>
      rcases sharedInteriorPair_edge_mem_one hf with rfl | rfl <;>
      decide
  · rcases sharedInteriorPair_edge_mem_two he with rfl | rfl | rfl <;>
      rcases sharedInteriorPair_edge_mem_two hf with rfl | rfl | rfl <;>
      decide
  · rcases sharedInteriorPair_edge_mem_three he with rfl | rfl <;>
      rcases sharedInteriorPair_edge_mem_three hf with rfl | rfl <;>
      decide
  · rcases sharedInteriorPair_edge_mem_four he with rfl | rfl <;>
      rcases sharedInteriorPair_edge_mem_four hf with rfl | rfl <;>
      decide
  · rcases sharedInteriorPair_edge_mem_five he with rfl | rfl <;>
      rcases sharedInteriorPair_edge_mem_five hf with rfl | rfl <;>
      decide
  · rcases sharedInteriorPair_edge_mem_six he with rfl | rfl <;>
      rcases sharedInteriorPair_edge_mem_six hf with rfl | rfl <;>
      decide
  · rcases sharedInteriorPair_edge_mem_seven he with rfl | rfl <;>
      rcases sharedInteriorPair_edge_mem_seven hf with rfl | rfl <;>
      decide

private theorem sharedEdgeRegion_eq_of_bicoloredWalk
    {a b : Color}
    {C : sharedInteriorPairAnnulusGraph.EdgeColoring Color}
    {u v : ↥(C.bicoloredSet a b)}
    (p : (C.bicoloredSubgraph a b).Walk u v) :
    sharedEdgeRegion u.1 = sharedEdgeRegion v.1 := by
  induction p with
  | nil => rfl
  | cons hadj p ih =>
      exact (sharedEdgeRegion_eq_of_lineGraph_adj (by simpa using hadj)).trans ih

private theorem sharedEdgeRegion_eq_of_bicoloredReachable
    {a b : Color}
    {C : sharedInteriorPairAnnulusGraph.EdgeColoring Color}
    {e f : sharedInteriorPairAnnulusGraph.edgeSet}
    {he : e ∈ C.bicoloredSet a b} {hf : f ∈ C.bicoloredSet a b}
    (hreach : (C.bicoloredSubgraph a b).Reachable ⟨e, he⟩ ⟨f, hf⟩) :
    sharedEdgeRegion e = sharedEdgeRegion f := by
  refine hreach.elim ?_
  intro p
  exact sharedEdgeRegion_eq_of_bicoloredWalk p

private theorem sharedEdgeRegion_eq_false_of_mem_component_containing_sip01
    {x y : Color}
    {C : sharedInteriorPairAnnulusGraph.EdgeColoring Color}
    {K : (C.bicoloredSubgraph x y).ConnectedComponent}
    {e : sharedInteriorPairAnnulusGraph.edgeSet}
    (h01 : sip01 ∈ C.kempeComponentSet x y K)
    (he : e ∈ C.kempeComponentSet x y K) :
    sharedEdgeRegion e = false := by
  rcases he with ⟨he', hec⟩
  rcases h01 with ⟨h01', h01c⟩
  have hcomp' :
      (C.bicoloredSubgraph x y).connectedComponentMk ⟨e, he'⟩ =
      (C.bicoloredSubgraph x y).connectedComponentMk ⟨sip01, h01'⟩ :=
    hec.trans h01c.symm
  have hreach : (C.bicoloredSubgraph x y).Reachable ⟨e, he'⟩ ⟨sip01, h01'⟩ :=
    ConnectedComponent.eq.mp hcomp'
  have hregion := sharedEdgeRegion_eq_of_bicoloredReachable hreach
  exact hregion.trans (by decide)

private theorem sharedEdgeRegion_eq_true_of_mem_component_containing_sip56
    {x y : Color}
    {C : sharedInteriorPairAnnulusGraph.EdgeColoring Color}
    {K : (C.bicoloredSubgraph x y).ConnectedComponent}
    {e : sharedInteriorPairAnnulusGraph.edgeSet}
    (h56 : sip56 ∈ C.kempeComponentSet x y K)
    (he : e ∈ C.kempeComponentSet x y K) :
    sharedEdgeRegion e = true := by
  rcases he with ⟨he', hec⟩
  rcases h56 with ⟨h56', h56c⟩
  have hcomp' :
      (C.bicoloredSubgraph x y).connectedComponentMk ⟨e, he'⟩ =
      (C.bicoloredSubgraph x y).connectedComponentMk ⟨sip56, h56'⟩ :=
    hec.trans h56c.symm
  have hreach : (C.bicoloredSubgraph x y).Reachable ⟨e, he'⟩ ⟨sip56, h56'⟩ :=
    ConnectedComponent.eq.mp hcomp'
  have hregion := sharedEdgeRegion_eq_of_bicoloredReachable hreach
  exact hregion.trans (by decide)

private def sharedInteriorPairFirstClassParametricEdgeColor
    (a b u v : Color) (e : sharedInteriorPairAnnulusGraph.edgeSet) : Color :=
  if e = sip01 ∨ e = sip24 then a
  else if e = sip12 ∨ e = sip30 then b
  else if e = sip23 ∨ e = sip40 then a + b
  else if e = sip56 then u
  else if e = sip67 then v
  else u + v

@[simp] private theorem sharedInteriorPairFirstClassParametricEdgeColor_sip01
    (a b u v : Color) :
    sharedInteriorPairFirstClassParametricEdgeColor a b u v sip01 = a := by
  simp [sharedInteriorPairFirstClassParametricEdgeColor]

@[simp] private theorem sharedInteriorPairFirstClassParametricEdgeColor_sip12
    (a b u v : Color) :
    sharedInteriorPairFirstClassParametricEdgeColor a b u v sip12 = b := by
  simp [sharedInteriorPairFirstClassParametricEdgeColor, sharedInteriorPairAnnulusGraph,
    sip01, sip12, sip23, sip24, sip30, sip40, sip56, sip67]

@[simp] private theorem sharedInteriorPairFirstClassParametricEdgeColor_sip23
    (a b u v : Color) :
    sharedInteriorPairFirstClassParametricEdgeColor a b u v sip23 = a + b := by
  simp [sharedInteriorPairFirstClassParametricEdgeColor, sharedInteriorPairAnnulusGraph,
    sip01, sip12, sip23, sip24, sip30, sip40, sip56, sip67]

@[simp] private theorem sharedInteriorPairFirstClassParametricEdgeColor_sip30
    (a b u v : Color) :
    sharedInteriorPairFirstClassParametricEdgeColor a b u v sip30 = b := by
  simp [sharedInteriorPairFirstClassParametricEdgeColor, sharedInteriorPairAnnulusGraph,
    sip01, sip12, sip23, sip24, sip30, sip40, sip56, sip67]

@[simp] private theorem sharedInteriorPairFirstClassParametricEdgeColor_sip24
    (a b u v : Color) :
    sharedInteriorPairFirstClassParametricEdgeColor a b u v sip24 = a := by
  simp [sharedInteriorPairFirstClassParametricEdgeColor, sharedInteriorPairAnnulusGraph,
    sip01, sip24]

@[simp] private theorem sharedInteriorPairFirstClassParametricEdgeColor_sip40
    (a b u v : Color) :
    sharedInteriorPairFirstClassParametricEdgeColor a b u v sip40 = a + b := by
  simp [sharedInteriorPairFirstClassParametricEdgeColor, sharedInteriorPairAnnulusGraph,
    sip01, sip12, sip23, sip24, sip30, sip40, sip56, sip67]

@[simp] private theorem sharedInteriorPairFirstClassParametricEdgeColor_sip56
    (a b u v : Color) :
    sharedInteriorPairFirstClassParametricEdgeColor a b u v sip56 = u := by
  simp [sharedInteriorPairFirstClassParametricEdgeColor, sharedInteriorPairAnnulusGraph,
    sip01, sip12, sip23, sip24, sip30, sip40, sip56]

@[simp] private theorem sharedInteriorPairFirstClassParametricEdgeColor_sip67
    (a b u v : Color) :
    sharedInteriorPairFirstClassParametricEdgeColor a b u v sip67 = v := by
  simp [sharedInteriorPairFirstClassParametricEdgeColor, sharedInteriorPairAnnulusGraph,
    sip01, sip12, sip23, sip24, sip30, sip40, sip56, sip67]

@[simp] private theorem sharedInteriorPairFirstClassParametricEdgeColor_sip75
    (a b u v : Color) :
    sharedInteriorPairFirstClassParametricEdgeColor a b u v sip75 = u + v := by
  simp [sharedInteriorPairFirstClassParametricEdgeColor, sharedInteriorPairAnnulusGraph,
    sip01, sip12, sip23, sip24, sip30, sip40, sip56, sip67, sip75]

private theorem sharedInteriorPairFirstClassParametricEdgeColor_ne_of_adj
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v)
    {e f : sharedInteriorPairAnnulusGraph.edgeSet}
    (hadj : sharedInteriorPairAnnulusGraph.lineGraph.Adj e f) :
    sharedInteriorPairFirstClassParametricEdgeColor a b u v e ≠
      sharedInteriorPairFirstClassParametricEdgeColor a b u v f := by
  rcases third_color_properties hab.1 hab.2.1 hab.2.2 with ⟨hab0, haba, habb⟩
  rcases third_color_properties huv.1 huv.2.1 huv.2.2 with ⟨huv0, huva, huvb⟩
  intro hcolor
  rw [SimpleGraph.lineGraph_adj_iff_exists] at hadj
  rcases hadj with ⟨hne, vtx, he, hf⟩
  fin_cases vtx
  · rcases sharedInteriorPair_edge_mem_zero he with rfl | rfl | rfl <;>
      rcases sharedInteriorPair_edge_mem_zero hf with rfl | rfl | rfl <;>
      first
      | simpa [sharedInteriorPairAnnulusGraph, sip01, sip30, sip40] using hne
      | exact hab.2.2 (by simpa using hcolor)
      | exact hab.2.2 (by simpa using hcolor.symm)
      | exact haba (by simpa using hcolor)
      | exact haba (by simpa using hcolor.symm)
      | exact habb (by simpa using hcolor)
      | exact habb (by simpa using hcolor.symm)
  · rcases sharedInteriorPair_edge_mem_one he with rfl | rfl <;>
      rcases sharedInteriorPair_edge_mem_one hf with rfl | rfl <;>
      first
      | simpa [sharedInteriorPairAnnulusGraph, sip01, sip12] using hne
      | exact hab.2.2 (by simpa using hcolor)
      | exact hab.2.2 (by simpa using hcolor.symm)
  · rcases sharedInteriorPair_edge_mem_two he with rfl | rfl | rfl <;>
      rcases sharedInteriorPair_edge_mem_two hf with rfl | rfl | rfl <;>
      first
      | simpa [sharedInteriorPairAnnulusGraph, sip12, sip23, sip24] using hne
      | exact hab.2.2 (by simpa using hcolor)
      | exact hab.2.2 (by simpa using hcolor.symm)
      | exact habb (by simpa using hcolor)
      | exact habb (by simpa using hcolor.symm)
      | exact haba (by simpa using hcolor)
      | exact haba (by simpa using hcolor.symm)
  · rcases sharedInteriorPair_edge_mem_three he with rfl | rfl <;>
      rcases sharedInteriorPair_edge_mem_three hf with rfl | rfl <;>
      first
      | simpa [sharedInteriorPairAnnulusGraph, sip23, sip30] using hne
      | exact habb (by simpa using hcolor)
      | exact habb (by simpa using hcolor.symm)
  · rcases sharedInteriorPair_edge_mem_four he with rfl | rfl <;>
      rcases sharedInteriorPair_edge_mem_four hf with rfl | rfl <;>
      first
      | simpa [sharedInteriorPairAnnulusGraph, sip24, sip40] using hne
      | exact haba (by simpa using hcolor)
      | exact haba (by simpa using hcolor.symm)
  · rcases sharedInteriorPair_edge_mem_five he with rfl | rfl <;>
      rcases sharedInteriorPair_edge_mem_five hf with rfl | rfl <;>
      first
      | simpa [sharedInteriorPairAnnulusGraph, sip56, sip75] using hne
      | exact huva (by simpa using hcolor)
      | exact huva (by simpa using hcolor.symm)
  · rcases sharedInteriorPair_edge_mem_six he with rfl | rfl <;>
      rcases sharedInteriorPair_edge_mem_six hf with rfl | rfl <;>
      first
      | simpa [sharedInteriorPairAnnulusGraph, sip56, sip67] using hne
      | exact huv.2.2 (by simpa using hcolor)
      | exact huv.2.2 (by simpa using hcolor.symm)
  · rcases sharedInteriorPair_edge_mem_seven he with rfl | rfl <;>
      rcases sharedInteriorPair_edge_mem_seven hf with rfl | rfl <;>
      first
      | simpa [sharedInteriorPairAnnulusGraph, sip67, sip75] using hne
      | exact huvb (by simpa using hcolor)
      | exact huvb (by simpa using hcolor.symm)

private def sharedInteriorPairFirstClassParametricTaitEdgeColoring
    (a b u v : Color) (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sharedInteriorPairAnnulusGraph.EdgeColoring Color :=
  Coloring.mk (sharedInteriorPairFirstClassParametricEdgeColor a b u v) (by
    intro e f hadj
    exact sharedInteriorPairFirstClassParametricEdgeColor_ne_of_adj hab huv hadj)

private theorem sharedInteriorPairFirstClassParametricTaitEdgeColoring_isTait
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    IsTaitEdgeColoring sharedInteriorPairAnnulusGraph
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv) := by
  rcases third_color_properties hab.1 hab.2.1 hab.2.2 with ⟨hab0, _, _⟩
  rcases third_color_properties huv.1 huv.2.1 huv.2.2 with ⟨huv0, _, _⟩
  intro e
  rcases sharedInteriorPairAnnulus_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | simpa [sharedInteriorPairFirstClassParametricTaitEdgeColoring] using hab.1
    | simpa [sharedInteriorPairFirstClassParametricTaitEdgeColoring] using hab.2.1
    | simpa [sharedInteriorPairFirstClassParametricTaitEdgeColoring] using hab0
    | simpa [sharedInteriorPairFirstClassParametricTaitEdgeColoring] using huv.1
    | simpa [sharedInteriorPairFirstClassParametricTaitEdgeColoring] using huv.2.1
    | simpa [sharedInteriorPairFirstClassParametricTaitEdgeColoring] using huv0

private def sharedInteriorPairSecondClassParametricEdgeColor
    (a b u v : Color) (e : sharedInteriorPairAnnulusGraph.edgeSet) : Color :=
  if e = sip01 ∨ e = sip23 then a
  else if e = sip12 ∨ e = sip40 then b
  else if e = sip30 ∨ e = sip24 then a + b
  else if e = sip56 then u
  else if e = sip67 then v
  else u + v

@[simp] private theorem sharedInteriorPairSecondClassParametricEdgeColor_sip01
    (a b u v : Color) :
    sharedInteriorPairSecondClassParametricEdgeColor a b u v sip01 = a := by
  simp [sharedInteriorPairSecondClassParametricEdgeColor]

@[simp] private theorem sharedInteriorPairSecondClassParametricEdgeColor_sip12
    (a b u v : Color) :
    sharedInteriorPairSecondClassParametricEdgeColor a b u v sip12 = b := by
  simp [sharedInteriorPairSecondClassParametricEdgeColor, sharedInteriorPairAnnulusGraph,
    sip01, sip12, sip23, sip24, sip30, sip40, sip56, sip67]

@[simp] private theorem sharedInteriorPairSecondClassParametricEdgeColor_sip23
    (a b u v : Color) :
    sharedInteriorPairSecondClassParametricEdgeColor a b u v sip23 = a := by
  simp [sharedInteriorPairSecondClassParametricEdgeColor, sharedInteriorPairAnnulusGraph,
    sip01, sip23]

@[simp] private theorem sharedInteriorPairSecondClassParametricEdgeColor_sip30
    (a b u v : Color) :
    sharedInteriorPairSecondClassParametricEdgeColor a b u v sip30 = a + b := by
  simp [sharedInteriorPairSecondClassParametricEdgeColor, sharedInteriorPairAnnulusGraph,
    sip01, sip12, sip23, sip24, sip30, sip40, sip56, sip67]

@[simp] private theorem sharedInteriorPairSecondClassParametricEdgeColor_sip24
    (a b u v : Color) :
    sharedInteriorPairSecondClassParametricEdgeColor a b u v sip24 = a + b := by
  simp [sharedInteriorPairSecondClassParametricEdgeColor, sharedInteriorPairAnnulusGraph,
    sip01, sip12, sip23, sip24, sip30, sip40, sip56, sip67]

@[simp] private theorem sharedInteriorPairSecondClassParametricEdgeColor_sip40
    (a b u v : Color) :
    sharedInteriorPairSecondClassParametricEdgeColor a b u v sip40 = b := by
  simp [sharedInteriorPairSecondClassParametricEdgeColor, sharedInteriorPairAnnulusGraph,
    sip01, sip12, sip23, sip24, sip30, sip40, sip56, sip67]

@[simp] private theorem sharedInteriorPairSecondClassParametricEdgeColor_sip56
    (a b u v : Color) :
    sharedInteriorPairSecondClassParametricEdgeColor a b u v sip56 = u := by
  simp [sharedInteriorPairSecondClassParametricEdgeColor, sharedInteriorPairAnnulusGraph,
    sip01, sip12, sip23, sip24, sip30, sip40, sip56]

@[simp] private theorem sharedInteriorPairSecondClassParametricEdgeColor_sip67
    (a b u v : Color) :
    sharedInteriorPairSecondClassParametricEdgeColor a b u v sip67 = v := by
  simp [sharedInteriorPairSecondClassParametricEdgeColor, sharedInteriorPairAnnulusGraph,
    sip01, sip12, sip23, sip24, sip30, sip40, sip56, sip67]

@[simp] private theorem sharedInteriorPairSecondClassParametricEdgeColor_sip75
    (a b u v : Color) :
    sharedInteriorPairSecondClassParametricEdgeColor a b u v sip75 = u + v := by
  simp [sharedInteriorPairSecondClassParametricEdgeColor, sharedInteriorPairAnnulusGraph,
    sip01, sip12, sip23, sip24, sip30, sip40, sip56, sip67, sip75]

private theorem sharedInteriorPairSecondClassParametricEdgeColor_ne_of_adj
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v)
    {e f : sharedInteriorPairAnnulusGraph.edgeSet}
    (hadj : sharedInteriorPairAnnulusGraph.lineGraph.Adj e f) :
    sharedInteriorPairSecondClassParametricEdgeColor a b u v e ≠
      sharedInteriorPairSecondClassParametricEdgeColor a b u v f := by
  rcases third_color_properties hab.1 hab.2.1 hab.2.2 with ⟨hab0, haba, habb⟩
  rcases third_color_properties huv.1 huv.2.1 huv.2.2 with ⟨huv0, huva, huvb⟩
  intro hcolor
  rw [SimpleGraph.lineGraph_adj_iff_exists] at hadj
  rcases hadj with ⟨hne, vtx, he, hf⟩
  fin_cases vtx
  · rcases sharedInteriorPair_edge_mem_zero he with rfl | rfl | rfl <;>
      rcases sharedInteriorPair_edge_mem_zero hf with rfl | rfl | rfl <;>
      first
      | simpa [sharedInteriorPairAnnulusGraph, sip01, sip30, sip40] using hne
      | exact haba (by simpa using hcolor)
      | exact haba (by simpa using hcolor.symm)
      | exact hab.2.2 (by simpa using hcolor)
      | exact hab.2.2 (by simpa using hcolor.symm)
      | exact habb (by simpa using hcolor)
      | exact habb (by simpa using hcolor.symm)
  · rcases sharedInteriorPair_edge_mem_one he with rfl | rfl <;>
      rcases sharedInteriorPair_edge_mem_one hf with rfl | rfl <;>
      first
      | simpa [sharedInteriorPairAnnulusGraph, sip01, sip12] using hne
      | exact hab.2.2 (by simpa using hcolor)
      | exact hab.2.2 (by simpa using hcolor.symm)
  · rcases sharedInteriorPair_edge_mem_two he with rfl | rfl | rfl <;>
      rcases sharedInteriorPair_edge_mem_two hf with rfl | rfl | rfl <;>
      first
      | simpa [sharedInteriorPairAnnulusGraph, sip12, sip23, sip24] using hne
      | exact hab.2.2 (by simpa using hcolor)
      | exact hab.2.2 (by simpa using hcolor.symm)
      | exact habb (by simpa using hcolor)
      | exact habb (by simpa using hcolor.symm)
      | exact haba (by simpa using hcolor)
      | exact haba (by simpa using hcolor.symm)
  · rcases sharedInteriorPair_edge_mem_three he with rfl | rfl <;>
      rcases sharedInteriorPair_edge_mem_three hf with rfl | rfl <;>
      first
      | simpa [sharedInteriorPairAnnulusGraph, sip23, sip30] using hne
      | exact haba (by simpa using hcolor)
      | exact haba (by simpa using hcolor.symm)
  · rcases sharedInteriorPair_edge_mem_four he with rfl | rfl <;>
      rcases sharedInteriorPair_edge_mem_four hf with rfl | rfl <;>
      first
      | simpa [sharedInteriorPairAnnulusGraph, sip24, sip40] using hne
      | exact habb (by simpa using hcolor)
      | exact habb (by simpa using hcolor.symm)
  · rcases sharedInteriorPair_edge_mem_five he with rfl | rfl <;>
      rcases sharedInteriorPair_edge_mem_five hf with rfl | rfl <;>
      first
      | simpa [sharedInteriorPairAnnulusGraph, sip56, sip75] using hne
      | exact huva (by simpa using hcolor)
      | exact huva (by simpa using hcolor.symm)
  · rcases sharedInteriorPair_edge_mem_six he with rfl | rfl <;>
      rcases sharedInteriorPair_edge_mem_six hf with rfl | rfl <;>
      first
      | simpa [sharedInteriorPairAnnulusGraph, sip56, sip67] using hne
      | exact huv.2.2 (by simpa using hcolor)
      | exact huv.2.2 (by simpa using hcolor.symm)
  · rcases sharedInteriorPair_edge_mem_seven he with rfl | rfl <;>
      rcases sharedInteriorPair_edge_mem_seven hf with rfl | rfl <;>
      first
      | simpa [sharedInteriorPairAnnulusGraph, sip67, sip75] using hne
      | exact huvb (by simpa using hcolor)
      | exact huvb (by simpa using hcolor.symm)

private def sharedInteriorPairSecondClassParametricTaitEdgeColoring
    (a b u v : Color) (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sharedInteriorPairAnnulusGraph.EdgeColoring Color :=
  Coloring.mk (sharedInteriorPairSecondClassParametricEdgeColor a b u v) (by
    intro e f hadj
    exact sharedInteriorPairSecondClassParametricEdgeColor_ne_of_adj hab huv hadj)

private theorem sharedInteriorPairSecondClassParametricTaitEdgeColoring_isTait
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    IsTaitEdgeColoring sharedInteriorPairAnnulusGraph
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv) := by
  rcases third_color_properties hab.1 hab.2.1 hab.2.2 with ⟨hab0, _, _⟩
  rcases third_color_properties huv.1 huv.2.1 huv.2.2 with ⟨huv0, _, _⟩
  intro e
  rcases sharedInteriorPairAnnulus_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | simpa [sharedInteriorPairSecondClassParametricTaitEdgeColoring] using hab.1
    | simpa [sharedInteriorPairSecondClassParametricTaitEdgeColoring] using hab.2.1
    | simpa [sharedInteriorPairSecondClassParametricTaitEdgeColoring] using hab0
    | simpa [sharedInteriorPairSecondClassParametricTaitEdgeColoring] using huv.1
    | simpa [sharedInteriorPairSecondClassParametricTaitEdgeColoring] using huv.2.1
    | simpa [sharedInteriorPairSecondClassParametricTaitEdgeColoring] using huv0

private theorem sharedInteriorPairTaitEdgeColoring_eq_firstClassParametric :
    sharedInteriorPairTaitEdgeColoring =
      sharedInteriorPairFirstClassParametricTaitEdgeColoring red blue red blue
        validColorPair_red_blue validColorPair_red_blue := by
  apply DFunLike.ext
  intro e
  change sharedInteriorPairEdgeColor e =
    sharedInteriorPairFirstClassParametricEdgeColor red blue red blue e
  rcases sharedInteriorPairAnnulus_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [sharedInteriorPairEdgeColor, sharedInteriorPairFirstClassParametricEdgeColor,
      sharedInteriorPairAnnulusGraph, sip01, sip12, sip23, sip24, sip30, sip40, sip56, sip67,
      sip75]

private theorem sharedInteriorPairSecondClosureTaitEdgeColoring_eq_secondClassParametric :
    sharedInteriorPairSecondClosureTaitEdgeColoring =
      sharedInteriorPairSecondClassParametricTaitEdgeColoring red blue red blue
        validColorPair_red_blue validColorPair_red_blue := by
  apply DFunLike.ext
  intro e
  change sharedInteriorPairSecondClosureEdgeColor e =
    sharedInteriorPairSecondClassParametricEdgeColor red blue red blue e
  rcases sharedInteriorPairAnnulus_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [sharedInteriorPairSecondClosureEdgeColor, sharedInteriorPairSecondClassParametricEdgeColor,
      sharedInteriorPairAnnulusGraph, sip01, sip12, sip23, sip24, sip30, sip40, sip56, sip67,
      sip75]

private theorem validColorPair_sharedInteriorPairCore_of_isTait
    (C : sharedInteriorPairAnnulusGraph.EdgeColoring Color)
    (hC : IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C) :
    ValidColorPair (C sip01) (C sip12) :=
  ⟨hC sip01, hC sip12, C.valid sip01_adj_sip12⟩

private theorem validColorPair_sharedInteriorPairTriangle_of_isTait
    (C : sharedInteriorPairAnnulusGraph.EdgeColoring Color)
    (hC : IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C) :
    ValidColorPair (C sip56) (C sip67) :=
  ⟨hC sip56, hC sip67, C.valid sip56_adj_sip67⟩

private theorem sharedInteriorPair_tait_forces_sip75
    (C : sharedInteriorPairAnnulusGraph.EdgeColoring Color)
    (hC : IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C) :
    C sip75 = C sip56 + C sip67 := by
  exact eq_third_color_of_ne_zero_ne_ne (hC sip56) (hC sip67) (hC sip75)
    (C.valid sip56_adj_sip67) (C.valid sip56_adj_sip75) (C.valid sip67_adj_sip75)

private theorem sharedInteriorPair_tait_forces_sip24
    (C : sharedInteriorPairAnnulusGraph.EdgeColoring Color)
    (hC : IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C) :
    C sip24 = C sip12 + C sip23 := by
  exact eq_third_color_of_ne_zero_ne_ne (hC sip12) (hC sip23) (hC sip24)
    (C.valid sip12_adj_sip23) (C.valid sip12_adj_sip24) (C.valid sip23_adj_sip24)

private theorem sharedInteriorPair_tait_forces_sip40
    (C : sharedInteriorPairAnnulusGraph.EdgeColoring Color)
    (hC : IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C) :
    C sip40 = C sip01 + C sip30 := by
  exact eq_third_color_of_ne_zero_ne_ne (hC sip01) (hC sip30) (hC sip40)
    (C.valid sip01_adj_sip30) (C.valid sip01_adj_sip40) (C.valid sip30_adj_sip40)

private theorem sharedInteriorPair_tait_sip23_eq_left_or_third
    (C : sharedInteriorPairAnnulusGraph.EdgeColoring Color)
    (hC : IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C) :
    C sip23 = C sip01 ∨ C sip23 = C sip01 + C sip12 := by
  exact eq_left_or_eq_add_of_ne_right (hC sip01) (hC sip12) (hC sip23)
    (C.valid sip01_adj_sip12) (C.valid sip12_adj_sip23).symm

private theorem eq_first_or_secondClassParametric_of_isTait
    (C : sharedInteriorPairAnnulusGraph.EdgeColoring Color)
    (hC : IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C) :
    C =
        sharedInteriorPairFirstClassParametricTaitEdgeColoring
          (C sip01) (C sip12) (C sip56) (C sip67)
          (validColorPair_sharedInteriorPairCore_of_isTait C hC)
          (validColorPair_sharedInteriorPairTriangle_of_isTait C hC) ∨
      C =
        sharedInteriorPairSecondClassParametricTaitEdgeColoring
          (C sip01) (C sip12) (C sip56) (C sip67)
          (validColorPair_sharedInteriorPairCore_of_isTait C hC)
          (validColorPair_sharedInteriorPairTriangle_of_isTait C hC) := by
  let hab := validColorPair_sharedInteriorPairCore_of_isTait C hC
  let huv := validColorPair_sharedInteriorPairTriangle_of_isTait C hC
  have hsip75 : C sip75 = C sip56 + C sip67 :=
    sharedInteriorPair_tait_forces_sip75 C hC
  have hsip24 : C sip24 = C sip12 + C sip23 :=
    sharedInteriorPair_tait_forces_sip24 C hC
  have hsip40 : C sip40 = C sip01 + C sip30 :=
    sharedInteriorPair_tait_forces_sip40 C hC
  rcases sharedInteriorPair_tait_sip23_eq_left_or_third C hC with h23 | h23
  · right
    have hsip24_eq : C sip24 = C sip01 + C sip12 := by
      calc
        C sip24 = C sip12 + C sip23 := hsip24
        _ = C sip01 + C sip12 := by rw [h23, add_comm]
    have hsip40_ne_left : C sip40 ≠ C sip01 := (C.valid sip01_adj_sip40).symm
    have hsip40_ne_add : C sip40 ≠ C sip01 + C sip12 := by
      rw [← hsip24_eq]
      exact (C.valid sip24_adj_sip40).symm
    have hsip40_eq : C sip40 = C sip12 :=
      eq_right_of_ne_left_ne_add hab.1 hab.2.1 (hC sip40) hab.2.2 hsip40_ne_left hsip40_ne_add
    have hsip30_eq : C sip30 = C sip01 + C sip12 := by
      have hsip30_from40 : C sip01 + C sip40 = C sip30 := by
        calc
          C sip01 + C sip40 = C sip01 + (C sip01 + C sip30) := by
            exact congrArg (fun x => C sip01 + x) hsip40
          _ = C sip30 := by
            calc
              C sip01 + (C sip01 + C sip30) = (C sip01 + C sip01) + C sip30 := by
                ac_rfl
              _ = C sip30 := by simp
      calc
        C sip30 = C sip01 + C sip40 := hsip30_from40.symm
        _ = C sip01 + C sip12 := by rw [hsip40_eq]
    apply DFunLike.ext
    intro e
    change C e =
      sharedInteriorPairSecondClassParametricEdgeColor
        (C sip01) (C sip12) (C sip56) (C sip67) e
    rcases sharedInteriorPairAnnulus_edge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · simpa [h23]
    · simpa [hsip30_eq]
    · simpa using hsip24_eq
    · simpa [hsip40_eq]
    · simp
    · simp
    · simpa [hsip75]
  · left
    have hsip30_ne_left : C sip30 ≠ C sip01 := (C.valid sip01_adj_sip30).symm
    have hsip30_ne_add : C sip30 ≠ C sip01 + C sip12 := by
      rw [← h23]
      exact (C.valid sip23_adj_sip30).symm
    have hsip30_eq : C sip30 = C sip12 :=
      eq_right_of_ne_left_ne_add hab.1 hab.2.1 (hC sip30) hab.2.2 hsip30_ne_left hsip30_ne_add
    have hsip40_eq : C sip40 = C sip01 + C sip12 := by
      calc
        C sip40 = C sip01 + C sip30 := hsip40
        _ = C sip01 + C sip12 := by rw [hsip30_eq]
    apply DFunLike.ext
    intro e
    change C e =
      sharedInteriorPairFirstClassParametricEdgeColor
        (C sip01) (C sip12) (C sip56) (C sip67) e
    rcases sharedInteriorPairAnnulus_edge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · simpa [h23]
    · simpa [hsip30_eq]
    · calc
        C sip24 = C sip12 + C sip23 := hsip24
        _ = C sip01 := by
          rw [h23]
          calc
            C sip12 + (C sip01 + C sip12) = (C sip12 + C sip12) + C sip01 := by
              ac_rfl
            _ = C sip01 := by simp
    · simpa using hsip40_eq
    · simp
    · simp
    · simpa [hsip75]

private theorem not_mem_kempeComponentSet_of_ne_left_ne_right
    {x y : Color}
    {C : sharedInteriorPairAnnulusGraph.EdgeColoring Color}
    {K : (C.bicoloredSubgraph x y).ConnectedComponent}
    {e : sharedInteriorPairAnnulusGraph.edgeSet}
    (hx : C e ≠ x) (hy : C e ≠ y) :
    e ∉ C.kempeComponentSet x y K := by
  intro hmem
  rcases C.mem_bicoloredSet_of_mem_kempeComponentSet hmem with h | h
  · exact hx h
  · exact hy h

private theorem not_mem_component_containing_sip01_of_sharedEdgeRegion_true
    {x y : Color}
    {C : sharedInteriorPairAnnulusGraph.EdgeColoring Color}
    {K : (C.bicoloredSubgraph x y).ConnectedComponent}
    {e : sharedInteriorPairAnnulusGraph.edgeSet}
    (h01 : sip01 ∈ C.kempeComponentSet x y K)
    (hregion : sharedEdgeRegion e = true) :
    e ∉ C.kempeComponentSet x y K := by
  intro hmem
  have hfalse := sharedEdgeRegion_eq_false_of_mem_component_containing_sip01 h01 hmem
  rw [hregion] at hfalse
  cases hfalse

private theorem not_mem_component_containing_sip56_of_sharedEdgeRegion_false
    {x y : Color}
    {C : sharedInteriorPairAnnulusGraph.EdgeColoring Color}
    {K : (C.bicoloredSubgraph x y).ConnectedComponent}
    {e : sharedInteriorPairAnnulusGraph.edgeSet}
    (h56 : sip56 ∈ C.kempeComponentSet x y K)
    (hregion : sharedEdgeRegion e = false) :
    e ∉ C.kempeComponentSet x y K := by
  intro hmem
  have htrue := sharedEdgeRegion_eq_true_of_mem_component_containing_sip56 h56 hmem
  rw [hregion] at htrue
  cases htrue

private theorem sip01_mem_firstClass_bicoloredSet_ab
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip01 ∈
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv).bicoloredSet a b := by
  left
  change sharedInteriorPairFirstClassParametricEdgeColor a b u v sip01 = a
  simp

private noncomputable def sharedInteriorPairFirstClassABComponent
    (a b u v : Color) (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    ((sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv).bicoloredSubgraph
      a b).ConnectedComponent :=
  let C := sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv
  (C.bicoloredSubgraph a b).connectedComponentMk
    ⟨sip01, sip01_mem_firstClass_bicoloredSet_ab hab huv⟩

private theorem sip01_mem_sharedInteriorPairFirstClassABComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip01 ∈
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        a b (sharedInteriorPairFirstClassABComponent a b u v hab huv) := by
  let C := sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv
  exact C.mem_kempeComponentSet_self (sip01_mem_firstClass_bicoloredSet_ab hab huv)

private theorem sip12_mem_sharedInteriorPairFirstClassABComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip12 ∈
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        a b (sharedInteriorPairFirstClassABComponent a b u v hab huv) := by
  let C := sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv
  exact C.mem_kempeComponentSet_of_adj
    (sip01_mem_sharedInteriorPairFirstClassABComponent hab huv) sip01_adj_sip12 (by
      right
      change sharedInteriorPairFirstClassParametricEdgeColor a b u v sip12 = b
      simp)

private theorem sip30_mem_sharedInteriorPairFirstClassABComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip30 ∈
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        a b (sharedInteriorPairFirstClassABComponent a b u v hab huv) := by
  let C := sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv
  exact C.mem_kempeComponentSet_of_adj
    (sip01_mem_sharedInteriorPairFirstClassABComponent hab huv) sip01_adj_sip30 (by
      right
      change sharedInteriorPairFirstClassParametricEdgeColor a b u v sip30 = b
      simp)

private theorem sip24_mem_sharedInteriorPairFirstClassABComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip24 ∈
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        a b (sharedInteriorPairFirstClassABComponent a b u v hab huv) := by
  let C := sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv
  exact C.mem_kempeComponentSet_of_adj
    (sip12_mem_sharedInteriorPairFirstClassABComponent hab huv) sip12_adj_sip24 (by
      left
      change sharedInteriorPairFirstClassParametricEdgeColor a b u v sip24 = a
      simp)

private theorem sip23_not_mem_sharedInteriorPairFirstClassABComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip23 ∉
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        a b (sharedInteriorPairFirstClassABComponent a b u v hab huv) := by
  rcases third_color_properties hab.1 hab.2.1 hab.2.2 with ⟨_, haba, habb⟩
  let C := sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv
  exact not_mem_kempeComponentSet_of_ne_left_ne_right
    (C := C) (K := sharedInteriorPairFirstClassABComponent a b u v hab huv)
    (e := sip23)
    (by
      change sharedInteriorPairFirstClassParametricEdgeColor a b u v sip23 ≠ a
      simpa using haba)
    (by
      change sharedInteriorPairFirstClassParametricEdgeColor a b u v sip23 ≠ b
      simpa using habb)

private theorem sip40_not_mem_sharedInteriorPairFirstClassABComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip40 ∉
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        a b (sharedInteriorPairFirstClassABComponent a b u v hab huv) := by
  rcases third_color_properties hab.1 hab.2.1 hab.2.2 with ⟨_, haba, habb⟩
  let C := sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv
  exact not_mem_kempeComponentSet_of_ne_left_ne_right
    (C := C) (K := sharedInteriorPairFirstClassABComponent a b u v hab huv)
    (e := sip40)
    (by
      change sharedInteriorPairFirstClassParametricEdgeColor a b u v sip40 ≠ a
      simpa using haba)
    (by
      change sharedInteriorPairFirstClassParametricEdgeColor a b u v sip40 ≠ b
      simpa using habb)

private theorem sip56_not_mem_sharedInteriorPairFirstClassABComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip56 ∉
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        a b (sharedInteriorPairFirstClassABComponent a b u v hab huv) := by
  exact not_mem_component_containing_sip01_of_sharedEdgeRegion_true
    (sip01_mem_sharedInteriorPairFirstClassABComponent hab huv) (by decide)

private theorem sip67_not_mem_sharedInteriorPairFirstClassABComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip67 ∉
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        a b (sharedInteriorPairFirstClassABComponent a b u v hab huv) := by
  exact not_mem_component_containing_sip01_of_sharedEdgeRegion_true
    (sip01_mem_sharedInteriorPairFirstClassABComponent hab huv) (by decide)

private theorem sip75_not_mem_sharedInteriorPairFirstClassABComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip75 ∉
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        a b (sharedInteriorPairFirstClassABComponent a b u v hab huv) := by
  exact not_mem_component_containing_sip01_of_sharedEdgeRegion_true
    (sip01_mem_sharedInteriorPairFirstClassABComponent hab huv) (by decide)

private theorem sharedInteriorPairFirstClassParametricTaitEdgeColoring_swap_ab_eq
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv).swapOnKempeComponent
        a b (sharedInteriorPairFirstClassABComponent a b u v hab huv) =
      sharedInteriorPairFirstClassParametricTaitEdgeColoring b a u v
        (validColorPair_symm hab) huv := by
  apply DFunLike.ext
  intro e
  rcases sharedInteriorPairAnnulus_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [Coloring.swapOnKempeComponent_apply_of_mem]
    · change Equiv.swap a b (sharedInteriorPairFirstClassParametricEdgeColor a b u v sip01) =
        sharedInteriorPairFirstClassParametricEdgeColor b a u v sip01
      simp
    · exact sip01_mem_sharedInteriorPairFirstClassABComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_mem]
    · change Equiv.swap a b (sharedInteriorPairFirstClassParametricEdgeColor a b u v sip12) =
        sharedInteriorPairFirstClassParametricEdgeColor b a u v sip12
      simp
    · exact sip12_mem_sharedInteriorPairFirstClassABComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change sharedInteriorPairFirstClassParametricEdgeColor a b u v sip23 =
        sharedInteriorPairFirstClassParametricEdgeColor b a u v sip23
      simp [add_comm]
    · exact sip23_not_mem_sharedInteriorPairFirstClassABComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_mem]
    · change Equiv.swap a b (sharedInteriorPairFirstClassParametricEdgeColor a b u v sip30) =
        sharedInteriorPairFirstClassParametricEdgeColor b a u v sip30
      simp
    · exact sip30_mem_sharedInteriorPairFirstClassABComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_mem]
    · change Equiv.swap a b (sharedInteriorPairFirstClassParametricEdgeColor a b u v sip24) =
        sharedInteriorPairFirstClassParametricEdgeColor b a u v sip24
      simp
    · exact sip24_mem_sharedInteriorPairFirstClassABComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change sharedInteriorPairFirstClassParametricEdgeColor a b u v sip40 =
        sharedInteriorPairFirstClassParametricEdgeColor b a u v sip40
      simp [add_comm]
    · exact sip40_not_mem_sharedInteriorPairFirstClassABComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change sharedInteriorPairFirstClassParametricEdgeColor a b u v sip56 =
        sharedInteriorPairFirstClassParametricEdgeColor b a u v sip56
      simp
    · exact sip56_not_mem_sharedInteriorPairFirstClassABComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change sharedInteriorPairFirstClassParametricEdgeColor a b u v sip67 =
        sharedInteriorPairFirstClassParametricEdgeColor b a u v sip67
      simp
    · exact sip67_not_mem_sharedInteriorPairFirstClassABComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change sharedInteriorPairFirstClassParametricEdgeColor a b u v sip75 =
        sharedInteriorPairFirstClassParametricEdgeColor b a u v sip75
      simp
    · exact sip75_not_mem_sharedInteriorPairFirstClassABComponent hab huv

private theorem sharedInteriorPairFirstClassParametricTaitEdgeColoring_swap_ab_mem_edgeKempeClosure
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sharedInteriorPairFirstClassParametricTaitEdgeColoring b a u v
        (validColorPair_symm hab) huv ∈
      sharedInteriorPairAnnulusGraph.EdgeKempeClosure
        (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv) := by
  rw [← sharedInteriorPairFirstClassParametricTaitEdgeColoring_swap_ab_eq hab huv]
  exact sharedInteriorPairAnnulusGraph.mem_edgeKempeClosure_of_mem_of_step
    (sharedInteriorPairAnnulusGraph.mem_edgeKempeClosure_self
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv))
    a b (sharedInteriorPairFirstClassABComponent a b u v hab huv)

private theorem sip01_mem_firstClass_bicoloredSet_aThird
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip01 ∈
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv).bicoloredSet
        a (a + b) := by
  left
  change sharedInteriorPairFirstClassParametricEdgeColor a b u v sip01 = a
  simp

private noncomputable def sharedInteriorPairFirstClassAThirdComponent
    (a b u v : Color) (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    ((sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv).bicoloredSubgraph
      a (a + b)).ConnectedComponent :=
  let C := sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv
  (C.bicoloredSubgraph a (a + b)).connectedComponentMk
    ⟨sip01, sip01_mem_firstClass_bicoloredSet_aThird hab huv⟩

private theorem sip01_mem_sharedInteriorPairFirstClassAThirdComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip01 ∈
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        a (a + b) (sharedInteriorPairFirstClassAThirdComponent a b u v hab huv) := by
  let C := sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv
  exact C.mem_kempeComponentSet_self (sip01_mem_firstClass_bicoloredSet_aThird hab huv)

private theorem sip40_mem_sharedInteriorPairFirstClassAThirdComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip40 ∈
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        a (a + b) (sharedInteriorPairFirstClassAThirdComponent a b u v hab huv) := by
  let C := sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv
  exact C.mem_kempeComponentSet_of_adj
    (sip01_mem_sharedInteriorPairFirstClassAThirdComponent hab huv) sip01_adj_sip40 (by
      right
      change sharedInteriorPairFirstClassParametricEdgeColor a b u v sip40 = a + b
      simp)

private theorem sip24_mem_sharedInteriorPairFirstClassAThirdComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip24 ∈
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        a (a + b) (sharedInteriorPairFirstClassAThirdComponent a b u v hab huv) := by
  let C := sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv
  exact C.mem_kempeComponentSet_of_adj
    (sip40_mem_sharedInteriorPairFirstClassAThirdComponent hab huv) sip24_adj_sip40.symm (by
      left
      change sharedInteriorPairFirstClassParametricEdgeColor a b u v sip24 = a
      simp)

private theorem sip23_mem_sharedInteriorPairFirstClassAThirdComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip23 ∈
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        a (a + b) (sharedInteriorPairFirstClassAThirdComponent a b u v hab huv) := by
  let C := sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv
  exact C.mem_kempeComponentSet_of_adj
    (sip24_mem_sharedInteriorPairFirstClassAThirdComponent hab huv) sip23_adj_sip24.symm (by
      right
      change sharedInteriorPairFirstClassParametricEdgeColor a b u v sip23 = a + b
      simp)

private theorem sip12_not_mem_sharedInteriorPairFirstClassAThirdComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip12 ∉
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        a (a + b) (sharedInteriorPairFirstClassAThirdComponent a b u v hab huv) := by
  rcases third_color_properties hab.1 hab.2.1 hab.2.2 with ⟨_, _, habb⟩
  let C := sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv
  exact not_mem_kempeComponentSet_of_ne_left_ne_right
    (C := C) (K := sharedInteriorPairFirstClassAThirdComponent a b u v hab huv)
    (e := sip12)
    (by
      change sharedInteriorPairFirstClassParametricEdgeColor a b u v sip12 ≠ a
      simpa using hab.2.2.symm)
    (by
      change sharedInteriorPairFirstClassParametricEdgeColor a b u v sip12 ≠ a + b
      simpa using habb.symm)

private theorem sip30_not_mem_sharedInteriorPairFirstClassAThirdComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip30 ∉
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        a (a + b) (sharedInteriorPairFirstClassAThirdComponent a b u v hab huv) := by
  rcases third_color_properties hab.1 hab.2.1 hab.2.2 with ⟨_, _, habb⟩
  let C := sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv
  exact not_mem_kempeComponentSet_of_ne_left_ne_right
    (C := C) (K := sharedInteriorPairFirstClassAThirdComponent a b u v hab huv)
    (e := sip30)
    (by
      change sharedInteriorPairFirstClassParametricEdgeColor a b u v sip30 ≠ a
      simpa using hab.2.2.symm)
    (by
      change sharedInteriorPairFirstClassParametricEdgeColor a b u v sip30 ≠ a + b
      simpa using habb.symm)

private theorem sip56_not_mem_sharedInteriorPairFirstClassAThirdComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip56 ∉
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        a (a + b) (sharedInteriorPairFirstClassAThirdComponent a b u v hab huv) := by
  exact not_mem_component_containing_sip01_of_sharedEdgeRegion_true
    (sip01_mem_sharedInteriorPairFirstClassAThirdComponent hab huv) (by decide)

private theorem sip67_not_mem_sharedInteriorPairFirstClassAThirdComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip67 ∉
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        a (a + b) (sharedInteriorPairFirstClassAThirdComponent a b u v hab huv) := by
  exact not_mem_component_containing_sip01_of_sharedEdgeRegion_true
    (sip01_mem_sharedInteriorPairFirstClassAThirdComponent hab huv) (by decide)

private theorem sip75_not_mem_sharedInteriorPairFirstClassAThirdComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip75 ∉
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        a (a + b) (sharedInteriorPairFirstClassAThirdComponent a b u v hab huv) := by
  exact not_mem_component_containing_sip01_of_sharedEdgeRegion_true
    (sip01_mem_sharedInteriorPairFirstClassAThirdComponent hab huv) (by decide)

private theorem sharedInteriorPairFirstClassParametricTaitEdgeColoring_swap_aThird_eq
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv).swapOnKempeComponent
        a (a + b) (sharedInteriorPairFirstClassAThirdComponent a b u v hab huv) =
      sharedInteriorPairFirstClassParametricTaitEdgeColoring (a + b) b u v
        (validColorPair_third_left hab) huv := by
  apply DFunLike.ext
  intro e
  rcases sharedInteriorPairAnnulus_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [Coloring.swapOnKempeComponent_apply_of_mem]
    · change Equiv.swap a (a + b) (sharedInteriorPairFirstClassParametricEdgeColor a b u v sip01) =
        sharedInteriorPairFirstClassParametricEdgeColor (a + b) b u v sip01
      simp
    · exact sip01_mem_sharedInteriorPairFirstClassAThirdComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change sharedInteriorPairFirstClassParametricEdgeColor a b u v sip12 =
        sharedInteriorPairFirstClassParametricEdgeColor (a + b) b u v sip12
      simp
    · exact sip12_not_mem_sharedInteriorPairFirstClassAThirdComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_mem]
    · change Equiv.swap a (a + b) (sharedInteriorPairFirstClassParametricEdgeColor a b u v sip23) =
        sharedInteriorPairFirstClassParametricEdgeColor (a + b) b u v sip23
      simp [add_assoc]
    · exact sip23_mem_sharedInteriorPairFirstClassAThirdComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change sharedInteriorPairFirstClassParametricEdgeColor a b u v sip30 =
        sharedInteriorPairFirstClassParametricEdgeColor (a + b) b u v sip30
      simp
    · exact sip30_not_mem_sharedInteriorPairFirstClassAThirdComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_mem]
    · change Equiv.swap a (a + b) (sharedInteriorPairFirstClassParametricEdgeColor a b u v sip24) =
        sharedInteriorPairFirstClassParametricEdgeColor (a + b) b u v sip24
      simp
    · exact sip24_mem_sharedInteriorPairFirstClassAThirdComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_mem]
    · change Equiv.swap a (a + b) (sharedInteriorPairFirstClassParametricEdgeColor a b u v sip40) =
        sharedInteriorPairFirstClassParametricEdgeColor (a + b) b u v sip40
      simp [add_assoc]
    · exact sip40_mem_sharedInteriorPairFirstClassAThirdComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change sharedInteriorPairFirstClassParametricEdgeColor a b u v sip56 =
        sharedInteriorPairFirstClassParametricEdgeColor (a + b) b u v sip56
      simp
    · exact sip56_not_mem_sharedInteriorPairFirstClassAThirdComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change sharedInteriorPairFirstClassParametricEdgeColor a b u v sip67 =
        sharedInteriorPairFirstClassParametricEdgeColor (a + b) b u v sip67
      simp
    · exact sip67_not_mem_sharedInteriorPairFirstClassAThirdComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change sharedInteriorPairFirstClassParametricEdgeColor a b u v sip75 =
        sharedInteriorPairFirstClassParametricEdgeColor (a + b) b u v sip75
      simp
    · exact sip75_not_mem_sharedInteriorPairFirstClassAThirdComponent hab huv

private theorem sharedInteriorPairFirstClassParametricTaitEdgeColoring_swap_aThird_mem_edgeKempeClosure
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sharedInteriorPairFirstClassParametricTaitEdgeColoring (a + b) b u v
        (validColorPair_third_left hab) huv ∈
      sharedInteriorPairAnnulusGraph.EdgeKempeClosure
        (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv) := by
  rw [← sharedInteriorPairFirstClassParametricTaitEdgeColoring_swap_aThird_eq hab huv]
  exact sharedInteriorPairAnnulusGraph.mem_edgeKempeClosure_of_mem_of_step
    (sharedInteriorPairAnnulusGraph.mem_edgeKempeClosure_self
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv))
    a (a + b) (sharedInteriorPairFirstClassAThirdComponent a b u v hab huv)

private theorem sip56_mem_firstClass_bicoloredSet_uv
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip56 ∈
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv).bicoloredSet u v := by
  left
  change sharedInteriorPairFirstClassParametricEdgeColor a b u v sip56 = u
  simp

private noncomputable def sharedInteriorPairFirstClassOuterUVComponent
    (a b u v : Color) (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    ((sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv).bicoloredSubgraph
      u v).ConnectedComponent :=
  let C := sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv
  (C.bicoloredSubgraph u v).connectedComponentMk
    ⟨sip56, sip56_mem_firstClass_bicoloredSet_uv hab huv⟩

private theorem sip56_mem_sharedInteriorPairFirstClassOuterUVComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip56 ∈
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        u v (sharedInteriorPairFirstClassOuterUVComponent a b u v hab huv) := by
  let C := sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv
  exact C.mem_kempeComponentSet_self (sip56_mem_firstClass_bicoloredSet_uv hab huv)

private theorem sip67_mem_sharedInteriorPairFirstClassOuterUVComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip67 ∈
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        u v (sharedInteriorPairFirstClassOuterUVComponent a b u v hab huv) := by
  let C := sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv
  exact C.mem_kempeComponentSet_of_adj
    (sip56_mem_sharedInteriorPairFirstClassOuterUVComponent hab huv) sip56_adj_sip67 (by
      right
      change sharedInteriorPairFirstClassParametricEdgeColor a b u v sip67 = v
      simp)

private theorem sip75_not_mem_sharedInteriorPairFirstClassOuterUVComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip75 ∉
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        u v (sharedInteriorPairFirstClassOuterUVComponent a b u v hab huv) := by
  rcases third_color_properties huv.1 huv.2.1 huv.2.2 with ⟨_, huva, huvb⟩
  let C := sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv
  exact not_mem_kempeComponentSet_of_ne_left_ne_right
    (C := C) (K := sharedInteriorPairFirstClassOuterUVComponent a b u v hab huv)
    (e := sip75)
    (by
      change sharedInteriorPairFirstClassParametricEdgeColor a b u v sip75 ≠ u
      simpa using huva)
    (by
      change sharedInteriorPairFirstClassParametricEdgeColor a b u v sip75 ≠ v
      simpa using huvb)

private theorem sip01_not_mem_sharedInteriorPairFirstClassOuterUVComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip01 ∉
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        u v (sharedInteriorPairFirstClassOuterUVComponent a b u v hab huv) := by
  exact not_mem_component_containing_sip56_of_sharedEdgeRegion_false
    (sip56_mem_sharedInteriorPairFirstClassOuterUVComponent hab huv) (by decide)

private theorem sip12_not_mem_sharedInteriorPairFirstClassOuterUVComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip12 ∉
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        u v (sharedInteriorPairFirstClassOuterUVComponent a b u v hab huv) := by
  exact not_mem_component_containing_sip56_of_sharedEdgeRegion_false
    (sip56_mem_sharedInteriorPairFirstClassOuterUVComponent hab huv) (by decide)

private theorem sip23_not_mem_sharedInteriorPairFirstClassOuterUVComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip23 ∉
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        u v (sharedInteriorPairFirstClassOuterUVComponent a b u v hab huv) := by
  exact not_mem_component_containing_sip56_of_sharedEdgeRegion_false
    (sip56_mem_sharedInteriorPairFirstClassOuterUVComponent hab huv) (by decide)

private theorem sip30_not_mem_sharedInteriorPairFirstClassOuterUVComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip30 ∉
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        u v (sharedInteriorPairFirstClassOuterUVComponent a b u v hab huv) := by
  exact not_mem_component_containing_sip56_of_sharedEdgeRegion_false
    (sip56_mem_sharedInteriorPairFirstClassOuterUVComponent hab huv) (by decide)

private theorem sip24_not_mem_sharedInteriorPairFirstClassOuterUVComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip24 ∉
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        u v (sharedInteriorPairFirstClassOuterUVComponent a b u v hab huv) := by
  exact not_mem_component_containing_sip56_of_sharedEdgeRegion_false
    (sip56_mem_sharedInteriorPairFirstClassOuterUVComponent hab huv) (by decide)

private theorem sip40_not_mem_sharedInteriorPairFirstClassOuterUVComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip40 ∉
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        u v (sharedInteriorPairFirstClassOuterUVComponent a b u v hab huv) := by
  exact not_mem_component_containing_sip56_of_sharedEdgeRegion_false
    (sip56_mem_sharedInteriorPairFirstClassOuterUVComponent hab huv) (by decide)

private theorem sharedInteriorPairFirstClassParametricTaitEdgeColoring_swap_uv_eq
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv).swapOnKempeComponent
        u v (sharedInteriorPairFirstClassOuterUVComponent a b u v hab huv) =
      sharedInteriorPairFirstClassParametricTaitEdgeColoring a b v u hab
        (validColorPair_symm huv) := by
  apply DFunLike.ext
  intro e
  rcases sharedInteriorPairAnnulus_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change sharedInteriorPairFirstClassParametricEdgeColor a b u v sip01 =
        sharedInteriorPairFirstClassParametricEdgeColor a b v u sip01
      simp
    · exact sip01_not_mem_sharedInteriorPairFirstClassOuterUVComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change sharedInteriorPairFirstClassParametricEdgeColor a b u v sip12 =
        sharedInteriorPairFirstClassParametricEdgeColor a b v u sip12
      simp
    · exact sip12_not_mem_sharedInteriorPairFirstClassOuterUVComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change sharedInteriorPairFirstClassParametricEdgeColor a b u v sip23 =
        sharedInteriorPairFirstClassParametricEdgeColor a b v u sip23
      simp
    · exact sip23_not_mem_sharedInteriorPairFirstClassOuterUVComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change sharedInteriorPairFirstClassParametricEdgeColor a b u v sip30 =
        sharedInteriorPairFirstClassParametricEdgeColor a b v u sip30
      simp
    · exact sip30_not_mem_sharedInteriorPairFirstClassOuterUVComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change sharedInteriorPairFirstClassParametricEdgeColor a b u v sip24 =
        sharedInteriorPairFirstClassParametricEdgeColor a b v u sip24
      simp
    · exact sip24_not_mem_sharedInteriorPairFirstClassOuterUVComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change sharedInteriorPairFirstClassParametricEdgeColor a b u v sip40 =
        sharedInteriorPairFirstClassParametricEdgeColor a b v u sip40
      simp
    · exact sip40_not_mem_sharedInteriorPairFirstClassOuterUVComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_mem]
    · change Equiv.swap u v (sharedInteriorPairFirstClassParametricEdgeColor a b u v sip56) =
        sharedInteriorPairFirstClassParametricEdgeColor a b v u sip56
      simp
    · exact sip56_mem_sharedInteriorPairFirstClassOuterUVComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_mem]
    · change Equiv.swap u v (sharedInteriorPairFirstClassParametricEdgeColor a b u v sip67) =
        sharedInteriorPairFirstClassParametricEdgeColor a b v u sip67
      simp
    · exact sip67_mem_sharedInteriorPairFirstClassOuterUVComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change sharedInteriorPairFirstClassParametricEdgeColor a b u v sip75 =
        sharedInteriorPairFirstClassParametricEdgeColor a b v u sip75
      simp [add_comm]
    · exact sip75_not_mem_sharedInteriorPairFirstClassOuterUVComponent hab huv

private theorem sharedInteriorPairFirstClassParametricTaitEdgeColoring_swap_uv_mem_edgeKempeClosure
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sharedInteriorPairFirstClassParametricTaitEdgeColoring a b v u hab
        (validColorPair_symm huv) ∈
      sharedInteriorPairAnnulusGraph.EdgeKempeClosure
        (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv) := by
  rw [← sharedInteriorPairFirstClassParametricTaitEdgeColoring_swap_uv_eq hab huv]
  exact sharedInteriorPairAnnulusGraph.mem_edgeKempeClosure_of_mem_of_step
    (sharedInteriorPairAnnulusGraph.mem_edgeKempeClosure_self
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv))
    u v (sharedInteriorPairFirstClassOuterUVComponent a b u v hab huv)

private theorem sip56_mem_firstClass_bicoloredSet_uThird
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip56 ∈
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv).bicoloredSet
        u (u + v) := by
  left
  change sharedInteriorPairFirstClassParametricEdgeColor a b u v sip56 = u
  simp

private noncomputable def sharedInteriorPairFirstClassOuterUThirdComponent
    (a b u v : Color) (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    ((sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv).bicoloredSubgraph
      u (u + v)).ConnectedComponent :=
  let C := sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv
  (C.bicoloredSubgraph u (u + v)).connectedComponentMk
    ⟨sip56, sip56_mem_firstClass_bicoloredSet_uThird hab huv⟩

private theorem sip56_mem_sharedInteriorPairFirstClassOuterUThirdComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip56 ∈
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        u (u + v) (sharedInteriorPairFirstClassOuterUThirdComponent a b u v hab huv) := by
  let C := sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv
  exact C.mem_kempeComponentSet_self (sip56_mem_firstClass_bicoloredSet_uThird hab huv)

private theorem sip75_mem_sharedInteriorPairFirstClassOuterUThirdComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip75 ∈
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        u (u + v) (sharedInteriorPairFirstClassOuterUThirdComponent a b u v hab huv) := by
  let C := sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv
  exact C.mem_kempeComponentSet_of_adj
    (sip56_mem_sharedInteriorPairFirstClassOuterUThirdComponent hab huv) sip56_adj_sip75 (by
      right
      change sharedInteriorPairFirstClassParametricEdgeColor a b u v sip75 = u + v
      simp)

private theorem sip67_not_mem_sharedInteriorPairFirstClassOuterUThirdComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip67 ∉
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        u (u + v) (sharedInteriorPairFirstClassOuterUThirdComponent a b u v hab huv) := by
  rcases third_color_properties huv.1 huv.2.1 huv.2.2 with ⟨_, _, huvb⟩
  let C := sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv
  exact not_mem_kempeComponentSet_of_ne_left_ne_right
    (C := C) (K := sharedInteriorPairFirstClassOuterUThirdComponent a b u v hab huv)
    (e := sip67)
    (by
      change sharedInteriorPairFirstClassParametricEdgeColor a b u v sip67 ≠ u
      simpa using huv.2.2.symm)
    (by
      change sharedInteriorPairFirstClassParametricEdgeColor a b u v sip67 ≠ u + v
      simpa using huvb.symm)

private theorem sip01_not_mem_sharedInteriorPairFirstClassOuterUThirdComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip01 ∉
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        u (u + v) (sharedInteriorPairFirstClassOuterUThirdComponent a b u v hab huv) := by
  exact not_mem_component_containing_sip56_of_sharedEdgeRegion_false
    (sip56_mem_sharedInteriorPairFirstClassOuterUThirdComponent hab huv) (by decide)

private theorem sip12_not_mem_sharedInteriorPairFirstClassOuterUThirdComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip12 ∉
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        u (u + v) (sharedInteriorPairFirstClassOuterUThirdComponent a b u v hab huv) := by
  exact not_mem_component_containing_sip56_of_sharedEdgeRegion_false
    (sip56_mem_sharedInteriorPairFirstClassOuterUThirdComponent hab huv) (by decide)

private theorem sip23_not_mem_sharedInteriorPairFirstClassOuterUThirdComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip23 ∉
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        u (u + v) (sharedInteriorPairFirstClassOuterUThirdComponent a b u v hab huv) := by
  exact not_mem_component_containing_sip56_of_sharedEdgeRegion_false
    (sip56_mem_sharedInteriorPairFirstClassOuterUThirdComponent hab huv) (by decide)

private theorem sip30_not_mem_sharedInteriorPairFirstClassOuterUThirdComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip30 ∉
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        u (u + v) (sharedInteriorPairFirstClassOuterUThirdComponent a b u v hab huv) := by
  exact not_mem_component_containing_sip56_of_sharedEdgeRegion_false
    (sip56_mem_sharedInteriorPairFirstClassOuterUThirdComponent hab huv) (by decide)

private theorem sip24_not_mem_sharedInteriorPairFirstClassOuterUThirdComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip24 ∉
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        u (u + v) (sharedInteriorPairFirstClassOuterUThirdComponent a b u v hab huv) := by
  exact not_mem_component_containing_sip56_of_sharedEdgeRegion_false
    (sip56_mem_sharedInteriorPairFirstClassOuterUThirdComponent hab huv) (by decide)

private theorem sip40_not_mem_sharedInteriorPairFirstClassOuterUThirdComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip40 ∉
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        u (u + v) (sharedInteriorPairFirstClassOuterUThirdComponent a b u v hab huv) := by
  exact not_mem_component_containing_sip56_of_sharedEdgeRegion_false
    (sip56_mem_sharedInteriorPairFirstClassOuterUThirdComponent hab huv) (by decide)

private theorem sharedInteriorPairFirstClassParametricTaitEdgeColoring_swap_uThird_eq
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv).swapOnKempeComponent
        u (u + v) (sharedInteriorPairFirstClassOuterUThirdComponent a b u v hab huv) =
      sharedInteriorPairFirstClassParametricTaitEdgeColoring a b (u + v) v hab
        (validColorPair_third_left huv) := by
  apply DFunLike.ext
  intro e
  rcases sharedInteriorPairAnnulus_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change sharedInteriorPairFirstClassParametricEdgeColor a b u v sip01 =
        sharedInteriorPairFirstClassParametricEdgeColor a b (u + v) v sip01
      simp
    · exact sip01_not_mem_sharedInteriorPairFirstClassOuterUThirdComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change sharedInteriorPairFirstClassParametricEdgeColor a b u v sip12 =
        sharedInteriorPairFirstClassParametricEdgeColor a b (u + v) v sip12
      simp
    · exact sip12_not_mem_sharedInteriorPairFirstClassOuterUThirdComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change sharedInteriorPairFirstClassParametricEdgeColor a b u v sip23 =
        sharedInteriorPairFirstClassParametricEdgeColor a b (u + v) v sip23
      simp
    · exact sip23_not_mem_sharedInteriorPairFirstClassOuterUThirdComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change sharedInteriorPairFirstClassParametricEdgeColor a b u v sip30 =
        sharedInteriorPairFirstClassParametricEdgeColor a b (u + v) v sip30
      simp
    · exact sip30_not_mem_sharedInteriorPairFirstClassOuterUThirdComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change sharedInteriorPairFirstClassParametricEdgeColor a b u v sip24 =
        sharedInteriorPairFirstClassParametricEdgeColor a b (u + v) v sip24
      simp
    · exact sip24_not_mem_sharedInteriorPairFirstClassOuterUThirdComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change sharedInteriorPairFirstClassParametricEdgeColor a b u v sip40 =
        sharedInteriorPairFirstClassParametricEdgeColor a b (u + v) v sip40
      simp
    · exact sip40_not_mem_sharedInteriorPairFirstClassOuterUThirdComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_mem]
    · change Equiv.swap u (u + v) (sharedInteriorPairFirstClassParametricEdgeColor a b u v sip56) =
        sharedInteriorPairFirstClassParametricEdgeColor a b (u + v) v sip56
      simp
    · exact sip56_mem_sharedInteriorPairFirstClassOuterUThirdComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change sharedInteriorPairFirstClassParametricEdgeColor a b u v sip67 =
        sharedInteriorPairFirstClassParametricEdgeColor a b (u + v) v sip67
      simp
    · exact sip67_not_mem_sharedInteriorPairFirstClassOuterUThirdComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_mem]
    · change Equiv.swap u (u + v) (sharedInteriorPairFirstClassParametricEdgeColor a b u v sip75) =
        sharedInteriorPairFirstClassParametricEdgeColor a b (u + v) v sip75
      simp [add_assoc]
    · exact sip75_mem_sharedInteriorPairFirstClassOuterUThirdComponent hab huv

private theorem sharedInteriorPairFirstClassParametricTaitEdgeColoring_swap_uThird_mem_edgeKempeClosure
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sharedInteriorPairFirstClassParametricTaitEdgeColoring a b (u + v) v hab
        (validColorPair_third_left huv) ∈
      sharedInteriorPairAnnulusGraph.EdgeKempeClosure
        (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv) := by
  rw [← sharedInteriorPairFirstClassParametricTaitEdgeColoring_swap_uThird_eq hab huv]
  exact sharedInteriorPairAnnulusGraph.mem_edgeKempeClosure_of_mem_of_step
    (sharedInteriorPairAnnulusGraph.mem_edgeKempeClosure_self
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv))
    u (u + v) (sharedInteriorPairFirstClassOuterUThirdComponent a b u v hab huv)

private theorem sharedInteriorPairFirstClassParametricTaitEdgeColoring_edgeKempeClosure_eq_swap_ab
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sharedInteriorPairAnnulusGraph.EdgeKempeClosure
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv) =
    sharedInteriorPairAnnulusGraph.EdgeKempeClosure
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring b a u v (validColorPair_symm hab) huv) := by
  apply sharedInteriorPairAnnulusGraph.edgeKempeClosure_eq_of_mem_of_mem
  · exact sharedInteriorPairFirstClassParametricTaitEdgeColoring_swap_ab_mem_edgeKempeClosure hab huv
  · simpa using
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring_swap_ab_mem_edgeKempeClosure
        (a := b) (b := a) (u := u) (v := v) (hab := validColorPair_symm hab) (huv := huv))

private theorem sharedInteriorPairFirstClassParametricTaitEdgeColoring_edgeKempeClosure_eq_swap_aThird
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sharedInteriorPairAnnulusGraph.EdgeKempeClosure
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv) =
    sharedInteriorPairAnnulusGraph.EdgeKempeClosure
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring (a + b) b u v
        (validColorPair_third_left hab) huv) := by
  apply sharedInteriorPairAnnulusGraph.edgeKempeClosure_eq_of_mem_of_mem
  · exact sharedInteriorPairFirstClassParametricTaitEdgeColoring_swap_aThird_mem_edgeKempeClosure hab huv
  · simpa [add_assoc] using
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring_swap_aThird_mem_edgeKempeClosure
        (a := a + b) (b := b) (u := u) (v := v) (hab := validColorPair_third_left hab) (huv := huv))

private theorem sharedInteriorPairFirstClassParametricTaitEdgeColoring_edgeKempeClosure_eq_swap_uv
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sharedInteriorPairAnnulusGraph.EdgeKempeClosure
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv) =
    sharedInteriorPairAnnulusGraph.EdgeKempeClosure
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b v u hab (validColorPair_symm huv)) := by
  apply sharedInteriorPairAnnulusGraph.edgeKempeClosure_eq_of_mem_of_mem
  · exact sharedInteriorPairFirstClassParametricTaitEdgeColoring_swap_uv_mem_edgeKempeClosure hab huv
  · simpa using
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring_swap_uv_mem_edgeKempeClosure
        (a := a) (b := b) (u := v) (v := u) (hab := hab) (huv := validColorPair_symm huv))

private theorem sharedInteriorPairFirstClassParametricTaitEdgeColoring_edgeKempeClosure_eq_swap_uThird
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sharedInteriorPairAnnulusGraph.EdgeKempeClosure
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv) =
    sharedInteriorPairAnnulusGraph.EdgeKempeClosure
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b (u + v) v hab
        (validColorPair_third_left huv)) := by
  apply sharedInteriorPairAnnulusGraph.edgeKempeClosure_eq_of_mem_of_mem
  · exact sharedInteriorPairFirstClassParametricTaitEdgeColoring_swap_uThird_mem_edgeKempeClosure hab huv
  · simpa [add_assoc] using
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring_swap_uThird_mem_edgeKempeClosure
        (a := a) (b := b) (u := u + v) (v := v) (hab := hab) (huv := validColorPair_third_left huv))

private theorem sharedInteriorPairFirstClassParametricTaitEdgeColoring_coreClosure_eq_base
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sharedInteriorPairAnnulusGraph.EdgeKempeClosure
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv) =
    sharedInteriorPairAnnulusGraph.EdgeKempeClosure
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring red blue u v validColorPair_red_blue huv) := by
  let K := fun x y (hxy : ValidColorPair x y) =>
    sharedInteriorPairAnnulusGraph.EdgeKempeClosure
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring x y u v hxy huv)
  exact closure_eq_base_of_swap_ab_swap_aThird K
    (fun hxy => sharedInteriorPairFirstClassParametricTaitEdgeColoring_edgeKempeClosure_eq_swap_ab hxy huv)
    (fun hxy => sharedInteriorPairFirstClassParametricTaitEdgeColoring_edgeKempeClosure_eq_swap_aThird hxy huv)
    hab

private theorem sharedInteriorPairFirstClassParametricTaitEdgeColoring_outerClosure_eq_base
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sharedInteriorPairAnnulusGraph.EdgeKempeClosure
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv) =
    sharedInteriorPairAnnulusGraph.EdgeKempeClosure
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b red blue hab validColorPair_red_blue) := by
  let K := fun x y (hxy : ValidColorPair x y) =>
    sharedInteriorPairAnnulusGraph.EdgeKempeClosure
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b x y hab hxy)
  exact closure_eq_base_of_swap_ab_swap_aThird K
    (fun hxy => sharedInteriorPairFirstClassParametricTaitEdgeColoring_edgeKempeClosure_eq_swap_uv hab hxy)
    (fun hxy => sharedInteriorPairFirstClassParametricTaitEdgeColoring_edgeKempeClosure_eq_swap_uThird hab hxy)
    huv

private theorem sharedInteriorPairFirstClassParametricTaitEdgeColoring_edgeKempeClosure_eq_explicit
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sharedInteriorPairAnnulusGraph.EdgeKempeClosure
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv) =
    sharedInteriorPairAnnulusGraph.EdgeKempeClosure sharedInteriorPairTaitEdgeColoring := by
  calc
    sharedInteriorPairAnnulusGraph.EdgeKempeClosure
        (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv) =
      sharedInteriorPairAnnulusGraph.EdgeKempeClosure
        (sharedInteriorPairFirstClassParametricTaitEdgeColoring red blue u v validColorPair_red_blue huv) :=
      sharedInteriorPairFirstClassParametricTaitEdgeColoring_coreClosure_eq_base hab huv
    _ =
      sharedInteriorPairAnnulusGraph.EdgeKempeClosure
        (sharedInteriorPairFirstClassParametricTaitEdgeColoring red blue red blue
          validColorPair_red_blue validColorPair_red_blue) :=
      sharedInteriorPairFirstClassParametricTaitEdgeColoring_outerClosure_eq_base
        validColorPair_red_blue huv
    _ = sharedInteriorPairAnnulusGraph.EdgeKempeClosure sharedInteriorPairTaitEdgeColoring := by
      rw [sharedInteriorPairTaitEdgeColoring_eq_firstClassParametric]

private theorem sip01_mem_secondClass_bicoloredSet_ab
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip01 ∈
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv).bicoloredSet a b := by
  left
  change sharedInteriorPairSecondClassParametricEdgeColor a b u v sip01 = a
  simp

private noncomputable def sharedInteriorPairSecondClassABComponent
    (a b u v : Color) (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    ((sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv).bicoloredSubgraph
      a b).ConnectedComponent :=
  let C := sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv
  (C.bicoloredSubgraph a b).connectedComponentMk
    ⟨sip01, sip01_mem_secondClass_bicoloredSet_ab hab huv⟩

private theorem sip01_mem_sharedInteriorPairSecondClassABComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip01 ∈
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        a b (sharedInteriorPairSecondClassABComponent a b u v hab huv) := by
  let C := sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv
  exact C.mem_kempeComponentSet_self (sip01_mem_secondClass_bicoloredSet_ab hab huv)

private theorem sip12_mem_sharedInteriorPairSecondClassABComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip12 ∈
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        a b (sharedInteriorPairSecondClassABComponent a b u v hab huv) := by
  let C := sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv
  exact C.mem_kempeComponentSet_of_adj
    (sip01_mem_sharedInteriorPairSecondClassABComponent hab huv) sip01_adj_sip12 (by
      right
      change sharedInteriorPairSecondClassParametricEdgeColor a b u v sip12 = b
      simp)

private theorem sip23_mem_sharedInteriorPairSecondClassABComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip23 ∈
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        a b (sharedInteriorPairSecondClassABComponent a b u v hab huv) := by
  let C := sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv
  exact C.mem_kempeComponentSet_of_adj
    (sip12_mem_sharedInteriorPairSecondClassABComponent hab huv) sip12_adj_sip23 (by
      left
      change sharedInteriorPairSecondClassParametricEdgeColor a b u v sip23 = a
      simp)

private theorem sip40_mem_sharedInteriorPairSecondClassABComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip40 ∈
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        a b (sharedInteriorPairSecondClassABComponent a b u v hab huv) := by
  let C := sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv
  exact C.mem_kempeComponentSet_of_adj
    (sip01_mem_sharedInteriorPairSecondClassABComponent hab huv) sip01_adj_sip40 (by
      right
      change sharedInteriorPairSecondClassParametricEdgeColor a b u v sip40 = b
      simp)

private theorem sip30_not_mem_sharedInteriorPairSecondClassABComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip30 ∉
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        a b (sharedInteriorPairSecondClassABComponent a b u v hab huv) := by
  rcases third_color_properties hab.1 hab.2.1 hab.2.2 with ⟨_, haba, habb⟩
  let C := sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv
  exact not_mem_kempeComponentSet_of_ne_left_ne_right
    (C := C) (K := sharedInteriorPairSecondClassABComponent a b u v hab huv)
    (e := sip30)
    (by
      change sharedInteriorPairSecondClassParametricEdgeColor a b u v sip30 ≠ a
      simpa using haba)
    (by
      change sharedInteriorPairSecondClassParametricEdgeColor a b u v sip30 ≠ b
      simpa using habb)

private theorem sip24_not_mem_sharedInteriorPairSecondClassABComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip24 ∉
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        a b (sharedInteriorPairSecondClassABComponent a b u v hab huv) := by
  rcases third_color_properties hab.1 hab.2.1 hab.2.2 with ⟨_, haba, habb⟩
  let C := sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv
  exact not_mem_kempeComponentSet_of_ne_left_ne_right
    (C := C) (K := sharedInteriorPairSecondClassABComponent a b u v hab huv)
    (e := sip24)
    (by
      change sharedInteriorPairSecondClassParametricEdgeColor a b u v sip24 ≠ a
      simpa using haba)
    (by
      change sharedInteriorPairSecondClassParametricEdgeColor a b u v sip24 ≠ b
      simpa using habb)

private theorem sip56_not_mem_sharedInteriorPairSecondClassABComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip56 ∉
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        a b (sharedInteriorPairSecondClassABComponent a b u v hab huv) := by
  exact not_mem_component_containing_sip01_of_sharedEdgeRegion_true
    (sip01_mem_sharedInteriorPairSecondClassABComponent hab huv) (by decide)

private theorem sip67_not_mem_sharedInteriorPairSecondClassABComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip67 ∉
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        a b (sharedInteriorPairSecondClassABComponent a b u v hab huv) := by
  exact not_mem_component_containing_sip01_of_sharedEdgeRegion_true
    (sip01_mem_sharedInteriorPairSecondClassABComponent hab huv) (by decide)

private theorem sip75_not_mem_sharedInteriorPairSecondClassABComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip75 ∉
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        a b (sharedInteriorPairSecondClassABComponent a b u v hab huv) := by
  exact not_mem_component_containing_sip01_of_sharedEdgeRegion_true
    (sip01_mem_sharedInteriorPairSecondClassABComponent hab huv) (by decide)

private theorem sharedInteriorPairSecondClassParametricTaitEdgeColoring_swap_ab_eq
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv).swapOnKempeComponent
        a b (sharedInteriorPairSecondClassABComponent a b u v hab huv) =
      sharedInteriorPairSecondClassParametricTaitEdgeColoring b a u v
        (validColorPair_symm hab) huv := by
  apply DFunLike.ext
  intro e
  rcases sharedInteriorPairAnnulus_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [Coloring.swapOnKempeComponent_apply_of_mem]
    · change Equiv.swap a b (sharedInteriorPairSecondClassParametricEdgeColor a b u v sip01) =
        sharedInteriorPairSecondClassParametricEdgeColor b a u v sip01
      simp
    · exact sip01_mem_sharedInteriorPairSecondClassABComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_mem]
    · change Equiv.swap a b (sharedInteriorPairSecondClassParametricEdgeColor a b u v sip12) =
        sharedInteriorPairSecondClassParametricEdgeColor b a u v sip12
      simp
    · exact sip12_mem_sharedInteriorPairSecondClassABComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_mem]
    · change Equiv.swap a b (sharedInteriorPairSecondClassParametricEdgeColor a b u v sip23) =
        sharedInteriorPairSecondClassParametricEdgeColor b a u v sip23
      simp
    · exact sip23_mem_sharedInteriorPairSecondClassABComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change sharedInteriorPairSecondClassParametricEdgeColor a b u v sip30 =
        sharedInteriorPairSecondClassParametricEdgeColor b a u v sip30
      simp [add_comm]
    · exact sip30_not_mem_sharedInteriorPairSecondClassABComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change sharedInteriorPairSecondClassParametricEdgeColor a b u v sip24 =
        sharedInteriorPairSecondClassParametricEdgeColor b a u v sip24
      simp [add_comm]
    · exact sip24_not_mem_sharedInteriorPairSecondClassABComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_mem]
    · change Equiv.swap a b (sharedInteriorPairSecondClassParametricEdgeColor a b u v sip40) =
        sharedInteriorPairSecondClassParametricEdgeColor b a u v sip40
      simp
    · exact sip40_mem_sharedInteriorPairSecondClassABComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change sharedInteriorPairSecondClassParametricEdgeColor a b u v sip56 =
        sharedInteriorPairSecondClassParametricEdgeColor b a u v sip56
      simp
    · exact sip56_not_mem_sharedInteriorPairSecondClassABComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change sharedInteriorPairSecondClassParametricEdgeColor a b u v sip67 =
        sharedInteriorPairSecondClassParametricEdgeColor b a u v sip67
      simp
    · exact sip67_not_mem_sharedInteriorPairSecondClassABComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change sharedInteriorPairSecondClassParametricEdgeColor a b u v sip75 =
        sharedInteriorPairSecondClassParametricEdgeColor b a u v sip75
      simp
    · exact sip75_not_mem_sharedInteriorPairSecondClassABComponent hab huv

private theorem sharedInteriorPairSecondClassParametricTaitEdgeColoring_swap_ab_mem_edgeKempeClosure
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sharedInteriorPairSecondClassParametricTaitEdgeColoring b a u v
        (validColorPair_symm hab) huv ∈
      sharedInteriorPairAnnulusGraph.EdgeKempeClosure
        (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv) := by
  rw [← sharedInteriorPairSecondClassParametricTaitEdgeColoring_swap_ab_eq hab huv]
  exact sharedInteriorPairAnnulusGraph.mem_edgeKempeClosure_of_mem_of_step
    (sharedInteriorPairAnnulusGraph.mem_edgeKempeClosure_self
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv))
    a b (sharedInteriorPairSecondClassABComponent a b u v hab huv)

private theorem sip01_mem_secondClass_bicoloredSet_aThird
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip01 ∈
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv).bicoloredSet
        a (a + b) := by
  left
  change sharedInteriorPairSecondClassParametricEdgeColor a b u v sip01 = a
  simp

private noncomputable def sharedInteriorPairSecondClassAThirdComponent
    (a b u v : Color) (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    ((sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv).bicoloredSubgraph
      a (a + b)).ConnectedComponent :=
  let C := sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv
  (C.bicoloredSubgraph a (a + b)).connectedComponentMk
    ⟨sip01, sip01_mem_secondClass_bicoloredSet_aThird hab huv⟩

private theorem sip01_mem_sharedInteriorPairSecondClassAThirdComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip01 ∈
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        a (a + b) (sharedInteriorPairSecondClassAThirdComponent a b u v hab huv) := by
  let C := sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv
  exact C.mem_kempeComponentSet_self (sip01_mem_secondClass_bicoloredSet_aThird hab huv)

private theorem sip30_mem_sharedInteriorPairSecondClassAThirdComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip30 ∈
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        a (a + b) (sharedInteriorPairSecondClassAThirdComponent a b u v hab huv) := by
  let C := sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv
  exact C.mem_kempeComponentSet_of_adj
    (sip01_mem_sharedInteriorPairSecondClassAThirdComponent hab huv) sip01_adj_sip30 (by
      right
      change sharedInteriorPairSecondClassParametricEdgeColor a b u v sip30 = a + b
      simp)

private theorem sip23_mem_sharedInteriorPairSecondClassAThirdComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip23 ∈
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        a (a + b) (sharedInteriorPairSecondClassAThirdComponent a b u v hab huv) := by
  let C := sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv
  exact C.mem_kempeComponentSet_of_adj
    (sip30_mem_sharedInteriorPairSecondClassAThirdComponent hab huv) sip23_adj_sip30.symm (by
      left
      change sharedInteriorPairSecondClassParametricEdgeColor a b u v sip23 = a
      simp)

private theorem sip24_mem_sharedInteriorPairSecondClassAThirdComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip24 ∈
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        a (a + b) (sharedInteriorPairSecondClassAThirdComponent a b u v hab huv) := by
  let C := sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv
  exact C.mem_kempeComponentSet_of_adj
    (sip23_mem_sharedInteriorPairSecondClassAThirdComponent hab huv) sip23_adj_sip24 (by
      right
      change sharedInteriorPairSecondClassParametricEdgeColor a b u v sip24 = a + b
      simp)

private theorem sip12_not_mem_sharedInteriorPairSecondClassAThirdComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip12 ∉
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        a (a + b) (sharedInteriorPairSecondClassAThirdComponent a b u v hab huv) := by
  rcases third_color_properties hab.1 hab.2.1 hab.2.2 with ⟨_, _, habb⟩
  let C := sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv
  exact not_mem_kempeComponentSet_of_ne_left_ne_right
    (C := C) (K := sharedInteriorPairSecondClassAThirdComponent a b u v hab huv)
    (e := sip12)
    (by
      change sharedInteriorPairSecondClassParametricEdgeColor a b u v sip12 ≠ a
      simpa using hab.2.2.symm)
    (by
      change sharedInteriorPairSecondClassParametricEdgeColor a b u v sip12 ≠ a + b
      simpa using habb.symm)

private theorem sip40_not_mem_sharedInteriorPairSecondClassAThirdComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip40 ∉
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        a (a + b) (sharedInteriorPairSecondClassAThirdComponent a b u v hab huv) := by
  rcases third_color_properties hab.1 hab.2.1 hab.2.2 with ⟨_, _, habb⟩
  let C := sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv
  exact not_mem_kempeComponentSet_of_ne_left_ne_right
    (C := C) (K := sharedInteriorPairSecondClassAThirdComponent a b u v hab huv)
    (e := sip40)
    (by
      change sharedInteriorPairSecondClassParametricEdgeColor a b u v sip40 ≠ a
      simpa using hab.2.2.symm)
    (by
      change sharedInteriorPairSecondClassParametricEdgeColor a b u v sip40 ≠ a + b
      simpa using habb.symm)

private theorem sip56_not_mem_sharedInteriorPairSecondClassAThirdComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip56 ∉
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        a (a + b) (sharedInteriorPairSecondClassAThirdComponent a b u v hab huv) := by
  exact not_mem_component_containing_sip01_of_sharedEdgeRegion_true
    (sip01_mem_sharedInteriorPairSecondClassAThirdComponent hab huv) (by decide)

private theorem sip67_not_mem_sharedInteriorPairSecondClassAThirdComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip67 ∉
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        a (a + b) (sharedInteriorPairSecondClassAThirdComponent a b u v hab huv) := by
  exact not_mem_component_containing_sip01_of_sharedEdgeRegion_true
    (sip01_mem_sharedInteriorPairSecondClassAThirdComponent hab huv) (by decide)

private theorem sip75_not_mem_sharedInteriorPairSecondClassAThirdComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip75 ∉
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        a (a + b) (sharedInteriorPairSecondClassAThirdComponent a b u v hab huv) := by
  exact not_mem_component_containing_sip01_of_sharedEdgeRegion_true
    (sip01_mem_sharedInteriorPairSecondClassAThirdComponent hab huv) (by decide)

private theorem sharedInteriorPairSecondClassParametricTaitEdgeColoring_swap_aThird_eq
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv).swapOnKempeComponent
        a (a + b) (sharedInteriorPairSecondClassAThirdComponent a b u v hab huv) =
      sharedInteriorPairSecondClassParametricTaitEdgeColoring (a + b) b u v
        (validColorPair_third_left hab) huv := by
  apply DFunLike.ext
  intro e
  rcases sharedInteriorPairAnnulus_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [Coloring.swapOnKempeComponent_apply_of_mem]
    · change Equiv.swap a (a + b) (sharedInteriorPairSecondClassParametricEdgeColor a b u v sip01) =
        sharedInteriorPairSecondClassParametricEdgeColor (a + b) b u v sip01
      simp
    · exact sip01_mem_sharedInteriorPairSecondClassAThirdComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change sharedInteriorPairSecondClassParametricEdgeColor a b u v sip12 =
        sharedInteriorPairSecondClassParametricEdgeColor (a + b) b u v sip12
      simp
    · exact sip12_not_mem_sharedInteriorPairSecondClassAThirdComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_mem]
    · change Equiv.swap a (a + b) (sharedInteriorPairSecondClassParametricEdgeColor a b u v sip23) =
        sharedInteriorPairSecondClassParametricEdgeColor (a + b) b u v sip23
      simp
    · exact sip23_mem_sharedInteriorPairSecondClassAThirdComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_mem]
    · change Equiv.swap a (a + b) (sharedInteriorPairSecondClassParametricEdgeColor a b u v sip30) =
        sharedInteriorPairSecondClassParametricEdgeColor (a + b) b u v sip30
      simp [add_assoc]
    · exact sip30_mem_sharedInteriorPairSecondClassAThirdComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_mem]
    · change Equiv.swap a (a + b) (sharedInteriorPairSecondClassParametricEdgeColor a b u v sip24) =
        sharedInteriorPairSecondClassParametricEdgeColor (a + b) b u v sip24
      simp [add_assoc]
    · exact sip24_mem_sharedInteriorPairSecondClassAThirdComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change sharedInteriorPairSecondClassParametricEdgeColor a b u v sip40 =
        sharedInteriorPairSecondClassParametricEdgeColor (a + b) b u v sip40
      simp
    · exact sip40_not_mem_sharedInteriorPairSecondClassAThirdComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change sharedInteriorPairSecondClassParametricEdgeColor a b u v sip56 =
        sharedInteriorPairSecondClassParametricEdgeColor (a + b) b u v sip56
      simp
    · exact sip56_not_mem_sharedInteriorPairSecondClassAThirdComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change sharedInteriorPairSecondClassParametricEdgeColor a b u v sip67 =
        sharedInteriorPairSecondClassParametricEdgeColor (a + b) b u v sip67
      simp
    · exact sip67_not_mem_sharedInteriorPairSecondClassAThirdComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change sharedInteriorPairSecondClassParametricEdgeColor a b u v sip75 =
        sharedInteriorPairSecondClassParametricEdgeColor (a + b) b u v sip75
      simp
    · exact sip75_not_mem_sharedInteriorPairSecondClassAThirdComponent hab huv

private theorem sharedInteriorPairSecondClassParametricTaitEdgeColoring_swap_aThird_mem_edgeKempeClosure
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sharedInteriorPairSecondClassParametricTaitEdgeColoring (a + b) b u v
        (validColorPair_third_left hab) huv ∈
      sharedInteriorPairAnnulusGraph.EdgeKempeClosure
        (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv) := by
  rw [← sharedInteriorPairSecondClassParametricTaitEdgeColoring_swap_aThird_eq hab huv]
  exact sharedInteriorPairAnnulusGraph.mem_edgeKempeClosure_of_mem_of_step
    (sharedInteriorPairAnnulusGraph.mem_edgeKempeClosure_self
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv))
    a (a + b) (sharedInteriorPairSecondClassAThirdComponent a b u v hab huv)

private theorem sip56_mem_secondClass_bicoloredSet_uv
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip56 ∈
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv).bicoloredSet u v := by
  left
  change sharedInteriorPairSecondClassParametricEdgeColor a b u v sip56 = u
  simp

private noncomputable def sharedInteriorPairSecondClassOuterUVComponent
    (a b u v : Color) (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    ((sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv).bicoloredSubgraph
      u v).ConnectedComponent :=
  let C := sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv
  (C.bicoloredSubgraph u v).connectedComponentMk
    ⟨sip56, sip56_mem_secondClass_bicoloredSet_uv hab huv⟩

private theorem sip56_mem_sharedInteriorPairSecondClassOuterUVComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip56 ∈
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        u v (sharedInteriorPairSecondClassOuterUVComponent a b u v hab huv) := by
  let C := sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv
  exact C.mem_kempeComponentSet_self (sip56_mem_secondClass_bicoloredSet_uv hab huv)

private theorem sip67_mem_sharedInteriorPairSecondClassOuterUVComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip67 ∈
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        u v (sharedInteriorPairSecondClassOuterUVComponent a b u v hab huv) := by
  let C := sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv
  exact C.mem_kempeComponentSet_of_adj
    (sip56_mem_sharedInteriorPairSecondClassOuterUVComponent hab huv) sip56_adj_sip67 (by
      right
      change sharedInteriorPairSecondClassParametricEdgeColor a b u v sip67 = v
      simp)

private theorem sip75_not_mem_sharedInteriorPairSecondClassOuterUVComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip75 ∉
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        u v (sharedInteriorPairSecondClassOuterUVComponent a b u v hab huv) := by
  rcases third_color_properties huv.1 huv.2.1 huv.2.2 with ⟨_, huva, huvb⟩
  let C := sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv
  exact not_mem_kempeComponentSet_of_ne_left_ne_right
    (C := C) (K := sharedInteriorPairSecondClassOuterUVComponent a b u v hab huv)
    (e := sip75)
    (by
      change sharedInteriorPairSecondClassParametricEdgeColor a b u v sip75 ≠ u
      simpa using huva)
    (by
      change sharedInteriorPairSecondClassParametricEdgeColor a b u v sip75 ≠ v
      simpa using huvb)

private theorem sip01_not_mem_sharedInteriorPairSecondClassOuterUVComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip01 ∉
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        u v (sharedInteriorPairSecondClassOuterUVComponent a b u v hab huv) := by
  exact not_mem_component_containing_sip56_of_sharedEdgeRegion_false
    (sip56_mem_sharedInteriorPairSecondClassOuterUVComponent hab huv) (by decide)

private theorem sip12_not_mem_sharedInteriorPairSecondClassOuterUVComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip12 ∉
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        u v (sharedInteriorPairSecondClassOuterUVComponent a b u v hab huv) := by
  exact not_mem_component_containing_sip56_of_sharedEdgeRegion_false
    (sip56_mem_sharedInteriorPairSecondClassOuterUVComponent hab huv) (by decide)

private theorem sip23_not_mem_sharedInteriorPairSecondClassOuterUVComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip23 ∉
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        u v (sharedInteriorPairSecondClassOuterUVComponent a b u v hab huv) := by
  exact not_mem_component_containing_sip56_of_sharedEdgeRegion_false
    (sip56_mem_sharedInteriorPairSecondClassOuterUVComponent hab huv) (by decide)

private theorem sip30_not_mem_sharedInteriorPairSecondClassOuterUVComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip30 ∉
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        u v (sharedInteriorPairSecondClassOuterUVComponent a b u v hab huv) := by
  exact not_mem_component_containing_sip56_of_sharedEdgeRegion_false
    (sip56_mem_sharedInteriorPairSecondClassOuterUVComponent hab huv) (by decide)

private theorem sip24_not_mem_sharedInteriorPairSecondClassOuterUVComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip24 ∉
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        u v (sharedInteriorPairSecondClassOuterUVComponent a b u v hab huv) := by
  exact not_mem_component_containing_sip56_of_sharedEdgeRegion_false
    (sip56_mem_sharedInteriorPairSecondClassOuterUVComponent hab huv) (by decide)

private theorem sip40_not_mem_sharedInteriorPairSecondClassOuterUVComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip40 ∉
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        u v (sharedInteriorPairSecondClassOuterUVComponent a b u v hab huv) := by
  exact not_mem_component_containing_sip56_of_sharedEdgeRegion_false
    (sip56_mem_sharedInteriorPairSecondClassOuterUVComponent hab huv) (by decide)

private theorem sharedInteriorPairSecondClassParametricTaitEdgeColoring_swap_uv_eq
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv).swapOnKempeComponent
        u v (sharedInteriorPairSecondClassOuterUVComponent a b u v hab huv) =
      sharedInteriorPairSecondClassParametricTaitEdgeColoring a b v u hab
        (validColorPair_symm huv) := by
  apply DFunLike.ext
  intro e
  rcases sharedInteriorPairAnnulus_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change sharedInteriorPairSecondClassParametricEdgeColor a b u v sip01 =
        sharedInteriorPairSecondClassParametricEdgeColor a b v u sip01
      simp
    · exact sip01_not_mem_sharedInteriorPairSecondClassOuterUVComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change sharedInteriorPairSecondClassParametricEdgeColor a b u v sip12 =
        sharedInteriorPairSecondClassParametricEdgeColor a b v u sip12
      simp
    · exact sip12_not_mem_sharedInteriorPairSecondClassOuterUVComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change sharedInteriorPairSecondClassParametricEdgeColor a b u v sip23 =
        sharedInteriorPairSecondClassParametricEdgeColor a b v u sip23
      simp
    · exact sip23_not_mem_sharedInteriorPairSecondClassOuterUVComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change sharedInteriorPairSecondClassParametricEdgeColor a b u v sip30 =
        sharedInteriorPairSecondClassParametricEdgeColor a b v u sip30
      simp
    · exact sip30_not_mem_sharedInteriorPairSecondClassOuterUVComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change sharedInteriorPairSecondClassParametricEdgeColor a b u v sip24 =
        sharedInteriorPairSecondClassParametricEdgeColor a b v u sip24
      simp
    · exact sip24_not_mem_sharedInteriorPairSecondClassOuterUVComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change sharedInteriorPairSecondClassParametricEdgeColor a b u v sip40 =
        sharedInteriorPairSecondClassParametricEdgeColor a b v u sip40
      simp
    · exact sip40_not_mem_sharedInteriorPairSecondClassOuterUVComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_mem]
    · change Equiv.swap u v (sharedInteriorPairSecondClassParametricEdgeColor a b u v sip56) =
        sharedInteriorPairSecondClassParametricEdgeColor a b v u sip56
      simp
    · exact sip56_mem_sharedInteriorPairSecondClassOuterUVComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_mem]
    · change Equiv.swap u v (sharedInteriorPairSecondClassParametricEdgeColor a b u v sip67) =
        sharedInteriorPairSecondClassParametricEdgeColor a b v u sip67
      simp
    · exact sip67_mem_sharedInteriorPairSecondClassOuterUVComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change sharedInteriorPairSecondClassParametricEdgeColor a b u v sip75 =
        sharedInteriorPairSecondClassParametricEdgeColor a b v u sip75
      simp [add_comm]
    · exact sip75_not_mem_sharedInteriorPairSecondClassOuterUVComponent hab huv

private theorem sharedInteriorPairSecondClassParametricTaitEdgeColoring_swap_uv_mem_edgeKempeClosure
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sharedInteriorPairSecondClassParametricTaitEdgeColoring a b v u hab
        (validColorPair_symm huv) ∈
      sharedInteriorPairAnnulusGraph.EdgeKempeClosure
        (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv) := by
  rw [← sharedInteriorPairSecondClassParametricTaitEdgeColoring_swap_uv_eq hab huv]
  exact sharedInteriorPairAnnulusGraph.mem_edgeKempeClosure_of_mem_of_step
    (sharedInteriorPairAnnulusGraph.mem_edgeKempeClosure_self
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv))
    u v (sharedInteriorPairSecondClassOuterUVComponent a b u v hab huv)

private theorem sip56_mem_secondClass_bicoloredSet_uThird
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip56 ∈
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv).bicoloredSet
        u (u + v) := by
  left
  change sharedInteriorPairSecondClassParametricEdgeColor a b u v sip56 = u
  simp

private noncomputable def sharedInteriorPairSecondClassOuterUThirdComponent
    (a b u v : Color) (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    ((sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv).bicoloredSubgraph
      u (u + v)).ConnectedComponent :=
  let C := sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv
  (C.bicoloredSubgraph u (u + v)).connectedComponentMk
    ⟨sip56, sip56_mem_secondClass_bicoloredSet_uThird hab huv⟩

private theorem sip56_mem_sharedInteriorPairSecondClassOuterUThirdComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip56 ∈
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        u (u + v) (sharedInteriorPairSecondClassOuterUThirdComponent a b u v hab huv) := by
  let C := sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv
  exact C.mem_kempeComponentSet_self (sip56_mem_secondClass_bicoloredSet_uThird hab huv)

private theorem sip75_mem_sharedInteriorPairSecondClassOuterUThirdComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip75 ∈
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        u (u + v) (sharedInteriorPairSecondClassOuterUThirdComponent a b u v hab huv) := by
  let C := sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv
  exact C.mem_kempeComponentSet_of_adj
    (sip56_mem_sharedInteriorPairSecondClassOuterUThirdComponent hab huv) sip56_adj_sip75 (by
      right
      change sharedInteriorPairSecondClassParametricEdgeColor a b u v sip75 = u + v
      simp)

private theorem sip67_not_mem_sharedInteriorPairSecondClassOuterUThirdComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip67 ∉
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        u (u + v) (sharedInteriorPairSecondClassOuterUThirdComponent a b u v hab huv) := by
  rcases third_color_properties huv.1 huv.2.1 huv.2.2 with ⟨_, _, huvb⟩
  let C := sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv
  exact not_mem_kempeComponentSet_of_ne_left_ne_right
    (C := C) (K := sharedInteriorPairSecondClassOuterUThirdComponent a b u v hab huv)
    (e := sip67)
    (by
      change sharedInteriorPairSecondClassParametricEdgeColor a b u v sip67 ≠ u
      simpa using huv.2.2.symm)
    (by
      change sharedInteriorPairSecondClassParametricEdgeColor a b u v sip67 ≠ u + v
      simpa using huvb.symm)

private theorem sip01_not_mem_sharedInteriorPairSecondClassOuterUThirdComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip01 ∉
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        u (u + v) (sharedInteriorPairSecondClassOuterUThirdComponent a b u v hab huv) := by
  exact not_mem_component_containing_sip56_of_sharedEdgeRegion_false
    (sip56_mem_sharedInteriorPairSecondClassOuterUThirdComponent hab huv) (by decide)

private theorem sip12_not_mem_sharedInteriorPairSecondClassOuterUThirdComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip12 ∉
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        u (u + v) (sharedInteriorPairSecondClassOuterUThirdComponent a b u v hab huv) := by
  exact not_mem_component_containing_sip56_of_sharedEdgeRegion_false
    (sip56_mem_sharedInteriorPairSecondClassOuterUThirdComponent hab huv) (by decide)

private theorem sip23_not_mem_sharedInteriorPairSecondClassOuterUThirdComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip23 ∉
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        u (u + v) (sharedInteriorPairSecondClassOuterUThirdComponent a b u v hab huv) := by
  exact not_mem_component_containing_sip56_of_sharedEdgeRegion_false
    (sip56_mem_sharedInteriorPairSecondClassOuterUThirdComponent hab huv) (by decide)

private theorem sip30_not_mem_sharedInteriorPairSecondClassOuterUThirdComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip30 ∉
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        u (u + v) (sharedInteriorPairSecondClassOuterUThirdComponent a b u v hab huv) := by
  exact not_mem_component_containing_sip56_of_sharedEdgeRegion_false
    (sip56_mem_sharedInteriorPairSecondClassOuterUThirdComponent hab huv) (by decide)

private theorem sip24_not_mem_sharedInteriorPairSecondClassOuterUThirdComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip24 ∉
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        u (u + v) (sharedInteriorPairSecondClassOuterUThirdComponent a b u v hab huv) := by
  exact not_mem_component_containing_sip56_of_sharedEdgeRegion_false
    (sip56_mem_sharedInteriorPairSecondClassOuterUThirdComponent hab huv) (by decide)

private theorem sip40_not_mem_sharedInteriorPairSecondClassOuterUThirdComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sip40 ∉
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        u (u + v) (sharedInteriorPairSecondClassOuterUThirdComponent a b u v hab huv) := by
  exact not_mem_component_containing_sip56_of_sharedEdgeRegion_false
    (sip56_mem_sharedInteriorPairSecondClassOuterUThirdComponent hab huv) (by decide)

private theorem sharedInteriorPairSecondClassParametricTaitEdgeColoring_swap_uThird_eq
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv).swapOnKempeComponent
        u (u + v) (sharedInteriorPairSecondClassOuterUThirdComponent a b u v hab huv) =
      sharedInteriorPairSecondClassParametricTaitEdgeColoring a b (u + v) v hab
        (validColorPair_third_left huv) := by
  apply DFunLike.ext
  intro e
  rcases sharedInteriorPairAnnulus_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change sharedInteriorPairSecondClassParametricEdgeColor a b u v sip01 =
        sharedInteriorPairSecondClassParametricEdgeColor a b (u + v) v sip01
      simp
    · exact sip01_not_mem_sharedInteriorPairSecondClassOuterUThirdComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change sharedInteriorPairSecondClassParametricEdgeColor a b u v sip12 =
        sharedInteriorPairSecondClassParametricEdgeColor a b (u + v) v sip12
      simp
    · exact sip12_not_mem_sharedInteriorPairSecondClassOuterUThirdComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change sharedInteriorPairSecondClassParametricEdgeColor a b u v sip23 =
        sharedInteriorPairSecondClassParametricEdgeColor a b (u + v) v sip23
      simp
    · exact sip23_not_mem_sharedInteriorPairSecondClassOuterUThirdComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change sharedInteriorPairSecondClassParametricEdgeColor a b u v sip30 =
        sharedInteriorPairSecondClassParametricEdgeColor a b (u + v) v sip30
      simp
    · exact sip30_not_mem_sharedInteriorPairSecondClassOuterUThirdComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change sharedInteriorPairSecondClassParametricEdgeColor a b u v sip24 =
        sharedInteriorPairSecondClassParametricEdgeColor a b (u + v) v sip24
      simp
    · exact sip24_not_mem_sharedInteriorPairSecondClassOuterUThirdComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change sharedInteriorPairSecondClassParametricEdgeColor a b u v sip40 =
        sharedInteriorPairSecondClassParametricEdgeColor a b (u + v) v sip40
      simp
    · exact sip40_not_mem_sharedInteriorPairSecondClassOuterUThirdComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_mem]
    · change Equiv.swap u (u + v) (sharedInteriorPairSecondClassParametricEdgeColor a b u v sip56) =
        sharedInteriorPairSecondClassParametricEdgeColor a b (u + v) v sip56
      simp
    · exact sip56_mem_sharedInteriorPairSecondClassOuterUThirdComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change sharedInteriorPairSecondClassParametricEdgeColor a b u v sip67 =
        sharedInteriorPairSecondClassParametricEdgeColor a b (u + v) v sip67
      simp
    · exact sip67_not_mem_sharedInteriorPairSecondClassOuterUThirdComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_mem]
    · change Equiv.swap u (u + v) (sharedInteriorPairSecondClassParametricEdgeColor a b u v sip75) =
        sharedInteriorPairSecondClassParametricEdgeColor a b (u + v) v sip75
      simp [add_assoc]
    · exact sip75_mem_sharedInteriorPairSecondClassOuterUThirdComponent hab huv

private theorem sharedInteriorPairSecondClassParametricTaitEdgeColoring_swap_uThird_mem_edgeKempeClosure
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sharedInteriorPairSecondClassParametricTaitEdgeColoring a b (u + v) v hab
        (validColorPair_third_left huv) ∈
      sharedInteriorPairAnnulusGraph.EdgeKempeClosure
        (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv) := by
  rw [← sharedInteriorPairSecondClassParametricTaitEdgeColoring_swap_uThird_eq hab huv]
  exact sharedInteriorPairAnnulusGraph.mem_edgeKempeClosure_of_mem_of_step
    (sharedInteriorPairAnnulusGraph.mem_edgeKempeClosure_self
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv))
    u (u + v) (sharedInteriorPairSecondClassOuterUThirdComponent a b u v hab huv)

private theorem sharedInteriorPairSecondClassParametricTaitEdgeColoring_edgeKempeClosure_eq_swap_ab
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sharedInteriorPairAnnulusGraph.EdgeKempeClosure
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv) =
    sharedInteriorPairAnnulusGraph.EdgeKempeClosure
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring b a u v (validColorPair_symm hab) huv) := by
  apply sharedInteriorPairAnnulusGraph.edgeKempeClosure_eq_of_mem_of_mem
  · exact sharedInteriorPairSecondClassParametricTaitEdgeColoring_swap_ab_mem_edgeKempeClosure hab huv
  · simpa using
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring_swap_ab_mem_edgeKempeClosure
        (a := b) (b := a) (u := u) (v := v) (hab := validColorPair_symm hab) (huv := huv))

private theorem sharedInteriorPairSecondClassParametricTaitEdgeColoring_edgeKempeClosure_eq_swap_aThird
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sharedInteriorPairAnnulusGraph.EdgeKempeClosure
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv) =
    sharedInteriorPairAnnulusGraph.EdgeKempeClosure
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring (a + b) b u v
        (validColorPair_third_left hab) huv) := by
  apply sharedInteriorPairAnnulusGraph.edgeKempeClosure_eq_of_mem_of_mem
  · exact sharedInteriorPairSecondClassParametricTaitEdgeColoring_swap_aThird_mem_edgeKempeClosure hab huv
  · simpa [add_assoc] using
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring_swap_aThird_mem_edgeKempeClosure
        (a := a + b) (b := b) (u := u) (v := v) (hab := validColorPair_third_left hab) (huv := huv))

private theorem sharedInteriorPairSecondClassParametricTaitEdgeColoring_edgeKempeClosure_eq_swap_uv
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sharedInteriorPairAnnulusGraph.EdgeKempeClosure
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv) =
    sharedInteriorPairAnnulusGraph.EdgeKempeClosure
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b v u hab (validColorPair_symm huv)) := by
  apply sharedInteriorPairAnnulusGraph.edgeKempeClosure_eq_of_mem_of_mem
  · exact sharedInteriorPairSecondClassParametricTaitEdgeColoring_swap_uv_mem_edgeKempeClosure hab huv
  · simpa using
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring_swap_uv_mem_edgeKempeClosure
        (a := a) (b := b) (u := v) (v := u) (hab := hab) (huv := validColorPair_symm huv))

private theorem sharedInteriorPairSecondClassParametricTaitEdgeColoring_edgeKempeClosure_eq_swap_uThird
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sharedInteriorPairAnnulusGraph.EdgeKempeClosure
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv) =
    sharedInteriorPairAnnulusGraph.EdgeKempeClosure
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b (u + v) v hab
        (validColorPair_third_left huv)) := by
  apply sharedInteriorPairAnnulusGraph.edgeKempeClosure_eq_of_mem_of_mem
  · exact sharedInteriorPairSecondClassParametricTaitEdgeColoring_swap_uThird_mem_edgeKempeClosure hab huv
  · simpa [add_assoc] using
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring_swap_uThird_mem_edgeKempeClosure
        (a := a) (b := b) (u := u + v) (v := v) (hab := hab) (huv := validColorPair_third_left huv))

private theorem sharedInteriorPairSecondClassParametricTaitEdgeColoring_coreClosure_eq_base
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sharedInteriorPairAnnulusGraph.EdgeKempeClosure
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv) =
    sharedInteriorPairAnnulusGraph.EdgeKempeClosure
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring red blue u v validColorPair_red_blue huv) := by
  let K := fun x y (hxy : ValidColorPair x y) =>
    sharedInteriorPairAnnulusGraph.EdgeKempeClosure
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring x y u v hxy huv)
  exact closure_eq_base_of_swap_ab_swap_aThird K
    (fun hxy => sharedInteriorPairSecondClassParametricTaitEdgeColoring_edgeKempeClosure_eq_swap_ab hxy huv)
    (fun hxy => sharedInteriorPairSecondClassParametricTaitEdgeColoring_edgeKempeClosure_eq_swap_aThird hxy huv)
    hab

private theorem sharedInteriorPairSecondClassParametricTaitEdgeColoring_outerClosure_eq_base
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sharedInteriorPairAnnulusGraph.EdgeKempeClosure
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv) =
    sharedInteriorPairAnnulusGraph.EdgeKempeClosure
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b red blue hab validColorPair_red_blue) := by
  let K := fun x y (hxy : ValidColorPair x y) =>
    sharedInteriorPairAnnulusGraph.EdgeKempeClosure
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b x y hab hxy)
  exact closure_eq_base_of_swap_ab_swap_aThird K
    (fun hxy => sharedInteriorPairSecondClassParametricTaitEdgeColoring_edgeKempeClosure_eq_swap_uv hab hxy)
    (fun hxy => sharedInteriorPairSecondClassParametricTaitEdgeColoring_edgeKempeClosure_eq_swap_uThird hab hxy)
    huv

private theorem sharedInteriorPairSecondClassParametricTaitEdgeColoring_edgeKempeClosure_eq_explicit
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    sharedInteriorPairAnnulusGraph.EdgeKempeClosure
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv) =
    sharedInteriorPairAnnulusGraph.EdgeKempeClosure sharedInteriorPairSecondClosureTaitEdgeColoring := by
  calc
    sharedInteriorPairAnnulusGraph.EdgeKempeClosure
        (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv) =
      sharedInteriorPairAnnulusGraph.EdgeKempeClosure
        (sharedInteriorPairSecondClassParametricTaitEdgeColoring red blue u v validColorPair_red_blue huv) :=
      sharedInteriorPairSecondClassParametricTaitEdgeColoring_coreClosure_eq_base hab huv
    _ =
      sharedInteriorPairAnnulusGraph.EdgeKempeClosure
        (sharedInteriorPairSecondClassParametricTaitEdgeColoring red blue red blue
          validColorPair_red_blue validColorPair_red_blue) :=
      sharedInteriorPairSecondClassParametricTaitEdgeColoring_outerClosure_eq_base
        validColorPair_red_blue huv
    _ = sharedInteriorPairAnnulusGraph.EdgeKempeClosure sharedInteriorPairSecondClosureTaitEdgeColoring := by
      rw [sharedInteriorPairSecondClosureTaitEdgeColoring_eq_secondClassParametric]

private theorem sharedInteriorPairAnnulusEmbedding_boundaryZeroProjectedGeneratorDetector_for_firstClassParametricTaitColoring
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    BoundaryZeroProjectedGeneratorDetector sharedInteriorPairAnnulusEmbedding
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv) := by
  have hdetExplicit :
      BoundaryZeroProjectedGeneratorDetector sharedInteriorPairAnnulusEmbedding
        sharedInteriorPairTaitEdgeColoring :=
    BoundaryZeroProjectedGeneratorDetector.of_boundaryZeroAnnihilatorTrivial
      sharedInteriorPairAnnulusEmbedding_boundaryZeroAnnihilatorTrivial_for_explicitTaitColoring
  exact BoundaryZeroProjectedGeneratorDetector.of_edgeKempeClosure_eq
    (G := sharedInteriorPairAnnulusGraph) (emb := sharedInteriorPairAnnulusEmbedding)
    (C₀ := sharedInteriorPairTaitEdgeColoring)
    (C₁ := sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv)
    (sharedInteriorPairFirstClassParametricTaitEdgeColoring_edgeKempeClosure_eq_explicit hab huv).symm
    hdetExplicit

private theorem sharedInteriorPairAnnulusEmbedding_boundaryZeroProjectedGeneratorDetector_for_secondClassParametricTaitColoring
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    BoundaryZeroProjectedGeneratorDetector sharedInteriorPairAnnulusEmbedding
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv) := by
  have hdetExplicit :
      BoundaryZeroProjectedGeneratorDetector sharedInteriorPairAnnulusEmbedding
        sharedInteriorPairSecondClosureTaitEdgeColoring :=
    BoundaryZeroProjectedGeneratorDetector.of_boundaryZeroAnnihilatorTrivial
      sharedInteriorPairAnnulusEmbedding_boundaryZeroAnnihilatorTrivial_for_secondClosureTaitColoring
  exact BoundaryZeroProjectedGeneratorDetector.of_edgeKempeClosure_eq
    (G := sharedInteriorPairAnnulusGraph) (emb := sharedInteriorPairAnnulusEmbedding)
    (C₀ := sharedInteriorPairSecondClosureTaitEdgeColoring)
    (C₁ := sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv)
    (sharedInteriorPairSecondClassParametricTaitEdgeColoring_edgeKempeClosure_eq_explicit hab huv).symm
    hdetExplicit

/-- Every first shared closure-class parametric Tait coloring reduces to the explicit
shared endpoint already kernel-checked in `Theorem49SharedInteriorPairEndpointRegression`. -/
theorem sharedInteriorPairAnnulusEmbedding_theorem49BoundaryRootSynthesis_for_firstClassParametricTaitColoring
    [FiniteDimensional F2 (sharedInteriorPairAnnulusGraph.edgeSet → Color)]
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    Theorem49BoundaryRootSynthesis sharedInteriorPairAnnulusEmbedding
      (sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv) := by
  exact Theorem49BoundaryRootSynthesis.of_edgeKempeClosure_eq
    (G := sharedInteriorPairAnnulusGraph) (emb := sharedInteriorPairAnnulusEmbedding)
    (C₀ := sharedInteriorPairTaitEdgeColoring)
    (C₁ := sharedInteriorPairFirstClassParametricTaitEdgeColoring a b u v hab huv)
    (sharedInteriorPairFirstClassParametricTaitEdgeColoring_edgeKempeClosure_eq_explicit hab huv).symm
    sharedInteriorPairAnnulusEmbedding_theorem49BoundaryRootSynthesis_for_explicitTaitColoring

/-- Every second shared closure-class parametric Tait coloring reduces to the second explicit
shared endpoint already kernel-checked in
`Theorem49SharedInteriorPairSecondClosureEndpointRegression`. -/
theorem sharedInteriorPairAnnulusEmbedding_theorem49BoundaryRootSynthesis_for_secondClassParametricTaitColoring
    [FiniteDimensional F2 (sharedInteriorPairAnnulusGraph.edgeSet → Color)]
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    Theorem49BoundaryRootSynthesis sharedInteriorPairAnnulusEmbedding
      (sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv) := by
  exact Theorem49BoundaryRootSynthesis.of_edgeKempeClosure_eq
    (G := sharedInteriorPairAnnulusGraph) (emb := sharedInteriorPairAnnulusEmbedding)
    (C₀ := sharedInteriorPairSecondClosureTaitEdgeColoring)
    (C₁ := sharedInteriorPairSecondClassParametricTaitEdgeColoring a b u v hab huv)
    (sharedInteriorPairSecondClassParametricTaitEdgeColoring_edgeKempeClosure_eq_explicit hab huv).symm
    sharedInteriorPairAnnulusEmbedding_theorem49BoundaryRootSynthesis_for_secondClosureTaitColoring

/-- The endpoint detector certificate also propagates across both shared closure classes:
every Tait coloring of the benchmark annulus has a nontrivial projected-generator pairing
against each nonzero selected-boundary-zero chain. -/
theorem sharedInteriorPairAnnulusEmbedding_boundaryZeroProjectedGeneratorDetector_of_isTait
    (C : sharedInteriorPairAnnulusGraph.EdgeColoring Color)
    (hC : IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C) :
    BoundaryZeroProjectedGeneratorDetector sharedInteriorPairAnnulusEmbedding C := by
  let hab := validColorPair_sharedInteriorPairCore_of_isTait C hC
  let huv := validColorPair_sharedInteriorPairTriangle_of_isTait C hC
  rcases eq_first_or_secondClassParametric_of_isTait C hC with hfirst | hsecond
  · rw [hfirst]
    exact
      sharedInteriorPairAnnulusEmbedding_boundaryZeroProjectedGeneratorDetector_for_firstClassParametricTaitColoring
        hab huv
  · rw [hsecond]
    exact
      sharedInteriorPairAnnulusEmbedding_boundaryZeroProjectedGeneratorDetector_for_secondClassParametricTaitColoring
        hab huv

/-- The shared-interior-pair benchmark full sweep closes: every Tait coloring of the honest
annulus embedding belongs to one of the two kernel-checked closure classes, so theorem 4.9
synthesis holds for all `72` Tait colorings. -/
theorem sharedInteriorPairAnnulusEmbedding_theorem49BoundaryRootSynthesis_of_isTait
    [FiniteDimensional F2 (sharedInteriorPairAnnulusGraph.edgeSet → Color)]
    (C : sharedInteriorPairAnnulusGraph.EdgeColoring Color)
    (hC : IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C) :
    Theorem49BoundaryRootSynthesis sharedInteriorPairAnnulusEmbedding C := by
  let hab := validColorPair_sharedInteriorPairCore_of_isTait C hC
  let huv := validColorPair_sharedInteriorPairTriangle_of_isTait C hC
  rcases eq_first_or_secondClassParametric_of_isTait C hC with hfirst | hsecond
  · rw [hfirst]
    exact sharedInteriorPairAnnulusEmbedding_theorem49BoundaryRootSynthesis_for_firstClassParametricTaitColoring
      hab huv
  · rw [hsecond]
    exact sharedInteriorPairAnnulusEmbedding_theorem49BoundaryRootSynthesis_for_secondClassParametricTaitColoring
      hab huv

end Theorem49SharedInteriorPairFullSweepRegression

end Mettapedia.GraphTheory.FourColor
