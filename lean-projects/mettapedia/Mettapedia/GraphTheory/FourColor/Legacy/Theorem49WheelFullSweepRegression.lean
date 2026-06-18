import Mettapedia.GraphTheory.FourColor.Legacy.Theorem49WheelEndpointRegression
import Mettapedia.GraphTheory.FourColor.Theorem49BoundaryProjectionDetector
import Mettapedia.GraphTheory.FourColor.Theorem49SynthesisClosureInvariance
import Mathlib.Tactic

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open Theorem49PlanarBoundaryAnnulusWheelWitnessRegression
open Theorem49WheelEndpointRegression

namespace Theorem49WheelFullSweepRegression

private theorem eq_third_color_of_ne_zero_ne_ne {a b c : Color}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    c = a + b := by
  rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero a ha with rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero b hb with rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero c hc with rfl | rfl | rfl <;>
    simp at hab hac hbc ⊢

private def wheelWithInnerTriangleParametricEdgeColor
    (a b u v : Color) (e : wheelWithInnerTriangleGraph.edgeSet) : Color :=
  if e = wit01 ∨ e = wit23 then a
  else if e = wit02 ∨ e = wit31 then b
  else if e = wit03 ∨ e = wit12 then a + b
  else if e = wit45 then u
  else if e = wit56 then v
  else u + v

@[simp] private theorem wheelWithInnerTriangleParametricEdgeColor_wit01
    (a b u v : Color) :
    wheelWithInnerTriangleParametricEdgeColor a b u v wit01 = a := by
  simp [wheelWithInnerTriangleParametricEdgeColor]

@[simp] private theorem wheelWithInnerTriangleParametricEdgeColor_wit02
    (a b u v : Color) :
    wheelWithInnerTriangleParametricEdgeColor a b u v wit02 = b := by
  simp [wheelWithInnerTriangleParametricEdgeColor, wheelWithInnerTriangleGraph, wit01, wit02,
    wit03, wit12, wit23, wit31, wit45, wit56]

@[simp] private theorem wheelWithInnerTriangleParametricEdgeColor_wit03
    (a b u v : Color) :
    wheelWithInnerTriangleParametricEdgeColor a b u v wit03 = a + b := by
  simp [wheelWithInnerTriangleParametricEdgeColor, wheelWithInnerTriangleGraph, wit01, wit02,
    wit03, wit12, wit23, wit31, wit45, wit56]

@[simp] private theorem wheelWithInnerTriangleParametricEdgeColor_wit12
    (a b u v : Color) :
    wheelWithInnerTriangleParametricEdgeColor a b u v wit12 = a + b := by
  simp [wheelWithInnerTriangleParametricEdgeColor, wheelWithInnerTriangleGraph, wit01, wit02,
    wit03, wit12, wit23, wit31, wit45, wit56]

@[simp] private theorem wheelWithInnerTriangleParametricEdgeColor_wit23
    (a b u v : Color) :
    wheelWithInnerTriangleParametricEdgeColor a b u v wit23 = a := by
  simp [wheelWithInnerTriangleParametricEdgeColor, wheelWithInnerTriangleGraph, wit01, wit23]

@[simp] private theorem wheelWithInnerTriangleParametricEdgeColor_wit31
    (a b u v : Color) :
    wheelWithInnerTriangleParametricEdgeColor a b u v wit31 = b := by
  simp [wheelWithInnerTriangleParametricEdgeColor, wheelWithInnerTriangleGraph, wit01, wit02,
    wit03, wit12, wit23, wit31, wit45, wit56]

@[simp] private theorem wheelWithInnerTriangleParametricEdgeColor_wit45
    (a b u v : Color) :
    wheelWithInnerTriangleParametricEdgeColor a b u v wit45 = u := by
  simp [wheelWithInnerTriangleParametricEdgeColor, wheelWithInnerTriangleGraph, wit01, wit02,
    wit03, wit12, wit23, wit31, wit45]

@[simp] private theorem wheelWithInnerTriangleParametricEdgeColor_wit56
    (a b u v : Color) :
    wheelWithInnerTriangleParametricEdgeColor a b u v wit56 = v := by
  simp [wheelWithInnerTriangleParametricEdgeColor, wheelWithInnerTriangleGraph, wit01, wit02,
    wit03, wit12, wit23, wit31, wit45, wit56]

@[simp] private theorem wheelWithInnerTriangleParametricEdgeColor_wit64
    (a b u v : Color) :
    wheelWithInnerTriangleParametricEdgeColor a b u v wit64 = u + v := by
  simp [wheelWithInnerTriangleParametricEdgeColor, wheelWithInnerTriangleGraph, wit01, wit02,
    wit03, wit12, wit23, wit31, wit45, wit56, wit64]

private theorem validColorPair_symm {a b : Color} (hab : ValidColorPair a b) :
    ValidColorPair b a :=
  ⟨hab.2.1, hab.1, hab.2.2.symm⟩

private theorem validColorPair_third_left {a b : Color} (hab : ValidColorPair a b) :
    ValidColorPair (a + b) b := by
  rcases third_color_properties hab.1 hab.2.1 hab.2.2 with ⟨hab0, haba, habb⟩
  exact ⟨hab0, hab.2.1, habb⟩

private theorem validColorPair_left_third {a b : Color} (hab : ValidColorPair a b) :
    ValidColorPair a (a + b) := by
  rcases third_color_properties hab.1 hab.2.1 hab.2.2 with ⟨hab0, haba, habb⟩
  exact ⟨hab.1, hab0, haba.symm⟩

private theorem wit01_adj_wit02 :
    wheelWithInnerTriangleGraph.lineGraph.Adj wit01 wit02 := by
  rw [SimpleGraph.lineGraph_adj_iff_exists]
  refine ⟨by decide, (0 : Fin 7), ?_, ?_⟩ <;> simp [wit01, wit02]

private theorem wit01_adj_wit03 :
    wheelWithInnerTriangleGraph.lineGraph.Adj wit01 wit03 := by
  rw [SimpleGraph.lineGraph_adj_iff_exists]
  refine ⟨by decide, (0 : Fin 7), ?_, ?_⟩ <;> simp [wit01, wit03]

private theorem wit02_adj_wit03 :
    wheelWithInnerTriangleGraph.lineGraph.Adj wit02 wit03 := by
  rw [SimpleGraph.lineGraph_adj_iff_exists]
  refine ⟨by decide, (0 : Fin 7), ?_, ?_⟩ <;> simp [wit02, wit03]

private theorem wit01_adj_wit12 :
    wheelWithInnerTriangleGraph.lineGraph.Adj wit01 wit12 := by
  rw [SimpleGraph.lineGraph_adj_iff_exists]
  refine ⟨by decide, (1 : Fin 7), ?_, ?_⟩ <;> simp [wit01, wit12]

private theorem wit02_adj_wit12 :
    wheelWithInnerTriangleGraph.lineGraph.Adj wit02 wit12 := by
  rw [SimpleGraph.lineGraph_adj_iff_exists]
  refine ⟨by decide, (2 : Fin 7), ?_, ?_⟩ <;> simp [wit02, wit12]

private theorem wit02_adj_wit23 :
    wheelWithInnerTriangleGraph.lineGraph.Adj wit02 wit23 := by
  rw [SimpleGraph.lineGraph_adj_iff_exists]
  refine ⟨by decide, (2 : Fin 7), ?_, ?_⟩ <;> simp [wit02, wit23]

private theorem wit03_adj_wit23 :
    wheelWithInnerTriangleGraph.lineGraph.Adj wit03 wit23 := by
  rw [SimpleGraph.lineGraph_adj_iff_exists]
  refine ⟨by decide, (3 : Fin 7), ?_, ?_⟩ <;> simp [wit03, wit23]

private theorem wit01_adj_wit31 :
    wheelWithInnerTriangleGraph.lineGraph.Adj wit01 wit31 := by
  rw [SimpleGraph.lineGraph_adj_iff_exists]
  refine ⟨by decide, (1 : Fin 7), ?_, ?_⟩ <;> simp [wit01, wit31]

private theorem wit03_adj_wit31 :
    wheelWithInnerTriangleGraph.lineGraph.Adj wit03 wit31 := by
  rw [SimpleGraph.lineGraph_adj_iff_exists]
  refine ⟨by decide, (3 : Fin 7), ?_, ?_⟩ <;> simp [wit03, wit31]

private theorem wit45_adj_wit56 :
    wheelWithInnerTriangleGraph.lineGraph.Adj wit45 wit56 := by
  rw [SimpleGraph.lineGraph_adj_iff_exists]
  refine ⟨by decide, (5 : Fin 7), ?_, ?_⟩ <;> simp [wit45, wit56]

private theorem wit45_adj_wit64 :
    wheelWithInnerTriangleGraph.lineGraph.Adj wit45 wit64 := by
  rw [SimpleGraph.lineGraph_adj_iff_exists]
  refine ⟨by decide, (4 : Fin 7), ?_, ?_⟩ <;> simp [wit45, wit64]

private theorem wit56_adj_wit64 :
    wheelWithInnerTriangleGraph.lineGraph.Adj wit56 wit64 := by
  rw [SimpleGraph.lineGraph_adj_iff_exists]
  refine ⟨by decide, (6 : Fin 7), ?_, ?_⟩ <;> simp [wit56, wit64]

private theorem wheelWithInnerTriangleParametricEdgeColor_ne_of_adj
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v)
    {e f : wheelWithInnerTriangleGraph.edgeSet}
    (hadj : wheelWithInnerTriangleGraph.lineGraph.Adj e f) :
    wheelWithInnerTriangleParametricEdgeColor a b u v e ≠
      wheelWithInnerTriangleParametricEdgeColor a b u v f := by
  rcases third_color_properties hab.1 hab.2.1 hab.2.2 with ⟨hab0, haba, habb⟩
  rcases third_color_properties huv.1 huv.2.1 huv.2.2 with ⟨huv0, huva, huvb⟩
  intro hcolor
  rw [SimpleGraph.lineGraph_adj_iff_exists] at hadj
  rcases hadj with ⟨hne, vtx, he, hf⟩
  fin_cases vtx
  · rcases wheelWithInnerTriangle_edge_mem_zero he with rfl | rfl | rfl <;>
      rcases wheelWithInnerTriangle_edge_mem_zero hf with rfl | rfl | rfl <;>
      first
      | simpa [wheelWithInnerTriangleGraph, wit01, wit02, wit03] using hne
      | exact hab.2.2 (by simpa using hcolor)
      | exact hab.2.2 (by simpa using hcolor.symm)
      | exact haba (by simpa using hcolor)
      | exact haba (by simpa using hcolor.symm)
      | exact habb (by simpa using hcolor)
      | exact habb (by simpa using hcolor.symm)
  · rcases wheelWithInnerTriangle_edge_mem_one he with rfl | rfl | rfl <;>
      rcases wheelWithInnerTriangle_edge_mem_one hf with rfl | rfl | rfl <;>
      first
      | simpa [wheelWithInnerTriangleGraph, wit01, wit12, wit31] using hne
      | exact hab.2.2 (by simpa using hcolor)
      | exact hab.2.2 (by simpa using hcolor.symm)
      | exact haba (by simpa using hcolor)
      | exact haba (by simpa using hcolor.symm)
      | exact habb (by simpa using hcolor)
      | exact habb (by simpa using hcolor.symm)
  · rcases wheelWithInnerTriangle_edge_mem_two he with rfl | rfl | rfl <;>
      rcases wheelWithInnerTriangle_edge_mem_two hf with rfl | rfl | rfl <;>
      first
      | simpa [wheelWithInnerTriangleGraph, wit02, wit12, wit23] using hne
      | exact hab.2.2 (by simpa using hcolor)
      | exact hab.2.2 (by simpa using hcolor.symm)
      | exact haba (by simpa using hcolor)
      | exact haba (by simpa using hcolor.symm)
      | exact habb (by simpa using hcolor)
      | exact habb (by simpa using hcolor.symm)
  · rcases wheelWithInnerTriangle_edge_mem_three he with rfl | rfl | rfl <;>
      rcases wheelWithInnerTriangle_edge_mem_three hf with rfl | rfl | rfl <;>
      first
      | simpa [wheelWithInnerTriangleGraph, wit03, wit23, wit31] using hne
      | exact hab.2.2 (by simpa using hcolor)
      | exact hab.2.2 (by simpa using hcolor.symm)
      | exact haba (by simpa using hcolor)
      | exact haba (by simpa using hcolor.symm)
      | exact habb (by simpa using hcolor)
      | exact habb (by simpa using hcolor.symm)
  · rcases wheelWithInnerTriangle_edge_mem_four he with rfl | rfl <;>
      rcases wheelWithInnerTriangle_edge_mem_four hf with rfl | rfl <;>
      first
      | simpa [wheelWithInnerTriangleGraph, wit45, wit64] using hne
      | exact huva (by simpa using hcolor)
      | exact huva (by simpa using hcolor.symm)
  · rcases wheelWithInnerTriangle_edge_mem_five he with rfl | rfl <;>
      rcases wheelWithInnerTriangle_edge_mem_five hf with rfl | rfl <;>
      first
      | simpa [wheelWithInnerTriangleGraph, wit45, wit56] using hne
      | exact huv.2.2 (by simpa using hcolor)
      | exact huv.2.2 (by simpa using hcolor.symm)
  · rcases wheelWithInnerTriangle_edge_mem_six he with rfl | rfl <;>
      rcases wheelWithInnerTriangle_edge_mem_six hf with rfl | rfl <;>
      first
      | simpa [wheelWithInnerTriangleGraph, wit56, wit64] using hne
      | exact huvb (by simpa using hcolor)
      | exact huvb (by simpa using hcolor.symm)

private def wheelWithInnerTriangleParametricTaitEdgeColoring
    (a b u v : Color) (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    wheelWithInnerTriangleGraph.EdgeColoring Color :=
  Coloring.mk (wheelWithInnerTriangleParametricEdgeColor a b u v) (by
    intro e f hadj
    exact wheelWithInnerTriangleParametricEdgeColor_ne_of_adj hab huv hadj)

private theorem wheelWithInnerTriangleParametricTaitEdgeColoring_isTait
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    IsTaitEdgeColoring wheelWithInnerTriangleGraph
      (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv) := by
  intro e
  rcases third_color_properties hab.1 hab.2.1 hab.2.2 with ⟨hab0, _, _⟩
  rcases third_color_properties huv.1 huv.2.1 huv.2.2 with ⟨huv0, _, _⟩
  rcases wheelWithInnerTriangle_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [wheelWithInnerTriangleParametricTaitEdgeColoring] using hab.1
  · simpa [wheelWithInnerTriangleParametricTaitEdgeColoring] using hab.2.1
  · simpa [wheelWithInnerTriangleParametricTaitEdgeColoring] using hab0
  · simpa [wheelWithInnerTriangleParametricTaitEdgeColoring] using hab0
  · simpa [wheelWithInnerTriangleParametricTaitEdgeColoring] using hab.1
  · simpa [wheelWithInnerTriangleParametricTaitEdgeColoring] using hab.2.1
  · simpa [wheelWithInnerTriangleParametricTaitEdgeColoring] using huv.1
  · simpa [wheelWithInnerTriangleParametricTaitEdgeColoring] using huv.2.1
  · simpa [wheelWithInnerTriangleParametricTaitEdgeColoring] using huv0

private theorem validColorPair_wheelSpokes_of_isTait
    (C : wheelWithInnerTriangleGraph.EdgeColoring Color)
    (hC : IsTaitEdgeColoring wheelWithInnerTriangleGraph C) :
    ValidColorPair (C wit01) (C wit02) :=
  ⟨hC wit01, hC wit02, C.valid wit01_adj_wit02⟩

private theorem validColorPair_wheelTriangle_of_isTait
    (C : wheelWithInnerTriangleGraph.EdgeColoring Color)
    (hC : IsTaitEdgeColoring wheelWithInnerTriangleGraph C) :
    ValidColorPair (C wit45) (C wit56) :=
  ⟨hC wit45, hC wit56, C.valid wit45_adj_wit56⟩

private theorem wheelWithInnerTriangle_tait_forces_wit03
    (C : wheelWithInnerTriangleGraph.EdgeColoring Color)
    (hC : IsTaitEdgeColoring wheelWithInnerTriangleGraph C) :
    C wit03 = C wit01 + C wit02 := by
  exact eq_third_color_of_ne_zero_ne_ne (hC wit01) (hC wit02) (hC wit03)
    (C.valid wit01_adj_wit02) (C.valid wit01_adj_wit03) (C.valid wit02_adj_wit03)

private theorem wheelWithInnerTriangle_tait_forces_wit12
    (C : wheelWithInnerTriangleGraph.EdgeColoring Color)
    (hC : IsTaitEdgeColoring wheelWithInnerTriangleGraph C) :
    C wit12 = C wit01 + C wit02 := by
  exact eq_third_color_of_ne_zero_ne_ne (hC wit01) (hC wit02) (hC wit12)
    (C.valid wit01_adj_wit02) (C.valid wit01_adj_wit12) (C.valid wit02_adj_wit12)

private theorem wheelWithInnerTriangle_tait_forces_wit23
    (C : wheelWithInnerTriangleGraph.EdgeColoring Color)
    (hC : IsTaitEdgeColoring wheelWithInnerTriangleGraph C) :
    C wit23 = C wit01 := by
  calc
    C wit23 = C wit02 + C wit03 := by
      exact eq_third_color_of_ne_zero_ne_ne (hC wit02) (hC wit03) (hC wit23)
        (C.valid wit02_adj_wit03) (C.valid wit02_adj_wit23) (C.valid wit03_adj_wit23)
    _ = C wit01 := by
      rw [wheelWithInnerTriangle_tait_forces_wit03 C hC]
      calc
        C wit02 + (C wit01 + C wit02) = C wit01 + (C wit02 + C wit02) := by
          ac_rfl
        _ = C wit01 := by
          simp

private theorem wheelWithInnerTriangle_tait_forces_wit31
    (C : wheelWithInnerTriangleGraph.EdgeColoring Color)
    (hC : IsTaitEdgeColoring wheelWithInnerTriangleGraph C) :
    C wit31 = C wit02 := by
  calc
    C wit31 = C wit01 + C wit03 := by
      exact eq_third_color_of_ne_zero_ne_ne (hC wit01) (hC wit03) (hC wit31)
        (C.valid wit01_adj_wit03) (C.valid wit01_adj_wit31) (C.valid wit03_adj_wit31)
    _ = C wit02 := by
      rw [wheelWithInnerTriangle_tait_forces_wit03 C hC]
      calc
        C wit01 + (C wit01 + C wit02) = C wit02 + (C wit01 + C wit01) := by
          ac_rfl
        _ = C wit02 := by
          simp

private theorem wheelWithInnerTriangle_tait_forces_wit64
    (C : wheelWithInnerTriangleGraph.EdgeColoring Color)
    (hC : IsTaitEdgeColoring wheelWithInnerTriangleGraph C) :
    C wit64 = C wit45 + C wit56 := by
  exact eq_third_color_of_ne_zero_ne_ne (hC wit45) (hC wit56) (hC wit64)
    (C.valid wit45_adj_wit56) (C.valid wit45_adj_wit64) (C.valid wit56_adj_wit64)

private theorem eq_wheelWithInnerTriangleParametricTaitEdgeColoring_of_isTait
    (C : wheelWithInnerTriangleGraph.EdgeColoring Color)
    (hC : IsTaitEdgeColoring wheelWithInnerTriangleGraph C) :
    C =
      wheelWithInnerTriangleParametricTaitEdgeColoring
        (C wit01) (C wit02) (C wit45) (C wit56)
        (validColorPair_wheelSpokes_of_isTait C hC)
        (validColorPair_wheelTriangle_of_isTait C hC) := by
  apply DFunLike.ext
  intro e
  change C e =
    wheelWithInnerTriangleParametricEdgeColor
      (C wit01) (C wit02) (C wit45) (C wit56) e
  rcases wheelWithInnerTriangle_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp
  · simp
  · simp [wheelWithInnerTriangle_tait_forces_wit03 C hC]
  · simp [wheelWithInnerTriangle_tait_forces_wit12 C hC]
  · simp [wheelWithInnerTriangle_tait_forces_wit23 C hC]
  · simp [wheelWithInnerTriangle_tait_forces_wit31 C hC]
  · simp
  · simp
  · simp [wheelWithInnerTriangle_tait_forces_wit64 C hC]

private theorem validColorPair_red_blue : ValidColorPair red blue :=
  ⟨red_ne_zero, blue_ne_zero, red_ne_blue⟩

private def wheelEdgeCluster (e : wheelWithInnerTriangleGraph.edgeSet) : Bool :=
  if e = wit45 ∨ e = wit56 ∨ e = wit64 then true else false

private theorem wheelEdgeCluster_eq_of_lineGraph_adj
    {e f : wheelWithInnerTriangleGraph.edgeSet}
    (hadj : wheelWithInnerTriangleGraph.lineGraph.Adj e f) :
    wheelEdgeCluster e = wheelEdgeCluster f := by
  rw [SimpleGraph.lineGraph_adj_iff_exists] at hadj
  rcases hadj with ⟨_, vtx, he, hf⟩
  fin_cases vtx
  · rcases wheelWithInnerTriangle_edge_mem_zero he with rfl | rfl | rfl <;>
      rcases wheelWithInnerTriangle_edge_mem_zero hf with rfl | rfl | rfl <;>
      decide
  · rcases wheelWithInnerTriangle_edge_mem_one he with rfl | rfl | rfl <;>
      rcases wheelWithInnerTriangle_edge_mem_one hf with rfl | rfl | rfl <;>
      decide
  · rcases wheelWithInnerTriangle_edge_mem_two he with rfl | rfl | rfl <;>
      rcases wheelWithInnerTriangle_edge_mem_two hf with rfl | rfl | rfl <;>
      decide
  · rcases wheelWithInnerTriangle_edge_mem_three he with rfl | rfl | rfl <;>
      rcases wheelWithInnerTriangle_edge_mem_three hf with rfl | rfl | rfl <;>
      decide
  · rcases wheelWithInnerTriangle_edge_mem_four he with rfl | rfl <;>
      rcases wheelWithInnerTriangle_edge_mem_four hf with rfl | rfl <;>
      decide
  · rcases wheelWithInnerTriangle_edge_mem_five he with rfl | rfl <;>
      rcases wheelWithInnerTriangle_edge_mem_five hf with rfl | rfl <;>
      decide
  · rcases wheelWithInnerTriangle_edge_mem_six he with rfl | rfl <;>
      rcases wheelWithInnerTriangle_edge_mem_six hf with rfl | rfl <;>
      decide

private theorem wheelEdgeCluster_eq_of_bicoloredWalk
    {a b : Color}
    {C : wheelWithInnerTriangleGraph.EdgeColoring Color}
    {u v : ↥(C.bicoloredSet a b)}
    (p : (C.bicoloredSubgraph a b).Walk u v) :
    wheelEdgeCluster u.1 = wheelEdgeCluster v.1 := by
  induction p with
  | nil =>
      rfl
  | cons hadj p ih =>
      exact (wheelEdgeCluster_eq_of_lineGraph_adj (by simpa using hadj)).trans ih

private theorem wheelEdgeCluster_eq_of_bicoloredReachable
    {a b : Color}
    {C : wheelWithInnerTriangleGraph.EdgeColoring Color}
    {e f : wheelWithInnerTriangleGraph.edgeSet}
    {he : e ∈ C.bicoloredSet a b} {hf : f ∈ C.bicoloredSet a b}
    (hreach : (C.bicoloredSubgraph a b).Reachable ⟨e, he⟩ ⟨f, hf⟩) :
    wheelEdgeCluster e = wheelEdgeCluster f := by
  refine hreach.elim ?_
  intro p
  exact wheelEdgeCluster_eq_of_bicoloredWalk p

private theorem wheelWithInnerTriangleTaitEdgeColoring_eq_parametric :
    wheelWithInnerTriangleTaitEdgeColoring =
      wheelWithInnerTriangleParametricTaitEdgeColoring red blue red blue
        validColorPair_red_blue validColorPair_red_blue := by
  apply DFunLike.ext
  intro e
  change wheelWithInnerTriangleEdgeColor e =
    wheelWithInnerTriangleParametricEdgeColor red blue red blue e
  rcases wheelWithInnerTriangle_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [wheelWithInnerTriangleEdgeColor, wheelWithInnerTriangleParametricEdgeColor,
      wheelWithInnerTriangleGraph, wit01, wit02, wit03, wit12, wit23, wit31, wit45, wit56,
      wit64]

private theorem wit01_mem_parametric_bicoloredSet_ab
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    wit01 ∈
      (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv).bicoloredSet a b := by
  left
  change wheelWithInnerTriangleParametricEdgeColor a b u v wit01 = a
  simp

private noncomputable def wheelK4ABComponent
    (a b u v : Color) (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    ((wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv).bicoloredSubgraph
      a b).ConnectedComponent :=
  let C := wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv
  (C.bicoloredSubgraph a b).connectedComponentMk
    ⟨wit01, wit01_mem_parametric_bicoloredSet_ab hab huv⟩

private theorem wit01_mem_wheelK4ABComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    wit01 ∈
      (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        a b (wheelK4ABComponent a b u v hab huv) := by
  let C := wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv
  exact C.mem_kempeComponentSet_self (wit01_mem_parametric_bicoloredSet_ab hab huv)

private theorem wit02_mem_wheelK4ABComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    wit02 ∈
      (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        a b (wheelK4ABComponent a b u v hab huv) := by
  let C := wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv
  exact C.mem_kempeComponentSet_of_adj (wit01_mem_wheelK4ABComponent hab huv) wit01_adj_wit02
    (by
      right
      change wheelWithInnerTriangleParametricEdgeColor a b u v wit02 = b
      simp)

private theorem wit23_mem_wheelK4ABComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    wit23 ∈
      (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        a b (wheelK4ABComponent a b u v hab huv) := by
  let C := wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv
  exact C.mem_kempeComponentSet_of_adj (wit02_mem_wheelK4ABComponent hab huv) wit02_adj_wit23
    (by
      left
      change wheelWithInnerTriangleParametricEdgeColor a b u v wit23 = a
      simp)

private theorem wit31_mem_wheelK4ABComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    wit31 ∈
      (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        a b (wheelK4ABComponent a b u v hab huv) := by
  let C := wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv
  exact C.mem_kempeComponentSet_of_adj (wit01_mem_wheelK4ABComponent hab huv) wit01_adj_wit31
    (by
      right
      change wheelWithInnerTriangleParametricEdgeColor a b u v wit31 = b
      simp)

private theorem wheelEdgeCluster_eq_false_of_mem_wheelK4ABComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v)
    {e : wheelWithInnerTriangleGraph.edgeSet}
    (hmem : e ∈
      (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        a b (wheelK4ABComponent a b u v hab huv)) :
    wheelEdgeCluster e = false := by
  rcases hmem with ⟨he, hcomp⟩
  let C := wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv
  have hcomp' :
      (C.bicoloredSubgraph a b).connectedComponentMk ⟨e, he⟩ =
      (C.bicoloredSubgraph a b).connectedComponentMk
        ⟨wit01, wit01_mem_parametric_bicoloredSet_ab hab huv⟩ := by
    simpa [wheelK4ABComponent, C] using hcomp
  have hreach :
      (C.bicoloredSubgraph a b).Reachable ⟨e, he⟩
        ⟨wit01, wit01_mem_parametric_bicoloredSet_ab hab huv⟩ :=
    (ConnectedComponent.eq.mp hcomp')
  have hcluster :=
    wheelEdgeCluster_eq_of_bicoloredReachable hreach
  have hwit01 : wheelEdgeCluster wit01 = false := by
    decide
  exact hcluster.trans hwit01

private theorem wit03_not_mem_wheelK4ABComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    wit03 ∉
      (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        a b (wheelK4ABComponent a b u v hab huv) := by
  rcases third_color_properties hab.1 hab.2.1 hab.2.2 with ⟨_, haba, habb⟩
  intro hmem
  let C := wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv
  rcases C.mem_bicoloredSet_of_mem_kempeComponentSet hmem with h | h
  · change wheelWithInnerTriangleParametricEdgeColor a b u v wit03 = a at h
    exact haba (by simpa using h.symm)
  · change wheelWithInnerTriangleParametricEdgeColor a b u v wit03 = b at h
    exact habb (by simpa using h.symm)

private theorem wit12_not_mem_wheelK4ABComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    wit12 ∉
      (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        a b (wheelK4ABComponent a b u v hab huv) := by
  rcases third_color_properties hab.1 hab.2.1 hab.2.2 with ⟨_, haba, habb⟩
  intro hmem
  let C := wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv
  rcases C.mem_bicoloredSet_of_mem_kempeComponentSet hmem with h | h
  · change wheelWithInnerTriangleParametricEdgeColor a b u v wit12 = a at h
    exact haba (by simpa using h.symm)
  · change wheelWithInnerTriangleParametricEdgeColor a b u v wit12 = b at h
    exact habb (by simpa using h.symm)

private theorem wit45_not_mem_wheelK4ABComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    wit45 ∉
      (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        a b (wheelK4ABComponent a b u v hab huv) := by
  intro hmem
  have hcluster := wheelEdgeCluster_eq_false_of_mem_wheelK4ABComponent hab huv hmem
  simp [wheelEdgeCluster] at hcluster

private theorem wit56_not_mem_wheelK4ABComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    wit56 ∉
      (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        a b (wheelK4ABComponent a b u v hab huv) := by
  intro hmem
  have hcluster := wheelEdgeCluster_eq_false_of_mem_wheelK4ABComponent hab huv hmem
  simp [wheelEdgeCluster] at hcluster

private theorem wit64_not_mem_wheelK4ABComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    wit64 ∉
      (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        a b (wheelK4ABComponent a b u v hab huv) := by
  intro hmem
  have hcluster := wheelEdgeCluster_eq_false_of_mem_wheelK4ABComponent hab huv hmem
  simp [wheelEdgeCluster] at hcluster

private theorem wheelWithInnerTriangleParametricTaitEdgeColoring_swap_ab_eq
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv).swapOnKempeComponent
        a b (wheelK4ABComponent a b u v hab huv) =
      wheelWithInnerTriangleParametricTaitEdgeColoring b a u v
        (validColorPair_symm hab) huv := by
  apply DFunLike.ext
  intro e
  rcases wheelWithInnerTriangle_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [Coloring.swapOnKempeComponent_apply_of_mem]
    · change Equiv.swap a b (wheelWithInnerTriangleParametricEdgeColor a b u v wit01) =
        wheelWithInnerTriangleParametricEdgeColor b a u v wit01
      simp
    · exact wit01_mem_wheelK4ABComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_mem]
    · change Equiv.swap a b (wheelWithInnerTriangleParametricEdgeColor a b u v wit02) =
        wheelWithInnerTriangleParametricEdgeColor b a u v wit02
      simp
    · exact wit02_mem_wheelK4ABComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change wheelWithInnerTriangleParametricEdgeColor a b u v wit03 =
        wheelWithInnerTriangleParametricEdgeColor b a u v wit03
      simp [add_comm]
    · exact wit03_not_mem_wheelK4ABComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change wheelWithInnerTriangleParametricEdgeColor a b u v wit12 =
        wheelWithInnerTriangleParametricEdgeColor b a u v wit12
      simp [add_comm]
    · exact wit12_not_mem_wheelK4ABComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_mem]
    · change Equiv.swap a b (wheelWithInnerTriangleParametricEdgeColor a b u v wit23) =
        wheelWithInnerTriangleParametricEdgeColor b a u v wit23
      simp
    · exact wit23_mem_wheelK4ABComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_mem]
    · change Equiv.swap a b (wheelWithInnerTriangleParametricEdgeColor a b u v wit31) =
        wheelWithInnerTriangleParametricEdgeColor b a u v wit31
      simp
    · exact wit31_mem_wheelK4ABComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change wheelWithInnerTriangleParametricEdgeColor a b u v wit45 =
        wheelWithInnerTriangleParametricEdgeColor b a u v wit45
      simp
    · exact wit45_not_mem_wheelK4ABComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change wheelWithInnerTriangleParametricEdgeColor a b u v wit56 =
        wheelWithInnerTriangleParametricEdgeColor b a u v wit56
      simp
    · exact wit56_not_mem_wheelK4ABComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change wheelWithInnerTriangleParametricEdgeColor a b u v wit64 =
        wheelWithInnerTriangleParametricEdgeColor b a u v wit64
      simp
    · exact wit64_not_mem_wheelK4ABComponent hab huv

private theorem wheelWithInnerTriangleParametricTaitEdgeColoring_swap_ab_mem_edgeKempeClosure
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    wheelWithInnerTriangleParametricTaitEdgeColoring b a u v
        (validColorPair_symm hab) huv ∈
      wheelWithInnerTriangleGraph.EdgeKempeClosure
        (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv) := by
  rw [← wheelWithInnerTriangleParametricTaitEdgeColoring_swap_ab_eq hab huv]
  exact wheelWithInnerTriangleGraph.mem_edgeKempeClosure_of_mem_of_step
    (wheelWithInnerTriangleGraph.mem_edgeKempeClosure_self
      (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv))
    a b (wheelK4ABComponent a b u v hab huv)

private theorem wheelEdgeCluster_eq_false_of_mem_component_containing_wit01
    {x y : Color}
    {C : wheelWithInnerTriangleGraph.EdgeColoring Color}
    {K : (C.bicoloredSubgraph x y).ConnectedComponent}
    {e : wheelWithInnerTriangleGraph.edgeSet}
    (h01 : wit01 ∈ C.kempeComponentSet x y K)
    (he : e ∈ C.kempeComponentSet x y K) :
    wheelEdgeCluster e = false := by
  rcases he with ⟨he', hec⟩
  rcases h01 with ⟨h01', h01c⟩
  have hcomp' :
      (C.bicoloredSubgraph x y).connectedComponentMk ⟨e, he'⟩ =
      (C.bicoloredSubgraph x y).connectedComponentMk ⟨wit01, h01'⟩ :=
    hec.trans h01c.symm
  have hreach : (C.bicoloredSubgraph x y).Reachable ⟨e, he'⟩ ⟨wit01, h01'⟩ :=
    ConnectedComponent.eq.mp hcomp'
  have hcluster := wheelEdgeCluster_eq_of_bicoloredReachable hreach
  exact hcluster.trans (by decide)

private theorem wheelEdgeCluster_eq_true_of_mem_component_containing_wit45
    {x y : Color}
    {C : wheelWithInnerTriangleGraph.EdgeColoring Color}
    {K : (C.bicoloredSubgraph x y).ConnectedComponent}
    {e : wheelWithInnerTriangleGraph.edgeSet}
    (h45 : wit45 ∈ C.kempeComponentSet x y K)
    (he : e ∈ C.kempeComponentSet x y K) :
    wheelEdgeCluster e = true := by
  rcases he with ⟨he', hec⟩
  rcases h45 with ⟨h45', h45c⟩
  have hcomp' :
      (C.bicoloredSubgraph x y).connectedComponentMk ⟨e, he'⟩ =
      (C.bicoloredSubgraph x y).connectedComponentMk ⟨wit45, h45'⟩ :=
    hec.trans h45c.symm
  have hreach : (C.bicoloredSubgraph x y).Reachable ⟨e, he'⟩ ⟨wit45, h45'⟩ :=
    ConnectedComponent.eq.mp hcomp'
  have hcluster := wheelEdgeCluster_eq_of_bicoloredReachable hreach
  exact hcluster.trans (by decide)

private theorem wit01_mem_parametric_bicoloredSet_aThird
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    wit01 ∈
      (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv).bicoloredSet a (a + b) := by
  left
  change wheelWithInnerTriangleParametricEdgeColor a b u v wit01 = a
  simp

private noncomputable def wheelK4AThirdComponent
    (a b u v : Color) (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    ((wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv).bicoloredSubgraph
      a (a + b)).ConnectedComponent :=
  let C := wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv
  (C.bicoloredSubgraph a (a + b)).connectedComponentMk
    ⟨wit01, wit01_mem_parametric_bicoloredSet_aThird hab huv⟩

private theorem wit01_mem_wheelK4AThirdComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    wit01 ∈
      (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        a (a + b) (wheelK4AThirdComponent a b u v hab huv) := by
  let C := wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv
  exact C.mem_kempeComponentSet_self (wit01_mem_parametric_bicoloredSet_aThird hab huv)

private theorem wit03_mem_wheelK4AThirdComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    wit03 ∈
      (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        a (a + b) (wheelK4AThirdComponent a b u v hab huv) := by
  let C := wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv
  exact C.mem_kempeComponentSet_of_adj (wit01_mem_wheelK4AThirdComponent hab huv) wit01_adj_wit03
    (by
      right
      change wheelWithInnerTriangleParametricEdgeColor a b u v wit03 = a + b
      simp)

private theorem wit23_mem_wheelK4AThirdComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    wit23 ∈
      (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        a (a + b) (wheelK4AThirdComponent a b u v hab huv) := by
  let C := wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv
  exact C.mem_kempeComponentSet_of_adj (wit03_mem_wheelK4AThirdComponent hab huv) wit03_adj_wit23
    (by
      left
      change wheelWithInnerTriangleParametricEdgeColor a b u v wit23 = a
      simp)

private theorem wit12_mem_wheelK4AThirdComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    wit12 ∈
      (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        a (a + b) (wheelK4AThirdComponent a b u v hab huv) := by
  let C := wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv
  exact C.mem_kempeComponentSet_of_adj (wit01_mem_wheelK4AThirdComponent hab huv) wit01_adj_wit12
    (by
      right
      change wheelWithInnerTriangleParametricEdgeColor a b u v wit12 = a + b
      simp)

private theorem wit02_not_mem_wheelK4AThirdComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    wit02 ∉
      (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        a (a + b) (wheelK4AThirdComponent a b u v hab huv) := by
  rcases third_color_properties hab.1 hab.2.1 hab.2.2 with ⟨_, haba, habb⟩
  intro hmem
  let C := wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv
  rcases C.mem_bicoloredSet_of_mem_kempeComponentSet hmem with h | h
  · change wheelWithInnerTriangleParametricEdgeColor a b u v wit02 = a at h
    exact hab.2.2.symm (by simpa using h)
  · change wheelWithInnerTriangleParametricEdgeColor a b u v wit02 = a + b at h
    exact habb.symm (by simpa using h)

private theorem wit31_not_mem_wheelK4AThirdComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    wit31 ∉
      (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        a (a + b) (wheelK4AThirdComponent a b u v hab huv) := by
  rcases third_color_properties hab.1 hab.2.1 hab.2.2 with ⟨_, haba, habb⟩
  intro hmem
  let C := wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv
  rcases C.mem_bicoloredSet_of_mem_kempeComponentSet hmem with h | h
  · change wheelWithInnerTriangleParametricEdgeColor a b u v wit31 = a at h
    exact hab.2.2.symm (by simpa using h)
  · change wheelWithInnerTriangleParametricEdgeColor a b u v wit31 = a + b at h
    exact habb.symm (by simpa using h)

private theorem wit45_not_mem_wheelK4AThirdComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    wit45 ∉
      (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        a (a + b) (wheelK4AThirdComponent a b u v hab huv) := by
  intro hmem
  have hcluster := wheelEdgeCluster_eq_false_of_mem_component_containing_wit01
    (wit01_mem_wheelK4AThirdComponent hab huv) hmem
  simp [wheelEdgeCluster] at hcluster

private theorem wit56_not_mem_wheelK4AThirdComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    wit56 ∉
      (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        a (a + b) (wheelK4AThirdComponent a b u v hab huv) := by
  intro hmem
  have hcluster := wheelEdgeCluster_eq_false_of_mem_component_containing_wit01
    (wit01_mem_wheelK4AThirdComponent hab huv) hmem
  simp [wheelEdgeCluster] at hcluster

private theorem wit64_not_mem_wheelK4AThirdComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    wit64 ∉
      (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        a (a + b) (wheelK4AThirdComponent a b u v hab huv) := by
  intro hmem
  have hcluster := wheelEdgeCluster_eq_false_of_mem_component_containing_wit01
    (wit01_mem_wheelK4AThirdComponent hab huv) hmem
  simp [wheelEdgeCluster] at hcluster

private theorem wheelWithInnerTriangleParametricTaitEdgeColoring_swap_aThird_eq
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv).swapOnKempeComponent
        a (a + b) (wheelK4AThirdComponent a b u v hab huv) =
      wheelWithInnerTriangleParametricTaitEdgeColoring (a + b) b u v
        (validColorPair_third_left hab) huv := by
  apply DFunLike.ext
  intro e
  rcases wheelWithInnerTriangle_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [Coloring.swapOnKempeComponent_apply_of_mem]
    · change Equiv.swap a (a + b) (wheelWithInnerTriangleParametricEdgeColor a b u v wit01) =
        wheelWithInnerTriangleParametricEdgeColor (a + b) b u v wit01
      simp
    · exact wit01_mem_wheelK4AThirdComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change wheelWithInnerTriangleParametricEdgeColor a b u v wit02 =
        wheelWithInnerTriangleParametricEdgeColor (a + b) b u v wit02
      simp
    · exact wit02_not_mem_wheelK4AThirdComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_mem]
    · change Equiv.swap a (a + b) (wheelWithInnerTriangleParametricEdgeColor a b u v wit03) =
        wheelWithInnerTriangleParametricEdgeColor (a + b) b u v wit03
      simp [add_assoc]
    · exact wit03_mem_wheelK4AThirdComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_mem]
    · change Equiv.swap a (a + b) (wheelWithInnerTriangleParametricEdgeColor a b u v wit12) =
        wheelWithInnerTriangleParametricEdgeColor (a + b) b u v wit12
      simp [add_assoc]
    · exact wit12_mem_wheelK4AThirdComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_mem]
    · change Equiv.swap a (a + b) (wheelWithInnerTriangleParametricEdgeColor a b u v wit23) =
        wheelWithInnerTriangleParametricEdgeColor (a + b) b u v wit23
      simp
    · exact wit23_mem_wheelK4AThirdComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change wheelWithInnerTriangleParametricEdgeColor a b u v wit31 =
        wheelWithInnerTriangleParametricEdgeColor (a + b) b u v wit31
      simp
    · exact wit31_not_mem_wheelK4AThirdComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change wheelWithInnerTriangleParametricEdgeColor a b u v wit45 =
        wheelWithInnerTriangleParametricEdgeColor (a + b) b u v wit45
      simp
    · exact wit45_not_mem_wheelK4AThirdComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change wheelWithInnerTriangleParametricEdgeColor a b u v wit56 =
        wheelWithInnerTriangleParametricEdgeColor (a + b) b u v wit56
      simp
    · exact wit56_not_mem_wheelK4AThirdComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change wheelWithInnerTriangleParametricEdgeColor a b u v wit64 =
        wheelWithInnerTriangleParametricEdgeColor (a + b) b u v wit64
      simp
    · exact wit64_not_mem_wheelK4AThirdComponent hab huv

private theorem wheelWithInnerTriangleParametricTaitEdgeColoring_swap_aThird_mem_edgeKempeClosure
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    wheelWithInnerTriangleParametricTaitEdgeColoring (a + b) b u v
        (validColorPair_third_left hab) huv ∈
      wheelWithInnerTriangleGraph.EdgeKempeClosure
        (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv) := by
  rw [← wheelWithInnerTriangleParametricTaitEdgeColoring_swap_aThird_eq hab huv]
  exact wheelWithInnerTriangleGraph.mem_edgeKempeClosure_of_mem_of_step
    (wheelWithInnerTriangleGraph.mem_edgeKempeClosure_self
      (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv))
    a (a + b) (wheelK4AThirdComponent a b u v hab huv)

private theorem wit45_mem_parametric_bicoloredSet_uv
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    wit45 ∈
      (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv).bicoloredSet u v := by
  left
  change wheelWithInnerTriangleParametricEdgeColor a b u v wit45 = u
  simp

private noncomputable def wheelOuterUVComponent
    (a b u v : Color) (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    ((wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv).bicoloredSubgraph
      u v).ConnectedComponent :=
  let C := wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv
  (C.bicoloredSubgraph u v).connectedComponentMk
    ⟨wit45, wit45_mem_parametric_bicoloredSet_uv hab huv⟩

private theorem wit45_mem_wheelOuterUVComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    wit45 ∈
      (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        u v (wheelOuterUVComponent a b u v hab huv) := by
  let C := wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv
  exact C.mem_kempeComponentSet_self (wit45_mem_parametric_bicoloredSet_uv hab huv)

private theorem wit56_mem_wheelOuterUVComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    wit56 ∈
      (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        u v (wheelOuterUVComponent a b u v hab huv) := by
  let C := wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv
  exact C.mem_kempeComponentSet_of_adj (wit45_mem_wheelOuterUVComponent hab huv) wit45_adj_wit56
    (by
      right
      change wheelWithInnerTriangleParametricEdgeColor a b u v wit56 = v
      simp)

private theorem wit64_not_mem_wheelOuterUVComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    wit64 ∉
      (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        u v (wheelOuterUVComponent a b u v hab huv) := by
  rcases third_color_properties huv.1 huv.2.1 huv.2.2 with ⟨_, huva, huvb⟩
  intro hmem
  let C := wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv
  rcases C.mem_bicoloredSet_of_mem_kempeComponentSet hmem with h | h
  · change wheelWithInnerTriangleParametricEdgeColor a b u v wit64 = u at h
    exact huva (by simpa using h)
  · change wheelWithInnerTriangleParametricEdgeColor a b u v wit64 = v at h
    exact huvb (by simpa using h)

private theorem wit01_not_mem_wheelOuterUVComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    wit01 ∉
      (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        u v (wheelOuterUVComponent a b u v hab huv) := by
  intro hmem
  have hcluster := wheelEdgeCluster_eq_true_of_mem_component_containing_wit45
    (wit45_mem_wheelOuterUVComponent hab huv) hmem
  have hwit01 : wheelEdgeCluster wit01 = false := by
    decide
  exact Bool.false_ne_true (hwit01.symm.trans hcluster)

private theorem wit02_not_mem_wheelOuterUVComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    wit02 ∉
      (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        u v (wheelOuterUVComponent a b u v hab huv) := by
  intro hmem
  have hcluster := wheelEdgeCluster_eq_true_of_mem_component_containing_wit45
    (wit45_mem_wheelOuterUVComponent hab huv) hmem
  have hwit02 : wheelEdgeCluster wit02 = false := by
    decide
  exact Bool.false_ne_true (hwit02.symm.trans hcluster)

private theorem wit03_not_mem_wheelOuterUVComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    wit03 ∉
      (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        u v (wheelOuterUVComponent a b u v hab huv) := by
  intro hmem
  have hcluster := wheelEdgeCluster_eq_true_of_mem_component_containing_wit45
    (wit45_mem_wheelOuterUVComponent hab huv) hmem
  have hwit03 : wheelEdgeCluster wit03 = false := by
    decide
  exact Bool.false_ne_true (hwit03.symm.trans hcluster)

private theorem wit12_not_mem_wheelOuterUVComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    wit12 ∉
      (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        u v (wheelOuterUVComponent a b u v hab huv) := by
  intro hmem
  have hcluster := wheelEdgeCluster_eq_true_of_mem_component_containing_wit45
    (wit45_mem_wheelOuterUVComponent hab huv) hmem
  have hwit12 : wheelEdgeCluster wit12 = false := by
    decide
  exact Bool.false_ne_true (hwit12.symm.trans hcluster)

private theorem wit23_not_mem_wheelOuterUVComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    wit23 ∉
      (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        u v (wheelOuterUVComponent a b u v hab huv) := by
  intro hmem
  have hcluster := wheelEdgeCluster_eq_true_of_mem_component_containing_wit45
    (wit45_mem_wheelOuterUVComponent hab huv) hmem
  have hwit23 : wheelEdgeCluster wit23 = false := by
    decide
  exact Bool.false_ne_true (hwit23.symm.trans hcluster)

private theorem wit31_not_mem_wheelOuterUVComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    wit31 ∉
      (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        u v (wheelOuterUVComponent a b u v hab huv) := by
  intro hmem
  have hcluster := wheelEdgeCluster_eq_true_of_mem_component_containing_wit45
    (wit45_mem_wheelOuterUVComponent hab huv) hmem
  have hwit31 : wheelEdgeCluster wit31 = false := by
    decide
  exact Bool.false_ne_true (hwit31.symm.trans hcluster)

private theorem wheelWithInnerTriangleParametricTaitEdgeColoring_swap_uv_eq
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv).swapOnKempeComponent
        u v (wheelOuterUVComponent a b u v hab huv) =
      wheelWithInnerTriangleParametricTaitEdgeColoring a b v u hab
        (validColorPair_symm huv) := by
  apply DFunLike.ext
  intro e
  rcases wheelWithInnerTriangle_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change wheelWithInnerTriangleParametricEdgeColor a b u v wit01 =
        wheelWithInnerTriangleParametricEdgeColor a b v u wit01
      simp
    · exact wit01_not_mem_wheelOuterUVComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change wheelWithInnerTriangleParametricEdgeColor a b u v wit02 =
        wheelWithInnerTriangleParametricEdgeColor a b v u wit02
      simp
    · exact wit02_not_mem_wheelOuterUVComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change wheelWithInnerTriangleParametricEdgeColor a b u v wit03 =
        wheelWithInnerTriangleParametricEdgeColor a b v u wit03
      simp
    · exact wit03_not_mem_wheelOuterUVComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change wheelWithInnerTriangleParametricEdgeColor a b u v wit12 =
        wheelWithInnerTriangleParametricEdgeColor a b v u wit12
      simp
    · exact wit12_not_mem_wheelOuterUVComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change wheelWithInnerTriangleParametricEdgeColor a b u v wit23 =
        wheelWithInnerTriangleParametricEdgeColor a b v u wit23
      simp
    · exact wit23_not_mem_wheelOuterUVComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change wheelWithInnerTriangleParametricEdgeColor a b u v wit31 =
        wheelWithInnerTriangleParametricEdgeColor a b v u wit31
      simp
    · exact wit31_not_mem_wheelOuterUVComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_mem]
    · change Equiv.swap u v (wheelWithInnerTriangleParametricEdgeColor a b u v wit45) =
        wheelWithInnerTriangleParametricEdgeColor a b v u wit45
      simp
    · exact wit45_mem_wheelOuterUVComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_mem]
    · change Equiv.swap u v (wheelWithInnerTriangleParametricEdgeColor a b u v wit56) =
        wheelWithInnerTriangleParametricEdgeColor a b v u wit56
      simp
    · exact wit56_mem_wheelOuterUVComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change wheelWithInnerTriangleParametricEdgeColor a b u v wit64 =
        wheelWithInnerTriangleParametricEdgeColor a b v u wit64
      simp [add_comm]
    · exact wit64_not_mem_wheelOuterUVComponent hab huv

private theorem wheelWithInnerTriangleParametricTaitEdgeColoring_swap_uv_mem_edgeKempeClosure
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    wheelWithInnerTriangleParametricTaitEdgeColoring a b v u hab
        (validColorPair_symm huv) ∈
      wheelWithInnerTriangleGraph.EdgeKempeClosure
        (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv) := by
  rw [← wheelWithInnerTriangleParametricTaitEdgeColoring_swap_uv_eq hab huv]
  exact wheelWithInnerTriangleGraph.mem_edgeKempeClosure_of_mem_of_step
    (wheelWithInnerTriangleGraph.mem_edgeKempeClosure_self
      (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv))
    u v (wheelOuterUVComponent a b u v hab huv)

private theorem wit45_mem_parametric_bicoloredSet_uThird
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    wit45 ∈
      (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv).bicoloredSet
        u (u + v) := by
  left
  change wheelWithInnerTriangleParametricEdgeColor a b u v wit45 = u
  simp

private noncomputable def wheelOuterUThirdComponent
    (a b u v : Color) (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    ((wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv).bicoloredSubgraph
      u (u + v)).ConnectedComponent :=
  let C := wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv
  (C.bicoloredSubgraph u (u + v)).connectedComponentMk
    ⟨wit45, wit45_mem_parametric_bicoloredSet_uThird hab huv⟩

private theorem wit45_mem_wheelOuterUThirdComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    wit45 ∈
      (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        u (u + v) (wheelOuterUThirdComponent a b u v hab huv) := by
  let C := wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv
  exact C.mem_kempeComponentSet_self (wit45_mem_parametric_bicoloredSet_uThird hab huv)

private theorem wit64_mem_wheelOuterUThirdComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    wit64 ∈
      (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        u (u + v) (wheelOuterUThirdComponent a b u v hab huv) := by
  let C := wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv
  exact C.mem_kempeComponentSet_of_adj
    (wit45_mem_wheelOuterUThirdComponent hab huv) wit45_adj_wit64 (by
      right
      change wheelWithInnerTriangleParametricEdgeColor a b u v wit64 = u + v
      simp)

private theorem wit56_not_mem_wheelOuterUThirdComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    wit56 ∉
      (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        u (u + v) (wheelOuterUThirdComponent a b u v hab huv) := by
  rcases third_color_properties huv.1 huv.2.1 huv.2.2 with ⟨_, huva, huvb⟩
  intro hmem
  let C := wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv
  rcases C.mem_bicoloredSet_of_mem_kempeComponentSet hmem with h | h
  · change wheelWithInnerTriangleParametricEdgeColor a b u v wit56 = u at h
    exact huv.2.2.symm (by simpa using h)
  · change wheelWithInnerTriangleParametricEdgeColor a b u v wit56 = u + v at h
    exact huvb.symm (by simpa using h)

private theorem wit01_not_mem_wheelOuterUThirdComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    wit01 ∉
      (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        u (u + v) (wheelOuterUThirdComponent a b u v hab huv) := by
  intro hmem
  have hcluster := wheelEdgeCluster_eq_true_of_mem_component_containing_wit45
    (wit45_mem_wheelOuterUThirdComponent hab huv) hmem
  have hwit01 : wheelEdgeCluster wit01 = false := by
    decide
  exact Bool.false_ne_true (hwit01.symm.trans hcluster)

private theorem wit02_not_mem_wheelOuterUThirdComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    wit02 ∉
      (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        u (u + v) (wheelOuterUThirdComponent a b u v hab huv) := by
  intro hmem
  have hcluster := wheelEdgeCluster_eq_true_of_mem_component_containing_wit45
    (wit45_mem_wheelOuterUThirdComponent hab huv) hmem
  have hwit02 : wheelEdgeCluster wit02 = false := by
    decide
  exact Bool.false_ne_true (hwit02.symm.trans hcluster)

private theorem wit03_not_mem_wheelOuterUThirdComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    wit03 ∉
      (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        u (u + v) (wheelOuterUThirdComponent a b u v hab huv) := by
  intro hmem
  have hcluster := wheelEdgeCluster_eq_true_of_mem_component_containing_wit45
    (wit45_mem_wheelOuterUThirdComponent hab huv) hmem
  have hwit03 : wheelEdgeCluster wit03 = false := by
    decide
  exact Bool.false_ne_true (hwit03.symm.trans hcluster)

private theorem wit12_not_mem_wheelOuterUThirdComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    wit12 ∉
      (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        u (u + v) (wheelOuterUThirdComponent a b u v hab huv) := by
  intro hmem
  have hcluster := wheelEdgeCluster_eq_true_of_mem_component_containing_wit45
    (wit45_mem_wheelOuterUThirdComponent hab huv) hmem
  have hwit12 : wheelEdgeCluster wit12 = false := by
    decide
  exact Bool.false_ne_true (hwit12.symm.trans hcluster)

private theorem wit23_not_mem_wheelOuterUThirdComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    wit23 ∉
      (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        u (u + v) (wheelOuterUThirdComponent a b u v hab huv) := by
  intro hmem
  have hcluster := wheelEdgeCluster_eq_true_of_mem_component_containing_wit45
    (wit45_mem_wheelOuterUThirdComponent hab huv) hmem
  have hwit23 : wheelEdgeCluster wit23 = false := by
    decide
  exact Bool.false_ne_true (hwit23.symm.trans hcluster)

private theorem wit31_not_mem_wheelOuterUThirdComponent
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    wit31 ∉
      (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv).kempeComponentSet
        u (u + v) (wheelOuterUThirdComponent a b u v hab huv) := by
  intro hmem
  have hcluster := wheelEdgeCluster_eq_true_of_mem_component_containing_wit45
    (wit45_mem_wheelOuterUThirdComponent hab huv) hmem
  have hwit31 : wheelEdgeCluster wit31 = false := by
    decide
  exact Bool.false_ne_true (hwit31.symm.trans hcluster)

private theorem wheelWithInnerTriangleParametricTaitEdgeColoring_swap_uThird_eq
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv).swapOnKempeComponent
        u (u + v) (wheelOuterUThirdComponent a b u v hab huv) =
      wheelWithInnerTriangleParametricTaitEdgeColoring a b (u + v) v hab
        (validColorPair_third_left huv) := by
  apply DFunLike.ext
  intro e
  rcases wheelWithInnerTriangle_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change wheelWithInnerTriangleParametricEdgeColor a b u v wit01 =
        wheelWithInnerTriangleParametricEdgeColor a b (u + v) v wit01
      simp
    · exact wit01_not_mem_wheelOuterUThirdComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change wheelWithInnerTriangleParametricEdgeColor a b u v wit02 =
        wheelWithInnerTriangleParametricEdgeColor a b (u + v) v wit02
      simp
    · exact wit02_not_mem_wheelOuterUThirdComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change wheelWithInnerTriangleParametricEdgeColor a b u v wit03 =
        wheelWithInnerTriangleParametricEdgeColor a b (u + v) v wit03
      simp
    · exact wit03_not_mem_wheelOuterUThirdComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change wheelWithInnerTriangleParametricEdgeColor a b u v wit12 =
        wheelWithInnerTriangleParametricEdgeColor a b (u + v) v wit12
      simp
    · exact wit12_not_mem_wheelOuterUThirdComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change wheelWithInnerTriangleParametricEdgeColor a b u v wit23 =
        wheelWithInnerTriangleParametricEdgeColor a b (u + v) v wit23
      simp
    · exact wit23_not_mem_wheelOuterUThirdComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change wheelWithInnerTriangleParametricEdgeColor a b u v wit31 =
        wheelWithInnerTriangleParametricEdgeColor a b (u + v) v wit31
      simp
    · exact wit31_not_mem_wheelOuterUThirdComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_mem]
    · change Equiv.swap u (u + v) (wheelWithInnerTriangleParametricEdgeColor a b u v wit45) =
        wheelWithInnerTriangleParametricEdgeColor a b (u + v) v wit45
      simp
    · exact wit45_mem_wheelOuterUThirdComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · change wheelWithInnerTriangleParametricEdgeColor a b u v wit56 =
        wheelWithInnerTriangleParametricEdgeColor a b (u + v) v wit56
      simp
    · exact wit56_not_mem_wheelOuterUThirdComponent hab huv
  · rw [Coloring.swapOnKempeComponent_apply_of_mem]
    · change Equiv.swap u (u + v) (wheelWithInnerTriangleParametricEdgeColor a b u v wit64) =
        wheelWithInnerTriangleParametricEdgeColor a b (u + v) v wit64
      simp [add_assoc]
    · exact wit64_mem_wheelOuterUThirdComponent hab huv

private theorem wheelWithInnerTriangleParametricTaitEdgeColoring_swap_uThird_mem_edgeKempeClosure
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    wheelWithInnerTriangleParametricTaitEdgeColoring a b (u + v) v hab
        (validColorPair_third_left huv) ∈
      wheelWithInnerTriangleGraph.EdgeKempeClosure
        (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv) := by
  rw [← wheelWithInnerTriangleParametricTaitEdgeColoring_swap_uThird_eq hab huv]
  exact wheelWithInnerTriangleGraph.mem_edgeKempeClosure_of_mem_of_step
    (wheelWithInnerTriangleGraph.mem_edgeKempeClosure_self
      (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv))
    u (u + v) (wheelOuterUThirdComponent a b u v hab huv)

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

private theorem wheelWithInnerTriangleParametricTaitEdgeColoring_edgeKempeClosure_eq_swap_ab
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    wheelWithInnerTriangleGraph.EdgeKempeClosure
      (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv) =
    wheelWithInnerTriangleGraph.EdgeKempeClosure
      (wheelWithInnerTriangleParametricTaitEdgeColoring b a u v (validColorPair_symm hab) huv) := by
  apply wheelWithInnerTriangleGraph.edgeKempeClosure_eq_of_mem_of_mem
  · exact wheelWithInnerTriangleParametricTaitEdgeColoring_swap_ab_mem_edgeKempeClosure hab huv
  · simpa using
      (wheelWithInnerTriangleParametricTaitEdgeColoring_swap_ab_mem_edgeKempeClosure
        (a := b) (b := a) (u := u) (v := v) (hab := validColorPair_symm hab) (huv := huv))

private theorem wheelWithInnerTriangleParametricTaitEdgeColoring_edgeKempeClosure_eq_swap_aThird
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    wheelWithInnerTriangleGraph.EdgeKempeClosure
      (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv) =
    wheelWithInnerTriangleGraph.EdgeKempeClosure
      (wheelWithInnerTriangleParametricTaitEdgeColoring (a + b) b u v
        (validColorPair_third_left hab) huv) := by
  apply wheelWithInnerTriangleGraph.edgeKempeClosure_eq_of_mem_of_mem
  · exact wheelWithInnerTriangleParametricTaitEdgeColoring_swap_aThird_mem_edgeKempeClosure hab huv
  · simpa [add_assoc] using
      (wheelWithInnerTriangleParametricTaitEdgeColoring_swap_aThird_mem_edgeKempeClosure
        (a := a + b) (b := b) (u := u) (v := v)
        (hab := validColorPair_third_left hab) (huv := huv))

private theorem wheelWithInnerTriangleParametricTaitEdgeColoring_edgeKempeClosure_eq_swap_uv
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    wheelWithInnerTriangleGraph.EdgeKempeClosure
      (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv) =
    wheelWithInnerTriangleGraph.EdgeKempeClosure
      (wheelWithInnerTriangleParametricTaitEdgeColoring a b v u hab (validColorPair_symm huv)) := by
  apply wheelWithInnerTriangleGraph.edgeKempeClosure_eq_of_mem_of_mem
  · exact wheelWithInnerTriangleParametricTaitEdgeColoring_swap_uv_mem_edgeKempeClosure hab huv
  · simpa using
      (wheelWithInnerTriangleParametricTaitEdgeColoring_swap_uv_mem_edgeKempeClosure
        (a := a) (b := b) (u := v) (v := u) (hab := hab) (huv := validColorPair_symm huv))

private theorem wheelWithInnerTriangleParametricTaitEdgeColoring_edgeKempeClosure_eq_swap_uThird
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    wheelWithInnerTriangleGraph.EdgeKempeClosure
      (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv) =
    wheelWithInnerTriangleGraph.EdgeKempeClosure
      (wheelWithInnerTriangleParametricTaitEdgeColoring a b (u + v) v hab
        (validColorPair_third_left huv)) := by
  apply wheelWithInnerTriangleGraph.edgeKempeClosure_eq_of_mem_of_mem
  · exact wheelWithInnerTriangleParametricTaitEdgeColoring_swap_uThird_mem_edgeKempeClosure hab huv
  · simpa [add_assoc] using
      (wheelWithInnerTriangleParametricTaitEdgeColoring_swap_uThird_mem_edgeKempeClosure
        (a := a) (b := b) (u := u + v) (v := v) (hab := hab)
        (huv := validColorPair_third_left huv))

private theorem wheelWithInnerTriangleParametricTaitEdgeColoring_k4Closure_eq_base
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    wheelWithInnerTriangleGraph.EdgeKempeClosure
      (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv) =
    wheelWithInnerTriangleGraph.EdgeKempeClosure
      (wheelWithInnerTriangleParametricTaitEdgeColoring red blue u v validColorPair_red_blue huv) := by
  let K := fun x y (hxy : ValidColorPair x y) =>
    wheelWithInnerTriangleGraph.EdgeKempeClosure
      (wheelWithInnerTriangleParametricTaitEdgeColoring x y u v hxy huv)
  change K a b hab = K red blue validColorPair_red_blue
  rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero a hab.1 with rfl | rfl | rfl
  · rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero b hab.2.1 with rfl | rfl | rfl
    · exact False.elim (hab.2.2 rfl)
    · rfl
    · calc
        K red purple hab = K blue purple validColorPair_blue_purple := by
          simpa [K] using
            (wheelWithInnerTriangleParametricTaitEdgeColoring_edgeKempeClosure_eq_swap_aThird
              (a := blue) (b := purple) (u := u) (v := v) validColorPair_blue_purple huv).symm
        _ = K purple blue validColorPair_purple_blue := by
          simpa [K] using
            (wheelWithInnerTriangleParametricTaitEdgeColoring_edgeKempeClosure_eq_swap_ab
              (a := purple) (b := blue) (u := u) (v := v) validColorPair_purple_blue huv).symm
        _ = K red blue validColorPair_red_blue := by
          simpa [K] using
            (wheelWithInnerTriangleParametricTaitEdgeColoring_edgeKempeClosure_eq_swap_aThird
              (a := red) (b := blue) (u := u) (v := v) validColorPair_red_blue huv).symm
  · rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero b hab.2.1 with rfl | rfl | rfl
    · simpa [K] using
        (wheelWithInnerTriangleParametricTaitEdgeColoring_edgeKempeClosure_eq_swap_ab
          (a := red) (b := blue) (u := u) (v := v) validColorPair_red_blue huv).symm
    · exact False.elim (hab.2.2 rfl)
    · calc
        K blue purple hab = K purple blue validColorPair_purple_blue := by
          simpa [K] using
            (wheelWithInnerTriangleParametricTaitEdgeColoring_edgeKempeClosure_eq_swap_ab
              (a := purple) (b := blue) (u := u) (v := v) validColorPair_purple_blue huv).symm
        _ = K red blue validColorPair_red_blue := by
          simpa [K] using
            (wheelWithInnerTriangleParametricTaitEdgeColoring_edgeKempeClosure_eq_swap_aThird
              (a := red) (b := blue) (u := u) (v := v) validColorPair_red_blue huv).symm
  · rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero b hab.2.1 with rfl | rfl | rfl
    · calc
        K purple red hab = K blue red validColorPair_blue_red := by
          simpa [K] using
            (wheelWithInnerTriangleParametricTaitEdgeColoring_edgeKempeClosure_eq_swap_aThird
              (a := blue) (b := red) (u := u) (v := v) validColorPair_blue_red huv).symm
        _ = K red blue validColorPair_red_blue := by
          simpa [K] using
            (wheelWithInnerTriangleParametricTaitEdgeColoring_edgeKempeClosure_eq_swap_ab
              (a := red) (b := blue) (u := u) (v := v) validColorPair_red_blue huv).symm
    · simpa [K] using
        (wheelWithInnerTriangleParametricTaitEdgeColoring_edgeKempeClosure_eq_swap_aThird
          (a := red) (b := blue) (u := u) (v := v) validColorPair_red_blue huv).symm
    · exact False.elim (hab.2.2 rfl)

private theorem wheelWithInnerTriangleParametricTaitEdgeColoring_outerClosure_eq_base
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    wheelWithInnerTriangleGraph.EdgeKempeClosure
      (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv) =
    wheelWithInnerTriangleGraph.EdgeKempeClosure
      (wheelWithInnerTriangleParametricTaitEdgeColoring a b red blue hab validColorPair_red_blue) := by
  let K := fun x y (hxy : ValidColorPair x y) =>
    wheelWithInnerTriangleGraph.EdgeKempeClosure
      (wheelWithInnerTriangleParametricTaitEdgeColoring a b x y hab hxy)
  change K u v huv = K red blue validColorPair_red_blue
  rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero u huv.1 with rfl | rfl | rfl
  · rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero v huv.2.1 with rfl | rfl | rfl
    · exact False.elim (huv.2.2 rfl)
    · rfl
    · calc
        K red purple huv = K blue purple validColorPair_blue_purple := by
          simpa [K] using
            (wheelWithInnerTriangleParametricTaitEdgeColoring_edgeKempeClosure_eq_swap_uThird
              (a := a) (b := b) (u := blue) (v := purple) (hab := hab)
              validColorPair_blue_purple).symm
        _ = K purple blue validColorPair_purple_blue := by
          simpa [K] using
            (wheelWithInnerTriangleParametricTaitEdgeColoring_edgeKempeClosure_eq_swap_uv
              (a := a) (b := b) (u := purple) (v := blue) (hab := hab)
              validColorPair_purple_blue).symm
        _ = K red blue validColorPair_red_blue := by
          simpa [K] using
            (wheelWithInnerTriangleParametricTaitEdgeColoring_edgeKempeClosure_eq_swap_uThird
              (a := a) (b := b) (u := red) (v := blue) (hab := hab)
              validColorPair_red_blue).symm
  · rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero v huv.2.1 with rfl | rfl | rfl
    · simpa [K] using
        (wheelWithInnerTriangleParametricTaitEdgeColoring_edgeKempeClosure_eq_swap_uv
          (a := a) (b := b) (u := red) (v := blue) (hab := hab)
          validColorPair_red_blue).symm
    · exact False.elim (huv.2.2 rfl)
    · calc
        K blue purple huv = K purple blue validColorPair_purple_blue := by
          simpa [K] using
            (wheelWithInnerTriangleParametricTaitEdgeColoring_edgeKempeClosure_eq_swap_uv
              (a := a) (b := b) (u := purple) (v := blue) (hab := hab)
              validColorPair_purple_blue).symm
        _ = K red blue validColorPair_red_blue := by
          simpa [K] using
            (wheelWithInnerTriangleParametricTaitEdgeColoring_edgeKempeClosure_eq_swap_uThird
              (a := a) (b := b) (u := red) (v := blue) (hab := hab)
              validColorPair_red_blue).symm
  · rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero v huv.2.1 with rfl | rfl | rfl
    · calc
        K purple red huv = K blue red validColorPair_blue_red := by
          simpa [K] using
            (wheelWithInnerTriangleParametricTaitEdgeColoring_edgeKempeClosure_eq_swap_uThird
              (a := a) (b := b) (u := blue) (v := red) (hab := hab)
              validColorPair_blue_red).symm
        _ = K red blue validColorPair_red_blue := by
          simpa [K] using
            (wheelWithInnerTriangleParametricTaitEdgeColoring_edgeKempeClosure_eq_swap_uv
              (a := a) (b := b) (u := red) (v := blue) (hab := hab)
              validColorPair_red_blue).symm
    · simpa [K] using
        (wheelWithInnerTriangleParametricTaitEdgeColoring_edgeKempeClosure_eq_swap_uThird
          (a := a) (b := b) (u := red) (v := blue) (hab := hab)
          validColorPair_red_blue).symm
    · exact False.elim (huv.2.2 rfl)

private theorem wheelWithInnerTriangleParametricTaitEdgeColoring_edgeKempeClosure_eq_explicit
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    wheelWithInnerTriangleGraph.EdgeKempeClosure
      (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv) =
    wheelWithInnerTriangleGraph.EdgeKempeClosure wheelWithInnerTriangleTaitEdgeColoring := by
  calc
    wheelWithInnerTriangleGraph.EdgeKempeClosure
        (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv) =
      wheelWithInnerTriangleGraph.EdgeKempeClosure
        (wheelWithInnerTriangleParametricTaitEdgeColoring red blue u v validColorPair_red_blue huv) :=
      wheelWithInnerTriangleParametricTaitEdgeColoring_k4Closure_eq_base hab huv
    _ =
      wheelWithInnerTriangleGraph.EdgeKempeClosure
        (wheelWithInnerTriangleParametricTaitEdgeColoring red blue red blue
          validColorPair_red_blue validColorPair_red_blue) :=
      wheelWithInnerTriangleParametricTaitEdgeColoring_outerClosure_eq_base
        validColorPair_red_blue huv
    _ = wheelWithInnerTriangleGraph.EdgeKempeClosure wheelWithInnerTriangleTaitEdgeColoring := by
      rw [wheelWithInnerTriangleTaitEdgeColoring_eq_parametric]

private theorem wheelWithInnerTriangleEmbedding_boundaryZeroProjectedGeneratorDetector_for_parametricTaitColoring
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    BoundaryZeroProjectedGeneratorDetector wheelWithInnerTriangleEmbedding
      (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv) := by
  have hdetExplicit :
      BoundaryZeroProjectedGeneratorDetector wheelWithInnerTriangleEmbedding
        wheelWithInnerTriangleTaitEdgeColoring :=
    BoundaryZeroProjectedGeneratorDetector.of_boundaryZeroAnnihilatorTrivial
      wheelWithInnerTriangleEmbedding_boundaryZeroAnnihilatorTrivial_for_explicitTaitColoring
  exact BoundaryZeroProjectedGeneratorDetector.of_edgeKempeClosure_eq
    (G := wheelWithInnerTriangleGraph) (emb := wheelWithInnerTriangleEmbedding)
    (C₀ := wheelWithInnerTriangleTaitEdgeColoring)
    (C₁ := wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv)
    (wheelWithInnerTriangleParametricTaitEdgeColoring_edgeKempeClosure_eq_explicit hab huv).symm
    hdetExplicit

/-- Every wheel benchmark Tait coloring lies in the same edge-Kempe closure class as the
explicit wheel endpoint already checked directly in `Theorem49WheelEndpointRegression`. -/
theorem wheelWithInnerTriangleEmbedding_theorem49BoundaryRootSynthesis_for_parametricTaitColoring
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)]
    {a b u v : Color} (hab : ValidColorPair a b) (huv : ValidColorPair u v) :
    Theorem49BoundaryRootSynthesis wheelWithInnerTriangleEmbedding
      (wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv) := by
  exact Theorem49BoundaryRootSynthesis.of_edgeKempeClosure_eq
    (G := wheelWithInnerTriangleGraph) (emb := wheelWithInnerTriangleEmbedding)
    (C₀ := wheelWithInnerTriangleTaitEdgeColoring)
    (C₁ := wheelWithInnerTriangleParametricTaitEdgeColoring a b u v hab huv)
    (wheelWithInnerTriangleParametricTaitEdgeColoring_edgeKempeClosure_eq_explicit hab huv).symm
    wheelWithInnerTriangleEmbedding_theorem49BoundaryRootSynthesis_for_explicitTaitColoring

/-- The explicit wheel detector certificate propagates to every wheel Tait coloring in the
unique wheel edge-Kempe closure class. -/
theorem wheelWithInnerTriangleEmbedding_boundaryZeroProjectedGeneratorDetector_of_isTait
    (C : wheelWithInnerTriangleGraph.EdgeColoring Color)
    (hC : IsTaitEdgeColoring wheelWithInnerTriangleGraph C) :
    BoundaryZeroProjectedGeneratorDetector wheelWithInnerTriangleEmbedding C := by
  let hab := validColorPair_wheelSpokes_of_isTait C hC
  let huv := validColorPair_wheelTriangle_of_isTait C hC
  rw [eq_wheelWithInnerTriangleParametricTaitEdgeColoring_of_isTait C hC]
  exact wheelWithInnerTriangleEmbedding_boundaryZeroProjectedGeneratorDetector_for_parametricTaitColoring
    hab huv

/-- The wheel full sweep closes: every Tait coloring of the honest wheel embedding satisfies the
current theorem-4.9 synthesis endpoint because all such colorings lie in the explicit wheel
closure class. -/
theorem wheelWithInnerTriangleEmbedding_theorem49BoundaryRootSynthesis_of_isTait
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)]
    (C : wheelWithInnerTriangleGraph.EdgeColoring Color)
    (hC : IsTaitEdgeColoring wheelWithInnerTriangleGraph C) :
    Theorem49BoundaryRootSynthesis wheelWithInnerTriangleEmbedding C := by
  let hab := validColorPair_wheelSpokes_of_isTait C hC
  let huv := validColorPair_wheelTriangle_of_isTait C hC
  rw [eq_wheelWithInnerTriangleParametricTaitEdgeColoring_of_isTait C hC]
  exact wheelWithInnerTriangleEmbedding_theorem49BoundaryRootSynthesis_for_parametricTaitColoring
    hab huv

end Theorem49WheelFullSweepRegression

end Mettapedia.GraphTheory.FourColor
