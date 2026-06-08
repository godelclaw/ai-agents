import Mettapedia.Computability.PNP.FiniteCoinPostprocessingSameSignObstruction

/-!
# P vs NP grassroots: signed-bias quantizer obstruction

The finite-coin signed fiber bias is the bottom-up analogue of a boundary-law
field: positive bias means more true-side than false-side coin mass in one
output fiber, negative bias means the reverse.

This file isolates the repair route where a later predictor sees only a finite
postprocessing of that signed bias.  If every quantizer cell stays entirely on
one side of zero, then quantization cannot lower the finite-coin output defect
and cannot make a fixed tolerance certificate newly true.

So any successful finite quantization repair must merge positive-bias and
negative-bias outputs into the same quantizer cell.
-/

namespace Mettapedia.Computability.PNP

/-- A signed-bias quantizer is one-sided if every output cell contains only
nonnegative biases or only nonpositive biases. -/
def finiteCoinSignedBiasQuantizerOneSided {β : Type*} (q : Int → β) : Prop :=
  ∀ z : β, (∀ s : Int, q s = z → 0 ≤ s) ∨ (∀ s : Int, q s = z → s ≤ 0)

/-- Quantize each original finite-coin output only through its signed
true-minus-false fiber bias. -/
def finiteCoinSignedBiasQuantizedRecoding
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (q : Int → β) : Bool → Coin → β :=
  fun b c => q (finiteCoinSignedFiberBias r (r b c))

/-- A one-sided signed-bias quantizer induces one-sided signed bias on every
postprocessed fiber of the original output surface. -/
theorem finiteOutputFiberSignedBiasOneSided_of_finiteCoinSignedBiasQuantizerOneSided
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (q : Int → β)
    (hone : finiteCoinSignedBiasQuantizerOneSided q) :
    finiteOutputFiberSignedBiasOneSided r
      (fun y => q (finiteCoinSignedFiberBias r y)) := by
  intro z
  rcases hone z with hnonneg | hnonpos
  · left
    intro y hy
    exact hnonneg (finiteCoinSignedFiberBias r y)
      (by simpa [finiteOutputPreimageFiber] using hy)
  · right
    intro y hy
    exact hnonpos (finiteCoinSignedFiberBias r y)
      (by simpa [finiteOutputPreimageFiber] using hy)

/-- If every signed-bias quantizer cell is one-sided, quantizing the bias
cannot strictly lower the finite-coin output defect. -/
theorem countIndependentWithinOutputDefect_finiteCoinOutput_le_of_finiteCoinSignedBiasQuantizerOneSided
    {Coin α β : Type*} [Fintype Coin] [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (q : Int → β)
    (hone : finiteCoinSignedBiasQuantizerOneSided q) :
    countIndependentWithinOutputDefect (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput r) ≤
    countIndependentWithinOutputDefect (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput (finiteCoinSignedBiasQuantizedRecoding r q)) := by
  simpa [finiteCoinSignedBiasQuantizedRecoding] using
    countIndependentWithinOutputDefect_finiteCoinOutput_le_of_signedBiasOneSided
      r (fun y => q (finiteCoinSignedFiberBias r y))
      (finiteOutputFiberSignedBiasOneSided_of_finiteCoinSignedBiasQuantizerOneSided
        r q hone)

/-- A one-sided signed-bias quantizer cannot make a failing tolerance-`τ`
certificate newly true. -/
theorem not_countIndependentWithinToleranceOutput_finiteCoinSignedBiasQuantizedRecoding_of_not_tolerance_of_oneSided
    {Coin α β : Type*} [Fintype Coin] [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (q : Int → β) (τ : Nat)
    (hone : finiteCoinSignedBiasQuantizerOneSided q)
    (hnot : ¬ CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput r) τ) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput (finiteCoinSignedBiasQuantizedRecoding r q)) τ := by
  intro hpost
  have hpost_le :
      countIndependentWithinOutputDefect (Ω := Bool × Coin)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (finiteCoinOutput (finiteCoinSignedBiasQuantizedRecoding r q)) ≤ τ :=
    (countIndependentWithinToleranceOutput_iff_outputDefect_le
      (fun _ω : Bool × Coin => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput (finiteCoinSignedBiasQuantizedRecoding r q)) τ).mp hpost
  have horig_le :
      countIndependentWithinOutputDefect (Ω := Bool × Coin)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (finiteCoinOutput r) ≤ τ := by
    exact le_trans
      (countIndependentWithinOutputDefect_finiteCoinOutput_le_of_finiteCoinSignedBiasQuantizerOneSided
        r q hone)
      hpost_le
  exact hnot
    ((countIndependentWithinToleranceOutput_iff_outputDefect_le
      (fun _ω : Bool × Coin => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput r) τ).mpr horig_le)

/-- So if bias quantization strictly lowers the finite-coin output defect, then
the quantizer cannot be one-sided. -/
theorem not_finiteCoinSignedBiasQuantizerOneSided_of_quantizedOutput_outputDefect_lt
    {Coin α β : Type*} [Fintype Coin] [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (q : Int → β)
    (hlt : countIndependentWithinOutputDefect (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput (finiteCoinSignedBiasQuantizedRecoding r q)) <
      countIndependentWithinOutputDefect (Ω := Bool × Coin)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (finiteCoinOutput r)) :
    ¬ finiteCoinSignedBiasQuantizerOneSided q := by
  intro hone
  exact (Nat.not_lt_of_ge
    (countIndependentWithinOutputDefect_finiteCoinOutput_le_of_finiteCoinSignedBiasQuantizerOneSided
      r q hone)) hlt

/-- The same one-sided-quantizer obstruction in tolerance form. -/
theorem not_finiteCoinSignedBiasQuantizerOneSided_of_quantizedOutput_tolerance_of_not_tolerance
    {Coin α β : Type*} [Fintype Coin] [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (q : Int → β) (τ : Nat)
    (hpost : CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput (finiteCoinSignedBiasQuantizedRecoding r q)) τ)
    (hnot : ¬ CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput r) τ) :
    ¬ finiteCoinSignedBiasQuantizerOneSided q := by
  intro hone
  exact
    not_countIndependentWithinToleranceOutput_finiteCoinSignedBiasQuantizedRecoding_of_not_tolerance_of_oneSided
      r q τ hone hnot hpost

/-- If signed-bias quantization strictly lowers the finite-coin output defect,
then one quantizer cell contains both a positive-bias and a negative-bias
original output. -/
theorem exists_oppositeSign_quantizerCollision_of_quantizedOutput_outputDefect_lt
    {Coin α β : Type*} [Fintype Coin] [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (q : Int → β)
    (hlt : countIndependentWithinOutputDefect (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput (finiteCoinSignedBiasQuantizedRecoding r q)) <
      countIndependentWithinOutputDefect (Ω := Bool × Coin)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (finiteCoinOutput r)) :
    ∃ yPos yNeg : α,
      q (finiteCoinSignedFiberBias r yPos) =
        q (finiteCoinSignedFiberBias r yNeg) ∧
        yPos ≠ yNeg ∧
        0 < finiteCoinSignedFiberBias r yPos ∧
          finiteCoinSignedFiberBias r yNeg < 0 := by
  simpa [finiteCoinSignedBiasQuantizedRecoding] using
    exists_oppositeSign_observedOutput_collision_of_postcompose_outputDefect_lt
      r (fun y => q (finiteCoinSignedFiberBias r y)) hlt

/-- The same opposite-sign quantizer-cell obstruction in tolerance form. -/
theorem exists_oppositeSign_quantizerCollision_of_quantizedOutput_tolerance_of_not_tolerance
    {Coin α β : Type*} [Fintype Coin] [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (q : Int → β) (τ : Nat)
    (hpost : CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput (finiteCoinSignedBiasQuantizedRecoding r q)) τ)
    (hnot : ¬ CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput r) τ) :
    ∃ yPos yNeg : α,
      q (finiteCoinSignedFiberBias r yPos) =
        q (finiteCoinSignedFiberBias r yNeg) ∧
        yPos ≠ yNeg ∧
        0 < finiteCoinSignedFiberBias r yPos ∧
          finiteCoinSignedFiberBias r yNeg < 0 := by
  simpa [finiteCoinSignedBiasQuantizedRecoding] using
    exists_oppositeSign_observedOutput_collision_of_postcompose_tolerance_of_not_tolerance
      r (fun y => q (finiteCoinSignedFiberBias r y)) τ hpost hnot

end Mettapedia.Computability.PNP
