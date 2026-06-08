import Mettapedia.Computability.PNP.FiniteCoinSignedBiasQuantizerObstruction

/-!
# P vs NP grassroots: dithered signed-bias quantizer obstruction

The v13 manuscript explicitly allows finite quantizers with independent public
dither.  This file lifts the signed-bias quantizer obstruction to that
setting.

We adjoin the finite dither seed to the observed output, then postprocess the
pair `(original output, seed)` by a deterministic quantizer of the signed
finite-coin bias together with the seed.  If every output bucket stays on one
side of zero bias, then this dithered quantization still cannot improve the
finite-coin defect or make a failing tolerance certificate newly true.

So any successful finite dithered quantizer must contain some output bucket
that merges a positive-bias output/seed pair with a negative-bias
output/seed pair.
-/

namespace Mettapedia.Computability.PNP

/-- Adjoin a finite public dither seed to the observed output. -/
def finiteCoinOutputWithDither
    {Coin α Dither : Type*} (r : Bool → Coin → α) :
    Bool → Coin × Dither → α × Dither :=
  fun b cd => (r b cd.1, cd.2)

/-- The true-side fiber count for one output/seed pair is the same as the
true-side fiber count of the underlying output alone. -/
theorem coinTrueFiberCount_outputWithDither
    {Coin α Dither : Type*} [Fintype Coin] [Fintype Dither]
    [DecidableEq α] [DecidableEq Dither]
    (r : Bool → Coin → α) (y : α) (d : Dither) :
    coinTrueFiberCount (finiteCoinOutputWithDither r) (y, d) =
      coinTrueFiberCount r y := by
  have hprod :
      finiteEventCount (Coin × Dither)
          (fun cd => r true cd.1 = y ∧ cd.2 = d) =
        finiteEventCount Coin (fun c => r true c = y) *
          finiteEventCount Dither (fun d' => d' = d) := by
    simpa using
      (finiteEventCount_prod
        (Ω := Coin) (Coin := Dither)
        (fun c : Coin => r true c = y)
        (fun d' : Dither => d' = d))
  have hd :
      finiteEventCount Dither (fun d' : Dither => d' = d) = 1 := by
    simp [finiteEventCount]
  calc
    coinTrueFiberCount (finiteCoinOutputWithDither r) (y, d) =
        finiteEventCount (Coin × Dither)
          (fun cd => r true cd.1 = y ∧ cd.2 = d) := by
            simp [coinTrueFiberCount, finiteCoinOutputWithDither]
    _ =
        finiteEventCount Coin (fun c => r true c = y) *
          finiteEventCount Dither (fun d' => d' = d) := hprod
    _ = finiteEventCount Coin (fun c => r true c = y) := by
          rw [hd, Nat.mul_one]
    _ = coinTrueFiberCount r y := by
          simp [coinTrueFiberCount]

/-- The false-side fiber count for one output/seed pair is the same as the
false-side fiber count of the underlying output alone. -/
theorem coinFalseFiberCount_outputWithDither
    {Coin α Dither : Type*} [Fintype Coin] [Fintype Dither]
    [DecidableEq α] [DecidableEq Dither]
    (r : Bool → Coin → α) (y : α) (d : Dither) :
    coinFalseFiberCount (finiteCoinOutputWithDither r) (y, d) =
      coinFalseFiberCount r y := by
  have hprod :
      finiteEventCount (Coin × Dither)
          (fun cd => r false cd.1 = y ∧ cd.2 = d) =
        finiteEventCount Coin (fun c => r false c = y) *
          finiteEventCount Dither (fun d' => d' = d) := by
    simpa using
      (finiteEventCount_prod
        (Ω := Coin) (Coin := Dither)
        (fun c : Coin => r false c = y)
        (fun d' : Dither => d' = d))
  have hd :
      finiteEventCount Dither (fun d' : Dither => d' = d) = 1 := by
    simp [finiteEventCount]
  calc
    coinFalseFiberCount (finiteCoinOutputWithDither r) (y, d) =
        finiteEventCount (Coin × Dither)
          (fun cd => r false cd.1 = y ∧ cd.2 = d) := by
            simp [coinFalseFiberCount, finiteCoinOutputWithDither]
    _ =
        finiteEventCount Coin (fun c => r false c = y) *
          finiteEventCount Dither (fun d' => d' = d) := hprod
    _ = finiteEventCount Coin (fun c => r false c = y) := by
          rw [hd, Nat.mul_one]
    _ = coinFalseFiberCount r y := by
          simp [coinFalseFiberCount]

/-- Adjoining an independent finite dither seed does not change the signed
true-minus-false bias of an output fiber; it only splits that fiber into seed
slices. -/
theorem finiteCoinSignedFiberBias_outputWithDither
    {Coin α Dither : Type*} [Fintype Coin] [Fintype Dither]
    [DecidableEq α] [DecidableEq Dither]
    (r : Bool → Coin → α) (y : α) (d : Dither) :
    finiteCoinSignedFiberBias (finiteCoinOutputWithDither r) (y, d) =
      finiteCoinSignedFiberBias r y := by
  unfold finiteCoinSignedFiberBias
  rw [coinTrueFiberCount_outputWithDither r y d,
    coinFalseFiberCount_outputWithDither r y d]

/-- A dithered signed-bias quantizer is one-sided if each output bucket
contains only nonnegative biases or only nonpositive biases, uniformly across
all dither seeds. -/
def finiteCoinSignedBiasDitheredQuantizerOneSided
    {Dither β : Type*} (q : Int × Dither → β) : Prop :=
  ∀ z : β,
    (∀ s : Int, ∀ d : Dither, q (s, d) = z → 0 ≤ s) ∨
      (∀ s : Int, ∀ d : Dither, q (s, d) = z → s ≤ 0)

/-- Quantize the signed finite-coin bias after adjoining an independent finite
dither seed to the observation. -/
def finiteCoinSignedBiasDitheredQuantizedRecoding
    {Coin α Dither β : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (q : Int × Dither → β) :
    Bool → Coin × Dither → β :=
  fun b cd => q (finiteCoinSignedFiberBias r (r b cd.1), cd.2)

/-- A one-sided dithered signed-bias quantizer induces one-sided signed bias on
the dither-adjoined output surface. -/
theorem finiteOutputFiberSignedBiasOneSided_of_finiteCoinSignedBiasDitheredQuantizerOneSided
    {Coin α Dither β : Type*} [Fintype Coin] [Fintype Dither] [Fintype α]
    [DecidableEq α] [DecidableEq Dither] [DecidableEq β]
    (r : Bool → Coin → α) (q : Int × Dither → β)
    (hone : finiteCoinSignedBiasDitheredQuantizerOneSided q) :
    finiteOutputFiberSignedBiasOneSided (finiteCoinOutputWithDither r)
      (fun yd => q (finiteCoinSignedFiberBias r yd.1, yd.2)) := by
  intro z
  rcases hone z with hnonneg | hnonpos
  · left
    intro yd hyd
    rcases yd with ⟨y, d⟩
    have hq : q (finiteCoinSignedFiberBias r y, d) = z := by
      simpa [finiteOutputPreimageFiber] using hyd
    rw [finiteCoinSignedFiberBias_outputWithDither r y d]
    exact hnonneg (finiteCoinSignedFiberBias r y) d hq
  · right
    intro yd hyd
    rcases yd with ⟨y, d⟩
    have hq : q (finiteCoinSignedFiberBias r y, d) = z := by
      simpa [finiteOutputPreimageFiber] using hyd
    rw [finiteCoinSignedFiberBias_outputWithDither r y d]
    exact hnonpos (finiteCoinSignedFiberBias r y) d hq

/-- A one-sided finite dithered signed-bias quantizer cannot strictly lower the
finite-coin output defect on the dither-adjoined sample space. -/
theorem countIndependentWithinOutputDefect_finiteCoinOutputWithDither_le_of_finiteCoinSignedBiasDitheredQuantizerOneSided
    {Coin α Dither β : Type*} [Fintype Coin] [Fintype Dither]
    [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq Dither] [DecidableEq β]
    (r : Bool → Coin → α) (q : Int × Dither → β)
    (hone : finiteCoinSignedBiasDitheredQuantizerOneSided q) :
    countIndependentWithinOutputDefect (Ω := Bool × (Coin × Dither))
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin × Dither))
      (finiteCoinOutput (finiteCoinOutputWithDither r)) ≤
    countIndependentWithinOutputDefect (Ω := Bool × (Coin × Dither))
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin × Dither))
      (finiteCoinOutput (finiteCoinSignedBiasDitheredQuantizedRecoding r q)) := by
  simpa [finiteCoinSignedBiasDitheredQuantizedRecoding, finiteCoinOutputWithDither] using
    countIndependentWithinOutputDefect_finiteCoinOutput_le_of_signedBiasOneSided
      (r := finiteCoinOutputWithDither r)
      (g := fun yd => q (finiteCoinSignedFiberBias r yd.1, yd.2))
      (finiteOutputFiberSignedBiasOneSided_of_finiteCoinSignedBiasDitheredQuantizerOneSided
        r q hone)

/-- A one-sided finite dithered signed-bias quantizer cannot make a failing
tolerance-`τ` certificate newly true on the dither-adjoined sample space. -/
theorem not_countIndependentWithinToleranceOutput_finiteCoinSignedBiasDitheredQuantizedRecoding_of_not_tolerance_of_oneSided
    {Coin α Dither β : Type*} [Fintype Coin] [Fintype Dither]
    [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq Dither] [DecidableEq β]
    (r : Bool → Coin → α) (q : Int × Dither → β) (τ : Nat)
    (hone : finiteCoinSignedBiasDitheredQuantizerOneSided q)
    (hnot : ¬ CountIndependentWithinToleranceOutput (Ω := Bool × (Coin × Dither))
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin × Dither))
      (finiteCoinOutput (finiteCoinOutputWithDither r)) τ) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Bool × (Coin × Dither))
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin × Dither))
      (finiteCoinOutput (finiteCoinSignedBiasDitheredQuantizedRecoding r q)) τ := by
  intro hpost
  have hpost_le :
      countIndependentWithinOutputDefect (Ω := Bool × (Coin × Dither))
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Coin × Dither))
        (finiteCoinOutput (finiteCoinSignedBiasDitheredQuantizedRecoding r q)) ≤ τ :=
    (countIndependentWithinToleranceOutput_iff_outputDefect_le
      (fun _ω : Bool × (Coin × Dither) => True)
      (finiteCoinSourceTrue (Coin := Coin × Dither))
      (finiteCoinOutput (finiteCoinSignedBiasDitheredQuantizedRecoding r q)) τ).mp hpost
  have horig_le :
      countIndependentWithinOutputDefect (Ω := Bool × (Coin × Dither))
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Coin × Dither))
        (finiteCoinOutput (finiteCoinOutputWithDither r)) ≤ τ := by
    exact le_trans
      (countIndependentWithinOutputDefect_finiteCoinOutputWithDither_le_of_finiteCoinSignedBiasDitheredQuantizerOneSided
        r q hone)
      hpost_le
  exact hnot
    ((countIndependentWithinToleranceOutput_iff_outputDefect_le
      (fun _ω : Bool × (Coin × Dither) => True)
      (finiteCoinSourceTrue (Coin := Coin × Dither))
      (finiteCoinOutput (finiteCoinOutputWithDither r)) τ).mpr horig_le)

/-- So if dithered signed-bias quantization strictly lowers the finite-coin
output defect, the quantizer cannot be one-sided. -/
theorem not_finiteCoinSignedBiasDitheredQuantizerOneSided_of_quantizedOutput_outputDefect_lt
    {Coin α Dither β : Type*} [Fintype Coin] [Fintype Dither]
    [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq Dither] [DecidableEq β]
    (r : Bool → Coin → α) (q : Int × Dither → β)
    (hlt : countIndependentWithinOutputDefect (Ω := Bool × (Coin × Dither))
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin × Dither))
      (finiteCoinOutput (finiteCoinSignedBiasDitheredQuantizedRecoding r q)) <
      countIndependentWithinOutputDefect (Ω := Bool × (Coin × Dither))
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Coin × Dither))
        (finiteCoinOutput (finiteCoinOutputWithDither r))) :
    ¬ finiteCoinSignedBiasDitheredQuantizerOneSided q := by
  intro hone
  exact (Nat.not_lt_of_ge
    (countIndependentWithinOutputDefect_finiteCoinOutputWithDither_le_of_finiteCoinSignedBiasDitheredQuantizerOneSided
      r q hone)) hlt

/-- The same one-sided-dithered-quantizer obstruction in tolerance form. -/
theorem not_finiteCoinSignedBiasDitheredQuantizerOneSided_of_quantizedOutput_tolerance_of_not_tolerance
    {Coin α Dither β : Type*} [Fintype Coin] [Fintype Dither]
    [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq Dither] [DecidableEq β]
    (r : Bool → Coin → α) (q : Int × Dither → β) (τ : Nat)
    (hpost : CountIndependentWithinToleranceOutput (Ω := Bool × (Coin × Dither))
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin × Dither))
      (finiteCoinOutput (finiteCoinSignedBiasDitheredQuantizedRecoding r q)) τ)
    (hnot : ¬ CountIndependentWithinToleranceOutput (Ω := Bool × (Coin × Dither))
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin × Dither))
      (finiteCoinOutput (finiteCoinOutputWithDither r)) τ) :
    ¬ finiteCoinSignedBiasDitheredQuantizerOneSided q := by
  intro hone
  exact
    not_countIndependentWithinToleranceOutput_finiteCoinSignedBiasDitheredQuantizedRecoding_of_not_tolerance_of_oneSided
      r q τ hone hnot hpost

/-- If dithered signed-bias quantization strictly lowers the finite-coin output
defect, then one quantizer bucket contains both a positive-bias output/seed
pair and a negative-bias output/seed pair. -/
theorem exists_oppositeSign_ditheredQuantizerCollision_of_quantizedOutput_outputDefect_lt
    {Coin α Dither β : Type*} [Fintype Coin] [Fintype Dither]
    [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq Dither] [DecidableEq β]
    (r : Bool → Coin → α) (q : Int × Dither → β)
    (hlt : countIndependentWithinOutputDefect (Ω := Bool × (Coin × Dither))
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin × Dither))
      (finiteCoinOutput (finiteCoinSignedBiasDitheredQuantizedRecoding r q)) <
      countIndependentWithinOutputDefect (Ω := Bool × (Coin × Dither))
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Coin × Dither))
        (finiteCoinOutput (finiteCoinOutputWithDither r))) :
    ∃ yPos yNeg : α, ∃ dPos dNeg : Dither,
      q (finiteCoinSignedFiberBias r yPos, dPos) =
        q (finiteCoinSignedFiberBias r yNeg, dNeg) ∧
        0 < finiteCoinSignedFiberBias r yPos ∧
          finiteCoinSignedFiberBias r yNeg < 0 := by
  rcases
      exists_oppositeSign_observedOutput_collision_of_postcompose_outputDefect_lt
        (r := finiteCoinOutputWithDither r)
        (g := fun yd => q (finiteCoinSignedFiberBias r yd.1, yd.2))
        hlt with
    ⟨⟨yPos, dPos⟩, ⟨yNeg, dNeg⟩, hq, _hne, hpos, hneg⟩
  refine ⟨yPos, yNeg, dPos, dNeg, hq, ?_, ?_⟩
  · rwa [finiteCoinSignedFiberBias_outputWithDither] at hpos
  · rwa [finiteCoinSignedFiberBias_outputWithDither] at hneg

/-- The same opposite-sign-bucket obstruction in tolerance form for dithered
finite quantization. -/
theorem exists_oppositeSign_ditheredQuantizerCollision_of_quantizedOutput_tolerance_of_not_tolerance
    {Coin α Dither β : Type*} [Fintype Coin] [Fintype Dither]
    [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq Dither] [DecidableEq β]
    (r : Bool → Coin → α) (q : Int × Dither → β) (τ : Nat)
    (hpost : CountIndependentWithinToleranceOutput (Ω := Bool × (Coin × Dither))
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin × Dither))
      (finiteCoinOutput (finiteCoinSignedBiasDitheredQuantizedRecoding r q)) τ)
    (hnot : ¬ CountIndependentWithinToleranceOutput (Ω := Bool × (Coin × Dither))
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin × Dither))
      (finiteCoinOutput (finiteCoinOutputWithDither r)) τ) :
    ∃ yPos yNeg : α, ∃ dPos dNeg : Dither,
      q (finiteCoinSignedFiberBias r yPos, dPos) =
        q (finiteCoinSignedFiberBias r yNeg, dNeg) ∧
        0 < finiteCoinSignedFiberBias r yPos ∧
          finiteCoinSignedFiberBias r yNeg < 0 := by
  rcases
      exists_oppositeSign_observedOutput_collision_of_postcompose_tolerance_of_not_tolerance
        (r := finiteCoinOutputWithDither r)
        (g := fun yd => q (finiteCoinSignedFiberBias r yd.1, yd.2))
        τ hpost hnot with
    ⟨⟨yPos, dPos⟩, ⟨yNeg, dNeg⟩, hq, _hne, hpos, hneg⟩
  refine ⟨yPos, yNeg, dPos, dNeg, hq, ?_, ?_⟩
  · rwa [finiteCoinSignedFiberBias_outputWithDither] at hpos
  · rwa [finiteCoinSignedFiberBias_outputWithDither] at hneg

end Mettapedia.Computability.PNP
