import Mettapedia.Computability.PNP.FiniteCoinPostprocessingImprovementObstruction

/-!
# P vs NP grassroots: same-sign postprocessing obstruction

The previous finite-coin postprocessing lane already shows that strict
postprocessing improvement forces some observed output collision.  This file
sharpens that obstruction.  A many-to-one map that merges only one-sided
source biases inside each postprocessed fiber cannot strictly improve the
finite-coin output defect, and therefore cannot turn a failing tolerance-`τ`
certificate into a passing one.

Thus strict deterministic postprocessing improvement requires genuine
opposite-sign cancellation inside one merged output fiber.
-/

namespace Mettapedia.Computability.PNP

/-- The unsigned imbalance of one finite-coin output fiber is the absolute
value of its signed true-minus-false bias. -/
theorem finiteCoinFiberImbalance_eq_natAbs_signedFiberBias
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (y : α) :
    finiteCoinFiberImbalance r y = Int.natAbs (finiteCoinSignedFiberBias r y) := by
  by_cases htf : coinFalseFiberCount r y ≤ coinTrueFiberCount r y
  · simp [finiteCoinFiberImbalance, finiteCoinSignedFiberBias,
      Nat.sub_eq_zero_of_le htf,
      Int.natAbs_natCast_sub_natCast_of_ge htf]
  · have hft : coinTrueFiberCount r y ≤ coinFalseFiberCount r y := le_of_not_ge htf
    simp [finiteCoinFiberImbalance, finiteCoinSignedFiberBias,
      Nat.sub_eq_zero_of_le hft,
      Int.natAbs_natCast_sub_natCast_of_le hft]

/-- Every postprocessed fiber is one-sided in signed source bias: all original
outputs merged into the fiber are either nonnegative-bias or nonpositive-bias.
-/
def finiteOutputFiberSignedBiasOneSided
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) : Prop :=
  ∀ z : β,
    (∀ y ∈ finiteOutputPreimageFiber g z, 0 ≤ finiteCoinSignedFiberBias r y) ∨
      (∀ y ∈ finiteOutputPreimageFiber g z, finiteCoinSignedFiberBias r y ≤ 0)

/-- If no postprocessed fiber contains both a positive-bias and a negative-bias
original output, then every postprocessed fiber is one-sided in signed bias. -/
theorem finiteOutputFiberSignedBiasOneSided_of_no_oppositeSignObservedOutputCollision
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hnone :
      ¬ ∃ yPos yNeg : α,
        g yPos = g yNeg ∧
          0 < finiteCoinSignedFiberBias r yPos ∧
            finiteCoinSignedFiberBias r yNeg < 0) :
    finiteOutputFiberSignedBiasOneSided r g := by
  classical
  intro z
  by_cases hpos :
      ∃ y : α, y ∈ finiteOutputPreimageFiber g z ∧
        0 < finiteCoinSignedFiberBias r y
  · rcases hpos with ⟨yPos, hyPos, hPosBias⟩
    left
    intro y hy
    by_contra hnonneg
    have hNegBias : finiteCoinSignedFiberBias r y < 0 := lt_of_not_ge hnonneg
    have hEq : g yPos = g y := by
      have hyPos' : g yPos = z := by
        simpa [finiteOutputPreimageFiber] using hyPos
      have hy' : g y = z := by
        simpa [finiteOutputPreimageFiber] using hy
      exact hyPos'.trans hy'.symm
    exact hnone ⟨yPos, y, hEq, hPosBias, hNegBias⟩
  · right
    intro y hy
    by_contra hnonpos
    have hPosBias : 0 < finiteCoinSignedFiberBias r y := lt_of_not_ge hnonpos
    exact hpos ⟨y, hy, hPosBias⟩

/-- On a postprocessed fiber whose original signed biases are all nonnegative,
the postprocessed imbalance is the sum of the original imbalances. -/
theorem finiteCoinFiberImbalance_postcompose_eq_sum_preimage_of_nonneg_signedBias
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) (z : β)
    (hnonneg :
      ∀ y ∈ finiteOutputPreimageFiber g z, 0 ≤ finiteCoinSignedFiberBias r y) :
    finiteCoinFiberImbalance (fun b c => g (r b c)) z =
      ∑ y ∈ finiteOutputPreimageFiber g z, finiteCoinFiberImbalance r y := by
  apply Int.ofNat.inj
  rw [finiteCoinFiberImbalance_eq_natAbs_signedFiberBias,
    finiteCoinSignedFiberBias_postcompose_eq_sum_preimage]
  have hsum_nonneg :
      0 ≤ ∑ y ∈ finiteOutputPreimageFiber g z, finiteCoinSignedFiberBias r y := by
    exact Finset.sum_nonneg hnonneg
  have hleft :
      (((∑ y ∈ finiteOutputPreimageFiber g z,
          finiteCoinSignedFiberBias r y).natAbs : Nat) : Int) =
        ∑ y ∈ finiteOutputPreimageFiber g z, finiteCoinSignedFiberBias r y :=
    Int.natAbs_of_nonneg hsum_nonneg
  calc
    (Int.ofNat
        (∑ y ∈ finiteOutputPreimageFiber g z, finiteCoinSignedFiberBias r y).natAbs : Int) =
        ∑ y ∈ finiteOutputPreimageFiber g z, finiteCoinSignedFiberBias r y := by
          simpa using hleft
    _ =
        ∑ y ∈ finiteOutputPreimageFiber g z, ↑(finiteCoinFiberImbalance r y) := by
          refine Finset.sum_congr rfl ?_
          intro y hy
          rw [finiteCoinFiberImbalance_eq_natAbs_signedFiberBias,
            Int.natAbs_of_nonneg (hnonneg y hy)]
    _ = (↑(∑ y ∈ finiteOutputPreimageFiber g z, finiteCoinFiberImbalance r y) : Int) := by
          symm
          rw [Nat.cast_sum]

/-- On a postprocessed fiber whose original signed biases are all nonpositive,
the postprocessed imbalance is again the sum of the original imbalances. -/
theorem finiteCoinFiberImbalance_postcompose_eq_sum_preimage_of_nonpos_signedBias
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) (z : β)
    (hnonpos :
      ∀ y ∈ finiteOutputPreimageFiber g z, finiteCoinSignedFiberBias r y ≤ 0) :
    finiteCoinFiberImbalance (fun b c => g (r b c)) z =
      ∑ y ∈ finiteOutputPreimageFiber g z, finiteCoinFiberImbalance r y := by
  apply Int.ofNat.inj
  rw [finiteCoinFiberImbalance_eq_natAbs_signedFiberBias,
    finiteCoinSignedFiberBias_postcompose_eq_sum_preimage]
  have hsum_nonpos :
      (∑ y ∈ finiteOutputPreimageFiber g z, finiteCoinSignedFiberBias r y) ≤ 0 := by
    exact Finset.sum_nonpos hnonpos
  have hleft :
      (((∑ y ∈ finiteOutputPreimageFiber g z,
          finiteCoinSignedFiberBias r y).natAbs : Nat) : Int) =
        -(∑ y ∈ finiteOutputPreimageFiber g z, finiteCoinSignedFiberBias r y) :=
    Int.ofNat_natAbs_of_nonpos hsum_nonpos
  calc
    (Int.ofNat
        (∑ y ∈ finiteOutputPreimageFiber g z, finiteCoinSignedFiberBias r y).natAbs : Int) =
        -(∑ y ∈ finiteOutputPreimageFiber g z, finiteCoinSignedFiberBias r y) := by
          simpa using hleft
    _ =
        ∑ y ∈ finiteOutputPreimageFiber g z, -(finiteCoinSignedFiberBias r y) := by
          rw [Finset.sum_neg_distrib]
    _ = ∑ y ∈ finiteOutputPreimageFiber g z, ↑(finiteCoinFiberImbalance r y) := by
          refine Finset.sum_congr rfl ?_
          intro y hy
          symm
          rw [finiteCoinFiberImbalance_eq_natAbs_signedFiberBias,
            Int.ofNat_natAbs_of_nonpos (hnonpos y hy)]
    _ = (↑(∑ y ∈ finiteOutputPreimageFiber g z, finiteCoinFiberImbalance r y) : Int) := by
          symm
          rw [Nat.cast_sum]

/-- If every postprocessed fiber is one-sided in signed bias, then every
original output imbalance is bounded by the imbalance of its postprocessed
image.  Same-sign merging cannot shrink fiber imbalance. -/
theorem finiteCoinFiberImbalance_le_postcompose_of_signedBiasOneSided
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hcoh : finiteOutputFiberSignedBiasOneSided r g) (y : α) :
    finiteCoinFiberImbalance r y ≤
      finiteCoinFiberImbalance (fun b c => g (r b c)) (g y) := by
  let s := finiteOutputPreimageFiber g (g y)
  have hyMem : y ∈ s := by
    simp [s, finiteOutputPreimageFiber]
  have hsum_ge :
      finiteCoinFiberImbalance r y ≤ ∑ y' ∈ s, finiteCoinFiberImbalance r y' := by
    simpa [s] using
      (Finset.single_le_sum
        (f := fun y' => finiteCoinFiberImbalance r y')
        (fun _ _ => Nat.zero_le _)
        hyMem)
  rcases hcoh (g y) with hnonneg | hnonpos
  · calc
      finiteCoinFiberImbalance r y ≤ ∑ y' ∈ s, finiteCoinFiberImbalance r y' := hsum_ge
      _ = finiteCoinFiberImbalance (fun b c => g (r b c)) (g y) := by
            symm
            exact finiteCoinFiberImbalance_postcompose_eq_sum_preimage_of_nonneg_signedBias
              r g (g y) hnonneg
  · calc
      finiteCoinFiberImbalance r y ≤ ∑ y' ∈ s, finiteCoinFiberImbalance r y' := hsum_ge
      _ = finiteCoinFiberImbalance (fun b c => g (r b c)) (g y) := by
            symm
            exact finiteCoinFiberImbalance_postcompose_eq_sum_preimage_of_nonpos_signedBias
              r g (g y) hnonpos

/-- If every postprocessed fiber is one-sided in signed bias, deterministic
postprocessing cannot strictly lower the finite-coin output defect. -/
theorem countIndependentWithinOutputDefect_finiteCoinOutput_le_of_signedBiasOneSided
    {Coin α β : Type*} [Fintype Coin] [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hcoh : finiteOutputFiberSignedBiasOneSided r g) :
    countIndependentWithinOutputDefect (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput r) ≤
    countIndependentWithinOutputDefect (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput (fun b c => g (r b c))) := by
  classical
  rw [countIndependentWithinOutputDefect_finiteCoinOutput_eq_sup_scaled_fiberImbalance,
    countIndependentWithinOutputDefect_finiteCoinOutput_eq_sup_scaled_fiberImbalance]
  refine Finset.sup_le ?_
  intro y _hy
  calc
    Fintype.card Coin * finiteCoinFiberImbalance r y ≤
        Fintype.card Coin *
          finiteCoinFiberImbalance (fun b c => g (r b c)) (g y) :=
      Nat.mul_le_mul_left _
        (finiteCoinFiberImbalance_le_postcompose_of_signedBiasOneSided r g hcoh y)
    _ ≤ (Finset.univ : Finset β).sup
          (fun z => Fintype.card Coin *
            finiteCoinFiberImbalance (fun b c => g (r b c)) z) :=
      Finset.le_sup
        (s := (Finset.univ : Finset β))
        (f := fun z => Fintype.card Coin *
          finiteCoinFiberImbalance (fun b c => g (r b c)) z)
        (Finset.mem_univ (g y))

/-- If deterministic postprocessing strictly lowers the finite-coin output
defect, then some postprocessed fiber must merge a positive-bias original
output with a negative-bias original output.  Same-sign collisions cannot
explain quantitative improvement. -/
theorem exists_oppositeSign_observedOutput_collision_of_postcompose_outputDefect_lt
    {Coin α β : Type*} [Fintype Coin] [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hlt : countIndependentWithinOutputDefect (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput (fun b c => g (r b c))) <
      countIndependentWithinOutputDefect (Ω := Bool × Coin)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (finiteCoinOutput r)) :
    ∃ yPos yNeg : α,
      g yPos = g yNeg ∧ yPos ≠ yNeg ∧
        0 < finiteCoinSignedFiberBias r yPos ∧
          finiteCoinSignedFiberBias r yNeg < 0 := by
  by_contra hnone
  have hnoneWeak :
      ¬ ∃ yPos yNeg : α,
        g yPos = g yNeg ∧
          0 < finiteCoinSignedFiberBias r yPos ∧
            finiteCoinSignedFiberBias r yNeg < 0 := by
    intro h
    rcases h with ⟨yPos, yNeg, hEq, hPos, hNeg⟩
    have hne : yPos ≠ yNeg := by
      intro hsame
      subst yNeg
      linarith
    exact hnone ⟨yPos, yNeg, hEq, hne, hPos, hNeg⟩
  have hcoh :=
    finiteOutputFiberSignedBiasOneSided_of_no_oppositeSignObservedOutputCollision
      r g hnoneWeak
  have hle :=
    countIndependentWithinOutputDefect_finiteCoinOutput_le_of_signedBiasOneSided
      r g hcoh
  exact (Nat.not_lt_of_ge hle) hlt

/-- The same mixed-sign cancellation obstruction in tolerance form: if
postprocessing makes a fixed tolerance-`τ` certificate newly true, then some
postprocessed fiber must merge a positive-bias original output with a
negative-bias original output. -/
theorem exists_oppositeSign_observedOutput_collision_of_postcompose_tolerance_of_not_tolerance
    {Coin α β : Type*} [Fintype Coin] [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) (τ : Nat)
    (hpost : CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput (fun b c => g (r b c))) τ)
    (hnot : ¬ CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput r) τ) :
    ∃ yPos yNeg : α,
      g yPos = g yNeg ∧ yPos ≠ yNeg ∧
        0 < finiteCoinSignedFiberBias r yPos ∧
          finiteCoinSignedFiberBias r yNeg < 0 := by
  have hpost_le :
      countIndependentWithinOutputDefect (Ω := Bool × Coin)
          (fun _ω => True)
          (finiteCoinSourceTrue (Coin := Coin))
          (finiteCoinOutput (fun b c => g (r b c))) ≤ τ :=
    (countIndependentWithinToleranceOutput_iff_outputDefect_le
      (fun _ω : Bool × Coin => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput (fun b c => g (r b c))) τ).mp hpost
  have horig_not_le :
      ¬ countIndependentWithinOutputDefect (Ω := Bool × Coin)
          (fun _ω => True)
          (finiteCoinSourceTrue (Coin := Coin))
          (finiteCoinOutput r) ≤ τ := by
    intro hle
    exact hnot
      ((countIndependentWithinToleranceOutput_iff_outputDefect_le
        (fun _ω : Bool × Coin => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (finiteCoinOutput r) τ).mpr hle)
  have horig_lt :
      τ <
        countIndependentWithinOutputDefect (Ω := Bool × Coin)
          (fun _ω => True)
          (finiteCoinSourceTrue (Coin := Coin))
          (finiteCoinOutput r) :=
    Nat.lt_of_not_ge horig_not_le
  have hlt :
      countIndependentWithinOutputDefect (Ω := Bool × Coin)
          (fun _ω => True)
          (finiteCoinSourceTrue (Coin := Coin))
          (finiteCoinOutput (fun b c => g (r b c))) <
        countIndependentWithinOutputDefect (Ω := Bool × Coin)
          (fun _ω => True)
          (finiteCoinSourceTrue (Coin := Coin))
          (finiteCoinOutput r) :=
    lt_of_le_of_lt hpost_le horig_lt
  exact
    exists_oppositeSign_observedOutput_collision_of_postcompose_outputDefect_lt
      r g hlt

end Mettapedia.Computability.PNP
