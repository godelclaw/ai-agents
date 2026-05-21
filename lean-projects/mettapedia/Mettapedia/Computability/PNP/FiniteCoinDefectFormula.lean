import Mettapedia.Computability.PNP.FiniteCoinIndependenceBridge

/-!
# P vs NP grassroots: finite-coin output defect formula

`FiniteCoinIndependenceBridge` identifies balanced finite-coin fibers with
zero finite-count source/output defect on `Bool × Coin`.  This file quantifies
the same bridge: each output fiber's symmetric finite-count defect is exactly
`|Coin|` times the imbalance between its true-side and false-side coin counts.
-/

namespace Mettapedia.Computability.PNP

/-- The unsigned finite-coin imbalance of one output fiber. -/
def finiteCoinFiberImbalance {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (y : α) : Nat :=
  max (coinTrueFiberCount r y - coinFalseFiberCount r y)
    (coinFalseFiberCount r y - coinTrueFiberCount r y)

/-- One output fiber has zero imbalance exactly when its true-side and
false-side coin counts are equal. -/
theorem finiteCoinFiberImbalance_eq_zero_iff
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (y : α) :
    finiteCoinFiberImbalance r y = 0 ↔
      coinTrueFiberCount r y = coinFalseFiberCount r y := by
  let T := coinTrueFiberCount r y
  let F := coinFalseFiberCount r y
  constructor
  · intro h
    have hTF : T - F = 0 := by
      have hle : T - F ≤ 0 := by
        exact le_trans (le_max_left _ _) (le_of_eq h)
      omega
    have hFT : F - T = 0 := by
      have hle : F - T ≤ 0 := by
        exact le_trans (le_max_right _ _) (le_of_eq h)
      omega
    omega
  · intro h
    simp [finiteCoinFiberImbalance, h]

/-- Forward finite-count source/output defect of one finite-coin output fiber:
`|Coin|` times the positive true-minus-false fiber imbalance. -/
theorem countIndependentWithinForwardGap_finiteCoinOutput_fiber
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (y : α) :
    countIndependentWithinForwardGap (Ω := Bool × Coin)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (fun ω => finiteCoinOutput r ω = y) =
      Fintype.card Coin *
        (coinTrueFiberCount r y - coinFalseFiberCount r y) := by
  let n := Fintype.card Coin
  let T := coinTrueFiberCount r y
  let F := coinFalseFiberCount r y
  have hC :
      finiteEventCount (Bool × Coin) (fun _ω => True) = 2 * n := by
    simpa [n] using (finiteCoinSampleSpace_count (Coin := Coin))
  have hCE :
      finiteEventCount (Bool × Coin) (finiteCoinSourceTrue (Coin := Coin)) = n := by
    simpa [n] using (finiteCoinSourceTrue_count (Coin := Coin))
  have hCEF :
      finiteEventCount (Bool × Coin)
          (fun ω => finiteCoinSourceTrue (Coin := Coin) ω ∧
            finiteCoinOutput r ω = y) = T := by
    simpa [coinTrueFiberCount, T] using
      finiteCoinSourceTrue_outputPredicate_count r (fun z => z = y)
  have hCF :
      finiteEventCount (Bool × Coin) (fun ω => finiteCoinOutput r ω = y) =
        T + F := by
    simpa [coinTrueFiberCount, coinFalseFiberCount, T, F] using
      finiteCoinOutputPredicate_count r (fun z => z = y)
  calc
    countIndependentWithinForwardGap (Ω := Bool × Coin)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (fun ω => finiteCoinOutput r ω = y)
        = (2 * n) * T - n * (T + F) := by
          simp [countIndependentWithinForwardGap, hC, hCE, hCEF, hCF]
    _ = n * (T - F) := by
          calc
            (2 * n) * T - n * (T + F)
                = n * (2 * T) - n * (T + F) := by ring_nf
            _ = n * (2 * T - (T + F)) := by
                  rw [Nat.mul_sub_left_distrib]
            _ = n * (T - F) := by
                  have hsub : 2 * T - (T + F) = T - F := by
                    omega
                  rw [hsub]

/-- Backward finite-count source/output defect of one finite-coin output fiber:
`|Coin|` times the positive false-minus-true fiber imbalance. -/
theorem countIndependentWithinBackwardGap_finiteCoinOutput_fiber
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (y : α) :
    countIndependentWithinBackwardGap (Ω := Bool × Coin)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (fun ω => finiteCoinOutput r ω = y) =
      Fintype.card Coin *
        (coinFalseFiberCount r y - coinTrueFiberCount r y) := by
  let n := Fintype.card Coin
  let T := coinTrueFiberCount r y
  let F := coinFalseFiberCount r y
  have hC :
      finiteEventCount (Bool × Coin) (fun _ω => True) = 2 * n := by
    simpa [n] using (finiteCoinSampleSpace_count (Coin := Coin))
  have hCE :
      finiteEventCount (Bool × Coin) (finiteCoinSourceTrue (Coin := Coin)) = n := by
    simpa [n] using (finiteCoinSourceTrue_count (Coin := Coin))
  have hCEF :
      finiteEventCount (Bool × Coin)
          (fun ω => finiteCoinSourceTrue (Coin := Coin) ω ∧
            finiteCoinOutput r ω = y) = T := by
    simpa [coinTrueFiberCount, T] using
      finiteCoinSourceTrue_outputPredicate_count r (fun z => z = y)
  have hCF :
      finiteEventCount (Bool × Coin) (fun ω => finiteCoinOutput r ω = y) =
        T + F := by
    simpa [coinTrueFiberCount, coinFalseFiberCount, T, F] using
      finiteCoinOutputPredicate_count r (fun z => z = y)
  calc
    countIndependentWithinBackwardGap (Ω := Bool × Coin)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (fun ω => finiteCoinOutput r ω = y)
        = n * (T + F) - (2 * n) * T := by
          simp [countIndependentWithinBackwardGap, hC, hCE, hCEF, hCF]
    _ = n * (F - T) := by
          calc
            n * (T + F) - (2 * n) * T
                = n * (T + F) - n * (2 * T) := by ring_nf
            _ = n * ((T + F) - 2 * T) := by
                  rw [Nat.mul_sub_left_distrib]
            _ = n * (F - T) := by
                  have hsub : (T + F) - 2 * T = F - T := by
                    omega
                  rw [hsub]

/-- Symmetric finite-count source/output defect of one finite-coin output fiber:
`|Coin|` times the unsigned true/false coin-fiber imbalance. -/
theorem countIndependentWithinDefect_finiteCoinOutput_fiber
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (y : α) :
    countIndependentWithinDefect (Ω := Bool × Coin)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (fun ω => finiteCoinOutput r ω = y) =
      Fintype.card Coin * finiteCoinFiberImbalance r y := by
  let n := Fintype.card Coin
  let T := coinTrueFiberCount r y
  let F := coinFalseFiberCount r y
  simp [countIndependentWithinDefect,
    countIndependentWithinForwardGap_finiteCoinOutput_fiber,
    countIndependentWithinBackwardGap_finiteCoinOutput_fiber,
    finiteCoinFiberImbalance, max_mul_mul_left]

/-- Approximate output independence for a finite-coin output is exactly a
uniform bound on the scaled fiber imbalances. -/
theorem countIndependentWithinToleranceOutput_finiteCoinOutput_iff_forall_scaled_fiberImbalance_le
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (τ : Nat) :
    CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (finiteCoinOutput r) τ ↔
      ∀ y : α, Fintype.card Coin * finiteCoinFiberImbalance r y ≤ τ := by
  constructor
  · intro h y
    have hy :=
      (countIndependentWithinTolerance_iff_defect_le
        (fun _ω : Bool × Coin => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (fun ω => finiteCoinOutput r ω = y) τ).mp (h y)
    simpa [countIndependentWithinDefect_finiteCoinOutput_fiber] using hy
  · intro h y
    exact (countIndependentWithinTolerance_iff_defect_le
      (fun _ω : Bool × Coin => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (fun ω => finiteCoinOutput r ω = y) τ).mpr (by
        simpa [countIndependentWithinDefect_finiteCoinOutput_fiber] using h y)

/-- For finite output types, the maximum output defect is the maximum scaled
fiber imbalance over the output type. -/
theorem countIndependentWithinOutputDefect_finiteCoinOutput_eq_sup_scaled_fiberImbalance
    {Coin α : Type*} [Fintype Coin] [Fintype α] [DecidableEq α]
    (r : Bool → Coin → α) :
    countIndependentWithinOutputDefect (Ω := Bool × Coin)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (finiteCoinOutput r) =
      (Finset.univ : Finset α).sup
        (fun y => Fintype.card Coin * finiteCoinFiberImbalance r y) := by
  unfold countIndependentWithinOutputDefect
  refine Finset.sup_congr rfl ?_
  intro y _hy
  exact countIndependentWithinDefect_finiteCoinOutput_fiber r y

/-- Balanced finite-coin fibers are exactly zero imbalance in every output
fiber. -/
theorem finiteCoinRecodingFiberBalanced_iff_forall_fiberImbalance_eq_zero
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) :
    FiniteCoinRecodingFiberBalanced r ↔
      ∀ y : α, finiteCoinFiberImbalance r y = 0 := by
  constructor
  · intro h y
    exact (finiteCoinFiberImbalance_eq_zero_iff r y).mpr (h y)
  · intro h y
    exact (finiteCoinFiberImbalance_eq_zero_iff r y).mp (h y)

end Mettapedia.Computability.PNP
