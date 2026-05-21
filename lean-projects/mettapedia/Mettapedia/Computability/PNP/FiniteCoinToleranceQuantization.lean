import Mettapedia.Computability.PNP.FiniteCoinDefectFormula

/-!
# P vs NP grassroots: finite-coin tolerance quantization

`FiniteCoinDefectFormula` proves that a finite-coin output fiber's symmetric
finite-count source/output defect is exactly `|Coin|` times the unsigned
true/false fiber imbalance.  This file records the threshold consequence:
there is no nonzero finite-coin imbalance below one whole coin block of defect.

Thus, any output-independence tolerance strictly below `|Coin|` collapses back
to exact balanced fibers.  This is a bottom-up obstruction to repairing a
balanced-fiber finite-coin recoding by asking for only a very small approximate
independence slack.
-/

namespace Mettapedia.Computability.PNP

/-- A nonzero finite-coin fiber imbalance contributes at least one full
`|Coin|` block to the scaled finite-count defect. -/
theorem finiteCoin_card_le_scaled_fiberImbalance_of_ne_zero
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (y : α)
    (hne : finiteCoinFiberImbalance r y ≠ 0) :
    Fintype.card Coin ≤
      Fintype.card Coin * finiteCoinFiberImbalance r y := by
  have hpos : 0 < finiteCoinFiberImbalance r y := Nat.pos_of_ne_zero hne
  have hone : 1 ≤ finiteCoinFiberImbalance r y := hpos
  calc
    Fintype.card Coin = Fintype.card Coin * 1 := by simp
    _ ≤ Fintype.card Coin * finiteCoinFiberImbalance r y :=
      Nat.mul_le_mul_left (Fintype.card Coin) hone

/-- If a scaled finite-coin fiber imbalance is bounded by a tolerance smaller
than `|Coin|`, then the imbalance is zero. -/
theorem finiteCoinFiberImbalance_eq_zero_of_scaled_le_of_lt_card
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (y : α) {τ : Nat}
    (hle : Fintype.card Coin * finiteCoinFiberImbalance r y ≤ τ)
    (hlt : τ < Fintype.card Coin) :
    finiteCoinFiberImbalance r y = 0 := by
  by_contra hne
  have hcard_le :
      Fintype.card Coin ≤
        Fintype.card Coin * finiteCoinFiberImbalance r y :=
    finiteCoin_card_le_scaled_fiberImbalance_of_ne_zero r y hne
  exact (not_lt_of_ge (le_trans hcard_le hle)) hlt

/-- The same threshold statement, phrased directly as equality of the true and
false coin counts in one output fiber. -/
theorem finiteCoinFiberBalanced_of_scaled_fiberImbalance_le_of_lt_card
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (y : α) {τ : Nat}
    (hle : Fintype.card Coin * finiteCoinFiberImbalance r y ≤ τ)
    (hlt : τ < Fintype.card Coin) :
    coinTrueFiberCount r y = coinFalseFiberCount r y := by
  exact (finiteCoinFiberImbalance_eq_zero_iff r y).mp
    (finiteCoinFiberImbalance_eq_zero_of_scaled_le_of_lt_card r y hle hlt)

/-- Output independence of a finite-coin recoding at tolerance below `|Coin|`
forces exact balanced fibers. -/
theorem finiteCoinRecodingFiberBalanced_of_countIndependentWithinToleranceOutput_lt_card
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) {τ : Nat}
    (happrox : CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput r) τ)
    (hlt : τ < Fintype.card Coin) :
    FiniteCoinRecodingFiberBalanced r := by
  rw [finiteCoinRecodingFiberBalanced_iff_forall_fiberImbalance_eq_zero]
  intro y
  have hscaled :
      Fintype.card Coin * finiteCoinFiberImbalance r y ≤ τ :=
    (countIndependentWithinToleranceOutput_finiteCoinOutput_iff_forall_scaled_fiberImbalance_le
      r τ).mp happrox y
  exact finiteCoinFiberImbalance_eq_zero_of_scaled_le_of_lt_card r y hscaled hlt

/-- Below one coin block of tolerance, approximate output independence is
equivalent to exact balanced fibers. -/
theorem countIndependentWithinToleranceOutput_finiteCoinOutput_lt_card_iff_fiberBalanced
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) {τ : Nat}
    (hlt : τ < Fintype.card Coin) :
    CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput r) τ ↔
    FiniteCoinRecodingFiberBalanced r := by
  constructor
  · intro happrox
    exact finiteCoinRecodingFiberBalanced_of_countIndependentWithinToleranceOutput_lt_card
      r happrox hlt
  · intro hbal
    exact countIndependentWithinToleranceOutput_mono
      (fun _ω : Bool × Coin => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput r)
      (Nat.zero_le τ)
      ((finiteCoinRecodingFiberBalanced_iff_countIndependentWithinToleranceOutput_zero
        r).mp hbal)

/-- If a finite-output recoding has maximum output defect below `|Coin|`, then
its finite-coin fibers are exactly balanced. -/
theorem finiteCoinRecodingFiberBalanced_of_outputDefect_lt_card
    {Coin α : Type*} [Fintype Coin] [Fintype α] [DecidableEq α]
    (r : Bool → Coin → α)
    (hlt :
      countIndependentWithinOutputDefect (Ω := Bool × Coin)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (finiteCoinOutput r) < Fintype.card Coin) :
    FiniteCoinRecodingFiberBalanced r := by
  have happrox :
      CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (finiteCoinOutput r)
        (countIndependentWithinOutputDefect (Ω := Bool × Coin)
          (fun _ω => True)
          (finiteCoinSourceTrue (Coin := Coin))
          (finiteCoinOutput r)) := by
    exact (countIndependentWithinToleranceOutput_iff_outputDefect_le
      (fun _ω : Bool × Coin => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput r)
      (countIndependentWithinOutputDefect (Ω := Bool × Coin)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (finiteCoinOutput r))).mpr le_rfl
  exact finiteCoinRecodingFiberBalanced_of_countIndependentWithinToleranceOutput_lt_card
    r happrox hlt

/-- Conversely, any unbalanced finite-output finite-coin recoding has maximum
output defect at least `|Coin|`. -/
theorem card_le_outputDefect_of_not_finiteCoinRecodingFiberBalanced
    {Coin α : Type*} [Fintype Coin] [Fintype α] [DecidableEq α]
    (r : Bool → Coin → α)
    (hnot : ¬ FiniteCoinRecodingFiberBalanced r) :
    Fintype.card Coin ≤
      countIndependentWithinOutputDefect (Ω := Bool × Coin)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (finiteCoinOutput r) := by
  classical
  have hnotall : ¬ ∀ y : α, finiteCoinFiberImbalance r y = 0 := by
    intro hall
    exact hnot
      ((finiteCoinRecodingFiberBalanced_iff_forall_fiberImbalance_eq_zero r).mpr hall)
  rcases not_forall.mp hnotall with ⟨y, hy⟩
  calc
    Fintype.card Coin ≤ Fintype.card Coin * finiteCoinFiberImbalance r y :=
      finiteCoin_card_le_scaled_fiberImbalance_of_ne_zero r y hy
    _ ≤ (Finset.univ : Finset α).sup
        (fun z => Fintype.card Coin * finiteCoinFiberImbalance r z) :=
      Finset.le_sup
        (s := (Finset.univ : Finset α))
        (f := fun z => Fintype.card Coin * finiteCoinFiberImbalance r z)
        (Finset.mem_univ y)
    _ = countIndependentWithinOutputDefect (Ω := Bool × Coin)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (finiteCoinOutput r) := by
      rw [← countIndependentWithinOutputDefect_finiteCoinOutput_eq_sup_scaled_fiberImbalance r]

/-- For a nonempty finite coin space, finite-output defect below one coin block
is equivalent to exact balanced fibers. -/
theorem countIndependentWithinOutputDefect_lt_card_iff_fiberBalanced
    {Coin α : Type*} [Fintype Coin] [Nonempty Coin] [Fintype α] [DecidableEq α]
    (r : Bool → Coin → α) :
    countIndependentWithinOutputDefect (Ω := Bool × Coin)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (finiteCoinOutput r) < Fintype.card Coin ↔
      FiniteCoinRecodingFiberBalanced r := by
  constructor
  · intro hlt
    exact finiteCoinRecodingFiberBalanced_of_outputDefect_lt_card r hlt
  · intro hbal
    have hdef :
        countIndependentWithinOutputDefect (Ω := Bool × Coin)
          (fun _ω => True)
          (finiteCoinSourceTrue (Coin := Coin))
          (finiteCoinOutput r) = 0 :=
      (finiteCoinRecodingFiberBalanced_iff_countIndependentWithinOutputDefect_eq_zero
        r).mp hbal
    rw [hdef]
    exact Fintype.card_pos

end Mettapedia.Computability.PNP
