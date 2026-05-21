import Mettapedia.Computability.PNP.FiniteCoinToleranceQuantization

/-!
# P vs NP grassroots: finite-coin postprocessing foundations

The finite-coin source-erasure layer says that balanced fibers erase the source
bit from all decidable output predicates.  This file records how that behaves
under deterministic postprocessing of the output.

Exact erasure is stable under every deterministic postprocessing map.  For the
approximate finite-count API, a finite postprocessing map with output fibers of
size at most `m` converts tolerance `τ` into tolerance `m * τ`: coarsening may
aggregate defects, but only by the number of original output fibers being
merged.
-/

namespace Mettapedia.Computability.PNP

/-- The finite preimage of one postprocessed output value. -/
def finiteOutputPreimageFiber {α β : Type*} [Fintype α] [DecidableEq β]
    (g : α → β) (z : β) : Finset α :=
  (Finset.univ : Finset α).filter (fun y => g y = z)

/-- A deterministic finite-output postprocessing map has fibers of size at most
`m`. -/
def finiteOutputMapFiberCardBound {α β : Type*} [Fintype α] [DecidableEq β]
    (g : α → β) (m : Nat) : Prop :=
  ∀ z : β, (finiteOutputPreimageFiber g z).card ≤ m

/-- Every finite-output postprocessing map has the trivial fiber bound
`|α|`. -/
theorem finiteOutputMapFiberCardBound_card
    {α β : Type*} [Fintype α] [DecidableEq β] (g : α → β) :
    finiteOutputMapFiberCardBound g (Fintype.card α) := by
  intro z
  exact Finset.card_le_card (Finset.filter_subset (fun y => g y = z)
    (Finset.univ : Finset α))

/-- Predicate neutrality is preserved by deterministic postprocessing. -/
theorem finiteCoinOutputPredicateNeutral_postcompose
    {Coin α β : Type*} [Fintype Coin]
    (r : Bool → Coin → α) (g : α → β)
    (P : β → Prop) [DecidablePred P]
    (hneutral : finiteCoinOutputPredicateNeutral r (fun y => P (g y))) :
    finiteCoinOutputPredicateNeutral (fun b c => g (r b c)) P := by
  simpa [finiteCoinOutputPredicateNeutral] using hneutral

/-- Predicate erasure is preserved by deterministic postprocessing. -/
theorem finiteCoinOutputPredicateErasing_postcompose
    {Coin α β : Type*} [Fintype Coin]
    (r : Bool → Coin → α) (g : α → β)
    (herase : FiniteCoinOutputPredicateErasing r) :
    FiniteCoinOutputPredicateErasing (fun b c => g (r b c)) := by
  intro P _hP
  exact finiteCoinOutputPredicateNeutral_postcompose r g P
    (herase (fun y => P (g y)))

/-- Balanced finite-coin fibers are preserved by deterministic postprocessing. -/
theorem finiteCoinRecodingFiberBalanced_postcompose
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hbal : FiniteCoinRecodingFiberBalanced r) :
    FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)) := by
  exact finiteCoinRecodingFiberBalanced_of_outputPredicateErasing
    (fun b c => g (r b c))
    (finiteCoinOutputPredicateErasing_postcompose r g
      (finiteCoinOutputPredicateErasing_of_fiberBalanced r hbal))

/-- The true-side fiber count is unchanged by an injective deterministic
postprocessing map. -/
theorem coinTrueFiberCount_postcompose_injective
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hinj : Function.Injective g) (y : α) :
    coinTrueFiberCount (fun b c => g (r b c)) (g y) =
      coinTrueFiberCount r y := by
  apply le_antisymm
  · simpa [coinTrueFiberCount] using
      (finiteEventCount_le_of_imp (Ω := Coin)
        (fun c h => hinj h))
  · simpa [coinTrueFiberCount] using
      (finiteEventCount_le_of_imp (Ω := Coin)
        (fun c h => by simp [h]))

/-- The false-side fiber count is unchanged by an injective deterministic
postprocessing map. -/
theorem coinFalseFiberCount_postcompose_injective
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hinj : Function.Injective g) (y : α) :
    coinFalseFiberCount (fun b c => g (r b c)) (g y) =
      coinFalseFiberCount r y := by
  apply le_antisymm
  · simpa [coinFalseFiberCount] using
      (finiteEventCount_le_of_imp (Ω := Coin)
        (fun c h => hinj h))
  · simpa [coinFalseFiberCount] using
      (finiteEventCount_le_of_imp (Ω := Coin)
        (fun c h => by simp [h]))

/-- Injective deterministic postprocessing cannot create balanced finite-coin
fibers that were not already present before postprocessing. -/
theorem finiteCoinRecodingFiberBalanced_of_postcompose_injective
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hinj : Function.Injective g)
    (hbal : FiniteCoinRecodingFiberBalanced (fun b c => g (r b c))) :
    FiniteCoinRecodingFiberBalanced r := by
  intro y
  have hpost := hbal (g y)
  have htrue := coinTrueFiberCount_postcompose_injective r g hinj y
  have hfalse := coinFalseFiberCount_postcompose_injective r g hinj y
  calc
    coinTrueFiberCount r y =
        coinTrueFiberCount (fun b c => g (r b c)) (g y) := htrue.symm
    _ = coinFalseFiberCount (fun b c => g (r b c)) (g y) := hpost
    _ = coinFalseFiberCount r y := hfalse

/-- For injective deterministic postprocessing, balanced finite-coin fibers are
exactly preserved.  Lossless recoding therefore cannot be the step that repairs
an unbalanced finite-coin source/output relation. -/
theorem finiteCoinRecodingFiberBalanced_postcompose_iff_of_injective
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hinj : Function.Injective g) :
    FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)) ↔
      FiniteCoinRecodingFiberBalanced r := by
  constructor
  · exact finiteCoinRecodingFiberBalanced_of_postcompose_injective r g hinj
  · exact finiteCoinRecodingFiberBalanced_postcompose r g

/-- A postprocessor with a left inverse on the actually observed finite-coin
outputs cannot create balanced fibers that were not already present.  This
blocks the repair where a many-to-one coarsening is claimed to preserve the
original recoding on the proof-relevant samples. -/
theorem finiteCoinRecodingFiberBalanced_of_postcompose_observedLeftInverse
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) (recover : β → α)
    (hrecover : ∀ b c, recover (g (r b c)) = r b c)
    (hbal : FiniteCoinRecodingFiberBalanced (fun b c => g (r b c))) :
    FiniteCoinRecodingFiberBalanced r := by
  have herase :
      FiniteCoinOutputPredicateErasing (fun b c => g (r b c)) :=
    finiteCoinOutputPredicateErasing_of_fiberBalanced
      (fun b c => g (r b c)) hbal
  intro y
  have hpred := herase (fun z => recover z = y)
  have htrue :
      finiteEventCount Coin (fun c => recover (g (r true c)) = y) =
        coinTrueFiberCount r y := by
    apply le_antisymm
    · simpa [coinTrueFiberCount] using
        (finiteEventCount_le_of_imp (Ω := Coin)
          (fun c h => by
            rw [hrecover true c] at h
            exact h))
    · simpa [coinTrueFiberCount] using
        (finiteEventCount_le_of_imp (Ω := Coin)
          (fun c h => by
            rw [hrecover true c]
            exact h))
  have hfalse :
      finiteEventCount Coin (fun c => recover (g (r false c)) = y) =
        coinFalseFiberCount r y := by
    apply le_antisymm
    · simpa [coinFalseFiberCount] using
        (finiteEventCount_le_of_imp (Ω := Coin)
          (fun c h => by
            rw [hrecover false c] at h
            exact h))
    · simpa [coinFalseFiberCount] using
        (finiteEventCount_le_of_imp (Ω := Coin)
          (fun c h => by
            rw [hrecover false c]
            exact h))
  calc
    coinTrueFiberCount r y =
        finiteEventCount Coin (fun c => recover (g (r true c)) = y) :=
          htrue.symm
    _ = finiteEventCount Coin (fun c => recover (g (r false c)) = y) := hpred
    _ = coinFalseFiberCount r y := hfalse

/-- For postprocessors with a left inverse on the observed finite-coin samples,
balanced fibers are exactly preserved.  Non-injective postprocessing can only
repair an imbalance by losing original-output information on the observed
support. -/
theorem finiteCoinRecodingFiberBalanced_postcompose_iff_of_observedLeftInverse
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) (recover : β → α)
    (hrecover : ∀ b c, recover (g (r b c)) = r b c) :
    FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)) ↔
      FiniteCoinRecodingFiberBalanced r := by
  constructor
  · exact finiteCoinRecodingFiberBalanced_of_postcompose_observedLeftInverse
      r g recover hrecover
  · exact finiteCoinRecodingFiberBalanced_postcompose r g

/-- A postprocessor that is injective on the actually observed finite-coin
outputs cannot create balanced fibers that were not already present.  This is
weaker than global injectivity and avoids choosing an explicit recovery map:
only collisions on the finite observed support matter. -/
theorem finiteCoinRecodingFiberBalanced_of_postcompose_observedInjective
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hinjObs :
      ∀ b1 c1 b2 c2,
        g (r b1 c1) = g (r b2 c2) → r b1 c1 = r b2 c2)
    (hbal : FiniteCoinRecodingFiberBalanced (fun b c => g (r b c))) :
    FiniteCoinRecodingFiberBalanced r := by
  intro y
  by_cases hobs : ∃ b : Bool, ∃ c : Coin, r b c = y
  · rcases hobs with ⟨b0, c0, hy⟩
    have htrue :
        coinTrueFiberCount (fun b c => g (r b c)) (g y) =
          coinTrueFiberCount r y := by
      apply le_antisymm
      · simpa [coinTrueFiberCount] using
          (finiteEventCount_le_of_imp (Ω := Coin)
            (fun c h => by
              have hgy : g (r true c) = g (r b0 c0) := by
                simpa [hy] using h
              exact (hinjObs true c b0 c0 hgy).trans hy))
      · simpa [coinTrueFiberCount] using
          (finiteEventCount_le_of_imp (Ω := Coin)
            (fun c h => by simp [h]))
    have hfalse :
        coinFalseFiberCount (fun b c => g (r b c)) (g y) =
          coinFalseFiberCount r y := by
      apply le_antisymm
      · simpa [coinFalseFiberCount] using
          (finiteEventCount_le_of_imp (Ω := Coin)
            (fun c h => by
              have hgy : g (r false c) = g (r b0 c0) := by
                simpa [hy] using h
              exact (hinjObs false c b0 c0 hgy).trans hy))
      · simpa [coinFalseFiberCount] using
          (finiteEventCount_le_of_imp (Ω := Coin)
            (fun c h => by simp [h]))
    calc
      coinTrueFiberCount r y =
          coinTrueFiberCount (fun b c => g (r b c)) (g y) := htrue.symm
      _ = coinFalseFiberCount (fun b c => g (r b c)) (g y) := hbal (g y)
      _ = coinFalseFiberCount r y := hfalse
  · have htrue_zero : coinTrueFiberCount r y = 0 := by
      exact finiteEventCount_zero_of_forall_not (Ω := Coin)
        (fun c => r true c = y)
        (fun c hc => hobs ⟨true, c, hc⟩)
    have hfalse_zero : coinFalseFiberCount r y = 0 := by
      exact finiteEventCount_zero_of_forall_not (Ω := Coin)
        (fun c => r false c = y)
        (fun c hc => hobs ⟨false, c, hc⟩)
    rw [htrue_zero, hfalse_zero]

/-- For postprocessors injective on the observed finite-coin support, balanced
fibers are exactly preserved.  Hence postprocessing can repair an imbalance
only by creating a collision between distinct observed original outputs. -/
theorem finiteCoinRecodingFiberBalanced_postcompose_iff_of_observedInjective
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hinjObs :
      ∀ b1 c1 b2 c2,
        g (r b1 c1) = g (r b2 c2) → r b1 c1 = r b2 c2) :
    FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)) ↔
      FiniteCoinRecodingFiberBalanced r := by
  constructor
  · exact finiteCoinRecodingFiberBalanced_of_postcompose_observedInjective
      r g hinjObs
  · exact finiteCoinRecodingFiberBalanced_postcompose r g

/-- On any actually observed output value, an observed-support-injective
postprocessor preserves the true-side fiber count exactly. -/
theorem coinTrueFiberCount_postcompose_observedInjective
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hinjObs :
      ∀ b1 c1 b2 c2,
        g (r b1 c1) = g (r b2 c2) → r b1 c1 = r b2 c2)
    {y : α} (hobs : ∃ b : Bool, ∃ c : Coin, r b c = y) :
    coinTrueFiberCount (fun b c => g (r b c)) (g y) =
      coinTrueFiberCount r y := by
  rcases hobs with ⟨b0, c0, hy⟩
  apply le_antisymm
  · simpa [coinTrueFiberCount] using
      (finiteEventCount_le_of_imp (Ω := Coin)
        (fun c h => by
          have hgy : g (r true c) = g (r b0 c0) := by
            simpa [hy] using h
          exact (hinjObs true c b0 c0 hgy).trans hy))
  · simpa [coinTrueFiberCount] using
      (finiteEventCount_le_of_imp (Ω := Coin)
        (fun c h => by simp [h]))

/-- On any actually observed output value, an observed-support-injective
postprocessor preserves the false-side fiber count exactly. -/
theorem coinFalseFiberCount_postcompose_observedInjective
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hinjObs :
      ∀ b1 c1 b2 c2,
        g (r b1 c1) = g (r b2 c2) → r b1 c1 = r b2 c2)
    {y : α} (hobs : ∃ b : Bool, ∃ c : Coin, r b c = y) :
    coinFalseFiberCount (fun b c => g (r b c)) (g y) =
      coinFalseFiberCount r y := by
  rcases hobs with ⟨b0, c0, hy⟩
  apply le_antisymm
  · simpa [coinFalseFiberCount] using
      (finiteEventCount_le_of_imp (Ω := Coin)
        (fun c h => by
          have hgy : g (r false c) = g (r b0 c0) := by
            simpa [hy] using h
          exact (hinjObs false c b0 c0 hgy).trans hy))
  · simpa [coinFalseFiberCount] using
      (finiteEventCount_le_of_imp (Ω := Coin)
        (fun c h => by simp [h]))

/-- On the finite-coin output surface, postprocessing that is injective on the
observed support preserves the whole tolerance certificate exactly.  Lossless
coarsening on the proof-relevant support cannot reduce the required
approximation budget. -/
theorem countIndependentWithinToleranceOutput_finiteCoinOutput_postcompose_iff_of_observedInjective
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) (τ : Nat)
    (hinjObs :
      ∀ b1 c1 b2 c2,
        g (r b1 c1) = g (r b2 c2) → r b1 c1 = r b2 c2) :
    CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput (fun b c => g (r b c))) τ ↔
    CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput r) τ := by
  rw [countIndependentWithinToleranceOutput_finiteCoinOutput_iff_forall_scaled_fiberImbalance_le,
    countIndependentWithinToleranceOutput_finiteCoinOutput_iff_forall_scaled_fiberImbalance_le]
  constructor
  · intro h y
    by_cases hobs : ∃ b : Bool, ∃ c : Coin, r b c = y
    · have htrue :=
        coinTrueFiberCount_postcompose_observedInjective r g hinjObs hobs
      have hfalse :=
        coinFalseFiberCount_postcompose_observedInjective r g hinjObs hobs
      have himb :
          finiteCoinFiberImbalance (fun b c => g (r b c)) (g y) =
            finiteCoinFiberImbalance r y := by
        simp [finiteCoinFiberImbalance, htrue, hfalse]
      simpa [himb] using h (g y)
    · have htrue_zero : coinTrueFiberCount r y = 0 := by
        exact finiteEventCount_zero_of_forall_not (Ω := Coin)
          (fun c => r true c = y)
          (fun c hc => hobs ⟨true, c, hc⟩)
      have hfalse_zero : coinFalseFiberCount r y = 0 := by
        exact finiteEventCount_zero_of_forall_not (Ω := Coin)
          (fun c => r false c = y)
          (fun c hc => hobs ⟨false, c, hc⟩)
      simp [finiteCoinFiberImbalance, htrue_zero, hfalse_zero]
  · intro h z
    by_cases hobs :
        ∃ b : Bool, ∃ c : Coin, g (r b c) = z
    · rcases hobs with ⟨b0, c0, hz⟩
      let y := r b0 c0
      have hyobs : ∃ b : Bool, ∃ c : Coin, r b c = y := ⟨b0, c0, rfl⟩
      have htrue :=
        coinTrueFiberCount_postcompose_observedInjective r g hinjObs hyobs
      have hfalse :=
        coinFalseFiberCount_postcompose_observedInjective r g hinjObs hyobs
      have hz' : z = g y := by
        simpa [y] using hz.symm
      subst z
      have himb :
          finiteCoinFiberImbalance (fun b c => g (r b c)) (g y) =
            finiteCoinFiberImbalance r y := by
        simp [finiteCoinFiberImbalance, htrue, hfalse]
      simpa [y, himb] using h y
    · have htrue_zero :
          coinTrueFiberCount (fun b c => g (r b c)) z = 0 := by
        exact finiteEventCount_zero_of_forall_not (Ω := Coin)
          (fun c => g (r true c) = z)
          (fun c hc => hobs ⟨true, c, hc⟩)
      have hfalse_zero :
          coinFalseFiberCount (fun b c => g (r b c)) z = 0 := by
        exact finiteEventCount_zero_of_forall_not (Ω := Coin)
          (fun c => g (r false c) = z)
          (fun c hc => hobs ⟨false, c, hc⟩)
      simp [finiteCoinFiberImbalance, htrue_zero, hfalse_zero]

/-- An observed left inverse on the actually observed outputs gives the same
exact tolerance preservation as observed injectivity. -/
theorem countIndependentWithinToleranceOutput_finiteCoinOutput_postcompose_iff_of_observedLeftInverse
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) (recover : β → α) (τ : Nat)
    (hrecover : ∀ b c, recover (g (r b c)) = r b c) :
    CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput (fun b c => g (r b c))) τ ↔
    CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput r) τ := by
  have hinjObs :
      ∀ b1 c1 b2 c2,
        g (r b1 c1) = g (r b2 c2) → r b1 c1 = r b2 c2 := by
    intro b1 c1 b2 c2 hEq
    calc
      r b1 c1 = recover (g (r b1 c1)) := (hrecover b1 c1).symm
      _ = recover (g (r b2 c2)) := by rw [hEq]
      _ = r b2 c2 := hrecover b2 c2
  exact
    countIndependentWithinToleranceOutput_finiteCoinOutput_postcompose_iff_of_observedInjective
      r g τ hinjObs

/-- For finite output types, observed-support-injective postprocessing
preserves the whole max output defect exactly. -/
theorem countIndependentWithinOutputDefect_finiteCoinOutput_postcompose_eq_of_observedInjective
    {Coin α β : Type*} [Fintype Coin] [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hinjObs :
      ∀ b1 c1 b2 c2,
        g (r b1 c1) = g (r b2 c2) → r b1 c1 = r b2 c2) :
    countIndependentWithinOutputDefect (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput (fun b c => g (r b c))) =
    countIndependentWithinOutputDefect (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput r) := by
  apply le_antisymm
  · let D :=
      countIndependentWithinOutputDefect (Ω := Bool × Coin)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (finiteCoinOutput r)
    have hpost :
        CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
          (fun _ω => True)
          (finiteCoinSourceTrue (Coin := Coin))
          (finiteCoinOutput (fun b c => g (r b c))) D := by
      exact
        (countIndependentWithinToleranceOutput_finiteCoinOutput_postcompose_iff_of_observedInjective
          r g D hinjObs).2
        ((countIndependentWithinToleranceOutput_iff_outputDefect_le
          (fun _ω : Bool × Coin => True)
          (finiteCoinSourceTrue (Coin := Coin))
          (finiteCoinOutput r) D).mpr le_rfl)
    exact
      (countIndependentWithinToleranceOutput_iff_outputDefect_le
        (fun _ω : Bool × Coin => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (finiteCoinOutput (fun b c => g (r b c))) D).mp hpost
  · let D :=
      countIndependentWithinOutputDefect (Ω := Bool × Coin)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (finiteCoinOutput (fun b c => g (r b c)))
    have horig :
        CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
          (fun _ω => True)
          (finiteCoinSourceTrue (Coin := Coin))
          (finiteCoinOutput r) D := by
      exact
        (countIndependentWithinToleranceOutput_finiteCoinOutput_postcompose_iff_of_observedInjective
          r g D hinjObs).1
        ((countIndependentWithinToleranceOutput_iff_outputDefect_le
          (fun _ω : Bool × Coin => True)
          (finiteCoinSourceTrue (Coin := Coin))
          (finiteCoinOutput (fun b c => g (r b c))) D).mpr le_rfl)
    exact
      (countIndependentWithinToleranceOutput_iff_outputDefect_le
        (fun _ω : Bool × Coin => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (finiteCoinOutput r) D).mp horig

/-- An observed left inverse on the actually observed outputs also preserves
the max output defect exactly. -/
theorem countIndependentWithinOutputDefect_finiteCoinOutput_postcompose_eq_of_observedLeftInverse
    {Coin α β : Type*} [Fintype Coin] [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) (recover : β → α)
    (hrecover : ∀ b c, recover (g (r b c)) = r b c) :
    countIndependentWithinOutputDefect (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput (fun b c => g (r b c))) =
    countIndependentWithinOutputDefect (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput r) := by
  have hinjObs :
      ∀ b1 c1 b2 c2,
        g (r b1 c1) = g (r b2 c2) → r b1 c1 = r b2 c2 := by
    intro b1 c1 b2 c2 hEq
    calc
      r b1 c1 = recover (g (r b1 c1)) := (hrecover b1 c1).symm
      _ = recover (g (r b2 c2)) := by rw [hEq]
      _ = r b2 c2 := hrecover b2 c2
  exact
    countIndependentWithinOutputDefect_finiteCoinOutput_postcompose_eq_of_observedInjective
      r g hinjObs

/-- If postprocessing creates balanced fibers from an originally unbalanced
finite-coin recoding, then it must identify two distinct observed original
outputs.  This is the collision-level obstruction for many-to-one coarsening
repairs. -/
theorem exists_observedOutput_collision_of_postcompose_fiberBalanced_of_not_fiberBalanced
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hbal : FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)))
    (hnot : ¬ FiniteCoinRecodingFiberBalanced r) :
    ∃ b1 : Bool, ∃ c1 : Coin, ∃ b2 : Bool, ∃ c2 : Coin,
      r b1 c1 ≠ r b2 c2 ∧ g (r b1 c1) = g (r b2 c2) := by
  by_contra hnone
  apply hnot
  exact finiteCoinRecodingFiberBalanced_of_postcompose_observedInjective
    r g
    (fun b1 c1 b2 c2 hEq => by
      by_contra hne
      exact hnone ⟨b1, c1, b2, c2, hne, hEq⟩)
    hbal

/-- Under injective deterministic postprocessing, predicate erasure is exactly
preserved.  Any repair that creates erasure by postprocessing must therefore
use a genuinely many-to-one map. -/
theorem finiteCoinOutputPredicateErasing_postcompose_iff_of_injective
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hinj : Function.Injective g) :
    FiniteCoinOutputPredicateErasing (fun b c => g (r b c)) ↔
      FiniteCoinOutputPredicateErasing r := by
  constructor
  · intro herase
    exact finiteCoinOutputPredicateErasing_of_fiberBalanced r
      (finiteCoinRecodingFiberBalanced_of_postcompose_injective r g hinj
        ((finiteCoinRecodingFiberBalanced_iff_outputPredicateErasing
          (fun b c => g (r b c))).mpr herase))
  · exact finiteCoinOutputPredicateErasing_postcompose r g

/-- If a postprocessor is injective on the observed finite-coin support,
predicate erasure after postprocessing is equivalent to predicate erasure before
postprocessing. -/
theorem finiteCoinOutputPredicateErasing_postcompose_iff_of_observedInjective
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hinjObs :
      ∀ b1 c1 b2 c2,
        g (r b1 c1) = g (r b2 c2) → r b1 c1 = r b2 c2) :
    FiniteCoinOutputPredicateErasing (fun b c => g (r b c)) ↔
      FiniteCoinOutputPredicateErasing r := by
  constructor
  · intro herase
    exact finiteCoinOutputPredicateErasing_of_fiberBalanced r
      (finiteCoinRecodingFiberBalanced_of_postcompose_observedInjective
        r g hinjObs
        ((finiteCoinRecodingFiberBalanced_iff_outputPredicateErasing
          (fun b c => g (r b c))).mpr herase))
  · exact finiteCoinOutputPredicateErasing_postcompose r g

/-- If a postprocessor has a left inverse on the observed finite-coin samples,
predicate erasure after postprocessing is equivalent to predicate erasure before
postprocessing. -/
theorem finiteCoinOutputPredicateErasing_postcompose_iff_of_observedLeftInverse
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) (recover : β → α)
    (hrecover : ∀ b c, recover (g (r b c)) = r b c) :
    FiniteCoinOutputPredicateErasing (fun b c => g (r b c)) ↔
      FiniteCoinOutputPredicateErasing r := by
  constructor
  · intro herase
    exact finiteCoinOutputPredicateErasing_of_fiberBalanced r
      (finiteCoinRecodingFiberBalanced_of_postcompose_observedLeftInverse
        r g recover hrecover
        ((finiteCoinRecodingFiberBalanced_iff_outputPredicateErasing
          (fun b c => g (r b c))).mpr herase))
  · exact finiteCoinOutputPredicateErasing_postcompose r g

/-- A constant output is always balanced: this is the degenerate many-to-one
postprocessing endpoint that erases all finite-coin source information. -/
theorem finiteCoinRecodingFiberBalanced_constant
    {Coin β : Type*} [Fintype Coin] [DecidableEq β] (z : β) :
    FiniteCoinRecodingFiberBalanced (fun _b (_c : Coin) => z) := by
  intro y
  rfl

/-- The true-side fiber count after postprocessing is the sum of the true-side
counts over the original outputs merged into that postprocessed value. -/
theorem coinTrueFiberCount_postcompose_eq_sum_preimage
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) (z : β) :
    coinTrueFiberCount (fun b c => g (r b c)) z =
      ∑ y ∈ finiteOutputPreimageFiber g z, coinTrueFiberCount r y := by
  classical
  simpa [finiteOutputPreimageFiber, coinTrueFiberCount] using
    (finiteEventCount_comp_eq_sum_fibers_of_mapsTo
      (fun c : Coin => r true c)
      (Finset.univ : Finset α)
      (fun y : α => g y = z)
      (by intro c; simp))

/-- The false-side fiber count after postprocessing is the sum of the false-side
counts over the original outputs merged into that postprocessed value. -/
theorem coinFalseFiberCount_postcompose_eq_sum_preimage
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) (z : β) :
    coinFalseFiberCount (fun b c => g (r b c)) z =
      ∑ y ∈ finiteOutputPreimageFiber g z, coinFalseFiberCount r y := by
  classical
  simpa [finiteOutputPreimageFiber, coinFalseFiberCount] using
    (finiteEventCount_comp_eq_sum_fibers_of_mapsTo
      (fun c : Coin => r false c)
      (Finset.univ : Finset α)
      (fun y : α => g y = z)
      (by intro c; simp))

/-- The signed true-minus-false finite-coin fiber bias.  Balance is exactly the
vanishing of this integer-valued bias at every output. -/
def finiteCoinSignedFiberBias {Coin α : Type*} [Fintype Coin]
    [DecidableEq α] (r : Bool → Coin → α) (y : α) : Int :=
  (coinTrueFiberCount r y : Int) - (coinFalseFiberCount r y : Int)

/-- The signed bias of a postprocessed output is the sum of the signed biases
of the original outputs merged into it. -/
theorem finiteCoinSignedFiberBias_postcompose_eq_sum_preimage
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) (z : β) :
    finiteCoinSignedFiberBias (fun b c => g (r b c)) z =
      ∑ y ∈ finiteOutputPreimageFiber g z, finiteCoinSignedFiberBias r y := by
  classical
  unfold finiteCoinSignedFiberBias
  rw [coinTrueFiberCount_postcompose_eq_sum_preimage r g z,
    coinFalseFiberCount_postcompose_eq_sum_preimage r g z]
  simp [Nat.cast_sum, Finset.sum_sub_distrib]

/-- Balanced finite-coin fibers are exactly the outputs with zero signed bias. -/
theorem finiteCoinRecodingFiberBalanced_iff_forall_signedFiberBias_eq_zero
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) :
    FiniteCoinRecodingFiberBalanced r ↔
      ∀ y : α, finiteCoinSignedFiberBias r y = 0 := by
  constructor
  · intro h y
    simp [finiteCoinSignedFiberBias, h y]
  · intro h y
    have hz := h y
    unfold finiteCoinSignedFiberBias at hz
    omega

/-- If deterministic postprocessing has balanced fibers, then every
postprocessed fiber has exact zero total signed original bias. -/
theorem finiteCoinSignedFiberBias_sum_preimage_eq_zero_of_postcompose_fiberBalanced
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hbal : FiniteCoinRecodingFiberBalanced (fun b c => g (r b c))) (z : β) :
    (∑ y ∈ finiteOutputPreimageFiber g z, finiteCoinSignedFiberBias r y) = 0 := by
  rw [← finiteCoinSignedFiberBias_postcompose_eq_sum_preimage r g z]
  exact
    (finiteCoinRecodingFiberBalanced_iff_forall_signedFiberBias_eq_zero
      (fun b c => g (r b c))).mp hbal z

/-- Deterministic postprocessing creates balanced finite-coin fibers exactly
when every postprocessed fiber has zero total signed original bias.  Any repair
via coarsening must therefore supply exact cancellation in every merged fiber,
not merely a collision. -/
theorem finiteCoinRecodingFiberBalanced_postcompose_iff_forall_sum_signedFiberBias_preimage_eq_zero
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) :
    FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)) ↔
      ∀ z : β,
        (∑ y ∈ finiteOutputPreimageFiber g z,
          finiteCoinSignedFiberBias r y) = 0 := by
  rw [finiteCoinRecodingFiberBalanced_iff_forall_signedFiberBias_eq_zero
    (fun b c => g (r b c))]
  constructor
  · intro h z
    have hz := h z
    rw [finiteCoinSignedFiberBias_postcompose_eq_sum_preimage r g z] at hz
    exact hz
  · intro h z
    rw [finiteCoinSignedFiberBias_postcompose_eq_sum_preimage r g z]
    exact h z

/-- If a true-heavy original output becomes part of a balanced postprocessed
fiber, that same postprocessed fiber must contain a false-heavy original
output.  Thus a successful coarsening repair cannot use only same-bias
collisions. -/
theorem exists_falseHeavy_output_in_postprocessedFiber_of_trueHeavy
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) {yTrue : α}
    (hbal : FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)))
    (hheavy : coinFalseFiberCount r yTrue < coinTrueFiberCount r yTrue) :
    ∃ yFalse : α,
      g yFalse = g yTrue ∧ yFalse ≠ yTrue ∧
        coinTrueFiberCount r yFalse < coinFalseFiberCount r yFalse := by
  classical
  let s := finiteOutputPreimageFiber g (g yTrue)
  by_contra hnone
  have hle :
      ∀ y ∈ s, coinFalseFiberCount r y ≤ coinTrueFiberCount r y := by
    intro y hy
    by_cases hyEq : y = yTrue
    · subst y
      exact Nat.le_of_lt hheavy
    · exact le_of_not_gt (fun hgt => by
        have hgy : g y = g yTrue := by
          simpa [s, finiteOutputPreimageFiber] using hy
        exact hnone ⟨y, hgy, hyEq, hgt⟩)
  have hyTrueMem : yTrue ∈ s := by
    simp [s, finiteOutputPreimageFiber]
  have hsum_lt :
      (∑ y ∈ s, coinFalseFiberCount r y) <
        ∑ y ∈ s, coinTrueFiberCount r y := by
    exact Finset.sum_lt_sum hle ⟨yTrue, hyTrueMem, hheavy⟩
  have htrue := coinTrueFiberCount_postcompose_eq_sum_preimage r g (g yTrue)
  have hfalse := coinFalseFiberCount_postcompose_eq_sum_preimage r g (g yTrue)
  have hsum_eq :
      (∑ y ∈ s, coinTrueFiberCount r y) =
        ∑ y ∈ s, coinFalseFiberCount r y := by
    calc
      (∑ y ∈ s, coinTrueFiberCount r y)
          = coinTrueFiberCount (fun b c => g (r b c)) (g yTrue) := by
            simpa [s] using htrue.symm
      _ = coinFalseFiberCount (fun b c => g (r b c)) (g yTrue) :=
            hbal (g yTrue)
      _ = ∑ y ∈ s, coinFalseFiberCount r y := by
            simpa [s] using hfalse
  rw [hsum_eq] at hsum_lt
  exact (Nat.lt_irrefl _) hsum_lt

/-- The symmetric form: if a false-heavy original output becomes part of a
balanced postprocessed fiber, that same postprocessed fiber must contain a
true-heavy original output. -/
theorem exists_trueHeavy_output_in_postprocessedFiber_of_falseHeavy
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) {yFalse : α}
    (hbal : FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)))
    (hheavy : coinTrueFiberCount r yFalse < coinFalseFiberCount r yFalse) :
    ∃ yTrue : α,
      g yTrue = g yFalse ∧ yTrue ≠ yFalse ∧
        coinFalseFiberCount r yTrue < coinTrueFiberCount r yTrue := by
  classical
  let s := finiteOutputPreimageFiber g (g yFalse)
  by_contra hnone
  have hle :
      ∀ y ∈ s, coinTrueFiberCount r y ≤ coinFalseFiberCount r y := by
    intro y hy
    by_cases hyEq : y = yFalse
    · subst y
      exact Nat.le_of_lt hheavy
    · exact le_of_not_gt (fun hgt => by
        have hgy : g y = g yFalse := by
          simpa [s, finiteOutputPreimageFiber] using hy
        exact hnone ⟨y, hgy, hyEq, hgt⟩)
  have hyFalseMem : yFalse ∈ s := by
    simp [s, finiteOutputPreimageFiber]
  have hsum_lt :
      (∑ y ∈ s, coinTrueFiberCount r y) <
        ∑ y ∈ s, coinFalseFiberCount r y := by
    exact Finset.sum_lt_sum hle ⟨yFalse, hyFalseMem, hheavy⟩
  have htrue := coinTrueFiberCount_postcompose_eq_sum_preimage r g (g yFalse)
  have hfalse := coinFalseFiberCount_postcompose_eq_sum_preimage r g (g yFalse)
  have hsum_eq :
      (∑ y ∈ s, coinTrueFiberCount r y) =
        ∑ y ∈ s, coinFalseFiberCount r y := by
    calc
      (∑ y ∈ s, coinTrueFiberCount r y)
          = coinTrueFiberCount (fun b c => g (r b c)) (g yFalse) := by
            simpa [s] using htrue.symm
      _ = coinFalseFiberCount (fun b c => g (r b c)) (g yFalse) :=
            hbal (g yFalse)
      _ = ∑ y ∈ s, coinFalseFiberCount r y := by
            simpa [s] using hfalse
  rw [hsum_eq] at hsum_lt
  exact (Nat.lt_irrefl _) hsum_lt

/-- If postprocessing balances an originally unbalanced finite-coin recoding,
then some postprocessed fiber must merge a true-heavy original output with a
false-heavy original output.  This is stronger than mere non-injectivity: the
repair must cancel opposite source biases inside one postprocessed value. -/
theorem exists_oppositeBias_observedOutput_collision_of_postcompose_fiberBalanced_of_not_fiberBalanced
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hbal : FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)))
    (hnot : ¬ FiniteCoinRecodingFiberBalanced r) :
    ∃ yTrue yFalse : α,
      g yTrue = g yFalse ∧ yTrue ≠ yFalse ∧
        coinFalseFiberCount r yTrue < coinTrueFiberCount r yTrue ∧
          coinTrueFiberCount r yFalse < coinFalseFiberCount r yFalse := by
  have hnotall :
      ¬ ∀ y : α, coinTrueFiberCount r y = coinFalseFiberCount r y := hnot
  rcases not_forall.mp hnotall with ⟨y, hne⟩
  rcases lt_or_gt_of_ne hne with htf | hft
  · rcases exists_trueHeavy_output_in_postprocessedFiber_of_falseHeavy
      r g hbal htf with ⟨yTrue, hgy, hne', htrueHeavy⟩
    exact ⟨yTrue, y, hgy, hne', htrueHeavy, htf⟩
  · rcases exists_falseHeavy_output_in_postprocessedFiber_of_trueHeavy
      r g hbal hft with ⟨yFalse, hgy, hne', hfalseHeavy⟩
    exact ⟨y, yFalse, hgy.symm, (fun h => hne' h.symm), hft, hfalseHeavy⟩

/-- A postprocessed fiber's unsigned imbalance is bounded by the sum of the
unsigned imbalances of the original fibers merged into it. -/
theorem finiteCoinFiberImbalance_postcompose_le_sum_preimage
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) (z : β) :
    finiteCoinFiberImbalance (fun b c => g (r b c)) z ≤
      ∑ y ∈ finiteOutputPreimageFiber g z, finiteCoinFiberImbalance r y := by
  classical
  let s := finiteOutputPreimageFiber g z
  have htrue := coinTrueFiberCount_postcompose_eq_sum_preimage r g z
  have hfalse := coinFalseFiberCount_postcompose_eq_sum_preimage r g z
  have hleft :
      (∑ y ∈ s, coinTrueFiberCount r y) -
          (∑ y ∈ s, coinFalseFiberCount r y) ≤
        ∑ y ∈ s, finiteCoinFiberImbalance r y := by
    have hsum :
        (∑ y ∈ s, coinTrueFiberCount r y) ≤
          (∑ y ∈ s, coinFalseFiberCount r y) +
            ∑ y ∈ s, finiteCoinFiberImbalance r y := by
      calc
        (∑ y ∈ s, coinTrueFiberCount r y)
            ≤ ∑ y ∈ s,
                (coinFalseFiberCount r y + finiteCoinFiberImbalance r y) := by
              refine Finset.sum_le_sum ?_
              intro y _hy
              have hgap :
                  coinTrueFiberCount r y - coinFalseFiberCount r y ≤
                    finiteCoinFiberImbalance r y := by
                exact le_max_left _ _
              omega
        _ = (∑ y ∈ s, coinFalseFiberCount r y) +
              ∑ y ∈ s, finiteCoinFiberImbalance r y := by
            rw [Finset.sum_add_distrib]
    omega
  have hright :
      (∑ y ∈ s, coinFalseFiberCount r y) -
          (∑ y ∈ s, coinTrueFiberCount r y) ≤
        ∑ y ∈ s, finiteCoinFiberImbalance r y := by
    have hsum :
        (∑ y ∈ s, coinFalseFiberCount r y) ≤
          (∑ y ∈ s, coinTrueFiberCount r y) +
            ∑ y ∈ s, finiteCoinFiberImbalance r y := by
      calc
        (∑ y ∈ s, coinFalseFiberCount r y)
            ≤ ∑ y ∈ s,
                (coinTrueFiberCount r y + finiteCoinFiberImbalance r y) := by
              refine Finset.sum_le_sum ?_
              intro y _hy
              have hgap :
                  coinFalseFiberCount r y - coinTrueFiberCount r y ≤
                    finiteCoinFiberImbalance r y := by
                exact le_max_right _ _
              omega
        _ = (∑ y ∈ s, coinTrueFiberCount r y) +
              ∑ y ∈ s, finiteCoinFiberImbalance r y := by
            rw [Finset.sum_add_distrib]
    omega
  unfold finiteCoinFiberImbalance
  rw [htrue, hfalse]
  exact max_le hleft hright

/-- Deterministic postprocessing with fibers of size at most `m` turns
finite-coin output tolerance `τ` into tolerance `m * τ`. -/
theorem countIndependentWithinToleranceOutput_finiteCoinOutput_postcompose
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) {m τ : Nat}
    (hbound : finiteOutputMapFiberCardBound g m)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput r) τ) :
    CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput (fun b c => g (r b c))) (m * τ) := by
  classical
  refine
    (countIndependentWithinToleranceOutput_finiteCoinOutput_iff_forall_scaled_fiberImbalance_le
      (fun b c => g (r b c)) (m * τ)).mpr ?_
  intro z
  let s := finiteOutputPreimageFiber g z
  have himb := finiteCoinFiberImbalance_postcompose_le_sum_preimage r g z
  have hscaled :
      ∀ y : α, Fintype.card Coin * finiteCoinFiberImbalance r y ≤ τ :=
    (countIndependentWithinToleranceOutput_finiteCoinOutput_iff_forall_scaled_fiberImbalance_le
      r τ).mp happrox
  calc
    Fintype.card Coin *
        finiteCoinFiberImbalance (fun b c => g (r b c)) z
        ≤ Fintype.card Coin *
            (∑ y ∈ s, finiteCoinFiberImbalance r y) :=
          Nat.mul_le_mul_left (Fintype.card Coin) himb
    _ = ∑ y ∈ s, Fintype.card Coin * finiteCoinFiberImbalance r y := by
          rw [Finset.mul_sum]
    _ ≤ ∑ _y ∈ s, τ := by
          refine Finset.sum_le_sum ?_
          intro y _hy
          exact hscaled y
    _ = s.card * τ := by
          simp [Nat.mul_comm]
    _ ≤ m * τ := by
          exact Nat.mul_le_mul_right τ (by simpa [s] using hbound z)

/-- The trivial finite-output bound: postprocessing by any map out of `α`
turns tolerance `τ` into tolerance `|α| * τ`. -/
theorem countIndependentWithinToleranceOutput_finiteCoinOutput_postcompose_card
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) {τ : Nat}
    (happrox : CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput r) τ) :
    CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput (fun b c => g (r b c))) (Fintype.card α * τ) :=
  countIndependentWithinToleranceOutput_finiteCoinOutput_postcompose
    r g (finiteOutputMapFiberCardBound_card g) happrox

/-- Finite-output max defect obeys the same finite-preimage postprocessing
bound as the pointwise tolerance certificate. -/
theorem countIndependentWithinOutputDefect_finiteCoinOutput_postcompose_le
    {Coin α β : Type*} [Fintype Coin] [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) {m : Nat}
    (hbound : finiteOutputMapFiberCardBound g m) :
    countIndependentWithinOutputDefect (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput (fun b c => g (r b c))) ≤
    m *
      countIndependentWithinOutputDefect (Ω := Bool × Coin)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (finiteCoinOutput r) := by
  let D :=
    countIndependentWithinOutputDefect (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput r)
  have happrox :
      CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (finiteCoinOutput r) D := by
    exact (countIndependentWithinToleranceOutput_iff_outputDefect_le
      (fun _ω : Bool × Coin => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput r) D).mpr le_rfl
  have hpost :
      CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (finiteCoinOutput (fun b c => g (r b c))) (m * D) :=
    countIndependentWithinToleranceOutput_finiteCoinOutput_postcompose
      r g hbound happrox
  exact (countIndependentWithinToleranceOutput_iff_outputDefect_le
    (fun _ω : Bool × Coin => True)
    (finiteCoinSourceTrue (Coin := Coin))
    (finiteCoinOutput (fun b c => g (r b c))) (m * D)).mp hpost

/-- With the trivial finite-output bound, any deterministic postprocessing by a
map out of `α` multiplies max defect by at most `|α|`. -/
theorem countIndependentWithinOutputDefect_finiteCoinOutput_postcompose_le_card
    {Coin α β : Type*} [Fintype Coin] [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) :
    countIndependentWithinOutputDefect (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput (fun b c => g (r b c))) ≤
    Fintype.card α *
      countIndependentWithinOutputDefect (Ω := Bool × Coin)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (finiteCoinOutput r) :=
  countIndependentWithinOutputDefect_finiteCoinOutput_postcompose_le
    r g (finiteOutputMapFiberCardBound_card g)

end Mettapedia.Computability.PNP
