import Mettapedia.Computability.PNP.ResolutionDemandObstruction

/-!
# P vs NP crux: randomized residuals are still resolution-budgeted

A randomized residual object can be viewed as a deterministic residual side
channel on the product of the original finite sample space with a finite coin
space.  Therefore randomness does not evade the orbit-resolution obstruction:
positive advantage still forces positive joint mass where the coin-indexed
residual separates involution partners.
-/

namespace Mettapedia.Computability.PNP

section

variable {α Coin U V : Type*} [Fintype α] [Fintype Coin]

/-- Lift an involution on the source space to the product with a finite coin
space, leaving the coin unchanged. -/
def coinLiftInvolution (τ : α → α) : α × Coin → α × Coin :=
  fun xr => (τ xr.1, xr.2)

/-- Product weight for a source weight and a coin weight. -/
def productWeight (w : α → ℕ) (coinWeight : Coin → ℕ) : α × Coin → ℕ :=
  fun xr => w xr.1 * coinWeight xr.2

/-- The joint orbit-resolving mass of a randomized residual side channel. -/
noncomputable def randomizedResidualResolvedMass
    (τ : α → α) (v : α → Coin → V)
    (w : α → ℕ) (coinWeight : Coin → ℕ) : ℕ :=
  resolvedMass (coinLiftInvolution (Coin := Coin) τ)
    (fun xr : α × Coin => v xr.1 xr.2)
    (productWeight w coinWeight)

omit [Fintype α] [Fintype Coin] in
theorem coinLiftInvolution_involutive
    (τ : α → α) (hτ : Function.Involutive τ) :
    Function.Involutive (coinLiftInvolution (Coin := Coin) τ) := by
  intro xr
  cases xr
  simp [coinLiftInvolution, hτ _]

/-- Randomized residual advantage is bounded by the joint mass where the
coin-indexed residual separates involution partners. -/
theorem doubledAdvantage_randomizedResidual_le_resolvedMass
    (τ : α → α) (u : α → U) (v : α → Coin → V)
    (y : α → Bool) (w : α → ℕ) (coinWeight : Coin → ℕ)
    (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x) :
    doubledAdvantage
        (fun xr : α × Coin => (u xr.1, v xr.1 xr.2))
        (fun xr : α × Coin => y xr.1)
        (productWeight w coinWeight) h
      ≤ randomizedResidualResolvedMass τ v w coinWeight := by
  exact
    doubledAdvantage_pair_le_resolvedMass
      (τ := coinLiftInvolution (Coin := Coin) τ)
      (u := fun xr : α × Coin => u xr.1)
      (v := fun xr : α × Coin => v xr.1 xr.2)
      (y := fun xr : α × Coin => y xr.1)
      (w := productWeight w coinWeight)
      (h := h)
      (coinLiftInvolution_involutive (Coin := Coin) τ hτ)
      (fun xr => hu xr.1)
      (fun xr => hy xr.1)
      (fun xr => by
        cases xr
        simp [productWeight, coinLiftInvolution, hw])

/-- A claimed randomized-residual doubled advantage of at least `δ` forces at
least `δ` units of joint orbit-resolving mass. -/
theorem randomizedResidualResolvedMass_ge_of_le_doubledAdvantage
    (τ : α → α) (u : α → U) (v : α → Coin → V)
    (y : α → Bool) (w : α → ℕ) (coinWeight : Coin → ℕ)
    (h : U × V → Bool) (δ : ℕ)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hδ :
      δ ≤ doubledAdvantage
        (fun xr : α × Coin => (u xr.1, v xr.1 xr.2))
        (fun xr : α × Coin => y xr.1)
        (productWeight w coinWeight) h) :
    δ ≤ randomizedResidualResolvedMass τ v w coinWeight :=
  le_trans hδ <|
    doubledAdvantage_randomizedResidual_le_resolvedMass
      τ u v y w coinWeight h hτ hu hy hw

/-- If the randomized residual is coinwise unresolved, then its joint
orbit-resolving mass is zero. -/
theorem randomizedResidualResolvedMass_eq_zero_of_coinwise_unresolved
    (τ : α → α) (v : α → Coin → V)
    (w : α → ℕ) (coinWeight : Coin → ℕ)
    (hunresolved : ∀ x c, v (τ x) c = v x c) :
    randomizedResidualResolvedMass τ v w coinWeight = 0 := by
  classical
  unfold randomizedResidualResolvedMass resolvedMass outsideMass sliceMass
  apply Finset.sum_eq_zero
  intro xr _
  exfalso
  exact xr.2 (by
    dsimp [unresolvedBySideChannel, coinLiftInvolution]
    exact hunresolved xr.1.1 xr.1.2)

/-- If the randomized residual is unresolved on every positive joint
source/coin support point, then its joint orbit-resolving mass is zero. -/
theorem randomizedResidualResolvedMass_eq_zero_of_supportwise_unresolved
    (τ : α → α) (v : α → Coin → V)
    (w : α → ℕ) (coinWeight : Coin → ℕ)
    (hunresolved :
      ∀ x c, 0 < w x * coinWeight c → v (τ x) c = v x c) :
    randomizedResidualResolvedMass τ v w coinWeight = 0 := by
  classical
  unfold randomizedResidualResolvedMass resolvedMass outsideMass sliceMass
  apply Finset.sum_eq_zero
  intro xr _
  by_cases hpos : 0 < w xr.1.1 * coinWeight xr.1.2
  · exfalso
    exact xr.2 (by
      dsimp [unresolvedBySideChannel, coinLiftInvolution]
      exact hunresolved xr.1.1 xr.1.2 hpos)
  · have hzero : w xr.1.1 * coinWeight xr.1.2 = 0 :=
      Nat.eq_zero_of_not_pos hpos
    simp [productWeight, hzero]

/-- If the source support is fixed by the involution wherever it has positive
weight, then no randomized residual can resolve any positive joint mass. -/
theorem randomizedResidualResolvedMass_eq_zero_of_fixed_source_support
    (τ : α → α) (v : α → Coin → V)
    (w : α → ℕ) (coinWeight : Coin → ℕ)
    (hsupport : ∀ x, 0 < w x → τ x = x) :
    randomizedResidualResolvedMass τ v w coinWeight = 0 := by
  classical
  unfold randomizedResidualResolvedMass resolvedMass outsideMass sliceMass
  apply Finset.sum_eq_zero
  intro xr _
  by_cases hx : 0 < w xr.1.1
  · exfalso
    exact xr.2 (by
      dsimp [unresolvedBySideChannel, coinLiftInvolution]
      rw [hsupport xr.1.1 hx])
  · have hx0 : w xr.1.1 = 0 := Nat.eq_zero_of_not_pos hx
    simp [productWeight, hx0]

/-- Coinwise-unresolved randomized residuals cannot support positive doubled
advantage. -/
theorem not_pos_doubledAdvantage_randomizedResidual_of_coinwise_unresolved
    (τ : α → α) (u : α → U) (v : α → Coin → V)
    (y : α → Bool) (w : α → ℕ) (coinWeight : Coin → ℕ)
    (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hunresolved : ∀ x c, v (τ x) c = v x c) :
    ¬ 0 < doubledAdvantage
        (fun xr : α × Coin => (u xr.1, v xr.1 xr.2))
        (fun xr : α × Coin => y xr.1)
        (productWeight w coinWeight) h := by
  have hle :=
    doubledAdvantage_randomizedResidual_le_resolvedMass
      τ u v y w coinWeight h hτ hu hy hw
  have hzero :=
    randomizedResidualResolvedMass_eq_zero_of_coinwise_unresolved
      τ v w coinWeight hunresolved
  omega

/-- Supportwise-unresolved randomized residuals cannot support positive
doubled advantage. -/
theorem not_pos_doubledAdvantage_randomizedResidual_of_supportwise_unresolved
    (τ : α → α) (u : α → U) (v : α → Coin → V)
    (y : α → Bool) (w : α → ℕ) (coinWeight : Coin → ℕ)
    (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hunresolved :
      ∀ x c, 0 < w x * coinWeight c → v (τ x) c = v x c) :
    ¬ 0 < doubledAdvantage
        (fun xr : α × Coin => (u xr.1, v xr.1 xr.2))
        (fun xr : α × Coin => y xr.1)
        (productWeight w coinWeight) h := by
  have hle :=
    doubledAdvantage_randomizedResidual_le_resolvedMass
      τ u v y w coinWeight h hτ hu hy hw
  have hzero :=
    randomizedResidualResolvedMass_eq_zero_of_supportwise_unresolved
      τ v w coinWeight hunresolved
  omega

/-- If positive source weight only occurs at involution-fixed points, then no
randomized residual can support positive doubled advantage. -/
theorem not_pos_doubledAdvantage_randomizedResidual_of_fixed_source_support
    (τ : α → α) (u : α → U) (v : α → Coin → V)
    (y : α → Bool) (w : α → ℕ) (coinWeight : Coin → ℕ)
    (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hsupport : ∀ x, 0 < w x → τ x = x) :
    ¬ 0 < doubledAdvantage
        (fun xr : α × Coin => (u xr.1, v xr.1 xr.2))
        (fun xr : α × Coin => y xr.1)
        (productWeight w coinWeight) h := by
  have hle :=
    doubledAdvantage_randomizedResidual_le_resolvedMass
      τ u v y w coinWeight h hτ hu hy hw
  have hzero :=
    randomizedResidualResolvedMass_eq_zero_of_fixed_source_support
      τ v w coinWeight hsupport
  omega

/-- Strict half-accuracy advantage for a randomized residual forces positive
joint orbit-resolving mass. -/
theorem randomizedResidualResolvedMass_pos_of_total_lt_two_mul_weightedCorrectMass
    (τ : α → α) (u : α → U) (v : α → Coin → V)
    (y : α → Bool) (w : α → ℕ) (coinWeight : Coin → ℕ)
    (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv :
      weightedTotalMass (productWeight w coinWeight) <
        2 * weightedCorrectMass
          (fun xr : α × Coin => (u xr.1, v xr.1 xr.2))
          (fun xr : α × Coin => y xr.1)
          (productWeight w coinWeight) h) :
    0 < randomizedResidualResolvedMass τ v w coinWeight := by
  exact
    resolvedMass_pos_of_total_lt_two_mul_weightedCorrectMass_pair
      (τ := coinLiftInvolution (Coin := Coin) τ)
      (u := fun xr : α × Coin => u xr.1)
      (v := fun xr : α × Coin => v xr.1 xr.2)
      (y := fun xr : α × Coin => y xr.1)
      (w := productWeight w coinWeight)
      (h := h)
      (coinLiftInvolution_involutive (Coin := Coin) τ hτ)
      (fun xr => hu xr.1)
      (fun xr => hy xr.1)
      (fun xr => by
        cases xr
        simp [productWeight, coinLiftInvolution, hw])
      hadv

/-- If positive source weight only occurs at involution-fixed points, then no
randomized residual can beat half accuracy. -/
theorem not_total_lt_two_mul_weightedCorrectMass_randomizedResidual_of_fixed_source_support
    (τ : α → α) (u : α → U) (v : α → Coin → V)
    (y : α → Bool) (w : α → ℕ) (coinWeight : Coin → ℕ)
    (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hsupport : ∀ x, 0 < w x → τ x = x) :
    ¬ weightedTotalMass (productWeight w coinWeight) <
      2 * weightedCorrectMass
        (fun xr : α × Coin => (u xr.1, v xr.1 xr.2))
        (fun xr : α × Coin => y xr.1)
        (productWeight w coinWeight) h := by
  intro hadv
  have hpos :
      0 < randomizedResidualResolvedMass τ v w coinWeight :=
    randomizedResidualResolvedMass_pos_of_total_lt_two_mul_weightedCorrectMass
      τ u v y w coinWeight h hτ hu hy hw hadv
  have hzero :=
    randomizedResidualResolvedMass_eq_zero_of_fixed_source_support
      τ v w coinWeight hsupport
  omega

/-- Every positive randomized-residual doubled advantage witnesses positive
joint orbit-resolving mass. -/
theorem randomizedResidualResolvedMass_pos_of_pos_doubledAdvantage
    (τ : α → α) (u : α → U) (v : α → Coin → V)
    (y : α → Bool) (w : α → ℕ) (coinWeight : Coin → ℕ)
    (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv :
      0 < doubledAdvantage
        (fun xr : α × Coin => (u xr.1, v xr.1 xr.2))
        (fun xr : α × Coin => y xr.1)
        (productWeight w coinWeight) h) :
    0 < randomizedResidualResolvedMass τ v w coinWeight := by
  have hle :=
    doubledAdvantage_randomizedResidual_le_resolvedMass
      τ u v y w coinWeight h hτ hu hy hw
  omega

/-- Positive joint randomized-residual resolving mass exposes a positive-weight
source/coin pair whose residual value changes across the involution. -/
theorem exists_resolving_coin_of_pos_randomizedResidualResolvedMass
    (τ : α → α) (v : α → Coin → V)
    (w : α → ℕ) (coinWeight : Coin → ℕ)
    (hmass : 0 < randomizedResidualResolvedMass τ v w coinWeight) :
    ∃ x c, 0 < w x * coinWeight c ∧ v (τ x) c ≠ v x c := by
  classical
  by_contra hnone
  have hunresolved :
      ∀ x c, 0 < w x * coinWeight c → v (τ x) c = v x c := by
    intro x c hpos
    by_contra hneq
    exact hnone ⟨x, c, hpos, hneq⟩
  have hzero :=
    randomizedResidualResolvedMass_eq_zero_of_supportwise_unresolved
      τ v w coinWeight hunresolved
  omega

/-- Positive joint randomized-residual resolving mass has a deterministic
positive-weight coin slice with positive ordinary side-channel resolving mass.
Thus the obstruction cannot be hidden only in the finite mixture. -/
theorem exists_positive_coin_resolvedMass_of_pos_randomizedResidualResolvedMass
    (τ : α → α) (v : α → Coin → V)
    (w : α → ℕ) (coinWeight : Coin → ℕ)
    (hmass : 0 < randomizedResidualResolvedMass τ v w coinWeight) :
    ∃ c, 0 < coinWeight c ∧ 0 < resolvedMass τ (fun x => v x c) w := by
  rcases exists_resolving_coin_of_pos_randomizedResidualResolvedMass
      τ v w coinWeight hmass with ⟨x, c, hprod, hchange⟩
  have hx : 0 < w x := by
    by_contra hnot
    have hzero : w x = 0 := Nat.eq_zero_of_not_pos hnot
    have hprod_zero : w x * coinWeight c = 0 := by simp [hzero]
    omega
  have hc : 0 < coinWeight c := by
    by_contra hnot
    have hzero : coinWeight c = 0 := Nat.eq_zero_of_not_pos hnot
    have hprod_zero : w x * coinWeight c = 0 := by simp [hzero]
    omega
  exact
    ⟨c, hc,
      resolvedMass_pos_of_resolving_point
        (τ := τ) (v := fun x => v x c) (w := w) hx hchange⟩

/-- Every positive randomized-residual doubled advantage exposes a positive
joint-support source/coin pair whose residual value changes across the
involution. -/
theorem exists_resolving_coin_of_pos_doubledAdvantage_randomizedResidual
    (τ : α → α) (u : α → U) (v : α → Coin → V)
    (y : α → Bool) (w : α → ℕ) (coinWeight : Coin → ℕ)
    (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv :
      0 < doubledAdvantage
        (fun xr : α × Coin => (u xr.1, v xr.1 xr.2))
        (fun xr : α × Coin => y xr.1)
        (productWeight w coinWeight) h) :
    ∃ x c, 0 < w x * coinWeight c ∧ v (τ x) c ≠ v x c :=
  exists_resolving_coin_of_pos_randomizedResidualResolvedMass
    (τ := τ) (v := v) (w := w) (coinWeight := coinWeight)
    (randomizedResidualResolvedMass_pos_of_pos_doubledAdvantage
      τ u v y w coinWeight h hτ hu hy hw hadv)

/-- Every positive randomized-residual doubled advantage is already witnessed
by a deterministic positive-weight coin slice with positive ordinary
side-channel resolving mass. -/
theorem exists_positive_coin_resolvedMass_of_pos_doubledAdvantage_randomizedResidual
    (τ : α → α) (u : α → U) (v : α → Coin → V)
    (y : α → Bool) (w : α → ℕ) (coinWeight : Coin → ℕ)
    (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv :
      0 < doubledAdvantage
        (fun xr : α × Coin => (u xr.1, v xr.1 xr.2))
        (fun xr : α × Coin => y xr.1)
        (productWeight w coinWeight) h) :
    ∃ c, 0 < coinWeight c ∧ 0 < resolvedMass τ (fun x => v x c) w :=
  exists_positive_coin_resolvedMass_of_pos_randomizedResidualResolvedMass
    (τ := τ) (v := v) (w := w) (coinWeight := coinWeight)
    (randomizedResidualResolvedMass_pos_of_pos_doubledAdvantage
      τ u v y w coinWeight h hτ hu hy hw hadv)

/-- Every strict half-accuracy randomized-residual advantage exposes a
positive joint-support source/coin pair whose residual value changes across
the involution. -/
theorem exists_resolving_coin_of_total_lt_two_mul_weightedCorrectMass_randomizedResidual
    (τ : α → α) (u : α → U) (v : α → Coin → V)
    (y : α → Bool) (w : α → ℕ) (coinWeight : Coin → ℕ)
    (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv :
      weightedTotalMass (productWeight w coinWeight) <
        2 * weightedCorrectMass
          (fun xr : α × Coin => (u xr.1, v xr.1 xr.2))
          (fun xr : α × Coin => y xr.1)
          (productWeight w coinWeight) h) :
    ∃ x c, 0 < w x * coinWeight c ∧ v (τ x) c ≠ v x c :=
  exists_resolving_coin_of_pos_randomizedResidualResolvedMass
    (τ := τ) (v := v) (w := w) (coinWeight := coinWeight)
    (randomizedResidualResolvedMass_pos_of_total_lt_two_mul_weightedCorrectMass
      τ u v y w coinWeight h hτ hu hy hw hadv)

/-- Every strict half-accuracy randomized-residual advantage is already
witnessed by a deterministic positive-weight coin slice with positive ordinary
side-channel resolving mass. -/
theorem exists_positive_coin_resolvedMass_of_total_lt_two_mul_weightedCorrectMass_randomizedResidual
    (τ : α → α) (u : α → U) (v : α → Coin → V)
    (y : α → Bool) (w : α → ℕ) (coinWeight : Coin → ℕ)
    (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv :
      weightedTotalMass (productWeight w coinWeight) <
        2 * weightedCorrectMass
          (fun xr : α × Coin => (u xr.1, v xr.1 xr.2))
          (fun xr : α × Coin => y xr.1)
          (productWeight w coinWeight) h) :
    ∃ c, 0 < coinWeight c ∧ 0 < resolvedMass τ (fun x => v x c) w :=
  exists_positive_coin_resolvedMass_of_pos_randomizedResidualResolvedMass
    (τ := τ) (v := v) (w := w) (coinWeight := coinWeight)
    (randomizedResidualResolvedMass_pos_of_total_lt_two_mul_weightedCorrectMass
      τ u v y w coinWeight h hτ hu hy hw hadv)

end

end Mettapedia.Computability.PNP
