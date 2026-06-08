import Mettapedia.Computability.PNP.PostSwitchForkObstruction
import Mettapedia.Computability.PNP.RandomizedResidualObstruction

/-!
# P vs NP crux: randomized residuals on the exact post-switch surface

The generic randomized-residual obstruction reduces randomized side information
to an ordinary side channel on a source/coin product.  This file specializes
that theorem to the manuscript's exact post-switch input surface.

If the proof keeps the exact local-input invariance premise for positive-weight
post-switch inputs, then every finite-coin randomized residual has zero joint
orbit-resolving mass, and therefore cannot produce positive doubled advantage.
-/

namespace Mettapedia.Computability.PNP

section

variable {Z Coin V : Type*} {k : ℕ} [Fintype Z] [Fintype Coin]

/-- Exact-input-invariant weighted support forces every randomized residual to
have zero joint resolving mass on the post-switch source/coin product. -/
theorem randomizedResidualResolvedMass_tiInputMap_eq_zero_of_exactInputInvariantWeightedSupport
    (v : PostSwitchInput Z k → Coin → V)
    (w : PostSwitchInput Z k → ℕ) (coinWeight : Coin → ℕ)
    (hsupport : exactInputInvariantWeightedSupport w) :
    randomizedResidualResolvedMass tiInputMap v w coinWeight = 0 := by
  exact
    randomizedResidualResolvedMass_eq_zero_of_fixed_source_support
      (τ := tiInputMap)
      (v := v)
      (w := w)
      (coinWeight := coinWeight)
      hsupport

/-- Supplying positive randomized joint resolving mass contradicts the exact
local-input invariance support premise. -/
theorem not_exactInputInvariantWeightedSupport_of_pos_randomizedResidualResolvedMass_tiInputMap
    (v : PostSwitchInput Z k → Coin → V)
    (w : PostSwitchInput Z k → ℕ) (coinWeight : Coin → ℕ)
    (hmass : 0 < randomizedResidualResolvedMass tiInputMap v w coinWeight) :
    ¬ exactInputInvariantWeightedSupport w := by
  intro hsupport
  have hzero :=
    randomizedResidualResolvedMass_tiInputMap_eq_zero_of_exactInputInvariantWeightedSupport
      v w coinWeight hsupport
  omega

/-- Under exact local-input-invariant support, no finite-coin randomized
residual side channel over the invariant projection can produce positive
doubled advantage. -/
theorem not_pos_doubledAdvantage_randomizedResidual_invariantProjection_of_exactInputInvariantWeightedSupport
    (v : PostSwitchInput Z k → Coin → V)
    (y : PostSwitchInput Z k → Bool)
    (w : PostSwitchInput Z k → ℕ) (coinWeight : Coin → ℕ)
    (h : (Z × BitVec k) × V → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hsupport : exactInputInvariantWeightedSupport w) :
    ¬ 0 < doubledAdvantage
        (fun xr : PostSwitchInput Z k × Coin =>
          (invariantProjection xr.1, v xr.1 xr.2))
        (fun xr : PostSwitchInput Z k × Coin => y xr.1)
        (productWeight w coinWeight) h := by
  exact
    not_pos_doubledAdvantage_randomizedResidual_of_fixed_source_support
      (τ := tiInputMap)
      (u := invariantProjection)
      (v := v)
      (y := y)
      (w := w)
      (coinWeight := coinWeight)
      (h := h)
      tiInputMap_involutive
      invariantProjection_tiInputMap
      hy
      hw
      hsupport

/-- Under exact local-input-invariant support, no finite-coin randomized
residual side channel over the invariant projection can even beat half
accuracy. -/
theorem not_total_lt_two_mul_weightedCorrectMass_randomizedResidual_invariantProjection_of_exactInputInvariantWeightedSupport
    (v : PostSwitchInput Z k → Coin → V)
    (y : PostSwitchInput Z k → Bool)
    (w : PostSwitchInput Z k → ℕ) (coinWeight : Coin → ℕ)
    (h : (Z × BitVec k) × V → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hsupport : exactInputInvariantWeightedSupport w) :
    ¬ weightedTotalMass (productWeight w coinWeight) <
      2 * weightedCorrectMass
        (fun xr : PostSwitchInput Z k × Coin =>
          (invariantProjection xr.1, v xr.1 xr.2))
        (fun xr : PostSwitchInput Z k × Coin => y xr.1)
        (productWeight w coinWeight) h := by
  exact
    not_total_lt_two_mul_weightedCorrectMass_randomizedResidual_of_fixed_source_support
      (τ := tiInputMap)
      (u := invariantProjection)
      (v := v)
      (y := y)
      (w := w)
      (coinWeight := coinWeight)
      (h := h)
      tiInputMap_involutive
      invariantProjection_tiInputMap
      hy
      hw
      hsupport

/-- On the exact post-switch surface, a finite-coin randomized residual that is
unresolved on positive joint support cannot produce positive advantage over
the invariant projection. -/
theorem not_pos_doubledAdvantage_randomizedResidual_invariantProjection_of_supportwise_unresolved
    (v : PostSwitchInput Z k → Coin → V)
    (y : PostSwitchInput Z k → Bool)
    (w : PostSwitchInput Z k → ℕ) (coinWeight : Coin → ℕ)
    (h : (Z × BitVec k) × V → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hunresolved :
      ∀ u c, 0 < w u * coinWeight c → v (tiInputMap u) c = v u c) :
    ¬ 0 < doubledAdvantage
        (fun xr : PostSwitchInput Z k × Coin =>
          (invariantProjection xr.1, v xr.1 xr.2))
        (fun xr : PostSwitchInput Z k × Coin => y xr.1)
        (productWeight w coinWeight) h := by
  exact
    not_pos_doubledAdvantage_randomizedResidual_of_supportwise_unresolved
      (τ := tiInputMap)
      (u := invariantProjection)
      (v := v)
      (y := y)
      (w := w)
      (coinWeight := coinWeight)
      (h := h)
      tiInputMap_involutive
      invariantProjection_tiInputMap
      hy
      hw
      hunresolved

/-- Any positive finite-coin randomized-residual advantage on the exact
post-switch surface exposes a positive joint-support input/coin pair where the
residual distinguishes the local-input switch. -/
theorem exists_resolving_coin_of_pos_doubledAdvantage_randomizedResidual_invariantProjection
    (v : PostSwitchInput Z k → Coin → V)
    (y : PostSwitchInput Z k → Bool)
    (w : PostSwitchInput Z k → ℕ) (coinWeight : Coin → ℕ)
    (h : (Z × BitVec k) × V → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hadv :
      0 < doubledAdvantage
        (fun xr : PostSwitchInput Z k × Coin =>
          (invariantProjection xr.1, v xr.1 xr.2))
        (fun xr : PostSwitchInput Z k × Coin => y xr.1)
        (productWeight w coinWeight) h) :
    ∃ u c, 0 < w u * coinWeight c ∧ v (tiInputMap u) c ≠ v u c :=
  exists_resolving_coin_of_pos_doubledAdvantage_randomizedResidual
    (τ := tiInputMap)
    (u := invariantProjection)
    (v := v)
    (y := y)
    (w := w)
    (coinWeight := coinWeight)
    (h := h)
    tiInputMap_involutive
    invariantProjection_tiInputMap
    hy
    hw
    hadv

/-- On the exact post-switch surface, positive finite-coin randomized-residual
advantage is already witnessed by a deterministic positive-weight coin slice
whose residual side channel has positive ordinary resolving mass. -/
theorem exists_positive_coin_resolvedMass_of_pos_doubledAdvantage_randomizedResidual_invariantProjection
    (v : PostSwitchInput Z k → Coin → V)
    (y : PostSwitchInput Z k → Bool)
    (w : PostSwitchInput Z k → ℕ) (coinWeight : Coin → ℕ)
    (h : (Z × BitVec k) × V → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hadv :
      0 < doubledAdvantage
        (fun xr : PostSwitchInput Z k × Coin =>
          (invariantProjection xr.1, v xr.1 xr.2))
        (fun xr : PostSwitchInput Z k × Coin => y xr.1)
        (productWeight w coinWeight) h) :
    ∃ c, 0 < coinWeight c ∧
      0 < resolvedMass tiInputMap (fun u => v u c) w :=
  exists_positive_coin_resolvedMass_of_pos_doubledAdvantage_randomizedResidual
    (τ := tiInputMap)
    (u := invariantProjection)
    (v := v)
    (y := y)
    (w := w)
    (coinWeight := coinWeight)
    (h := h)
    tiInputMap_involutive
    invariantProjection_tiInputMap
    hy
    hw
    hadv

/-- On the exact post-switch surface, strict half-accuracy finite-coin
randomized-residual advantage is already witnessed by a deterministic
positive-weight coin slice whose residual side channel has positive ordinary
resolving mass. -/
theorem exists_positive_coin_resolvedMass_of_total_lt_two_mul_weightedCorrectMass_randomizedResidual_invariantProjection
    (v : PostSwitchInput Z k → Coin → V)
    (y : PostSwitchInput Z k → Bool)
    (w : PostSwitchInput Z k → ℕ) (coinWeight : Coin → ℕ)
    (h : (Z × BitVec k) × V → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hadv :
      weightedTotalMass (productWeight w coinWeight) <
        2 * weightedCorrectMass
          (fun xr : PostSwitchInput Z k × Coin =>
            (invariantProjection xr.1, v xr.1 xr.2))
          (fun xr : PostSwitchInput Z k × Coin => y xr.1)
          (productWeight w coinWeight) h) :
    ∃ c, 0 < coinWeight c ∧
      0 < resolvedMass tiInputMap (fun u => v u c) w :=
  exists_positive_coin_resolvedMass_of_total_lt_two_mul_weightedCorrectMass_randomizedResidual
    (τ := tiInputMap)
    (u := invariantProjection)
    (v := v)
    (y := y)
    (w := w)
    (coinWeight := coinWeight)
    (h := h)
    tiInputMap_involutive
    invariantProjection_tiInputMap
    hy
    hw
    hadv

/-- On the exact post-switch surface, strict half-accuracy finite-coin
randomized-residual advantage is already witnessed by a deterministic
positive-weight coin slice carrying the ordinary invariant-projection residual
obstruction package. -/
theorem exists_positive_coin_obstruction_package_of_total_lt_two_mul_weightedCorrectMass_randomizedResidual_invariantProjection
    (v : PostSwitchInput Z k → Coin → V)
    (y : PostSwitchInput Z k → Bool)
    (w : PostSwitchInput Z k → ℕ) (coinWeight : Coin → ℕ)
    (h : (Z × BitVec k) × V → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hadv :
      weightedTotalMass (productWeight w coinWeight) <
        2 * weightedCorrectMass
          (fun xr : PostSwitchInput Z k × Coin =>
            (invariantProjection xr.1, v xr.1 xr.2))
          (fun xr : PostSwitchInput Z k × Coin => y xr.1)
          (productWeight w coinWeight) h) :
    ∃ c, 0 < coinWeight c ∧
      (¬ SideInfoDeterminedBy invariantProjection (fun u => v u c) ∧
        PositiveWeightSideInfoCollisionOverBase invariantProjection
          (fun u => v u c) w ∧
        (∃ u, 0 < w u ∧
          invariantProjection (tiInputMap u) = invariantProjection u ∧
          v (tiInputMap u) c ≠ v u c) ∧
        (∃ u, 0 < w u ∧
          ¬ SourceOnlyPredicateCapturesSideEq invariantProjection
            (fun u => v u c) (v u c))) :=
  exists_positive_coin_obstruction_package_of_total_lt_two_mul_weightedCorrectMass_randomizedResidual
    (τ := tiInputMap)
    (u := invariantProjection)
    (v := v)
    (y := y)
    (w := w)
    (coinWeight := coinWeight)
    (h := h)
    tiInputMap_involutive
    invariantProjection_tiInputMap
    hy
    hw
    hadv

/-- Strict half-accuracy finite-coin randomized-residual advantage on the
exact post-switch surface refutes exact local-input-invariant support. -/
theorem not_exactInputInvariantWeightedSupport_of_total_lt_two_mul_weightedCorrectMass_randomizedResidual_invariantProjection
    (v : PostSwitchInput Z k → Coin → V)
    (y : PostSwitchInput Z k → Bool)
    (w : PostSwitchInput Z k → ℕ) (coinWeight : Coin → ℕ)
    (h : (Z × BitVec k) × V → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hadv :
      weightedTotalMass (productWeight w coinWeight) <
        2 * weightedCorrectMass
          (fun xr : PostSwitchInput Z k × Coin =>
            (invariantProjection xr.1, v xr.1 xr.2))
          (fun xr : PostSwitchInput Z k × Coin => y xr.1)
          (productWeight w coinWeight) h) :
    ¬ exactInputInvariantWeightedSupport w := by
  intro hsupport
  exact
    not_total_lt_two_mul_weightedCorrectMass_randomizedResidual_invariantProjection_of_exactInputInvariantWeightedSupport
      v y w coinWeight h hy hw hsupport hadv

/-- The exact post-switch route cannot simultaneously claim positive
randomized-residual advantage and exact-input-invariant weighted support. -/
theorem not_pos_doubledAdvantage_randomizedResidual_and_exactInputInvariantWeightedSupport
    (v : PostSwitchInput Z k → Coin → V)
    (y : PostSwitchInput Z k → Bool)
    (w : PostSwitchInput Z k → ℕ) (coinWeight : Coin → ℕ)
    (h : (Z × BitVec k) × V → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u) :
    ¬ (0 < doubledAdvantage
          (fun xr : PostSwitchInput Z k × Coin =>
            (invariantProjection xr.1, v xr.1 xr.2))
          (fun xr : PostSwitchInput Z k × Coin => y xr.1)
          (productWeight w coinWeight) h ∧
        exactInputInvariantWeightedSupport w) := by
  intro hboth
  exact
    not_pos_doubledAdvantage_randomizedResidual_invariantProjection_of_exactInputInvariantWeightedSupport
      v y w coinWeight h hy hw hboth.2 hboth.1

/-- The same contradiction on the strict half-accuracy surface. -/
theorem not_total_lt_two_mul_weightedCorrectMass_randomizedResidual_and_exactInputInvariantWeightedSupport
    (v : PostSwitchInput Z k → Coin → V)
    (y : PostSwitchInput Z k → Bool)
    (w : PostSwitchInput Z k → ℕ) (coinWeight : Coin → ℕ)
    (h : (Z × BitVec k) × V → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u) :
    ¬ (weightedTotalMass (productWeight w coinWeight) <
          2 * weightedCorrectMass
            (fun xr : PostSwitchInput Z k × Coin =>
              (invariantProjection xr.1, v xr.1 xr.2))
            (fun xr : PostSwitchInput Z k × Coin => y xr.1)
            (productWeight w coinWeight) h ∧
        exactInputInvariantWeightedSupport w) := by
  intro hboth
  exact
    not_total_lt_two_mul_weightedCorrectMass_randomizedResidual_invariantProjection_of_exactInputInvariantWeightedSupport
      v y w coinWeight h hy hw hboth.2 hboth.1

end

end Mettapedia.Computability.PNP
