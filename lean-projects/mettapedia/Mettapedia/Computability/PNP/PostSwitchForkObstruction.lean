import Mettapedia.Computability.PNP.PostSwitchInputObstruction
import Mettapedia.Computability.PNP.ResolutionDemandObstruction
import Mettapedia.Computability.PNP.InvariantScoreObstruction
import Mathlib.Tactic

/-!
# P vs NP crux: the exact post-switch input forces a sharp fork

The paper's exact local input is `u_i = (z, a_i, b)` and its involution acts by
`b ↦ b ⊕ a_i`.  Combined with the earlier symmetry-budget files, this gives a
clean specialized fork:

* if we keep only the invariant projection `(z, a_i)`, every symmetry-respecting
  soft score has zero signed correlation with the flipped target;
* if we also keep `b` as a side channel, then any success advantage over chance
  is bounded by the mass on nonzero VV columns, because those are exactly the
  points where `b` separates an involution pair.

This file packages that exact manuscript bridge in Lean.
-/

namespace Mettapedia.Computability.PNP

section

variable {Z : Type*} {k : ℕ}

noncomputable instance instFintypePostSwitchInput [Fintype Z] :
    Fintype (PostSwitchInput Z k) := by
  classical
  let e : PostSwitchInput Z k ≃ ((Z × BitVec k) × BitVec k) := by
    refine
      { toFun := fun u => ((PostSwitchInput.z u, PostSwitchInput.a u), PostSwitchInput.b u)
        invFun := fun t => ⟨t.1.1, t.1.2, t.2⟩
        left_inv := ?_
        right_inv := ?_ }
    · intro u
      cases u
      rfl
    · intro t
      cases t
      rfl
  exact Fintype.ofEquiv ((Z × BitVec k) × BitVec k) e.symm

instance instDecidablePredNonzeroColumn :
    DecidablePred (fun u : PostSwitchInput Z k => nonzeroColumn u.a) := by
  intro u
  classical
  unfold nonzeroColumn
  infer_instance

@[simp] theorem vvToggle_vvToggle (a b : BitVec k) :
    vvToggle a (vvToggle a b) = b := by
  funext i
  cases hai : a i <;> cases hbi : b i <;> simp [vvToggle, Bool.xor, hai, hbi]

theorem tiInputMap_involutive : Function.Involutive (@tiInputMap Z k) := by
  intro u
  cases u
  simp [tiInputMap, vvToggle_vvToggle]

theorem unresolvedBySideChannel_tiInputMap_b_iff_zeroColumn
    (u : PostSwitchInput Z k) :
    unresolvedBySideChannel tiInputMap (fun x => x.b) u ↔ u.a = zeroVec := by
  cases u
  simp [unresolvedBySideChannel, tiInputMap, vvToggle_eq_self_iff_zero]

theorem resolvedBySideChannel_tiInputMap_b_iff_nonzeroColumn
    (u : PostSwitchInput Z k) :
    ¬ unresolvedBySideChannel tiInputMap (fun x => x.b) u ↔ nonzeroColumn u.a := by
  rw [unresolvedBySideChannel_tiInputMap_b_iff_zeroColumn]
  simpa using (nonzeroColumn_iff_ne_zero u.a).symm

theorem weighted_signedScore_sum_eq_zero_on_invariantProjection
    [Fintype Z]
    (y : PostSwitchInput Z k → Bool) (w : PostSwitchInput Z k → ℕ)
    (score : Z × BitVec k → ℤ)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u) :
    ∑ u : PostSwitchInput Z k,
      (w u : ℤ) * score (invariantProjection u) * targetSign (y u) = 0 := by
  simpa using
    (weighted_signedScore_sum_eq_zero
      (τ := tiInputMap)
      (u := invariantProjection)
      (y := y)
      (w := w)
      (score := score)
      tiInputMap_involutive
      invariantProjection_tiInputMap
      hy
      hw)

theorem doubledAdvantage_invariantProjection_with_b_le_nonzeroColumnMass
    [Fintype Z]
    (y : PostSwitchInput Z k → Bool) (w : PostSwitchInput Z k → ℕ)
    (h : (Z × BitVec k) × BitVec k → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u) :
    doubledAdvantage (fun u => (invariantProjection u, u.b)) y w h ≤
      sliceMass (fun u : PostSwitchInput Z k => nonzeroColumn u.a) w := by
  have hbound :
      doubledAdvantage (fun u => (invariantProjection u, u.b)) y w h ≤
        resolvedMass tiInputMap (fun u => u.b) w :=
    doubledAdvantage_pair_le_resolvedMass
      (τ := tiInputMap)
      (u := invariantProjection)
      (v := fun u => u.b)
      (y := y)
      (w := w)
      (h := h)
      tiInputMap_involutive
      invariantProjection_tiInputMap
      hy
      hw
  have hresolved :
      resolvedMass tiInputMap (fun u => u.b) w =
        sliceMass (fun u : PostSwitchInput Z k => nonzeroColumn u.a) w := by
    classical
    have hp :
        (fun u : PostSwitchInput Z k =>
          ¬ unresolvedBySideChannel tiInputMap (fun x => x.b) u) =
          (fun u : PostSwitchInput Z k => nonzeroColumn u.a) := by
      funext u
      exact propext (resolvedBySideChannel_tiInputMap_b_iff_nonzeroColumn u)
    unfold resolvedMass outsideMass
    simp [hp]
  rwa [hresolved] at hbound

/-- Any claimed doubled advantage from the exact `(z, a_i, b)` post-switch
input forces at least that much mass on nonzero `a_i` columns. -/
theorem nonzeroColumnMass_ge_of_le_doubledAdvantage_invariantProjection_with_b
    [Fintype Z]
    (y : PostSwitchInput Z k → Bool) (w : PostSwitchInput Z k → ℕ)
    (h : (Z × BitVec k) × BitVec k → Bool) (δ : ℕ)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hδ :
      δ ≤ doubledAdvantage (fun u => (invariantProjection u, u.b)) y w h) :
    δ ≤ sliceMass (fun u : PostSwitchInput Z k => nonzeroColumn u.a) w :=
  le_trans hδ <|
    doubledAdvantage_invariantProjection_with_b_le_nonzeroColumnMass y w h hy hw

/-- Any positive doubled advantage from the exact `(z, a_i, b)` post-switch
input forces positive mass on nonzero `a_i` columns. -/
theorem pos_nonzeroColumnMass_of_pos_doubledAdvantage_invariantProjection_with_b
    [Fintype Z]
    (y : PostSwitchInput Z k → Bool) (w : PostSwitchInput Z k → ℕ)
    (h : (Z × BitVec k) × BitVec k → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hpos :
      0 < doubledAdvantage (fun u => (invariantProjection u, u.b)) y w h) :
    0 < sliceMass (fun u : PostSwitchInput Z k => nonzeroColumn u.a) w :=
  lt_of_lt_of_le hpos <|
    doubledAdvantage_invariantProjection_with_b_le_nonzeroColumnMass y w h hy hw

/-- Positive nonzero-column mass exposes a positive-weight post-switch input
whose `a_i` column is nonzero. -/
theorem exists_nonzeroColumn_of_pos_nonzeroColumnMass
    [Fintype Z]
    (w : PostSwitchInput Z k → ℕ)
    (hmass :
      0 < sliceMass (fun u : PostSwitchInput Z k => nonzeroColumn u.a) w) :
    ∃ u : PostSwitchInput Z k, 0 < w u ∧ nonzeroColumn u.a := by
  classical
  unfold sliceMass at hmass
  by_contra hnone
  have hzero :
      (∑ u : {u : PostSwitchInput Z k // nonzeroColumn u.a}, w u.1) = 0 := by
    apply Finset.sum_eq_zero
    intro u _
    exact Nat.eq_zero_of_not_pos fun hpos =>
      hnone ⟨u.1, hpos, u.2⟩
  exact (Nat.ne_of_gt hmass) hzero

/-- Any positive `b`-side-channel advantage exposes a positive-weight input
where the `b` side channel changes under the manuscript involution. -/
theorem exists_b_resolving_input_of_pos_doubledAdvantage_invariantProjection_with_b
    [Fintype Z]
    (y : PostSwitchInput Z k → Bool) (w : PostSwitchInput Z k → ℕ)
    (h : (Z × BitVec k) × BitVec k → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hpos :
      0 < doubledAdvantage (fun u => (invariantProjection u, u.b)) y w h) :
    ∃ u : PostSwitchInput Z k, 0 < w u ∧ (tiInputMap u).b ≠ u.b :=
  exists_resolving_point_of_pos_doubledAdvantage_pair
    (τ := tiInputMap)
    (u := invariantProjection)
    (v := fun u : PostSwitchInput Z k => u.b)
    (y := y)
    (w := w)
    (h := h)
    tiInputMap_involutive
    invariantProjection_tiInputMap
    hy
    hw
    hpos

/-- Any positive `b`-side-channel advantage exposes a positive-weight
post-switch input on a nonzero `a_i` column. -/
theorem exists_nonzeroColumn_of_pos_doubledAdvantage_invariantProjection_with_b
    [Fintype Z]
    (y : PostSwitchInput Z k → Bool) (w : PostSwitchInput Z k → ℕ)
    (h : (Z × BitVec k) × BitVec k → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hpos :
      0 < doubledAdvantage (fun u => (invariantProjection u, u.b)) y w h) :
    ∃ u : PostSwitchInput Z k, 0 < w u ∧ nonzeroColumn u.a := by
  rcases
      exists_b_resolving_input_of_pos_doubledAdvantage_invariantProjection_with_b
        y w h hy hw hpos with ⟨u, huw, hchange⟩
  refine ⟨u, huw, ?_⟩
  exact (resolvedBySideChannel_tiInputMap_b_iff_nonzeroColumn u).1 (by
    simpa [unresolvedBySideChannel] using hchange)

/-- Any strict half-accuracy advantage from the exact `(z, a_i, b)` post-switch
input forces positive mass on nonzero `a_i` columns. -/
theorem pos_nonzeroColumnMass_of_total_lt_two_mul_weightedCorrectMass_invariantProjection_with_b
    [Fintype Z]
    (y : PostSwitchInput Z k → Bool) (w : PostSwitchInput Z k → ℕ)
    (h : (Z × BitVec k) × BitVec k → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hadv :
      weightedTotalMass w <
        2 * weightedCorrectMass (fun u => (invariantProjection u, u.b)) y w h) :
    0 < sliceMass (fun u : PostSwitchInput Z k => nonzeroColumn u.a) w := by
  have hpos :
      0 < doubledAdvantage (fun u => (invariantProjection u, u.b)) y w h := by
    unfold doubledAdvantage
    omega
  exact
    pos_nonzeroColumnMass_of_pos_doubledAdvantage_invariantProjection_with_b
      y w h hy hw hpos

/-- Any strict half-accuracy advantage from the exact `(z, a_i, b)` post-switch
input exposes a positive-weight input where the retained `b` side channel
changes under the involution. -/
theorem exists_b_resolving_input_of_total_lt_two_mul_weightedCorrectMass_invariantProjection_with_b
    [Fintype Z]
    (y : PostSwitchInput Z k → Bool) (w : PostSwitchInput Z k → ℕ)
    (h : (Z × BitVec k) × BitVec k → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hadv :
      weightedTotalMass w <
        2 * weightedCorrectMass (fun u => (invariantProjection u, u.b)) y w h) :
    ∃ u : PostSwitchInput Z k, 0 < w u ∧ (tiInputMap u).b ≠ u.b := by
  have hpos :
      0 < doubledAdvantage (fun u => (invariantProjection u, u.b)) y w h := by
    unfold doubledAdvantage
    omega
  exact
    exists_b_resolving_input_of_pos_doubledAdvantage_invariantProjection_with_b
      y w h hy hw hpos

/-- Any strict half-accuracy advantage from the exact `(z, a_i, b)` post-switch
input exposes a positive-weight input on a nonzero `a_i` column. -/
theorem exists_nonzeroColumn_of_total_lt_two_mul_weightedCorrectMass_invariantProjection_with_b
    [Fintype Z]
    (y : PostSwitchInput Z k → Bool) (w : PostSwitchInput Z k → ℕ)
    (h : (Z × BitVec k) × BitVec k → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hadv :
      weightedTotalMass w <
        2 * weightedCorrectMass (fun u => (invariantProjection u, u.b)) y w h) :
    ∃ u : PostSwitchInput Z k, 0 < w u ∧ nonzeroColumn u.a := by
  have hpos :
      0 < doubledAdvantage (fun u => (invariantProjection u, u.b)) y w h := by
    unfold doubledAdvantage
    omega
  exact
    exists_nonzeroColumn_of_pos_doubledAdvantage_invariantProjection_with_b
      y w h hy hw hpos

/-- If the proof-relevant post-switch mass has no nonzero `a_i` columns, then
keeping the `b` side channel cannot produce positive doubled advantage. -/
theorem not_pos_doubledAdvantage_invariantProjection_with_b_of_zero_nonzeroColumnMass
    [Fintype Z]
    (y : PostSwitchInput Z k → Bool) (w : PostSwitchInput Z k → ℕ)
    (h : (Z × BitVec k) × BitVec k → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hmass : sliceMass (fun u : PostSwitchInput Z k => nonzeroColumn u.a) w = 0) :
    ¬ 0 < doubledAdvantage (fun u => (invariantProjection u, u.b)) y w h := by
  have hle :
      doubledAdvantage (fun u => (invariantProjection u, u.b)) y w h ≤
        sliceMass (fun u : PostSwitchInput Z k => nonzeroColumn u.a) w :=
    doubledAdvantage_invariantProjection_with_b_le_nonzeroColumnMass y w h hy hw
  omega

/-- If the proof-relevant post-switch mass has no nonzero `a_i` columns, then
keeping the `b` side channel cannot even beat half accuracy. -/
theorem not_total_lt_two_mul_weightedCorrectMass_invariantProjection_with_b_of_zero_nonzeroColumnMass
    [Fintype Z]
    (y : PostSwitchInput Z k → Bool) (w : PostSwitchInput Z k → ℕ)
    (h : (Z × BitVec k) × BitVec k → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hmass : sliceMass (fun u : PostSwitchInput Z k => nonzeroColumn u.a) w = 0) :
    ¬ weightedTotalMass w <
      2 * weightedCorrectMass (fun u => (invariantProjection u, u.b)) y w h := by
  intro hadv
  have hpos :
      0 < doubledAdvantage (fun u => (invariantProjection u, u.b)) y w h := by
    unfold doubledAdvantage
    omega
  exact
    not_pos_doubledAdvantage_invariantProjection_with_b_of_zero_nonzeroColumnMass
      y w h hy hw hmass hpos

/-- A weighted support is exact-input invariant when every positive-weight
post-switch input is fixed by the manuscript involution on the full local input
`(z, a_i, b)`. -/
def exactInputInvariantWeightedSupport
    (w : PostSwitchInput Z k → ℕ) : Prop :=
  ∀ u, 0 < w u → tiInputMap u = u

/-- If the proof-relevant weighted support is exact-input invariant, then it
has no mass on nonzero `a_i` columns.  Nonzero columns are exactly where the
full local input changes under the manuscript involution. -/
theorem nonzeroColumnMass_eq_zero_of_exactInputInvariantWeightedSupport
    [Fintype Z]
    (w : PostSwitchInput Z k → ℕ)
    (hsupport : exactInputInvariantWeightedSupport w) :
    sliceMass (fun u : PostSwitchInput Z k => nonzeroColumn u.a) w = 0 := by
  classical
  unfold sliceMass
  apply Finset.sum_eq_zero
  intro u _
  exact Nat.eq_zero_of_not_pos fun hpos =>
    tiInputMap_ne_self_of_nonzeroColumn u.1 u.2 (hsupport u.1 hpos)

/-- Supplying positive nonzero-column mass contradicts exact-input invariance
of the weighted support. -/
theorem not_exactInputInvariantWeightedSupport_of_pos_nonzeroColumnMass
    [Fintype Z]
    (w : PostSwitchInput Z k → ℕ)
    (hmass :
      0 < sliceMass (fun u : PostSwitchInput Z k => nonzeroColumn u.a) w) :
    ¬ exactInputInvariantWeightedSupport w := by
  intro hsupport
  have hzero := nonzeroColumnMass_eq_zero_of_exactInputInvariantWeightedSupport
    (Z := Z) (k := k) w hsupport
  omega

/-- Therefore the exact local-input invariance premise itself blocks every
positive `b`-side-channel advantage on the manuscript post-switch surface. -/
theorem not_pos_doubledAdvantage_invariantProjection_with_b_of_exactInputInvariantWeightedSupport
    [Fintype Z]
    (y : PostSwitchInput Z k → Bool) (w : PostSwitchInput Z k → ℕ)
    (h : (Z × BitVec k) × BitVec k → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hsupport : exactInputInvariantWeightedSupport w) :
    ¬ 0 < doubledAdvantage (fun u => (invariantProjection u, u.b)) y w h := by
  exact
    not_pos_doubledAdvantage_invariantProjection_with_b_of_zero_nonzeroColumnMass
      y w h hy hw
      (nonzeroColumnMass_eq_zero_of_exactInputInvariantWeightedSupport
        (Z := Z) (k := k) w hsupport)

/-- Therefore the exact local-input invariance premise itself blocks every
strict half-accuracy `b`-side-channel advantage on the manuscript post-switch
surface. -/
theorem not_total_lt_two_mul_weightedCorrectMass_invariantProjection_with_b_of_exactInputInvariantWeightedSupport
    [Fintype Z]
    (y : PostSwitchInput Z k → Bool) (w : PostSwitchInput Z k → ℕ)
    (h : (Z × BitVec k) × BitVec k → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hsupport : exactInputInvariantWeightedSupport w) :
    ¬ weightedTotalMass w <
      2 * weightedCorrectMass (fun u => (invariantProjection u, u.b)) y w h := by
  exact
    not_total_lt_two_mul_weightedCorrectMass_invariantProjection_with_b_of_zero_nonzeroColumnMass
      y w h hy hw
      (nonzeroColumnMass_eq_zero_of_exactInputInvariantWeightedSupport
        (Z := Z) (k := k) w hsupport)

/-- Positive `b`-side-channel advantage refutes the manuscript-style
exact-input-invariant support premise. -/
theorem not_exactInputInvariantWeightedSupport_of_pos_doubledAdvantage_invariantProjection_with_b
    [Fintype Z]
    (y : PostSwitchInput Z k → Bool) (w : PostSwitchInput Z k → ℕ)
    (h : (Z × BitVec k) × BitVec k → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hpos :
      0 < doubledAdvantage (fun u => (invariantProjection u, u.b)) y w h) :
    ¬ exactInputInvariantWeightedSupport w := by
  intro hsupport
  exact
    not_pos_doubledAdvantage_invariantProjection_with_b_of_exactInputInvariantWeightedSupport
      y w h hy hw hsupport hpos

/-- Strict half-accuracy `b`-side-channel advantage refutes the
manuscript-style exact-input-invariant support premise. -/
theorem not_exactInputInvariantWeightedSupport_of_total_lt_two_mul_weightedCorrectMass_invariantProjection_with_b
    [Fintype Z]
    (y : PostSwitchInput Z k → Bool) (w : PostSwitchInput Z k → ℕ)
    (h : (Z × BitVec k) × BitVec k → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hadv :
      weightedTotalMass w <
        2 * weightedCorrectMass (fun u => (invariantProjection u, u.b)) y w h) :
    ¬ exactInputInvariantWeightedSupport w := by
  intro hsupport
  exact
    not_total_lt_two_mul_weightedCorrectMass_invariantProjection_with_b_of_exactInputInvariantWeightedSupport
      y w h hy hw hsupport hadv

/-- A single theorem-form contradiction: the manuscript fork cannot have both
positive `b`-side-channel advantage and exact-input-invariant weighted support. -/
theorem not_pos_doubledAdvantage_and_exactInputInvariantWeightedSupport
    [Fintype Z]
    (y : PostSwitchInput Z k → Bool) (w : PostSwitchInput Z k → ℕ)
    (h : (Z × BitVec k) × BitVec k → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u) :
    ¬ (0 < doubledAdvantage (fun u => (invariantProjection u, u.b)) y w h ∧
        exactInputInvariantWeightedSupport w) := by
  intro hboth
  exact
    not_pos_doubledAdvantage_invariantProjection_with_b_of_exactInputInvariantWeightedSupport
      y w h hy hw hboth.2 hboth.1

/-- The same contradiction on the strict half-accuracy surface. -/
theorem not_total_lt_two_mul_weightedCorrectMass_and_exactInputInvariantWeightedSupport
    [Fintype Z]
    (y : PostSwitchInput Z k → Bool) (w : PostSwitchInput Z k → ℕ)
    (h : (Z × BitVec k) × BitVec k → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u) :
    ¬ (weightedTotalMass w <
          2 * weightedCorrectMass (fun u => (invariantProjection u, u.b)) y w h ∧
        exactInputInvariantWeightedSupport w) := by
  intro hboth
  exact
    not_total_lt_two_mul_weightedCorrectMass_invariantProjection_with_b_of_exactInputInvariantWeightedSupport
      y w h hy hw hboth.2 hboth.1

end

end Mettapedia.Computability.PNP
