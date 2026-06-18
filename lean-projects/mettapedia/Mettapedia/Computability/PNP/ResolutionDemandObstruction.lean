import Mettapedia.Computability.PNP.SideChannelResolutionObstruction
import Mathlib.Tactic

/-!
# P vs NP crux: domination advantage forces orbit-resolving mass

The side-channel resolution obstruction shows that total success is bounded by
the mass where a retained side channel actually separates involution partners.

This file packages the converse quantitative reading: any claimed global
advantage over chance forces at least that much orbit-resolving mass.
-/

namespace Mettapedia.Computability.PNP

section

variable {α U V : Type*} [Fintype α]

/-- Twice the success advantage over chance for a weighted classifier. -/
def doubledAdvantage
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool) : ℕ :=
  2 * weightedCorrectMass u y w h - weightedTotalMass w

/-- The total mass splits into correct and incorrect mass. -/
theorem weightedTotalMass_eq_weightedCorrectMass_add_weightedIncorrectMass
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool) :
    weightedTotalMass w =
      weightedCorrectMass u y w h + weightedIncorrectMass u y w h := by
  classical
  unfold weightedTotalMass weightedCorrectMass weightedIncorrectMass
  simpa [incorrect_iff_not_correct] using
    (Fintype.sum_subtype_add_sum_subtype (Correct u y h) w).symm

/-- If every positive-weight point is classified correctly, the incorrect mass
vanishes. -/
theorem weightedIncorrectMass_eq_zero_of_supportwise_correct
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool)
    (hcorrect : ∀ x, 0 < w x → Correct u y h x) :
    weightedIncorrectMass u y w h = 0 := by
  unfold weightedIncorrectMass
  apply Finset.sum_eq_zero
  intro x _
  by_cases hxw : 0 < w x.1
  · exact False.elim (x.2 (hcorrect x.1 hxw))
  · exact Nat.eq_zero_of_not_pos hxw

/-- If every positive-weight point is classified correctly, then all supported
mass is correct mass. -/
theorem weightedCorrectMass_eq_weightedTotalMass_of_supportwise_correct
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool)
    (hcorrect : ∀ x, 0 < w x → Correct u y h x) :
    weightedCorrectMass u y w h = weightedTotalMass w := by
  have hsplit :
      weightedTotalMass w =
        weightedCorrectMass u y w h + weightedIncorrectMass u y w h :=
    weightedTotalMass_eq_weightedCorrectMass_add_weightedIncorrectMass
      u y w h
  have hzero :
      weightedIncorrectMass u y w h = 0 :=
    weightedIncorrectMass_eq_zero_of_supportwise_correct
      u y w h hcorrect
  omega

/-- Conversely, if the correct mass is the whole supported mass, then every
positive-weight point is classified correctly. -/
theorem supportwise_correct_of_weightedCorrectMass_eq_weightedTotalMass
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool)
    (hperfect : weightedCorrectMass u y w h = weightedTotalMass w) :
    ∀ x, 0 < w x → Correct u y h x := by
  have hsplit :
      weightedTotalMass w =
        weightedCorrectMass u y w h + weightedIncorrectMass u y w h :=
    weightedTotalMass_eq_weightedCorrectMass_add_weightedIncorrectMass
      u y w h
  have hzero : weightedIncorrectMass u y w h = 0 := by
    omega
  intro x hxw
  by_contra hbad
  let x' : {x : α // Incorrect u y h x} := ⟨x, hbad⟩
  have hle' :
      w x'.1 ≤ ∑ y : {x : α // Incorrect u y h x}, w y.1 := by
    exact
      Finset.single_le_sum
        (f := fun y : {x : α // Incorrect u y h x} => w y.1)
        (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ x')
  have hle : w x ≤ weightedIncorrectMass u y w h := by
    simpa [weightedIncorrectMass, x'] using hle'
  rw [hzero] at hle
  omega

/-- Supportwise perfect correctness already forces the doubled advantage to be
the whole support mass. -/
theorem doubledAdvantage_eq_weightedTotalMass_of_supportwise_correct
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool)
    (hcorrect : ∀ x, 0 < w x → Correct u y h x) :
    doubledAdvantage u y w h = weightedTotalMass w := by
  unfold doubledAdvantage
  rw [weightedCorrectMass_eq_weightedTotalMass_of_supportwise_correct
    u y w h hcorrect]
  omega

/-- The same exact doubled-advantage identity follows directly from exact total
correctness. -/
theorem doubledAdvantage_eq_weightedTotalMass_of_weightedCorrectMass_eq_weightedTotalMass
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool)
    (hperfect : weightedCorrectMass u y w h = weightedTotalMass w) :
    doubledAdvantage u y w h = weightedTotalMass w := by
  unfold doubledAdvantage
  omega

/-- Spending the whole supported mass as doubled advantage already forces exact
supported correctness. -/
theorem weightedCorrectMass_eq_weightedTotalMass_of_doubledAdvantage_eq_weightedTotalMass
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool)
    (hadv : doubledAdvantage u y w h = weightedTotalMass w) :
    weightedCorrectMass u y w h = weightedTotalMass w := by
  unfold doubledAdvantage at hadv
  omega

/-- Exact supported correctness is equivalent to spending the whole supported
mass as doubled advantage. -/
theorem weightedCorrectMass_eq_weightedTotalMass_iff_doubledAdvantage_eq_weightedTotalMass
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool) :
    weightedCorrectMass u y w h = weightedTotalMass w ↔
      doubledAdvantage u y w h = weightedTotalMass w := by
  constructor
  · intro hperfect
    exact
      doubledAdvantage_eq_weightedTotalMass_of_weightedCorrectMass_eq_weightedTotalMass
        u y w h hperfect
  · intro hadv
    exact
      weightedCorrectMass_eq_weightedTotalMass_of_doubledAdvantage_eq_weightedTotalMass
        u y w h hadv

/-- Any doubled success advantage achieved using an invariant feature map plus
side channel is bounded by the mass where the side channel resolves involution
pairs. -/
theorem doubledAdvantage_pair_le_resolvedMass
    (τ : α → α) (u : α → U) (v : α → V) (y : α → Bool) (w : α → ℕ)
    (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x) :
    doubledAdvantage (fun x => (u x, v x)) y w h ≤ resolvedMass τ v w := by
  unfold doubledAdvantage
  have hbound :
      2 * weightedCorrectMass (fun x => (u x, v x)) y w h
        ≤ weightedTotalMass w + resolvedMass τ v w :=
    two_mul_weightedCorrectMass_pair_le_total_plus_resolvedMass
      τ u v y w h hτ hu hy hw
  omega

/-- A claimed doubled advantage of at least `δ` forces at least `δ` units of
orbit-resolving side-channel mass. -/
theorem resolvedMass_ge_of_le_doubledAdvantage_pair
    (τ : α → α) (u : α → U) (v : α → V) (y : α → Bool) (w : α → ℕ)
    (h : U × V → Bool) (δ : ℕ)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hδ :
      δ ≤ doubledAdvantage (fun x => (u x, v x)) y w h) :
    δ ≤ resolvedMass τ v w :=
  le_trans hδ <|
    doubledAdvantage_pair_le_resolvedMass τ u v y w h hτ hu hy hw

/-- A direct half-accuracy form: if the classifier using an invariant feature
plus residual side channel beats chance by `δ`, then the residual side channel
must resolve at least `δ` units of orbit mass. -/
theorem resolvedMass_ge_of_total_plus_delta_le_two_mul_weightedCorrectMass_pair
    (τ : α → α) (u : α → U) (v : α → V) (y : α → Bool) (w : α → ℕ)
    (h : U × V → Bool) (δ : ℕ)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hδ :
      weightedTotalMass w + δ ≤
        2 * weightedCorrectMass (fun x => (u x, v x)) y w h) :
    δ ≤ resolvedMass τ v w := by
  have hbound :
      2 * weightedCorrectMass (fun x => (u x, v x)) y w h
        ≤ weightedTotalMass w + resolvedMass τ v w :=
    two_mul_weightedCorrectMass_pair_le_total_plus_resolvedMass
      τ u v y w h hτ hu hy hw
  omega

/-- Strict success above half accuracy forces positive orbit-resolving
side-channel mass. -/
theorem resolvedMass_pos_of_total_lt_two_mul_weightedCorrectMass_pair
    (τ : α → α) (u : α → U) (v : α → V) (y : α → Bool) (w : α → ℕ)
    (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv :
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (u x, v x)) y w h) :
    0 < resolvedMass τ v w := by
  have hle :
      1 ≤ resolvedMass τ v w :=
    resolvedMass_ge_of_total_plus_delta_le_two_mul_weightedCorrectMass_pair
      τ u v y w h 1 hτ hu hy hw (by omega)
  omega

/-- If a residual side channel resolves no involution-paired mass, then it
cannot support any positive doubled advantage. -/
theorem not_pos_doubledAdvantage_pair_of_resolvedMass_eq_zero
    (τ : α → α) (u : α → U) (v : α → V) (y : α → Bool) (w : α → ℕ)
    (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hres : resolvedMass τ v w = 0) :
    ¬ 0 < doubledAdvantage (fun x => (u x, v x)) y w h := by
  have hle :
    doubledAdvantage (fun x => (u x, v x)) y w h ≤ resolvedMass τ v w :=
    doubledAdvantage_pair_le_resolvedMass τ u v y w h hτ hu hy hw
  omega

/-- If a residual side channel is unresolved everywhere, its resolved mass is
zero. -/
theorem resolvedMass_eq_zero_of_unresolved
    (τ : α → α) (v : α → V) (w : α → ℕ)
    (hunresolved : ∀ x, v (τ x) = v x) :
    resolvedMass τ v w = 0 := by
  classical
  unfold resolvedMass outsideMass sliceMass
  apply Finset.sum_eq_zero
  intro x _
  exfalso
  exact x.2 (by
    dsimp [unresolvedBySideChannel]
    exact hunresolved x.1)

/-- If a residual side channel is unresolved on every positive-weight point,
its resolved mass is zero. -/
theorem resolvedMass_eq_zero_of_supportwise_unresolved
    (τ : α → α) (v : α → V) (w : α → ℕ)
    (hunresolved : ∀ x, 0 < w x → v (τ x) = v x) :
    resolvedMass τ v w = 0 := by
  classical
  unfold resolvedMass outsideMass sliceMass
  apply Finset.sum_eq_zero
  intro x _
  by_cases hx : 0 < w x.1
  · exfalso
    exact x.2 (by
      dsimp [unresolvedBySideChannel]
      exact hunresolved x.1 hx)
  · have hx0 : w x.1 = 0 := Nat.eq_zero_of_not_pos hx
    simp [hx0]

/-- If a residual side channel changes across every positive-weight involution
pair, then all supported mass is orbit-resolving mass. -/
theorem resolvedMass_le_weightedTotalMass
    (τ : α → α) (v : α → V) (w : α → ℕ) :
    resolvedMass τ v w ≤ weightedTotalMass w := by
  classical
  have hsplit :=
    weightedTotalMass_eq_slice_add_outside
      (p := unresolvedBySideChannel τ v)
      (w := w)
  unfold resolvedMass
  omega

theorem resolvedMass_eq_weightedTotalMass_of_supportwise_resolving
    (τ : α → α) (v : α → V) (w : α → ℕ)
    (hresolve : ∀ x, 0 < w x → v (τ x) ≠ v x) :
    resolvedMass τ v w = weightedTotalMass w := by
  classical
  have hslice :
      sliceMass (unresolvedBySideChannel τ v) w = 0 := by
    unfold sliceMass
    apply Finset.sum_eq_zero
    intro x _
    by_cases hx : 0 < w x.1
    · exfalso
      exact hresolve x.1 hx x.2
    · exact Nat.eq_zero_of_not_pos hx
  have hsplit :=
    weightedTotalMass_eq_slice_add_outside
      (p := unresolvedBySideChannel τ v)
      (w := w)
  unfold resolvedMass
  simpa [hslice] using hsplit.symm

/-- The orbit-resolving mass is all supported mass exactly when the side
channel changes across every positive-weight involution pair. -/
theorem resolvedMass_eq_weightedTotalMass_iff_supportwise_resolving
    (τ : α → α) (v : α → V) (w : α → ℕ) :
    resolvedMass τ v w = weightedTotalMass w ↔
      ∀ x, 0 < w x → v (τ x) ≠ v x := by
  constructor
  · intro hmass x hxw hside
    classical
    let p : α → Prop := unresolvedBySideChannel τ v
    have hsplit :
        weightedTotalMass w = sliceMass p w + resolvedMass τ v w := by
      unfold resolvedMass outsideMass
      simpa [p] using
        weightedTotalMass_eq_slice_add_outside (p := p) (w := w)
    have hzero : sliceMass p w = 0 := by
      omega
    let x' : {a : α // p a} := ⟨x, by simpa [p, unresolvedBySideChannel] using hside⟩
    have hle' :
        w x'.1 ≤ ∑ y : {a : α // p a}, w y.1 := by
      exact
        Finset.single_le_sum
          (f := fun y : {a : α // p a} => w y.1)
          (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ x')
    have hle :
        w x ≤ ∑ y : {a : α // p a}, w y.1 := by
      simpa [x'] using hle'
    unfold sliceMass at hzero
    have hle0 : w x ≤ 0 := by
      simpa [hzero] using hle
    omega
  · intro hresolve
    exact resolvedMass_eq_weightedTotalMass_of_supportwise_resolving τ v w hresolve

/-- If a classifier on `(u, v)` is correct on every positive-weight point,
then the residual side channel must resolve all supported involution pairs. -/
theorem resolvedMass_eq_weightedTotalMass_of_weightedCorrectMass_eq_weightedTotalMass_pair
    (τ : α → α) (u : α → U) (v : α → V) (y : α → Bool) (w : α → ℕ)
    (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hperfect :
      weightedCorrectMass (fun x => (u x, v x)) y w h =
        weightedTotalMass w) :
    resolvedMass τ v w = weightedTotalMass w := by
  have hbound :
      2 * weightedCorrectMass (fun x => (u x, v x)) y w h
        ≤ weightedTotalMass w + resolvedMass τ v w :=
    two_mul_weightedCorrectMass_pair_le_total_plus_resolvedMass
      τ u v y w h hτ hu hy hw
  have hupper : resolvedMass τ v w ≤ weightedTotalMass w :=
    resolvedMass_le_weightedTotalMass τ v w
  omega

/-- Perfect supported correctness on `(u, v)` forces the side channel to
change across every positive-weight involution pair. -/
theorem supportwise_resolving_of_weightedCorrectMass_eq_weightedTotalMass_pair
    (τ : α → α) (u : α → U) (v : α → V) (y : α → Bool) (w : α → ℕ)
    (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hperfect :
      weightedCorrectMass (fun x => (u x, v x)) y w h =
        weightedTotalMass w) :
    ∀ x, 0 < w x → v (τ x) ≠ v x := by
  exact
    (resolvedMass_eq_weightedTotalMass_iff_supportwise_resolving τ v w).1
      (resolvedMass_eq_weightedTotalMass_of_weightedCorrectMass_eq_weightedTotalMass_pair
        τ u v y w h hτ hu hy hw hperfect)

/-- Under exact total correctness on an invariant-pair feature surface, the
classifier's doubled advantage is exactly the orbit-resolving mass. -/
theorem doubledAdvantage_eq_resolvedMass_of_weightedCorrectMass_eq_weightedTotalMass_pair
    (τ : α → α) (u : α → U) (v : α → V) (y : α → Bool) (w : α → ℕ)
    (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hperfect :
      weightedCorrectMass (fun x => (u x, v x)) y w h =
        weightedTotalMass w) :
    doubledAdvantage (fun x => (u x, v x)) y w h = resolvedMass τ v w := by
  rw [doubledAdvantage_eq_weightedTotalMass_of_weightedCorrectMass_eq_weightedTotalMass
    (fun x => (u x, v x)) y w h hperfect]
  exact
    (resolvedMass_eq_weightedTotalMass_of_weightedCorrectMass_eq_weightedTotalMass_pair
      τ u v y w h hτ hu hy hw hperfect).symm

/-- A supportwise-unresolved residual side channel cannot support positive
doubled advantage. -/
theorem not_pos_doubledAdvantage_pair_of_supportwise_unresolved
    (τ : α → α) (u : α → U) (v : α → V) (y : α → Bool) (w : α → ℕ)
    (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hunresolved : ∀ x, 0 < w x → v (τ x) = v x) :
    ¬ 0 < doubledAdvantage (fun x => (u x, v x)) y w h := by
  exact
    not_pos_doubledAdvantage_pair_of_resolvedMass_eq_zero
      τ u v y w h hτ hu hy hw
      (resolvedMass_eq_zero_of_supportwise_unresolved τ v w hunresolved)

/-- If the final Boolean prediction is involution-invariant on all
positive-weight points, then it cannot beat half accuracy.  This blocks a
repair where a classifier syntactically uses a side channel but its realized
predictions on support still factor through an invariant source summary. -/
theorem not_total_lt_two_mul_weightedCorrectMass_of_supportwise_prediction_invariant
    (τ : α → α) (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool)
    (hτ : Function.Involutive τ)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hpred : ∀ x, 0 < w x → h (u (τ x)) = h (u x)) :
    ¬ weightedTotalMass w < 2 * weightedCorrectMass u y w h := by
  classical
  let p : α → Prop := fun x => 0 < w x
  let pred : α → Bool := fun x => h (u x)
  have hp : ∀ x, p x → p (τ x) := by
    intro x hx
    dsimp [p] at hx ⊢
    simpa [hw x] using hx
  have hpred_inv : ∀ x, p x → pred (τ x) = pred x := by
    intro x hx
    dsimp [p] at hx
    exact hpred x hx
  have hsupport : ∀ x, 0 < w x → p x := by
    intro x hx
    exact hx
  have hno :
      ¬ weightedTotalMass w <
        2 * weightedCorrectMass pred y w (fun b : Bool => b) :=
    not_total_lt_two_mul_weightedCorrectMass_of_support_subset
      τ p pred y w (fun b : Bool => b) hτ hp hpred_inv
      (fun x _ => hy x) (fun x _ => hw x) hsupport
  have hmass :
      weightedCorrectMass pred y w (fun b : Bool => b) =
        weightedCorrectMass u y w h := by
    rfl
  intro hadv
  exact hno (by simpa [hmass] using hadv)

/-- Positive doubled advantage is impossible under the same supportwise
prediction-invariance condition. -/
theorem not_pos_doubledAdvantage_of_supportwise_prediction_invariant
    (τ : α → α) (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool)
    (hτ : Function.Involutive τ)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hpred : ∀ x, 0 < w x → h (u (τ x)) = h (u x)) :
    ¬ 0 < doubledAdvantage u y w h := by
  intro hadv
  have hno :=
    not_total_lt_two_mul_weightedCorrectMass_of_supportwise_prediction_invariant
      τ u y w h hτ hy hw hpred
  have hlt : weightedTotalMass w < 2 * weightedCorrectMass u y w h := by
    unfold doubledAdvantage at hadv
    omega
  exact hno hlt

/-- Any positive doubled advantage must be witnessed by a positive-weight
involution pair where the final prediction actually changes. -/
theorem exists_positive_prediction_ne_of_pos_doubledAdvantage
    (τ : α → α) (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool)
    (hτ : Function.Involutive τ)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv : 0 < doubledAdvantage u y w h) :
    ∃ x, 0 < w x ∧ h (u (τ x)) ≠ h (u x) := by
  by_contra hnone
  have hpred : ∀ x, 0 < w x → h (u (τ x)) = h (u x) := by
    intro x hx
    by_contra hneq
    exact hnone ⟨x, hx, hneq⟩
  exact
    (not_pos_doubledAdvantage_of_supportwise_prediction_invariant
      τ u y w h hτ hy hw hpred) hadv

/-- The same prediction-separation witness follows from strict half-accuracy
advantage. -/
theorem exists_positive_prediction_ne_of_total_lt_two_mul_weightedCorrectMass
    (τ : α → α) (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool)
    (hτ : Function.Involutive τ)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv : weightedTotalMass w < 2 * weightedCorrectMass u y w h) :
    ∃ x, 0 < w x ∧ h (u (τ x)) ≠ h (u x) := by
  by_contra hnone
  have hpred : ∀ x, 0 < w x → h (u (τ x)) = h (u x) := by
    intro x hx
    by_contra hneq
    exact hnone ⟨x, hx, hneq⟩
  exact
    (not_total_lt_two_mul_weightedCorrectMass_of_supportwise_prediction_invariant
      τ u y w h hτ hy hw hpred) hadv

/-- Equivalently, every positive doubled advantage witnesses positive
orbit-resolving side-channel mass. -/
theorem resolvedMass_pos_of_pos_doubledAdvantage_pair
    (τ : α → α) (u : α → U) (v : α → V) (y : α → Bool) (w : α → ℕ)
    (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv : 0 < doubledAdvantage (fun x => (u x, v x)) y w h) :
    0 < resolvedMass τ v w := by
  have hle :
      doubledAdvantage (fun x => (u x, v x)) y w h ≤ resolvedMass τ v w :=
    doubledAdvantage_pair_le_resolvedMass τ u v y w h hτ hu hy hw
  omega

/-- Positive orbit-resolving mass exposes a positive-weight point where the
side-channel value changes across the involution. -/
theorem exists_resolving_point_of_pos_resolvedMass
    (τ : α → α) (v : α → V) (w : α → ℕ)
    (hmass : 0 < resolvedMass τ v w) :
    ∃ x, 0 < w x ∧ v (τ x) ≠ v x := by
  classical
  by_contra hnone
  have hunresolved : ∀ x, 0 < w x → v (τ x) = v x := by
    intro x hx
    by_contra hneq
    exact hnone ⟨x, hx, hneq⟩
  have hzero := resolvedMass_eq_zero_of_supportwise_unresolved τ v w hunresolved
  omega

/-- Conversely, one positive-weight point where the side channel changes across
the involution already gives positive orbit-resolving mass. -/
theorem resolvedMass_pos_of_resolving_point
    (τ : α → α) (v : α → V) (w : α → ℕ)
    {x : α} (hx : 0 < w x) (hchange : v (τ x) ≠ v x) :
    0 < resolvedMass τ v w := by
  classical
  unfold resolvedMass outsideMass sliceMass
  let x' : {a : α // ¬ unresolvedBySideChannel τ v a} :=
    ⟨x, by
      dsimp [unresolvedBySideChannel]
      exact hchange⟩
  have hle :
      w x ≤ ∑ y : {a : α // ¬ unresolvedBySideChannel τ v a}, w y.1 := by
    simpa [x'] using
      (Finset.single_le_sum
        (f := fun y : {a : α // ¬ unresolvedBySideChannel τ v a} => w y.1)
        (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ x'))
  exact lt_of_lt_of_le hx hle

/-- Every strict half-accuracy advantage from an invariant feature plus
residual side channel exposes a positive-weight point where the side channel
changes across the involution. -/
theorem exists_resolving_point_of_total_lt_two_mul_weightedCorrectMass_pair
    (τ : α → α) (u : α → U) (v : α → V) (y : α → Bool) (w : α → ℕ)
    (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv :
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (u x, v x)) y w h) :
    ∃ x, 0 < w x ∧ v (τ x) ≠ v x :=
  exists_resolving_point_of_pos_resolvedMass τ v w
    (resolvedMass_pos_of_total_lt_two_mul_weightedCorrectMass_pair
      τ u v y w h hτ hu hy hw hadv)

/-- Every positive doubled advantage from an invariant feature plus residual
side channel exposes a positive-weight point where the side channel changes
across the involution. -/
theorem exists_resolving_point_of_pos_doubledAdvantage_pair
    (τ : α → α) (u : α → U) (v : α → V) (y : α → Bool) (w : α → ℕ)
    (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv : 0 < doubledAdvantage (fun x => (u x, v x)) y w h) :
    ∃ x, 0 < w x ∧ v (τ x) ≠ v x :=
  exists_resolving_point_of_pos_resolvedMass τ v w
    (resolvedMass_pos_of_pos_doubledAdvantage_pair
      τ u v y w h hτ hu hy hw hadv)

end

end Mettapedia.Computability.PNP
