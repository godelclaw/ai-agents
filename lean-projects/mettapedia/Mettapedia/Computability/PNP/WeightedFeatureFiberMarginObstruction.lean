import Mettapedia.Computability.PNP.WeightedFiberNeutralityObstruction
import Mettapedia.Computability.PNP.ResolutionDemandObstruction
import Mathlib.Tactic

/-!
# P vs NP crux: fiber-balanced visible surfaces have exact zero margin

The residual-side counterexamples show that positive resolved mass and even
concrete proof-relevant witnesses still need not imply any visible-surface
success. One structural reason is that the visible surface may remain balanced
fiberwise: for each retained visible value, the total weight of `true` labels
matches the total weight of `false` labels.

This file isolates that obstruction directly. If every retained feature fiber is
weight-balanced in that sense, then every classifier using only those retained
features has exact half accuracy, hence zero doubled advantage.
-/

namespace Mettapedia.Computability.PNP

section

variable {α U : Type*} [Fintype α] [DecidableEq U]

/-- Flatten the nested `true` fiber subtype into a single conjunction subtype. -/
def featureFiberTrueEquivAnd
    (u : α → U) (y : α → Bool) (v : U) :
    FeatureFiberTrue u y v ≃ {x : α // u x = v ∧ y x = true} where
  toFun x := ⟨x.1.1, x.1.2, x.2⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl

/-- Flatten the nested `false` fiber subtype into a single conjunction subtype. -/
def featureFiberFalseEquivAnd
    (u : α → U) (y : α → Bool) (v : U) :
    FeatureFiberFalse u y v ≃ {x : α // u x = v ∧ y x = false} where
  toFun x := ⟨x.1.1, x.1.2, x.2⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl

/-- The weighted `true` mass on one visible fiber is the corresponding filtered
sum over the ambient finite domain. -/
theorem weightedFeatureFiberTrueMass_eq_sum_filter
    (u : α → U) (y : α → Bool) (w : α → ℕ) (v : U) :
    weightedFeatureFiberTrueMass u y w v =
      ∑ x ∈ (Finset.univ : Finset α) with u x = v ∧ y x = true, w x := by
  classical
  unfold weightedFeatureFiberTrueMass
  calc
    (∑ x : FeatureFiberTrue u y v, w x.1.1)
        = ∑ x : {x : α // u x = v ∧ y x = true}, w x.1 := by
            exact Fintype.sum_equiv
              (featureFiberTrueEquivAnd u y v)
              (fun x : FeatureFiberTrue u y v => w x.1.1)
              (fun x : {x : α // u x = v ∧ y x = true} => w x.1)
              (fun _ => rfl)
    _ = ∑ x ∈ (Finset.univ : Finset α) with u x = v ∧ y x = true, w x := by
      simpa using
    (Finset.sum_subtype_eq_sum_filter
      (s := (Finset.univ : Finset α))
      (p := fun x => u x = v ∧ y x = true)
      (f := w))

/-- The weighted `false` mass on one visible fiber is the corresponding filtered
sum over the ambient finite domain. -/
theorem weightedFeatureFiberFalseMass_eq_sum_filter
    (u : α → U) (y : α → Bool) (w : α → ℕ) (v : U) :
    weightedFeatureFiberFalseMass u y w v =
      ∑ x ∈ (Finset.univ : Finset α) with u x = v ∧ y x = false, w x := by
  classical
  unfold weightedFeatureFiberFalseMass
  calc
    (∑ x : FeatureFiberFalse u y v, w x.1.1)
        = ∑ x : {x : α // u x = v ∧ y x = false}, w x.1 := by
            exact Fintype.sum_equiv
              (featureFiberFalseEquivAnd u y v)
              (fun x : FeatureFiberFalse u y v => w x.1.1)
              (fun x : {x : α // u x = v ∧ y x = false} => w x.1)
              (fun _ => rfl)
    _ = ∑ x ∈ (Finset.univ : Finset α) with u x = v ∧ y x = false, w x := by
      simpa using
    (Finset.sum_subtype_eq_sum_filter
      (s := (Finset.univ : Finset α))
      (p := fun x => u x = v ∧ y x = false)
      (f := w))

section

variable [Fintype U]

/-- Predict `true` on a visible fiber exactly when the retained `true` mass on
that fiber strictly exceeds the retained `false` mass. -/
def weightedFeatureFiberMajorityClassifier
    (u : α → U) (y : α → Bool) (w : α → ℕ) : U → Bool := fun v =>
  if weightedFeatureFiberFalseMass u y w v < weightedFeatureFiberTrueMass u y w v
    then true
    else false

/-- The correct mass splits into the `true`-labeled mass on fibers predicted
`true` and the `false`-labeled mass on fibers predicted `false`. -/
theorem weightedCorrectMass_eq_sum_predictedTrue_trueMass_add_sum_predictedFalse_falseMass
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool) :
    weightedCorrectMass u y w h =
      (∑ v ∈ (Finset.univ : Finset U).filter (fun v => h v = true),
        weightedFeatureFiberTrueMass u y w v) +
      ∑ v ∈ (Finset.univ : Finset U).filter (fun v => h v = false),
        weightedFeatureFiberFalseMass u y w v := by
  classical
  have htrue :
      ∑ x ∈ (Finset.univ : Finset α) with y x = true ∧ h (u x) = true, w x =
        ∑ v ∈ (Finset.univ : Finset U).filter (fun v => h v = true),
          weightedFeatureFiberTrueMass u y w v := by
    calc
      ∑ x ∈ (Finset.univ : Finset α) with y x = true ∧ h (u x) = true, w x
          =
        ∑ v ∈ (Finset.univ : Finset U).filter (fun v => h v = true),
          ∑ x ∈ ((Finset.univ : Finset α).filter (fun x => y x = true)) with u x = v, w x := by
            simpa [Finset.filter_filter, and_left_comm, and_assoc] using
              (Finset.sum_fiberwise_eq_sum_filter
                ((Finset.univ : Finset α).filter (fun x => y x = true))
                ((Finset.univ : Finset U).filter (fun v => h v = true))
                u w).symm
      _ =
        ∑ v ∈ (Finset.univ : Finset U).filter (fun v => h v = true),
          weightedFeatureFiberTrueMass u y w v := by
            refine Finset.sum_congr rfl ?_
            intro v hv
            simpa [Finset.filter_filter, and_comm, and_left_comm, and_assoc] using
              (weightedFeatureFiberTrueMass_eq_sum_filter u y w v).symm
  have hfalse :
      ∑ x ∈ (Finset.univ : Finset α) with y x = false ∧ h (u x) = false, w x =
        ∑ v ∈ (Finset.univ : Finset U).filter (fun v => h v = false),
          weightedFeatureFiberFalseMass u y w v := by
    calc
      ∑ x ∈ (Finset.univ : Finset α) with y x = false ∧ h (u x) = false, w x
          =
        ∑ v ∈ (Finset.univ : Finset U).filter (fun v => h v = false),
          ∑ x ∈ ((Finset.univ : Finset α).filter (fun x => y x = false)) with u x = v, w x := by
            simpa [Finset.filter_filter, and_left_comm, and_assoc] using
              (Finset.sum_fiberwise_eq_sum_filter
                ((Finset.univ : Finset α).filter (fun x => y x = false))
                ((Finset.univ : Finset U).filter (fun v => h v = false))
                u w).symm
      _ =
        ∑ v ∈ (Finset.univ : Finset U).filter (fun v => h v = false),
          weightedFeatureFiberFalseMass u y w v := by
            refine Finset.sum_congr rfl ?_
            intro v hv
            simpa [Finset.filter_filter, and_comm, and_left_comm, and_assoc] using
              (weightedFeatureFiberFalseMass_eq_sum_filter u y w v).symm
  have hfilter :
      weightedCorrectMass u y w h =
        ∑ x ∈ (Finset.univ : Finset α) with h (u x) = y x, w x := by
    unfold weightedCorrectMass
    simpa [Correct] using
      (Finset.sum_subtype_eq_sum_filter
        (s := (Finset.univ : Finset α))
        (p := fun x => h (u x) = y x)
        (f := w))
  have hsplit :
      ∑ x ∈ (Finset.univ : Finset α) with h (u x) = y x, w x =
        (∑ x ∈ (Finset.univ : Finset α) with y x = true ∧ h (u x) = true, w x) +
        ∑ x ∈ (Finset.univ : Finset α) with y x = false ∧ h (u x) = false, w x := by
    rw [← Finset.sum_filter_add_sum_filter_not
      (s := (Finset.univ : Finset α).filter (fun x => h (u x) = y x))
      (p := fun x => y x = true)]
    have h1 :
        ∑ x ∈ ((Finset.univ : Finset α).filter (fun x => h (u x) = y x)) with y x = true, w x =
          ∑ x ∈ (Finset.univ : Finset α) with y x = true ∧ h (u x) = true, w x := by
      have hpred :
          (fun x : α => h (u x) = y x ∧ y x = true) =
            (fun x : α => y x = true ∧ h (u x) = true) := by
        funext x
        by_cases hy : y x <;> simp [hy]
      simp [Finset.filter_filter, hpred]
    have h2 :
        ∑ x ∈ ((Finset.univ : Finset α).filter (fun x => h (u x) = y x)) with ¬ y x = true, w x =
          ∑ x ∈ (Finset.univ : Finset α) with y x = false ∧ h (u x) = false, w x := by
      rw [Finset.filter_filter]
      have hpred :
          (fun x : α => h (u x) = y x ∧ y x = false) =
            (fun x : α => y x = false ∧ h (u x) = false) := by
        funext x
        by_cases hy : y x <;> simp [hy]
      simp [hpred]
    rw [h1, h2]
  rw [hfilter, hsplit, htrue, hfalse]

/-- The incorrect mass splits into the `false`-labeled mass on fibers predicted
`true` and the `true`-labeled mass on fibers predicted `false`. -/
theorem weightedIncorrectMass_eq_sum_predictedTrue_falseMass_add_sum_predictedFalse_trueMass
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool) :
    weightedIncorrectMass u y w h =
      (∑ v ∈ (Finset.univ : Finset U).filter (fun v => h v = true),
        weightedFeatureFiberFalseMass u y w v) +
      ∑ v ∈ (Finset.univ : Finset U).filter (fun v => h v = false),
        weightedFeatureFiberTrueMass u y w v := by
  classical
  have htrue :
      ∑ x ∈ (Finset.univ : Finset α) with y x = false ∧ h (u x) = true, w x =
        ∑ v ∈ (Finset.univ : Finset U).filter (fun v => h v = true),
          weightedFeatureFiberFalseMass u y w v := by
    calc
      ∑ x ∈ (Finset.univ : Finset α) with y x = false ∧ h (u x) = true, w x
          =
        ∑ v ∈ (Finset.univ : Finset U).filter (fun v => h v = true),
          ∑ x ∈ ((Finset.univ : Finset α).filter (fun x => y x = false)) with u x = v, w x := by
            simpa [Finset.filter_filter, and_left_comm, and_assoc] using
              (Finset.sum_fiberwise_eq_sum_filter
                ((Finset.univ : Finset α).filter (fun x => y x = false))
                ((Finset.univ : Finset U).filter (fun v => h v = true))
                u w).symm
      _ =
        ∑ v ∈ (Finset.univ : Finset U).filter (fun v => h v = true),
          weightedFeatureFiberFalseMass u y w v := by
            refine Finset.sum_congr rfl ?_
            intro v hv
            simpa [Finset.filter_filter, and_comm, and_left_comm, and_assoc] using
              (weightedFeatureFiberFalseMass_eq_sum_filter u y w v).symm
  have hfalse :
      ∑ x ∈ (Finset.univ : Finset α) with y x = true ∧ h (u x) = false, w x =
        ∑ v ∈ (Finset.univ : Finset U).filter (fun v => h v = false),
          weightedFeatureFiberTrueMass u y w v := by
    calc
      ∑ x ∈ (Finset.univ : Finset α) with y x = true ∧ h (u x) = false, w x
          =
        ∑ v ∈ (Finset.univ : Finset U).filter (fun v => h v = false),
          ∑ x ∈ ((Finset.univ : Finset α).filter (fun x => y x = true)) with u x = v, w x := by
            simpa [Finset.filter_filter, and_left_comm, and_assoc] using
              (Finset.sum_fiberwise_eq_sum_filter
                ((Finset.univ : Finset α).filter (fun x => y x = true))
                ((Finset.univ : Finset U).filter (fun v => h v = false))
                u w).symm
      _ =
        ∑ v ∈ (Finset.univ : Finset U).filter (fun v => h v = false),
          weightedFeatureFiberTrueMass u y w v := by
            refine Finset.sum_congr rfl ?_
            intro v hv
            simpa [Finset.filter_filter, and_comm, and_left_comm, and_assoc] using
              (weightedFeatureFiberTrueMass_eq_sum_filter u y w v).symm
  have hfilter :
      weightedIncorrectMass u y w h =
        ∑ x ∈ (Finset.univ : Finset α) with ¬ h (u x) = y x, w x := by
    unfold weightedIncorrectMass Incorrect
    simpa using
      (Finset.sum_subtype_eq_sum_filter
        (s := (Finset.univ : Finset α))
        (p := fun x => ¬ h (u x) = y x)
        (f := w))
  have hsplit :
      ∑ x ∈ (Finset.univ : Finset α) with ¬ h (u x) = y x, w x =
        (∑ x ∈ (Finset.univ : Finset α) with y x = false ∧ h (u x) = true, w x) +
        ∑ x ∈ (Finset.univ : Finset α) with y x = true ∧ h (u x) = false, w x := by
    rw [← Finset.sum_filter_add_sum_filter_not
      (s := (Finset.univ : Finset α).filter (fun x => ¬ h (u x) = y x))
      (p := fun x => y x = false)]
    have h1 :
        ∑ x ∈ ((Finset.univ : Finset α).filter (fun x => ¬ h (u x) = y x)) with y x = false, w x =
          ∑ x ∈ (Finset.univ : Finset α) with y x = false ∧ h (u x) = true, w x := by
      have hpred :
          (fun x : α => ¬ h (u x) = y x ∧ y x = false) =
            (fun x : α => y x = false ∧ h (u x) = true) := by
        funext x
        by_cases hy : y x <;> simp [hy]
      simp [Finset.filter_filter, hpred]
    have h2 :
        ∑ x ∈ ((Finset.univ : Finset α).filter (fun x => ¬ h (u x) = y x)) with ¬ y x = false, w x =
          ∑ x ∈ (Finset.univ : Finset α) with y x = true ∧ h (u x) = false, w x := by
      rw [Finset.filter_filter]
      have hpred :
          (fun x : α => ¬ h (u x) = y x ∧ y x = true) =
            (fun x : α => y x = true ∧ h (u x) = false) := by
        funext x
        by_cases hy : y x <;> simp [hy]
      simp [hpred]
    rw [h1, h2]
  rw [hfilter, hsplit, htrue, hfalse]

/-- If every visible fiber has balanced `true` and `false` weight, then every
classifier on those visible features has exactly the same correct and incorrect
mass. -/
theorem weightedCorrectMass_eq_weightedIncorrectMass_of_weightedFeatureFiberBalanced
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool)
    (hbal :
      ∀ v : U,
        weightedFeatureFiberTrueMass u y w v =
          weightedFeatureFiberFalseMass u y w v) :
    weightedCorrectMass u y w h = weightedIncorrectMass u y w h := by
  rw [weightedCorrectMass_eq_sum_predictedTrue_trueMass_add_sum_predictedFalse_falseMass,
    weightedIncorrectMass_eq_sum_predictedTrue_falseMass_add_sum_predictedFalse_trueMass]
  congr 1
  · exact Finset.sum_congr rfl (fun v _ => hbal v)
  · exact Finset.sum_congr rfl (fun v _ => (hbal v).symm)

/-- Under the same fiber-balance hypothesis, every classifier on those visible
features has exact half weighted accuracy. -/
theorem two_mul_weightedCorrectMass_eq_weightedTotalMass_of_weightedFeatureFiberBalanced
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool)
    (hbal :
      ∀ v : U,
        weightedFeatureFiberTrueMass u y w v =
          weightedFeatureFiberFalseMass u y w v) :
    2 * weightedCorrectMass u y w h = weightedTotalMass w := by
  have hsplit :
      weightedTotalMass w =
        weightedCorrectMass u y w h + weightedIncorrectMass u y w h :=
    weightedTotalMass_eq_weightedCorrectMass_add_weightedIncorrectMass u y w h
  have heq :
      weightedCorrectMass u y w h = weightedIncorrectMass u y w h :=
    weightedCorrectMass_eq_weightedIncorrectMass_of_weightedFeatureFiberBalanced
      u y w h hbal
  omega

/-- Therefore the doubled advantage of any classifier on a fiber-balanced
visible surface is exactly zero. -/
theorem doubledAdvantage_eq_zero_of_weightedFeatureFiberBalanced
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool)
    (hbal :
      ∀ v : U,
        weightedFeatureFiberTrueMass u y w v =
          weightedFeatureFiberFalseMass u y w v) :
    doubledAdvantage u y w h = 0 := by
  unfold doubledAdvantage
  rw [two_mul_weightedCorrectMass_eq_weightedTotalMass_of_weightedFeatureFiberBalanced
    u y w h hbal]
  omega

/-- Fiber-balanced visible surfaces cannot support any positive doubled
advantage. -/
theorem not_pos_doubledAdvantage_of_weightedFeatureFiberBalanced
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool)
    (hbal :
      ∀ v : U,
        weightedFeatureFiberTrueMass u y w v =
          weightedFeatureFiberFalseMass u y w v) :
    ¬ 0 < doubledAdvantage u y w h := by
  rw [doubledAdvantage_eq_zero_of_weightedFeatureFiberBalanced u y w h hbal]
  simp

/-- The same fiber-balance hypothesis blocks every strict half-accuracy claim
on the visible surface. -/
theorem not_total_lt_two_mul_weightedCorrectMass_of_weightedFeatureFiberBalanced
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool)
    (hbal :
      ∀ v : U,
        weightedFeatureFiberTrueMass u y w v =
          weightedFeatureFiberFalseMass u y w v) :
    ¬ weightedTotalMass w < 2 * weightedCorrectMass u y w h := by
  rw [two_mul_weightedCorrectMass_eq_weightedTotalMass_of_weightedFeatureFiberBalanced
    u y w h hbal]
  simp

/-- Any positive doubled advantage on a finite visible surface must be witnessed
by at least one visible fiber with unequal `true` and `false` weighted mass. -/
theorem exists_weightedFeatureFiber_imbalance_of_pos_doubledAdvantage
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool)
    (hadv : 0 < doubledAdvantage u y w h) :
    ∃ v : U,
      weightedFeatureFiberTrueMass u y w v ≠
        weightedFeatureFiberFalseMass u y w v := by
  by_contra hno
  have hbal :
      ∀ v : U,
        weightedFeatureFiberTrueMass u y w v =
          weightedFeatureFiberFalseMass u y w v := by
    intro v
    by_contra hneq
    exact hno ⟨v, hneq⟩
  exact
    (not_pos_doubledAdvantage_of_weightedFeatureFiberBalanced
      u y w h hbal) hadv

/-- Likewise, any strict-half weighted success on a finite visible surface must
already exhibit a visible fiber with unequal `true` and `false` weighted mass. -/
theorem exists_weightedFeatureFiber_imbalance_of_total_lt_two_mul_weightedCorrectMass
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool)
    (hadv : weightedTotalMass w < 2 * weightedCorrectMass u y w h) :
    ∃ v : U,
      weightedFeatureFiberTrueMass u y w v ≠
        weightedFeatureFiberFalseMass u y w v := by
  by_contra hno
  have hbal :
      ∀ v : U,
        weightedFeatureFiberTrueMass u y w v =
          weightedFeatureFiberFalseMass u y w v := by
    intro v
    by_contra hneq
    exact hno ⟨v, hneq⟩
  exact
    (not_total_lt_two_mul_weightedCorrectMass_of_weightedFeatureFiberBalanced
      u y w h hbal) hadv

/-- The correct mass can be written as a single sum over visible fibers, where
each fiber contributes its `true` mass or `false` mass according to the
classifier's prediction on that fiber. -/
theorem weightedCorrectMass_eq_sum_if_weightedFeatureFiberMass
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool) :
    weightedCorrectMass u y w h =
      ∑ v : U,
        if h v = true
          then weightedFeatureFiberTrueMass u y w v
          else weightedFeatureFiberFalseMass u y w v := by
  classical
  rw [weightedCorrectMass_eq_sum_predictedTrue_trueMass_add_sum_predictedFalse_falseMass]
  have hsum :
      ∑ v ∈ (Finset.univ : Finset U).filter (fun v => h v = true),
          (if h v = true
            then weightedFeatureFiberTrueMass u y w v
            else weightedFeatureFiberFalseMass u y w v) +
        ∑ v ∈ (Finset.univ : Finset U).filter (fun v => ¬ h v = true),
          (if h v = true
            then weightedFeatureFiberTrueMass u y w v
            else weightedFeatureFiberFalseMass u y w v) =
        ∑ v : U,
          if h v = true
            then weightedFeatureFiberTrueMass u y w v
            else weightedFeatureFiberFalseMass u y w v := by
    simpa using
      (Finset.sum_filter_add_sum_filter_not
        (s := (Finset.univ : Finset U))
        (p := fun v => h v = true)
        (f := fun v =>
          if h v = true
            then weightedFeatureFiberTrueMass u y w v
            else weightedFeatureFiberFalseMass u y w v))
  calc
    ∑ v ∈ (Finset.univ : Finset U).filter (fun v => h v = true),
        weightedFeatureFiberTrueMass u y w v +
      ∑ v ∈ (Finset.univ : Finset U).filter (fun v => h v = false),
        weightedFeatureFiberFalseMass u y w v
        =
      ∑ v ∈ (Finset.univ : Finset U).filter (fun v => h v = true),
          (if h v = true
            then weightedFeatureFiberTrueMass u y w v
            else weightedFeatureFiberFalseMass u y w v) +
        ∑ v ∈ (Finset.univ : Finset U).filter (fun v => h v = false),
          (if h v = true
            then weightedFeatureFiberTrueMass u y w v
            else weightedFeatureFiberFalseMass u y w v) := by
            congr 1
            · refine Finset.sum_congr rfl ?_
              intro v hv
              have hvtrue : h v = true := (Finset.mem_filter.mp hv).2
              simp [hvtrue]
            · refine Finset.sum_congr rfl ?_
              intro v hv
              have hvfalse : h v = false := (Finset.mem_filter.mp hv).2
              simp [hvfalse]
    _ = ∑ v : U,
          if h v = true
            then weightedFeatureFiberTrueMass u y w v
            else weightedFeatureFiberFalseMass u y w v := by
          simpa using hsum

/-- The incorrect mass has the analogous one-sum form over visible fibers. -/
theorem weightedIncorrectMass_eq_sum_if_weightedFeatureFiberMass
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool) :
    weightedIncorrectMass u y w h =
      ∑ v : U,
        if h v = true
          then weightedFeatureFiberFalseMass u y w v
          else weightedFeatureFiberTrueMass u y w v := by
  classical
  rw [weightedIncorrectMass_eq_sum_predictedTrue_falseMass_add_sum_predictedFalse_trueMass]
  have hsum :
      ∑ v ∈ (Finset.univ : Finset U).filter (fun v => h v = true),
          (if h v = true
            then weightedFeatureFiberFalseMass u y w v
            else weightedFeatureFiberTrueMass u y w v) +
        ∑ v ∈ (Finset.univ : Finset U).filter (fun v => ¬ h v = true),
          (if h v = true
            then weightedFeatureFiberFalseMass u y w v
            else weightedFeatureFiberTrueMass u y w v) =
        ∑ v : U,
          if h v = true
            then weightedFeatureFiberFalseMass u y w v
            else weightedFeatureFiberTrueMass u y w v := by
    simpa using
      (Finset.sum_filter_add_sum_filter_not
        (s := (Finset.univ : Finset U))
        (p := fun v => h v = true)
        (f := fun v =>
          if h v = true
            then weightedFeatureFiberFalseMass u y w v
            else weightedFeatureFiberTrueMass u y w v))
  calc
    ∑ v ∈ (Finset.univ : Finset U).filter (fun v => h v = true),
        weightedFeatureFiberFalseMass u y w v +
      ∑ v ∈ (Finset.univ : Finset U).filter (fun v => h v = false),
        weightedFeatureFiberTrueMass u y w v
        =
      ∑ v ∈ (Finset.univ : Finset U).filter (fun v => h v = true),
          (if h v = true
            then weightedFeatureFiberFalseMass u y w v
            else weightedFeatureFiberTrueMass u y w v) +
        ∑ v ∈ (Finset.univ : Finset U).filter (fun v => h v = false),
          (if h v = true
            then weightedFeatureFiberFalseMass u y w v
            else weightedFeatureFiberTrueMass u y w v) := by
            congr 1
            · refine Finset.sum_congr rfl ?_
              intro v hv
              have hvtrue : h v = true := (Finset.mem_filter.mp hv).2
              simp [hvtrue]
            · refine Finset.sum_congr rfl ?_
              intro v hv
              have hvfalse : h v = false := (Finset.mem_filter.mp hv).2
              simp [hvfalse]
    _ = ∑ v : U,
          if h v = true
            then weightedFeatureFiberFalseMass u y w v
            else weightedFeatureFiberTrueMass u y w v := by
          simpa using hsum

/-- The fiber-majority classifier never does worse than chance on a finite
visible surface. -/
theorem weightedIncorrectMass_le_weightedCorrectMass_of_weightedFeatureFiberMajorityClassifier
    (u : α → U) (y : α → Bool) (w : α → ℕ) :
    weightedIncorrectMass u y w (weightedFeatureFiberMajorityClassifier u y w) ≤
      weightedCorrectMass u y w (weightedFeatureFiberMajorityClassifier u y w) := by
  classical
  rw [weightedIncorrectMass_eq_sum_if_weightedFeatureFiberMass,
    weightedCorrectMass_eq_sum_if_weightedFeatureFiberMass]
  refine Finset.sum_le_sum ?_
  intro v hv
  by_cases hlt :
      weightedFeatureFiberFalseMass u y w v <
        weightedFeatureFiberTrueMass u y w v
  · simp [weightedFeatureFiberMajorityClassifier, hlt, le_of_lt hlt]
  · have hle :
        weightedFeatureFiberTrueMass u y w v ≤
          weightedFeatureFiberFalseMass u y w v :=
      Nat.le_of_not_gt hlt
    simp [weightedFeatureFiberMajorityClassifier, hlt, hle]

/-- If some visible fiber carries unequal `true` and `false` mass, then the
fiber-majority classifier beats chance strictly. -/
theorem weightedIncorrectMass_lt_weightedCorrectMass_of_exists_weightedFeatureFiber_imbalance
    (u : α → U) (y : α → Bool) (w : α → ℕ)
    (himb :
      ∃ v : U,
        weightedFeatureFiberTrueMass u y w v ≠
          weightedFeatureFiberFalseMass u y w v) :
    weightedIncorrectMass u y w (weightedFeatureFiberMajorityClassifier u y w) <
      weightedCorrectMass u y w (weightedFeatureFiberMajorityClassifier u y w) := by
  classical
  rcases himb with ⟨v, hneq⟩
  rw [weightedIncorrectMass_eq_sum_if_weightedFeatureFiberMass,
    weightedCorrectMass_eq_sum_if_weightedFeatureFiberMass]
  have hle :
      ∀ z : U,
        (if weightedFeatureFiberMajorityClassifier u y w z = true
          then weightedFeatureFiberFalseMass u y w z
          else weightedFeatureFiberTrueMass u y w z)
          ≤
        (if weightedFeatureFiberMajorityClassifier u y w z = true
          then weightedFeatureFiberTrueMass u y w z
          else weightedFeatureFiberFalseMass u y w z) := by
    intro z
    by_cases hlt :
        weightedFeatureFiberFalseMass u y w z <
          weightedFeatureFiberTrueMass u y w z
    · simp [weightedFeatureFiberMajorityClassifier, hlt, le_of_lt hlt]
    · have hle :
          weightedFeatureFiberTrueMass u y w z ≤
            weightedFeatureFiberFalseMass u y w z :=
        Nat.le_of_not_gt hlt
      simp [weightedFeatureFiberMajorityClassifier, hlt, hle]
  have hstrict :
      (if weightedFeatureFiberMajorityClassifier u y w v = true
        then weightedFeatureFiberFalseMass u y w v
        else weightedFeatureFiberTrueMass u y w v)
        <
      (if weightedFeatureFiberMajorityClassifier u y w v = true
        then weightedFeatureFiberTrueMass u y w v
        else weightedFeatureFiberFalseMass u y w v) := by
    by_cases hlt :
        weightedFeatureFiberFalseMass u y w v <
          weightedFeatureFiberTrueMass u y w v
    · simp [weightedFeatureFiberMajorityClassifier, hlt]
    · have hlt' :
          weightedFeatureFiberTrueMass u y w v <
            weightedFeatureFiberFalseMass u y w v :=
        lt_of_le_of_ne (Nat.le_of_not_gt hlt) hneq
      simp [weightedFeatureFiberMajorityClassifier, hlt, hlt']
  exact Finset.sum_lt_sum (fun z _ => hle z) ⟨v, Finset.mem_univ v, hstrict⟩

/-- Visible-fiber imbalance is already sufficient for a positive doubled
advantage: predict by weighted fiber-majority. -/
theorem pos_doubledAdvantage_of_exists_weightedFeatureFiber_imbalance
    (u : α → U) (y : α → Bool) (w : α → ℕ)
    (himb :
      ∃ v : U,
        weightedFeatureFiberTrueMass u y w v ≠
          weightedFeatureFiberFalseMass u y w v) :
    0 < doubledAdvantage u y w (weightedFeatureFiberMajorityClassifier u y w) := by
  have hsplit :
      weightedTotalMass w =
        weightedCorrectMass u y w (weightedFeatureFiberMajorityClassifier u y w) +
          weightedIncorrectMass u y w (weightedFeatureFiberMajorityClassifier u y w) :=
    weightedTotalMass_eq_weightedCorrectMass_add_weightedIncorrectMass
      u y w (weightedFeatureFiberMajorityClassifier u y w)
  have hlt :
      weightedIncorrectMass u y w (weightedFeatureFiberMajorityClassifier u y w) <
        weightedCorrectMass u y w (weightedFeatureFiberMajorityClassifier u y w) :=
    weightedIncorrectMass_lt_weightedCorrectMass_of_exists_weightedFeatureFiber_imbalance
      u y w himb
  unfold doubledAdvantage
  omega

/-- The same majority classifier then beats strict half weighted accuracy. -/
theorem total_lt_two_mul_weightedCorrectMass_of_exists_weightedFeatureFiber_imbalance
    (u : α → U) (y : α → Bool) (w : α → ℕ)
    (himb :
      ∃ v : U,
        weightedFeatureFiberTrueMass u y w v ≠
          weightedFeatureFiberFalseMass u y w v) :
    weightedTotalMass w <
      2 * weightedCorrectMass u y w (weightedFeatureFiberMajorityClassifier u y w) := by
  have hsplit :
      weightedTotalMass w =
        weightedCorrectMass u y w (weightedFeatureFiberMajorityClassifier u y w) +
          weightedIncorrectMass u y w (weightedFeatureFiberMajorityClassifier u y w) :=
    weightedTotalMass_eq_weightedCorrectMass_add_weightedIncorrectMass
      u y w (weightedFeatureFiberMajorityClassifier u y w)
  have hlt :
      weightedIncorrectMass u y w (weightedFeatureFiberMajorityClassifier u y w) <
        weightedCorrectMass u y w (weightedFeatureFiberMajorityClassifier u y w) :=
    weightedIncorrectMass_lt_weightedCorrectMass_of_exists_weightedFeatureFiber_imbalance
      u y w himb
  omega

/-- On a finite visible surface, positive doubled advantage exists exactly when
some visible fiber is weight-imbalanced. -/
theorem exists_pos_doubledAdvantage_iff_exists_weightedFeatureFiber_imbalance
    (u : α → U) (y : α → Bool) (w : α → ℕ) :
    (∃ h : U → Bool, 0 < doubledAdvantage u y w h) ↔
      ∃ v : U,
        weightedFeatureFiberTrueMass u y w v ≠
          weightedFeatureFiberFalseMass u y w v := by
  constructor
  · rintro ⟨h, hadv⟩
    exact exists_weightedFeatureFiber_imbalance_of_pos_doubledAdvantage u y w h hadv
  · intro himb
    exact ⟨weightedFeatureFiberMajorityClassifier u y w,
      pos_doubledAdvantage_of_exists_weightedFeatureFiber_imbalance u y w himb⟩

/-- The strict-half weighted-success formulation has the same exact visible
fiber criterion. -/
theorem exists_total_lt_two_mul_weightedCorrectMass_iff_exists_weightedFeatureFiber_imbalance
    (u : α → U) (y : α → Bool) (w : α → ℕ) :
    (∃ h : U → Bool,
      weightedTotalMass w < 2 * weightedCorrectMass u y w h) ↔
      ∃ v : U,
        weightedFeatureFiberTrueMass u y w v ≠
          weightedFeatureFiberFalseMass u y w v := by
  constructor
  · rintro ⟨h, hadv⟩
    exact
      exists_weightedFeatureFiber_imbalance_of_total_lt_two_mul_weightedCorrectMass
        u y w h hadv
  · intro himb
    exact ⟨weightedFeatureFiberMajorityClassifier u y w,
      total_lt_two_mul_weightedCorrectMass_of_exists_weightedFeatureFiber_imbalance
        u y w himb⟩

end

end

end Mettapedia.Computability.PNP
