import Mettapedia.Computability.PNP.SharedABFeatureObstruction

/-!
# Regression checks for shared raw `(a,b)` feature obstructions

These wrappers pin the exact-surface pullback refuters for the shared raw
`(a,b)` affine-feature, sparse-threshold, and decision-list classes.
-/

namespace Mettapedia.Computability.PNP.SharedABFeatureObstructionRegression

open Mettapedia.Computability.PNP

theorem fullABRuleFamily_not_realizedBySharedABAffineFeatureFamily_k1_regression
    (features : Fin 1 → AffineColumnCode (1 + 1)) :
    ¬ RealizedBySharedABAffineFeatureFamily (r := 1) (k := 1) features
        (fullABRuleFamily 1) := by
  exact
    fullABRuleFamily_not_realizedBySharedABAffineFeatureFamily_of_lt_cardFormula
      (r := 1) (k := 1) features (by decide)

theorem fullABRuleFamily_not_realizedBySharedABSparseThresholdAffineFamily_k1_regression
    (features : Fin 1 → AffineColumnCode (1 + 1)) :
    ¬ RealizedBySharedABSparseThresholdAffineFamily (r := 1) (k := 1) features
        (fullABRuleFamily 1) := by
  exact
    fullABRuleFamily_not_realizedBySharedABSparseThresholdAffineFamily_of_lt_cardFormula
      (r := 1) (k := 1) features (by decide)

theorem fullABRuleFamily_not_realizedBySharedABAffineDecisionListFamily_k1_regression
    (features : Fin 2 → AffineColumnCode (1 + 1)) :
    ¬ RealizedBySharedABAffineDecisionListFamily (r := 2) (k := 1) features
        (fullABRuleFamily 1) := by
  exact
    fullABRuleFamily_not_realizedBySharedABAffineDecisionListFamily_of_lt_cardFormula
      (r := 2) (k := 1) features (by decide)

theorem fullExactABRuleFamily_not_realizedBySharedExactABAffineFeatureFamily_k1_regression
    (features : Fin 1 → AffineColumnCode (1 + 1)) :
    ¬ RealizedBySharedExactABAffineFeatureFamily (Z := Unit) (r := 1) (k := 1)
        features (fullExactABRuleFamily Unit 1) := by
  exact
    fullExactABRuleFamily_not_realizedBySharedExactABAffineFeatureFamily_of_lt_cardFormula
      (Z := Unit) (r := 1) (k := 1) features (by decide)

theorem fullExactABRuleFamily_not_realizedBySharedExactABSparseThresholdAffineFamily_k1_regression
    (features : Fin 1 → AffineColumnCode (1 + 1)) :
    ¬ RealizedBySharedExactABSparseThresholdAffineFamily (Z := Unit) (r := 1) (k := 1)
        features (fullExactABRuleFamily Unit 1) := by
  exact
    fullExactABRuleFamily_not_realizedBySharedExactABSparseThresholdAffineFamily_of_lt_cardFormula
      (Z := Unit) (r := 1) (k := 1) features (by decide)

theorem fullExactABRuleFamily_not_realizedBySharedExactABAffineDecisionListFamily_k1_regression
    (features : Fin 2 → AffineColumnCode (1 + 1)) :
    ¬ RealizedBySharedExactABAffineDecisionListFamily (Z := Unit) (r := 2) (k := 1)
        features (fullExactABRuleFamily Unit 1) := by
  exact
    fullExactABRuleFamily_not_realizedBySharedExactABAffineDecisionListFamily_of_lt_cardFormula
      (Z := Unit) (r := 2) (k := 1) features (by decide)

theorem shared_ab_affine_feature_not_realized_of_injective_probe_regression
    {Probe : Type*} [Fintype Probe] {r k : ℕ} {Index : Type*}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hprobe : ∀ p, ∃ i, H.predict i = target p)
    (hcard : 2 ^ (2 ^ r) < Fintype.card Probe) :
    ¬ RealizedBySharedABAffineFeatureFamily (r := r) (k := k) features H := by
  exact
    not_realizedBySharedABAffineFeatureFamily_of_injective_probe_of_lt_budgetImageCard
      target hinj hprobe hcard

theorem shared_ab_sparse_threshold_not_realized_of_injective_probe_regression
    {Probe : Type*} [Fintype Probe] {r k : ℕ} {Index : Type*}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hprobe : ∀ p, ∃ i, H.predict i = target p)
    (hcard : 2 ^ (2 * r) < Fintype.card Probe) :
    ¬ RealizedBySharedABSparseThresholdAffineFamily (r := r) (k := k) features H := by
  exact
    not_realizedBySharedABSparseThresholdAffineFamily_of_injective_probe_of_lt_budgetImageCard
      target hinj hprobe hcard

theorem shared_ab_decision_list_not_realized_of_injective_probe_regression
    {Probe : Type*} [Fintype Probe] {r k : ℕ} {Index : Type*}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hprobe : ∀ p, ∃ i, H.predict i = target p)
    (hcard : 2 ^ (r + 1) < Fintype.card Probe) :
    ¬ RealizedBySharedABAffineDecisionListFamily (r := r) (k := k) features H := by
  exact
    not_realizedBySharedABAffineDecisionListFamily_of_injective_probe_of_lt_budgetImageCard
      target hinj hprobe hcard

theorem shared_exact_ab_affine_feature_not_realized_of_factorsThrough_injective_probe_regression
    {Z Probe : Type*} [Inhabited Z] [Fintype Probe] {r k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hprobe : ∀ p, ∃ i, H.predict i = target p)
    (hcard : 2 ^ (2 ^ r) < Fintype.card Probe)
    (hfactor : G.FactorsThrough abVisibleData H) :
    ¬ RealizedBySharedExactABAffineFeatureFamily
        (Z := Z) (r := r) (k := k) features G := by
  exact
    not_realizedBySharedExactABAffineFeatureFamily_of_factorsThrough_ab_and_injective_probe_of_lt_budgetImageCard
      target hinj hprobe hcard hfactor

theorem shared_exact_ab_sparse_threshold_not_realized_of_factorsThrough_injective_probe_regression
    {Z Probe : Type*} [Inhabited Z] [Fintype Probe] {r k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hprobe : ∀ p, ∃ i, H.predict i = target p)
    (hcard : 2 ^ (2 * r) < Fintype.card Probe)
    (hfactor : G.FactorsThrough abVisibleData H) :
    ¬ RealizedBySharedExactABSparseThresholdAffineFamily
        (Z := Z) (r := r) (k := k) features G := by
  exact
    not_realizedBySharedExactABSparseThresholdAffineFamily_of_factorsThrough_ab_and_injective_probe_of_lt_budgetImageCard
      target hinj hprobe hcard hfactor

theorem shared_exact_ab_decision_list_not_realized_of_factorsThrough_injective_probe_regression
    {Z Probe : Type*} [Inhabited Z] [Fintype Probe] {r k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hprobe : ∀ p, ∃ i, H.predict i = target p)
    (hcard : 2 ^ (r + 1) < Fintype.card Probe)
    (hfactor : G.FactorsThrough abVisibleData H) :
    ¬ RealizedBySharedExactABAffineDecisionListFamily
        (Z := Z) (r := r) (k := k) features G := by
  exact
    not_realizedBySharedExactABAffineDecisionListFamily_of_factorsThrough_ab_and_injective_probe_of_lt_budgetImageCard
      target hinj hprobe hcard hfactor

end Mettapedia.Computability.PNP.SharedABFeatureObstructionRegression
