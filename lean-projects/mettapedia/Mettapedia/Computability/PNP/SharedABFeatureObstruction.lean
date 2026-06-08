import Mettapedia.Computability.PNP.ABDecisionListObstruction
import Mettapedia.Computability.PNP.SharedABFeatureRoutes

/-!
# PNP crux: shared raw `(a,b)` feature routes need a strict subclass theorem

`SharedABFeatureRoutes.lean` gives positive route interfaces for shared raw
`(a,b)` affine-feature families.  This file records the matching obstruction at
the exact-surface pullback layer.

If an exact switched family factors through `(a,b)` and the reduced family is
still fully expressive on `ABVisibleSurface k`, then any shared-basis
realization of the exact family forces the reduced truth-table lower bound.  So
the shared-basis route must prove that the actual reduced switched family is a
strict subclass of all Boolean rules on `(a,b)`.
-/

namespace Mettapedia.Computability.PNP

section ReducedFullRules

variable {r k : ℕ}

/-- The full raw `(a,b)` rule family cannot be realized by a shared affine
feature family below the reduced truth-table threshold. -/
theorem fullABRuleFamily_not_realizedBySharedABAffineFeatureFamily_of_lt_surfaceCard
    (features : Fin r → AffineColumnCode (k + k))
    (hs : 2 ^ r < Fintype.card (ABVisibleSurface k)) :
    ¬ RealizedBySharedABAffineFeatureFamily (r := r) (k := k) features
        (fullABRuleFamily k) := by
  exact
    not_realizedBySharedABAffineFeatureFamily_of_surjective_predict_of_lt_surfaceCard
      (r := r) (k := k) hs (fullABRuleFamily_surjective k)

/-- Formula form of the full-rule obstruction for shared affine features. -/
theorem fullABRuleFamily_not_realizedBySharedABAffineFeatureFamily_of_lt_cardFormula
    (features : Fin r → AffineColumnCode (k + k))
    (hs : 2 ^ r < 2 ^ (2 * k)) :
    ¬ RealizedBySharedABAffineFeatureFamily (r := r) (k := k) features
        (fullABRuleFamily k) := by
  exact
    fullABRuleFamily_not_realizedBySharedABAffineFeatureFamily_of_lt_surfaceCard
      (r := r) (k := k) features
      (by simpa [card_abVisibleSurface (k := k)] using hs)

/-- The full raw `(a,b)` rule family cannot be realized by a shared sparse
threshold family below the reduced truth-table threshold. -/
theorem fullABRuleFamily_not_realizedBySharedABSparseThresholdAffineFamily_of_lt_surfaceCard
    (features : Fin r → AffineColumnCode (k + k))
    (hs : 2 * r < Fintype.card (ABVisibleSurface k)) :
    ¬ RealizedBySharedABSparseThresholdAffineFamily (r := r) (k := k) features
        (fullABRuleFamily k) := by
  exact
    not_realizedBySharedABSparseThresholdAffineFamily_of_surjective_predict_of_lt_surfaceCard
      (r := r) (k := k) hs (fullABRuleFamily_surjective k)

/-- Formula form of the full-rule obstruction for shared sparse-threshold
features. -/
theorem fullABRuleFamily_not_realizedBySharedABSparseThresholdAffineFamily_of_lt_cardFormula
    (features : Fin r → AffineColumnCode (k + k))
    (hs : 2 * r < 2 ^ (2 * k)) :
    ¬ RealizedBySharedABSparseThresholdAffineFamily (r := r) (k := k) features
        (fullABRuleFamily k) := by
  exact
    fullABRuleFamily_not_realizedBySharedABSparseThresholdAffineFamily_of_lt_surfaceCard
      (r := r) (k := k) features
      (by simpa [card_abVisibleSurface (k := k)] using hs)

/-- The full raw `(a,b)` rule family cannot be realized by a shared decision-list
family below the reduced truth-table threshold. -/
theorem fullABRuleFamily_not_realizedBySharedABAffineDecisionListFamily_of_lt_surfaceCard
    (features : Fin r → AffineColumnCode (k + k))
    (hs : r + 1 < Fintype.card (ABVisibleSurface k)) :
    ¬ RealizedBySharedABAffineDecisionListFamily (r := r) (k := k) features
        (fullABRuleFamily k) := by
  exact
    not_realizedBySharedABAffineDecisionListFamily_of_surjective_predict_of_lt_surfaceCard
      (r := r) (k := k) hs (fullABRuleFamily_surjective k)

/-- Formula form of the full-rule obstruction for shared decision-list
features. -/
theorem fullABRuleFamily_not_realizedBySharedABAffineDecisionListFamily_of_lt_cardFormula
    (features : Fin r → AffineColumnCode (k + k))
    (hs : r + 1 < 2 ^ (2 * k)) :
    ¬ RealizedBySharedABAffineDecisionListFamily (r := r) (k := k) features
        (fullABRuleFamily k) := by
  exact
    fullABRuleFamily_not_realizedBySharedABAffineDecisionListFamily_of_lt_surfaceCard
      (r := r) (k := k) features
      (by simpa [card_abVisibleSurface (k := k)] using hs)

end ReducedFullRules

section ReducedFiniteProbe

variable {Probe : Type*} [Fintype Probe] {r k : ℕ} {Index : Type*}

/-- Partial-image form for shared affine features on the raw `(a,b)` surface:
realizing an injectively indexed probe family forces the probe count to fit
inside the finite predictor image of the shared truth-table combiner. -/
theorem probeCard_le_of_realizedBySharedABAffineFeatureFamily_of_injective_probe
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hprobe : ∀ p, ∃ i, H.predict i = target p)
    (hreal : RealizedBySharedABAffineFeatureFamily (r := r) (k := k) features H) :
    Fintype.card Probe ≤ 2 ^ (2 ^ r) :=
  IndexedPredictorFamily.finitePredictorCover_card_le_of_injective_realization
    (G := H) target hinj hprobe
    (IndexedPredictorFamily.finitePredictorCover_of_hasBitBudget
      (G := H) (s := 2 ^ r)
      (abVisibleHasBitBudget_of_realizedBySharedABAffineFeatureFamily
        (r := r) (k := k) hreal))

/-- Shared affine features cannot realize an injective probe family larger than
their finite predictor image. -/
theorem not_realizedBySharedABAffineFeatureFamily_of_injective_probe_of_lt_budgetImageCard
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hprobe : ∀ p, ∃ i, H.predict i = target p)
    (hcard : 2 ^ (2 ^ r) < Fintype.card Probe) :
    ¬ RealizedBySharedABAffineFeatureFamily (r := r) (k := k) features H := by
  intro hreal
  exact Nat.not_le_of_lt hcard <|
    probeCard_le_of_realizedBySharedABAffineFeatureFamily_of_injective_probe
      (r := r) (k := k) target hinj hprobe hreal

/-- Partial-image form for shared sparse-threshold features on the raw
`(a,b)` surface. -/
theorem probeCard_le_of_realizedBySharedABSparseThresholdAffineFamily_of_injective_probe
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hprobe : ∀ p, ∃ i, H.predict i = target p)
    (hreal :
      RealizedBySharedABSparseThresholdAffineFamily (r := r) (k := k) features H) :
    Fintype.card Probe ≤ 2 ^ (2 * r) :=
  IndexedPredictorFamily.finitePredictorCover_card_le_of_injective_realization
    (G := H) target hinj hprobe
    (IndexedPredictorFamily.finitePredictorCover_of_hasBitBudget
      (G := H) (s := 2 * r)
      (abVisibleHasBitBudget_of_realizedBySharedABSparseThresholdAffineFamily
        (r := r) (k := k) hreal))

/-- Shared sparse-threshold features cannot realize an injective probe family
larger than their finite predictor image. -/
theorem not_realizedBySharedABSparseThresholdAffineFamily_of_injective_probe_of_lt_budgetImageCard
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hprobe : ∀ p, ∃ i, H.predict i = target p)
    (hcard : 2 ^ (2 * r) < Fintype.card Probe) :
    ¬ RealizedBySharedABSparseThresholdAffineFamily (r := r) (k := k) features H := by
  intro hreal
  exact Nat.not_le_of_lt hcard <|
    probeCard_le_of_realizedBySharedABSparseThresholdAffineFamily_of_injective_probe
      (r := r) (k := k) target hinj hprobe hreal

/-- Partial-image form for shared decision-list features on the raw `(a,b)`
surface. -/
theorem probeCard_le_of_realizedBySharedABAffineDecisionListFamily_of_injective_probe
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hprobe : ∀ p, ∃ i, H.predict i = target p)
    (hreal :
      RealizedBySharedABAffineDecisionListFamily (r := r) (k := k) features H) :
    Fintype.card Probe ≤ 2 ^ (r + 1) :=
  IndexedPredictorFamily.finitePredictorCover_card_le_of_injective_realization
    (G := H) target hinj hprobe
    (IndexedPredictorFamily.finitePredictorCover_of_hasBitBudget
      (G := H) (s := r + 1)
      (abVisibleHasBitBudget_of_realizedBySharedABAffineDecisionListFamily
        (r := r) (k := k) hreal))

/-- Shared decision-list features cannot realize an injective probe family
larger than their finite predictor image. -/
theorem not_realizedBySharedABAffineDecisionListFamily_of_injective_probe_of_lt_budgetImageCard
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hprobe : ∀ p, ∃ i, H.predict i = target p)
    (hcard : 2 ^ (r + 1) < Fintype.card Probe) :
    ¬ RealizedBySharedABAffineDecisionListFamily (r := r) (k := k) features H := by
  intro hreal
  exact Nat.not_le_of_lt hcard <|
    probeCard_le_of_realizedBySharedABAffineDecisionListFamily_of_injective_probe
      (r := r) (k := k) target hinj hprobe hreal

end ReducedFiniteProbe

section ExactPullback

variable {Z : Type*} {r k : ℕ} {Index : Type*}

/-- If an exact family factors through a fully expressive raw `(a,b)` family,
then a shared affine-feature exact realization forces the reduced truth-table
lower bound. -/
theorem abVisible_surfaceCard_le_of_realizedBySharedExactABAffineFeatureFamily_of_factorsThrough_ab
    [Inhabited Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hfactor : G.FactorsThrough abVisibleData H)
    (hsurj : Function.Surjective H.predict)
    (hreal : RealizedBySharedExactABAffineFeatureFamily
      (Z := Z) (r := r) (k := k) features G) :
    Fintype.card (ABVisibleSurface k) ≤ 2 ^ r := by
  exact
    abVisible_surfaceCard_le_of_exactVisibleCompressionTarget_of_factorsThrough
      (Z := Z) (k := k) (s := 2 ^ r) hfactor hsurj
      (exactVisibleCompressionTarget_of_realizedBySharedExactABAffineFeatureFamily
        (Z := Z) (r := r) (k := k) (Index := Index) features hreal)

/-- Shared affine-feature exact realization is impossible below the reduced
truth-table threshold when the reduced family is fully expressive. -/
theorem not_realizedBySharedExactABAffineFeatureFamily_of_factorsThrough_ab_and_surjective_predict_of_lt_surfaceCard
    [Inhabited Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hs : 2 ^ r < Fintype.card (ABVisibleSurface k))
    (hfactor : G.FactorsThrough abVisibleData H)
    (hsurj : Function.Surjective H.predict) :
    ¬ RealizedBySharedExactABAffineFeatureFamily
        (Z := Z) (r := r) (k := k) features G := by
  intro hreal
  exact Nat.not_le_of_lt hs <|
    abVisible_surfaceCard_le_of_realizedBySharedExactABAffineFeatureFamily_of_factorsThrough_ab
      (Z := Z) (r := r) (k := k) hfactor hsurj hreal

/-- Formula form of the exact-pullback obstruction for shared affine features. -/
theorem not_realizedBySharedExactABAffineFeatureFamily_of_factorsThrough_ab_and_surjective_predict_of_lt_cardFormula
    [Inhabited Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hs : 2 ^ r < 2 ^ (2 * k))
    (hfactor : G.FactorsThrough abVisibleData H)
    (hsurj : Function.Surjective H.predict) :
    ¬ RealizedBySharedExactABAffineFeatureFamily
        (Z := Z) (r := r) (k := k) features G := by
  exact
    not_realizedBySharedExactABAffineFeatureFamily_of_factorsThrough_ab_and_surjective_predict_of_lt_surfaceCard
      (Z := Z) (r := r) (k := k)
      (by simpa [card_abVisibleSurface (k := k)] using hs)
      hfactor hsurj

/-- If an exact family factors through a fully expressive raw `(a,b)` family,
then a shared sparse-threshold exact realization forces the reduced truth-table
lower bound. -/
theorem abVisible_surfaceCard_le_of_realizedBySharedExactABSparseThresholdAffineFamily_of_factorsThrough_ab
    [Inhabited Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hfactor : G.FactorsThrough abVisibleData H)
    (hsurj : Function.Surjective H.predict)
    (hreal : RealizedBySharedExactABSparseThresholdAffineFamily
      (Z := Z) (r := r) (k := k) features G) :
    Fintype.card (ABVisibleSurface k) ≤ 2 * r := by
  exact
    abVisible_surfaceCard_le_of_exactVisibleCompressionTarget_of_factorsThrough
      (Z := Z) (k := k) (s := 2 * r) hfactor hsurj
      (exactVisibleCompressionTarget_of_realizedBySharedExactABSparseThresholdAffineFamily
        (Z := Z) (r := r) (k := k) (Index := Index) features hreal)

/-- Shared sparse-threshold exact realization is impossible below the reduced
truth-table threshold when the reduced family is fully expressive. -/
theorem not_realizedBySharedExactABSparseThresholdAffineFamily_of_factorsThrough_ab_and_surjective_predict_of_lt_surfaceCard
    [Inhabited Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hs : 2 * r < Fintype.card (ABVisibleSurface k))
    (hfactor : G.FactorsThrough abVisibleData H)
    (hsurj : Function.Surjective H.predict) :
    ¬ RealizedBySharedExactABSparseThresholdAffineFamily
        (Z := Z) (r := r) (k := k) features G := by
  intro hreal
  exact Nat.not_le_of_lt hs <|
    abVisible_surfaceCard_le_of_realizedBySharedExactABSparseThresholdAffineFamily_of_factorsThrough_ab
      (Z := Z) (r := r) (k := k) hfactor hsurj hreal

/-- Formula form of the exact-pullback obstruction for shared sparse-threshold
features. -/
theorem not_realizedBySharedExactABSparseThresholdAffineFamily_of_factorsThrough_ab_and_surjective_predict_of_lt_cardFormula
    [Inhabited Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hs : 2 * r < 2 ^ (2 * k))
    (hfactor : G.FactorsThrough abVisibleData H)
    (hsurj : Function.Surjective H.predict) :
    ¬ RealizedBySharedExactABSparseThresholdAffineFamily
        (Z := Z) (r := r) (k := k) features G := by
  exact
    not_realizedBySharedExactABSparseThresholdAffineFamily_of_factorsThrough_ab_and_surjective_predict_of_lt_surfaceCard
      (Z := Z) (r := r) (k := k)
      (by simpa [card_abVisibleSurface (k := k)] using hs)
      hfactor hsurj

/-- If an exact family factors through a fully expressive raw `(a,b)` family,
then a shared decision-list exact realization forces the reduced truth-table
lower bound. -/
theorem abVisible_surfaceCard_le_of_realizedBySharedExactABAffineDecisionListFamily_of_factorsThrough_ab
    [Inhabited Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hfactor : G.FactorsThrough abVisibleData H)
    (hsurj : Function.Surjective H.predict)
    (hreal : RealizedBySharedExactABAffineDecisionListFamily
      (Z := Z) (r := r) (k := k) features G) :
    Fintype.card (ABVisibleSurface k) ≤ r + 1 := by
  exact
    abVisible_surfaceCard_le_of_exactVisibleCompressionTarget_of_factorsThrough
      (Z := Z) (k := k) (s := r + 1) hfactor hsurj
      (exactVisibleCompressionTarget_of_realizedBySharedExactABAffineDecisionListFamily
        (Z := Z) (r := r) (k := k) (Index := Index) features hreal)

/-- Shared decision-list exact realization is impossible below the reduced
truth-table threshold when the reduced family is fully expressive. -/
theorem not_realizedBySharedExactABAffineDecisionListFamily_of_factorsThrough_ab_and_surjective_predict_of_lt_surfaceCard
    [Inhabited Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hs : r + 1 < Fintype.card (ABVisibleSurface k))
    (hfactor : G.FactorsThrough abVisibleData H)
    (hsurj : Function.Surjective H.predict) :
    ¬ RealizedBySharedExactABAffineDecisionListFamily
        (Z := Z) (r := r) (k := k) features G := by
  intro hreal
  exact Nat.not_le_of_lt hs <|
    abVisible_surfaceCard_le_of_realizedBySharedExactABAffineDecisionListFamily_of_factorsThrough_ab
      (Z := Z) (r := r) (k := k) hfactor hsurj hreal

/-- Formula form of the exact-pullback obstruction for shared decision-list
features. -/
theorem not_realizedBySharedExactABAffineDecisionListFamily_of_factorsThrough_ab_and_surjective_predict_of_lt_cardFormula
    [Inhabited Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hs : r + 1 < 2 ^ (2 * k))
    (hfactor : G.FactorsThrough abVisibleData H)
    (hsurj : Function.Surjective H.predict) :
    ¬ RealizedBySharedExactABAffineDecisionListFamily
        (Z := Z) (r := r) (k := k) features G := by
  exact
    not_realizedBySharedExactABAffineDecisionListFamily_of_factorsThrough_ab_and_surjective_predict_of_lt_surfaceCard
      (Z := Z) (r := r) (k := k)
      (by simpa [card_abVisibleSurface (k := k)] using hs)
      hfactor hsurj

/-- Exact-pullback partial-image form for shared affine features: any
injectively indexed finite probe family already realized on the reduced
`(a,b)` view must fit inside the shared truth-table predictor image. -/
theorem probeCard_le_of_realizedBySharedExactABAffineFeatureFamily_of_factorsThrough_ab_and_injective_probe
    [Inhabited Z] {Probe : Type*} [Fintype Probe]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hprobe : ∀ p, ∃ i, H.predict i = target p)
    (hfactor : G.FactorsThrough abVisibleData H)
    (hreal : RealizedBySharedExactABAffineFeatureFamily
      (Z := Z) (r := r) (k := k) features G) :
    Fintype.card Probe ≤ 2 ^ (2 ^ r) := by
  have htarget :
      ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (2 ^ r) :=
    exactVisibleCompressionTarget_of_realizedBySharedExactABAffineFeatureFamily
      (Z := Z) (r := r) (k := k) (Index := Index) features hreal
  have hcover : G.FinitePredictorCover (2 ^ (2 ^ r)) :=
    (exactVisibleCompressionTarget_iff_finitePredictorCover
      (Z := Z) (k := k) (s := 2 ^ r) (Index := Index) (G := G)).mp htarget
  exact
    abVisible_finitePredictorCover_card_le_of_factorsThrough_of_injective_realization
      (Z := Z) (k := k) (Index := Index)
      target hinj hprobe hfactor hcover

/-- Shared exact affine-feature realization is impossible when a larger
injective probe family is already realized on the reduced `(a,b)` view. -/
theorem not_realizedBySharedExactABAffineFeatureFamily_of_factorsThrough_ab_and_injective_probe_of_lt_budgetImageCard
    [Inhabited Z] {Probe : Type*} [Fintype Probe]
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
  intro hreal
  exact Nat.not_le_of_lt hcard <|
    probeCard_le_of_realizedBySharedExactABAffineFeatureFamily_of_factorsThrough_ab_and_injective_probe
      (Z := Z) (r := r) (k := k) target hinj hprobe hfactor hreal

/-- Exact-pullback partial-image form for shared sparse-threshold features. -/
theorem probeCard_le_of_realizedBySharedExactABSparseThresholdAffineFamily_of_factorsThrough_ab_and_injective_probe
    [Inhabited Z] {Probe : Type*} [Fintype Probe]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hprobe : ∀ p, ∃ i, H.predict i = target p)
    (hfactor : G.FactorsThrough abVisibleData H)
    (hreal : RealizedBySharedExactABSparseThresholdAffineFamily
      (Z := Z) (r := r) (k := k) features G) :
    Fintype.card Probe ≤ 2 ^ (2 * r) := by
  have htarget :
      ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (2 * r) :=
    exactVisibleCompressionTarget_of_realizedBySharedExactABSparseThresholdAffineFamily
      (Z := Z) (r := r) (k := k) (Index := Index) features hreal
  have hcover : G.FinitePredictorCover (2 ^ (2 * r)) :=
    (exactVisibleCompressionTarget_iff_finitePredictorCover
      (Z := Z) (k := k) (s := 2 * r) (Index := Index) (G := G)).mp htarget
  exact
    abVisible_finitePredictorCover_card_le_of_factorsThrough_of_injective_realization
      (Z := Z) (k := k) (Index := Index)
      target hinj hprobe hfactor hcover

/-- Shared exact sparse-threshold realization is impossible when a larger
injective probe family is already realized on the reduced `(a,b)` view. -/
theorem not_realizedBySharedExactABSparseThresholdAffineFamily_of_factorsThrough_ab_and_injective_probe_of_lt_budgetImageCard
    [Inhabited Z] {Probe : Type*} [Fintype Probe]
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
  intro hreal
  exact Nat.not_le_of_lt hcard <|
    probeCard_le_of_realizedBySharedExactABSparseThresholdAffineFamily_of_factorsThrough_ab_and_injective_probe
      (Z := Z) (r := r) (k := k) target hinj hprobe hfactor hreal

/-- Exact-pullback partial-image form for shared decision-list features. -/
theorem probeCard_le_of_realizedBySharedExactABAffineDecisionListFamily_of_factorsThrough_ab_and_injective_probe
    [Inhabited Z] {Probe : Type*} [Fintype Probe]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hprobe : ∀ p, ∃ i, H.predict i = target p)
    (hfactor : G.FactorsThrough abVisibleData H)
    (hreal : RealizedBySharedExactABAffineDecisionListFamily
      (Z := Z) (r := r) (k := k) features G) :
    Fintype.card Probe ≤ 2 ^ (r + 1) := by
  have htarget :
      ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (r + 1) :=
    exactVisibleCompressionTarget_of_realizedBySharedExactABAffineDecisionListFamily
      (Z := Z) (r := r) (k := k) (Index := Index) features hreal
  have hcover : G.FinitePredictorCover (2 ^ (r + 1)) :=
    (exactVisibleCompressionTarget_iff_finitePredictorCover
      (Z := Z) (k := k) (s := r + 1) (Index := Index) (G := G)).mp htarget
  exact
    abVisible_finitePredictorCover_card_le_of_factorsThrough_of_injective_realization
      (Z := Z) (k := k) (Index := Index)
      target hinj hprobe hfactor hcover

/-- Shared exact decision-list realization is impossible when a larger
injective probe family is already realized on the reduced `(a,b)` view. -/
theorem not_realizedBySharedExactABAffineDecisionListFamily_of_factorsThrough_ab_and_injective_probe_of_lt_budgetImageCard
    [Inhabited Z] {Probe : Type*} [Fintype Probe]
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
  intro hreal
  exact Nat.not_le_of_lt hcard <|
    probeCard_le_of_realizedBySharedExactABAffineDecisionListFamily_of_factorsThrough_ab_and_injective_probe
      (Z := Z) (r := r) (k := k) target hinj hprobe hfactor hreal

end ExactPullback

section FullExactPullback

variable {Z : Type*} {r k : ℕ}

/-- The exact pullback of the full raw `(a,b)` rule family cannot be realized by
shared affine features below the reduced truth-table threshold. -/
theorem fullExactABRuleFamily_not_realizedBySharedExactABAffineFeatureFamily_of_lt_surfaceCard
    [Inhabited Z]
    (features : Fin r → AffineColumnCode (k + k))
    (hs : 2 ^ r < Fintype.card (ABVisibleSurface k)) :
    ¬ RealizedBySharedExactABAffineFeatureFamily
        (Z := Z) (r := r) (k := k) features (fullExactABRuleFamily Z k) := by
  exact
    not_realizedBySharedExactABAffineFeatureFamily_of_factorsThrough_ab_and_surjective_predict_of_lt_surfaceCard
      (Z := Z) (r := r) (k := k) hs
      (fullExactABRuleFamily_factorsThrough_ab Z k)
      (fullABRuleFamily_surjective k)

/-- Formula form for the exact full raw-rule pullback and shared affine
features. -/
theorem fullExactABRuleFamily_not_realizedBySharedExactABAffineFeatureFamily_of_lt_cardFormula
    [Inhabited Z]
    (features : Fin r → AffineColumnCode (k + k))
    (hs : 2 ^ r < 2 ^ (2 * k)) :
    ¬ RealizedBySharedExactABAffineFeatureFamily
        (Z := Z) (r := r) (k := k) features (fullExactABRuleFamily Z k) := by
  exact
    fullExactABRuleFamily_not_realizedBySharedExactABAffineFeatureFamily_of_lt_surfaceCard
      (Z := Z) (r := r) (k := k) features
      (by simpa [card_abVisibleSurface (k := k)] using hs)

/-- The exact pullback of the full raw `(a,b)` rule family cannot be realized by
shared sparse-threshold features below the reduced truth-table threshold. -/
theorem fullExactABRuleFamily_not_realizedBySharedExactABSparseThresholdAffineFamily_of_lt_surfaceCard
    [Inhabited Z]
    (features : Fin r → AffineColumnCode (k + k))
    (hs : 2 * r < Fintype.card (ABVisibleSurface k)) :
    ¬ RealizedBySharedExactABSparseThresholdAffineFamily
        (Z := Z) (r := r) (k := k) features (fullExactABRuleFamily Z k) := by
  exact
    not_realizedBySharedExactABSparseThresholdAffineFamily_of_factorsThrough_ab_and_surjective_predict_of_lt_surfaceCard
      (Z := Z) (r := r) (k := k) hs
      (fullExactABRuleFamily_factorsThrough_ab Z k)
      (fullABRuleFamily_surjective k)

/-- Formula form for the exact full raw-rule pullback and shared
sparse-threshold features. -/
theorem fullExactABRuleFamily_not_realizedBySharedExactABSparseThresholdAffineFamily_of_lt_cardFormula
    [Inhabited Z]
    (features : Fin r → AffineColumnCode (k + k))
    (hs : 2 * r < 2 ^ (2 * k)) :
    ¬ RealizedBySharedExactABSparseThresholdAffineFamily
        (Z := Z) (r := r) (k := k) features (fullExactABRuleFamily Z k) := by
  exact
    fullExactABRuleFamily_not_realizedBySharedExactABSparseThresholdAffineFamily_of_lt_surfaceCard
      (Z := Z) (r := r) (k := k) features
      (by simpa [card_abVisibleSurface (k := k)] using hs)

/-- The exact pullback of the full raw `(a,b)` rule family cannot be realized by
shared decision-list features below the reduced truth-table threshold. -/
theorem fullExactABRuleFamily_not_realizedBySharedExactABAffineDecisionListFamily_of_lt_surfaceCard
    [Inhabited Z]
    (features : Fin r → AffineColumnCode (k + k))
    (hs : r + 1 < Fintype.card (ABVisibleSurface k)) :
    ¬ RealizedBySharedExactABAffineDecisionListFamily
        (Z := Z) (r := r) (k := k) features (fullExactABRuleFamily Z k) := by
  exact
    not_realizedBySharedExactABAffineDecisionListFamily_of_factorsThrough_ab_and_surjective_predict_of_lt_surfaceCard
      (Z := Z) (r := r) (k := k) hs
      (fullExactABRuleFamily_factorsThrough_ab Z k)
      (fullABRuleFamily_surjective k)

/-- Formula form for the exact full raw-rule pullback and shared decision-list
features. -/
theorem fullExactABRuleFamily_not_realizedBySharedExactABAffineDecisionListFamily_of_lt_cardFormula
    [Inhabited Z]
    (features : Fin r → AffineColumnCode (k + k))
    (hs : r + 1 < 2 ^ (2 * k)) :
    ¬ RealizedBySharedExactABAffineDecisionListFamily
        (Z := Z) (r := r) (k := k) features (fullExactABRuleFamily Z k) := by
  exact
    fullExactABRuleFamily_not_realizedBySharedExactABAffineDecisionListFamily_of_lt_surfaceCard
      (Z := Z) (r := r) (k := k) features
      (by simpa [card_abVisibleSurface (k := k)] using hs)

end FullExactPullback

end Mettapedia.Computability.PNP
