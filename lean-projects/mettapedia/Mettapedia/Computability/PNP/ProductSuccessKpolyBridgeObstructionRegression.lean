import Mettapedia.Computability.PNP.ProductSuccessKpolyBridgeObstruction

/-!
# Regression tests for product-success/Kpoly bridge obstructions
-/

namespace Mettapedia.Computability.PNP.ProductSuccessKpolyBridgeObstructionRegression

open Mettapedia.Computability.PNP

universe u v

theorem full_exact_visible_rule_family_surjective_regression
    (Z : Type*) (k : ℕ) :
    Function.Surjective (fullExactVisibleRuleFamily Z k).predict := by
  exact fullExactVisibleRuleFamily_surjective Z k

theorem product_bound_semantic_bridge_iff_exact_visible_compression_bridge_regression
    {Ω : Type u} [Fintype Ω] {Z : Type v} {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} {G : ExactVisibleSwitchedFamily Z k Index} :
    ProductBoundSemanticFiniteImageBridge Ω Z k s hist items G ↔
      (V13FieldedProductBoundFrom Ω hist items →
        ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s) := by
  exact productBoundSemanticFiniteImageBridge_iff_exactVisibleCompressionBridge

theorem product_bound_true_bridge_iff_finite_predictor_cover_regression
    {Ω : Type u} [Fintype Ω] {Z : Type v} {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} {G : ExactVisibleSwitchedFamily Z k Index}
    (hprod : V13FieldedProductBoundFrom Ω hist items) :
    (V13FieldedProductBoundFrom Ω hist items →
        ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s) ↔
      G.FinitePredictorCover (2 ^ s) := by
  exact productBound_true_exactVisibleCompressionBridge_iff_finitePredictorCover
    hprod

theorem product_bound_only_bridge_iff_forall_semantic_finite_image_bridge_regression
    {Ω : Type u} [Fintype Ω] {Z : Type v} {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)} :
    ProductBoundOnlyExactVisibleCompressionBridge Ω Z k s hist items ↔
      ∀ {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index),
        ProductBoundSemanticFiniteImageBridge Ω Z k s hist items G := by
  exact
    productBoundOnlyExactVisibleCompressionBridge_iff_forall_semanticFiniteImageBridge

theorem fielded_switching_semantic_bridge_iff_exact_visible_compression_bridge_regression
    {Ω : Type u} [Fintype Ω] {Z : Type v} {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} {G : ExactVisibleSwitchedFamily Z k Index} :
    FieldedSwitchingSemanticFiniteImageBridge Ω Z k s hist items G ↔
      (V13FieldSwitchingInstantiatedFrom hist items →
        ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s) := by
  exact fieldedSwitchingSemanticFiniteImageBridge_iff_exactVisibleCompressionBridge

theorem fielded_switching_true_bridge_iff_finite_predictor_cover_regression
    {Ω : Type u} [Fintype Ω] {Z : Type v} {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} {G : ExactVisibleSwitchedFamily Z k Index}
    (hfield : V13FieldSwitchingInstantiatedFrom hist items) :
    (V13FieldSwitchingInstantiatedFrom hist items →
        ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s) ↔
      G.FinitePredictorCover (2 ^ s) := by
  exact fieldedSwitching_true_exactVisibleCompressionBridge_iff_finitePredictorCover
    hfield

theorem fielded_switching_only_bridge_iff_forall_semantic_finite_image_bridge_regression
    {Ω : Type u} [Fintype Ω] {Z : Type v} {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)} :
    FieldedSwitchingOnlyExactVisibleCompressionBridge Ω Z k s hist items ↔
      ∀ {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index),
        FieldedSwitchingSemanticFiniteImageBridge Ω Z k s hist items G := by
  exact
    fieldedSwitchingOnlyExactVisibleCompressionBridge_iff_forall_semanticFiniteImageBridge

theorem product_bound_only_clocked_payload_bridge_iff_forall_semantic_finite_image_bridge_regression
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s clock : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)} :
    ProductBoundOnlyClockedKpolyFiniteLearningBridge Ω Z k s clock hist items ↔
      ∀ {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index),
        ProductBoundSemanticFiniteImageBridge Ω Z k s hist items G := by
  exact
    productBoundOnlyClockedKpolyFiniteLearningBridge_iff_forall_semanticFiniteImageBridge

theorem fielded_switching_only_clocked_payload_bridge_iff_forall_semantic_finite_image_bridge_regression
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s clock : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)} :
    FieldedSwitchingOnlyClockedKpolyFiniteLearningBridge Ω Z k s clock hist items ↔
      ∀ {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index),
        FieldedSwitchingSemanticFiniteImageBridge Ω Z k s hist items G := by
  exact
    fieldedSwitchingOnlyClockedKpolyFiniteLearningBridge_iff_forall_semanticFiniteImageBridge

theorem product_bound_clocked_payload_bridge_implies_exact_visible_compression_regression
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s clock : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hbridge :
      ProductBoundOnlyClockedKpolyFiniteLearningBridge Ω Z k s clock hist items) :
    ProductBoundOnlyExactVisibleCompressionBridge Ω Z k s hist items := by
  exact
    productBoundOnlyExactVisibleCompressionBridge_of_clockedKpolyFiniteLearningBridge
      hbridge

theorem fielded_switching_clocked_payload_bridge_implies_exact_visible_compression_regression
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s clock : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hbridge :
      FieldedSwitchingOnlyClockedKpolyFiniteLearningBridge Ω Z k s clock hist items) :
    FieldedSwitchingOnlyExactVisibleCompressionBridge Ω Z k s hist items := by
  exact
    fieldedSwitchingOnlyExactVisibleCompressionBridge_of_clockedKpolyFiniteLearningBridge
      hbridge

theorem finite_predictor_cover_of_product_bound_only_bridge_regression
    {Ω : Type u} [Fintype Ω] {Z : Type v} {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index)
    (hbridge : ProductBoundOnlyExactVisibleCompressionBridge Ω Z k s hist items)
    (hprod : V13FieldedProductBoundFrom Ω hist items) :
    G.FinitePredictorCover (2 ^ s) := by
  exact finitePredictorCover_of_productBoundOnlyExactVisibleCompressionBridge
    G hbridge hprod

theorem finite_representative_cover_of_product_bound_only_bridge_regression
    {Ω : Type u} [Fintype Ω] {Z : Type v} {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index)
    (hbridge : ProductBoundOnlyExactVisibleCompressionBridge Ω Z k s hist items)
    (hprod : V13FieldedProductBoundFrom Ω hist items) :
    G.FiniteIndexRepresentativeCover (2 ^ s) := by
  exact finiteIndexRepresentativeCover_of_productBoundOnlyExactVisibleCompressionBridge
    G hbridge hprod

theorem finite_quotient_of_product_bound_only_bridge_regression
    {Ω : Type u} [Fintype Ω] {Z : Type v} {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index)
    (hbridge : ProductBoundOnlyExactVisibleCompressionBridge Ω Z k s hist items)
    (hprod : V13FieldedProductBoundFrom Ω hist items) :
    G.FinitePredictorQuotient (2 ^ s) := by
  exact finitePredictorQuotient_of_productBoundOnlyExactVisibleCompressionBridge
    G hbridge hprod

theorem finite_predictor_cover_of_fielded_switching_only_bridge_regression
    {Ω : Type u} [Fintype Ω] {Z : Type v} {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index)
    (hbridge : FieldedSwitchingOnlyExactVisibleCompressionBridge Ω Z k s hist items)
    (hfield : V13FieldSwitchingInstantiatedFrom hist items) :
    G.FinitePredictorCover (2 ^ s) := by
  exact finitePredictorCover_of_fieldedSwitchingOnlyExactVisibleCompressionBridge
    G hbridge hfield

theorem finite_representative_cover_of_fielded_switching_only_bridge_regression
    {Ω : Type u} [Fintype Ω] {Z : Type v} {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index)
    (hbridge : FieldedSwitchingOnlyExactVisibleCompressionBridge Ω Z k s hist items)
    (hfield : V13FieldSwitchingInstantiatedFrom hist items) :
    G.FiniteIndexRepresentativeCover (2 ^ s) := by
  exact finiteIndexRepresentativeCover_of_fieldedSwitchingOnlyExactVisibleCompressionBridge
    G hbridge hfield

theorem finite_quotient_of_fielded_switching_only_bridge_regression
    {Ω : Type u} [Fintype Ω] {Z : Type v} {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index)
    (hbridge : FieldedSwitchingOnlyExactVisibleCompressionBridge Ω Z k s hist items)
    (hfield : V13FieldSwitchingInstantiatedFrom hist items) :
    G.FinitePredictorQuotient (2 ^ s) := by
  exact finitePredictorQuotient_of_fieldedSwitchingOnlyExactVisibleCompressionBridge
    G hbridge hfield

theorem product_bound_bridge_surjective_family_counterexample_regression
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} {G : ExactVisibleSwitchedFamily Z k Index}
    (hprod : V13FieldedProductBoundFrom Ω hist items)
    (hsurj : Function.Surjective G.predict)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (V13FieldedProductBoundFrom Ω hist items →
        ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s) := by
  exact
    not_productBoundExactVisibleCompressionBridge_of_true_productBound_of_surjective_predict_of_lt_surfaceCard
      hprod hsurj hs

theorem fielded_switching_bridge_surjective_family_counterexample_regression
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} {G : ExactVisibleSwitchedFamily Z k Index}
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hsurj : Function.Surjective G.predict)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (V13FieldSwitchingInstantiatedFrom hist items →
        ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s) := by
  exact
    not_fieldedSwitchingExactVisibleCompressionBridge_of_true_fieldedSwitching_of_surjective_predict_of_lt_surfaceCard
      hfield hsurj hs

theorem product_bound_semantic_bridge_surjective_family_counterexample_regression
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} {G : ExactVisibleSwitchedFamily Z k Index}
    (hprod : V13FieldedProductBoundFrom Ω hist items)
    (hsurj : Function.Surjective G.predict)
    (hs : 2 ^ s < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ProductBoundSemanticFiniteImageBridge Ω Z k s hist items G := by
  exact
    not_productBoundSemanticFiniteImageBridge_of_true_productBound_of_surjective_predict_of_lt_predictorCard
      hprod hsurj hs

theorem fielded_switching_semantic_bridge_surjective_family_counterexample_regression
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} {G : ExactVisibleSwitchedFamily Z k Index}
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hsurj : Function.Surjective G.predict)
    (hs : 2 ^ s < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ FieldedSwitchingSemanticFiniteImageBridge Ω Z k s hist items G := by
  exact
    not_fieldedSwitchingSemanticFiniteImageBridge_of_true_fieldedSwitching_of_surjective_predict_of_lt_predictorCard
      hfield hsurj hs

theorem product_bound_clocked_payload_bridge_surjective_family_counterexample_regression
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s clock : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} {G : ExactVisibleSwitchedFamily Z k Index}
    (hprod : V13FieldedProductBoundFrom Ω hist items)
    (hsurj : Function.Surjective G.predict)
    (hs : 2 ^ s < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (V13FieldedProductBoundFrom Ω hist items →
        ClockedKpolyFiniteLearningPayload G s clock) := by
  exact
    not_productBoundClockedKpolyFiniteLearningBridge_of_true_productBound_of_surjective_predict_of_lt_predictorCard
      hprod hsurj hs

theorem fielded_switching_clocked_payload_bridge_surjective_family_counterexample_regression
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s clock : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} {G : ExactVisibleSwitchedFamily Z k Index}
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hsurj : Function.Surjective G.predict)
    (hs : 2 ^ s < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (V13FieldSwitchingInstantiatedFrom hist items →
        ClockedKpolyFiniteLearningPayload G s clock) := by
  exact
    not_fieldedSwitchingClockedKpolyFiniteLearningBridge_of_true_fieldedSwitching_of_surjective_predict_of_lt_predictorCard
      hfield hsurj hs

theorem product_bound_only_bridge_surjective_family_counterexample_regression
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index)
    (hprod : V13FieldedProductBoundFrom Ω hist items)
    (hsurj : Function.Surjective G.predict)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ProductBoundOnlyExactVisibleCompressionBridge Ω Z k s hist items := by
  exact
    not_productBoundOnlyExactVisibleCompressionBridge_of_true_productBound_of_surjective_predict_of_lt_surfaceCard
      G hprod hsurj hs

theorem fielded_switching_only_bridge_surjective_family_counterexample_regression
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index)
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hsurj : Function.Surjective G.predict)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ FieldedSwitchingOnlyExactVisibleCompressionBridge Ω Z k s hist items := by
  exact
    not_fieldedSwitchingOnlyExactVisibleCompressionBridge_of_true_fieldedSwitching_of_surjective_predict_of_lt_surfaceCard
      G hfield hsurj hs

theorem product_bound_only_clocked_payload_bridge_surjective_family_counterexample_regression
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s clock : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index)
    (hprod : V13FieldedProductBoundFrom Ω hist items)
    (hsurj : Function.Surjective G.predict)
    (hs : 2 ^ s < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ProductBoundOnlyClockedKpolyFiniteLearningBridge
        Ω Z k s clock hist items := by
  exact
    not_productBoundOnlyClockedKpolyFiniteLearningBridge_of_true_productBound_of_surjective_predict_of_lt_predictorCard
      G hprod hsurj hs

theorem fielded_switching_only_clocked_payload_bridge_surjective_family_counterexample_regression
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s clock : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index)
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hsurj : Function.Surjective G.predict)
    (hs : 2 ^ s < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ FieldedSwitchingOnlyClockedKpolyFiniteLearningBridge
        Ω Z k s clock hist items := by
  exact
    not_fieldedSwitchingOnlyClockedKpolyFiniteLearningBridge_of_true_fieldedSwitching_of_surjective_predict_of_lt_predictorCard
      G hfield hsurj hs

theorem product_bound_only_bridge_empty_counterexample_regression
    {Ω : Type*} [Fintype Ω] {Z : Type*} [Fintype Z] {k s : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ProductBoundOnlyExactVisibleCompressionBridge
        Ω Z k s ([] : List (FiniteEvent Ω)) ([] : List (V13FieldedStep Ω)) := by
  exact not_productBoundOnlyExactVisibleCompressionBridge_nil_of_lt_surfaceCard
    (Ω := Ω) (Z := Z) (k := k) (s := s) hs

theorem fielded_switching_only_bridge_empty_counterexample_regression
    {Ω : Type*} [Fintype Ω] {Z : Type*} [Fintype Z] {k s : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ FieldedSwitchingOnlyExactVisibleCompressionBridge
        Ω Z k s ([] : List (FiniteEvent Ω)) ([] : List (V13FieldedStep Ω)) := by
  exact not_fieldedSwitchingOnlyExactVisibleCompressionBridge_nil_of_lt_surfaceCard
    (Ω := Ω) (Z := Z) (k := k) (s := s) hs

theorem product_bound_only_clocked_payload_bridge_empty_counterexample_regression
    {Ω : Type*} [Fintype Ω] {Z : Type*} [Fintype Z] {k s clock : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ProductBoundOnlyClockedKpolyFiniteLearningBridge
        Ω Z k s clock
        ([] : List (FiniteEvent Ω)) ([] : List (V13FieldedStep Ω)) := by
  exact not_productBoundOnlyClockedKpolyFiniteLearningBridge_nil_of_lt_surfaceCard
    (Ω := Ω) (Z := Z) (k := k) (s := s) (clock := clock) hs

theorem fielded_switching_only_clocked_payload_bridge_empty_counterexample_regression
    {Ω : Type*} [Fintype Ω] {Z : Type*} [Fintype Z] {k s clock : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ FieldedSwitchingOnlyClockedKpolyFiniteLearningBridge
        Ω Z k s clock
        ([] : List (FiniteEvent Ω)) ([] : List (V13FieldedStep Ω)) := by
  exact not_fieldedSwitchingOnlyClockedKpolyFiniteLearningBridge_nil_of_lt_surfaceCard
    (Ω := Ω) (Z := Z) (k := k) (s := s) (clock := clock) hs

theorem product_bound_only_bridge_bool_pair_one_step_counterexample_regression
    {Z : Type*} [Fintype Z] {k s : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ProductBoundOnlyExactVisibleCompressionBridge
        (Bool × Bool) Z k s
        ([] : List (FiniteEvent (Bool × Bool)))
        [v13BoolPairUnitFieldedStep] := by
  exact
    not_productBoundOnlyExactVisibleCompressionBridge_boolPair_one_step_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) hs

theorem fielded_switching_only_bridge_bool_pair_one_step_counterexample_regression
    {Z : Type*} [Fintype Z] {k s : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ FieldedSwitchingOnlyExactVisibleCompressionBridge
        (Bool × Bool) Z k s
        ([] : List (FiniteEvent (Bool × Bool)))
        [v13BoolPairUnitFieldedStep] := by
  exact
    not_fieldedSwitchingOnlyExactVisibleCompressionBridge_boolPair_one_step_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) hs

theorem product_bound_only_clocked_payload_bridge_bool_pair_one_step_counterexample_regression
    {Z : Type*} [Fintype Z] {k s clock : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ProductBoundOnlyClockedKpolyFiniteLearningBridge
        (Bool × Bool) Z k s clock
        ([] : List (FiniteEvent (Bool × Bool)))
        [v13BoolPairUnitFieldedStep] := by
  exact
    not_productBoundOnlyClockedKpolyFiniteLearningBridge_boolPair_one_step_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) (clock := clock) hs

theorem fielded_switching_only_clocked_payload_bridge_bool_pair_one_step_counterexample_regression
    {Z : Type*} [Fintype Z] {k s clock : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ FieldedSwitchingOnlyClockedKpolyFiniteLearningBridge
        (Bool × Bool) Z k s clock
        ([] : List (FiniteEvent (Bool × Bool)))
        [v13BoolPairUnitFieldedStep] := by
  exact
    not_fieldedSwitchingOnlyClockedKpolyFiniteLearningBridge_boolPair_one_step_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) (clock := clock) hs

theorem product_bound_only_bridge_bool_pair_concrete_counterexample_regression :
    ¬ ProductBoundOnlyExactVisibleCompressionBridge
        (Bool × Bool) Bool 1 0
        ([] : List (FiniteEvent (Bool × Bool)))
        [v13BoolPairUnitFieldedStep] := by
  refine
    not_productBoundOnlyExactVisibleCompressionBridge_boolPair_one_step_of_lt_surfaceCard
      (Z := Bool) (k := 1) (s := 0) ?_
  rw [card_exactVisiblePostSwitchSurface (Z := Bool) (k := 1)]
  decide

theorem fielded_switching_only_bridge_bool_pair_concrete_counterexample_regression :
    ¬ FieldedSwitchingOnlyExactVisibleCompressionBridge
        (Bool × Bool) Bool 1 0
        ([] : List (FiniteEvent (Bool × Bool)))
        [v13BoolPairUnitFieldedStep] := by
  refine
    not_fieldedSwitchingOnlyExactVisibleCompressionBridge_boolPair_one_step_of_lt_surfaceCard
      (Z := Bool) (k := 1) (s := 0) ?_
  rw [card_exactVisiblePostSwitchSurface (Z := Bool) (k := 1)]
  decide

theorem product_bound_only_clocked_payload_bridge_bool_pair_concrete_counterexample_regression :
    ¬ ProductBoundOnlyClockedKpolyFiniteLearningBridge
        (Bool × Bool) Bool 1 0 0
        ([] : List (FiniteEvent (Bool × Bool)))
        [v13BoolPairUnitFieldedStep] := by
  refine
    not_productBoundOnlyClockedKpolyFiniteLearningBridge_boolPair_one_step_of_lt_surfaceCard
      (Z := Bool) (k := 1) (s := 0) (clock := 0) ?_
  rw [card_exactVisiblePostSwitchSurface (Z := Bool) (k := 1)]
  decide

theorem fielded_switching_only_clocked_payload_bridge_bool_pair_concrete_counterexample_regression :
    ¬ FieldedSwitchingOnlyClockedKpolyFiniteLearningBridge
        (Bool × Bool) Bool 1 0 0
        ([] : List (FiniteEvent (Bool × Bool)))
        [v13BoolPairUnitFieldedStep] := by
  refine
    not_fieldedSwitchingOnlyClockedKpolyFiniteLearningBridge_boolPair_one_step_of_lt_surfaceCard
      (Z := Bool) (k := 1) (s := 0) (clock := 0) ?_
  rw [card_exactVisiblePostSwitchSurface (Z := Bool) (k := 1)]
  decide

end Mettapedia.Computability.PNP.ProductSuccessKpolyBridgeObstructionRegression
