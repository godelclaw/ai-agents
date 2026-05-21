import Mettapedia.Computability.PNP.CruxSynthesis

/-!
# Regression checks for the PNP crux synthesis ledger

These wrappers pin the meta-synthesis status of the current PNP packet: it
covers the deterministic same-source and existing fixed-field obstruction
families listed in the ledger, including the same-source finite-count
approximation subcase, but it is not stop-grade because named repair classes
remain uncovered.
-/

namespace Mettapedia.Computability.PNP.CruxSynthesisRegression

open Mettapedia.Computability.PNP
open Mettapedia.GSLT.Meredith.WeaknessBridge
open scoped ENNReal

universe u v w z

theorem current_pnp_covered_repair_classes_exact_regression
    (repair : PNPRepairClass) :
    repair ∈ currentPNPCoveredRepairClasses ↔
      currentPNPLocalCruxPacket.covers repair := by
  exact currentPNPCoveredRepairClasses_exact repair

theorem current_pnp_uncovered_repair_classes_exact_regression
    (repair : PNPRepairClass) :
    repair ∈ currentPNPUncoveredRepairClasses ↔
      ¬ currentPNPLocalCruxPacket.covers repair := by
  exact currentPNPUncoveredRepairClasses_exact repair

theorem short_global_decoder_supported_sat_search_equiv_single_message_regression
    {Public : Type u} {Var : Public → Type v}
    {Witness : Public → Type w} {Message : Type z}
    (D : ManuscriptCNFReadoutData Public Var Witness Message)
    (hsat : D.SupportedCNFSatisfiable)
    (hcomplete : D.CNFExtractionComplete) :
    D.SupportedArbitraryOutputSATSearchCorrect ↔ D.SingleMessagePromise := by
  exact
    shortGlobalDecoderCoverage_anchor_supported_sat_search_equiv_singleMessagePromise
      D hsat hcomplete

theorem short_global_decoder_incomplete_extraction_countermodel_regression :
    unrepresentedOneVarManuscriptCNFReadoutData.SupportedArbitraryOutputSATSearchCorrect ∧
      ¬ unrepresentedOneVarManuscriptCNFReadoutData.SingleMessagePromise ∧
      ¬ unrepresentedOneVarManuscriptCNFReadoutData.CNFExtractionComplete := by
  exact shortGlobalDecoderCoverage_anchor_incomplete_extraction_countermodel

theorem current_pnp_finite_coin_covered_subrepairs_exact_regression
    (repair : PNPFiniteCoinSubrepairClass) :
    repair ∈ currentPNPFiniteCoinCoveredSubrepairs := by
  exact currentPNPFiniteCoinCoveredSubrepairs_exact repair

theorem current_pnp_residual_side_information_covered_subrepairs_exact_regression
    (repair : PNPResidualSideInformationSubrepairClass) :
    repair ∈ currentPNPResidualSideInformationCoveredSubrepairs := by
  exact currentPNPResidualSideInformationCoveredSubrepairs_exact repair

theorem current_pnp_residual_side_information_toy_collision_subrepair_regression :
    PNPResidualSideInformationSubrepairClass.concreteSameSourceResidualCollision ∈
      currentPNPResidualSideInformationCoveredSubrepairs := by
  exact currentPNPResidualSideInformationCoveredSubrepairs_exact
    PNPResidualSideInformationSubrepairClass.concreteSameSourceResidualCollision

theorem current_pnp_residual_side_information_supported_collision_subrepair_regression :
    PNPResidualSideInformationSubrepairClass.positiveAdvantageSupportedResidualCollision ∈
      currentPNPResidualSideInformationCoveredSubrepairs := by
  exact currentPNPResidualSideInformationCoveredSubrepairs_exact
    PNPResidualSideInformationSubrepairClass.positiveAdvantageSupportedResidualCollision

theorem current_pnp_residual_side_information_prediction_separation_subrepair_regression :
    PNPResidualSideInformationSubrepairClass.strictHalfAdvantagePredictionSeparation ∈
      currentPNPResidualSideInformationCoveredSubrepairs := by
  exact currentPNPResidualSideInformationCoveredSubrepairs_exact
    PNPResidualSideInformationSubrepairClass.strictHalfAdvantagePredictionSeparation

theorem current_pnp_residual_side_information_positive_resolved_mass_subrepair_regression :
    PNPResidualSideInformationSubrepairClass.positiveAdvantageForcesPositiveResolvedMass ∈
      currentPNPResidualSideInformationCoveredSubrepairs := by
  exact currentPNPResidualSideInformationCoveredSubrepairs_exact
    PNPResidualSideInformationSubrepairClass.positiveAdvantageForcesPositiveResolvedMass

theorem current_pnp_residual_side_information_strict_half_positive_resolved_mass_subrepair_regression :
    PNPResidualSideInformationSubrepairClass.strictHalfAdvantageForcesPositiveResolvedMass ∈
      currentPNPResidualSideInformationCoveredSubrepairs := by
  exact currentPNPResidualSideInformationCoveredSubrepairs_exact
    PNPResidualSideInformationSubrepairClass.strictHalfAdvantageForcesPositiveResolvedMass

theorem current_pnp_residual_side_information_positive_resolved_mass_pure_package_subrepair_regression :
    PNPResidualSideInformationSubrepairClass.positiveResolvedMassPureResidualPackage ∈
      currentPNPResidualSideInformationCoveredSubrepairs := by
  exact currentPNPResidualSideInformationCoveredSubrepairs_exact
    PNPResidualSideInformationSubrepairClass.positiveResolvedMassPureResidualPackage

theorem current_pnp_residual_side_information_exact_post_switch_pure_package_subrepair_regression :
    PNPResidualSideInformationSubrepairClass.exactPostSwitchConcretePureResidualWitness ∈
      currentPNPResidualSideInformationCoveredSubrepairs := by
  exact currentPNPResidualSideInformationCoveredSubrepairs_exact
    PNPResidualSideInformationSubrepairClass.exactPostSwitchConcretePureResidualWitness

theorem current_pnp_residual_side_information_exact_post_switch_fork_subrepair_regression :
    PNPResidualSideInformationSubrepairClass.exactPostSwitchPredictionWitnessForcesForkObstruction ∈
      currentPNPResidualSideInformationCoveredSubrepairs := by
  exact currentPNPResidualSideInformationCoveredSubrepairs_exact
    PNPResidualSideInformationSubrepairClass.exactPostSwitchPredictionWitnessForcesForkObstruction

theorem v13_residual_side_information_subcoverage_regression :
    V13ResidualSideInformationSubcoverage := by
  exact v13ResidualSideInformationSubcoverage

theorem current_pnp_randomized_residual_covered_subrepairs_exact_regression
    (repair : PNPRandomizedResidualSubrepairClass) :
    repair ∈ currentPNPRandomizedResidualCoveredSubrepairs := by
  exact currentPNPRandomizedResidualCoveredSubrepairs_exact repair

theorem current_pnp_randomized_residual_deterministic_coin_slice_regression :
    PNPRandomizedResidualSubrepairClass.positiveAdvantageDeterministicCoinSliceWitness ∈
      currentPNPRandomizedResidualCoveredSubrepairs := by
  exact currentPNPRandomizedResidualCoveredSubrepairs_exact
    PNPRandomizedResidualSubrepairClass.positiveAdvantageDeterministicCoinSliceWitness

theorem current_pnp_randomized_residual_strict_half_deterministic_coin_slice_regression :
    PNPRandomizedResidualSubrepairClass.strictHalfDeterministicCoinSliceWitness ∈
      currentPNPRandomizedResidualCoveredSubrepairs := by
  exact currentPNPRandomizedResidualCoveredSubrepairs_exact
    PNPRandomizedResidualSubrepairClass.strictHalfDeterministicCoinSliceWitness

theorem current_pnp_randomized_residual_strict_half_coin_slice_residual_package_regression :
    PNPRandomizedResidualSubrepairClass.strictHalfDeterministicCoinSliceResidualObstructionPackage ∈
      currentPNPRandomizedResidualCoveredSubrepairs := by
  exact currentPNPRandomizedResidualCoveredSubrepairs_exact
    PNPRandomizedResidualSubrepairClass.strictHalfDeterministicCoinSliceResidualObstructionPackage

theorem current_pnp_post_switch_randomized_residual_deterministic_coin_slice_regression :
    PNPRandomizedResidualSubrepairClass.postSwitchPositiveAdvantageDeterministicCoinSliceWitness ∈
      currentPNPRandomizedResidualCoveredSubrepairs := by
  exact currentPNPRandomizedResidualCoveredSubrepairs_exact
    PNPRandomizedResidualSubrepairClass.postSwitchPositiveAdvantageDeterministicCoinSliceWitness

theorem current_pnp_post_switch_randomized_residual_strict_half_blocker_regression :
    PNPRandomizedResidualSubrepairClass.postSwitchExactSupportNoStrictHalfAdvantage ∈
      currentPNPRandomizedResidualCoveredSubrepairs := by
  exact currentPNPRandomizedResidualCoveredSubrepairs_exact
    PNPRandomizedResidualSubrepairClass.postSwitchExactSupportNoStrictHalfAdvantage

theorem current_pnp_post_switch_randomized_residual_strict_half_deterministic_coin_slice_regression :
    PNPRandomizedResidualSubrepairClass.postSwitchStrictHalfDeterministicCoinSliceWitness ∈
      currentPNPRandomizedResidualCoveredSubrepairs := by
  exact currentPNPRandomizedResidualCoveredSubrepairs_exact
    PNPRandomizedResidualSubrepairClass.postSwitchStrictHalfDeterministicCoinSliceWitness

theorem current_pnp_post_switch_randomized_residual_strict_half_coin_slice_residual_package_regression :
    PNPRandomizedResidualSubrepairClass.postSwitchStrictHalfDeterministicCoinSliceResidualObstructionPackage ∈
      currentPNPRandomizedResidualCoveredSubrepairs := by
  exact currentPNPRandomizedResidualCoveredSubrepairs_exact
    PNPRandomizedResidualSubrepairClass.postSwitchStrictHalfDeterministicCoinSliceResidualObstructionPackage

theorem current_pnp_post_switch_randomized_residual_supportwise_unresolved_subrepair_regression :
    PNPRandomizedResidualSubrepairClass.postSwitchSupportwiseUnresolvedNoAdvantage ∈
      currentPNPRandomizedResidualCoveredSubrepairs := by
  exact currentPNPRandomizedResidualCoveredSubrepairs_exact
    PNPRandomizedResidualSubrepairClass.postSwitchSupportwiseUnresolvedNoAdvantage

theorem v13_randomized_residual_subcoverage_regression :
    V13RandomizedResidualSubcoverage := by
  exact v13RandomizedResidualSubcoverage

theorem randomized_residual_strict_half_coin_slice_residual_package_regression
    {α Coin U V : Type*} [Fintype α] [Fintype Coin]
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
    ∃ c, 0 < coinWeight c ∧
      (¬ SideInfoDeterminedBy u (fun x => v x c) ∧
        PositiveWeightSideInfoCollisionOverBase u (fun x => v x c) w ∧
        (∃ x, 0 < w x ∧ u (τ x) = u x ∧ v (τ x) c ≠ v x c) ∧
        (∃ x, 0 < w x ∧
          ¬ SourceOnlyPredicateCapturesSideEq u (fun x => v x c) (v x c))) := by
  exact
    randomizedResidualCoverage_anchor_strict_half_advantage_coin_slice_forces_residual_obstruction_package
      τ u v y w coinWeight h hτ hu hy hw hadv

theorem post_switch_randomized_residual_strict_half_coin_slice_residual_package_regression
    {Z Coin V : Type*} {k : ℕ} [Fintype Z] [Fintype Coin]
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
            (fun u => v u c) (v u c))) := by
  exact
    randomizedResidualCoverage_anchor_postSwitch_strict_half_advantage_coin_slice_forces_residual_obstruction_package
      v y w coinWeight h hy hw hadv

theorem post_switch_fork_strict_half_package_regression
    {Z : Type*} [Fintype Z] {k : ℕ}
    (y : PostSwitchInput Z k → Bool) (w : PostSwitchInput Z k → ℕ)
    (h : (Z × BitVec k) × BitVec k → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hadv :
      weightedTotalMass w <
        2 * weightedCorrectMass (fun u => (invariantProjection u, u.b)) y w h) :
    (∃ u : PostSwitchInput Z k, 0 < w u ∧ (tiInputMap u).b ≠ u.b) ∧
      (∃ u : PostSwitchInput Z k, 0 < w u ∧ nonzeroColumn u.a) ∧
      ¬ exactInputInvariantWeightedSupport w := by
  exact
    postSwitchForkCoverage_anchor_strict_half_advantage_fork_obstruction_package
      y w h hy hw hadv

theorem finite_coin_stack_uncovered_broad_classes_exact_regression
    (repair : PNPRepairClass) :
    repair ∈ finiteCoinStackUncoveredBroadRepairClasses ↔
      repair ∈ currentPNPUncoveredRepairClasses := by
  exact finiteCoinStackUncoveredBroadRepairClasses_exact repair

theorem current_pnp_kpoly_covered_subrepairs_exact_regression
    (repair : PNPKpolySubrepairClass) :
    repair ∈ currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact repair

theorem current_pnp_kpoly_actual_observed_support_subrepair_regression :
    PNPKpolySubrepairClass.actualObservedSupportPayloadInsufficiency ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualObservedSupportPayloadInsufficiency

theorem current_pnp_kpoly_actual_observed_support_section_boundary_regression :
    PNPKpolySubrepairClass.actualObservedSupportUniformSectionBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualObservedSupportUniformSectionBoundary

theorem current_pnp_kpoly_actual_observed_support_quotient_loss_regression :
    PNPKpolySubrepairClass.actualObservedSupportQuotientLossBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualObservedSupportQuotientLossBoundary

theorem current_pnp_kpoly_actual_observed_support_decoder_recovery_regression :
    PNPKpolySubrepairClass.actualObservedSupportDecoderRecoveryBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualObservedSupportDecoderRecoveryBoundary

theorem current_pnp_kpoly_actual_observed_support_observable_property_regression :
    PNPKpolySubrepairClass.actualObservedSupportObservablePropertyBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualObservedSupportObservablePropertyBoundary

theorem current_pnp_kpoly_actual_observed_support_property_factor_regression :
    PNPKpolySubrepairClass.actualObservedSupportPropertyFactorBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualObservedSupportPropertyFactorBoundary

theorem current_pnp_kpoly_actual_observed_support_point_query_regression :
    PNPKpolySubrepairClass.actualObservedSupportPointQueryBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualObservedSupportPointQueryBoundary

theorem current_pnp_kpoly_actual_observed_support_query_family_regression :
    PNPKpolySubrepairClass.actualObservedSupportQueryFamilyBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualObservedSupportQueryFamilyBoundary

theorem current_pnp_kpoly_actual_observed_support_adaptive_query_regression :
    PNPKpolySubrepairClass.actualObservedSupportAdaptiveQueryBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualObservedSupportAdaptiveQueryBoundary

theorem current_pnp_kpoly_actual_local_plugin_lookup_regression :
    PNPKpolySubrepairClass.actualLocalPluginLookupFullRuleObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalPluginLookupFullRuleObstruction

theorem current_pnp_kpoly_actual_local_plugin_majority_regression :
    PNPKpolySubrepairClass.actualLocalPluginMajorityFullRuleObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalPluginMajorityFullRuleObstruction

theorem current_pnp_kpoly_actual_local_plugin_sample_majority_regression :
    PNPKpolySubrepairClass.actualLocalPluginSampleMajorityFullRuleObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalPluginSampleMajorityFullRuleObstruction

theorem current_pnp_kpoly_actual_local_plugin_sample_majority_sparse_threshold_erm_visible_budget_regression :
    PNPKpolySubrepairClass.actualLocalPluginSampleMajoritySparseThresholdERMVisibleBudgetBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalPluginSampleMajoritySparseThresholdERMVisibleBudgetBoundary

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityThresholdBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityThresholdBoundary

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_false_support_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityFalseSupportBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityFalseSupportBoundary

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_default_tie_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityDefaultTieBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityDefaultTieBoundary

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_fallback_side_channel_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityFallbackSideChannelBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityFallbackSideChannelBoundary

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_fallback_finite_predictor_cover_obstruction_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityFallbackFinitePredictorCoverObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityFallbackFinitePredictorCoverObstruction

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_fallback_finite_index_representative_cover_obstruction_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityFallbackFiniteIndexRepresentativeCoverObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityFallbackFiniteIndexRepresentativeCoverObstruction

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_fallback_finite_predictor_quotient_obstruction_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityFallbackFinitePredictorQuotientObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityFallbackFinitePredictorQuotientObstruction

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_fallback_exact_visible_compression_obstruction_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityFallbackExactVisibleCompressionObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityFallbackExactVisibleCompressionObstruction

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_fallback_clocked_realization_obstruction_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityFallbackClockedRealizationObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityFallbackClockedRealizationObstruction

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_fallback_clocked_payload_obstruction_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityFallbackClockedPayloadObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityFallbackClockedPayloadObstruction

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_fallback_family_sparse_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityFallbackFamilySparseBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityFallbackFamilySparseBoundary

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_fallback_family_empty_sample_realization_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityFallbackFamilyEmptySampleRealizationBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityFallbackFamilyEmptySampleRealizationBoundary

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_fallback_family_radius_cover_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityFallbackFamilyRadiusCoverBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityFallbackFamilyRadiusCoverBoundary

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_fallback_family_finite_predictor_cover_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityFallbackFamilyFinitePredictorCoverBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityFallbackFamilyFinitePredictorCoverBoundary

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_fallback_family_radius_cover_surjectivity_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityFallbackFamilyRadiusCoverSurjectivityBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityFallbackFamilyRadiusCoverSurjectivityBoundary

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_fallback_family_pointwise_radius_cover_surjectivity_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityFallbackFamilyPointwiseRadiusCoverSurjectivityBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityFallbackFamilyPointwiseRadiusCoverSurjectivityBoundary

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_fallback_family_fallback_surjective_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityFallbackFamilyFallbackSurjectiveBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityFallbackFamilyFallbackSurjectiveBoundary

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_fallback_family_large_disagreement_support_obstruction_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityFallbackFamilyLargeDisagreementSupportObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityFallbackFamilyLargeDisagreementSupportObstruction

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_fallback_family_small_subsets_product_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityFallbackFamilySmallSubsetsProductBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityFallbackFamilySmallSubsetsProductBoundary

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_fallback_family_small_subsets_product_surjectivity_obstruction_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityFallbackFamilySmallSubsetsProductSurjectivityObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityFallbackFamilySmallSubsetsProductSurjectivityObstruction

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_fallback_family_full_radius_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityFallbackFamilyFullRadiusBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityFallbackFamilyFullRadiusBoundary

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_fallback_family_zero_sample_fallback_equivalence_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityFallbackFamilyZeroSampleFallbackEquivalence ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityFallbackFamilyZeroSampleFallbackEquivalence

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_fallback_family_zero_sample_finite_predictor_cover_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityFallbackFamilyZeroSampleFinitePredictorCoverBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityFallbackFamilyZeroSampleFinitePredictorCoverBoundary

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_fallback_family_zero_sample_finite_index_representative_cover_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityFallbackFamilyZeroSampleFiniteIndexRepresentativeCoverBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityFallbackFamilyZeroSampleFiniteIndexRepresentativeCoverBoundary

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_fallback_family_zero_sample_finite_predictor_quotient_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityFallbackFamilyZeroSampleFinitePredictorQuotientBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityFallbackFamilyZeroSampleFinitePredictorQuotientBoundary

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_fallback_family_zero_sample_exact_visible_compression_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityFallbackFamilyZeroSampleExactVisibleCompressionBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityFallbackFamilyZeroSampleExactVisibleCompressionBoundary

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_fallback_family_zero_sample_clocked_realization_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityFallbackFamilyZeroSampleClockedRealizationBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityFallbackFamilyZeroSampleClockedRealizationBoundary

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_fallback_family_zero_sample_clocked_payload_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityFallbackFamilyZeroSampleClockedPayloadBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityFallbackFamilyZeroSampleClockedPayloadBoundary

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_bit_fallback_sparse_threshold_erm_visible_budget_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackSparseThresholdERMVisibleBudgetBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackSparseThresholdERMVisibleBudgetBoundary

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_bit_fallback_radius_cover_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackRadiusCoverBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackRadiusCoverBoundary

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_bit_fallback_finite_predictor_cover_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackFinitePredictorCoverBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackFinitePredictorCoverBoundary

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_bit_fallback_radius_cover_surjectivity_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackRadiusCoverSurjectivityBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackRadiusCoverSurjectivityBoundary

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_bit_fallback_pointwise_radius_cover_surjectivity_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackPointwiseRadiusCoverSurjectivityBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackPointwiseRadiusCoverSurjectivityBoundary

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_bit_fallback_full_radius_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackFullRadiusBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackFullRadiusBoundary

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_bit_fallback_zero_fallback_bits_deficit_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackZeroFallbackBitsDeficitObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackZeroFallbackBitsDeficitObstruction

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_bit_fallback_zero_fallback_bits_exact_radius_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackZeroFallbackBitsExactRadiusBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackZeroFallbackBitsExactRadiusBoundary

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_bit_fallback_zero_sample_finite_predictor_cover_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackZeroSampleFinitePredictorCoverBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackZeroSampleFinitePredictorCoverBoundary

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_bit_fallback_zero_sample_finite_index_representative_cover_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackZeroSampleFiniteIndexRepresentativeCoverBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackZeroSampleFiniteIndexRepresentativeCoverBoundary

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_bit_fallback_zero_sample_finite_predictor_quotient_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackZeroSampleFinitePredictorQuotientBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackZeroSampleFinitePredictorQuotientBoundary

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_bit_fallback_zero_sample_exact_visible_compression_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackZeroSampleExactVisibleCompressionBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackZeroSampleExactVisibleCompressionBoundary

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_bit_fallback_zero_sample_clocked_realization_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackZeroSampleClockedRealizationBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackZeroSampleClockedRealizationBoundary

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_bit_fallback_zero_sample_clocked_payload_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackZeroSampleClockedPayloadBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackZeroSampleClockedPayloadBoundary

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_bit_fallback_recovery_lightest_point_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackRecoveryLightestPointBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackRecoveryLightestPointBoundary

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_bit_fallback_exact_decoder_full_rule_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackExactDecoderFullRuleBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackExactDecoderFullRuleBoundary

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_bit_fallback_exact_decoder_sparse_threshold_erm_visible_budget_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackExactDecoderSparseThresholdERMVisibleBudgetBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackExactDecoderSparseThresholdERMVisibleBudgetBoundary

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_bit_fallback_exact_decoder_no_extractor_sparse_threshold_erm_visible_budget_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackExactDecoderNoExtractorSparseThresholdERMVisibleBudgetBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackExactDecoderNoExtractorSparseThresholdERMVisibleBudgetBoundary

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_bit_fallback_exact_decoder_visible_width_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackExactDecoderVisibleWidthBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackExactDecoderVisibleWidthBoundary

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_bit_fallback_exact_decoder_lightest_point_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackExactDecoderLightestPointBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackExactDecoderLightestPointBoundary

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_bit_fallback_exact_decoder_joint_recovery_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackExactDecoderJointRecoveryBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackExactDecoderJointRecoveryBoundary

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_bit_fallback_exact_decoder_no_extractor_visible_width_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackExactDecoderNoExtractorVisibleWidthBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackExactDecoderNoExtractorVisibleWidthBoundary

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_bit_fallback_exact_decoder_no_extractor_lightest_point_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackExactDecoderNoExtractorLightestPointBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackExactDecoderNoExtractorLightestPointBoundary

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_bit_fallback_exact_decoder_no_extractor_joint_recovery_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackExactDecoderNoExtractorJointRecoveryBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackExactDecoderNoExtractorJointRecoveryBoundary

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_bit_fallback_exact_decoder_clocked_payload_obstruction_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackExactDecoderClockedPayloadObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackExactDecoderClockedPayloadObstruction

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_bit_fallback_polynomial_envelope_budget_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackPolynomialEnvelopeBudgetBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackPolynomialEnvelopeBudgetBoundary

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_bit_fallback_polynomial_envelope_surjectivity_obstruction_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackPolynomialEnvelopeSurjectivityObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackPolynomialEnvelopeSurjectivityObstruction

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_bit_fallback_factor_budget_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackFactorBudgetBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackFactorBudgetBoundary

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_bit_fallback_factor_surjectivity_obstruction_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackFactorSurjectivityObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackFactorSurjectivityObstruction

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_bit_fallback_successor_factor_budget_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackSuccessorFactorBudgetBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackSuccessorFactorBudgetBoundary

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_bit_fallback_successor_factor_surjectivity_obstruction_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackSuccessorFactorSurjectivityObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackSuccessorFactorSurjectivityObstruction

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_bit_fallback_double_successor_factor_budget_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackDoubleSuccessorFactorBudgetBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackDoubleSuccessorFactorBudgetBoundary

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_bit_fallback_double_successor_factor_surjectivity_obstruction_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackDoubleSuccessorFactorSurjectivityObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackDoubleSuccessorFactorSurjectivityObstruction

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_bit_fallback_one_sample_budget_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackOneSampleBudgetBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackOneSampleBudgetBoundary

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_bit_fallback_one_sample_surjectivity_obstruction_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackOneSampleSurjectivityObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackOneSampleSurjectivityObstruction

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_bit_fallback_one_sample_successor_budget_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackOneSampleSuccessorBudgetBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackOneSampleSuccessorBudgetBoundary

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_bit_fallback_one_sample_successor_surjectivity_obstruction_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackOneSampleSuccessorSurjectivityObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackOneSampleSuccessorSurjectivityObstruction

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_bit_fallback_zero_sample_budget_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackZeroSampleBudgetBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackZeroSampleBudgetBoundary

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_bit_fallback_zero_sample_surjectivity_obstruction_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackZeroSampleSurjectivityObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackZeroSampleSurjectivityObstruction

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_bit_fallback_zero_sample_exact_decoder_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackZeroSampleExactDecoderBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackZeroSampleExactDecoderBoundary

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_bit_fallback_zero_sample_exact_decoder_finite_predictor_cover_obstruction_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackZeroSampleExactDecoderFinitePredictorCoverObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackZeroSampleExactDecoderFinitePredictorCoverObstruction

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_bit_fallback_zero_sample_exact_decoder_finite_index_representative_cover_obstruction_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackZeroSampleExactDecoderFiniteIndexRepresentativeCoverObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackZeroSampleExactDecoderFiniteIndexRepresentativeCoverObstruction

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_bit_fallback_zero_sample_exact_decoder_finite_predictor_quotient_obstruction_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackZeroSampleExactDecoderFinitePredictorQuotientObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackZeroSampleExactDecoderFinitePredictorQuotientObstruction

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_bit_fallback_zero_sample_exact_decoder_exact_visible_compression_obstruction_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackZeroSampleExactDecoderExactVisibleCompressionObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackZeroSampleExactDecoderExactVisibleCompressionObstruction

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_bit_fallback_zero_sample_exact_decoder_clocked_realization_obstruction_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackZeroSampleExactDecoderClockedRealizationObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackZeroSampleExactDecoderClockedRealizationObstruction

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_bit_fallback_zero_sample_exact_decoder_clocked_payload_obstruction_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackZeroSampleExactDecoderClockedPayloadObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackZeroSampleExactDecoderClockedPayloadObstruction

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_bit_fallback_zero_sample_fallback_equivalence_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackZeroSampleFallbackEquivalence ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackZeroSampleFallbackEquivalence

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_bit_fallback_one_sample_product_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackOneSampleProductBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackOneSampleProductBoundary

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_bit_fallback_one_sample_product_surjectivity_obstruction_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackOneSampleProductSurjectivityObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackOneSampleProductSurjectivityObstruction

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_bit_fallback_two_sample_quadratic_product_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackTwoSampleQuadraticProductBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackTwoSampleQuadraticProductBoundary

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_bit_fallback_two_sample_quadratic_product_surjectivity_obstruction_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackTwoSampleQuadraticProductSurjectivityObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackTwoSampleQuadraticProductSurjectivityObstruction

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_bit_fallback_two_sample_quadratic_envelope_budget_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackTwoSampleQuadraticEnvelopeBudgetBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackTwoSampleQuadraticEnvelopeBudgetBoundary

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_bit_fallback_two_sample_quadratic_envelope_surjectivity_obstruction_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackTwoSampleQuadraticEnvelopeSurjectivityObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackTwoSampleQuadraticEnvelopeSurjectivityObstruction

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_bit_fallback_small_subsets_product_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackSmallSubsetsProductBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackSmallSubsetsProductBoundary

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_bit_fallback_small_subsets_product_surjectivity_obstruction_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackSmallSubsetsProductSurjectivityObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackSmallSubsetsProductSurjectivityObstruction

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_bit_fallback_sum_choose_product_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackSumChooseProductBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackSumChooseProductBoundary

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_bit_fallback_sum_choose_product_surjectivity_obstruction_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackSumChooseProductSurjectivityObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackSumChooseProductSurjectivityObstruction

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_bit_fallback_sum_choose_envelope_budget_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackSumChooseEnvelopeBudgetBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackSumChooseEnvelopeBudgetBoundary

theorem current_pnp_kpoly_actual_local_bounded_sample_majority_bit_fallback_sum_choose_envelope_surjectivity_obstruction_regression :
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackSumChooseEnvelopeSurjectivityObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalBoundedSampleMajorityBitFallbackSumChooseEnvelopeSurjectivityObstruction

theorem current_pnp_kpoly_surjective_actual_local_joint_recovery_regression :
    PNPKpolySubrepairClass.surjectiveActualLocalJointRecoveryBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.surjectiveActualLocalJointRecoveryBoundary

theorem current_pnp_kpoly_surjective_actual_local_recovery_visible_width_regression :
    PNPKpolySubrepairClass.surjectiveActualLocalRecoveryVisibleWidthBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.surjectiveActualLocalRecoveryVisibleWidthBoundary

theorem current_pnp_kpoly_surjective_actual_local_recovery_lightest_point_regression :
    PNPKpolySubrepairClass.surjectiveActualLocalRecoveryLightestPointBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.surjectiveActualLocalRecoveryLightestPointBoundary

theorem current_pnp_kpoly_surjective_actual_local_no_extractor_lightest_point_regression :
    PNPKpolySubrepairClass.surjectiveActualLocalNoExtractorLightestPointBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.surjectiveActualLocalNoExtractorLightestPointBoundary

theorem current_pnp_kpoly_surjective_actual_local_no_extractor_visible_width_regression :
    PNPKpolySubrepairClass.surjectiveActualLocalNoExtractorVisibleWidthBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.surjectiveActualLocalNoExtractorVisibleWidthBoundary

theorem current_pnp_kpoly_exact_visible_representative_cover_surjectivity_regression :
    PNPKpolySubrepairClass.exactVisibleRepresentativeCoverSurjectivityObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.exactVisibleRepresentativeCoverSurjectivityObstruction

theorem current_pnp_kpoly_exact_visible_predictor_quotient_surjectivity_regression :
    PNPKpolySubrepairClass.exactVisiblePredictorQuotientSurjectivityObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.exactVisiblePredictorQuotientSurjectivityObstruction

theorem current_pnp_kpoly_exact_visible_clocked_realization_surjectivity_regression :
    PNPKpolySubrepairClass.exactVisibleClockedRealizationSurjectivityObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.exactVisibleClockedRealizationSurjectivityObstruction

theorem current_pnp_kpoly_injective_finite_representative_index_cover_lower_bound_regression :
    PNPKpolySubrepairClass.injectiveFiniteRepresentativeIndexCoverLowerBound ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.injectiveFiniteRepresentativeIndexCoverLowerBound

theorem current_pnp_kpoly_injective_finite_predictor_quotient_lower_bound_regression :
    PNPKpolySubrepairClass.injectiveFinitePredictorQuotientLowerBound ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.injectiveFinitePredictorQuotientLowerBound

theorem current_pnp_kpoly_injective_finite_probe_exact_visible_compression_regression :
    PNPKpolySubrepairClass.injectiveFiniteProbeExactVisibleCompressionObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.injectiveFiniteProbeExactVisibleCompressionObstruction

theorem current_pnp_kpoly_injective_finite_probe_clocked_realization_regression :
    PNPKpolySubrepairClass.injectiveFiniteProbeClockedRealizationObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.injectiveFiniteProbeClockedRealizationObstruction

theorem current_pnp_kpoly_section_backed_injective_finite_probe_pullback_lower_bound_regression :
    PNPKpolySubrepairClass.sectionBackedInjectiveFiniteProbePullbackLowerBound ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.sectionBackedInjectiveFiniteProbePullbackLowerBound

theorem current_pnp_kpoly_section_backed_injective_finite_probe_pullback_obstruction_regression :
    PNPKpolySubrepairClass.sectionBackedInjectiveFiniteProbePullbackObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.sectionBackedInjectiveFiniteProbePullbackObstruction

theorem current_pnp_kpoly_section_backed_injective_finite_representative_index_cover_lower_bound_regression :
    PNPKpolySubrepairClass.sectionBackedInjectiveFiniteRepresentativeIndexCoverLowerBound ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.sectionBackedInjectiveFiniteRepresentativeIndexCoverLowerBound

theorem current_pnp_kpoly_section_backed_injective_finite_representative_index_cover_obstruction_regression :
    PNPKpolySubrepairClass.sectionBackedInjectiveFiniteRepresentativeIndexCoverObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.sectionBackedInjectiveFiniteRepresentativeIndexCoverObstruction

theorem current_pnp_kpoly_section_backed_injective_finite_predictor_quotient_lower_bound_regression :
    PNPKpolySubrepairClass.sectionBackedInjectiveFinitePredictorQuotientLowerBound ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.sectionBackedInjectiveFinitePredictorQuotientLowerBound

theorem current_pnp_kpoly_section_backed_injective_finite_predictor_quotient_obstruction_regression :
    PNPKpolySubrepairClass.sectionBackedInjectiveFinitePredictorQuotientObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.sectionBackedInjectiveFinitePredictorQuotientObstruction

theorem current_pnp_kpoly_finite_representative_index_cover_equivalence_regression :
    PNPKpolySubrepairClass.finiteRepresentativeIndexCoverEquivalence ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.finiteRepresentativeIndexCoverEquivalence

theorem current_pnp_kpoly_exact_visible_compression_target_predictor_cover_equivalence_regression :
    PNPKpolySubrepairClass.exactVisibleCompressionTargetPredictorCoverEquivalence ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.exactVisibleCompressionTargetPredictorCoverEquivalence

theorem current_pnp_kpoly_clocked_exact_visible_realization_predictor_cover_equivalence_regression :
    PNPKpolySubrepairClass.clockedExactVisibleRealizationPredictorCoverEquivalence ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.clockedExactVisibleRealizationPredictorCoverEquivalence

theorem current_pnp_kpoly_clocked_finite_learning_payload_predictor_cover_equivalence_regression :
    PNPKpolySubrepairClass.clockedFiniteLearningPayloadPredictorCoverEquivalence ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.clockedFiniteLearningPayloadPredictorCoverEquivalence

theorem current_pnp_kpoly_clocked_finite_learning_payload_exact_visible_compression_equivalence_regression :
    PNPKpolySubrepairClass.clockedFiniteLearningPayloadExactVisibleCompressionEquivalence ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.clockedFiniteLearningPayloadExactVisibleCompressionEquivalence

theorem current_pnp_kpoly_exact_visible_compression_target_predictor_quotient_equivalence_regression :
    PNPKpolySubrepairClass.exactVisibleCompressionTargetPredictorQuotientEquivalence ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.exactVisibleCompressionTargetPredictorQuotientEquivalence

theorem current_pnp_kpoly_clocked_exact_visible_realization_predictor_quotient_equivalence_regression :
    PNPKpolySubrepairClass.clockedExactVisibleRealizationPredictorQuotientEquivalence ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.clockedExactVisibleRealizationPredictorQuotientEquivalence

theorem current_pnp_kpoly_exact_visible_compression_target_representative_index_cover_equivalence_regression :
    PNPKpolySubrepairClass.exactVisibleCompressionTargetRepresentativeIndexCoverEquivalence ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.exactVisibleCompressionTargetRepresentativeIndexCoverEquivalence

theorem current_pnp_kpoly_clocked_exact_visible_realization_representative_index_cover_equivalence_regression :
    PNPKpolySubrepairClass.clockedExactVisibleRealizationRepresentativeIndexCoverEquivalence ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.clockedExactVisibleRealizationRepresentativeIndexCoverEquivalence

theorem current_pnp_kpoly_not_clocked_exact_visible_realization_representative_index_cover_equivalence_regression :
    PNPKpolySubrepairClass.notClockedExactVisibleRealizationRepresentativeIndexCoverEquivalence ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.notClockedExactVisibleRealizationRepresentativeIndexCoverEquivalence

theorem current_pnp_kpoly_not_clocked_exact_visible_realization_predictor_quotient_equivalence_regression :
    PNPKpolySubrepairClass.notClockedExactVisibleRealizationPredictorQuotientEquivalence ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.notClockedExactVisibleRealizationPredictorQuotientEquivalence

theorem current_pnp_kpoly_finite_image_cover_budget_weakening_regression :
    PNPKpolySubrepairClass.finiteImageCoverBudgetWeakening ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.finiteImageCoverBudgetWeakening

theorem current_pnp_kpoly_finite_predictor_cover_budget_weakening_regression :
    PNPKpolySubrepairClass.finitePredictorCoverBudgetWeakeningBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.finitePredictorCoverBudgetWeakeningBoundary

theorem current_pnp_kpoly_finite_representative_index_cover_budget_weakening_regression :
    PNPKpolySubrepairClass.finiteRepresentativeIndexCoverBudgetWeakeningBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.finiteRepresentativeIndexCoverBudgetWeakeningBoundary

theorem current_pnp_kpoly_finite_predictor_quotient_budget_weakening_regression :
    PNPKpolySubrepairClass.finitePredictorQuotientBudgetWeakeningBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.finitePredictorQuotientBudgetWeakeningBoundary

theorem current_pnp_kpoly_finite_image_cover_factor_transport_regression :
    PNPKpolySubrepairClass.finiteImageCoverFactorTransport ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.finiteImageCoverFactorTransport

theorem current_pnp_kpoly_finite_predictor_cover_factor_transport_regression :
    PNPKpolySubrepairClass.finitePredictorCoverFactorTransportBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.finitePredictorCoverFactorTransportBoundary

theorem current_pnp_kpoly_finite_representative_index_cover_factor_transport_regression :
    PNPKpolySubrepairClass.finiteRepresentativeIndexCoverFactorTransportBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.finiteRepresentativeIndexCoverFactorTransportBoundary

theorem current_pnp_kpoly_finite_predictor_quotient_factor_transport_regression :
    PNPKpolySubrepairClass.finitePredictorQuotientFactorTransportBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.finitePredictorQuotientFactorTransportBoundary

theorem current_pnp_kpoly_section_backed_finite_predictor_cover_surjective_obstruction_regression :
    PNPKpolySubrepairClass.sectionBackedFinitePredictorCoverSurjectiveObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.sectionBackedFinitePredictorCoverSurjectiveObstruction

theorem current_pnp_kpoly_section_backed_finite_representative_index_cover_surjective_obstruction_regression :
    PNPKpolySubrepairClass.sectionBackedFiniteRepresentativeIndexCoverSurjectiveObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.sectionBackedFiniteRepresentativeIndexCoverSurjectiveObstruction

theorem current_pnp_kpoly_section_backed_finite_predictor_quotient_surjective_obstruction_regression :
    PNPKpolySubrepairClass.sectionBackedFinitePredictorQuotientSurjectiveObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.sectionBackedFinitePredictorQuotientSurjectiveObstruction

theorem current_pnp_kpoly_section_backed_finite_predictor_cover_surjective_lower_bound_regression :
    PNPKpolySubrepairClass.sectionBackedFinitePredictorCoverSurjectiveLowerBound ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.sectionBackedFinitePredictorCoverSurjectiveLowerBound

theorem current_pnp_kpoly_section_backed_finite_representative_index_cover_surjective_lower_bound_regression :
    PNPKpolySubrepairClass.sectionBackedFiniteRepresentativeIndexCoverSurjectiveLowerBound ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.sectionBackedFiniteRepresentativeIndexCoverSurjectiveLowerBound

theorem current_pnp_kpoly_section_backed_finite_predictor_quotient_surjective_lower_bound_regression :
    PNPKpolySubrepairClass.sectionBackedFinitePredictorQuotientSurjectiveLowerBound ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.sectionBackedFinitePredictorQuotientSurjectiveLowerBound

theorem current_pnp_kpoly_surjective_finite_predictor_cover_lower_bound_regression :
    PNPKpolySubrepairClass.surjectiveFinitePredictorCoverLowerBound ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.surjectiveFinitePredictorCoverLowerBound

theorem current_pnp_kpoly_surjective_finite_representative_index_cover_lower_bound_regression :
    PNPKpolySubrepairClass.surjectiveFiniteRepresentativeIndexCoverLowerBound ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.surjectiveFiniteRepresentativeIndexCoverLowerBound

theorem current_pnp_kpoly_surjective_finite_predictor_quotient_lower_bound_regression :
    PNPKpolySubrepairClass.surjectiveFinitePredictorQuotientLowerBound ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.surjectiveFinitePredictorQuotientLowerBound

theorem current_pnp_kpoly_finite_image_reduced_ab_pullback_obstruction_regression :
    PNPKpolySubrepairClass.finiteImageReducedABPullbackObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.finiteImageReducedABPullbackObstruction

theorem current_pnp_kpoly_finite_image_reduced_ab_injective_probe_pullback_obstruction_regression :
    PNPKpolySubrepairClass.finiteImageReducedABInjectiveProbePullbackObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.finiteImageReducedABInjectiveProbePullbackObstruction

theorem current_pnp_kpoly_finite_quotient_reduced_ab_pullback_obstruction_regression :
    PNPKpolySubrepairClass.finiteQuotientReducedABPullbackObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.finiteQuotientReducedABPullbackObstruction

theorem current_pnp_kpoly_exact_visible_clocked_finite_learning_payload_surjectivity_regression :
    PNPKpolySubrepairClass.exactVisibleClockedFiniteLearningPayloadSurjectivityObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.exactVisibleClockedFiniteLearningPayloadSurjectivityObstruction

theorem current_pnp_kpoly_injective_finite_probe_clocked_finite_learning_payload_regression :
    PNPKpolySubrepairClass.injectiveFiniteProbeClockedFiniteLearningPayloadObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.injectiveFiniteProbeClockedFiniteLearningPayloadObstruction

theorem current_pnp_kpoly_exact_visible_clocked_finite_learning_payload_surjectivity_lower_bound_regression :
    PNPKpolySubrepairClass.exactVisibleClockedFiniteLearningPayloadSurjectivityLowerBound ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.exactVisibleClockedFiniteLearningPayloadSurjectivityLowerBound

theorem current_pnp_kpoly_injective_finite_probe_clocked_finite_learning_payload_lower_bound_regression :
    PNPKpolySubrepairClass.injectiveFiniteProbeClockedFiniteLearningPayloadLowerBound ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.injectiveFiniteProbeClockedFiniteLearningPayloadLowerBound

theorem current_pnp_kpoly_section_backed_clocked_finite_learning_payload_surjective_lower_bound_regression :
    PNPKpolySubrepairClass.sectionBackedClockedFiniteLearningPayloadSurjectiveLowerBound ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.sectionBackedClockedFiniteLearningPayloadSurjectiveLowerBound

theorem current_pnp_kpoly_section_backed_clocked_finite_learning_payload_surjective_obstruction_regression :
    PNPKpolySubrepairClass.sectionBackedClockedFiniteLearningPayloadSurjectiveObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.sectionBackedClockedFiniteLearningPayloadSurjectiveObstruction

theorem current_pnp_kpoly_section_backed_injective_finite_probe_clocked_finite_learning_payload_lower_bound_regression :
    PNPKpolySubrepairClass.sectionBackedInjectiveFiniteProbeClockedFiniteLearningPayloadLowerBound ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.sectionBackedInjectiveFiniteProbeClockedFiniteLearningPayloadLowerBound

theorem current_pnp_kpoly_section_backed_injective_finite_probe_clocked_finite_learning_payload_obstruction_regression :
    PNPKpolySubrepairClass.sectionBackedInjectiveFiniteProbeClockedFiniteLearningPayloadObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.sectionBackedInjectiveFiniteProbeClockedFiniteLearningPayloadObstruction

theorem current_pnp_kpoly_exact_zab_bad_code_large_region_disagreement_regression :
    PNPKpolySubrepairClass.exactZABBadCodeLargeRegionDisagreementBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.exactZABBadCodeLargeRegionDisagreementBoundary

theorem current_pnp_kpoly_actual_local_zab_decision_list_visible_card_gap_regression :
    PNPKpolySubrepairClass.actualLocalZABDecisionListVisibleCardGapLowerBound ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalZABDecisionListVisibleCardGapLowerBound

theorem current_pnp_kpoly_actual_local_zab_decision_list_bitvec_truth_table_gap_regression :
    PNPKpolySubrepairClass.actualLocalZABDecisionListBitVecTruthTableGapObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalZABDecisionListBitVecTruthTableGapObstruction

theorem current_pnp_kpoly_surjective_actual_local_sparse_threshold_erm_visible_budget_regression :
    PNPKpolySubrepairClass.surjectiveActualLocalSparseThresholdERMVisibleBudgetBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.surjectiveActualLocalSparseThresholdERMVisibleBudgetBoundary

theorem current_pnp_kpoly_surjective_actual_local_sparse_threshold_erm_visible_width_regression :
    PNPKpolySubrepairClass.surjectiveActualLocalSparseThresholdERMVisibleWidthBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.surjectiveActualLocalSparseThresholdERMVisibleWidthBoundary

theorem current_pnp_kpoly_surjective_actual_local_no_extractor_sparse_threshold_erm_visible_width_regression :
    PNPKpolySubrepairClass.surjectiveActualLocalNoExtractorSparseThresholdERMVisibleWidthBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.surjectiveActualLocalNoExtractorSparseThresholdERMVisibleWidthBoundary

theorem current_pnp_kpoly_surjective_actual_local_recovery_payload_predictor_card_regression :
    PNPKpolySubrepairClass.surjectiveActualLocalRecoveryPayloadPredictorCardObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.surjectiveActualLocalRecoveryPayloadPredictorCardObstruction

theorem current_pnp_kpoly_surjective_actual_local_no_extractor_recovery_payload_predictor_card_regression :
    PNPKpolySubrepairClass.surjectiveActualLocalNoExtractorRecoveryPayloadPredictorCardObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.surjectiveActualLocalNoExtractorRecoveryPayloadPredictorCardObstruction

theorem current_pnp_kpoly_actual_local_recovery_payload_injective_probe_card_regression :
    PNPKpolySubrepairClass.actualLocalRecoveryPayloadInjectiveProbeCardObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalRecoveryPayloadInjectiveProbeCardObstruction

theorem current_pnp_kpoly_actual_local_no_extractor_recovery_payload_injective_probe_card_regression :
    PNPKpolySubrepairClass.actualLocalNoExtractorRecoveryPayloadInjectiveProbeCardObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalNoExtractorRecoveryPayloadInjectiveProbeCardObstruction

theorem current_pnp_kpoly_surjective_actual_local_recovery_uniform_cardinality_threshold_regression :
    PNPKpolySubrepairClass.surjectiveActualLocalRecoveryUniformCardinalityThresholdBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.surjectiveActualLocalRecoveryUniformCardinalityThresholdBoundary

theorem current_pnp_kpoly_full_rule_actual_local_recovery_bitvec_cardinality_threshold_regression :
    PNPKpolySubrepairClass.fullRuleActualLocalRecoveryBitVecCardinalityThresholdBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.fullRuleActualLocalRecoveryBitVecCardinalityThresholdBoundary

theorem current_pnp_kpoly_full_rule_actual_local_no_extractor_recovery_bitvec_cardinality_threshold_regression :
    PNPKpolySubrepairClass.fullRuleActualLocalNoExtractorRecoveryBitVecCardinalityThresholdObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.fullRuleActualLocalNoExtractorRecoveryBitVecCardinalityThresholdObstruction

theorem current_pnp_kpoly_full_rule_actual_local_recovery_threshold_width_regression :
    PNPKpolySubrepairClass.fullRuleActualLocalRecoveryThresholdWidthBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.fullRuleActualLocalRecoveryThresholdWidthBoundary

theorem current_pnp_kpoly_full_rule_actual_local_no_extractor_recovery_threshold_width_regression :
    PNPKpolySubrepairClass.fullRuleActualLocalNoExtractorRecoveryThresholdWidthObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.fullRuleActualLocalNoExtractorRecoveryThresholdWidthObstruction

theorem current_pnp_kpoly_bounded_sample_plugin_majority_actual_local_recovery_threshold_width_regression :
    PNPKpolySubrepairClass.boundedSamplePluginMajorityActualLocalRecoveryThresholdWidthBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.boundedSamplePluginMajorityActualLocalRecoveryThresholdWidthBoundary

theorem current_pnp_kpoly_bounded_sample_plugin_majority_actual_local_no_extractor_recovery_threshold_width_regression :
    PNPKpolySubrepairClass.boundedSamplePluginMajorityActualLocalNoExtractorRecoveryThresholdWidthObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.boundedSamplePluginMajorityActualLocalNoExtractorRecoveryThresholdWidthObstruction

theorem current_pnp_kpoly_full_rule_actual_local_recovery_threshold_visible_budget_regression :
    PNPKpolySubrepairClass.fullRuleActualLocalRecoveryThresholdVisibleBudgetBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.fullRuleActualLocalRecoveryThresholdVisibleBudgetBoundary

theorem current_pnp_kpoly_full_rule_actual_local_no_extractor_recovery_threshold_visible_budget_regression :
    PNPKpolySubrepairClass.fullRuleActualLocalNoExtractorRecoveryThresholdVisibleBudgetObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.fullRuleActualLocalNoExtractorRecoveryThresholdVisibleBudgetObstruction

theorem current_pnp_kpoly_bounded_sample_plugin_majority_actual_local_recovery_threshold_visible_budget_regression :
    PNPKpolySubrepairClass.boundedSamplePluginMajorityActualLocalRecoveryThresholdVisibleBudgetBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.boundedSamplePluginMajorityActualLocalRecoveryThresholdVisibleBudgetBoundary

theorem current_pnp_kpoly_bounded_sample_plugin_majority_actual_local_no_extractor_recovery_threshold_visible_budget_regression :
    PNPKpolySubrepairClass.boundedSamplePluginMajorityActualLocalNoExtractorRecoveryThresholdVisibleBudgetObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.boundedSamplePluginMajorityActualLocalNoExtractorRecoveryThresholdVisibleBudgetObstruction

theorem current_pnp_kpoly_surjective_actual_local_recovery_proper_region_mass_regression :
    PNPKpolySubrepairClass.surjectiveActualLocalRecoveryProperRegionMassBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.surjectiveActualLocalRecoveryProperRegionMassBoundary

theorem current_pnp_kpoly_surjective_actual_local_no_extractor_recovery_proper_region_mass_regression :
    PNPKpolySubrepairClass.surjectiveActualLocalNoExtractorProperRegionMassBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.surjectiveActualLocalNoExtractorProperRegionMassBoundary

theorem current_pnp_kpoly_actual_local_recovery_heavy_region_trace_card_regression :
    PNPKpolySubrepairClass.actualLocalRecoveryHeavyRegionTraceCardBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalRecoveryHeavyRegionTraceCardBoundary

theorem current_pnp_kpoly_actual_local_no_extractor_recovery_heavy_region_trace_card_regression :
    PNPKpolySubrepairClass.actualLocalNoExtractorRecoveryHeavyRegionTraceCardObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalNoExtractorRecoveryHeavyRegionTraceCardObstruction

theorem current_pnp_kpoly_actual_local_injective_recovery_uniform_cardinality_threshold_regression :
    PNPKpolySubrepairClass.actualLocalInjectiveRecoveryUniformCardinalityThresholdBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalInjectiveRecoveryUniformCardinalityThresholdBoundary

theorem current_pnp_kpoly_actual_local_injective_recovery_bitvec_cardinality_threshold_regression :
    PNPKpolySubrepairClass.actualLocalInjectiveRecoveryBitVecCardinalityThresholdBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalInjectiveRecoveryBitVecCardinalityThresholdBoundary

theorem current_pnp_kpoly_actual_local_no_injective_extractor_recovery_bitvec_cardinality_threshold_regression :
    PNPKpolySubrepairClass.actualLocalNoInjectiveExtractorRecoveryBitVecCardinalityThresholdObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualLocalNoInjectiveExtractorRecoveryBitVecCardinalityThresholdObstruction

def fin3ToBitVec0ActualSparseRecoveryPayloadBridge : Fin 3 → BitVec 0 := fun _ => zeroVec

noncomputable def fin3ZeroVisiblePointActualSparseRecoveryPayloadBridge :
    ExactVisiblePostSwitchSurface (Fin 3) 0 :=
  ⟨0, zeroVec, zeroVec⟩

noncomputable def fin3OneVisiblePointActualSparseRecoveryPayloadBridge :
    ExactVisiblePostSwitchSurface (Fin 3) 0 :=
  ⟨1, zeroVec, zeroVec⟩

noncomputable def fin3TwoVisiblePointActualSparseRecoveryPayloadBridge :
    ExactVisiblePostSwitchSurface (Fin 3) 0 :=
  ⟨2, zeroVec, zeroVec⟩

noncomputable def fin3PureMeasureActualSparseRecoveryPayloadBridge :
    PMF (ExactVisiblePostSwitchSurface (Fin 3) 0) :=
  PMF.pure fin3ZeroVisiblePointActualSparseRecoveryPayloadBridge

theorem fullRuleActualSwitchedLocalInterface_lt_predictorCard_fin3k0r0_payload_bridge_regression :
    2 ^ (2 * allAffinePointBlockFeatureCount (0 + (0 + 0))) <
      2 ^ Fintype.card (ExactVisiblePostSwitchSurface (Fin 3) 0) := by
  rw [card_exactVisiblePostSwitchSurface (Z := Fin 3) (k := 0)]
  norm_num [allAffinePointBlockFeatureCount_eq]

def fin5ProbeFamilyActualSparseRecoveryPayloadBridge
    (p : Fin 5) :
    ExactVisiblePostSwitchSurface (Fin 3) 0 → Bool :=
  match p.1 with
  | 0 => fun _ => false
  | 1 => fun u => decide (u.z = 0)
  | 2 => fun u => decide (u.z = 1)
  | 3 => fun u => decide (u.z = 2)
  | _ => fun _ => true

theorem fin5ProbeFamilyActualSparseRecoveryPayloadBridge_injective :
    Function.Injective fin5ProbeFamilyActualSparseRecoveryPayloadBridge := by
  decide

theorem fin5ProbeFamilyActualSparseRecoveryPayloadBridge_lt_card_regression :
    2 ^ (2 * allAffinePointBlockFeatureCount (0 + (0 + 0))) < Fintype.card (Fin 5) := by
  norm_num [allAffinePointBlockFeatureCount_eq]

def fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayloadBridge :
    ActualSwitchedLocalInterface
      (Fin 3)
      0
      (Fin 5)
      (ExactVisiblePostSwitchSurface (Fin 3) 0) where
  zOf := fun u => u.z
  aOf := fun _ u => u.a
  bOf := fun u => u.b
  localRule := fin5ProbeFamilyActualSparseRecoveryPayloadBridge
  output := fun p u => fin5ProbeFamilyActualSparseRecoveryPayloadBridge p u
  output_eq_local := by
    intro p u
    rfl

theorem fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayloadBridge_injective_predict :
    Function.Injective
      fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayloadBridge.predictorFamily.predict := by
  exact fin5ProbeFamilyActualSparseRecoveryPayloadBridge_injective

def exactVisiblePostSwitchSurfaceFin30EquivActualSparseRecoveryHeavyRegionTraceBridge :
    ExactVisiblePostSwitchSurface (Fin 3) 0 ≃ Fin 3 where
  toFun u := u.z
  invFun z := ⟨z, zeroVec, zeroVec⟩
  left_inv := by
    intro u
    cases u with
    | mk z a b =>
        have ha : (zeroVec : BitVec 0) = a := Subsingleton.elim _ _
        have hb : (zeroVec : BitVec 0) = b := Subsingleton.elim _ _
        cases ha
        cases hb
        rfl
  right_inv := by
    intro z
    rfl

noncomputable def fin3ZeroOneHalfMeasureActualSparseRecoveryHeavyRegionTraceBridge :
    PMF (ExactVisiblePostSwitchSurface (Fin 3) 0) :=
  PMF.ofFintype
    (fun u => if u.z = 2 then 0 else (2 : ℝ≥0∞)⁻¹)
    (by
      classical
      have hsum :
          ∑ a : ExactVisiblePostSwitchSurface (Fin 3) 0,
              (if a.z = 2 then 0 else (2 : ℝ≥0∞)⁻¹)
            =
          ∑ b : Fin 3, (if b = 2 then 0 else (2 : ℝ≥0∞)⁻¹) := by
        simpa using
          (Fintype.sum_equiv
            exactVisiblePostSwitchSurfaceFin30EquivActualSparseRecoveryHeavyRegionTraceBridge
            (fun u : ExactVisiblePostSwitchSurface (Fin 3) 0 =>
              if u.z = 2 then 0 else (2 : ℝ≥0∞)⁻¹)
            (fun b : Fin 3 => if b = 2 then 0 else (2 : ℝ≥0∞)⁻¹)
            (by
              intro b
              rfl))
      calc
        ∑ a : ExactVisiblePostSwitchSurface (Fin 3) 0,
            (if a.z = 2 then 0 else (2 : ℝ≥0∞)⁻¹)
          =
            ∑ b : Fin 3, (if b = 2 then 0 else (2 : ℝ≥0∞)⁻¹) := hsum
        _ = 1 := by
          rw [Fin.sum_univ_three]
          simpa [two_mul] using ENNReal.inv_two_add_inv_two)

noncomputable def fin3ZeroOneRegionActualSparseRecoveryHeavyRegionTraceBridge :
    Finset (ExactVisiblePostSwitchSurface (Fin 3) 0) :=
  by
    classical
    exact
      insert
        fin3ZeroVisiblePointActualSparseRecoveryPayloadBridge
        {fin3OneVisiblePointActualSparseRecoveryPayloadBridge}

theorem fin3ZeroOneRegionActualSparseRecoveryHeavyRegionTraceBridge_card :
    fin3ZeroOneRegionActualSparseRecoveryHeavyRegionTraceBridge.card = 2 := by
  simp [fin3ZeroOneRegionActualSparseRecoveryHeavyRegionTraceBridge,
    fin3ZeroVisiblePointActualSparseRecoveryPayloadBridge,
    fin3OneVisiblePointActualSparseRecoveryPayloadBridge]

theorem fin3ZeroOneRegionActualSparseRecoveryHeavyRegionTraceBridge_mass_eq_one :
    fin3ZeroOneRegionActualSparseRecoveryHeavyRegionTraceBridge.sum
        (fun x => fin3ZeroOneHalfMeasureActualSparseRecoveryHeavyRegionTraceBridge x) = 1 := by
  calc
    fin3ZeroOneRegionActualSparseRecoveryHeavyRegionTraceBridge.sum
        (fun x => fin3ZeroOneHalfMeasureActualSparseRecoveryHeavyRegionTraceBridge x)
      = (2 : ℝ≥0∞)⁻¹ + (2 : ℝ≥0∞)⁻¹ := by
          simp [fin3ZeroOneRegionActualSparseRecoveryHeavyRegionTraceBridge,
            fin3ZeroOneHalfMeasureActualSparseRecoveryHeavyRegionTraceBridge,
            fin3ZeroVisiblePointActualSparseRecoveryPayloadBridge,
            fin3OneVisiblePointActualSparseRecoveryPayloadBridge]
    _ = 1 := by
      simpa [two_mul] using ENNReal.inv_two_add_inv_two

private noncomputable def fin3ThreeQuartersActualSparseRecoveryHeavyRegionTraceBridge :
    ℝ≥0∞ :=
  (3 : ℝ≥0∞) / 4

private theorem fin3ThreeQuartersActualSparseRecoveryHeavyRegionTraceBridge_lt_one :
    fin3ThreeQuartersActualSparseRecoveryHeavyRegionTraceBridge < 1 := by
  have h₁ :
      fin3ThreeQuartersActualSparseRecoveryHeavyRegionTraceBridge = (3 : ℝ≥0∞) / 4 := by
    rfl
  have h₂ : (1 : ℝ≥0∞) = (4 : ℝ≥0∞) / 4 := by
    rw [ENNReal.div_self (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by simp)]
  rw [h₁, h₂]
  exact ENNReal.div_lt_div_right (by norm_num) (by simp) (by norm_num)

private theorem fin3ThreeQuartersActualSparseRecoveryHeavyRegionTraceBridge_lt_regionMass :
    fin3ThreeQuartersActualSparseRecoveryHeavyRegionTraceBridge <
      fin3ZeroOneRegionActualSparseRecoveryHeavyRegionTraceBridge.sum
        (fun x => fin3ZeroOneHalfMeasureActualSparseRecoveryHeavyRegionTraceBridge x) := by
  rw [fin3ZeroOneRegionActualSparseRecoveryHeavyRegionTraceBridge_mass_eq_one]
  exact fin3ThreeQuartersActualSparseRecoveryHeavyRegionTraceBridge_lt_one

def idBitVec1ActualSparseRecoveryCardinalityBridge : BitVec 1 → BitVec 1 := fun x => x

local instance exactVisiblePostSwitchSurfaceBitVec1k1NonemptyBridge :
    Nonempty (ExactVisiblePostSwitchSurface (BitVec 1) 1) :=
  ⟨⟨zeroVec, zeroVec, zeroVec⟩⟩

noncomputable def bitVec1k1UniformMeasureActualSparseRecoveryCardinalityBridge :
    PMF (ExactVisiblePostSwitchSurface (BitVec 1) 1) :=
  PMF.uniformOfFintype _

def constFalseActualSwitchedLocalInterfaceBitVec1k1ActualSparseRecoveryInjectiveBridge :
    ActualSwitchedLocalInterface
      (BitVec 1)
      1
      Unit
      (ExactVisiblePostSwitchSurface (BitVec 1) 1) where
  zOf := fun u => u.z
  aOf := fun _ u => u.a
  bOf := fun u => u.b
  localRule := fun _ _ => false
  output := fun _ _ => false
  output_eq_local := by
    intro _ _
    rfl

theorem constFalseActualSwitchedLocalInterfaceBitVec1k1ActualSparseRecoveryInjectiveBridge_not_surjective :
    ¬ Function.Surjective
        constFalseActualSwitchedLocalInterfaceBitVec1k1ActualSparseRecoveryInjectiveBridge.predictorFamily.predict := by
  intro hsurj
  rcases hsurj (fun _ => true) with ⟨u, htrue⟩
  cases u
  have h := congrFun htrue ⟨zeroVec, zeroVec, zeroVec⟩
  simp [constFalseActualSwitchedLocalInterfaceBitVec1k1ActualSparseRecoveryInjectiveBridge] at h

private theorem three_quarters_lt_seven_eighths_actualSparseRecoveryInjectiveBridge :
    (3 : ℝ≥0∞) / 4 < (7 : ℝ≥0∞) / 8 := by
  have h₁ : (3 : ℝ≥0∞) / 4 = 6 / 8 := by
    refine (ENNReal.div_eq_div_iff (by norm_num) (by simp) (by norm_num) (by simp)).2 ?_
    norm_num
  rw [h₁]
  exact ENNReal.div_lt_div_right (by norm_num) (by simp) (by norm_num)

noncomputable def bitVec1k0ZeroVisiblePointActualSparseRecoveryRegionBridge :
    ExactVisiblePostSwitchSurface (BitVec 1) 0 :=
  ⟨0, zeroVec, zeroVec⟩

noncomputable def bitVec1k0OneVisiblePointActualSparseRecoveryRegionBridge :
    ExactVisiblePostSwitchSurface (BitVec 1) 0 :=
  ⟨1, zeroVec, zeroVec⟩

noncomputable def bitVec1k0PureMeasureActualSparseRecoveryRegionBridge :
    PMF (ExactVisiblePostSwitchSurface (BitVec 1) 0) :=
  PMF.pure bitVec1k0ZeroVisiblePointActualSparseRecoveryRegionBridge

noncomputable def bitVec1k0HeavyRegionActualSparseRecoveryRegionBridge :
    Finset (ExactVisiblePostSwitchSurface (BitVec 1) 0) :=
  {bitVec1k0ZeroVisiblePointActualSparseRecoveryRegionBridge}

noncomputable local instance exactVisiblePostSwitchSurfaceBitVec1k0DecidableEqBridge :
    DecidableEq (ExactVisiblePostSwitchSurface (BitVec 1) 0) :=
  Classical.decEq _

private theorem bitVec1k0HeavyRegionActualSparseRecoveryRegionBridge_filter_card :
    ({x ∈ bitVec1k0HeavyRegionActualSparseRecoveryRegionBridge
        | x = bitVec1k0ZeroVisiblePointActualSparseRecoveryRegionBridge}).card = 1 := by
  apply Finset.card_eq_one.mpr
  refine ⟨bitVec1k0ZeroVisiblePointActualSparseRecoveryRegionBridge, ?_⟩
  simp [bitVec1k0HeavyRegionActualSparseRecoveryRegionBridge,
    bitVec1k0ZeroVisiblePointActualSparseRecoveryRegionBridge]

def zeroBitVec1ToBitVec0ActualSparseRecoveryThresholdVisibleBudgetBridge :
    BitVec 1 → BitVec 0 := fun _ => zeroVec

def zeroBitVec3ToBitVec1ActualSparseRecoveryThresholdVisibleBudgetBridge :
    BitVec 3 → BitVec 1 := fun _ => zeroVec

local instance exactVisiblePostSwitchSurfaceBitVec3k0NonemptyThresholdVisibleBudgetBridge :
    Nonempty (ExactVisiblePostSwitchSurface (BitVec 3) 0) :=
  ⟨⟨zeroVec, zeroVec, zeroVec⟩⟩

noncomputable def bitVec3k0UniformMeasureActualSparseRecoveryThresholdVisibleBudgetBridge :
    PMF (ExactVisiblePostSwitchSurface (BitVec 3) 0) :=
  PMF.uniformOfFintype _

private theorem half_lt_one_sub_pow_inv_of_two_lt_pow_cruxSynthesisRegression {p : ℕ}
    (hp : (2 : ℝ≥0∞) < 2 ^ p) :
    ((1 : ℝ≥0∞) / 2) < 1 - (2 ^ p : ℝ≥0∞)⁻¹ := by
  have hhalf : ((1 : ℝ≥0∞) / 2) = 1 - (2 : ℝ≥0∞)⁻¹ := by
    calc
      ((1 : ℝ≥0∞) / 2) = (2 : ℝ≥0∞)⁻¹ := by simp
      _ = 1 - (2 : ℝ≥0∞)⁻¹ := ENNReal.one_sub_inv_two.symm
  rw [hhalf]
  refine (ENNReal.sub_lt_iff_lt_left ?_ ?_).2 ?_
  · simp
  · simp
  have hinv_lt : (2 ^ p : ℝ≥0∞)⁻¹ < (2 : ℝ≥0∞)⁻¹ := by
    simpa using ENNReal.inv_lt_inv' hp
  have hpow_ge_one : (1 : ℝ≥0∞) ≤ 2 ^ p := by
    exact le_of_lt <| lt_trans (by norm_num : (1 : ℝ≥0∞) < 2) hp
  have hinv_le_one : (2 ^ p : ℝ≥0∞)⁻¹ ≤ 1 := by
    simpa using ENNReal.inv_le_inv' hpow_ge_one
  calc
    1 = (1 - (2 ^ p : ℝ≥0∞)⁻¹) + (2 ^ p : ℝ≥0∞)⁻¹ := by
      symm
      exact tsub_add_cancel_of_le hinv_le_one
    _ < (1 - (2 ^ p : ℝ≥0∞)⁻¹) + (2 : ℝ≥0∞)⁻¹ := by
      exact ENNReal.add_lt_add_left (by simp) hinv_lt
    _ = (2 : ℝ≥0∞)⁻¹ + (1 - (2 ^ p : ℝ≥0∞)⁻¹) := by
      rw [add_comm]

theorem kpoly_anchor_full_rule_actual_local_zab_data_forces_three_extractor_bits_regression
    {r : ℕ}
    {zfeat : BitVec 2 → BitVec r}
    (h :
      ActualSwitchedLocalInterface.ZABDecisionListData
        (fullRuleActualSwitchedLocalInterface (BitVec 2) 0) zfeat) :
    3 ≤ r := by
  exact
    kpolyCoverage_anchor_actualSwitchedLocal_zabDecisionList_visibleCardGapLowerBound_of_surjective_predict
      (T := fullRuleActualSwitchedLocalInterface (BitVec 2) 0)
      (zfeat := zfeat)
      h
      (fullRuleActualSwitchedLocalInterface_surjective (BitVec 2) 0)

theorem kpoly_anchor_full_rule_actual_local_not_zab_data_below_truth_table_gap_regression :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.ZABDecisionListData
          (fullRuleActualSwitchedLocalInterface (BitVec 2) 0)
          (fun z : BitVec 2 => z)) := by
  exact
    kpolyCoverage_anchor_fullRuleActualSwitchedLocal_not_nonempty_zabDecisionListData_of_extractorWidth_lt_truthTableGap
      (n := 2) (k := 0) (r := 2) (fun z : BitVec 2 => z) (by norm_num)

theorem kpoly_anchor_full_rule_actual_local_shared_sparse_threshold_erm_data_forces_positive_extractor_width_regression
    {r : ℕ}
    {zfeat : BitVec 2 → BitVec r}
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMData
          (fullRuleActualSwitchedLocalInterface (BitVec 2) 0)
          zfeat)) :
    1 ≤ r := by
  have hwidth :
      2 ≤ 2 * r + 2 * 0 + 1 := by
    exact
      kpolyCoverage_anchor_surjectiveActualLocal_visibleWidth_le_two_mul_extractorWidth_add_two_mul_k_succ_of_nonempty_sharedExactZABSparseThresholdERMData
        (k := 0) (r := r)
        (T := fullRuleActualSwitchedLocalInterface (BitVec 2) 0)
        (fullRuleActualSwitchedLocalInterface_surjective (BitVec 2) 0)
        zfeat
        h
  omega

theorem kpoly_anchor_full_rule_actual_local_no_extractor_shared_sparse_threshold_erm_data_below_half_width_regression :
    ¬ ∃ zfeat : BitVec 2 → BitVec 0,
        Nonempty
          (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMData
            (fullRuleActualSwitchedLocalInterface (BitVec 2) 0)
            zfeat) := by
  exact
    kpolyCoverage_anchor_surjectiveActualLocal_not_exists_sharedExactZABSparseThresholdERMData_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
      (n := 2) (k := 0) (r := 0)
      (T := fullRuleActualSwitchedLocalInterface (BitVec 2) 0)
      (fullRuleActualSwitchedLocalInterface_surjective (BitVec 2) 0)
      (by omega)

theorem kpoly_anchor_full_rule_actual_local_recovery_payload_predictor_card_regression :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          fin3PureMeasureActualSparseRecoveryPayloadBridge
          (fullRuleActualSwitchedLocalInterface (Fin 3) 0)
          fin3ToBitVec0ActualSparseRecoveryPayloadBridge
          0) := by
  exact
    kpolyCoverage_anchor_surjectiveActualLocal_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_lt_predictorCard
      (μ := fin3PureMeasureActualSparseRecoveryPayloadBridge)
      (T := fullRuleActualSwitchedLocalInterface (Fin 3) 0)
      (zfeat := fin3ToBitVec0ActualSparseRecoveryPayloadBridge)
      (q := 0)
      fullRuleActualSwitchedLocalInterface_lt_predictorCard_fin3k0r0_payload_bridge_regression
      (fullRuleActualSwitchedLocalInterface_surjective (Fin 3) 0)

theorem kpoly_anchor_full_rule_actual_local_no_extractor_recovery_payload_predictor_card_regression :
    ¬ ∃ zfeat : Fin 3 → BitVec 0,
        Nonempty
          (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
            fin3PureMeasureActualSparseRecoveryPayloadBridge
            (fullRuleActualSwitchedLocalInterface (Fin 3) 0)
            zfeat
            0) := by
  exact
    kpolyCoverage_anchor_surjectiveActualLocal_not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_lt_predictorCard
      (μ := fin3PureMeasureActualSparseRecoveryPayloadBridge)
      (T := fullRuleActualSwitchedLocalInterface (Fin 3) 0)
      (r := 0)
      (q := 0)
      fullRuleActualSwitchedLocalInterface_lt_predictorCard_fin3k0r0_payload_bridge_regression
      (fullRuleActualSwitchedLocalInterface_surjective (Fin 3) 0)

theorem kpoly_anchor_full_rule_actual_local_recovery_payload_injective_probe_card_regression :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          fin3PureMeasureActualSparseRecoveryPayloadBridge
          (fullRuleActualSwitchedLocalInterface (Fin 3) 0)
          fin3ToBitVec0ActualSparseRecoveryPayloadBridge
          0) := by
  exact
    kpolyCoverage_anchor_actualLocal_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_injective_realization_of_lt_card
      (μ := fin3PureMeasureActualSparseRecoveryPayloadBridge)
      (T := fullRuleActualSwitchedLocalInterface (Fin 3) 0)
      (zfeat := fin3ToBitVec0ActualSparseRecoveryPayloadBridge)
      (q := 0)
      fin5ProbeFamilyActualSparseRecoveryPayloadBridge
      fin5ProbeFamilyActualSparseRecoveryPayloadBridge_injective
      (fun p => (fullRuleActualSwitchedLocalInterface_surjective (Fin 3) 0)
        (fin5ProbeFamilyActualSparseRecoveryPayloadBridge p))
      fin5ProbeFamilyActualSparseRecoveryPayloadBridge_lt_card_regression

theorem kpoly_anchor_full_rule_actual_local_no_extractor_recovery_payload_injective_probe_card_regression :
    ¬ ∃ zfeat : Fin 3 → BitVec 0,
        Nonempty
          (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
            fin3PureMeasureActualSparseRecoveryPayloadBridge
            (fullRuleActualSwitchedLocalInterface (Fin 3) 0)
            zfeat
            0) := by
  exact
    kpolyCoverage_anchor_actualLocal_not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_injective_realization_of_lt_card
      (μ := fin3PureMeasureActualSparseRecoveryPayloadBridge)
      (T := fullRuleActualSwitchedLocalInterface (Fin 3) 0)
      (r := 0)
      (q := 0)
      fin5ProbeFamilyActualSparseRecoveryPayloadBridge
      fin5ProbeFamilyActualSparseRecoveryPayloadBridge_injective
      (fun p => (fullRuleActualSwitchedLocalInterface_surjective (Fin 3) 0)
        (fin5ProbeFamilyActualSparseRecoveryPayloadBridge p))
      fin5ProbeFamilyActualSparseRecoveryPayloadBridge_lt_card_regression

theorem kpoly_anchor_surjective_actual_local_recovery_uniform_cardinality_threshold_regression
    {q : ℝ≥0∞}
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          bitVec1k1UniformMeasureActualSparseRecoveryCardinalityBridge
          (fullRuleActualSwitchedLocalInterface (BitVec 1) 1)
          idBitVec1ActualSparseRecoveryCardinalityBridge
          q)) :
    1 - (Fintype.card (ExactVisiblePostSwitchSurface (BitVec 1) 1) : ℝ≥0∞)⁻¹ ≤ q := by
  exact
    kpolyCoverage_anchor_surjectiveActualLocal_one_sub_inv_card_le_of_nonempty_recovery
      (k := 1)
      (r := 1)
      (T := fullRuleActualSwitchedLocalInterface (BitVec 1) 1)
      (fullRuleActualSwitchedLocalInterface_surjective (BitVec 1) 1)
      idBitVec1ActualSparseRecoveryCardinalityBridge
      h

theorem kpoly_anchor_full_rule_actual_local_recovery_bitvec_cardinality_threshold_regression
    {q : ℝ≥0∞}
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          bitVec1k1UniformMeasureActualSparseRecoveryCardinalityBridge
          (fullRuleActualSwitchedLocalInterface (BitVec 1) 1)
          idBitVec1ActualSparseRecoveryCardinalityBridge
          q)) :
    1 - (2 ^ (1 + 2 * 1) : ℝ≥0∞)⁻¹ ≤ q := by
  exact
    kpolyCoverage_anchor_fullRuleActualLocal_one_sub_pow_inv_le_of_nonempty_recovery
      (k := 1)
      (r := 1)
      (μ := bitVec1k1UniformMeasureActualSparseRecoveryCardinalityBridge)
      idBitVec1ActualSparseRecoveryCardinalityBridge
      h

theorem kpoly_anchor_full_rule_actual_local_no_extractor_recovery_bitvec_cardinality_threshold_regression :
    ¬ ∃ zfeat : BitVec 1 → BitVec 1,
        Nonempty
          (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
            bitVec1k1UniformMeasureActualSparseRecoveryCardinalityBridge
            (fullRuleActualSwitchedLocalInterface (BitVec 1) 1)
            zfeat
            0) := by
  exact
    kpolyCoverage_anchor_fullRuleActualLocal_not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_lt_one_sub_pow_inv
      (n := 1)
      (k := 1)
      (r := 1)
      bitVec1k1UniformMeasureActualSparseRecoveryCardinalityBridge
      (q := 0)
      (by
        rw [tsub_pos_iff_lt]
        exact ENNReal.inv_lt_one.2 (by norm_num))

theorem kpoly_anchor_actual_local_injective_recovery_uniform_cardinality_threshold_boundary_regression
    {q : ℝ≥0∞}
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          bitVec1k1UniformMeasureActualSparseRecoveryCardinalityBridge
          constFalseActualSwitchedLocalInterfaceBitVec1k1ActualSparseRecoveryInjectiveBridge
          idBitVec1ActualSparseRecoveryCardinalityBridge
          q)) :
    1 - (Fintype.card (ExactVisiblePostSwitchSurface (BitVec 1) 1) : ℝ≥0∞)⁻¹ ≤ q := by
  exact
    kpolyCoverage_anchor_actualLocal_one_sub_inv_card_le_of_nonempty_recovery_of_injective_zfeat
      (k := 1)
      (r := 1)
      (T := constFalseActualSwitchedLocalInterfaceBitVec1k1ActualSparseRecoveryInjectiveBridge)
      (zfeat := idBitVec1ActualSparseRecoveryCardinalityBridge)
      ()
      (fun _ _ hxy => hxy)
      (by norm_num)
      h

theorem kpoly_anchor_actual_local_injective_recovery_bitvec_cardinality_threshold_boundary_regression
    {q : ℝ≥0∞}
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          bitVec1k1UniformMeasureActualSparseRecoveryCardinalityBridge
          constFalseActualSwitchedLocalInterfaceBitVec1k1ActualSparseRecoveryInjectiveBridge
          idBitVec1ActualSparseRecoveryCardinalityBridge
          q)) :
    1 - (2 ^ (1 + 2 * 1) : ℝ≥0∞)⁻¹ ≤ q := by
  exact
    kpolyCoverage_anchor_actualLocal_one_sub_pow_inv_le_of_nonempty_recovery_of_injective_zfeat
      (k := 1)
      (r := 1)
      (T := constFalseActualSwitchedLocalInterfaceBitVec1k1ActualSparseRecoveryInjectiveBridge)
      (zfeat := idBitVec1ActualSparseRecoveryCardinalityBridge)
      ()
      (fun _ _ hxy => hxy)
      (by norm_num)
      h

theorem kpoly_anchor_actual_local_no_injective_extractor_recovery_bitvec_cardinality_threshold_regression :
    ¬ ∃ zfeat : BitVec 1 → BitVec 1,
        Function.Injective zfeat ∧
          Nonempty
            (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
              bitVec1k1UniformMeasureActualSparseRecoveryCardinalityBridge
              constFalseActualSwitchedLocalInterfaceBitVec1k1ActualSparseRecoveryInjectiveBridge
              zfeat
              ((3 : ℝ≥0∞) / 4)) := by
  exact
    kpolyCoverage_anchor_actualLocal_not_exists_injective_sharedExactZABSparseThresholdERMRecoveryData_of_lt_one_sub_pow_inv
      (n := 1)
      (k := 1)
      (r := 1)
      bitVec1k1UniformMeasureActualSparseRecoveryCardinalityBridge
      constFalseActualSwitchedLocalInterfaceBitVec1k1ActualSparseRecoveryInjectiveBridge
      ((3 : ℝ≥0∞) / 4)
      ()
      (by norm_num)
      (by
        have hthreshold : 1 - (2 ^ 3 : ℝ≥0∞)⁻¹ = (7 : ℝ≥0∞) / 8 := by
          have hsum : (1 : ℝ≥0∞) = (7 : ℝ≥0∞) / 8 + (2 ^ 3 : ℝ≥0∞)⁻¹ := by
            have hinv : ((2 ^ 3 : ℝ≥0∞)⁻¹) = (1 : ℝ≥0∞) / 8 := by
              norm_num
            calc
              (1 : ℝ≥0∞) = (8 : ℝ≥0∞) / 8 := by
                    exact (ENNReal.div_self (by norm_num) (by simp)).symm
              _ = ((7 : ℝ≥0∞) + 1) / 8 := by norm_num
              _ = (7 : ℝ≥0∞) / 8 + (1 : ℝ≥0∞) / 8 := by
                    simpa using
                      (ENNReal.div_add_div_same
                        (a := (7 : ℝ≥0∞))
                        (b := (1 : ℝ≥0∞))
                        (c := (8 : ℝ≥0∞))).symm
              _ = (7 : ℝ≥0∞) / 8 + (2 ^ 3 : ℝ≥0∞)⁻¹ := by
                    rw [hinv]
          exact ENNReal.sub_eq_of_eq_add (by simp) hsum
        rw [hthreshold]
        exact three_quarters_lt_seven_eighths_actualSparseRecoveryInjectiveBridge)

theorem kpoly_anchor_full_rule_actual_local_recovery_threshold_width_boundary_regression
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          bitVec1k1UniformMeasureActualSparseRecoveryCardinalityBridge
          (fullRuleActualSwitchedLocalInterface (BitVec 1) 1)
          idBitVec1ActualSparseRecoveryCardinalityBridge
          ((1 : ℝ≥0∞) / 2))) :
    1 + 2 * 1 < 4 := by
  exact
    kpolyCoverage_anchor_fullRuleActualLocal_visibleWidth_lt_of_nonempty_recovery_of_lt_one_sub_pow_inv
      (k := 1)
      (r := 1)
      (p := 4)
      (μ := bitVec1k1UniformMeasureActualSparseRecoveryCardinalityBridge)
      idBitVec1ActualSparseRecoveryCardinalityBridge
      h
      (half_lt_one_sub_pow_inv_of_two_lt_pow_cruxSynthesisRegression
        (by norm_num : (2 : ℝ≥0∞) < 2 ^ 4))

theorem kpoly_anchor_full_rule_actual_local_no_extractor_recovery_threshold_width_regression :
    ¬ ∃ zfeat : BitVec 1 → BitVec 1,
        Nonempty
          (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
            bitVec1k1UniformMeasureActualSparseRecoveryCardinalityBridge
            (fullRuleActualSwitchedLocalInterface (BitVec 1) 1)
            zfeat
            ((1 : ℝ≥0∞) / 2)) := by
  exact
    kpolyCoverage_anchor_fullRuleActualLocal_not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_lt_one_sub_pow_inv_of_le_visibleWidth
      (n := 1)
      (k := 1)
      (r := 1)
      (p := 3)
      bitVec1k1UniformMeasureActualSparseRecoveryCardinalityBridge
      (((1 : ℝ≥0∞) / 2))
      (by norm_num)
      (half_lt_one_sub_pow_inv_of_two_lt_pow_cruxSynthesisRegression
        (by norm_num : (2 : ℝ≥0∞) < 2 ^ 3))

theorem kpoly_anchor_bounded_sample_plugin_majority_actual_local_recovery_threshold_width_boundary_regression
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          bitVec1k1UniformMeasureActualSparseRecoveryCardinalityBridge
          (boundedSamplePluginMajorityActualSwitchedLocalInterface (BitVec 1) 1 8)
          idBitVec1ActualSparseRecoveryCardinalityBridge
          ((1 : ℝ≥0∞) / 2))) :
    1 + 2 * 1 < 4 := by
  exact
    kpolyCoverage_anchor_boundedSamplePluginMajorityActualLocal_visibleWidth_lt_of_nonempty_recovery_of_lt_one_sub_pow_inv
      (k := 1)
      (r := 1)
      (sampleBound := 8)
      (p := 4)
      (μ := bitVec1k1UniformMeasureActualSparseRecoveryCardinalityBridge)
      idBitVec1ActualSparseRecoveryCardinalityBridge
      h
      (by
        rw [card_exactVisiblePostSwitchSurface_bitVec]
        norm_num)
      (half_lt_one_sub_pow_inv_of_two_lt_pow_cruxSynthesisRegression
        (by norm_num : (2 : ℝ≥0∞) < 2 ^ 4))

theorem kpoly_anchor_bounded_sample_plugin_majority_actual_local_no_extractor_recovery_threshold_width_regression :
    ¬ ∃ zfeat : BitVec 1 → BitVec 1,
        Nonempty
          (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
            bitVec1k1UniformMeasureActualSparseRecoveryCardinalityBridge
            (boundedSamplePluginMajorityActualSwitchedLocalInterface (BitVec 1) 1 8)
            zfeat
            ((1 : ℝ≥0∞) / 2)) := by
  exact
    kpolyCoverage_anchor_boundedSamplePluginMajorityActualLocal_not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_lt_one_sub_pow_inv_of_le_visibleWidth
      (n := 1)
      (k := 1)
      (r := 1)
      (sampleBound := 8)
      (p := 3)
      bitVec1k1UniformMeasureActualSparseRecoveryCardinalityBridge
      (((1 : ℝ≥0∞) / 2))
      (by
        rw [card_exactVisiblePostSwitchSurface_bitVec]
        norm_num)
      (by norm_num)
      (half_lt_one_sub_pow_inv_of_two_lt_pow_cruxSynthesisRegression
        (by norm_num : (2 : ℝ≥0∞) < 2 ^ 3))

theorem kpoly_anchor_full_rule_actual_local_recovery_threshold_visible_budget_boundary_regression
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          bitVec1k1UniformMeasureActualSparseRecoveryCardinalityBridge
          (fullRuleActualSwitchedLocalInterface (BitVec 1) 1)
          zeroBitVec1ToBitVec0ActualSparseRecoveryThresholdVisibleBudgetBridge
          ((1 : ℝ≥0∞) / 2))) :
    1 ≤ 2 * 0 + 2 * 1 + 0 := by
  exact
    kpolyCoverage_anchor_fullRuleActualLocal_visibleWidth_le_two_mul_extractorWidth_add_two_mul_k_add_slack_of_nonempty_recovery_of_lt_one_sub_pow_inv
      (k := 1)
      (r := 0)
      (slack := 0)
      (μ := bitVec1k1UniformMeasureActualSparseRecoveryCardinalityBridge)
      zeroBitVec1ToBitVec0ActualSparseRecoveryThresholdVisibleBudgetBridge
      h
      (half_lt_one_sub_pow_inv_of_two_lt_pow_cruxSynthesisRegression
        (by norm_num : (2 : ℝ≥0∞) < 2 ^ 5))

theorem kpoly_anchor_full_rule_actual_local_no_extractor_recovery_threshold_visible_budget_regression :
    ¬ ∃ zfeat : BitVec 3 → BitVec 1,
        Nonempty
          (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
            bitVec3k0UniformMeasureActualSparseRecoveryThresholdVisibleBudgetBridge
            (fullRuleActualSwitchedLocalInterface (BitVec 3) 0)
            zfeat
            ((1 : ℝ≥0∞) / 2)) := by
  exact
    kpolyCoverage_anchor_fullRuleActualLocal_not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_lt_one_sub_pow_inv_of_two_mul_extractorWidth_add_two_mul_k_add_slack_lt_visibleWidth
      (n := 3)
      (k := 0)
      (r := 1)
      (slack := 0)
      bitVec3k0UniformMeasureActualSparseRecoveryThresholdVisibleBudgetBridge
      (((1 : ℝ≥0∞) / 2))
      (by norm_num)
      (half_lt_one_sub_pow_inv_of_two_lt_pow_cruxSynthesisRegression
        (by norm_num : (2 : ℝ≥0∞) < 2 ^ 3))

theorem kpoly_anchor_bounded_sample_plugin_majority_actual_local_recovery_threshold_visible_budget_boundary_regression
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          bitVec1k1UniformMeasureActualSparseRecoveryCardinalityBridge
          (boundedSamplePluginMajorityActualSwitchedLocalInterface (BitVec 1) 1 8)
          zeroBitVec1ToBitVec0ActualSparseRecoveryThresholdVisibleBudgetBridge
          ((1 : ℝ≥0∞) / 2))) :
    1 ≤ 2 * 0 + 2 * 1 + 0 := by
  exact
    kpolyCoverage_anchor_boundedSamplePluginMajorityActualLocal_visibleWidth_le_two_mul_extractorWidth_add_two_mul_k_add_slack_of_nonempty_recovery_of_lt_one_sub_pow_inv
      (k := 1)
      (r := 0)
      (sampleBound := 8)
      (slack := 0)
      (μ := bitVec1k1UniformMeasureActualSparseRecoveryCardinalityBridge)
      zeroBitVec1ToBitVec0ActualSparseRecoveryThresholdVisibleBudgetBridge
      h
      (by
        rw [card_exactVisiblePostSwitchSurface_bitVec]
        norm_num)
      (half_lt_one_sub_pow_inv_of_two_lt_pow_cruxSynthesisRegression
        (by norm_num : (2 : ℝ≥0∞) < 2 ^ 5))

theorem kpoly_anchor_bounded_sample_plugin_majority_actual_local_no_extractor_recovery_threshold_visible_budget_regression :
    ¬ ∃ zfeat : BitVec 3 → BitVec 1,
        Nonempty
          (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
            bitVec3k0UniformMeasureActualSparseRecoveryThresholdVisibleBudgetBridge
            (boundedSamplePluginMajorityActualSwitchedLocalInterface (BitVec 3) 0 8)
            zfeat
            ((1 : ℝ≥0∞) / 2)) := by
  exact
    kpolyCoverage_anchor_boundedSamplePluginMajorityActualLocal_not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_lt_one_sub_pow_inv_of_two_mul_extractorWidth_add_two_mul_k_add_slack_lt_visibleWidth
      (n := 3)
      (k := 0)
      (r := 1)
      (sampleBound := 8)
      (slack := 0)
      bitVec3k0UniformMeasureActualSparseRecoveryThresholdVisibleBudgetBridge
      (((1 : ℝ≥0∞) / 2))
      (by
        rw [card_exactVisiblePostSwitchSurface_bitVec]
        norm_num)
      (by norm_num)
      (half_lt_one_sub_pow_inv_of_two_lt_pow_cruxSynthesisRegression
        (by norm_num : (2 : ℝ≥0∞) < 2 ^ 3))

theorem kpoly_anchor_surjective_actual_local_recovery_proper_region_mass_boundary_regression
    {q : ℝ≥0∞}
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          bitVec1k0PureMeasureActualSparseRecoveryRegionBridge
          (fullRuleActualSwitchedLocalInterface (BitVec 1) 0)
          zeroBitVec1ToBitVec0ActualSparseRecoveryThresholdVisibleBudgetBridge
          q)) :
    1 ≤ q := by
  have hbound :=
    kpolyCoverage_anchor_surjectiveActualLocal_regionMass_le_of_nonempty_recovery_of_exists_not_mem
      (k := 0)
      (r := 0)
      (T := fullRuleActualSwitchedLocalInterface (BitVec 1) 0)
      (μ := bitVec1k0PureMeasureActualSparseRecoveryRegionBridge)
      (q := q)
      (fullRuleActualSwitchedLocalInterface_surjective (BitVec 1) 0)
      zeroBitVec1ToBitVec0ActualSparseRecoveryThresholdVisibleBudgetBridge
      h
      bitVec1k0HeavyRegionActualSparseRecoveryRegionBridge
      (by
        exact ⟨bitVec1k0OneVisiblePointActualSparseRecoveryRegionBridge, by
          simp [bitVec1k0HeavyRegionActualSparseRecoveryRegionBridge,
            bitVec1k0OneVisiblePointActualSparseRecoveryRegionBridge,
            bitVec1k0ZeroVisiblePointActualSparseRecoveryRegionBridge]⟩)
  have hmass_eq :
      bitVec1k0HeavyRegionActualSparseRecoveryRegionBridge.sum
          (fun x => bitVec1k0PureMeasureActualSparseRecoveryRegionBridge x) = 1 := by
    simp [bitVec1k0HeavyRegionActualSparseRecoveryRegionBridge,
      bitVec1k0PureMeasureActualSparseRecoveryRegionBridge,
      bitVec1k0ZeroVisiblePointActualSparseRecoveryRegionBridge]
  rw [hmass_eq] at hbound
  exact hbound

theorem kpoly_anchor_surjective_actual_local_no_extractor_recovery_proper_region_mass_regression :
    ¬ ∃ zfeat : BitVec 1 → BitVec 0,
        Nonempty
          (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
            bitVec1k0PureMeasureActualSparseRecoveryRegionBridge
            (fullRuleActualSwitchedLocalInterface (BitVec 1) 0)
            zfeat
            0) := by
  exact
    kpolyCoverage_anchor_surjectiveActualLocal_not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_exists_not_mem_of_lt_regionMass
      (Z := BitVec 1)
      (k := 0)
      (r := 0)
      bitVec1k0PureMeasureActualSparseRecoveryRegionBridge
      (fullRuleActualSwitchedLocalInterface (BitVec 1) 0)
      (q := 0)
      (fullRuleActualSwitchedLocalInterface_surjective (BitVec 1) 0)
      bitVec1k0HeavyRegionActualSparseRecoveryRegionBridge
      (by
        exact ⟨bitVec1k0OneVisiblePointActualSparseRecoveryRegionBridge, by
          simp [bitVec1k0HeavyRegionActualSparseRecoveryRegionBridge,
            bitVec1k0OneVisiblePointActualSparseRecoveryRegionBridge,
            bitVec1k0ZeroVisiblePointActualSparseRecoveryRegionBridge]⟩)
      (by
        have hmass_eq :
            bitVec1k0HeavyRegionActualSparseRecoveryRegionBridge.sum
                (fun x => bitVec1k0PureMeasureActualSparseRecoveryRegionBridge x) = 1 := by
          simp [bitVec1k0HeavyRegionActualSparseRecoveryRegionBridge,
            bitVec1k0PureMeasureActualSparseRecoveryRegionBridge,
            bitVec1k0ZeroVisiblePointActualSparseRecoveryRegionBridge]
        rw [hmass_eq]
        norm_num)

theorem kpoly_anchor_actual_local_recovery_heavy_region_trace_card_boundary_regression
    {q : ℝ≥0∞}
    (hmass :
      q <
        fin3ZeroOneRegionActualSparseRecoveryHeavyRegionTraceBridge.sum
          (fun x => fin3ZeroOneHalfMeasureActualSparseRecoveryHeavyRegionTraceBridge x))
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          fin3ZeroOneHalfMeasureActualSparseRecoveryHeavyRegionTraceBridge
          fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayloadBridge
          fin3ToBitVec0ActualSparseRecoveryPayloadBridge
          q)) :
    Fintype.card (Fin 5) ≤
      2 ^ fin3ZeroOneRegionActualSparseRecoveryHeavyRegionTraceBridge.card := by
  exact
    kpolyCoverage_anchor_actualLocal_predictorCard_le_two_pow_regionCard_of_nonempty_recovery_of_injective_predict_of_lt_regionMass
      (μ := fin3ZeroOneHalfMeasureActualSparseRecoveryHeavyRegionTraceBridge)
      (T := fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayloadBridge)
      (Index := Fin 5)
      (r := 0)
      (zfeat := fin3ToBitVec0ActualSparseRecoveryPayloadBridge)
      h
      fin3ZeroOneRegionActualSparseRecoveryHeavyRegionTraceBridge
      hmass
      fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayloadBridge_injective_predict

theorem kpoly_anchor_actual_local_no_extractor_recovery_heavy_region_trace_card_regression :
    ¬ ∃ zfeat : Fin 3 → BitVec 0,
        Nonempty
          (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
            fin3ZeroOneHalfMeasureActualSparseRecoveryHeavyRegionTraceBridge
            fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayloadBridge
            zfeat
            fin3ThreeQuartersActualSparseRecoveryHeavyRegionTraceBridge) := by
  have hcard :
      2 ^ fin3ZeroOneRegionActualSparseRecoveryHeavyRegionTraceBridge.card <
        Fintype.card (Fin 5) := by
    rw [fin3ZeroOneRegionActualSparseRecoveryHeavyRegionTraceBridge_card]
    norm_num
  exact
    kpolyCoverage_anchor_actualLocal_not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_lt_regionCard_of_injective_predict_of_lt_regionMass
      (Z := Fin 3)
      (k := 0)
      (r := 0)
      (Index := Fin 5)
      (μ := fin3ZeroOneHalfMeasureActualSparseRecoveryHeavyRegionTraceBridge)
      (T := fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayloadBridge)
      (q := fin3ThreeQuartersActualSparseRecoveryHeavyRegionTraceBridge)
      fin3ZeroOneRegionActualSparseRecoveryHeavyRegionTraceBridge
      fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayloadBridge_injective_predict
      fin3ThreeQuartersActualSparseRecoveryHeavyRegionTraceBridge_lt_regionMass
      hcard

theorem current_pnp_kpoly_product_bound_bridge_finite_image_regression :
    PNPKpolySubrepairClass.productBoundBridgeFiniteImageBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.productBoundBridgeFiniteImageBoundary

theorem current_pnp_kpoly_fielded_switching_bridge_finite_image_regression :
    PNPKpolySubrepairClass.fieldedSwitchingBridgeFiniteImageBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.fieldedSwitchingBridgeFiniteImageBoundary

theorem current_pnp_kpoly_product_bound_full_visible_regression :
    PNPKpolySubrepairClass.productBoundOnlyFullVisibleObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.productBoundOnlyFullVisibleObstruction

theorem current_pnp_kpoly_fielded_switching_full_visible_regression :
    PNPKpolySubrepairClass.fieldedSwitchingOnlyFullVisibleObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.fieldedSwitchingOnlyFullVisibleObstruction

theorem current_pnp_kpoly_product_bound_surjective_visible_regression :
    PNPKpolySubrepairClass.productBoundOnlySurjectiveVisibleObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.productBoundOnlySurjectiveVisibleObstruction

theorem current_pnp_kpoly_fielded_switching_surjective_visible_regression :
    PNPKpolySubrepairClass.fieldedSwitchingOnlySurjectiveVisibleObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.fieldedSwitchingOnlySurjectiveVisibleObstruction

theorem current_pnp_kpoly_product_bound_clocked_payload_boundary_regression :
    PNPKpolySubrepairClass.productBoundClockedPayloadBridgeFiniteImageBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.productBoundClockedPayloadBridgeFiniteImageBoundary

theorem current_pnp_kpoly_fielded_switching_clocked_payload_boundary_regression :
    PNPKpolySubrepairClass.fieldedSwitchingClockedPayloadBridgeFiniteImageBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.fieldedSwitchingClockedPayloadBridgeFiniteImageBoundary

theorem current_pnp_kpoly_product_bound_clocked_payload_full_visible_regression :
    PNPKpolySubrepairClass.productBoundOnlyClockedPayloadFullVisibleObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.productBoundOnlyClockedPayloadFullVisibleObstruction

theorem current_pnp_kpoly_fielded_switching_clocked_payload_full_visible_regression :
    PNPKpolySubrepairClass.fieldedSwitchingOnlyClockedPayloadFullVisibleObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.fieldedSwitchingOnlyClockedPayloadFullVisibleObstruction

theorem current_pnp_kpoly_product_bound_clocked_payload_surjective_regression :
    PNPKpolySubrepairClass.productBoundOnlyClockedPayloadSurjectiveVisibleObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.productBoundOnlyClockedPayloadSurjectiveVisibleObstruction

theorem current_pnp_kpoly_fielded_switching_clocked_payload_surjective_regression :
    PNPKpolySubrepairClass.fieldedSwitchingOnlyClockedPayloadSurjectiveVisibleObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.fieldedSwitchingOnlyClockedPayloadSurjectiveVisibleObstruction

theorem current_pnp_kpoly_actual_switched_history_bitvec_full_width_interval_regression :
    PNPKpolySubrepairClass.actualSwitchedHistoryBitVecFullWidthIntervalObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualSwitchedHistoryBitVecFullWidthIntervalObstruction

theorem current_pnp_kpoly_actual_switched_history_bitvec_full_width_interval_clocked_payload_regression :
    PNPKpolySubrepairClass.actualSwitchedHistoryBitVecFullWidthIntervalClockedPayloadObstruction ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualSwitchedHistoryBitVecFullWidthIntervalClockedPayloadObstruction

theorem kpoly_anchor_full_rule_actual_switched_history_exact_visible_interval_regression :
    ¬ ActualSwitchedLocalInterface.SwitchedHistoryExactVisibleCompressionWrapper
        Bool
        (fullRuleActualSwitchedLocalInterface (BitVec 1) 1)
        4
        ([] : List (FiniteEvent Bool))
        ([] : List (V13FieldedStep Bool)) := by
  exact
    kpolyCoverage_anchor_not_switchedHistoryExactVisibleCompressionWrapper_of_true_fieldedSwitching_of_surjective_predict_of_le_fullWidthBudget
      (T := fullRuleActualSwitchedLocalInterface (BitVec 1) 1)
      (s := 4)
      (hist := ([] : List (FiniteEvent Bool)))
      (items := ([] : List (V13FieldedStep Bool)))
      (by trivial)
      (fullRuleActualSwitchedLocalInterface_surjective (BitVec 1) 1)
      (by norm_num)
      (by norm_num)

theorem kpoly_anchor_full_rule_actual_switched_history_clocked_interval_regression :
    ¬ ActualSwitchedLocalInterface.SwitchedHistoryClockedKpolyFiniteLearningWrapper
        Bool
        (fullRuleActualSwitchedLocalInterface (BitVec 1) 1)
        4
        0
        ([] : List (FiniteEvent Bool))
        ([] : List (V13FieldedStep Bool)) := by
  exact
    kpolyCoverage_anchor_not_switchedHistoryClockedKpolyFiniteLearningWrapper_of_true_fieldedSwitching_of_surjective_predict_of_le_fullWidthBudget
      (T := fullRuleActualSwitchedLocalInterface (BitVec 1) 1)
      (s := 4) (clock := 0)
      (hist := ([] : List (FiniteEvent Bool)))
      (items := ([] : List (V13FieldedStep Bool)))
      (by trivial)
      (fullRuleActualSwitchedLocalInterface_surjective (BitVec 1) 1)
      (by norm_num)
      (by norm_num)

theorem current_pnp_kpoly_support_full_rule_output_family_factor_regression :
    PNPKpolySubrepairClass.supportFullRuleOutputFamilyFactorBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.supportFullRuleOutputFamilyFactorBoundary

theorem current_pnp_kpoly_support_full_rule_observed_rule_injective_surjective_regression :
    PNPKpolySubrepairClass.supportFullRuleObservedRuleInjectiveSurjectiveBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.supportFullRuleObservedRuleInjectiveSurjectiveBoundary

theorem current_pnp_kpoly_support_full_rule_exact_decoder_surjective_regression :
    PNPKpolySubrepairClass.supportFullRuleExactDecoderSurjectiveBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.supportFullRuleExactDecoderSurjectiveBoundary

theorem current_pnp_kpoly_support_full_rule_observed_rule_map_noninjective_regression :
    PNPKpolySubrepairClass.supportFullRuleObservedRuleMapNoninjectiveBelowSurfaceCard ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.supportFullRuleObservedRuleMapNoninjectiveBelowSurfaceCard

theorem current_pnp_kpoly_support_full_rule_distinct_rules_same_output_regression :
    PNPKpolySubrepairClass.supportFullRuleDistinctRulesSameOutputBelowSurfaceCard ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.supportFullRuleDistinctRulesSameOutputBelowSurfaceCard

theorem current_pnp_kpoly_support_full_rule_property_decoder_constancy_regression :
    PNPKpolySubrepairClass.supportFullRulePropertyDecoderFiberConstancyBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.supportFullRulePropertyDecoderFiberConstancyBoundary

theorem current_pnp_kpoly_support_full_rule_property_decoder_iff_regression :
    PNPKpolySubrepairClass.supportFullRulePropertyDecoderIffFiberConstancyBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.supportFullRulePropertyDecoderIffFiberConstancyBoundary

theorem current_pnp_kpoly_support_full_rule_no_property_decoder_regression :
    PNPKpolySubrepairClass.supportFullRuleNoPropertyDecoderSameOutputBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.supportFullRuleNoPropertyDecoderSameOutputBoundary

theorem current_pnp_kpoly_support_full_rule_eval_decoder_range_regression :
    PNPKpolySubrepairClass.supportFullRuleEvalDecoderRangeBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.supportFullRuleEvalDecoderRangeBoundary

theorem current_pnp_kpoly_support_full_rule_all_eval_decoders_surjective_regression :
    PNPKpolySubrepairClass.supportFullRuleAllEvalDecodersSurjectiveBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.supportFullRuleAllEvalDecodersSurjectiveBoundary

theorem current_pnp_kpoly_support_full_rule_query_decoder_range_regression :
    PNPKpolySubrepairClass.supportFullRuleQueryDecoderRangeBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.supportFullRuleQueryDecoderRangeBoundary

theorem current_pnp_kpoly_support_full_rule_no_query_decoder_missed_query_regression :
    PNPKpolySubrepairClass.supportFullRuleNoQueryDecoderMissedQueryBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.supportFullRuleNoQueryDecoderMissedQueryBoundary

theorem current_pnp_kpoly_support_full_rule_adaptive_query_decoder_reachable_regression :
    PNPKpolySubrepairClass.supportFullRuleAdaptiveQueryDecoderReachableBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.supportFullRuleAdaptiveQueryDecoderReachableBoundary

theorem current_pnp_kpoly_support_full_rule_adaptive_query_decoder_iff_regression :
    PNPKpolySubrepairClass.supportFullRuleAdaptiveQueryDecoderIffFiberConstancyBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.supportFullRuleAdaptiveQueryDecoderIffFiberConstancyBoundary

theorem current_pnp_kpoly_support_full_rule_no_adaptive_query_decoder_regression :
    PNPKpolySubrepairClass.supportFullRuleNoAdaptiveQueryDecoderSameOutputEvalBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.supportFullRuleNoAdaptiveQueryDecoderSameOutputEvalBoundary

theorem current_pnp_kpoly_support_full_rule_no_root_adaptive_query_decoder_regression :
    PNPKpolySubrepairClass.supportFullRuleNoRootAdaptiveQueryDecoderMissedPointBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.supportFullRuleNoRootAdaptiveQueryDecoderMissedPointBoundary

theorem current_pnp_kpoly_support_full_rule_no_exact_decoder_regression :
    PNPKpolySubrepairClass.supportFullRuleNoExactDecoderBelowSurfaceCard ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.supportFullRuleNoExactDecoderBelowSurfaceCard

theorem current_pnp_kpoly_support_full_rule_unobservable_eval_regression :
    PNPKpolySubrepairClass.supportFullRuleUnobservableEvalBelowSurfaceCard ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.supportFullRuleUnobservableEvalBelowSurfaceCard

theorem current_pnp_kpoly_support_full_rule_observed_small_cover_regression :
    PNPKpolySubrepairClass.supportFullRuleObservedSmallNotExactVisibleCoverBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.supportFullRuleObservedSmallNotExactVisibleCoverBoundary

theorem current_pnp_kpoly_support_full_rule_not_clocked_payload_regression :
    PNPKpolySubrepairClass.supportFullRuleNotClockedPayloadBelowSurfaceCard ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.supportFullRuleNotClockedPayloadBelowSurfaceCard

theorem current_pnp_kpoly_support_full_rule_uniform_section_finite_cover_regression :
    PNPKpolySubrepairClass.supportFullRuleUniformSectionFinitePredictorCoverBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.supportFullRuleUniformSectionFinitePredictorCoverBoundary

theorem current_pnp_kpoly_support_full_rule_uniform_section_clocked_payload_regression :
    PNPKpolySubrepairClass.supportFullRuleUniformSectionClockedPayloadBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.supportFullRuleUniformSectionClockedPayloadBoundary

theorem current_pnp_kpoly_support_full_rule_uniform_section_surface_card_regression :
    PNPKpolySubrepairClass.supportFullRuleUniformSectionSurfaceCardBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.supportFullRuleUniformSectionSurfaceCardBoundary

theorem current_pnp_kpoly_support_full_rule_no_uniform_section_regression :
    PNPKpolySubrepairClass.supportFullRuleNoUniformSectionBelowSurfaceCard ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.supportFullRuleNoUniformSectionBelowSurfaceCard

theorem current_pnp_kpoly_one_block_full_rule_observed_small_cover_regression :
    PNPKpolySubrepairClass.oneBlockFullRuleObservedSmallNotExactVisibleCoverBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.oneBlockFullRuleObservedSmallNotExactVisibleCoverBoundary

theorem current_pnp_kpoly_one_block_full_rule_not_clocked_payload_regression :
    PNPKpolySubrepairClass.oneBlockFullRuleNotClockedPayloadBelowSurfaceCard ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.oneBlockFullRuleNotClockedPayloadBelowSurfaceCard

theorem current_pnp_kpoly_one_block_full_rule_no_exact_decoder_regression :
    PNPKpolySubrepairClass.oneBlockFullRuleNoExactDecoderOneLtSurfaceCardBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.oneBlockFullRuleNoExactDecoderOneLtSurfaceCardBoundary

theorem current_pnp_kpoly_one_block_full_rule_unobservable_eval_regression :
    PNPKpolySubrepairClass.oneBlockFullRuleUnobservableEvalOneLtSurfaceCardBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.oneBlockFullRuleUnobservableEvalOneLtSurfaceCardBoundary

theorem kpoly_anchor_product_bound_clocked_payload_bridge_iff_finite_image_regression
    {Ω : Type u} {Z : Type v} [Fintype Ω] [Fintype Z] {k s clock : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)} :
    ProductBoundOnlyClockedKpolyFiniteLearningBridge Ω Z k s clock hist items ↔
      ∀ {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index),
        ProductBoundSemanticFiniteImageBridge Ω Z k s hist items G := by
  exact
    kpolyCoverage_anchor_productBoundOnlyClockedKpolyFiniteLearningBridge_iff_forall_semanticFiniteImageBridge

theorem kpoly_anchor_fielded_switching_clocked_payload_bridge_iff_finite_image_regression
    {Ω : Type u} {Z : Type v} [Fintype Ω] [Fintype Z] {k s clock : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)} :
    FieldedSwitchingOnlyClockedKpolyFiniteLearningBridge Ω Z k s clock hist items ↔
      ∀ {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index),
        FieldedSwitchingSemanticFiniteImageBridge Ω Z k s hist items G := by
  exact
    kpolyCoverage_anchor_fieldedSwitchingOnlyClockedKpolyFiniteLearningBridge_iff_forall_semanticFiniteImageBridge

theorem kpoly_anchor_exact_zab_recovery_large_region_disagreement_regression
    {Z : Type u} [Fintype Z] {r k : ℕ} {Index : Type v}
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (i : Index)
    (c :
      (rawExactZABDecisionListBitFamily Z r k zfeat).toEncodedFamily.BadCodes
        (G.predict i))
    (region : Finset (ExactVisiblePostSwitchSurface Z k))
    (hmass : q < region.sum (fun x => μ x)) :
    ∃ x, x ∈ region ∧ μ x ≠ 0 ∧
      (rawExactZABDecisionListBitFamily Z r k zfeat).decode c.1 x ≠
        G.predict i x := by
  exact
    kpolyCoverage_anchor_exactZABERMRecoveryData_exists_pos_mass_disagreement_in_region_of_badCode
      h i c region hmass

theorem pnp_packet_missing_repair_blocks_stop_grade_regression
    {packet : PNPCruxPacket} {repair : PNPRepairClass}
    (hmiss : ¬ packet.covers repair) :
    ¬ packet.StopGrade := by
  exact PNPCruxPacket.not_stopGrade_of_not_covers hmiss

theorem current_pnp_packet_theorem_backed_v13_status_regression :
    currentPNPLocalCruxPacket.covers .repeatedPositiveFieldedPivot ∧
      currentPNPLocalCruxPacket.covers .forcedPositiveFieldedStep ∧
      currentPNPLocalCruxPacket.covers .fixedFieldBadCell ∧
      currentPNPLocalCruxPacket.covers .fieldRefinementOfBadCell ∧
      currentPNPLocalCruxPacket.covers .cdEvidenceNormalization ∧
      currentPNPLocalCruxPacket.covers .traceCaptureFactorization ∧
      currentPNPLocalCruxPacket.covers .atomicEvidenceBudget ∧
      currentPNPLocalCruxPacket.covers .acceiEnvelopeProduct ∧
        ¬ currentPNPLocalCruxPacket.StopGrade := by
  exact currentPNPLocalCruxPacket_theoremBacked_v13_status

theorem current_pnp_strongest_honest_status_regression :
    currentPNPLocalCruxPacket.covers .repeatedPositiveFieldedPivot ∧
      currentPNPLocalCruxPacket.covers .forcedPositiveFieldedStep ∧
      currentPNPLocalCruxPacket.covers .fixedFieldBadCell ∧
      currentPNPLocalCruxPacket.covers .fieldRefinementOfBadCell ∧
      currentPNPLocalCruxPacket.covers .cdEvidenceNormalization ∧
      currentPNPLocalCruxPacket.covers .traceCaptureFactorization ∧
      currentPNPLocalCruxPacket.covers .atomicEvidenceBudget ∧
      currentPNPLocalCruxPacket.covers .acceiEnvelopeProduct ∧
      currentPNPLocalCruxPacket.covers .clockedFiniteUniformKernel ∧
      (∀ {r k clock : ℕ} {Index : Type u} [Fintype (BitVec r)]
        (samples :
          Index → Sample (ExactVisiblePostSwitchSurface (BitVec r) k) Bool),
        ClockedKpolyFiniteLearningPayload
          (bitVecZABDecisionListERMFamily
            (r := r) (k := k) (Index := Index) samples)
          (r + 2 * k + 1) clock) ∧
      (∀ {Z : Type v} [Fintype Z] {k s clock : ℕ}
        (_ : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)),
        ¬ (∀ {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index),
          ClockedKpolyFiniteLearningPayload G s clock)) ∧
      ¬ currentPNPLocalCruxPacket.covers .kpolyCompressionBridge ∧
      ¬ currentPNPLocalCruxPacket.StopGrade := by
  exact currentPNPStrongestHonestStatus

theorem current_pnp_packet_not_stop_grade_regression :
    ¬ currentPNPLocalCruxPacket.StopGrade := by
  exact not_stopGrade_currentPNPLocalCruxPacket

theorem current_pnp_packet_residual_side_information_uncovered_regression :
    ¬ currentPNPLocalCruxPacket.covers .residualSideInformation := by
  exact residualSideInformation_uncovered_currentPNPLocalCruxPacket

theorem current_pnp_packet_randomized_residual_uncovered_regression :
    ¬ currentPNPLocalCruxPacket.covers .randomizedResidual := by
  exact randomizedResidual_uncovered_currentPNPLocalCruxPacket

theorem current_pnp_packet_same_source_finite_count_approximation_covered_regression :
    currentPNPLocalCruxPacket.covers .sameSourceFiniteCountApproximation := by
  exact sameSourceFiniteCountApproximation_covered_currentPNPLocalCruxPacket

theorem current_pnp_residual_promoted_packet_extends_current_regression :
    currentPNPResidualPromotedPacket.Extends currentPNPLocalCruxPacket := by
  exact currentPNPResidualPromotedPacket_extends_current

theorem current_pnp_residual_promoted_packet_residual_side_information_covered_regression :
    currentPNPResidualPromotedPacket.covers .residualSideInformation := by
  exact residualSideInformation_covered_currentPNPResidualPromotedPacket

theorem current_pnp_residual_promoted_packet_randomized_residual_uncovered_regression :
    ¬ currentPNPResidualPromotedPacket.covers .randomizedResidual := by
  exact randomizedResidual_uncovered_currentPNPResidualPromotedPacket

theorem current_pnp_residual_promoted_packet_approximate_decorrelation_uncovered_regression :
    ¬ currentPNPResidualPromotedPacket.covers .approximateDecorrelation := by
  exact approximateDecorrelation_uncovered_currentPNPResidualPromotedPacket

theorem current_pnp_residual_promoted_packet_kpoly_bridge_uncovered_regression :
    ¬ currentPNPResidualPromotedPacket.covers .kpolyCompressionBridge := by
  exact kpolyCompressionBridge_uncovered_currentPNPResidualPromotedPacket

theorem current_pnp_residual_promoted_packet_not_stop_grade_regression :
    ¬ currentPNPResidualPromotedPacket.StopGrade := by
  exact not_stopGrade_currentPNPResidualPromotedPacket

theorem current_pnp_residual_promoted_packet_next_target_uncovered_regression :
    ¬ currentPNPResidualPromotedPacket.covers
      currentPNPResidualPromotedNextMarginalTarget := by
  exact currentPNPResidualPromotedNextMarginalTarget_uncovered

theorem current_pnp_residual_promoted_packet_next_target_mem_uncovered_regression :
    currentPNPResidualPromotedNextMarginalTarget ∈
      currentPNPResidualPromotedUncoveredRepairClasses := by
  exact currentPNPResidualPromotedNextMarginalTarget_mem_uncovered

theorem current_pnp_residual_promoted_packet_status_regression :
    currentPNPResidualPromotedPacket.Extends currentPNPLocalCruxPacket ∧
      currentPNPResidualPromotedPacket.covers .residualSideInformation ∧
      ¬ currentPNPResidualPromotedPacket.covers .randomizedResidual ∧
      ¬ currentPNPResidualPromotedPacket.covers .approximateDecorrelation ∧
      ¬ currentPNPResidualPromotedPacket.covers .kpolyCompressionBridge ∧
      ¬ currentPNPResidualPromotedPacket.StopGrade := by
  exact currentPNPResidualPromotedStatus

theorem current_pnp_randomized_residual_promoted_packet_extends_residual_promoted_regression :
    currentPNPRandomizedResidualPromotedPacket.Extends
      currentPNPResidualPromotedPacket := by
  exact currentPNPRandomizedResidualPromotedPacket_extends_residualPromoted

theorem current_pnp_randomized_residual_promoted_packet_residual_side_information_covered_regression :
    currentPNPRandomizedResidualPromotedPacket.covers
      .residualSideInformation := by
  exact
    residualSideInformation_covered_currentPNPRandomizedResidualPromotedPacket

theorem current_pnp_randomized_residual_promoted_packet_randomized_residual_covered_regression :
    currentPNPRandomizedResidualPromotedPacket.covers .randomizedResidual := by
  exact randomizedResidual_covered_currentPNPRandomizedResidualPromotedPacket

theorem current_pnp_randomized_residual_promoted_packet_approximate_decorrelation_uncovered_regression :
    ¬ currentPNPRandomizedResidualPromotedPacket.covers
      .approximateDecorrelation := by
  exact
    approximateDecorrelation_uncovered_currentPNPRandomizedResidualPromotedPacket

theorem current_pnp_randomized_residual_promoted_packet_kpoly_bridge_uncovered_regression :
    ¬ currentPNPRandomizedResidualPromotedPacket.covers
      .kpolyCompressionBridge := by
  exact
    kpolyCompressionBridge_uncovered_currentPNPRandomizedResidualPromotedPacket

theorem current_pnp_randomized_residual_promoted_packet_not_stop_grade_regression :
    ¬ currentPNPRandomizedResidualPromotedPacket.StopGrade := by
  exact not_stopGrade_currentPNPRandomizedResidualPromotedPacket

theorem current_pnp_randomized_residual_promoted_packet_next_target_uncovered_regression :
    ¬ currentPNPRandomizedResidualPromotedPacket.covers
      currentPNPRandomizedResidualPromotedNextMarginalTarget := by
  exact currentPNPRandomizedResidualPromotedNextMarginalTarget_uncovered

theorem current_pnp_randomized_residual_promoted_packet_next_target_mem_uncovered_regression :
    currentPNPRandomizedResidualPromotedNextMarginalTarget ∈
      currentPNPRandomizedResidualPromotedUncoveredRepairClasses := by
  exact currentPNPRandomizedResidualPromotedNextMarginalTarget_mem_uncovered

theorem current_pnp_randomized_residual_promoted_packet_status_regression :
    currentPNPRandomizedResidualPromotedPacket.Extends
        currentPNPResidualPromotedPacket ∧
      currentPNPRandomizedResidualPromotedPacket.covers
        .residualSideInformation ∧
      currentPNPRandomizedResidualPromotedPacket.covers .randomizedResidual ∧
      ¬ currentPNPRandomizedResidualPromotedPacket.covers
        .approximateDecorrelation ∧
      ¬ currentPNPRandomizedResidualPromotedPacket.covers
        .kpolyCompressionBridge ∧
      ¬ currentPNPRandomizedResidualPromotedPacket.StopGrade := by
  exact currentPNPRandomizedResidualPromotedStatus

theorem current_pnp_approximate_decorrelation_promoted_packet_extends_randomized_residual_promoted_regression :
    currentPNPApproximateDecorrelationPromotedPacket.Extends
      currentPNPRandomizedResidualPromotedPacket := by
  exact
    currentPNPApproximateDecorrelationPromotedPacket_extends_randomizedResidualPromoted

theorem current_pnp_approximate_decorrelation_promoted_packet_residual_side_information_covered_regression :
    currentPNPApproximateDecorrelationPromotedPacket.covers
      .residualSideInformation := by
  exact
    residualSideInformation_covered_currentPNPApproximateDecorrelationPromotedPacket

theorem current_pnp_approximate_decorrelation_promoted_packet_randomized_residual_covered_regression :
    currentPNPApproximateDecorrelationPromotedPacket.covers
      .randomizedResidual := by
  exact randomizedResidual_covered_currentPNPApproximateDecorrelationPromotedPacket

theorem current_pnp_approximate_decorrelation_promoted_packet_approximate_decorrelation_covered_regression :
    currentPNPApproximateDecorrelationPromotedPacket.covers
      .approximateDecorrelation := by
  exact
    approximateDecorrelation_covered_currentPNPApproximateDecorrelationPromotedPacket

theorem current_pnp_approximate_decorrelation_promoted_packet_kpoly_bridge_uncovered_regression :
    ¬ currentPNPApproximateDecorrelationPromotedPacket.covers
      .kpolyCompressionBridge := by
  exact
    kpolyCompressionBridge_uncovered_currentPNPApproximateDecorrelationPromotedPacket

theorem current_pnp_approximate_decorrelation_promoted_packet_not_stop_grade_regression :
    ¬ currentPNPApproximateDecorrelationPromotedPacket.StopGrade := by
  exact not_stopGrade_currentPNPApproximateDecorrelationPromotedPacket

theorem current_pnp_approximate_decorrelation_promoted_packet_next_target_uncovered_regression :
    ¬ currentPNPApproximateDecorrelationPromotedPacket.covers
      currentPNPApproximateDecorrelationPromotedNextMarginalTarget := by
  exact currentPNPApproximateDecorrelationPromotedNextMarginalTarget_uncovered

theorem current_pnp_approximate_decorrelation_promoted_packet_next_target_mem_uncovered_regression :
    currentPNPApproximateDecorrelationPromotedNextMarginalTarget ∈
      currentPNPApproximateDecorrelationPromotedUncoveredRepairClasses := by
  exact
    currentPNPApproximateDecorrelationPromotedNextMarginalTarget_mem_uncovered

theorem current_pnp_approximate_decorrelation_promoted_packet_status_regression :
    currentPNPApproximateDecorrelationPromotedPacket.Extends
        currentPNPRandomizedResidualPromotedPacket ∧
      currentPNPApproximateDecorrelationPromotedPacket.covers
        .residualSideInformation ∧
      currentPNPApproximateDecorrelationPromotedPacket.covers
        .randomizedResidual ∧
      currentPNPApproximateDecorrelationPromotedPacket.covers
        .approximateDecorrelation ∧
      ¬ currentPNPApproximateDecorrelationPromotedPacket.covers
        .kpolyCompressionBridge ∧
      ¬ currentPNPApproximateDecorrelationPromotedPacket.StopGrade := by
  exact currentPNPApproximateDecorrelationPromotedStatus

theorem current_pnp_kpoly_compression_bridge_promoted_packet_extends_approximate_decorrelation_promoted_regression :
    currentPNPKpolyCompressionBridgePromotedPacket.Extends
      currentPNPApproximateDecorrelationPromotedPacket := by
  exact
    currentPNPKpolyCompressionBridgePromotedPacket_extends_approximateDecorrelationPromoted

theorem current_pnp_kpoly_compression_bridge_promoted_packet_residual_side_information_covered_regression :
    currentPNPKpolyCompressionBridgePromotedPacket.covers
      .residualSideInformation := by
  exact
    residualSideInformation_covered_currentPNPKpolyCompressionBridgePromotedPacket

theorem current_pnp_kpoly_compression_bridge_promoted_packet_randomized_residual_covered_regression :
    currentPNPKpolyCompressionBridgePromotedPacket.covers
      .randomizedResidual := by
  exact randomizedResidual_covered_currentPNPKpolyCompressionBridgePromotedPacket

theorem current_pnp_kpoly_compression_bridge_promoted_packet_approximate_decorrelation_covered_regression :
    currentPNPKpolyCompressionBridgePromotedPacket.covers
      .approximateDecorrelation := by
  exact
    approximateDecorrelation_covered_currentPNPKpolyCompressionBridgePromotedPacket

theorem current_pnp_kpoly_compression_bridge_promoted_packet_kpoly_bridge_covered_regression :
    currentPNPKpolyCompressionBridgePromotedPacket.covers
      .kpolyCompressionBridge := by
  exact
    kpolyCompressionBridge_covered_currentPNPKpolyCompressionBridgePromotedPacket

theorem current_pnp_kpoly_compression_bridge_promoted_packet_covers_current_gaps_regression :
    currentPNPKpolyCompressionBridgePromotedPacket.CoversList
      currentPNPUncoveredRepairClasses := by
  exact currentPNPKpolyCompressionBridgePromotedPacket_covers_current_gaps

theorem current_pnp_kpoly_compression_bridge_promoted_packet_stop_grade_regression :
    currentPNPKpolyCompressionBridgePromotedPacket.StopGrade := by
  exact stopGrade_currentPNPKpolyCompressionBridgePromotedPacket

theorem current_pnp_kpoly_compression_bridge_promoted_packet_status_regression :
    currentPNPKpolyCompressionBridgePromotedPacket.Extends
        currentPNPApproximateDecorrelationPromotedPacket ∧
      currentPNPKpolyCompressionBridgePromotedPacket.covers
        .residualSideInformation ∧
      currentPNPKpolyCompressionBridgePromotedPacket.covers
        .randomizedResidual ∧
      currentPNPKpolyCompressionBridgePromotedPacket.covers
        .approximateDecorrelation ∧
      currentPNPKpolyCompressionBridgePromotedPacket.covers
        .kpolyCompressionBridge ∧
      currentPNPKpolyCompressionBridgePromotedPacket.StopGrade := by
  exact currentPNPKpolyCompressionBridgePromotedStatus

theorem canonical_zab_erm_route_coverage_regression :
    CanonicalZABERMRouteCoverage := by
  exact canonicalZABERMRouteCoverage

theorem canonical_zab_erm_route_clocked_payload_and_strict_budget_regression
    {Z : Type v} [Fintype Z] {r k clock : ℕ} {Index : Type u}
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index} {q : ℝ≥0∞}
    (h :
  CanonicalZABERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ zfeat G q) :
    ClockedKpolyFiniteLearningPayload G (r + 2 * k + 1) clock ∧
      (r + 2 * k + 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k) →
        ¬ Function.Surjective G.predict) := by
  rcases
      canonicalZABERMRouteCoverage
        (Z := Z) (r := r) (k := k) (clock := clock) (Index := Index)
        (μ := μ) (zfeat := zfeat) (G := G) (q := q) h
    with
    ⟨_, _, _, _, hpayload, hstrict⟩
  exact ⟨hpayload, hstrict⟩

theorem current_pnp_packet_v13_repeated_positive_fielded_pivot_covered_regression :
    currentPNPLocalCruxPacket.covers .repeatedPositiveFieldedPivot := by
  exact v13RepeatedPositiveFieldedPivotCoverage

theorem current_pnp_packet_v13_forced_positive_fielded_step_covered_regression :
    currentPNPLocalCruxPacket.covers .forcedPositiveFieldedStep := by
  exact forcedPositiveFieldedStep_covered_currentPNPLocalCruxPacket

theorem v13_forced_positive_fielded_step_bool_pair_forced_diagonal_blocks_regression :
    V13FieldSwitchingInstantiated
      [v13BoolPairUnitFieldedStep,
        v13BoolPairSecondCoordinateUnitFieldedStep] ∧
      ¬ V13FieldSwitchingInstantiated
        [v13BoolPairUnitFieldedStep,
          v13BoolPairSecondCoordinateUnitFieldedStep,
          v13BoolPairDiagonalUnitFieldedStep] := by
  exact v13BoolPairFirstSecondThenForcedDiagonal_blocked

theorem current_pnp_packet_v13_fixed_field_bad_cell_covered_regression :
    currentPNPLocalCruxPacket.covers .fixedFieldBadCell := by
  exact v13FieldedBadCellCoverage

theorem current_pnp_packet_v13_field_refinement_bad_cell_covered_regression :
    currentPNPLocalCruxPacket.covers .fieldRefinementOfBadCell := by
  exact v13FieldRefinementBadCellCoverage

theorem current_pnp_packet_v13_cd_evidence_normalization_covered_regression :
    currentPNPLocalCruxPacket.covers .cdEvidenceNormalization := by
  exact cdEvidenceNormalization_covered_currentPNPLocalCruxPacket

theorem v13_evidence_normalization_toy_residual_blocks_regression :
    ¬ v13ToyEvidenceSurface.NormalizesNonNeutral ∧
      v13ToyEvidenceSurface.PositiveResidualScore v13ToyEvidenceScore ∧
      ¬ v13ToyEvidenceSurface.PositiveAtomsCovered v13ToyEvidenceScore := by
  exact v13EvidenceNormalizationCoverage_anchor_toyResidual_blocks

theorem current_pnp_packet_v13_trace_capture_factorization_covered_regression :
    currentPNPLocalCruxPacket.covers .traceCaptureFactorization := by
  exact traceCaptureFactorization_covered_currentPNPLocalCruxPacket

instance : Fintype V13ToyTraceState where
  elems := {.left, .right}
  complete := by
    intro s
    cases s <;> simp

noncomputable instance : Fintype (Subtype v13CollapsedTraceSurface.targetRelevant) :=
  Fintype.ofEquiv V13ToyTraceState
    (Equiv.subtypeUnivEquiv (fun _ => trivial)).symm

theorem v13_trace_capture_collapsed_trace_blocks_regression :
    ¬ v13CollapsedTraceSurface.ObserverTraceDecodable v13ToyTraceObserver ∧
      v13CollapsedTraceSurface.RelevantTraceCollision ∧
      ¬ v13CollapsedTraceSurface.CapturesAllBoolObservers := by
  exact v13TraceCaptureFactorizationCoverage_anchor_collapsedTrace_blocks

theorem v13_trace_capture_collapsed_random_trace_blocks_regression :
    v13CollapsedTraceSurface.RandomObserverSameTraceConflict
        v13ToyRandomTraceObserver ∧
      ¬ v13CollapsedTraceSurface.RandomObserverTraceDecodable
        v13ToyRandomTraceObserver := by
  exact v13TraceCaptureFactorizationCoverage_anchor_collapsedRandomTrace_blocks

theorem v13_trace_capture_collapsed_trace_cardinality_budget_regression :
    (Fintype.card Unit <
        Fintype.card (Subtype v13CollapsedTraceSurface.targetRelevant)) ∧
      ¬ v13CollapsedTraceSurface.CapturesAllBoolObservers := by
  have hcard :
      Fintype.card (Subtype v13CollapsedTraceSurface.targetRelevant) =
        Fintype.card V13ToyTraceState := by
    exact Fintype.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial)
  refine ⟨?_, ?_⟩
  · rw [hcard]
    decide
  · rcases
      (traceCaptureFactorization_covered_currentPNPLocalCruxPacket :
        V13TraceCaptureFactorizationCoverage) with
      ⟨_, _, _, _, hsmallTrace, _, _⟩
    exact
      hsmallTrace v13CollapsedTraceSurface
        (by
          rw [hcard]
          decide)

theorem v13_trace_capture_collapsed_trace_image_budget_regression :
    (2 ^ Fintype.card Unit <
        2 ^ Fintype.card (Subtype v13CollapsedTraceSurface.targetRelevant)) ∧
      ¬ v13CollapsedTraceSurface.CapturesAllBoolObservers := by
  have hcard :
      Fintype.card (Subtype v13CollapsedTraceSurface.targetRelevant) =
        Fintype.card V13ToyTraceState := by
    exact Fintype.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial)
  refine ⟨?_, ?_⟩
  · rw [hcard]
    decide
  · rcases
      (traceCaptureFactorization_covered_currentPNPLocalCruxPacket :
        V13TraceCaptureFactorizationCoverage) with
      ⟨_, _, _, _, _, _, hsmallImage⟩
    exact
      hsmallImage v13CollapsedTraceSurface
        (by
          rw [hcard]
          decide)

theorem current_pnp_packet_v13_atomic_evidence_budget_covered_regression :
    currentPNPLocalCruxPacket.covers .atomicEvidenceBudget := by
  exact atomicEvidenceBudget_covered_currentPNPLocalCruxPacket

theorem v13_atomic_evidence_budget_double_counted_atom_blocks_regression :
    v13DoubleCountedBudgetSurface.atomBudget = 1 ∧
      v13DoubleCountedBudgetSurface.coordinateSummedCost = 2 ∧
      ¬ v13DoubleCountedBudgetSurface.NoDoubleCounting ∧
      v13DoubleCountedBudgetSurface.atomBudget <
        v13DoubleCountedBudgetSurface.coordinateSummedCost := by
  exact v13AtomicEvidenceBudgetCoverage_anchor_doubleCountedAtom_blocks

theorem v13_atomic_evidence_budget_cancellation_blocks_regression :
    v13CancellationBudgetSurface.coordinateSummedCost =
        v13CancellationBudgetSurface.atomBudget ∧
      (v13CancellationBudgetSurface.NoDoubleCounting ↔
        v13CancellationBudgetSurface.AllPositiveCostAtomsCharged) ∧
      ¬ v13CancellationBudgetSurface.ExactnessSideConditions := by
  exact v13AtomicEvidenceBudgetCoverage_anchor_cancellation_blocks

theorem
    current_pnp_packet_v13_atomic_evidence_budget_equivalence_only_not_enough_regression :
    ¬ ∀ {Coord Atom : Type} [Fintype Coord] [Fintype Atom]
        (S : V13AtomicEvidenceBudgetSurface Coord Atom) [DecidableRel S.charges],
        S.coordinateSummedCost = S.atomBudget →
          (S.NoDoubleCounting ↔ S.AllPositiveCostAtomsCharged) →
          S.ExactnessSideConditions := by
  have hcover : V13AtomicEvidenceBudgetCoverage :=
    atomicEvidenceBudget_covered_currentPNPLocalCruxPacket
  exact hcover.2.2

theorem current_pnp_packet_v13_accei_envelope_product_covered_regression :
    currentPNPLocalCruxPacket.covers .acceiEnvelopeProduct := by
  exact acceiEnvelopeProduct_covered_currentPNPLocalCruxPacket

theorem v13_accei_envelope_product_good_pruning_coverage_regression
    {ι : Type u} [Fintype ι] (η : ι → ℕ) (threshold budget : ℕ)
    (hbudget : (∑ i, η i) ≤ budget) :
    Fintype.card ι - budget / (threshold + 1) ≤
        acceiGoodCount ι η threshold ∧
      (budget / (threshold + 1) < Fintype.card ι →
        ∃ i : ι, η i ≤ threshold) := by
  exact
    ⟨v13ACCEIEnvelopeProductCoverage.{u}.2.1 η threshold budget hbudget,
      v13ACCEIEnvelopeProductCoverage.{u}.2.2.1
        η threshold budget hbudget⟩

theorem v13_accei_envelope_product_markov_sharpness_coverage_regression
    (threshold : ℕ) :
    acceiBadCount Bool (oneGoodOneBadACCEIEnvelope threshold) threshold *
        (threshold + 1) =
        ∑ b : Bool, oneGoodOneBadACCEIEnvelope threshold b ∧
      Fintype.card Bool - (threshold + 1) / (threshold + 1) =
          acceiGoodCount Bool (oneGoodOneBadACCEIEnvelope threshold) threshold ∧
        ¬ ∀ b : Bool, oneGoodOneBadACCEIEnvelope threshold b ≤ threshold := by
  exact
    ⟨v13ACCEIEnvelopeProductCoverage.{0}.2.2.2.1 threshold,
      v13ACCEIEnvelopeProductCoverage.{0}.2.2.2.2.1 threshold⟩

theorem finite_coin_stack_under_same_source_finite_count_regression :
    currentPNPLocalCruxPacket.covers .sameSourceFiniteCountApproximation := by
  exact finiteCoinStack_under_sameSourceFiniteCountApproximation

theorem current_pnp_packet_approximate_decorrelation_uncovered_regression :
    ¬ currentPNPLocalCruxPacket.covers .approximateDecorrelation := by
  exact approximateDecorrelation_uncovered_currentPNPLocalCruxPacket

theorem finite_coin_stack_broad_randomized_residual_uncovered_regression :
    ¬ currentPNPLocalCruxPacket.covers .randomizedResidual := by
  exact finiteCoinStack_does_not_cover_randomizedResidual

theorem randomized_residual_subrepair_stack_broad_randomized_residual_uncovered_regression :
    ¬ currentPNPLocalCruxPacket.covers .randomizedResidual := by
  exact randomizedResidualSubrepairStack_does_not_cover_randomizedResidual

theorem finite_coin_stack_broad_residual_side_information_uncovered_regression :
    ¬ currentPNPLocalCruxPacket.covers .residualSideInformation := by
  exact finiteCoinStack_does_not_cover_residualSideInformation

theorem residual_side_information_subrepair_stack_broad_residual_side_information_uncovered_regression :
    ¬ currentPNPLocalCruxPacket.covers .residualSideInformation := by
  exact residualSideInformationSubrepairStack_does_not_cover_residualSideInformation

theorem finite_coin_stack_broad_approximate_decorrelation_uncovered_regression :
    ¬ currentPNPLocalCruxPacket.covers .approximateDecorrelation := by
  exact finiteCoinStack_does_not_cover_approximateDecorrelation

theorem finite_coin_stack_broad_kpoly_bridge_uncovered_regression :
    ¬ currentPNPLocalCruxPacket.covers .kpolyCompressionBridge := by
  exact finiteCoinStack_does_not_cover_kpolyCompressionBridge

theorem kpoly_subrepair_stack_broad_kpoly_bridge_uncovered_regression :
    ¬ currentPNPLocalCruxPacket.covers .kpolyCompressionBridge := by
  exact kpolySubrepairStack_does_not_cover_kpolyCompressionBridge

theorem current_pnp_next_marginal_target_uncovered_regression :
    ¬ currentPNPLocalCruxPacket.covers currentPNPNextMarginalTarget := by
  exact currentPNPNextMarginalTarget_uncovered

theorem current_pnp_missing_next_marginal_target_blocks_stop_grade_regression
    {packet : PNPCruxPacket}
    (hmiss : ¬ packet.covers currentPNPNextMarginalTarget) :
    ¬ packet.StopGrade := by
  exact not_stopGrade_of_not_covers_currentPNPNextMarginalTarget hmiss

theorem current_pnp_next_marginal_target_mem_uncovered_regression :
    currentPNPNextMarginalTarget ∈ currentPNPUncoveredRepairClasses := by
  exact currentPNPNextMarginalTarget_mem_uncovered

theorem current_pnp_next_marginal_target_mem_finite_coin_uncovered_regression :
    currentPNPNextMarginalTarget ∈ finiteCoinStackUncoveredBroadRepairClasses := by
  exact currentPNPNextMarginalTarget_mem_finiteCoin_uncovered_broad

theorem global_weakness_distinction_family_not_surjective_regression
    {U : Type u} [Fintype U] [DecidableEq U] [Nontrivial U]
    {Q : Type v} [Monoid Q] [CompleteLattice Q]
    (ev : GSLTEvidence U Q) {Index : Type*} {predict : Index → U → Bool}
    (hfamily : FamilyFactorsThroughDistinctionWeakness ev predict) :
    ¬ Function.Surjective predict := by
  exact
    globalWeaknessCoverage_anchor_distinction_family_not_surjective
      ev hfamily

theorem global_weakness_nonDistinction_family_not_surjective_regression
    {U : Type u} [Fintype U] [DecidableEq U] [Nontrivial U]
    {Q : Type v} [Monoid Q] [CompleteLattice Q]
    (ev : GSLTEvidence U Q) {Index : Type*} {predict : Index → U → Bool}
    (hfamily : FamilyFactorsThroughNonDistinctionWeakness ev predict) :
    ¬ Function.Surjective predict := by
  exact
    globalWeaknessCoverage_anchor_nonDistinction_family_not_surjective
      ev hfamily

theorem invariant_score_anchor_score_support_weight_symmetric_zero_signal_regression
    {α U : Type*} [Fintype α]
    (τ : α → α) (u : α → U) (y : α → Bool) (w : α → ℕ)
    (score : U → ℤ)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hsym : ∀ x, score (u x) ≠ 0 → w (τ x) = w x) :
    ∑ x : α, signedScoreContribution u y w score x = 0 := by
  exact
    invariantScoreCoverage_anchor_score_support_weight_symmetric_zero_signal
      τ u y w score hτ hu hy hsym

theorem invariant_score_anchor_nonzero_signal_exposes_weight_asymmetric_score_point_regression
    {α U : Type*} [Fintype α]
    (τ : α → α) (u : α → U) (y : α → Bool) (w : α → ℕ)
    (score : U → ℤ)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hsignal :
      (∑ x : α, signedScoreContribution u y w score x) ≠ 0) :
    ∃ x, w x ≠ w (τ x) ∧ score (u x) ≠ 0 := by
  exact
    invariantScoreCoverage_anchor_nonzero_signal_exposes_weight_asymmetric_score_point
      τ u y w score hτ hu hy hsignal

theorem asymmetry_budget_anchor_support_inside_symmetric_slice_blocks_strict_advantage_regression
    {α U : Type*} [Fintype α]
    (τ : α → α) (p : α → Prop) [DecidablePred p]
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool)
    (hτ : Function.Involutive τ)
    (hp : ∀ x, p x → p (τ x))
    (hu : ∀ x, p x → u (τ x) = u x)
    (hy : ∀ x, p x → y (τ x) = !(y x))
    (hw : ∀ x, p x → w (τ x) = w x)
    (hsupport : ∀ x, 0 < w x → p x) :
    ¬ weightedTotalMass w < 2 * weightedCorrectMass u y w h := by
  exact
    asymmetryBudgetCoverage_anchor_support_inside_symmetric_slice_blocks_strict_advantage
      τ p u y w h hτ hp hu hy hw hsupport

theorem asymmetry_budget_anchor_strict_advantage_exposes_outside_support_regression
    {α U : Type*} [Fintype α]
    (τ : α → α) (p : α → Prop) [DecidablePred p]
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool)
    (hτ : Function.Involutive τ)
    (hp : ∀ x, p x → p (τ x))
    (hu : ∀ x, p x → u (τ x) = u x)
    (hy : ∀ x, p x → y (τ x) = !(y x))
    (hw : ∀ x, p x → w (τ x) = w x)
    (hadv : weightedTotalMass w < 2 * weightedCorrectMass u y w h) :
    ∃ x, 0 < w x ∧ ¬ p x := by
  exact
    asymmetryBudgetCoverage_anchor_strict_advantage_exposes_outside_support
      τ p u y w h hτ hp hu hy hw hadv

theorem residual_side_information_anchor_collision_blocks_source_decoder_regression
    {Ω Base Side : Type*} {base : Ω → Base} {side : Ω → Side}
    {x y : Ω} (hbase : base x = base y) (hside : side x ≠ side y) :
    ¬ SideInfoDeterminedBy base side := by
  exact
    residualSideInformationCoverage_anchor_collision_blocks_source_decoder
      hbase hside

theorem residual_side_information_anchor_collision_blocks_source_predicate_regression
    {Ω Base Side : Type*} {base : Ω → Base} {side : Ω → Side}
    {x y : Ω} (hbase : base x = base y) (hside : side x ≠ side y) :
    ¬ SourceOnlyPredicateCapturesSideEq base side (side x) := by
  exact
    residualSideInformationCoverage_anchor_collision_blocks_source_predicate
      hbase hside

theorem residual_side_information_anchor_collision_blocks_source_boolean_classifier_regression
    {Ω Base : Type*} {base : Ω → Base} {target : Ω → Bool}
    {x y : Ω} (hbase : base x = base y) (htarget : target x ≠ target y) :
    ¬ SourceOnlyBooleanClassifier base target := by
  exact
    residualSideInformationCoverage_anchor_collision_blocks_source_boolean_classifier
      hbase htarget

theorem residual_side_information_anchor_toy_collision_regression :
    SideInfoCollisionOverBase residualSideInfoToyBase residualSideInfoToySide ∧
      ¬ SideInfoDeterminedBy residualSideInfoToyBase residualSideInfoToySide ∧
      ¬ SourceOnlyPredicateCapturesSideEq
        residualSideInfoToyBase residualSideInfoToySide false ∧
      ¬ SourceOnlyBooleanClassifier
      residualSideInfoToyBase residualSideInfoToySide := by
  exact residualSideInformationCoverage_anchor_toy_collision

theorem residual_side_information_anchor_source_determined_invariant_unresolved_regression
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (hbase : ∀ x, base (τ x) = base x)
    (hdet : SideInfoDeterminedBy base side) :
    ∀ x, side (τ x) = side x := by
  exact
    residualSideInformationCoverage_anchor_source_determined_invariant_unresolved
      τ base side hbase hdet

theorem residual_side_information_anchor_source_determined_zero_resolvedMass_regression
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side) (w : α → ℕ)
    (hbase : ∀ x, base (τ x) = base x)
    (hdet : SideInfoDeterminedBy base side) :
    resolvedMass τ side w = 0 := by
  exact
    residualSideInformationCoverage_anchor_source_determined_zero_resolvedMass
      τ base side w hbase hdet

theorem residual_side_information_anchor_source_determined_no_positive_advantage_regression
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hdet : SideInfoDeterminedBy base side)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x) :
    ¬ 0 < doubledAdvantage (fun x => (base x, side x)) y w h := by
  exact
    residualSideInformationCoverage_anchor_source_determined_no_positive_advantage
      τ base side y w h hτ hbase hdet hy hw

theorem residual_side_information_anchor_positive_advantage_positive_resolved_mass_regression
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv : 0 < doubledAdvantage (fun x => (base x, side x)) y w h) :
    0 < resolvedMass τ side w := by
  exact
    residualSideInformationCoverage_anchor_positive_advantage_forces_positive_resolvedMass
      τ base side y w h hτ hbase hy hw hadv

theorem residual_side_information_anchor_strict_half_advantage_positive_resolved_mass_regression
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv :
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h) :
    0 < resolvedMass τ side w := by
  exact
    residualSideInformationCoverage_anchor_strict_half_advantage_forces_positive_resolvedMass
      τ base side y w h hτ hbase hy hw hadv

theorem residual_side_information_anchor_positive_resolved_mass_same_base_collision_regression
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side) (w : α → ℕ)
    (hbase : ∀ x, base (τ x) = base x)
    (hmass : 0 < resolvedMass τ side w) :
    ∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x := by
  exact
    residualSideInformationCoverage_anchor_positive_resolvedMass_witnesses_same_base_residual_collision
      τ base side w hbase hmass

theorem residual_side_information_anchor_positive_resolved_mass_supported_obstruction_package_regression
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side) (w : α → ℕ)
    (hbase : ∀ x, base (τ x) = base x)
    (hmass : 0 < resolvedMass τ side w) :
    ¬ SideInfoDeterminedBy base side ∧
      PositiveWeightSideInfoCollisionOverBase base side w ∧
      (∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
      (∃ x, 0 < w x ∧
        ¬ SourceOnlyPredicateCapturesSideEq base side (side x)) := by
  exact
    residualSideInformationCoverage_anchor_positive_resolvedMass_forces_supported_obstruction_package
      τ base side w hbase hmass

theorem residual_side_information_anchor_exact_post_switch_active_orbit_pure_package_regression
    {Z : Type*} [Fintype Z] (z0 : Z) :
    0 < resolvedMass tiInputMap
        (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b)
        (activeOrbitWeight z0) ∧
      ¬ SideInfoDeterminedBy invariantVisibleData
          (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b) ∧
      PositiveWeightSideInfoCollisionOverBase invariantVisibleData
        (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b)
        (activeOrbitWeight z0) ∧
      (∃ u : ExactVisiblePostSwitchSurface Z 1,
        0 < activeOrbitWeight z0 u ∧
          invariantVisibleData (tiInputMap u) = invariantVisibleData u ∧
          (tiInputMap u).b ≠ u.b) ∧
      (∃ u : ExactVisiblePostSwitchSurface Z 1,
        0 < activeOrbitWeight z0 u ∧
          ¬ SourceOnlyPredicateCapturesSideEq invariantVisibleData
            (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b) (u.b)) := by
  exact
    residualSideInformationCoverage_anchor_exactPostSwitch_activeOrbit_pure_residual_package
      (Z := Z) z0

theorem residual_side_information_anchor_exact_post_switch_active_orbit_prediction_witness_regression
    {Z : Type*} [Fintype Z] (z0 : Z) :
    (∀ u : ExactVisiblePostSwitchSurface Z 1,
      invariantVisibleData (tiInputMap u) = invariantVisibleData u) ∧
    (∀ u : ExactVisiblePostSwitchSurface Z 1,
      activeOrbitWeight z0 (tiInputMap u) = activeOrbitWeight z0 u) ∧
    (∀ u : ExactVisiblePostSwitchSurface Z 1, 0 < activeOrbitWeight z0 u →
      activeOrbitTarget (tiInputMap u) = !(activeOrbitTarget u)) ∧
    0 <
      doubledAdvantage
        activeOrbitFeatures
        activeOrbitTarget
        (activeOrbitWeight z0)
        activeOrbitClassifier ∧
    ∃ u : ExactVisiblePostSwitchSurface Z 1,
      0 < activeOrbitWeight z0 u ∧
      activeOrbitClassifier (activeOrbitFeatures (tiInputMap u)) ≠
        activeOrbitClassifier (activeOrbitFeatures u) := by
  exact
    residualSideInformationCoverage_anchor_exactPostSwitch_activeOrbit_prediction_witness
      (Z := Z) z0

theorem residual_side_information_anchor_positive_advantage_forces_not_source_determined_regression
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv : 0 < doubledAdvantage (fun x => (base x, side x)) y w h) :
    ¬ SideInfoDeterminedBy base side := by
  exact
    residualSideInformationCoverage_anchor_positive_advantage_forces_not_source_determined
      τ base side y w h hτ hbase hy hw hadv

theorem residual_side_information_anchor_strict_half_advantage_forces_not_source_determined_regression
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv :
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h) :
    ¬ SideInfoDeterminedBy base side := by
  exact
    residualSideInformationCoverage_anchor_strict_half_advantage_forces_not_source_determined
      τ base side y w h hτ hbase hy hw hadv

theorem residual_side_information_anchor_positive_advantage_witnesses_same_base_collision_regression
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv : 0 < doubledAdvantage (fun x => (base x, side x)) y w h) :
    ∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x := by
  exact
    residualSideInformationCoverage_anchor_positive_advantage_witnesses_same_base_residual_collision
      τ base side y w h hτ hbase hy hw hadv

theorem residual_side_information_anchor_positive_advantage_positiveWeight_collision_regression
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv : 0 < doubledAdvantage (fun x => (base x, side x)) y w h) :
    PositiveWeightSideInfoCollisionOverBase base side w := by
  exact
    residualSideInformationCoverage_anchor_positive_advantage_positiveWeight_collision
      τ base side y w h hτ hbase hy hw hadv

theorem residual_side_information_anchor_positive_advantage_blocks_supported_source_predicate_regression
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv : 0 < doubledAdvantage (fun x => (base x, side x)) y w h) :
    ∃ x, 0 < w x ∧
      ¬ SourceOnlyPredicateCapturesSideEq base side (side x) := by
  exact
    residualSideInformationCoverage_anchor_positive_advantage_blocks_supported_source_predicate
      τ base side y w h hτ hbase hy hw hadv

theorem residual_side_information_anchor_supported_source_predicates_no_positive_advantage_regression
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hsource :
      ∀ x, 0 < w x → SourceOnlyPredicateCapturesSideEq base side (side x)) :
    ¬ 0 < doubledAdvantage (fun x => (base x, side x)) y w h := by
  exact
    residualSideInformationCoverage_anchor_supported_source_predicates_no_positive_advantage
      τ base side y w h hτ hbase hy hw hsource

theorem residual_side_information_anchor_supportwise_source_classifier_no_positive_advantage_regression
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hsource : SupportwiseSourceOnlyPairClassifier base side w h) :
    ¬ 0 < doubledAdvantage (fun x => (base x, side x)) y w h := by
  exact
    residualSideInformationCoverage_anchor_supportwise_source_classifier_no_positive_advantage
      τ base side y w h hτ hbase hy hw hsource

theorem residual_side_information_anchor_strict_half_advantage_witnesses_same_base_collision_regression
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv :
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h) :
    ∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x := by
  exact
    residualSideInformationCoverage_anchor_strict_half_advantage_witnesses_same_base_residual_collision
      τ base side y w h hτ hbase hy hw hadv

theorem residual_side_information_anchor_strict_half_advantage_positiveWeight_collision_regression
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv :
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h) :
    PositiveWeightSideInfoCollisionOverBase base side w := by
  exact
    residualSideInformationCoverage_anchor_strict_half_advantage_positiveWeight_collision
      τ base side y w h hτ hbase hy hw hadv

theorem residual_side_information_anchor_strict_half_advantage_blocks_supported_source_predicate_regression
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv :
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h) :
    ∃ x, 0 < w x ∧
      ¬ SourceOnlyPredicateCapturesSideEq base side (side x) := by
  exact
    residualSideInformationCoverage_anchor_strict_half_advantage_blocks_supported_source_predicate
      τ base side y w h hτ hbase hy hw hadv

theorem residual_side_information_anchor_supported_source_predicates_no_strict_half_advantage_regression
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hsource :
      ∀ x, 0 < w x → SourceOnlyPredicateCapturesSideEq base side (side x)) :
    ¬ weightedTotalMass w <
      2 * weightedCorrectMass (fun x => (base x, side x)) y w h := by
  exact
    residualSideInformationCoverage_anchor_supported_source_predicates_no_strict_half_advantage
      τ base side y w h hτ hbase hy hw hsource

theorem residual_side_information_anchor_supportwise_source_classifier_no_strict_half_advantage_regression
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hsource : SupportwiseSourceOnlyPairClassifier base side w h) :
    ¬ weightedTotalMass w <
      2 * weightedCorrectMass (fun x => (base x, side x)) y w h := by
  exact
    residualSideInformationCoverage_anchor_supportwise_source_classifier_no_strict_half_advantage
      τ base side y w h hτ hbase hy hw hsource

theorem residual_side_information_anchor_positive_advantage_prediction_separation_regression
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv : 0 < doubledAdvantage (fun x => (base x, side x)) y w h) :
    ∃ x, 0 < w x ∧
      h (base (τ x), side (τ x)) ≠ h (base x, side x) := by
  exact
    residualSideInformationCoverage_anchor_positive_advantage_prediction_separation
      τ base side y w h hτ hbase hy hw hadv

theorem residual_side_information_anchor_strict_half_advantage_prediction_separation_regression
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv :
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h) :
    ∃ x, 0 < w x ∧
      h (base (τ x), side (τ x)) ≠ h (base x, side x) := by
  exact
    residualSideInformationCoverage_anchor_strict_half_advantage_prediction_separation
      τ base side y w h hτ hbase hy hw hadv

theorem residual_side_information_anchor_positive_advantage_supported_obstruction_package_regression
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv : 0 < doubledAdvantage (fun x => (base x, side x)) y w h) :
    0 < resolvedMass τ side w ∧
      ¬ SideInfoDeterminedBy base side ∧
      ¬ SupportwiseSourceOnlyPairClassifier base side w h ∧
      (∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
      (∃ x, 0 < w x ∧
        ¬ SourceOnlyPredicateCapturesSideEq base side (side x)) ∧
      (∃ x, 0 < w x ∧
        h (base (τ x), side (τ x)) ≠ h (base x, side x)) := by
  exact
    residualSideInformationCoverage_anchor_positive_advantage_forces_supported_obstruction_package
      τ base side y w h hτ hbase hy hw hadv

theorem residual_side_information_anchor_strict_half_advantage_supported_obstruction_package_regression
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv :
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h) :
    0 < resolvedMass τ side w ∧
      ¬ SideInfoDeterminedBy base side ∧
      ¬ SupportwiseSourceOnlyPairClassifier base side w h ∧
      (∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
      (∃ x, 0 < w x ∧
        ¬ SourceOnlyPredicateCapturesSideEq base side (side x)) ∧
      (∃ x, 0 < w x ∧
        h (base (τ x), side (τ x)) ≠ h (base x, side x)) := by
  exact
    residualSideInformationCoverage_anchor_strict_half_advantage_forces_supported_obstruction_package
      τ base side y w h hτ hbase hy hw hadv

theorem side_channel_anchor_supportwise_unresolved_no_positive_advantage_regression
    {α U V : Type*} [Fintype α]
    (τ : α → α) (u : α → U) (v : α → V)
    (y : α → Bool) (w : α → ℕ) (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hunresolved : ∀ x, 0 < w x → v (τ x) = v x) :
    ¬ 0 < doubledAdvantage (fun x => (u x, v x)) y w h := by
  exact
    sideChannelCoverage_anchor_supportwise_unresolved_no_positive_advantage
      τ u v y w h hτ hu hy hw hunresolved

theorem side_channel_anchor_positive_advantage_resolution_witness_regression
    {α U V : Type*} [Fintype α]
    (τ : α → α) (u : α → U) (v : α → V)
    (y : α → Bool) (w : α → ℕ) (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv : 0 < doubledAdvantage (fun x => (u x, v x)) y w h) :
    ∃ x, 0 < w x ∧ v (τ x) ≠ v x := by
  exact
    sideChannelCoverage_anchor_positive_advantage_resolution_witness
      τ u v y w h hτ hu hy hw hadv

theorem side_channel_anchor_strict_half_accuracy_advantage_resolution_witness_regression
    {α U V : Type*} [Fintype α]
    (τ : α → α) (u : α → U) (v : α → V)
    (y : α → Bool) (w : α → ℕ) (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv :
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (u x, v x)) y w h) :
    ∃ x, 0 < w x ∧ v (τ x) ≠ v x := by
  exact
    sideChannelCoverage_anchor_strict_half_accuracy_advantage_resolution_witness
      τ u v y w h hτ hu hy hw hadv

theorem post_switch_fork_anchor_positive_advantage_b_resolution_witness_regression
    {Z : Type*} [Fintype Z] {k : ℕ}
    (y : PostSwitchInput Z k → Bool) (w : PostSwitchInput Z k → ℕ)
    (h : (Z × BitVec k) × BitVec k → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hadv : 0 < doubledAdvantage (fun u => (invariantProjection u, u.b)) y w h) :
    ∃ u : PostSwitchInput Z k, 0 < w u ∧ (tiInputMap u).b ≠ u.b := by
  exact
    postSwitchForkCoverage_anchor_positive_advantage_b_resolution_witness
      y w h hy hw hadv

theorem post_switch_fork_anchor_positive_advantage_nonzero_column_witness_regression
    {Z : Type*} [Fintype Z] {k : ℕ}
    (y : PostSwitchInput Z k → Bool) (w : PostSwitchInput Z k → ℕ)
    (h : (Z × BitVec k) × BitVec k → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hadv : 0 < doubledAdvantage (fun u => (invariantProjection u, u.b)) y w h) :
    ∃ u : PostSwitchInput Z k, 0 < w u ∧ nonzeroColumn u.a := by
  exact
    postSwitchForkCoverage_anchor_positive_advantage_nonzeroColumn_witness
      y w h hy hw hadv

theorem randomized_residual_anchor_supportwise_unresolved_no_positive_advantage_regression
    {α Coin U V : Type*} [Fintype α] [Fintype Coin]
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
  exact
    randomizedResidualCoverage_anchor_supportwise_unresolved_no_positive_advantage
      τ u v y w coinWeight h hτ hu hy hw hunresolved

theorem randomized_residual_anchor_positive_advantage_witnesses_resolving_coin_regression
    {α Coin U V : Type*} [Fintype α] [Fintype Coin]
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
    ∃ x c, 0 < w x * coinWeight c ∧ v (τ x) c ≠ v x c := by
  exact
    randomizedResidualCoverage_anchor_positive_advantage_witnesses_resolving_coin
      τ u v y w coinWeight h hτ hu hy hw hadv

theorem randomized_residual_anchor_positive_advantage_witnesses_deterministic_coin_slice_regression
    {α Coin U V : Type*} [Fintype α] [Fintype Coin]
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
    ∃ c, 0 < coinWeight c ∧ 0 < resolvedMass τ (fun x => v x c) w := by
  exact
    randomizedResidualCoverage_anchor_positive_advantage_witnesses_deterministic_coin_slice
      τ u v y w coinWeight h hτ hu hy hw hadv

theorem randomized_residual_anchor_post_switch_positive_advantage_witnesses_resolving_coin_regression
    {Z Coin V : Type*} {k : ℕ} [Fintype Z] [Fintype Coin]
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
    ∃ u c, 0 < w u * coinWeight c ∧ v (tiInputMap u) c ≠ v u c := by
  exact
    randomizedResidualCoverage_anchor_postSwitch_positive_advantage_witnesses_resolving_coin
      v y w coinWeight h hy hw hadv

theorem randomized_residual_anchor_post_switch_positive_advantage_witnesses_deterministic_coin_slice_regression
    {Z Coin V : Type*} {k : ℕ} [Fintype Z] [Fintype Coin]
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
      0 < resolvedMass tiInputMap (fun u => v u c) w := by
  exact
    randomizedResidualCoverage_anchor_postSwitch_positive_advantage_witnesses_deterministic_coin_slice
      v y w coinWeight h hy hw hadv

theorem kpoly_anchor_clocked_realization_regression
    {Z : Type*} {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} :
    (∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F) ↔
      ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s := by
  exact
    kpolyCoverage_anchor_clockedRealization_iff_exactVisibleCompressionTarget
      (G := G) (s := s) (clock := clock)

theorem kpoly_anchor_full_ab_rule_not_raw_decision_list_regression
    {k : ℕ} (hk : 0 < k) :
    ¬ RealizedByABDecisionListFamily (k := k) (fullABRuleFamily k) := by
  exact kpolyCoverage_anchor_fullABRule_not_rawDecisionList_of_pos
    (k := k) hk

theorem kpoly_anchor_full_exact_ab_rule_not_raw_exact_decision_list_regression
    (Z : Type*) [Inhabited Z] {k : ℕ} (hk : 0 < k) :
    ¬ RealizedByRawExactABDecisionListFamily (Z := Z) (k := k)
        (fullExactABRuleFamily Z k) := by
  exact kpolyCoverage_anchor_fullExactABRule_not_rawExactDecisionList_of_pos
    (Z := Z) (k := k) hk

theorem kpoly_anchor_full_ab_rule_not_shared_affine_feature_regression
    {r k : ℕ} (features : Fin r → AffineColumnCode (k + k))
    (hs : 2 ^ r < 2 ^ (2 * k)) :
    ¬ RealizedBySharedABAffineFeatureFamily (r := r) (k := k) features
        (fullABRuleFamily k) := by
  exact kpolyCoverage_anchor_fullABRule_not_sharedAffineFeature_of_lt_cardFormula
    (r := r) (k := k) features hs

theorem kpoly_anchor_full_ab_rule_not_shared_sparse_threshold_regression
    {r k : ℕ} (features : Fin r → AffineColumnCode (k + k))
    (hs : 2 * r < 2 ^ (2 * k)) :
    ¬ RealizedBySharedABSparseThresholdAffineFamily (r := r) (k := k) features
        (fullABRuleFamily k) := by
  exact kpolyCoverage_anchor_fullABRule_not_sharedSparseThreshold_of_lt_cardFormula
    (r := r) (k := k) features hs

theorem kpoly_anchor_full_ab_rule_not_shared_decision_list_regression
    {r k : ℕ} (features : Fin r → AffineColumnCode (k + k))
    (hs : r + 1 < 2 ^ (2 * k)) :
    ¬ RealizedBySharedABAffineDecisionListFamily (r := r) (k := k) features
        (fullABRuleFamily k) := by
  exact kpolyCoverage_anchor_fullABRule_not_sharedDecisionList_of_lt_cardFormula
    (r := r) (k := k) features hs

theorem kpoly_anchor_full_exact_ab_rule_not_shared_exact_affine_feature_regression
    (Z : Type*) [Inhabited Z] {r k : ℕ}
    (features : Fin r → AffineColumnCode (k + k))
    (hs : 2 ^ r < 2 ^ (2 * k)) :
    ¬ RealizedBySharedExactABAffineFeatureFamily (Z := Z) (r := r) (k := k)
        features (fullExactABRuleFamily Z k) := by
  exact kpolyCoverage_anchor_fullExactABRule_not_sharedExactAffineFeature_of_lt_cardFormula
    (Z := Z) (r := r) (k := k) features hs

theorem kpoly_anchor_full_exact_ab_rule_not_shared_exact_sparse_threshold_regression
    (Z : Type*) [Inhabited Z] {r k : ℕ}
    (features : Fin r → AffineColumnCode (k + k))
    (hs : 2 * r < 2 ^ (2 * k)) :
    ¬ RealizedBySharedExactABSparseThresholdAffineFamily (Z := Z) (r := r) (k := k)
        features (fullExactABRuleFamily Z k) := by
  exact kpolyCoverage_anchor_fullExactABRule_not_sharedExactSparseThreshold_of_lt_cardFormula
    (Z := Z) (r := r) (k := k) features hs

theorem kpoly_anchor_full_exact_ab_rule_not_shared_exact_decision_list_regression
    (Z : Type*) [Inhabited Z] {r k : ℕ}
    (features : Fin r → AffineColumnCode (k + k))
    (hs : r + 1 < 2 ^ (2 * k)) :
    ¬ RealizedBySharedExactABAffineDecisionListFamily (Z := Z) (r := r) (k := k)
        features (fullExactABRuleFamily Z k) := by
  exact kpolyCoverage_anchor_fullExactABRule_not_sharedExactDecisionList_of_lt_cardFormula
    (Z := Z) (r := r) (k := k) features hs

theorem kpoly_anchor_not_shared_ab_affine_feature_of_injective_probe_regression
    {Probe : Type*} [Fintype Probe] {r k : ℕ} {Index : Type*}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hprobe : ∀ p, ∃ i, H.predict i = target p)
    (hcard : 2 ^ (2 ^ r) < Fintype.card Probe) :
    ¬ RealizedBySharedABAffineFeatureFamily (r := r) (k := k) features H := by
  exact
    kpolyCoverage_anchor_not_sharedABAffineFeature_of_injective_probe_of_lt_budgetImageCard
      target hinj hprobe hcard

theorem kpoly_anchor_not_shared_ab_sparse_threshold_of_injective_probe_regression
    {Probe : Type*} [Fintype Probe] {r k : ℕ} {Index : Type*}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hprobe : ∀ p, ∃ i, H.predict i = target p)
    (hcard : 2 ^ (2 * r) < Fintype.card Probe) :
    ¬ RealizedBySharedABSparseThresholdAffineFamily (r := r) (k := k) features H := by
  exact
    kpolyCoverage_anchor_not_sharedABSparseThreshold_of_injective_probe_of_lt_budgetImageCard
      target hinj hprobe hcard

theorem kpoly_anchor_not_shared_ab_decision_list_of_injective_probe_regression
    {Probe : Type*} [Fintype Probe] {r k : ℕ} {Index : Type*}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hprobe : ∀ p, ∃ i, H.predict i = target p)
    (hcard : 2 ^ (r + 1) < Fintype.card Probe) :
    ¬ RealizedBySharedABAffineDecisionListFamily (r := r) (k := k) features H := by
  exact
    kpolyCoverage_anchor_not_sharedABDecisionList_of_injective_probe_of_lt_budgetImageCard
      target hinj hprobe hcard

theorem kpoly_anchor_not_shared_exact_ab_affine_feature_of_factorsThrough_injective_probe_regression
    {Z Probe : Type*} [Inhabited Z] [Fintype Probe]
    {r k : ℕ} {Index : Type*}
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
    kpolyCoverage_anchor_not_sharedExactABAffineFeature_of_factorsThrough_ab_and_injective_probe_of_lt_budgetImageCard
      target hinj hprobe hcard hfactor

theorem kpoly_anchor_not_shared_exact_ab_sparse_threshold_of_factorsThrough_injective_probe_regression
    {Z Probe : Type*} [Inhabited Z] [Fintype Probe]
    {r k : ℕ} {Index : Type*}
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
    kpolyCoverage_anchor_not_sharedExactABSparseThreshold_of_factorsThrough_ab_and_injective_probe_of_lt_budgetImageCard
      target hinj hprobe hcard hfactor

theorem kpoly_anchor_not_shared_exact_ab_decision_list_of_factorsThrough_injective_probe_regression
    {Z Probe : Type*} [Inhabited Z] [Fintype Probe]
    {r k : ℕ} {Index : Type*}
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
    kpolyCoverage_anchor_not_sharedExactABDecisionList_of_factorsThrough_ab_and_injective_probe_of_lt_budgetImageCard
      target hinj hprobe hcard hfactor

theorem kpoly_anchor_not_exists_predict_eq_of_abVisibleInvariant_separating_rule_regression
    {Z : Type*} {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hinv : ABVisibleInvariant (Z := Z) (k := k) G)
    {rule : ExactVisiblePostSwitchSurface Z k → Bool}
    (hsep : ABFiberSeparatingRule (Z := Z) (k := k) rule) :
    ¬ ∃ i, G.predict i = rule := by
  exact
    kpolyCoverage_anchor_not_exists_predict_eq_of_abVisibleInvariant_of_abFiberSeparatingRule
      hinv hsep

theorem kpoly_anchor_not_exists_predict_eq_boolZProjectionRule_of_abVisibleInvariant_regression
    {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Bool k Index}
    (hinv : ABVisibleInvariant (Z := Bool) (k := k) G) :
    ¬ ∃ i, G.predict i = boolZProjectionRule (k := k) := by
  exact
    kpolyCoverage_anchor_not_exists_predict_eq_boolZProjectionRule_of_abVisibleInvariant
      hinv

theorem kpoly_anchor_exists_pos_mass_disagreement_of_abVisibleInvariant_predict_regression
    {Z : Type*} {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hinv : ABVisibleInvariant (Z := Z) (k := k) G)
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {target : ExactVisiblePostSwitchSurface Z k → Bool}
    (i : Index)
    {u v : ExactVisiblePostSwitchSurface Z k}
    (hab : abVisibleData u = abVisibleData v)
    (hsep : target u ≠ target v)
    (huμ : μ u ≠ 0) (hvμ : μ v ≠ 0) :
    ∃ x, μ x ≠ 0 ∧ G.predict i x ≠ target x := by
  exact
    kpolyCoverage_anchor_exists_pos_mass_disagreement_of_abVisibleInvariant_predict_of_abFiberSeparation
      hinv (μ := μ) (target := target) i hab hsep huμ hvμ

theorem kpoly_anchor_exists_pos_mass_disagreement_boolZProjectionRule_of_abVisibleInvariant_regression
    {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Bool k Index}
    (hinv : ABVisibleInvariant (Z := Bool) (k := k) G)
    {μ : PMF (ExactVisiblePostSwitchSurface Bool k)}
    (i : Index)
    (hfalse : μ ⟨false, default, default⟩ ≠ 0)
    (htrue : μ ⟨true, default, default⟩ ≠ 0) :
    ∃ x, μ x ≠ 0 ∧ G.predict i x ≠ boolZProjectionRule (k := k) x := by
  exact
    kpolyCoverage_anchor_exists_pos_mass_disagreement_boolZProjectionRule_of_abVisibleInvariant
      hinv (μ := μ) i hfalse htrue

theorem kpoly_anchor_agreementMass_lt_one_of_abVisibleInvariant_predict_regression
    {Z : Type*} [Fintype Z] {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hinv : ABVisibleInvariant (Z := Z) (k := k) G)
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {target : ExactVisiblePostSwitchSurface Z k → Bool}
    (i : Index)
    {u v : ExactVisiblePostSwitchSurface Z k}
    (hab : abVisibleData u = abVisibleData v)
    (hsep : target u ≠ target v)
    (huμ : μ u ≠ 0) (hvμ : μ v ≠ 0) :
    agreementMass μ target (G.predict i) < 1 := by
  exact
    kpolyCoverage_anchor_agreementMass_lt_one_of_abVisibleInvariant_predict_of_abFiberSeparation
      hinv (μ := μ) (target := target) i hab hsep huμ hvμ

theorem kpoly_anchor_agreementMass_lt_one_boolZProjectionRule_of_abVisibleInvariant_regression
    {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Bool k Index}
    (hinv : ABVisibleInvariant (Z := Bool) (k := k) G)
    {μ : PMF (ExactVisiblePostSwitchSurface Bool k)}
    (i : Index)
    (hfalse : μ ⟨false, default, default⟩ ≠ 0)
    (htrue : μ ⟨true, default, default⟩ ≠ 0) :
    agreementMass μ (boolZProjectionRule (k := k)) (G.predict i) < 1 := by
  exact
    kpolyCoverage_anchor_agreementMass_lt_one_boolZProjectionRule_of_abVisibleInvariant
      hinv (μ := μ) i hfalse htrue

theorem kpoly_anchor_not_exists_agreementMass_eq_one_of_abVisibleInvariant_regression
    {Z : Type*} [Fintype Z] {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hinv : ABVisibleInvariant (Z := Z) (k := k) G)
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {target : ExactVisiblePostSwitchSurface Z k → Bool}
    {u v : ExactVisiblePostSwitchSurface Z k}
    (hab : abVisibleData u = abVisibleData v)
    (hsep : target u ≠ target v)
    (huμ : μ u ≠ 0) (hvμ : μ v ≠ 0) :
    ¬ ∃ i, agreementMass μ target (G.predict i) = 1 := by
  exact
    kpolyCoverage_anchor_not_exists_agreementMass_eq_one_of_abVisibleInvariant_of_abFiberSeparation
      hinv (μ := μ) (target := target) hab hsep huμ hvμ

theorem kpoly_anchor_not_exists_agreementMass_eq_one_boolZProjectionRule_of_abVisibleInvariant_regression
    {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Bool k Index}
    (hinv : ABVisibleInvariant (Z := Bool) (k := k) G)
    {μ : PMF (ExactVisiblePostSwitchSurface Bool k)}
    (hfalse : μ ⟨false, default, default⟩ ≠ 0)
    (htrue : μ ⟨true, default, default⟩ ≠ 0) :
    ¬ ∃ i, agreementMass μ (boolZProjectionRule (k := k)) (G.predict i) = 1 := by
  exact
    kpolyCoverage_anchor_not_exists_agreementMass_eq_one_boolZProjectionRule_of_abVisibleInvariant
      hinv (μ := μ) hfalse htrue

theorem kpoly_anchor_not_surjective_predict_of_abVisibleInvariant_nontrivial_regression
    {Z : Type*} [Nontrivial Z] {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hinv : ABVisibleInvariant (Z := Z) (k := k) G) :
    ¬ Function.Surjective G.predict := by
  exact
    kpolyCoverage_anchor_not_surjective_predict_of_abVisibleInvariant_of_nontrivial
      hinv

theorem kpoly_anchor_exact_visible_compression_target_iff_finite_predictor_cover_regression
    {Z : Type*} {k s : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s ↔
      G.FinitePredictorCover (2 ^ s) := by
  exact kpolyCoverage_anchor_exactVisibleCompressionTarget_iff_finitePredictorCover

theorem kpoly_anchor_product_bound_only_bridge_iff_forall_semantic_finite_image_regression
    {Ω : Type u} {Z : Type v} [Fintype Ω] {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)} :
    ProductBoundOnlyExactVisibleCompressionBridge Ω Z k s hist items ↔
      ∀ {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index),
        ProductBoundSemanticFiniteImageBridge Ω Z k s hist items G := by
  exact
    kpolyCoverage_anchor_productBoundOnlyExactVisibleCompressionBridge_iff_forall_semanticFiniteImageBridge

theorem kpoly_anchor_fielded_switching_only_bridge_iff_forall_semantic_finite_image_regression
    {Ω : Type u} {Z : Type v} [Fintype Ω] {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)} :
    FieldedSwitchingOnlyExactVisibleCompressionBridge Ω Z k s hist items ↔
      ∀ {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index),
        FieldedSwitchingSemanticFiniteImageBridge Ω Z k s hist items G := by
  exact
    kpolyCoverage_anchor_fieldedSwitchingOnlyExactVisibleCompressionBridge_iff_forall_semanticFiniteImageBridge

theorem kpoly_anchor_not_product_bound_only_bridge_nil_of_lt_surface_card_regression
    {Ω Z : Type*} [Fintype Ω] [Fintype Z] {k s : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ProductBoundOnlyExactVisibleCompressionBridge
        Ω Z k s ([] : List (FiniteEvent Ω)) ([] : List (V13FieldedStep Ω)) := by
  exact
    kpolyCoverage_anchor_not_productBoundOnlyExactVisibleCompressionBridge_nil_of_lt_surfaceCard
      (Ω := Ω) (Z := Z) (k := k) (s := s) hs

theorem kpoly_anchor_not_fielded_switching_only_bridge_nil_of_lt_surface_card_regression
    {Ω Z : Type*} [Fintype Ω] [Fintype Z] {k s : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ FieldedSwitchingOnlyExactVisibleCompressionBridge
        Ω Z k s ([] : List (FiniteEvent Ω)) ([] : List (V13FieldedStep Ω)) := by
  exact
    kpolyCoverage_anchor_not_fieldedSwitchingOnlyExactVisibleCompressionBridge_nil_of_lt_surfaceCard
      (Ω := Ω) (Z := Z) (k := k) (s := s) hs

theorem kpoly_anchor_not_product_bound_only_bridge_bool_pair_one_step_of_lt_surface_card_regression
    {Z : Type*} [Fintype Z] {k s : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ProductBoundOnlyExactVisibleCompressionBridge
        (Bool × Bool) Z k s
        ([] : List (FiniteEvent (Bool × Bool)))
        [v13BoolPairUnitFieldedStep] := by
  exact
    kpolyCoverage_anchor_not_productBoundOnlyExactVisibleCompressionBridge_boolPair_one_step_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) hs

theorem kpoly_anchor_not_fielded_switching_only_bridge_bool_pair_one_step_of_lt_surface_card_regression
    {Z : Type*} [Fintype Z] {k s : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ FieldedSwitchingOnlyExactVisibleCompressionBridge
        (Bool × Bool) Z k s
        ([] : List (FiniteEvent (Bool × Bool)))
        [v13BoolPairUnitFieldedStep] := by
  exact
    kpolyCoverage_anchor_not_fieldedSwitchingOnlyExactVisibleCompressionBridge_boolPair_one_step_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) hs

theorem kpoly_anchor_not_product_bound_only_bridge_surjective_family_regression
    {Ω : Type u} {Z : Type v} [Fintype Ω] [Fintype Z] {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index)
    (hprod : V13FieldedProductBoundFrom Ω hist items)
    (hsurj : Function.Surjective G.predict)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ProductBoundOnlyExactVisibleCompressionBridge Ω Z k s hist items := by
  exact
    kpolyCoverage_anchor_not_productBoundOnlyExactVisibleCompressionBridge_of_true_productBound_of_surjective_predict_of_lt_surfaceCard
      G hprod hsurj hs

theorem kpoly_anchor_not_fielded_switching_only_bridge_surjective_family_regression
    {Ω : Type u} {Z : Type v} [Fintype Ω] [Fintype Z] {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index)
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hsurj : Function.Surjective G.predict)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ FieldedSwitchingOnlyExactVisibleCompressionBridge Ω Z k s hist items := by
  exact
    kpolyCoverage_anchor_not_fieldedSwitchingOnlyExactVisibleCompressionBridge_of_true_fieldedSwitching_of_surjective_predict_of_lt_surfaceCard
      G hfield hsurj hs

theorem kpoly_anchor_clocked_realization_iff_finite_predictor_cover_regression
    {Z : Type*} {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} :
    (∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F) ↔
      G.FinitePredictorCover (2 ^ s) := by
  exact kpolyCoverage_anchor_clockedRealization_iff_finitePredictorCover

theorem kpoly_anchor_clocked_payload_iff_finite_predictor_cover_regression
    {Z : Type*} [Fintype Z] {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} :
    ClockedKpolyFiniteLearningPayload G s clock ↔
      G.FinitePredictorCover (2 ^ s) := by
  exact kpolyCoverage_anchor_clockedFiniteLearningPayload_iff_finitePredictorCover

theorem kpoly_anchor_exact_zab_erm_clocked_payload_regression
    {Z : Type v} [Fintype Z] {r k clock : ℕ} {Index : Type u}
    (zfeat : Z → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    ClockedKpolyFiniteLearningPayload
      (exactZABDecisionListERMFamily
        (Z := Z) (r := r) (k := k) (Index := Index) zfeat samples)
      (r + 2 * k + 1) clock := by
  exact
    kpolyCoverage_anchor_exactZABDecisionListERMClockedKpolyFiniteLearningPayload
      (Z := Z) (r := r) (k := k) (clock := clock) (Index := Index)
      zfeat samples

theorem kpoly_anchor_bitvec_zab_erm_clocked_payload_regression
    {r k clock : ℕ} {Index : Type u} [Fintype (BitVec r)]
    (samples :
      Index → Sample (ExactVisiblePostSwitchSurface (BitVec r) k) Bool) :
    ClockedKpolyFiniteLearningPayload
      (bitVecZABDecisionListERMFamily
        (r := r) (k := k) (Index := Index) samples)
      (r + 2 * k + 1) clock := by
  exact
    kpolyCoverage_anchor_bitVecZABDecisionListERMClockedKpolyFiniteLearningPayload
      (r := r) (k := k) (clock := clock) (Index := Index) samples

theorem kpoly_anchor_clocked_payload_of_eq_bitvec_zab_erm_regression
    {r k clock : ℕ} {Index : Type u} [Fintype (BitVec r)]
    (samples :
      Index → Sample (ExactVisiblePostSwitchSurface (BitVec r) k) Bool)
    {G : ExactVisibleSwitchedFamily (BitVec r) k Index}
    (hG :
      G =
        bitVecZABDecisionListERMFamily
          (r := r) (k := k) (Index := Index) samples) :
    ClockedKpolyFiniteLearningPayload G (r + 2 * k + 1) clock := by
  exact
    kpolyCoverage_anchor_clockedPayload_of_eq_bitVecZABDecisionListERMFamily
      (r := r) (k := k) (clock := clock) (Index := Index) samples hG

theorem kpoly_anchor_current_interface_not_forall_clocked_payload_regression
    {Z : Type v} [Fintype Z] {k s clock : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (∀ {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index),
        ClockedKpolyFiniteLearningPayload G s clock) := by
  exact
    kpolyCoverage_anchor_currentExactVisibleInterface_not_forall_clockedPayload_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) (clock := clock) hs

theorem kpoly_anchor_plugin_lookup_surjective_regression
    (Z : Type v) (k : ℕ) :
    Function.Surjective
      (pluginLookupActualSwitchedLocalInterface Z k).predictorFamily.predict := by
  exact kpolyCoverage_anchor_pluginLookup_surjective Z k

theorem kpoly_anchor_plugin_lookup_no_clocked_payload_regression
    {Z : Type v} [Fintype Z] {k s clock : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ClockedKpolyFiniteLearningPayload
        (pluginLookupActualSwitchedLocalInterface Z k).predictorFamily s clock := by
  exact
    kpolyCoverage_anchor_pluginLookup_not_clockedPayload_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) (clock := clock) hs

theorem kpoly_anchor_plugin_lookup_no_zab_data_regression
    {Z : Type v} [Fintype Z] {k r : ℕ}
    (zfeat : Z → BitVec r)
    (hs : r + 2 * k + 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.ZABDecisionListData
          (pluginLookupActualSwitchedLocalInterface Z k) zfeat) := by
  exact
    kpolyCoverage_anchor_pluginLookup_not_zabDecisionListData_of_lt_surfaceCard
      (Z := Z) (k := k) (r := r) zfeat hs

theorem kpoly_anchor_plugin_majority_surjective_regression
    (Z : Type v) (k : ℕ) :
    Function.Surjective
      (pluginMajorityActualSwitchedLocalInterface Z k).predictorFamily.predict := by
  exact kpolyCoverage_anchor_pluginMajority_surjective Z k

theorem kpoly_anchor_plugin_majority_no_clocked_payload_regression
    {Z : Type v} [Fintype Z] {k s clock : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ClockedKpolyFiniteLearningPayload
        (pluginMajorityActualSwitchedLocalInterface Z k).predictorFamily s clock := by
  exact
    kpolyCoverage_anchor_pluginMajority_not_clockedPayload_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) (clock := clock) hs

theorem kpoly_anchor_plugin_majority_no_zab_data_regression
    {Z : Type v} [Fintype Z] {k r : ℕ}
    (zfeat : Z → BitVec r)
    (hs : r + 2 * k + 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.ZABDecisionListData
          (pluginMajorityActualSwitchedLocalInterface Z k) zfeat) := by
  exact
    kpolyCoverage_anchor_pluginMajority_not_zabDecisionListData_of_lt_surfaceCard
      (Z := Z) (k := k) (r := r) zfeat hs

theorem kpoly_anchor_plugin_sample_majority_surjective_regression
    (Z : Type v) (k : ℕ) [Fintype Z] :
    Function.Surjective
      (pluginSampleMajorityActualSwitchedLocalInterface Z k).predictorFamily.predict := by
  exact kpolyCoverage_anchor_pluginSampleMajority_surjective Z k

theorem kpoly_anchor_plugin_sample_majority_no_clocked_payload_regression
    {Z : Type v} [Fintype Z] {k s clock : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ClockedKpolyFiniteLearningPayload
        (pluginSampleMajorityActualSwitchedLocalInterface Z k).predictorFamily s clock := by
  exact
    kpolyCoverage_anchor_pluginSampleMajority_not_clockedPayload_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) (clock := clock) hs

theorem kpoly_anchor_plugin_sample_majority_no_zab_data_regression
    {Z : Type v} [Fintype Z] {k r : ℕ}
    (zfeat : Z → BitVec r)
    (hs : r + 2 * k + 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.ZABDecisionListData
          (pluginSampleMajorityActualSwitchedLocalInterface Z k) zfeat) := by
  exact
    kpolyCoverage_anchor_pluginSampleMajority_not_zabDecisionListData_of_lt_surfaceCard
      (Z := Z) (k := k) (r := r) zfeat hs

theorem kpoly_anchor_surjective_actual_local_no_extractor_visible_width_plugin_sample_majority_regression
    (μ : PMF (ExactVisiblePostSwitchSurface (BitVec 2) 0))
    (q : ℝ≥0∞) :
    ¬ ∃ zfeat : BitVec 2 → BitVec 0,
        Nonempty
          (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
            μ
            (pluginSampleMajorityActualSwitchedLocalInterface (BitVec 2) 0)
            zfeat
            q) := by
  exact
    kpolyCoverage_anchor_surjectiveActualLocal_not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
      (n := 2)
      (k := 0)
      (r := 0)
      (μ := μ)
      (T := pluginSampleMajorityActualSwitchedLocalInterface (BitVec 2) 0)
      (q := q)
      (kpolyCoverage_anchor_pluginSampleMajority_surjective (BitVec 2) 0)
      (by decide)

theorem kpoly_anchor_surjective_actual_local_not_exists_recovery_of_visible_width_gap_or_lt_one_sub_apply_lightest_point_full_rule_regression
    (μ : PMF (ExactVisiblePostSwitchSurface (BitVec 2) 0))
    (q : ℝ≥0∞) :
    ¬ ∃ zfeat : BitVec 2 → BitVec 0,
        Nonempty
          (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
            μ
            (fullRuleActualSwitchedLocalInterface (BitVec 2) 0)
            zfeat
            q) := by
  letI : Nonempty (ExactVisiblePostSwitchSurface (BitVec 2) 0) :=
    ⟨⟨zeroVec, zeroVec, zeroVec⟩⟩
  exact
    kpolyCoverage_anchor_surjectiveActualLocal_not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_visibleWidth_gap_or_lt_one_sub_apply_lightestPoint
      (n := 2)
      (k := 0)
      (r := 0)
      (μ := μ)
      (T := fullRuleActualSwitchedLocalInterface (BitVec 2) 0)
      (q := q)
      (fullRuleActualSwitchedLocalInterface_surjective (BitVec 2) 0)
      (Or.inl (by decide))

theorem kpoly_anchor_bounded_sample_majority_surjective_iff_regression
    (Z : Type v) (k sampleBound : ℕ) [Fintype Z] :
    Function.Surjective
        (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).predictorFamily.predict ↔
      Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound := by
  exact
    kpolyCoverage_anchor_boundedSampleMajority_surjective_iff
      Z k sampleBound

theorem kpoly_anchor_bounded_sample_majority_false_support_card_regression
    {Z : Type v} [Fintype Z] {k sampleBound : ℕ}
    (sample :
      BoundedSampleIndex (ExactVisiblePostSwitchSurface Z k) sampleBound) :
    (PluginSampleMajority.falseSupport
      (fun u : ExactVisiblePostSwitchSurface Z k =>
        (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).predictorFamily.predict
          sample u)).card ≤ sampleBound := by
  exact
    kpolyCoverage_anchor_boundedSampleMajority_falseSupport_card_le_sampleBound
      (Z := Z) (k := k) (sampleBound := sampleBound) sample

theorem kpoly_anchor_bounded_sample_majority_not_realizes_large_false_support_regression
    {Z : Type v} [Fintype Z] {k sampleBound : ℕ}
    (rule : ExactVisibleRule Z k)
    (hcard : sampleBound < (PluginSampleMajority.falseSupport rule).card) :
    ¬ ∃ sample,
      (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).predictorFamily.predict
          sample =
        rule := by
  exact
    kpolyCoverage_anchor_boundedSampleMajority_not_realizes_rule_of_sampleBound_lt_falseSupport_card
      (Z := Z) (k := k) (sampleBound := sampleBound) rule hcard

theorem kpoly_anchor_bounded_sample_majority_default_nondefault_support_card_regression
    {Z : Type v} [Fintype Z] {k sampleBound : ℕ}
    (default : Bool)
    (sample :
      BoundedSampleIndex (ExactVisiblePostSwitchSurface Z k) sampleBound) :
    (PluginSampleMajority.nondefaultSupport default
      (fun u : ExactVisiblePostSwitchSurface Z k =>
        (boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface
          default Z k sampleBound).predictorFamily.predict sample u)).card ≤ sampleBound := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithDefault_nondefaultSupport_card_le_sampleBound
      (Z := Z) (k := k) (sampleBound := sampleBound) default sample

theorem kpoly_anchor_bounded_sample_majority_default_not_realizes_large_nondefault_support_regression
    {Z : Type v} [Fintype Z] {k sampleBound : ℕ}
    (default : Bool) (rule : ExactVisibleRule Z k)
    (hcard : sampleBound < (PluginSampleMajority.nondefaultSupport default rule).card) :
    ¬ ∃ sample,
      (boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface
          default Z k sampleBound).predictorFamily.predict sample =
        rule := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithDefault_not_realizes_rule_of_sampleBound_lt_nondefaultSupport_card
      (Z := Z) (k := k) (sampleBound := sampleBound) default rule hcard

theorem kpoly_anchor_bounded_sample_majority_default_surjective_iff_regression
    (default : Bool) (Z : Type v) (k sampleBound : ℕ) [Fintype Z] :
    Function.Surjective
        (boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface
          default Z k sampleBound).predictorFamily.predict ↔
      Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithDefault_surjective_iff
      default Z k sampleBound

theorem kpoly_anchor_bounded_sample_majority_fallback_empty_sample_regression
    {Z : Type v} {k sampleBound : ℕ}
    (fallback : ExactVisibleRule Z k) :
    (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
        Z k sampleBound).predictorFamily.predict
        (fallback, ⟨[], by simp⟩) =
      fallback := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithFallback_emptySample_predict
      (Z := Z) (k := k) (sampleBound := sampleBound) fallback

theorem kpoly_anchor_bounded_sample_majority_fallback_surjective_regression
    (Z : Type v) (k sampleBound : ℕ) :
    Function.Surjective
      (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
        Z k sampleBound).predictorFamily.predict := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithFallback_surjective
      Z k sampleBound

theorem kpoly_anchor_bounded_sample_majority_fallback_no_finite_cover_regression
    {Z : Type v} [Fintype Z] {k s sampleBound : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
        Z k sampleBound).predictorFamily.FinitePredictorCover (2 ^ s) := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithFallback_not_finitePredictorCover_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) (sampleBound := sampleBound) hs

theorem kpoly_anchor_bounded_sample_majority_fallback_no_finite_index_representative_cover_regression
    {Z : Type v} [Fintype Z] {k s sampleBound : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
        Z k sampleBound).predictorFamily.FiniteIndexRepresentativeCover (2 ^ s) := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithFallback_not_finiteIndexRepresentativeCover_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) (sampleBound := sampleBound) hs

theorem kpoly_anchor_bounded_sample_majority_fallback_no_finite_predictor_quotient_regression
    {Z : Type v} [Fintype Z] {k s sampleBound : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
        Z k sampleBound).predictorFamily.FinitePredictorQuotient (2 ^ s) := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithFallback_not_finitePredictorQuotient_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) (sampleBound := sampleBound) hs

theorem kpoly_anchor_bounded_sample_majority_fallback_no_exact_visible_compression_regression
    {Z : Type v} [Fintype Z] {k s sampleBound : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ExactVisibleCompressionTarget
        (Z := Z) (k := k)
        (Index := BoundedSampleFallbackIndex
          (ExactVisiblePostSwitchSurface Z k) sampleBound)
        (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
          Z k sampleBound).predictorFamily s := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithFallback_not_exactVisibleCompressionTarget_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) (sampleBound := sampleBound) hs

theorem kpoly_anchor_bounded_sample_majority_fallback_no_clocked_realization_regression
    {Z : Type v} [Fintype Z] {k s sampleBound clock : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
          Z k sampleBound).predictorFamily.RealizedByClockedBitFamily F := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithFallback_not_clockedRealization_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) (sampleBound := sampleBound) (clock := clock) hs

theorem kpoly_anchor_bounded_sample_majority_fallback_no_clocked_payload_regression
    {Z : Type v} [Fintype Z] {k s sampleBound clock : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ClockedKpolyFiniteLearningPayload
        (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
          Z k sampleBound).predictorFamily s clock := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithFallback_not_clockedPayload_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) (sampleBound := sampleBound) (clock := clock) hs

theorem kpoly_anchor_bounded_sample_majority_fallback_family_disagreement_support_card_regression
    {FallbackIndex : Type v} {Z : Type v} [Fintype Z] {k sampleBound : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k)
    (index :
      BoundedSampleFallbackFamilyIndex
        FallbackIndex (ExactVisiblePostSwitchSurface Z k) sampleBound) :
    (PluginSampleMajority.disagreementSupport (fallback index.1)
      (fun u : ExactVisiblePostSwitchSurface Z k =>
        (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k sampleBound fallback).predictorFamily.predict index u)).card ≤
        sampleBound := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_disagreementSupport_card_le_sampleBound
      (Z := Z) (k := k) (sampleBound := sampleBound) fallback index

theorem kpoly_anchor_bounded_sample_majority_fallback_family_empty_sample_regression
    {FallbackIndex : Type v} {Z : Type v} {k sampleBound : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k) (code : FallbackIndex) :
    (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
        FallbackIndex Z k sampleBound fallback).predictorFamily.predict
        (code, ⟨[], by simp⟩) =
      fallback code := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_emptySample_predict
      (Z := Z) (k := k) (sampleBound := sampleBound) fallback code

theorem kpoly_anchor_bounded_sample_majority_fallback_family_surjective_of_fallback_surjective_regression
    {FallbackIndex : Type v} {Z : Type v} {k sampleBound : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k)
    (hsurj : Function.Surjective fallback) :
    Function.Surjective
      (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
        FallbackIndex Z k sampleBound fallback).predictorFamily.predict := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_surjective_of_fallback_surjective
      (Z := Z) (k := k) (sampleBound := sampleBound) fallback hsurj

theorem kpoly_anchor_bounded_sample_majority_fallback_family_zero_sample_surjective_iff_fallback_surjective_regression
    {FallbackIndex : Type v} {Z : Type v} {k : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k) :
    Function.Surjective
        (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k 0 fallback).predictorFamily.predict ↔
      Function.Surjective fallback := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_zeroSample_surjective_iff_fallback_surjective
      (Z := Z) (k := k) fallback

theorem kpoly_anchor_bounded_sample_majority_fallback_family_zero_sample_finite_predictor_cover_regression
    {FallbackIndex : Type v} {Z : Type v} {k N : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k) :
    (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
        FallbackIndex Z k 0 fallback).predictorFamily.FinitePredictorCover N ↔
      (FallbackZeroSampleImage.fallbackFamily fallback).FinitePredictorCover N := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_zeroSample_finitePredictorCover_iff_fallbackFamily
      (FallbackIndex := FallbackIndex) (Z := Z) (k := k) (N := N) fallback

theorem kpoly_anchor_bounded_sample_majority_fallback_family_zero_sample_finite_index_representative_cover_regression
    {FallbackIndex : Type v} {Z : Type v} {k N : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k) :
    (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
        FallbackIndex Z k 0 fallback).predictorFamily.FiniteIndexRepresentativeCover N ↔
      (FallbackZeroSampleImage.fallbackFamily fallback).FiniteIndexRepresentativeCover N := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_zeroSample_finiteIndexRepresentativeCover_iff_fallbackFamily
      (FallbackIndex := FallbackIndex) (Z := Z) (k := k) (N := N) fallback

theorem kpoly_anchor_bounded_sample_majority_fallback_family_zero_sample_finite_predictor_quotient_regression
    {FallbackIndex : Type v} {Z : Type v} {k N : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k) :
    (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
        FallbackIndex Z k 0 fallback).predictorFamily.FinitePredictorQuotient N ↔
      (FallbackZeroSampleImage.fallbackFamily fallback).FinitePredictorQuotient N := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_zeroSample_finitePredictorQuotient_iff_fallbackFamily
      (FallbackIndex := FallbackIndex) (Z := Z) (k := k) (N := N) fallback

theorem kpoly_anchor_bounded_sample_majority_fallback_family_zero_sample_exact_visible_compression_regression
    {FallbackIndex : Type v} {Z : Type v} {k s : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k) :
    ExactVisibleCompressionTarget
        (Z := Z) (k := k)
        (Index := FallbackZeroSampleImage.ZeroSampleIndex FallbackIndex Z k)
        (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k 0 fallback).predictorFamily s ↔
      ExactVisibleCompressionTarget
        (Z := Z) (k := k)
        (Index := FallbackIndex)
        (FallbackZeroSampleImage.fallbackFamily fallback) s := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_zeroSample_exactVisibleCompressionTarget_iff_fallbackFamily
      (FallbackIndex := FallbackIndex) (Z := Z) (k := k) (s := s) fallback

theorem kpoly_anchor_bounded_sample_majority_fallback_family_zero_sample_clocked_realization_regression
    {FallbackIndex : Type v} {Z : Type v} {k s clock : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k) :
    (∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k 0 fallback).predictorFamily.RealizedByClockedBitFamily F) ↔
      ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        (FallbackZeroSampleImage.fallbackFamily fallback).RealizedByClockedBitFamily F := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_zeroSample_exists_clockedExactVisibleRealization_iff_fallbackFamily
      (FallbackIndex := FallbackIndex) (Z := Z) (k := k) (s := s) (clock := clock) fallback

theorem kpoly_anchor_bounded_sample_majority_fallback_family_zero_sample_clocked_payload_regression
    {FallbackIndex : Type v} {Z : Type v} [Fintype Z] {k s clock : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k) :
    ClockedKpolyFiniteLearningPayload
        (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k 0 fallback).predictorFamily s clock ↔
      ClockedKpolyFiniteLearningPayload
        (FallbackZeroSampleImage.fallbackFamily fallback) s clock := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_zeroSample_clockedPayload_iff_fallbackFamily
      (FallbackIndex := FallbackIndex) (Z := Z) (k := k) (s := s) (clock := clock) fallback

theorem kpoly_anchor_bounded_sample_majority_fallback_family_not_realizes_large_disagreement_support_regression
    {FallbackIndex : Type v} {Z : Type v} [Fintype Z] {k sampleBound : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k)
    (rule : ExactVisibleRule Z k)
    (hcard :
      ∀ code : FallbackIndex,
        sampleBound <
          (PluginSampleMajority.disagreementSupport (fallback code) rule).card) :
    ¬ ∃ index,
      (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k sampleBound fallback).predictorFamily.predict index =
        rule := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_not_realizes_rule_of_forall_sampleBound_lt_disagreementSupport_card
      (Z := Z) (k := k) (sampleBound := sampleBound) fallback rule hcard

theorem kpoly_anchor_bounded_sample_majority_fallback_family_finite_cover_regression
    {FallbackIndex : Type v} {Z : Type v} [Fintype FallbackIndex] [Fintype Z]
    {k sampleBound : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k) :
    (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
        FallbackIndex Z k sampleBound fallback).predictorFamily.FinitePredictorCover
      (Fintype.card FallbackIndex *
        (PluginSampleMajority.smallSubsets
          (ExactVisiblePostSwitchSurface Z k) sampleBound).card) := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_finitePredictorCover
      (Z := Z) (k := k) (sampleBound := sampleBound) fallback

theorem kpoly_anchor_bounded_sample_majority_fallback_family_exact_radius_cover_regression
    {FallbackIndex : Type v} {Z : Type v} [Fintype FallbackIndex] [Fintype Z]
    {k sampleBound : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k)
    (rule : ExactVisibleRule Z k) :
    (∃ index,
      (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k sampleBound fallback).predictorFamily.predict index =
        rule) ↔
      rule ∈ PluginSampleMajority.fallbackFamilyRadiusCover fallback sampleBound := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_realizes_rule_iff_mem_fallbackFamilyRadiusCover
      (Z := Z) (k := k) (sampleBound := sampleBound) fallback rule

theorem kpoly_anchor_bounded_sample_majority_fallback_family_surjective_iff_radius_cover_univ_regression
    {FallbackIndex : Type v} {Z : Type v} [Fintype FallbackIndex] [Fintype Z]
    {k sampleBound : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k) :
    Function.Surjective
        (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k sampleBound fallback).predictorFamily.predict ↔
      PluginSampleMajority.fallbackFamilyRadiusCover fallback sampleBound =
        (Finset.univ : Finset (ExactVisibleRule Z k)) := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_surjective_iff_fallbackFamilyRadiusCover_eq_univ
      (Z := Z) (k := k) (sampleBound := sampleBound) fallback

theorem kpoly_anchor_bounded_sample_majority_fallback_family_surjective_iff_pointwise_radius_cover_regression
    {FallbackIndex : Type v} {Z : Type v} [Fintype FallbackIndex] [Fintype Z]
    {k sampleBound : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k) :
    Function.Surjective
        (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k sampleBound fallback).predictorFamily.predict ↔
      ∀ rule : ExactVisibleRule Z k,
        ∃ code : FallbackIndex,
          (PluginSampleMajority.disagreementSupport (fallback code) rule).card ≤
            sampleBound := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_surjective_iff_forall_exists_disagreementSupport_card_le_sampleBound
      (Z := Z) (k := k) (sampleBound := sampleBound) fallback

theorem kpoly_anchor_bounded_sample_majority_fallback_family_not_surjective_small_hamming_cover_regression
    {FallbackIndex : Type v} {Z : Type v} [Fintype FallbackIndex] [Fintype Z]
    {k sampleBound : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k)
    (hcard :
      Fintype.card FallbackIndex *
          (PluginSampleMajority.smallSubsets
            (ExactVisiblePostSwitchSurface Z k) sampleBound).card <
        2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
        FallbackIndex Z k sampleBound fallback).predictorFamily.predict := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_not_surjective_of_code_mul_smallSubsets_card_lt_boolClassifierSpace
      (Z := Z) (k := k) (sampleBound := sampleBound) fallback hcard

theorem kpoly_anchor_bounded_sample_majority_fallback_family_hamming_cover_product_lower_bound_regression
    {FallbackIndex : Type v} {Z : Type v} [Fintype FallbackIndex] [Fintype Z]
    {k sampleBound : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k sampleBound fallback).predictorFamily.predict) :
    2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      Fintype.card FallbackIndex *
        (PluginSampleMajority.smallSubsets
          (ExactVisiblePostSwitchSurface Z k) sampleBound).card := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_boolClassifierSpace_card_le_code_mul_smallSubsets_card_of_surjective
      (Z := Z) (k := k) (sampleBound := sampleBound) fallback hsurj

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_exact_radius_cover_regression
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (rule : ExactVisibleRule Z k) :
    (∃ index,
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k sampleBound fallbackBits fallback).predictorFamily.predict index =
        rule) ↔
      rule ∈
        PluginSampleMajority.fallbackFamilyRadiusCover
          (fun code : ULift.{v} (BitCode fallbackBits) => fallback code.down)
          sampleBound := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_realizes_rule_iff_mem_fallbackFamilyRadiusCover
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) fallback rule

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_finite_cover_regression
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k) :
    (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound fallbackBits fallback).predictorFamily.FinitePredictorCover
      (2 ^ fallbackBits *
        (PluginSampleMajority.smallSubsets
          (ExactVisiblePostSwitchSurface Z k) sampleBound).card) := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_finitePredictorCover
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) fallback

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_surjective_iff_radius_cover_univ_regression
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k) :
    Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k sampleBound fallbackBits fallback).predictorFamily.predict ↔
      PluginSampleMajority.fallbackFamilyRadiusCover
          (fun code : ULift.{v} (BitCode fallbackBits) => fallback code.down)
          sampleBound =
        (Finset.univ : Finset (ExactVisibleRule Z k)) := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_surjective_iff_fallbackFamilyRadiusCover_eq_univ
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) fallback

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_surjective_iff_pointwise_radius_cover_regression
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k) :
    Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k sampleBound fallbackBits fallback).predictorFamily.predict ↔
      ∀ rule : ExactVisibleRule Z k,
        ∃ code : BitCode fallbackBits,
          (PluginSampleMajority.disagreementSupport (fallback code) rule).card ≤
            sampleBound := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_surjective_iff_forall_exists_disagreementSupport_card_le_sampleBound
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) fallback

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_not_surjective_small_hamming_cover_regression
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hcard :
      2 ^ fallbackBits *
          (PluginSampleMajority.smallSubsets
            (ExactVisiblePostSwitchSurface Z k) sampleBound).card <
        2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound fallbackBits fallback).predictorFamily.predict := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_surjective_of_bitCode_mul_smallSubsets_card_lt_boolClassifierSpace
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) fallback hcard

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_product_lower_bound_regression
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k sampleBound fallbackBits fallback).predictorFamily.predict) :
    2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      2 ^ fallbackBits *
        (PluginSampleMajority.smallSubsets
          (ExactVisiblePostSwitchSurface Z k) sampleBound).card := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_boolClassifierSpace_card_le_bitCode_mul_smallSubsets_card_of_surjective
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) fallback hsurj

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_binomial_product_lower_bound_regression
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k sampleBound fallbackBits fallback).predictorFamily.predict) :
    2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      2 ^ fallbackBits *
        ∑ i ∈ Finset.range (sampleBound + 1),
          (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose i := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_boolClassifierSpace_card_le_bitCode_mul_sum_choose_of_surjective
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) fallback hsurj

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_binomial_not_surjective_regression
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hcard :
      2 ^ fallbackBits *
          (∑ i ∈ Finset.range (sampleBound + 1),
            (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose i) <
        2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound fallbackBits fallback).predictorFamily.predict := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_surjective_of_bitCode_mul_sum_choose_lt_boolClassifierSpace
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) fallback hcard

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_sum_choose_total_bit_lower_bound_regression
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits overheadBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (henvelope :
      (∑ i ∈ Finset.range (sampleBound + 1),
        (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose i) ≤
        2 ^ overheadBits)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k sampleBound fallbackBits fallback).predictorFamily.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      fallbackBits + overheadBits := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_fallbackBits_add_overheadBits_ge_surfaceCard_of_sumChooseEnvelope_le_twoPow_surjective
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) (overheadBits := overheadBits)
      fallback henvelope hsurj

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_sum_choose_total_bit_deficit_not_surjective_regression
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits overheadBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (henvelope :
      (∑ i ∈ Finset.range (sampleBound + 1),
        (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose i) ≤
        2 ^ overheadBits)
    (hbits :
      fallbackBits + overheadBits <
        Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound fallbackBits fallback).predictorFamily.predict := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_surjective_of_sumChooseEnvelope_le_twoPow_and_fallbackBits_add_overheadBits_lt_surfaceCard
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) (overheadBits := overheadBits)
      fallback henvelope hbits

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_zero_fallback_bits_sample_bound_deficit_not_surjective_regression
    {Z : Type v} [Fintype Z] {k sampleBound : ℕ}
    (fallback : BitCode 0 → ExactVisibleRule Z k)
    (hbound :
      sampleBound < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound 0 fallback).predictorFamily.predict := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_surjective_zeroFallbackBits_of_sampleBound_lt_surfaceCard
      (Z := Z) (k := k) (sampleBound := sampleBound) fallback hbound

theorem kpoly_anchor_bounded_sample_majority_fallback_family_full_radius_surjective_regression
    {FallbackIndex : Type v} {Z : Type v}
    [Fintype FallbackIndex] [Nonempty FallbackIndex] [Fintype Z]
    {k sampleBound : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k)
    (hbound : Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound) :
    Function.Surjective
      (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
        FallbackIndex Z k sampleBound fallback).predictorFamily.predict := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_surjective_of_nonempty_of_surfaceCard_le_sampleBound
      (FallbackIndex := FallbackIndex) (Z := Z) (k := k)
      (sampleBound := sampleBound) fallback hbound

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_full_radius_surjective_regression
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hbound : Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound) :
    Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound fallbackBits fallback).predictorFamily.predict := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_surjective_of_surfaceCard_le_sampleBound
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) fallback hbound

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_zero_fallback_bits_exact_boundary_regression
    {Z : Type v} [Fintype Z] {k sampleBound : ℕ}
    (fallback : BitCode 0 → ExactVisibleRule Z k) :
    Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k sampleBound 0 fallback).predictorFamily.predict ↔
      Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_zeroFallbackBits_surjective_iff_surfaceCard_le_sampleBound
      (Z := Z) (k := k) (sampleBound := sampleBound) fallback

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_zero_sample_exact_decoder_surjective_regression
    {Z : Type v} [Fintype Z] {k : ℕ} :
    Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 0 (Fintype.card (ExactVisiblePostSwitchSurface Z k))
        (exactVisibleRuleDecode (Z := Z) (k := k))).predictorFamily.predict := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_surjective_zeroSample_exactVisibleRuleDecode
      (Z := Z) (k := k)

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_zero_sample_exact_decoder_no_finite_predictor_cover_regression
    {Z : Type v} [Fintype Z] {k s : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 0 (Fintype.card (ExactVisiblePostSwitchSurface Z k))
        (exactVisibleRuleDecode (Z := Z) (k := k))).predictorFamily.FinitePredictorCover (2 ^ s) := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_zeroSample_exactVisibleRuleDecode_not_finitePredictorCover_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) hs

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_zero_sample_exact_decoder_no_finite_index_representative_cover_regression
    {Z : Type v} [Fintype Z] {k s : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 0 (Fintype.card (ExactVisiblePostSwitchSurface Z k))
        (exactVisibleRuleDecode (Z := Z) (k := k))).predictorFamily.FiniteIndexRepresentativeCover (2 ^ s) := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_zeroSample_exactVisibleRuleDecode_not_finiteIndexRepresentativeCover_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) hs

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_zero_sample_exact_decoder_no_finite_predictor_quotient_regression
    {Z : Type v} [Fintype Z] {k s : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 0 (Fintype.card (ExactVisiblePostSwitchSurface Z k))
        (exactVisibleRuleDecode (Z := Z) (k := k))).predictorFamily.FinitePredictorQuotient (2 ^ s) := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_zeroSample_exactVisibleRuleDecode_not_finitePredictorQuotient_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) hs

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_zero_sample_exact_decoder_no_exact_visible_compression_regression
    {Z : Type v} [Fintype Z] {k s : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ExactVisibleCompressionTarget
        (Z := Z) (k := k)
        (Index := BitFallbackZeroSampleImage.ZeroSampleIndex
          Z k (Fintype.card (ExactVisiblePostSwitchSurface Z k)))
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 0 (Fintype.card (ExactVisiblePostSwitchSurface Z k))
          (exactVisibleRuleDecode (Z := Z) (k := k))).predictorFamily s := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_zeroSample_exactVisibleRuleDecode_not_exactVisibleCompressionTarget_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) hs

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_zero_sample_exact_decoder_no_clocked_exact_visible_realization_regression
    {Z : Type v} [Fintype Z] {k s clock : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 0 (Fintype.card (ExactVisiblePostSwitchSurface Z k))
          (exactVisibleRuleDecode (Z := Z) (k := k))).predictorFamily.RealizedByClockedBitFamily F := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_zeroSample_exactVisibleRuleDecode_not_exists_clockedExactVisibleRealization_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) (clock := clock) hs

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_zero_sample_surjective_iff_fallback_surjective_regression
    {Z : Type v} {k fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k) :
    Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 0 fallbackBits fallback).predictorFamily.predict ↔
      Function.Surjective fallback := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_zeroSample_surjective_iff_fallback_surjective
      (Z := Z) (k := k) (fallbackBits := fallbackBits) fallback

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_zero_sample_finite_predictor_cover_regression
    {Z : Type v} {k fallbackBits N : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k) :
    (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 0 fallbackBits fallback).predictorFamily.FinitePredictorCover N ↔
      (BitFallbackZeroSampleImage.fallbackDecoderFamily fallback).FinitePredictorCover N := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_zeroSample_finitePredictorCover_iff_fallbackDecoderFamily
      (Z := Z) (k := k) (fallbackBits := fallbackBits) (N := N) fallback

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_zero_sample_finite_index_representative_cover_regression
    {Z : Type v} {k fallbackBits N : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k) :
    (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 0 fallbackBits fallback).predictorFamily.FiniteIndexRepresentativeCover N ↔
      (BitFallbackZeroSampleImage.fallbackDecoderFamily fallback).FiniteIndexRepresentativeCover N := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_zeroSample_finiteIndexRepresentativeCover_iff_fallbackDecoderFamily
      (Z := Z) (k := k) (fallbackBits := fallbackBits) (N := N) fallback

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_zero_sample_finite_predictor_quotient_regression
    {Z : Type v} {k fallbackBits N : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k) :
    (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 0 fallbackBits fallback).predictorFamily.FinitePredictorQuotient N ↔
      (BitFallbackZeroSampleImage.fallbackDecoderFamily fallback).FinitePredictorQuotient N := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_zeroSample_finitePredictorQuotient_iff_fallbackDecoderFamily
      (Z := Z) (k := k) (fallbackBits := fallbackBits) (N := N) fallback

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_zero_sample_exact_visible_compression_regression
    {Z : Type v} {k fallbackBits s : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k) :
    ExactVisibleCompressionTarget
        (Z := Z) (k := k)
        (Index := BitFallbackZeroSampleImage.ZeroSampleIndex Z k fallbackBits)
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 0 fallbackBits fallback).predictorFamily s ↔
      ExactVisibleCompressionTarget
        (Z := Z) (k := k)
        (Index := BitCode fallbackBits)
        (BitFallbackZeroSampleImage.fallbackDecoderFamily fallback) s := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_zeroSample_exactVisibleCompressionTarget_iff_fallbackDecoderFamily
      (Z := Z) (k := k) (fallbackBits := fallbackBits) (s := s) fallback

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_zero_sample_clocked_exact_visible_realization_regression
    {Z : Type v} {k fallbackBits s clock : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k) :
    (∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 0 fallbackBits fallback).predictorFamily.RealizedByClockedBitFamily F) ↔
      ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        (BitFallbackZeroSampleImage.fallbackDecoderFamily fallback).RealizedByClockedBitFamily F := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_zeroSample_exists_clockedExactVisibleRealization_iff_fallbackDecoderFamily
      (Z := Z) (k := k) (fallbackBits := fallbackBits) (s := s) (clock := clock) fallback

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_zero_sample_clocked_payload_regression
    {Z : Type v} [Fintype Z] {k fallbackBits s clock : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k) :
    ClockedKpolyFiniteLearningPayload
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 0 fallbackBits fallback).predictorFamily s clock ↔
      ClockedKpolyFiniteLearningPayload
        (BitFallbackZeroSampleImage.fallbackDecoderFamily fallback) s clock := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_zeroSample_clockedPayload_iff_fallbackDecoderFamily
      (Z := Z) (k := k) (fallbackBits := fallbackBits) (s := s) (clock := clock) fallback

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_exact_decoder_surjective_regression
    {Z : Type v} [Fintype Z] {k sampleBound : ℕ} :
    Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound (Fintype.card (ExactVisiblePostSwitchSurface Z k))
        (exactVisibleRuleDecode (Z := Z) (k := k))).predictorFamily.predict := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_surjective_exactVisibleRuleDecode
      (Z := Z) (k := k) (sampleBound := sampleBound)

theorem kpoly_anchor_exact_visible_rule_decode_surjective_regression
    {Z : Type v} [Fintype Z] {k : ℕ} :
    Function.Surjective (exactVisibleRuleDecode (Z := Z) (k := k)) := by
  exact kpolyCoverage_anchor_exactVisibleRuleDecode_surjective (Z := Z) (k := k)

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_exact_decoder_no_clocked_payload_regression
    {Z : Type v} [Fintype Z] {k sampleBound s clock : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ClockedKpolyFiniteLearningPayload
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k sampleBound (Fintype.card (ExactVisiblePostSwitchSurface Z k))
          (exactVisibleRuleDecode (Z := Z) (k := k))).predictorFamily s clock := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_clockedPayload_of_exactVisibleRuleDecode_of_lt_surfaceCard
      (Z := Z) (k := k) (sampleBound := sampleBound) (s := s) (clock := clock) hs

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_zero_sample_exact_decoder_no_clocked_payload_regression
    {Z : Type v} [Fintype Z] {k s clock : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ClockedKpolyFiniteLearningPayload
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 0 (Fintype.card (ExactVisiblePostSwitchSurface Z k))
          (exactVisibleRuleDecode (Z := Z) (k := k))).predictorFamily s clock := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_zeroSample_exactVisibleRuleDecode_not_clockedPayload_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) (clock := clock) hs

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_sparse_threshold_erm_obstruction_exact_decoder_regression
    {Z : Type v} [Fintype Z] {k sampleBound r : ℕ}
    (zfeat : Z → BitVec r)
    (hs :
      2 * allAffinePointBlockFeatureCount (r + (k + k)) <
        Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMData
          (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
            Z k sampleBound
            (Fintype.card (ExactVisiblePostSwitchSurface Z k))
            (exactVisibleRuleDecode (Z := Z) (k := k)))
          zfeat) := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_nonempty_sharedExactZABSparseThresholdERMData_of_exactVisibleRuleDecode_of_lt_surfaceCard
      (k := k) (r := r) (sampleBound := sampleBound) zfeat hs

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_no_extractor_sparse_threshold_erm_visible_budget_exact_decoder_regression
    {Z : Type v} [Fintype Z] {k sampleBound r : ℕ}
    (hs :
      2 * allAffinePointBlockFeatureCount (r + (k + k)) <
        Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ∃ zfeat : Z → BitVec r,
        Nonempty
          (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMData
            (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
              Z k sampleBound
              (Fintype.card (ExactVisiblePostSwitchSurface Z k))
              (exactVisibleRuleDecode (Z := Z) (k := k)))
            zfeat) := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_exists_sharedExactZABSparseThresholdERMData_of_exactVisibleRuleDecode_of_lt_surfaceCard
      (k := k) (sampleBound := sampleBound) (r := r) hs

theorem kpoly_anchor_surjective_actual_local_lightest_point_exact_decoder_fallback_regression
    {Z : Type v} [Fintype Z] {k sampleBound r : ℕ}
    [Nonempty (ExactVisiblePostSwitchSurface Z k)]
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)} {q : ℝ≥0∞}
    (zfeat : Z → BitVec r)
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          μ
          (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
            Z k sampleBound
            (Fintype.card (ExactVisiblePostSwitchSurface Z k))
            (exactVisibleRuleDecode (Z := Z) (k := k)))
          zfeat
          q)) :
    1 - μ (PMF.lightestPoint μ) ≤ q := by
  exact
    kpolyCoverage_anchor_surjectiveActualLocal_one_sub_apply_lightestPoint_le_of_nonempty_recovery
      (T := boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound
        (Fintype.card (ExactVisiblePostSwitchSurface Z k))
        (exactVisibleRuleDecode (Z := Z) (k := k)))
      (kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_surjective_exactVisibleRuleDecode
        (Z := Z) (k := k) (sampleBound := sampleBound))
      zfeat
      h

theorem kpoly_anchor_surjective_actual_local_no_extractor_lightest_point_exact_decoder_fallback_regression
    {Z : Type v} [Fintype Z] {k sampleBound r : ℕ}
    [Nonempty (ExactVisiblePostSwitchSurface Z k)]
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (q : ℝ≥0∞)
    (hq_lt : q < 1 - μ (PMF.lightestPoint μ)) :
    ¬ ∃ zfeat : Z → BitVec r,
        Nonempty
          (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
            μ
            (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
              Z k sampleBound
              (Fintype.card (ExactVisiblePostSwitchSurface Z k))
              (exactVisibleRuleDecode (Z := Z) (k := k)))
            zfeat
            q) := by
  exact
    kpolyCoverage_anchor_surjectiveActualLocal_not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_lt_one_sub_apply_lightestPoint
      (r := r)
      (μ := μ)
      (T := boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound
        (Fintype.card (ExactVisiblePostSwitchSurface Z k))
        (exactVisibleRuleDecode (Z := Z) (k := k)))
      (q := q)
      (kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_surjective_exactVisibleRuleDecode
        (Z := Z) (k := k) (sampleBound := sampleBound))
      hq_lt

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_no_extractor_lightest_point_exact_decoder_regression
    {Z : Type v} [Fintype Z] {k sampleBound r : ℕ}
    [Nonempty (ExactVisiblePostSwitchSurface Z k)]
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (q : ℝ≥0∞)
    (hq_lt : q < 1 - μ (PMF.lightestPoint μ)) :
    ¬ ∃ zfeat : Z → BitVec r,
        Nonempty
          (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
            μ
            (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
              Z k sampleBound
              (Fintype.card (ExactVisiblePostSwitchSurface Z k))
              (exactVisibleRuleDecode (Z := Z) (k := k)))
            zfeat
            q) := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_exists_recovery_of_exactVisibleRuleDecode_of_lt_one_sub_apply_lightestPoint
      (k := k) (sampleBound := sampleBound) (r := r) μ q hq_lt

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_visible_width_threshold_exact_decoder_regression
    {n k sampleBound r : ℕ}
    [Nonempty (ExactVisiblePostSwitchSurface (BitVec n) k)]
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)} {q : ℝ≥0∞}
    (zfeat : BitVec n → BitVec r)
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          μ
          (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
            (BitVec n) k sampleBound
            (Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k))
            (exactVisibleRuleDecode (Z := BitVec n) (k := k)))
          zfeat
          q)) :
    n ≤ 2 * r + 2 * k + 1 := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_visibleWidth_le_two_mul_extractorWidth_add_two_mul_k_succ_of_nonempty_recovery_of_exactVisibleRuleDecode
      (k := k) (r := r) (sampleBound := sampleBound)
      (μ := μ) (q := q) zfeat h

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_lightest_point_threshold_exact_decoder_regression
    {Z : Type v} [Fintype Z] {k sampleBound r : ℕ}
    [Nonempty (ExactVisiblePostSwitchSurface Z k)]
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)} {q : ℝ≥0∞}
    (zfeat : Z → BitVec r)
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          μ
          (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
            Z k sampleBound
            (Fintype.card (ExactVisiblePostSwitchSurface Z k))
            (exactVisibleRuleDecode (Z := Z) (k := k)))
          zfeat
          q)) :
    1 - μ (PMF.lightestPoint μ) ≤ q := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_one_sub_apply_lightestPoint_le_of_nonempty_recovery_of_exactVisibleRuleDecode
      (k := k) (r := r) (sampleBound := sampleBound)
      (μ := μ) (q := q) zfeat h

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_visible_width_obstruction_exact_decoder_regression
    {n k sampleBound r : ℕ}
    [Nonempty (ExactVisiblePostSwitchSurface (BitVec n) k)]
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)} {q : ℝ≥0∞}
    (zfeat : BitVec n → BitVec r)
    (hgap : 2 * r + 2 * k + 1 < n) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          μ
          (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
            (BitVec n) k sampleBound
            (Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k))
            (exactVisibleRuleDecode (Z := BitVec n) (k := k)))
          zfeat
          q) := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_nonempty_recovery_of_exactVisibleRuleDecode_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
      (k := k) (r := r) (sampleBound := sampleBound)
      (μ := μ) (q := q) zfeat hgap

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_no_extractor_visible_width_exact_decoder_regression
    {n k sampleBound r : ℕ}
    [Nonempty (ExactVisiblePostSwitchSurface (BitVec n) k)]
    (μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k))
    (q : ℝ≥0∞)
    (hgap : 2 * r + 2 * k + 1 < n) :
    ¬ ∃ zfeat : BitVec n → BitVec r,
        Nonempty
          (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
            μ
            (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
              (BitVec n) k sampleBound
              (Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k))
              (exactVisibleRuleDecode (Z := BitVec n) (k := k)))
            zfeat
            q) := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_exists_recovery_of_exactVisibleRuleDecode_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
      (k := k) (sampleBound := sampleBound) (r := r) μ q hgap

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_joint_recovery_threshold_exact_decoder_regression
    {n k sampleBound r : ℕ}
    [Nonempty (ExactVisiblePostSwitchSurface (BitVec n) k)]
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)} {q : ℝ≥0∞}
    (zfeat : BitVec n → BitVec r)
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          μ
          (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
            (BitVec n) k sampleBound
            (Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k))
            (exactVisibleRuleDecode (Z := BitVec n) (k := k)))
          zfeat
          q)) :
    (n ≤ 2 * r + 2 * k + 1) ∧
      (1 - μ (PMF.lightestPoint μ) ≤ q) := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_visibleWidth_and_lightestPoint_threshold_of_nonempty_recovery_of_exactVisibleRuleDecode
      (k := k) (r := r) (sampleBound := sampleBound)
      (μ := μ) (q := q) zfeat h

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_joint_obstruction_exact_decoder_regression
    {n k sampleBound r : ℕ}
    [Nonempty (ExactVisiblePostSwitchSurface (BitVec n) k)]
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)} {q : ℝ≥0∞}
    (zfeat : BitVec n → BitVec r)
    (hbad : 2 * r + 2 * k + 1 < n ∨ q < 1 - μ (PMF.lightestPoint μ)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          μ
          (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
            (BitVec n) k sampleBound
            (Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k))
            (exactVisibleRuleDecode (Z := BitVec n) (k := k)))
          zfeat
          q) := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_nonempty_recovery_of_exactVisibleRuleDecode_of_visibleWidth_gap_or_lt_one_sub_apply_lightestPoint
      (k := k) (r := r) (sampleBound := sampleBound)
      (μ := μ) (q := q) zfeat hbad

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_no_extractor_joint_obstruction_exact_decoder_regression
    {n k sampleBound r : ℕ}
    [Nonempty (ExactVisiblePostSwitchSurface (BitVec n) k)]
    (μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k))
    (q : ℝ≥0∞)
    (hbad : 2 * r + 2 * k + 1 < n ∨ q < 1 - μ (PMF.lightestPoint μ)) :
    ¬ ∃ zfeat : BitVec n → BitVec r,
        Nonempty
          (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
            μ
            (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
              (BitVec n) k sampleBound
              (Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k))
              (exactVisibleRuleDecode (Z := BitVec n) (k := k)))
            zfeat
            q) := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_exists_recovery_of_exactVisibleRuleDecode_of_visibleWidth_gap_or_lt_one_sub_apply_lightestPoint
      (k := k) (sampleBound := sampleBound) (r := r) μ q hbad

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_polynomial_product_lower_bound_regression
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k sampleBound fallbackBits fallback).predictorFamily.predict) :
    2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      2 ^ fallbackBits *
        ((sampleBound + 1) *
          (Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1) ^ sampleBound) := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_boolClassifierSpace_card_le_bitCode_mul_sampleBound_succ_mul_surfaceCard_succ_pow_of_surjective
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) fallback hsurj

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_polynomial_not_surjective_regression
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hcard :
      2 ^ fallbackBits *
          ((sampleBound + 1) *
            (Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1) ^ sampleBound) <
        2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound fallbackBits fallback).predictorFamily.predict := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_surjective_of_bitCode_mul_sampleBound_succ_mul_surfaceCard_succ_pow_lt_boolClassifierSpace
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) fallback hcard

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_total_bit_lower_bound_regression
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits overheadBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (henvelope :
      (sampleBound + 1) *
          (Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1) ^ sampleBound ≤
        2 ^ overheadBits)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k sampleBound fallbackBits fallback).predictorFamily.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      fallbackBits + overheadBits := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_fallbackBits_add_overheadBits_ge_surfaceCard_of_polynomialEnvelope_le_twoPow_surjective
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) (overheadBits := overheadBits)
      fallback henvelope hsurj

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_total_bit_deficit_not_surjective_regression
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits overheadBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (henvelope :
      (sampleBound + 1) *
          (Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1) ^ sampleBound ≤
        2 ^ overheadBits)
    (hbits :
      fallbackBits + overheadBits <
        Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound fallbackBits fallback).predictorFamily.predict := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_surjective_of_polynomialEnvelope_le_twoPow_and_fallbackBits_add_overheadBits_lt_surfaceCard
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) (overheadBits := overheadBits)
      fallback henvelope hbits

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_factor_bit_lower_bound_regression
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits radiusBits baseBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hradius : sampleBound + 1 ≤ 2 ^ radiusBits)
    (hbase :
      Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1 ≤
        2 ^ baseBits)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k sampleBound fallbackBits fallback).predictorFamily.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      fallbackBits + radiusBits + baseBits * sampleBound := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_fallbackBits_add_radiusBits_add_baseBits_mul_sampleBound_ge_surfaceCard_of_envelopeFactors_le_twoPow_surjective
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) (radiusBits := radiusBits) (baseBits := baseBits)
      fallback hradius hbase hsurj

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_factor_bit_deficit_not_surjective_regression
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits radiusBits baseBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hradius : sampleBound + 1 ≤ 2 ^ radiusBits)
    (hbase :
      Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1 ≤
        2 ^ baseBits)
    (hbits :
      fallbackBits + radiusBits + baseBits * sampleBound <
        Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound fallbackBits fallback).predictorFamily.predict := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_surjective_of_envelopeFactors_le_twoPow_and_fallbackBits_add_radiusBits_add_baseBits_mul_sampleBound_lt_surfaceCard
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) (radiusBits := radiusBits) (baseBits := baseBits)
      fallback hradius hbase hbits

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_sample_bound_bit_lower_bound_regression
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits radiusBits baseBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hradius : sampleBound ≤ 2 ^ radiusBits)
    (hbase :
      Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1 ≤
        2 ^ baseBits)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k sampleBound fallbackBits fallback).predictorFamily.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      fallbackBits + (radiusBits + 1) + baseBits * sampleBound := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_fallbackBits_add_radiusBits_succ_add_baseBits_mul_sampleBound_ge_surfaceCard_of_sampleBound_le_twoPow_and_base_le_twoPow_surjective
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) (radiusBits := radiusBits) (baseBits := baseBits)
      fallback hradius hbase hsurj

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_sample_bound_bit_deficit_not_surjective_regression
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits radiusBits baseBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hradius : sampleBound ≤ 2 ^ radiusBits)
    (hbase :
      Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1 ≤
        2 ^ baseBits)
    (hbits :
      fallbackBits + (radiusBits + 1) + baseBits * sampleBound <
        Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound fallbackBits fallback).predictorFamily.predict := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_surjective_of_sampleBound_le_twoPow_and_base_le_twoPow_and_fallbackBits_add_radiusBits_succ_add_baseBits_mul_sampleBound_lt_surfaceCard
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) (radiusBits := radiusBits) (baseBits := baseBits)
      fallback hradius hbase hbits

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_raw_factor_bit_lower_bound_regression
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits radiusBits baseBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hradius : sampleBound ≤ 2 ^ radiusBits)
    (hbase :
      Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
        2 ^ baseBits)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k sampleBound fallbackBits fallback).predictorFamily.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      fallbackBits + (radiusBits + 1) + (baseBits + 1) * sampleBound := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_fallbackBits_add_radiusBits_succ_add_baseBits_succ_mul_sampleBound_ge_surfaceCard_of_sampleBound_le_twoPow_and_surfaceCard_le_twoPow_surjective
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) (radiusBits := radiusBits) (baseBits := baseBits)
      fallback hradius hbase hsurj

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_raw_factor_bit_deficit_not_surjective_regression
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits radiusBits baseBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hradius : sampleBound ≤ 2 ^ radiusBits)
    (hbase :
      Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
        2 ^ baseBits)
    (hbits :
      fallbackBits + (radiusBits + 1) + (baseBits + 1) * sampleBound <
        Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound fallbackBits fallback).predictorFamily.predict := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_surjective_of_sampleBound_le_twoPow_and_surfaceCard_le_twoPow_and_fallbackBits_add_radiusBits_succ_add_baseBits_succ_mul_sampleBound_lt_surfaceCard
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) (radiusBits := radiusBits) (baseBits := baseBits)
      fallback hradius hbase hbits

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_zero_sample_bit_lower_bound_regression
    {Z : Type v} [Fintype Z] {k fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 0 fallbackBits fallback).predictorFamily.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ fallbackBits := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_fallbackBits_ge_surfaceCard_of_zeroSample_surjective
      (Z := Z) (k := k) (fallbackBits := fallbackBits) fallback hsurj

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_zero_sample_not_surjective_regression
    {Z : Type v} [Fintype Z] {k fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hbits : fallbackBits < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 0 fallbackBits fallback).predictorFamily.predict := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_surjective_zeroSample_of_fallbackBits_lt_surfaceCard
      (Z := Z) (k := k) (fallbackBits := fallbackBits) fallback hbits

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_one_sample_product_lower_bound_regression
    {Z : Type v} [Fintype Z] {k fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 1 fallbackBits fallback).predictorFamily.predict) :
    2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      2 ^ fallbackBits *
        (Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1) := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_boolClassifierSpace_card_le_bitCode_mul_surfaceCard_succ_of_oneSample_surjective
      (Z := Z) (k := k) (fallbackBits := fallbackBits) fallback hsurj

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_one_sample_not_surjective_regression
    {Z : Type v} [Fintype Z] {k fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hcard :
      2 ^ fallbackBits *
          (Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1) <
        2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 1 fallbackBits fallback).predictorFamily.predict := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_surjective_oneSample_of_bitCode_mul_surfaceCard_succ_lt_boolClassifierSpace
      (Z := Z) (k := k) (fallbackBits := fallbackBits) fallback hcard

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_two_sample_quadratic_product_lower_bound_regression
    {Z : Type v} [Fintype Z] {k fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 2 fallbackBits fallback).predictorFamily.predict) :
    2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      2 ^ fallbackBits *
        (1 + Fintype.card (ExactVisiblePostSwitchSurface Z k) +
          (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose 2) := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_boolClassifierSpace_card_le_bitCode_mul_one_add_surfaceCard_add_choose_two_of_twoSample_surjective
      (Z := Z) (k := k) (fallbackBits := fallbackBits) fallback hsurj

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_two_sample_quadratic_not_surjective_regression
    {Z : Type v} [Fintype Z] {k fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hcard :
      2 ^ fallbackBits *
          (1 + Fintype.card (ExactVisiblePostSwitchSurface Z k) +
            (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose 2) <
        2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 2 fallbackBits fallback).predictorFamily.predict := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_surjective_twoSample_of_bitCode_mul_one_add_surfaceCard_add_choose_two_lt_boolClassifierSpace
      (Z := Z) (k := k) (fallbackBits := fallbackBits) fallback hcard

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_two_sample_quadratic_overhead_lower_bound_regression
    {Z : Type v} [Fintype Z] {k fallbackBits overheadBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (henvelope :
      1 + Fintype.card (ExactVisiblePostSwitchSurface Z k) +
          (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose 2 ≤
        2 ^ overheadBits)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 2 fallbackBits fallback).predictorFamily.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      fallbackBits + overheadBits := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_fallbackBits_add_overheadBits_ge_surfaceCard_of_twoSample_quadraticEnvelope_le_twoPow_surjective
      (Z := Z) (k := k) (fallbackBits := fallbackBits) (overheadBits := overheadBits)
      fallback henvelope hsurj

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_two_sample_quadratic_overhead_deficit_not_surjective_regression
    {Z : Type v} [Fintype Z] {k fallbackBits overheadBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (henvelope :
      1 + Fintype.card (ExactVisiblePostSwitchSurface Z k) +
          (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose 2 ≤
        2 ^ overheadBits)
    (hbits :
      fallbackBits + overheadBits <
        Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 2 fallbackBits fallback).predictorFamily.predict := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_surjective_twoSample_of_quadraticEnvelope_le_twoPow_and_fallbackBits_add_overheadBits_lt_surfaceCard
      (Z := Z) (k := k) (fallbackBits := fallbackBits) (overheadBits := overheadBits)
      fallback henvelope hbits

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_one_sample_successor_bit_lower_bound_regression
    {Z : Type v} [Fintype Z] {k fallbackBits baseBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hbase :
      Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1 ≤
        2 ^ baseBits)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 1 fallbackBits fallback).predictorFamily.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      fallbackBits + baseBits := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_fallbackBits_add_baseBits_ge_surfaceCard_of_oneSample_surfaceCard_succ_le_twoPow_surjective
      (Z := Z) (k := k) (fallbackBits := fallbackBits) (baseBits := baseBits)
      fallback hbase hsurj

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_one_sample_successor_bit_deficit_not_surjective_regression
    {Z : Type v} [Fintype Z] {k fallbackBits baseBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hbase :
      Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1 ≤
        2 ^ baseBits)
    (hbits :
      fallbackBits + baseBits <
        Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 1 fallbackBits fallback).predictorFamily.predict := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_surjective_oneSample_of_surfaceCard_succ_le_twoPow_and_fallbackBits_add_baseBits_lt_surfaceCard
      (Z := Z) (k := k) (fallbackBits := fallbackBits) (baseBits := baseBits)
      fallback hbase hbits

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_one_sample_raw_surface_bit_lower_bound_regression
    {Z : Type v} [Fintype Z] {k fallbackBits baseBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hbase :
      Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
        2 ^ baseBits)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 1 fallbackBits fallback).predictorFamily.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      fallbackBits + (baseBits + 1) := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_fallbackBits_add_baseBits_succ_ge_surfaceCard_of_oneSample_surfaceCard_le_twoPow_surjective
      (Z := Z) (k := k) (fallbackBits := fallbackBits) (baseBits := baseBits)
      fallback hbase hsurj

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_one_sample_raw_surface_bit_deficit_not_surjective_regression
    {Z : Type v} [Fintype Z] {k fallbackBits baseBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hbase :
      Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
        2 ^ baseBits)
    (hbits :
      fallbackBits + (baseBits + 1) <
        Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 1 fallbackBits fallback).predictorFamily.predict := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_surjective_oneSample_of_surfaceCard_le_twoPow_and_fallbackBits_add_baseBits_succ_lt_surfaceCard
      (Z := Z) (k := k) (fallbackBits := fallbackBits) (baseBits := baseBits)
      fallback hbase hbits

theorem kpoly_anchor_bounded_sample_majority_no_clocked_payload_regression
    {Z : Type v} [Fintype Z] {k s sampleBound clock : ℕ}
    (hbound : Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ClockedKpolyFiniteLearningPayload
        (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).predictorFamily
        s clock := by
  exact
    kpolyCoverage_anchor_boundedSampleMajority_not_clockedPayload_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) (sampleBound := sampleBound)
      (clock := clock) hbound hs

theorem kpoly_anchor_bounded_sample_majority_no_zab_data_regression
    {Z : Type v} [Fintype Z] {k r sampleBound : ℕ}
    (hbound : Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound)
    (zfeat : Z → BitVec r)
    (hs : r + 2 * k + 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.ZABDecisionListData
          (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound) zfeat) := by
  exact
    kpolyCoverage_anchor_boundedSampleMajority_not_zabDecisionListData_of_lt_surfaceCard
      (Z := Z) (k := k) (r := r) (sampleBound := sampleBound)
      hbound zfeat hs

theorem kpoly_anchor_support_full_rule_observed_small_not_full_cover_regression
    {Z : Type v} [Fintype Z] {Block : Type v} [Fintype Block] {k s : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.FinitePredictorCover
        (2 ^ Fintype.card Block) ∧
      ¬ (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily.FinitePredictorCover
        (2 ^ s) := by
  exact
    kpolyCoverage_anchor_supportFullRule_observedSmall_and_not_exactVisibleCover
      visibleOf hs

theorem kpoly_anchor_support_full_rule_not_clocked_payload_regression
    {Z : Type v} [Fintype Z] {Block : Type v} {k s clock : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ClockedKpolyFiniteLearningPayload
        (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily s clock := by
  exact
    kpolyCoverage_anchor_supportFullRule_not_clockedPayload_of_lt_surfaceCard
      visibleOf hs

theorem kpoly_anchor_uniform_visible_section_transfers_observed_cover_regression
    {Z : Type v} {Block Index : Type v} {k N : ℕ}
    (T : ActualSwitchedLocalInterface Z k Index Block)
    {sec : ExactVisiblePostSwitchSurface Z k → Block}
    (hsec : T.HasUniformVisibleSection sec)
    (hcover : T.outputFamily.FinitePredictorCover N) :
    T.predictorFamily.FinitePredictorCover N := by
  exact
    kpolyCoverage_anchor_uniformVisibleSection_transfers_observed_cover
      T hsec hcover

theorem kpoly_anchor_support_full_rule_uniform_section_finite_cover_regression
    {Z : Type v} [Fintype Z] {Block : Type v} [Fintype Block] {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    {sec : ExactVisiblePostSwitchSurface Z k → Block}
    (hsec :
      (supportFullRuleActualSwitchedLocalInterface visibleOf).HasUniformVisibleSection sec) :
    (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily.FinitePredictorCover
      (2 ^ Fintype.card Block) := by
  exact
    kpolyCoverage_anchor_supportFullRule_finitePredictorCover_card_of_uniformVisibleSection
      visibleOf hsec

theorem kpoly_anchor_support_full_rule_uniform_section_clocked_payload_regression
    {Z : Type v} [Fintype Z] {Block : Type v} [Fintype Block] {k clock : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    {sec : ExactVisiblePostSwitchSurface Z k → Block}
    (hsec :
      (supportFullRuleActualSwitchedLocalInterface visibleOf).HasUniformVisibleSection sec) :
    ClockedKpolyFiniteLearningPayload
      (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily
      (Fintype.card Block) clock := by
  exact
    kpolyCoverage_anchor_supportFullRule_clockedPayload_card_of_uniformVisibleSection
      visibleOf hsec

theorem kpoly_anchor_support_full_rule_uniform_section_forces_card_regression
    {Z : Type v} [Fintype Z] {Block : Type v} [Fintype Block] {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    {sec : ExactVisiblePostSwitchSurface Z k → Block}
    (hsec :
      (supportFullRuleActualSwitchedLocalInterface visibleOf).HasUniformVisibleSection sec) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ Fintype.card Block := by
  exact
    kpolyCoverage_anchor_supportFullRule_uniformSection_forces_surfaceCard_le_supportCard
      visibleOf hsec

theorem kpoly_anchor_support_full_rule_no_uniform_section_regression
    {Z : Type v} [Fintype Z] {Block : Type v} [Fintype Block] {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (hcard :
      Fintype.card Block < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ∃ sec : ExactVisiblePostSwitchSurface Z k → Block,
      (supportFullRuleActualSwitchedLocalInterface visibleOf).HasUniformVisibleSection sec := by
  exact
    kpolyCoverage_anchor_supportFullRule_no_uniformSection_below_surfaceCard
      visibleOf hcard

theorem kpoly_anchor_support_full_rule_output_family_factors_regression
    {Z : Type v} {Block : Type v} {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k) :
    (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.FactorsThrough
      visibleOf (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily := by
  exact
    kpolyCoverage_anchor_supportFullRule_outputFamily_factorsThrough_predictorFamily
      visibleOf

theorem kpoly_anchor_support_full_rule_observed_rule_injective_forces_surjective_regression
    {Z : Type v} {Block : Type v} {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (hinj :
      Function.Injective
        (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict) :
    Function.Surjective visibleOf := by
  exact
    kpolyCoverage_anchor_supportFullRule_observedRuleMap_injective_forces_surjective
      visibleOf hinj

theorem kpoly_anchor_support_full_rule_exact_decoder_forces_surjective_regression
    {Z : Type v} {Block : Type v} {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (decode : (Block → Bool) → ExactVisibleRule Z k)
    (hdecode :
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          rule) :
    Function.Surjective visibleOf := by
  exact
    kpolyCoverage_anchor_supportFullRule_exactDecoder_forces_surjective
      visibleOf decode hdecode

theorem kpoly_anchor_support_full_rule_property_decoder_constant_regression
    {Z : Type v} {Block : Type v} {α : Type v} {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (property : ExactVisibleRule Z k → α)
    (decode : (Block → Bool) → α)
    (hdecode :
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          property rule)
    {rule₀ rule₁ : ExactVisibleRule Z k}
    (hsame :
      (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₀ =
        (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₁) :
    property rule₀ = property rule₁ := by
  exact
    kpolyCoverage_anchor_supportFullRule_propertyDecoder_constant_on_observedFibers
      visibleOf property decode hdecode hsame

theorem kpoly_anchor_support_full_rule_property_decoder_iff_constant_regression
    {Z : Type v} {Block : Type v} {α : Type v} {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (property : ExactVisibleRule Z k → α) :
    (∃ decode : (Block → Bool) → α,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          property rule) ↔
      ∀ {rule₀ rule₁ : ExactVisibleRule Z k},
        (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₀ =
          (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₁ →
        property rule₀ = property rule₁ := by
  exact
    kpolyCoverage_anchor_supportFullRule_propertyDecoder_iff_constant_on_observedFibers
      visibleOf property

theorem kpoly_anchor_support_full_rule_no_property_decoder_regression
    {Z : Type v} {Block : Type v} {α : Type v} {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (property : ExactVisibleRule Z k → α)
    {rule₀ rule₁ : ExactVisibleRule Z k}
    (hsame :
      (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₀ =
        (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₁)
    (hprop : property rule₀ ≠ property rule₁) :
    ¬ ∃ decode : (Block → Bool) → α,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          property rule := by
  exact
    kpolyCoverage_anchor_supportFullRule_no_propertyDecoder_of_same_output_ne
      visibleOf property hsame hprop

theorem kpoly_anchor_support_full_rule_eval_decoder_iff_mem_range_regression
    {Z : Type v} {Block : Type v} {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (u₀ : ExactVisiblePostSwitchSurface Z k) :
    (∃ decode : (Block → Bool) → Bool,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          rule u₀) ↔ ∃ phi, visibleOf phi = u₀ := by
  exact
    kpolyCoverage_anchor_supportFullRule_evalDecoder_iff_mem_range
      visibleOf u₀

theorem kpoly_anchor_support_full_rule_all_eval_decoders_iff_surjective_regression
    {Z : Type v} {Block : Type v} {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k) :
    (∀ u₀ : ExactVisiblePostSwitchSurface Z k,
      ∃ decode : (Block → Bool) → Bool,
        ∀ rule : ExactVisibleRule Z k,
          decode
              ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
            rule u₀) ↔ Function.Surjective visibleOf := by
  exact
    kpolyCoverage_anchor_supportFullRule_all_evalDecoders_iff_surjective
      visibleOf

theorem kpoly_anchor_support_full_rule_query_decoder_iff_forall_mem_range_regression
    {Z : Type v} {Block : Type v} {Query : Type v} {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (queryOf : Query → ExactVisiblePostSwitchSurface Z k) :
    (∃ decode : (Block → Bool) → Query → Bool,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          fun q => rule (queryOf q)) ↔ ∀ q, ∃ phi, visibleOf phi = queryOf q := by
  exact
    kpolyCoverage_anchor_supportFullRule_queryDecoder_iff_forall_mem_range
      visibleOf queryOf

theorem kpoly_anchor_support_full_rule_no_query_decoder_of_missed_query_regression
    {Z : Type v} {Block : Type v} {Query : Type v} {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (queryOf : Query → ExactVisiblePostSwitchSurface Z k)
    (q₀ : Query) (hmiss : ∀ phi, visibleOf phi ≠ queryOf q₀) :
    ¬ ∃ decode : (Block → Bool) → Query → Bool,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          fun q => rule (queryOf q) := by
  exact
    kpolyCoverage_anchor_supportFullRule_no_queryDecoder_of_missed_query
      visibleOf queryOf q₀ hmiss

theorem kpoly_anchor_support_full_rule_adaptive_query_decoder_of_all_queries_reachable_regression
    {Z : Type v} {Block : Type v} {α : Type v} {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (tree : AdaptiveBoolQueryTree (ExactVisiblePostSwitchSurface Z k) α)
    (hreach : AdaptiveBoolQueryTree.AllQueriesReachable visibleOf tree) :
    ∃ decode : (Block → Bool) → α,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          AdaptiveBoolQueryTree.eval rule tree := by
  exact
    kpolyCoverage_anchor_supportFullRule_adaptiveQueryDecoder_of_allQueriesReachable
      visibleOf tree hreach

theorem kpoly_anchor_support_full_rule_adaptive_query_decoder_iff_constant_regression
    {Z : Type v} {Block : Type v} {α : Type v} {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (tree : AdaptiveBoolQueryTree (ExactVisiblePostSwitchSurface Z k) α) :
    (∃ decode : (Block → Bool) → α,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          AdaptiveBoolQueryTree.eval rule tree) ↔
      ∀ {rule₀ rule₁ : ExactVisibleRule Z k},
        (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₀ =
          (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₁ →
        AdaptiveBoolQueryTree.eval rule₀ tree =
          AdaptiveBoolQueryTree.eval rule₁ tree := by
  exact
    kpolyCoverage_anchor_supportFullRule_adaptiveQueryDecoder_iff_constant_on_observedFibers
      visibleOf tree

theorem kpoly_anchor_support_full_rule_no_adaptive_query_decoder_of_same_output_eval_ne_regression
    {Z : Type v} {Block : Type v} {α : Type v} {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (tree : AdaptiveBoolQueryTree (ExactVisiblePostSwitchSurface Z k) α)
    {rule₀ rule₁ : ExactVisibleRule Z k}
    (hsame :
      (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₀ =
        (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₁)
    (hne :
      AdaptiveBoolQueryTree.eval rule₀ tree ≠
        AdaptiveBoolQueryTree.eval rule₁ tree) :
    ¬ ∃ decode : (Block → Bool) → α,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          AdaptiveBoolQueryTree.eval rule tree := by
  exact
    kpolyCoverage_anchor_supportFullRule_no_adaptiveQueryDecoder_of_same_output_eval_ne
      visibleOf tree hsame hne

theorem kpoly_anchor_support_full_rule_no_root_adaptive_query_decoder_regression
    {Z : Type v} {Block : Type v} {α : Type v} {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (u₀ : ExactVisiblePostSwitchSurface Z k)
    {valueFalse valueTrue : α}
    (hmiss : ∀ phi, visibleOf phi ≠ u₀)
    (hne : valueFalse ≠ valueTrue) :
    ¬ ∃ decode : (Block → Bool) → α,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          AdaptiveBoolQueryTree.eval rule
            (AdaptiveBoolQueryTree.query u₀
              (AdaptiveBoolQueryTree.leaf valueFalse)
              (AdaptiveBoolQueryTree.leaf valueTrue)) := by
  exact
    kpolyCoverage_anchor_supportFullRule_no_rootAdaptiveQueryDecoder_of_missed_point_ne
      visibleOf u₀ hmiss hne

theorem kpoly_anchor_support_full_rule_no_observed_rule_injective_regression
    {Z : Type v} [Fintype Z] {Block : Type v} [Fintype Block] {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (hcard :
      Fintype.card Block < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Injective
        (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict := by
  exact
    kpolyCoverage_anchor_supportFullRule_no_observedRuleMap_injective_below_surfaceCard
      visibleOf hcard

theorem kpoly_anchor_support_full_rule_distinct_rules_same_output_regression
    {Z : Type v} [Fintype Z] {Block : Type v} [Fintype Block] {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (hcard :
      Fintype.card Block < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ∃ rule₀ rule₁ : ExactVisibleRule Z k,
      rule₀ ≠ rule₁ ∧
        (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₀ =
          (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₁ ∧
        (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily.predict rule₀ ≠
          (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily.predict rule₁ := by
  exact
    kpolyCoverage_anchor_supportFullRule_distinct_rules_same_output_below_surfaceCard
      visibleOf hcard

theorem kpoly_anchor_support_full_rule_no_exact_decoder_regression
    {Z : Type v} [Fintype Z] {Block : Type v} [Fintype Block] {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (hcard :
      Fintype.card Block < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ∃ decode : (Block → Bool) → ExactVisibleRule Z k,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          rule := by
  exact
    kpolyCoverage_anchor_supportFullRule_no_exactDecoder_below_surfaceCard
      visibleOf hcard

theorem kpoly_anchor_support_full_rule_exists_unobservable_eval_regression
    {Z : Type v} [Fintype Z] {Block : Type v} [Fintype Block] {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (hcard :
      Fintype.card Block < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ∃ u₀ : ExactVisiblePostSwitchSurface Z k,
      ¬ ∃ decode : (Block → Bool) → Bool,
        ∀ rule : ExactVisibleRule Z k,
          decode
              ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
            rule u₀ := by
  exact
    kpolyCoverage_anchor_supportFullRule_exists_unobservable_eval_below_surfaceCard
      visibleOf hcard

theorem kpoly_anchor_one_block_full_rule_observed_small_not_exact_visible_cover_regression
    {Z : Type v} [Fintype Z] {k s : ℕ}
    (u0 : ExactVisiblePostSwitchSurface Z k)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    (oneBlockFullRuleActualSwitchedLocalInterface u0).outputFamily.FinitePredictorCover 2 ∧
      ¬ (oneBlockFullRuleActualSwitchedLocalInterface u0).predictorFamily.FinitePredictorCover
        (2 ^ s) := by
  exact
    kpolyCoverage_anchor_oneBlockFullRule_observedSmall_and_not_exactVisibleCover
      u0 hs

theorem kpoly_anchor_one_block_full_rule_not_clocked_payload_regression
    {Z : Type v} [Fintype Z] {k s clock : ℕ}
    (u0 : ExactVisiblePostSwitchSurface Z k)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ClockedKpolyFiniteLearningPayload
        (oneBlockFullRuleActualSwitchedLocalInterface u0).predictorFamily s clock := by
  exact
    kpolyCoverage_anchor_oneBlockFullRule_not_clockedPayload_of_lt_surfaceCard
      u0 hs

theorem kpoly_anchor_one_block_full_rule_no_exact_decoder_regression
    {Z : Type v} [Fintype Z] {k : ℕ}
    (u0 : ExactVisiblePostSwitchSurface Z k)
    (hcard : 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ∃ decode : (Unit → Bool) → ExactVisibleRule Z k,
      ∀ rule : ExactVisibleRule Z k,
        decode ((oneBlockFullRuleActualSwitchedLocalInterface u0).outputFamily.predict rule) =
          rule := by
  exact
    kpolyCoverage_anchor_oneBlockFullRule_no_exactDecoder
      u0 hcard

theorem kpoly_anchor_one_block_full_rule_exists_unobservable_eval_regression
    {Z : Type v} [Fintype Z] {k : ℕ}
    (u0 : ExactVisiblePostSwitchSurface Z k)
    (hcard : 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ∃ u : ExactVisiblePostSwitchSurface Z k,
      ¬ ∃ decode : (Unit → Bool) → Bool,
        ∀ rule : ExactVisibleRule Z k,
          decode ((oneBlockFullRuleActualSwitchedLocalInterface u0).outputFamily.predict rule) =
            rule u := by
  exact
    kpolyCoverage_anchor_oneBlockFullRule_exists_unobservable_eval
      u0 hcard

theorem kpoly_anchor_finitePredictorCover_iff_finiteIndexRepresentativeCover_regression
    {Index Input : Type*} {G : IndexedPredictorFamily Index Input} {N : ℕ} :
    G.FinitePredictorCover N ↔ G.FiniteIndexRepresentativeCover N := by
  exact kpolyCoverage_anchor_finitePredictorCover_iff_finiteIndexRepresentativeCover

theorem kpoly_anchor_exact_visible_compression_target_iff_finitePredictorCover_regression
    {Z : Type*} {k s : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s ↔
      G.FinitePredictorCover (2 ^ s) := by
  exact kpolyCoverage_anchor_exactVisibleCompressionTarget_iff_finitePredictorCover

theorem kpoly_anchor_clocked_realization_iff_finitePredictorCover_regression
    {Z : Type*} {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} :
    (∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F) ↔
      G.FinitePredictorCover (2 ^ s) := by
  exact kpolyCoverage_anchor_clockedRealization_iff_finitePredictorCover

theorem kpoly_anchor_clocked_finite_learning_payload_iff_finitePredictorCover_regression
    {Z : Type*} [Fintype Z] {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} :
    ClockedKpolyFiniteLearningPayload G s clock ↔
      G.FinitePredictorCover (2 ^ s) := by
  exact kpolyCoverage_anchor_clockedFiniteLearningPayload_iff_finitePredictorCover

theorem kpoly_anchor_clocked_finite_learning_payload_iff_exact_visible_compression_target_regression
    {Z : Type*} [Fintype Z] {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} :
    ClockedKpolyFiniteLearningPayload G s clock ↔
      ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s := by
  exact kpolyCoverage_anchor_clockedFiniteLearningPayload_iff_exactVisibleCompressionTarget

theorem kpoly_anchor_exact_visible_compression_target_iff_finitePredictorQuotient_regression
    {Z : Type*} {k s : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s ↔
      G.FinitePredictorQuotient (2 ^ s) := by
  exact kpolyCoverage_anchor_exactVisibleCompressionTarget_iff_finitePredictorQuotient

theorem kpoly_anchor_clocked_realization_iff_finitePredictorQuotient_regression
    {Z : Type*} {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} :
    (∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F) ↔
      G.FinitePredictorQuotient (2 ^ s) := by
  exact kpolyCoverage_anchor_clockedRealization_iff_finitePredictorQuotient

theorem kpoly_anchor_exact_visible_compression_target_iff_finiteIndexRepresentativeCover_regression
    {Z : Type*} {k s : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s ↔
      G.FiniteIndexRepresentativeCover (2 ^ s) := by
  exact kpolyCoverage_anchor_exactVisibleCompressionTarget_iff_finiteIndexRepresentativeCover

theorem kpoly_anchor_clocked_realization_iff_finiteIndexRepresentativeCover_regression
    {Z : Type*} {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} :
    (∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F) ↔
      G.FiniteIndexRepresentativeCover (2 ^ s) := by
  exact kpolyCoverage_anchor_clockedRealization_iff_finiteIndexRepresentativeCover

theorem kpoly_anchor_not_clocked_realization_iff_not_finiteIndexRepresentativeCover_regression
    {Z : Type*} {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} :
    (¬ ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F) ↔
      ¬ G.FiniteIndexRepresentativeCover (2 ^ s) := by
  exact
    kpolyCoverage_anchor_not_clockedRealization_iff_not_finiteIndexRepresentativeCover

theorem kpoly_anchor_not_clocked_realization_iff_not_finitePredictorQuotient_regression
    {Z : Type*} {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} :
    (¬ ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F) ↔
      ¬ G.FinitePredictorQuotient (2 ^ s) := by
  exact
    kpolyCoverage_anchor_not_clockedRealization_iff_not_finitePredictorQuotient

theorem kpoly_anchor_finitePredictorCover_mono_regression
    {Index Input : Type*} {G : IndexedPredictorFamily Index Input} {N M : ℕ}
    (hNM : N ≤ M) (hcover : G.FinitePredictorCover N) :
    G.FinitePredictorCover M := by
  exact kpolyCoverage_anchor_finitePredictorCover_mono hNM hcover

theorem kpoly_anchor_finiteIndexRepresentativeCover_mono_regression
    {Index Input : Type*} {G : IndexedPredictorFamily Index Input} {N M : ℕ}
    (hNM : N ≤ M) (hrep : G.FiniteIndexRepresentativeCover N) :
    G.FiniteIndexRepresentativeCover M := by
  exact kpolyCoverage_anchor_finiteIndexRepresentativeCover_mono hNM hrep

theorem kpoly_anchor_finitePredictorQuotient_mono_regression
    {Index Input : Type*} {G : IndexedPredictorFamily Index Input} {N M : ℕ}
    (hNM : N ≤ M) (hquot : G.FinitePredictorQuotient N) :
    G.FinitePredictorQuotient M := by
  exact kpolyCoverage_anchor_finitePredictorQuotient_mono hNM hquot

theorem kpoly_anchor_finitePredictorCover_of_factorsThrough_regression
    {Index Input View : Type*} {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View} {view : Input → View} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hcover : H.FinitePredictorCover N) :
    G.FinitePredictorCover N := by
  exact kpolyCoverage_anchor_finitePredictorCover_of_factorsThrough
    hfactor hcover

theorem kpoly_anchor_finitePredictorCover_of_factorsThrough_of_rightInverse_regression
    {Index Input View : Type*} {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View} {view : Input → View}
    {sec : View → Input} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hcover : G.FinitePredictorCover N) :
    H.FinitePredictorCover N := by
  exact kpolyCoverage_anchor_finitePredictorCover_of_factorsThrough_of_rightInverse
    hfactor hsection hcover

theorem kpoly_anchor_finiteIndexRepresentativeCover_of_factorsThrough_regression
    {Index Input View : Type*} {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View} {view : Input → View} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hrep : H.FiniteIndexRepresentativeCover N) :
    G.FiniteIndexRepresentativeCover N := by
  exact kpolyCoverage_anchor_finiteIndexRepresentativeCover_of_factorsThrough
    hfactor hrep

theorem kpoly_anchor_finiteIndexRepresentativeCover_of_factorsThrough_of_rightInverse_regression
    {Index Input View : Type*} {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View} {view : Input → View}
    {sec : View → Input} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hrep : G.FiniteIndexRepresentativeCover N) :
    H.FiniteIndexRepresentativeCover N := by
  exact kpolyCoverage_anchor_finiteIndexRepresentativeCover_of_factorsThrough_of_rightInverse
    hfactor hsection hrep

theorem kpoly_anchor_finitePredictorQuotient_of_factorsThrough_regression
    {Index Input View : Type*} {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View} {view : Input → View} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hquot : H.FinitePredictorQuotient N) :
    G.FinitePredictorQuotient N := by
  exact kpolyCoverage_anchor_finitePredictorQuotient_of_factorsThrough
    hfactor hquot

theorem kpoly_anchor_finitePredictorQuotient_of_factorsThrough_of_rightInverse_regression
    {Index Input View : Type*} {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View} {view : Input → View}
    {sec : View → Input} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hquot : G.FinitePredictorQuotient N) :
    H.FinitePredictorQuotient N := by
  exact kpolyCoverage_anchor_finitePredictorQuotient_of_factorsThrough_of_rightInverse
    hfactor hsection hquot

theorem kpoly_anchor_not_finitePredictorCover_of_factorsThrough_of_rightInverse_regression
    {Index Input View : Type*} [Fintype View]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (hN : N < 2 ^ Fintype.card View)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hsurj : Function.Surjective H.predict) :
    ¬ G.FinitePredictorCover N := by
  exact kpolyCoverage_anchor_not_finitePredictorCover_of_factorsThrough_of_rightInverse
    hN hfactor hsection hsurj

theorem kpoly_anchor_not_finiteIndexRepresentativeCover_of_factorsThrough_of_rightInverse_regression
    {Index Input View : Type*} [Fintype View]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (hN : N < 2 ^ Fintype.card View)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hsurj : Function.Surjective H.predict) :
    ¬ G.FiniteIndexRepresentativeCover N := by
  exact kpolyCoverage_anchor_not_finiteIndexRepresentativeCover_of_factorsThrough_of_rightInverse
    hN hfactor hsection hsurj

theorem kpoly_anchor_not_finitePredictorQuotient_of_factorsThrough_of_rightInverse_regression
    {Index Input View : Type*} [Fintype View]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (hN : N < 2 ^ Fintype.card View)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hsurj : Function.Surjective H.predict) :
    ¬ G.FinitePredictorQuotient N := by
  exact kpolyCoverage_anchor_not_finitePredictorQuotient_of_factorsThrough_of_rightInverse
    hN hfactor hsection hsurj

theorem kpoly_anchor_finitePredictorCover_card_le_of_factorsThrough_of_rightInverse_of_surjective_predict_regression
    {Index Input View : Type*} [Fintype View]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hsurj : Function.Surjective H.predict)
    (hcover : G.FinitePredictorCover N) :
    2 ^ Fintype.card View ≤ N := by
  exact
    kpolyCoverage_anchor_finitePredictorCover_card_le_of_factorsThrough_of_rightInverse_of_surjective_predict
      hfactor hsection hsurj hcover

theorem kpoly_anchor_finiteIndexRepresentativeCover_card_le_of_factorsThrough_of_rightInverse_of_surjective_predict_regression
    {Index Input View : Type*} [Fintype View]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hsurj : Function.Surjective H.predict)
    (hrep : G.FiniteIndexRepresentativeCover N) :
    2 ^ Fintype.card View ≤ N := by
  exact
    kpolyCoverage_anchor_finiteIndexRepresentativeCover_card_le_of_factorsThrough_of_rightInverse_of_surjective_predict
      hfactor hsection hsurj hrep

theorem kpoly_anchor_finitePredictorQuotient_card_le_of_factorsThrough_of_rightInverse_of_surjective_predict_regression
    {Index Input View : Type*} [Fintype View]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hsurj : Function.Surjective H.predict)
    (hquot : G.FinitePredictorQuotient N) :
    2 ^ Fintype.card View ≤ N := by
  exact
    kpolyCoverage_anchor_finitePredictorQuotient_card_le_of_factorsThrough_of_rightInverse_of_surjective_predict
      hfactor hsection hsurj hquot

theorem kpoly_anchor_clocked_finite_learning_payload_card_le_of_factorsThrough_rightInverse_surjective_predict_regression
    {Z : Type*} [Fintype Z] {k s clock : ℕ} {Index View : Type*} [Fintype View]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : IndexedPredictorFamily Index View}
    {view : ExactVisiblePostSwitchSurface Z k → View}
    {sec : View → ExactVisiblePostSwitchSurface Z k}
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hsurj : Function.Surjective H.predict)
    (hpayload : ClockedKpolyFiniteLearningPayload G s clock) :
    2 ^ Fintype.card View ≤ 2 ^ s := by
  exact
    kpolyCoverage_anchor_clockedFiniteLearningPayload_card_le_of_factorsThrough_of_rightInverse_of_surjective_predict
      hfactor hsection hsurj hpayload

theorem kpoly_anchor_not_clocked_finite_learning_payload_of_factorsThrough_rightInverse_surjective_predict_regression
    {Z : Type*} [Fintype Z] {k s clock : ℕ} {Index View : Type*} [Fintype View]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : IndexedPredictorFamily Index View}
    {view : ExactVisiblePostSwitchSurface Z k → View}
    {sec : View → ExactVisiblePostSwitchSurface Z k}
    (hs : 2 ^ s < 2 ^ Fintype.card View)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hsurj : Function.Surjective H.predict) :
    ¬ ClockedKpolyFiniteLearningPayload G s clock := by
  exact
    kpolyCoverage_anchor_not_clockedFiniteLearningPayload_of_factorsThrough_of_rightInverse_of_surjective_predict_of_lt_card
      hs hfactor hsection hsurj

theorem kpoly_anchor_not_finitePredictorCover_of_factorsThrough_ab_and_surjective_predict_regression
    {Z : Type*} [Inhabited Z] {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index} {N : ℕ}
    (hN : N < 2 ^ Fintype.card (ABVisibleSurface k))
    (hfactor : G.FactorsThrough abVisibleData H)
    (hsurj : Function.Surjective H.predict) :
    ¬ G.FinitePredictorCover N := by
  exact kpolyCoverage_anchor_not_finitePredictorCover_of_factorsThrough_ab_and_surjective_predict
    hN hfactor hsurj

theorem kpoly_anchor_not_finiteIndexRepresentativeCover_of_factorsThrough_ab_and_surjective_predict_regression
    {Z : Type*} [Inhabited Z] {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index} {N : ℕ}
    (hN : N < 2 ^ Fintype.card (ABVisibleSurface k))
    (hfactor : G.FactorsThrough abVisibleData H)
    (hsurj : Function.Surjective H.predict) :
    ¬ G.FiniteIndexRepresentativeCover N := by
  exact kpolyCoverage_anchor_not_finiteIndexRepresentativeCover_of_factorsThrough_ab_and_surjective_predict
    hN hfactor hsurj

theorem kpoly_anchor_not_finitePredictorQuotient_of_factorsThrough_ab_and_surjective_predict_regression
    {Z : Type*} [Inhabited Z] {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index} {N : ℕ}
    (hN : N < 2 ^ Fintype.card (ABVisibleSurface k))
    (hfactor : G.FactorsThrough abVisibleData H)
    (hsurj : Function.Surjective H.predict) :
    ¬ G.FinitePredictorQuotient N := by
  exact kpolyCoverage_anchor_not_finitePredictorQuotient_of_factorsThrough_ab_and_surjective_predict
    hN hfactor hsurj

theorem kpoly_anchor_abVisible_finitePredictorCover_card_le_of_factorsThrough_injective_probe_regression
    {Z Probe : Type*} [Inhabited Z] [Fintype Probe]
    {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index} {N : ℕ}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hfactor : G.FactorsThrough abVisibleData H)
    (hcover : G.FinitePredictorCover N) :
    Fintype.card Probe ≤ N := by
  exact
    kpolyCoverage_anchor_abVisible_finitePredictorCover_card_le_of_factorsThrough_of_injective_realization
      target hinj hreal hfactor hcover

theorem kpoly_anchor_not_exact_visible_compression_target_of_factorsThrough_ab_injective_probe_regression
    {Z Probe : Type*} [Inhabited Z] [Fintype Probe]
    {k s : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hs : 2 ^ s < Fintype.card Probe)
    (hfactor : G.FactorsThrough abVisibleData H) :
    ¬ ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s := by
  exact
    kpolyCoverage_anchor_not_exactVisibleCompressionTarget_of_factorsThrough_ab_and_injective_realization_of_lt_card
      target hinj hreal hs hfactor

theorem kpoly_anchor_abVisible_finiteIndexRepresentativeCover_card_le_of_factorsThrough_injective_probe_regression
    {Z Probe : Type*} [Inhabited Z] [Fintype Probe]
    {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index} {N : ℕ}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hfactor : G.FactorsThrough abVisibleData H)
    (hrep : G.FiniteIndexRepresentativeCover N) :
    Fintype.card Probe ≤ N := by
  exact
    kpolyCoverage_anchor_abVisible_finiteIndexRepresentativeCover_card_le_of_factorsThrough_of_injective_realization
      target hinj hreal hfactor hrep

theorem kpoly_anchor_abVisible_finitePredictorQuotient_card_le_of_factorsThrough_injective_probe_regression
    {Z Probe : Type*} [Inhabited Z] [Fintype Probe]
    {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index} {N : ℕ}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hfactor : G.FactorsThrough abVisibleData H)
    (hquot : G.FinitePredictorQuotient N) :
    Fintype.card Probe ≤ N := by
  exact
    kpolyCoverage_anchor_abVisible_finitePredictorQuotient_card_le_of_factorsThrough_of_injective_realization
      target hinj hreal hfactor hquot

theorem kpoly_anchor_not_clocked_realization_of_factorsThrough_ab_injective_probe_regression
    {Z Probe : Type*} [Inhabited Z] [Fintype Probe]
    {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hs : 2 ^ s < Fintype.card Probe)
    (hfactor : G.FactorsThrough abVisibleData H) :
    ¬ ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F := by
  exact
    kpolyCoverage_anchor_not_clockedRealization_of_factorsThrough_ab_and_injective_realization_of_lt_card
      target hinj hreal hs hfactor

theorem kpoly_anchor_finitePredictorCover_card_le_of_surjective_predict_regression
    {Index Input : Type*} [Fintype Input]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (hsurj : Function.Surjective G.predict)
    (hcover : G.FinitePredictorCover N) :
    2 ^ Fintype.card Input ≤ N := by
  exact kpolyCoverage_anchor_finitePredictorCover_card_le_of_surjective_predict
    hsurj hcover

theorem kpoly_anchor_finiteIndexRepresentativeCover_card_le_of_surjective_predict_regression
    {Index Input : Type*} [Fintype Input]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (hsurj : Function.Surjective G.predict)
    (hrep : G.FiniteIndexRepresentativeCover N) :
    2 ^ Fintype.card Input ≤ N := by
  exact kpolyCoverage_anchor_finiteIndexRepresentativeCover_card_le_of_surjective_predict
    hsurj hrep

theorem kpoly_anchor_finitePredictorQuotient_card_le_of_surjective_predict_regression
    {Index Input : Type*} [Fintype Input]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (hsurj : Function.Surjective G.predict)
    (hquot : G.FinitePredictorQuotient N) :
    2 ^ Fintype.card Input ≤ N := by
  exact kpolyCoverage_anchor_finitePredictorQuotient_card_le_of_surjective_predict
    hsurj hquot

theorem kpoly_anchor_clocked_finite_learning_payload_card_le_of_surjective_predict_regression
    {Z : Type*} [Fintype Z] {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hsurj : Function.Surjective G.predict)
    (hpayload : ClockedKpolyFiniteLearningPayload G s clock) :
    2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ 2 ^ s := by
  exact
    kpolyCoverage_anchor_clockedFiniteLearningPayload_card_le_of_surjective_predict
      hsurj hpayload

theorem kpoly_anchor_finitePredictorCover_card_le_of_injective_realization_regression
    {Probe Index Input : Type*} [Fintype Probe]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (target : Probe → Input → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hcover : G.FinitePredictorCover N) :
    Fintype.card Probe ≤ N := by
  exact kpolyCoverage_anchor_finitePredictorCover_card_le_of_injective_realization
    target hinj hreal hcover

theorem kpoly_anchor_finiteIndexRepresentativeCover_card_le_of_injective_realization_regression
    {Probe Index Input : Type*} [Fintype Probe]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (target : Probe → Input → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hrep : G.FiniteIndexRepresentativeCover N) :
    Fintype.card Probe ≤ N := by
  exact
    kpolyCoverage_anchor_finiteIndexRepresentativeCover_card_le_of_injective_realization
      target hinj hreal hrep

theorem kpoly_anchor_finitePredictorQuotient_card_le_of_injective_realization_regression
    {Probe Index Input : Type*} [Fintype Probe]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (target : Probe → Input → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hquot : G.FinitePredictorQuotient N) :
    Fintype.card Probe ≤ N := by
  exact kpolyCoverage_anchor_finitePredictorQuotient_card_le_of_injective_realization
    target hinj hreal hquot

theorem kpoly_anchor_clocked_finite_learning_payload_card_le_of_injective_realization_regression
    {Probe Z : Type*} [Fintype Probe] [Fintype Z] {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hpayload : ClockedKpolyFiniteLearningPayload G s clock) :
    Fintype.card Probe ≤ 2 ^ s := by
  exact
    kpolyCoverage_anchor_clockedFiniteLearningPayload_card_le_of_injective_realization
      target hinj hreal hpayload

theorem kpoly_anchor_finitePredictorCover_card_le_of_factorsThrough_of_rightInverse_of_injective_realization_regression
    {Probe Index Input View : Type*} [Fintype Probe]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (target : Probe → View → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hcover : G.FinitePredictorCover N) :
    Fintype.card Probe ≤ N := by
  exact
    kpolyCoverage_anchor_finitePredictorCover_card_le_of_factorsThrough_of_rightInverse_of_injective_realization
      target hinj hreal hfactor hsection hcover

theorem kpoly_anchor_clocked_finite_learning_payload_card_le_of_factorsThrough_rightInverse_injective_realization_regression
    {Probe Z : Type*} [Fintype Probe] [Fintype Z] {k s clock : ℕ}
    {Index View : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : IndexedPredictorFamily Index View}
    {view : ExactVisiblePostSwitchSurface Z k → View}
    {sec : View → ExactVisiblePostSwitchSurface Z k}
    (target : Probe → View → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hpayload : ClockedKpolyFiniteLearningPayload G s clock) :
    Fintype.card Probe ≤ 2 ^ s := by
  exact
    kpolyCoverage_anchor_clockedFiniteLearningPayload_card_le_of_factorsThrough_of_rightInverse_of_injective_realization
      target hinj hreal hfactor hsection hpayload

theorem kpoly_anchor_not_clocked_finite_learning_payload_of_factorsThrough_rightInverse_injective_realization_regression
    {Probe Z : Type*} [Fintype Probe] [Fintype Z] {k s clock : ℕ}
    {Index View : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : IndexedPredictorFamily Index View}
    {view : ExactVisiblePostSwitchSurface Z k → View}
    {sec : View → ExactVisiblePostSwitchSurface Z k}
    (target : Probe → View → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hs : 2 ^ s < Fintype.card Probe)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view) :
    ¬ ClockedKpolyFiniteLearningPayload G s clock := by
  exact
    kpolyCoverage_anchor_not_clockedFiniteLearningPayload_of_factorsThrough_of_rightInverse_of_injective_realization_of_lt_card
      target hinj hreal hs hfactor hsection

theorem kpoly_anchor_not_finitePredictorCover_of_factorsThrough_of_rightInverse_of_injective_realization_of_lt_card_regression
    {Probe Index Input View : Type*} [Fintype Probe]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (target : Probe → View → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hN : N < Fintype.card Probe)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view) :
    ¬ G.FinitePredictorCover N := by
  exact
    kpolyCoverage_anchor_not_finitePredictorCover_of_factorsThrough_of_rightInverse_of_injective_realization_of_lt_card
      target hinj hreal hN hfactor hsection

theorem kpoly_anchor_finiteIndexRepresentativeCover_card_le_of_factorsThrough_of_rightInverse_of_injective_realization_regression
    {Probe Index Input View : Type*} [Fintype Probe]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (target : Probe → View → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hrep : G.FiniteIndexRepresentativeCover N) :
    Fintype.card Probe ≤ N := by
  exact
    kpolyCoverage_anchor_finiteIndexRepresentativeCover_card_le_of_factorsThrough_of_rightInverse_of_injective_realization
      target hinj hreal hfactor hsection hrep

theorem kpoly_anchor_not_finiteIndexRepresentativeCover_of_factorsThrough_of_rightInverse_of_injective_realization_of_lt_card_regression
    {Probe Index Input View : Type*} [Fintype Probe]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (target : Probe → View → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hN : N < Fintype.card Probe)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view) :
    ¬ G.FiniteIndexRepresentativeCover N := by
  exact
    kpolyCoverage_anchor_not_finiteIndexRepresentativeCover_of_factorsThrough_of_rightInverse_of_injective_realization_of_lt_card
      target hinj hreal hN hfactor hsection

theorem kpoly_anchor_finitePredictorQuotient_card_le_of_factorsThrough_of_rightInverse_of_injective_realization_regression
    {Probe Index Input View : Type*} [Fintype Probe]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (target : Probe → View → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hquot : G.FinitePredictorQuotient N) :
    Fintype.card Probe ≤ N := by
  exact
    kpolyCoverage_anchor_finitePredictorQuotient_card_le_of_factorsThrough_of_rightInverse_of_injective_realization
      target hinj hreal hfactor hsection hquot

theorem kpoly_anchor_not_finitePredictorQuotient_of_factorsThrough_of_rightInverse_of_injective_realization_of_lt_card_regression
    {Probe Index Input View : Type*} [Fintype Probe]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (target : Probe → View → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hN : N < Fintype.card Probe)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view) :
    ¬ G.FinitePredictorQuotient N := by
  exact
    kpolyCoverage_anchor_not_finitePredictorQuotient_of_factorsThrough_of_rightInverse_of_injective_realization_of_lt_card
      target hinj hreal hN hfactor hsection

theorem kpoly_anchor_not_exact_visible_finitePredictorCover_of_surjective_predict_regression
    {Z : Type*} [Fintype Z] {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} {N : ℕ}
    (hN : N < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k))
    (hsurj : Function.Surjective G.predict) :
    ¬ G.FinitePredictorCover N := by
  exact kpolyCoverage_anchor_not_exactVisible_finitePredictorCover_of_surjective_predict
    hN hsurj

theorem kpoly_anchor_not_exact_visible_finiteIndexRepresentativeCover_of_surjective_predict_regression
    {Z : Type*} [Fintype Z] {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} {N : ℕ}
    (hN : N < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k))
    (hsurj : Function.Surjective G.predict) :
    ¬ G.FiniteIndexRepresentativeCover N := by
  exact kpolyCoverage_anchor_not_exactVisible_finiteIndexRepresentativeCover_of_surjective_predict
    hN hsurj

theorem kpoly_anchor_not_exact_visible_finitePredictorQuotient_of_surjective_predict_regression
    {Z : Type*} [Fintype Z] {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} {N : ℕ}
    (hN : N < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k))
    (hsurj : Function.Surjective G.predict) :
    ¬ G.FinitePredictorQuotient N := by
  exact kpolyCoverage_anchor_not_exactVisible_finitePredictorQuotient_of_surjective_predict
    hN hsurj

theorem kpoly_anchor_not_clocked_realization_of_surjective_predict_of_lt_predictorCard_regression
    {Z : Type*} [Fintype Z] {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hs : 2 ^ s < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k))
    (hsurj : Function.Surjective G.predict) :
    ¬ ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F := by
  exact kpolyCoverage_anchor_not_clockedRealization_of_surjective_predict_of_lt_predictorCard
    hs hsurj

theorem kpoly_anchor_not_clocked_finite_learning_payload_of_surjective_predict_of_lt_predictorCard_regression
    {Z : Type*} [Fintype Z] {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hs : 2 ^ s < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k))
    (hsurj : Function.Surjective G.predict) :
    ¬ ClockedKpolyFiniteLearningPayload G s clock := by
  exact
    kpolyCoverage_anchor_not_clockedFiniteLearningPayload_of_surjective_predict_of_lt_predictorCard
      hs hsurj

theorem kpoly_anchor_not_exact_visible_compression_target_of_injective_realization_of_lt_card_regression
    {Probe Z : Type*} [Fintype Probe] {k s : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hs : 2 ^ s < Fintype.card Probe) :
    ¬ ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s := by
  exact
    kpolyCoverage_anchor_not_exactVisibleCompressionTarget_of_injective_realization_of_lt_card
      target hinj hreal hs

theorem kpoly_anchor_not_clocked_realization_of_injective_realization_of_lt_card_regression
    {Probe Z : Type*} [Fintype Probe] {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hs : 2 ^ s < Fintype.card Probe) :
    ¬ ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F := by
  exact
    kpolyCoverage_anchor_not_clockedRealization_of_injective_realization_of_lt_card
      target hinj hreal hs

theorem kpoly_anchor_not_clocked_finite_learning_payload_of_injective_realization_of_lt_card_regression
    {Probe Z : Type*} [Fintype Probe] [Fintype Z] {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hs : 2 ^ s < Fintype.card Probe) :
    ¬ ClockedKpolyFiniteLearningPayload G s clock := by
  exact
    kpolyCoverage_anchor_not_clockedFiniteLearningPayload_of_injective_realization_of_lt_card
      target hinj hreal hs

theorem current_pnp_packet_kpoly_compression_bridge_uncovered_regression :
    ¬ currentPNPLocalCruxPacket.covers .kpolyCompressionBridge := by
  exact kpolyCompressionBridge_uncovered_currentPNPLocalCruxPacket

theorem current_pnp_packet_clocked_finite_uniform_kernel_covered_regression :
    currentPNPLocalCruxPacket.covers .clockedFiniteUniformKernel := by
  exact clockedFiniteUniformKernel_covered_currentPNPLocalCruxPacket

theorem finite_coin_anchor_predicate_erasure_regression
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) :
    FiniteCoinRecodingFiberBalanced r ↔ FiniteCoinOutputPredicateErasing r := by
  exact finiteCoinCoverage_anchor_predicateErasure r

theorem finite_coin_anchor_decoder_half_accuracy_regression
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (decode : α → Bool)
    (hbal : FiniteCoinRecodingFiberBalanced r) :
    finiteCoinOutputDecoderHalfAccurate r decode := by
  exact finiteCoinCoverage_anchor_decoderHalfAccuracy r decode hbal

theorem finite_coin_anchor_exact_scaled_imbalance_regression
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (y : α) :
    countIndependentWithinDefect (Ω := Bool × Coin)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (fun ω => finiteCoinOutput r ω = y) =
      Fintype.card Coin * finiteCoinFiberImbalance r y := by
  exact finiteCoinCoverage_anchor_exactScaledFiberImbalance r y

theorem finite_coin_anchor_sub_card_tolerance_quantization_regression
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) {τ : Nat}
    (hlt : τ < Fintype.card Coin) :
    CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput r) τ ↔
    FiniteCoinRecodingFiberBalanced r := by
  exact finiteCoinCoverage_anchor_subCardinalityToleranceQuantization r hlt

theorem finite_coin_anchor_deterministic_postprocessing_regression
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hbal : FiniteCoinRecodingFiberBalanced r) :
    FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)) := by
  exact finiteCoinCoverage_anchor_deterministicOutputPostprocessing r g hbal

theorem finite_coin_anchor_injective_postprocessing_erasure_equivalence_regression
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hinj : Function.Injective g) :
    FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)) ↔
      FiniteCoinRecodingFiberBalanced r := by
  exact finiteCoinCoverage_anchor_injectivePostprocessingErasureEquivalence
    r g hinj

theorem finite_coin_anchor_observed_left_inverse_postprocessing_erasure_equivalence_regression
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) (recover : β → α)
    (hrecover : ∀ b c, recover (g (r b c)) = r b c) :
    FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)) ↔
      FiniteCoinRecodingFiberBalanced r := by
  exact finiteCoinCoverage_anchor_observedLeftInversePostprocessingErasureEquivalence
    r g recover hrecover

theorem finite_coin_anchor_observed_injective_postprocessing_erasure_equivalence_regression
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hinjObs :
      ∀ b1 c1 b2 c2,
        g (r b1 c1) = g (r b2 c2) → r b1 c1 = r b2 c2) :
    FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)) ↔
      FiniteCoinRecodingFiberBalanced r := by
  exact finiteCoinCoverage_anchor_observedInjectivePostprocessingErasureEquivalence
    r g hinjObs

theorem finite_coin_anchor_postprocessing_observed_output_collision_obligation_regression
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hbal : FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)))
    (hnot : ¬ FiniteCoinRecodingFiberBalanced r) :
    ∃ b1 : Bool, ∃ c1 : Coin, ∃ b2 : Bool, ∃ c2 : Coin,
      r b1 c1 ≠ r b2 c2 ∧ g (r b1 c1) = g (r b2 c2) := by
  exact finiteCoinCoverage_anchor_postprocessingObservedOutputCollisionObligation
    r g hbal hnot

theorem finite_coin_anchor_postprocessing_observed_opposite_bias_collision_obligation_regression
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hbal : FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)))
    (hnot : ¬ FiniteCoinRecodingFiberBalanced r) :
    ∃ yTrue yFalse : α,
      g yTrue = g yFalse ∧ yTrue ≠ yFalse ∧
        coinFalseFiberCount r yTrue < coinTrueFiberCount r yTrue ∧
          coinTrueFiberCount r yFalse < coinFalseFiberCount r yFalse := by
  exact finiteCoinCoverage_anchor_postprocessingObservedOppositeBiasCollisionObligation
    r g hbal hnot

theorem finite_coin_anchor_postprocessing_signed_bias_cancellation_certificate_regression
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) :
    FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)) ↔
      ∀ z : β,
        (∑ y ∈ finiteOutputPreimageFiber g z,
          finiteCoinSignedFiberBias r y) = 0 := by
  exact finiteCoinCoverage_anchor_postprocessingSignedBiasCancellationCertificate
    r g

theorem finite_coin_anchor_finite_preimage_postprocessing_blowup_regression
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
  exact finiteCoinCoverage_anchor_finitePreimagePostprocessingBlowup
    r g hbound happrox

theorem finite_coin_anchor_postprocessed_side_tolerance_observed_fiber_balance_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ ↔
    ∀ z : β,
      finiteEventCount Coin (fun c => post (r true c, side c) = z) =
        finiteEventCount Coin (fun c => post (r false c, side c) = z) := by
  exact
    finiteCoinCoverage_anchor_postprocessedSideToleranceObservedFiberBalance
      C E r side post htrue hfalse hlt

theorem finite_coin_anchor_postprocessed_side_observed_fiber_imbalance_lower_bound_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    (∀ z : β,
      loTrue * loFalse * Fintype.card Coin *
          (finiteEventCount Coin (fun c => post (r true c, side c) = z) -
            finiteEventCount Coin (fun c => post (r false c, side c) = z)) ≤ τ) ∧
    (∀ z : β,
      loTrue * loFalse * Fintype.card Coin *
          (finiteEventCount Coin (fun c => post (r false c, side c) = z) -
            finiteEventCount Coin (fun c => post (r true c, side c) = z)) ≤ τ) := by
  exact
    finiteCoinCoverage_anchor_postprocessedSideObservedFiberImbalanceLowerBound
      C E r side post τ loTrue loFalse htrue hfalse happrox

theorem finite_coin_anchor_postprocessed_side_predicate_erasure_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (P : β → Prop) [DecidablePred P] (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    finiteEventCount Coin (fun c => P (post (r true c, side c))) =
      finiteEventCount Coin (fun c => P (post (r false c, side c))) := by
  exact
    finiteCoinCoverage_anchor_postprocessedSidePredicateErasure
      C E r side post P htrue hfalse hlt happrox

theorem finite_coin_anchor_postprocessed_side_decoder_half_accuracy_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (decode : β → Bool) (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    finiteEventCount Coin (fun c => decode (post (r true c, side c)) = true) +
      finiteEventCount Coin (fun c => decode (post (r false c, side c)) = false) =
        Fintype.card Coin := by
  exact
    finiteCoinCoverage_anchor_postprocessedSideDecoderHalfAccuracy
      C E r side post decode htrue hfalse hlt happrox

theorem finite_coin_anchor_postprocessed_side_source_recovery_block_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [Nonempty Coin]
    [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (decode : β → Bool) (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (hdecodeTrue : ∀ c : Coin, decode (post (r true c, side c)) = true)
    (hdecodeFalse : ∀ c : Coin, decode (post (r false c, side c)) = false) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  exact
    finiteCoinCoverage_anchor_postprocessedSideSourceRecoveryBlock
      C E r side post decode htrue hfalse hlt hdecodeTrue hdecodeFalse

theorem finite_coin_anchor_postprocessed_side_collision_obligation_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [Nonempty Coin]
    [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    ∃ cTrue cFalse : Coin,
      post (r true cTrue, side cTrue) = post (r false cFalse, side cFalse) := by
  exact
    finiteCoinCoverage_anchor_postprocessedSideCollisionObligation
      C E r side post htrue hfalse hlt happrox

theorem finite_coin_anchor_postprocessed_side_pointwise_collision_obligation_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    (∀ cTrue : Coin,
        ∃ cFalse : Coin,
          post (r true cTrue, side cTrue) = post (r false cFalse, side cFalse)) ∧
      (∀ cFalse : Coin,
        ∃ cTrue : Coin,
          post (r true cTrue, side cTrue) =
            post (r false cFalse, side cFalse)) := by
  exact
    finiteCoinCoverage_anchor_postprocessedSidePointwiseCollisionObligation
      C E r side post htrue hfalse hlt happrox

theorem finite_coin_anchor_postprocessed_side_pointwise_collision_insufficient_regression :
    ∃ r : Bool → Fin 3 → Bool,
    ∃ side : Fin 3 → Unit,
    ∃ post : Bool × Unit → Bool,
      ((∀ cTrue : Fin 3,
          ∃ cFalse : Fin 3,
            post (r true cTrue, side cTrue) =
              post (r false cFalse, side cFalse)) ∧
        (∀ cFalse : Fin 3,
          ∃ cTrue : Fin 3,
            post (r true cTrue, side cTrue) =
              post (r false cFalse, side cFalse))) ∧
        ¬ ∃ e : Fin 3 ≃ Fin 3,
          ∀ c : Fin 3,
            post (r true c, side c) = post (r false (e c), side (e c)) := by
  exact finiteCoinCoverage_anchor_postprocessedSidePointwiseCollisionInsufficient

theorem finite_coin_anchor_postprocessed_side_one_sided_coin_map_insufficient_regression :
    ∃ r : Bool → Fin 3 → Bool,
    ∃ side : Fin 3 → Unit,
    ∃ post : Bool × Unit → Bool,
      (∃ f : Fin 3 → Fin 3,
        ∀ c : Fin 3,
          post (r true c, side c) = post (r false (f c), side (f c))) ∧
        (∀ f : Fin 3 → Fin 3,
          (∀ c : Fin 3,
            post (r true c, side c) = post (r false (f c), side (f c))) →
            ¬ Function.Injective f) ∧
          ¬ ∃ e : Fin 3 ≃ Fin 3,
            ∀ c : Fin 3,
              post (r true c, side c) = post (r false (e c), side (e c)) := by
  exact finiteCoinCoverage_anchor_postprocessedSideOneSidedCoinMapInsufficient

theorem finite_coin_anchor_postprocessed_side_injective_witness_map_equivalence_regression
    {Coin α Side β : Type*} [Fintype Coin] [DecidableEq β]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β) :
    ((∃ f : Coin → Coin,
      (∀ c : Coin,
        post (r true c, side c) = post (r false (f c), side (f c))) ∧
        Function.Injective f) ↔
      ∃ e : Coin ≃ Coin,
        ∀ c : Coin,
          post (r true c, side c) = post (r false (e c), side (e c))) ∧
      ((∃ f : Coin → Coin,
        (∀ c : Coin,
          post (r true c, side c) = post (r false (f c), side (f c))) ∧
          Function.Injective f) ↔
        ∀ z : β,
          finiteEventCount Coin (fun c => post (r true c, side c) = z) =
            finiteEventCount Coin (fun c => post (r false c, side c) = z)) := by
  exact finiteCoinCoverage_anchor_postprocessedSideInjectiveWitnessMapEquivalence
    r side post

theorem finite_coin_anchor_postprocessed_side_coin_matching_obligation_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    ∃ e : Coin ≃ Coin,
      ∀ c : Coin,
        post (r true c, side c) = post (r false (e c), side (e c)) := by
  exact
    finiteCoinCoverage_anchor_postprocessedSideCoinMatchingObligation
      C E r side post htrue hfalse hlt happrox

theorem finite_coin_anchor_postprocessed_side_coin_matching_cardinality_block_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (z : β) (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (hne :
      finiteEventCount Coin (fun c => post (r true c, side c) = z) ≠
        finiteEventCount Coin (fun c => post (r false c, side c) = z)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  exact
    finiteCoinCoverage_anchor_postprocessedSideCoinMatchingCardinalityBlock
      C E r side post z htrue hfalse hlt hne

theorem finite_coin_anchor_postprocessed_side_coin_matching_predicate_block_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (P : β → Prop) [DecidablePred P] (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (hne :
      finiteEventCount Coin (fun c => P (post (r true c, side c))) ≠
        finiteEventCount Coin (fun c => P (post (r false c, side c)))) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  exact
    finiteCoinCoverage_anchor_postprocessedSideCoinMatchingPredicateBlock
      C E r side post P htrue hfalse hlt hne

theorem finite_coin_anchor_postprocessed_side_predicate_matching_equivalence_regression
    {Coin α Side β : Type*} [Fintype Coin] [DecidableEq β]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β) :
    (∃ e : Coin ≃ Coin,
      ∀ c : Coin,
        post (r true c, side c) = post (r false (e c), side (e c))) ↔
      ∀ P : β → Prop, [DecidablePred P] →
        finiteEventCount Coin (fun c => P (post (r true c, side c))) =
          finiteEventCount Coin (fun c => P (post (r false c, side c))) := by
  exact
    finiteCoinCoverage_anchor_postprocessedSidePredicateMatchingEquivalence
      r side post

theorem finite_coin_anchor_postprocessed_side_approx_independence_coin_matching_equivalence_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ ↔
      ∃ e : Coin ≃ Coin,
        ∀ c : Coin,
          post (r true c, side c) = post (r false (e c), side (e c)) := by
  exact
    finiteCoinCoverage_anchor_postprocessedSideApproxIndependenceCoinMatchingEquivalence
      C E r side post htrue hfalse hlt

theorem finite_coin_anchor_coinwise_true_fiber_source_nonconstant_zero_block_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [Nonempty Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α)
    (htrue : ∀ c : Coin, r true c = y)
    (hfalse : ∀ c : Coin, r false c ≠ y)
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) 0 := by
  exact
    finiteCoinCoverage_anchor_coinwiseTrueFiber_sourceNonconstant_zeroBlock
      C E r y htrue hfalse hpos hneg

theorem finite_coin_anchor_coinwise_false_fiber_source_nonconstant_zero_block_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [Nonempty Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α)
    (htrue : ∀ c : Coin, r true c ≠ y)
    (hfalse : ∀ c : Coin, r false c = y)
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) 0 := by
  exact
    finiteCoinCoverage_anchor_coinwiseFalseFiber_sourceNonconstant_zeroBlock
      C E r y htrue hfalse hpos hneg

theorem finite_coin_anchor_source_nonconstant_zero_iff_balanced_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [Nonempty Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α)
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) 0 ↔
    FiniteCoinRecodingFiberBalanced r := by
  exact
    finiteCoinCoverage_anchor_sourceNonconstantZeroIffBalanced
      C E r hpos hneg

theorem finite_coin_anchor_source_lower_bound_tolerance_quantization_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ ↔
    FiniteCoinRecodingFiberBalanced r := by
  exact
    finiteCoinCoverage_anchor_sourceLowerBoundToleranceQuantization
      C E r htrue hfalse hlt

theorem finite_coin_anchor_retained_coin_tolerance_pointwise_collapse_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, xr.2)) τ ↔
    ∀ c : Coin, r true c = r false c := by
  exact
    finiteCoinCoverage_anchor_retainedCoinTolerancePointwiseCollapse
      C E r htrue hfalse hlt

theorem finite_coin_anchor_retained_side_tolerance_side_fiber_balance_regression
    {Ω Coin α Side : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    [DecidableEq Side]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, side xr.2)) τ ↔
    ∀ (y : α) (s : Side),
      finiteEventCount Coin (fun c => r true c = y ∧ side c = s) =
        finiteEventCount Coin (fun c => r false c = y ∧ side c = s) := by
  exact
    finiteCoinCoverage_anchor_retainedSideToleranceSideFiberBalance
      C E r side htrue hfalse hlt

theorem current_pnp_stop_grade_iff_gaps_covered_for_extensions_regression
    {packet : PNPCruxPacket}
    (hExtends : packet.Extends currentPNPLocalCruxPacket) :
    packet.StopGrade ↔ packet.CoversList currentPNPUncoveredRepairClasses := by
  exact stopGrade_iff_covers_currentPNP_gaps_of_extends_current hExtends

theorem current_pnp_extension_missing_gaps_blocks_stop_grade_regression
    {packet : PNPCruxPacket}
    (hExtends : packet.Extends currentPNPLocalCruxPacket)
    (hNotGaps : ¬ packet.CoversList currentPNPUncoveredRepairClasses) :
    ¬ packet.StopGrade := by
  exact not_stopGrade_of_not_covers_currentPNP_gaps_of_extends_current
    hExtends hNotGaps

theorem current_pnp_gap_completed_packet_stop_grade_regression :
    currentPNPGapCompletedPacket.StopGrade := by
  exact stopGrade_currentPNPGapCompletedPacket

theorem current_pnp_gap_completed_packet_covers_next_marginal_target_regression :
    currentPNPGapCompletedPacket.covers currentPNPNextMarginalTarget := by
  exact currentPNPGapCompletedPacket_covers_currentPNPNextMarginalTarget

end Mettapedia.Computability.PNP.CruxSynthesisRegression
