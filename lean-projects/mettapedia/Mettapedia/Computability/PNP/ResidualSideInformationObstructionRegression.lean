import Mettapedia.Computability.PNP.ResidualSideInformationObstruction

/-!
# Regression checks for residual side-information obstructions

These wrappers pin the functional separation: residual information that varies
inside one source-summary fiber cannot be decoded, classified, or equality-tested
from the source summary alone.
-/

namespace Mettapedia.Computability.PNP.ResidualSideInformationObstructionRegression

open Mettapedia.Computability.PNP

theorem side_info_collision_blocks_source_decoder_regression
    {Ω Base Side : Type*} {base : Ω → Base} {side : Ω → Side}
    {x y : Ω} (hbase : base x = base y) (hside : side x ≠ side y) :
    ¬ SideInfoDeterminedBy base side := by
  exact not_sideInfoDeterminedBy_of_same_base_ne_side hbase hside

theorem positive_weight_side_info_collision_is_collision_regression
    {Ω Base Side : Type*} {base : Ω → Base} {side : Ω → Side} {w : Ω → ℕ}
    (hcollision : PositiveWeightSideInfoCollisionOverBase base side w) :
    SideInfoCollisionOverBase base side := by
  exact sideInfoCollisionOverBase_of_positiveWeight_collision hcollision

theorem positive_weight_side_info_collision_blocks_source_decoder_regression
    {Ω Base Side : Type*} {base : Ω → Base} {side : Ω → Side} {w : Ω → ℕ}
    (hcollision : PositiveWeightSideInfoCollisionOverBase base side w) :
    ¬ SideInfoDeterminedBy base side := by
  exact not_sideInfoDeterminedBy_of_positiveWeight_collision hcollision

theorem side_info_collision_blocks_source_only_predicate_regression
    {Ω Base Side : Type*} {base : Ω → Base} {side : Ω → Side}
    {x y : Ω} (hbase : base x = base y) (hside : side x ≠ side y) :
    ¬ SourceOnlyPredicateCapturesSideEq base side (side x) := by
  exact not_sourceOnlyPredicateCapturesSideEq_left_of_same_base_ne_side
    hbase hside

theorem positive_weight_side_info_collision_blocks_supported_source_only_predicate_regression
    {Ω Base Side : Type*} {base : Ω → Base} {side : Ω → Side} {w : Ω → ℕ}
    (hcollision : PositiveWeightSideInfoCollisionOverBase base side w) :
    ∃ x, 0 < w x ∧
      ¬ SourceOnlyPredicateCapturesSideEq base side (side x) := by
  exact
    exists_positive_not_sourceOnlyPredicateCapturesSideEq_of_positiveWeight_collision
      hcollision

theorem side_info_collision_blocks_source_only_boolean_classifier_regression
    {Ω Base : Type*} {base : Ω → Base} {target : Ω → Bool}
    {x y : Ω} (hbase : base x = base y) (htarget : target x ≠ target y) :
    ¬ SourceOnlyBooleanClassifier base target := by
  exact not_sourceOnlyBooleanClassifier_of_same_base_ne_target hbase htarget

theorem residual_side_info_toy_collision_regression :
    SideInfoCollisionOverBase residualSideInfoToyBase residualSideInfoToySide := by
  exact residualSideInfoToy_collision

theorem residual_side_info_toy_not_source_determined_regression :
    ¬ SideInfoDeterminedBy residualSideInfoToyBase residualSideInfoToySide := by
  exact residualSideInfoToy_not_determinedBy_base

theorem residual_side_info_toy_not_source_only_predicate_regression :
    ¬ SourceOnlyPredicateCapturesSideEq
      residualSideInfoToyBase residualSideInfoToySide false := by
  exact residualSideInfoToy_not_sourceOnlyPredicate_false

theorem residual_side_info_toy_not_source_only_boolean_classifier_regression :
    ¬ SourceOnlyBooleanClassifier
      residualSideInfoToyBase residualSideInfoToySide := by
  exact residualSideInfoToy_not_sourceOnlyBooleanClassifier

end Mettapedia.Computability.PNP.ResidualSideInformationObstructionRegression
