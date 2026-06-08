import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleMajorityObstruction

/-!
# Regression checks for the bounded-sample plug-in majority obstruction

These wrappers keep the sample-bound hypothesis explicit: if the bound reaches
the exact visible alphabet size, plug-in majority still realizes all Boolean
rules on that alphabet and therefore cannot close the small-image bridge below
the truth-table budget.
-/

namespace Mettapedia.Computability.PNP.BoundedSampleMajorityObstructionRegression

open Mettapedia.Computability.PNP

example (Z : Type) (k sampleBound : ℕ) [Fintype Z]
    (hbound : Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound) :
    Function.Surjective
      (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).predictorFamily.predict :=
  boundedSamplePluginMajorityActualSwitchedLocalInterface_surjective Z k sampleBound hbound

example {Z : Type} {k sampleBound : ℕ} [Fintype Z]
    (hbound : sampleBound < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).predictorFamily.predict :=
  boundedSamplePluginMajorityActualSwitchedLocalInterface_not_surjective_of_sampleBound_lt_surfaceCard
    (Z := Z) (k := k) (sampleBound := sampleBound) hbound

example (Z : Type) (k sampleBound : ℕ) [Fintype Z] :
    Function.Surjective
        (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).predictorFamily.predict ↔
      Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound :=
  boundedSamplePluginMajorityActualSwitchedLocalInterface_surjective_iff Z k sampleBound

example {U : Type} [Fintype U] [DecidableEq U] {sampleBound : ℕ}
    (sample : BoundedSampleIndex U sampleBound) :
    (PluginSampleMajority.falseSupport
      (fun u : U => PluginSampleMajority.predict sample.1 u)).card ≤ sampleBound :=
  PluginSampleMajority.falseSupport_predict_card_le_bound sample

example {Z : Type} {k sampleBound : ℕ} [Fintype Z]
    (sample :
      BoundedSampleIndex (ExactVisiblePostSwitchSurface Z k) sampleBound) :
    (PluginSampleMajority.falseSupport
      (fun u : ExactVisiblePostSwitchSurface Z k =>
        (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).predictorFamily.predict
          sample u)).card ≤ sampleBound :=
  boundedSamplePluginMajorityActualSwitchedLocalInterface_falseSupport_card_le_sampleBound
    (Z := Z) (k := k) (sampleBound := sampleBound) sample

example {Z : Type} {k sampleBound : ℕ} [Fintype Z]
    (rule : ExactVisibleRule Z k)
    (hcard : sampleBound < (PluginSampleMajority.falseSupport rule).card) :
    ¬ ∃ sample,
      (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).predictorFamily.predict
          sample =
        rule :=
  boundedSamplePluginMajorityActualSwitchedLocalInterface_not_realizes_rule_of_sampleBound_lt_falseSupport_card
    (Z := Z) (k := k) (sampleBound := sampleBound) rule hcard

example {U : Type} [Fintype U] [DecidableEq U] {sampleBound : ℕ}
    (default : Bool) (sample : BoundedSampleIndex U sampleBound) :
    (PluginSampleMajority.nondefaultSupport default
      (fun u : U =>
        PluginSampleMajority.predictWithDefault default sample.1 u)).card ≤ sampleBound :=
  PluginSampleMajority.nondefaultSupport_predictWithDefault_card_le_bound default sample

example {Z : Type} {k sampleBound : ℕ} [Fintype Z]
    (default : Bool)
    (sample :
      BoundedSampleIndex (ExactVisiblePostSwitchSurface Z k) sampleBound) :
    (PluginSampleMajority.nondefaultSupport default
      (fun u : ExactVisiblePostSwitchSurface Z k =>
        (boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface
          default Z k sampleBound).predictorFamily.predict sample u)).card ≤ sampleBound :=
  boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface_nondefaultSupport_card_le_sampleBound
    (Z := Z) (k := k) (sampleBound := sampleBound) default sample

example {Z : Type} {k sampleBound : ℕ} [Fintype Z]
    (default : Bool) (rule : ExactVisibleRule Z k)
    (hcard : sampleBound < (PluginSampleMajority.nondefaultSupport default rule).card) :
    ¬ ∃ sample,
      (boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface
          default Z k sampleBound).predictorFamily.predict sample =
        rule :=
  boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface_not_realizes_rule_of_sampleBound_lt_nondefaultSupport_card
    (Z := Z) (k := k) (sampleBound := sampleBound) default rule hcard

example {Z : Type} {k sampleBound : ℕ} [Fintype Z]
    (default : Bool)
    (hbound : sampleBound < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface
        default Z k sampleBound).predictorFamily.predict :=
  boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface_not_surjective_of_sampleBound_lt_surfaceCard
    (Z := Z) (k := k) (sampleBound := sampleBound) default hbound

example (Z : Type) (k sampleBound : ℕ) [Fintype Z] (default : Bool) :
    Function.Surjective
        (boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface
          default Z k sampleBound).predictorFamily.predict ↔
      Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound :=
  boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface_surjective_iff
    default Z k sampleBound

example {U : Type} [DecidableEq U] (fallback : U → Bool) (u : U) :
    PluginSampleMajority.predictWithFallback fallback ([] : Sample U Bool) u =
      fallback u :=
  PluginSampleMajority.predictWithFallback_nil fallback u

example {Z : Type} {k sampleBound : ℕ}
    (fallback : ExactVisibleRule Z k) :
    (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
        Z k sampleBound).predictorFamily.predict
        (fallback, ⟨[], by simp⟩) =
      fallback :=
  boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface_emptySample_predict
    (Z := Z) (k := k) (sampleBound := sampleBound) fallback

example (Z : Type) (k sampleBound : ℕ) :
    Function.Surjective
      (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
        Z k sampleBound).predictorFamily.predict :=
  boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface_surjective
    Z k sampleBound

example {Z : Type} {k s sampleBound : ℕ} [Fintype Z]
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
        Z k sampleBound).predictorFamily.FinitePredictorCover (2 ^ s) :=
  boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface_not_finitePredictorCover_of_lt_surfaceCard
    (Z := Z) (k := k) (s := s) (sampleBound := sampleBound) hs

example {Z : Type} {k s sampleBound clock : ℕ} [Fintype Z]
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ClockedKpolyFiniteLearningPayload
        (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
          Z k sampleBound).predictorFamily s clock :=
  boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface_not_clockedKpolyFiniteLearningPayload_of_lt_surfaceCard
    (Z := Z) (k := k) (s := s) (sampleBound := sampleBound) (clock := clock) hs

example {U : Type} [Fintype U] [DecidableEq U] {sampleBound : ℕ}
    (fallback : U → Bool) (sample : BoundedSampleIndex U sampleBound) :
    (PluginSampleMajority.disagreementSupport fallback
      (fun u : U =>
        PluginSampleMajority.predictWithFallback fallback sample.1 u)).card ≤ sampleBound :=
  PluginSampleMajority.disagreementSupport_predictWithFallback_card_le_bound
    fallback sample

example {FallbackIndex Z : Type} {k sampleBound : ℕ} [Fintype Z]
    (fallback : FallbackIndex → ExactVisibleRule Z k)
    (index :
      BoundedSampleFallbackFamilyIndex
        FallbackIndex (ExactVisiblePostSwitchSurface Z k) sampleBound) :
    (PluginSampleMajority.disagreementSupport (fallback index.1)
      (fun u : ExactVisiblePostSwitchSurface Z k =>
        (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k sampleBound fallback).predictorFamily.predict index u)).card ≤
        sampleBound :=
  boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_disagreementSupport_card_le_sampleBound
    (Z := Z) (k := k) (sampleBound := sampleBound) fallback index

example {FallbackIndex Z : Type} {k sampleBound : ℕ} [Fintype Z]
    (fallback : FallbackIndex → ExactVisibleRule Z k)
    (rule : ExactVisibleRule Z k)
    (hcard :
      ∀ code : FallbackIndex,
        sampleBound <
          (PluginSampleMajority.disagreementSupport (fallback code) rule).card) :
    ¬ ∃ index,
      (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k sampleBound fallback).predictorFamily.predict index =
        rule :=
  boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_not_realizes_rule_of_forall_sampleBound_lt_disagreementSupport_card
    (Z := Z) (k := k) (sampleBound := sampleBound) fallback rule hcard

example {U : Type} [Fintype U] (reference : U → Bool) (s : Finset U) :
    PluginSampleMajority.disagreementSupport reference
      (PluginSampleMajority.flipOn reference s) = s :=
  PluginSampleMajority.disagreementSupport_flipOn reference s

example {U : Type} [Fintype U] (reference : U → Bool) (radius : ℕ) :
    (PluginSampleMajority.disagreementBall reference radius).card ≤
      (PluginSampleMajority.smallSubsets U radius).card :=
  PluginSampleMajority.disagreementBall_card_le_smallSubsets_card
    reference radius

example {FallbackIndex U : Type} [Fintype FallbackIndex] [Fintype U]
    (fallback : FallbackIndex → U → Bool) (radius : ℕ) :
    (PluginSampleMajority.fallbackFamilyRadiusCover fallback radius).card ≤
      Fintype.card FallbackIndex *
        (PluginSampleMajority.smallSubsets U radius).card :=
  PluginSampleMajority.fallbackFamilyRadiusCover_card_le fallback radius

example {FallbackIndex U : Type} [Fintype FallbackIndex] [Fintype U] [DecidableEq U]
    (fallback : FallbackIndex → U → Bool) {radius : ℕ}
    (hcover :
      PluginSampleMajority.fallbackFamilyRadiusCover fallback radius =
        (Finset.univ : Finset (U → Bool))) :
    2 ^ Fintype.card U ≤
      Fintype.card FallbackIndex *
        (PluginSampleMajority.smallSubsets U radius).card :=
  PluginSampleMajority.boolClassifierSpace_card_le_code_mul_smallSubsets_card_of_radiusCover_eq_univ
    fallback hcover

example {U : Type} [DecidableEq U]
    (fallback rule : U → Bool) (support : Finset U)
    (hoff : ∀ u : U, u ∉ support → fallback u = rule u) :
    PluginSampleMajority.predictWithFallback fallback
        (PluginSampleMajority.supportSample support rule) =
      rule :=
  PluginSampleMajority.predictWithFallback_supportSample_eq_of_eq_off_support
    fallback rule support hoff

example {FallbackIndex Z : Type} {k sampleBound : ℕ}
    [Fintype FallbackIndex] [Fintype Z]
    (fallback : FallbackIndex → ExactVisibleRule Z k)
    (rule : ExactVisibleRule Z k) :
    (∃ index,
      (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k sampleBound fallback).predictorFamily.predict index =
        rule) ↔
      rule ∈ PluginSampleMajority.fallbackFamilyRadiusCover fallback sampleBound :=
  boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_realizes_rule_iff_mem_fallbackFamilyRadiusCover
    (Z := Z) (k := k) (sampleBound := sampleBound) fallback rule

example {FallbackIndex Z : Type} {k sampleBound : ℕ}
    [Fintype FallbackIndex] [Fintype Z]
    (fallback : FallbackIndex → ExactVisibleRule Z k) :
    Function.Surjective
        (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k sampleBound fallback).predictorFamily.predict ↔
      PluginSampleMajority.fallbackFamilyRadiusCover fallback sampleBound =
        (Finset.univ : Finset (ExactVisibleRule Z k)) :=
  boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_surjective_iff_fallbackFamilyRadiusCover_eq_univ
    (Z := Z) (k := k) (sampleBound := sampleBound) fallback

example {FallbackIndex Z : Type} {k sampleBound : ℕ}
    [Fintype FallbackIndex] [Fintype Z]
    (fallback : FallbackIndex → ExactVisibleRule Z k) :
    Function.Surjective
        (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k sampleBound fallback).predictorFamily.predict ↔
      ∀ rule : ExactVisibleRule Z k,
        ∃ code : FallbackIndex,
          (PluginSampleMajority.disagreementSupport (fallback code) rule).card ≤
            sampleBound :=
  boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_surjective_iff_forall_exists_disagreementSupport_card_le_sampleBound
    (Z := Z) (k := k) (sampleBound := sampleBound) fallback

example {FallbackIndex Z : Type} {k sampleBound : ℕ}
    [Fintype FallbackIndex] [Fintype Z]
    (fallback : FallbackIndex → ExactVisibleRule Z k) :
    (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
        FallbackIndex Z k sampleBound fallback).predictorFamily.FinitePredictorCover
      (Fintype.card FallbackIndex *
        (PluginSampleMajority.smallSubsets
          (ExactVisiblePostSwitchSurface Z k) sampleBound).card) :=
  boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_finitePredictorCover
    (Z := Z) (k := k) (sampleBound := sampleBound) fallback

example {FallbackIndex Z : Type} {k sampleBound : ℕ}
    [Fintype FallbackIndex] [Fintype Z]
    (fallback : FallbackIndex → ExactVisibleRule Z k)
    (hcard :
      Fintype.card FallbackIndex *
          (PluginSampleMajority.smallSubsets
            (ExactVisiblePostSwitchSurface Z k) sampleBound).card <
        2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
        FallbackIndex Z k sampleBound fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_code_mul_smallSubsets_card_lt_boolClassifierSpace
    (Z := Z) (k := k) (sampleBound := sampleBound) fallback hcard

example {FallbackIndex Z : Type} {k sampleBound : ℕ}
    [Fintype FallbackIndex] [Fintype Z]
    (fallback : FallbackIndex → ExactVisibleRule Z k)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k sampleBound fallback).predictorFamily.predict) :
    2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      Fintype.card FallbackIndex *
        (PluginSampleMajority.smallSubsets
          (ExactVisiblePostSwitchSurface Z k) sampleBound).card :=
  boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_boolClassifierSpace_card_le_code_mul_smallSubsets_card_of_surjective
    (Z := Z) (k := k) (sampleBound := sampleBound) fallback hsurj

example {Z : Type} {k sampleBound fallbackBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hcard :
      2 ^ fallbackBits *
          (PluginSampleMajority.smallSubsets
            (ExactVisiblePostSwitchSurface Z k) sampleBound).card <
        2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound fallbackBits fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_bitCode_mul_smallSubsets_card_lt_boolClassifierSpace
    (Z := Z) (k := k) (sampleBound := sampleBound) (fallbackBits := fallbackBits)
    fallback hcard

example {Z : Type} {k sampleBound fallbackBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k sampleBound fallbackBits fallback).predictorFamily.predict) :
    2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      2 ^ fallbackBits *
        (PluginSampleMajority.smallSubsets
          (ExactVisiblePostSwitchSurface Z k) sampleBound).card :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_boolClassifierSpace_card_le_bitCode_mul_smallSubsets_card_of_surjective
    (Z := Z) (k := k) (sampleBound := sampleBound) (fallbackBits := fallbackBits)
    fallback hsurj

example {U : Type} [Fintype U] {radius : ℕ} :
    (PluginSampleMajority.smallSubsets U radius).card =
      ∑ i ∈ Finset.range (radius + 1), (Fintype.card U).choose i :=
  PluginSampleMajority.card_smallSubsets_eq_sum_range_choose (U := U) radius

example {n radius : ℕ} :
    (∑ i ∈ Finset.range (radius + 1), n.choose i) ≤
      (radius + 1) * (n + 1) ^ radius :=
  PluginSampleMajority.sum_range_choose_le_succ_mul_succ_pow n radius

example {U : Type} [Fintype U] {radius : ℕ} :
    (PluginSampleMajority.smallSubsets U radius).card ≤
      (radius + 1) * (Fintype.card U + 1) ^ radius :=
  PluginSampleMajority.card_smallSubsets_le_succ_mul_succ_card_pow (U := U) radius

example {U : Type} [Fintype U] {radius : ℕ}
    (hradius : radius < Fintype.card U) :
    PluginSampleMajority.smallSubsets U radius ⊂
      (Finset.univ : Finset (Finset U)) :=
  PluginSampleMajority.smallSubsets_ssubset_univ_of_radius_lt_card
    (U := U) (radius := radius) hradius

example {U : Type} [Fintype U] {radius : ℕ}
    (hradius : radius < Fintype.card U) :
    (PluginSampleMajority.smallSubsets U radius).card <
      2 ^ Fintype.card U :=
  PluginSampleMajority.card_smallSubsets_lt_twoPow_card_of_radius_lt_card
    (U := U) (radius := radius) hradius

example {n radius : ℕ} (hradius : radius < n) :
    (∑ i ∈ Finset.range (radius + 1), n.choose i) < 2 ^ n :=
  PluginSampleMajority.sum_range_choose_lt_twoPow_of_lt
    (n := n) (radius := radius) hradius

example {n radius radiusBits baseBits : ℕ}
    (hradius : radius + 1 ≤ 2 ^ radiusBits)
    (hbase : n + 1 ≤ 2 ^ baseBits) :
    (radius + 1) * (n + 1) ^ radius ≤
      2 ^ (radiusBits + baseBits * radius) :=
  PluginSampleMajority.succ_mul_succ_pow_le_twoPow_add_mul hradius hbase

example {radius radiusBits : ℕ}
    (hradius : radius ≤ 2 ^ radiusBits) :
    radius + 1 ≤ 2 ^ (radiusBits + 1) :=
  PluginSampleMajority.succ_le_twoPow_succ_of_le_twoPow hradius

example {n radius radiusBits baseBits : ℕ}
    (hradius : radius ≤ 2 ^ radiusBits)
    (hbase : n + 1 ≤ 2 ^ baseBits) :
    (radius + 1) * (n + 1) ^ radius ≤
      2 ^ ((radiusBits + 1) + baseBits * radius) :=
  PluginSampleMajority.succ_mul_succ_pow_le_twoPow_succ_add_mul hradius hbase

example {Z : Type} {k sampleBound fallbackBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k sampleBound fallbackBits fallback).predictorFamily.predict) :
    2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      2 ^ fallbackBits *
        ∑ i ∈ Finset.range (sampleBound + 1),
          (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose i :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_boolClassifierSpace_card_le_bitCode_mul_sum_choose_of_surjective
    (Z := Z) (k := k) (sampleBound := sampleBound) (fallbackBits := fallbackBits)
    fallback hsurj

example {Z : Type} {k sampleBound fallbackBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hcard :
      2 ^ fallbackBits *
          (∑ i ∈ Finset.range (sampleBound + 1),
            (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose i) <
        2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound fallbackBits fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_bitCode_mul_sum_choose_lt_boolClassifierSpace
    (Z := Z) (k := k) (sampleBound := sampleBound) (fallbackBits := fallbackBits)
    fallback hcard

example {Z : Type} {k sampleBound fallbackBits overheadBits : ℕ} [Fintype Z]
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
      fallbackBits + overheadBits :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_fallbackBits_add_overheadBits_ge_surfaceCard_of_sumChooseEnvelope_le_twoPow_surjective
    (Z := Z) (k := k) (sampleBound := sampleBound) (fallbackBits := fallbackBits)
    (overheadBits := overheadBits) fallback henvelope hsurj

example {Z : Type} {k sampleBound fallbackBits overheadBits : ℕ} [Fintype Z]
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
        Z k sampleBound fallbackBits fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_sumChooseEnvelope_le_twoPow_and_fallbackBits_add_overheadBits_lt_surfaceCard
    (Z := Z) (k := k) (sampleBound := sampleBound) (fallbackBits := fallbackBits)
    (overheadBits := overheadBits) fallback henvelope hbits

example {Z : Type} {k sampleBound : ℕ} [Fintype Z]
    (fallback : BitCode 0 → ExactVisibleRule Z k)
    (hbound :
      sampleBound < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound 0 fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_zeroFallbackBits_of_sampleBound_lt_surfaceCard
    (Z := Z) (k := k) (sampleBound := sampleBound) fallback hbound

example {U : Type} [Fintype U] (reference rule : U → Bool) :
    (PluginSampleMajority.disagreementSupport reference rule).card ≤
      Fintype.card U :=
  PluginSampleMajority.disagreementSupport_card_le_card reference rule

example {FallbackIndex U : Type} [Fintype FallbackIndex]
    [Nonempty FallbackIndex] [Fintype U]
    (fallback : FallbackIndex → U → Bool) {radius : ℕ}
    (hcard : Fintype.card U ≤ radius) (rule : U → Bool) :
    rule ∈ PluginSampleMajority.fallbackFamilyRadiusCover fallback radius :=
  PluginSampleMajority.mem_fallbackFamilyRadiusCover_of_nonempty_of_card_le_radius
    (fallback := fallback) hcard rule

example {FallbackIndex Z : Type} {k sampleBound : ℕ}
    [Fintype FallbackIndex] [Nonempty FallbackIndex] [Fintype Z]
    (fallback : FallbackIndex → ExactVisibleRule Z k)
    (hbound : Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound) :
    Function.Surjective
      (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
        FallbackIndex Z k sampleBound fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_surjective_of_nonempty_of_surfaceCard_le_sampleBound
    (FallbackIndex := FallbackIndex) (Z := Z) (k := k)
    (sampleBound := sampleBound) fallback hbound

example {FallbackIndex Z : Type} {k sampleBound : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k) (code : FallbackIndex) :
    (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
        FallbackIndex Z k sampleBound fallback).predictorFamily.predict
        (code, ⟨[], by simp⟩) =
      fallback code :=
  boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_emptySample_predict
    (Z := Z) (k := k) (sampleBound := sampleBound) fallback code

example {FallbackIndex Z : Type} {k sampleBound : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k)
    (hsurj : Function.Surjective fallback) :
    Function.Surjective
      (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
        FallbackIndex Z k sampleBound fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_surjective_of_fallback_surjective
    (Z := Z) (k := k) (sampleBound := sampleBound) fallback hsurj

example {FallbackIndex Z : Type} {k : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k) :
    Function.Surjective
        (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k 0 fallback).predictorFamily.predict ↔
      Function.Surjective fallback :=
  boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_zeroSample_surjective_iff_fallback_surjective
    (Z := Z) (k := k) fallback

example {Z : Type} {k sampleBound fallbackBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hbound : Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound) :
    Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound fallbackBits fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_surjective_of_surfaceCard_le_sampleBound
    (Z := Z) (k := k) (sampleBound := sampleBound)
    (fallbackBits := fallbackBits) fallback hbound

example {Z : Type} {k sampleBound : ℕ} [Fintype Z]
    (fallback : BitCode 0 → ExactVisibleRule Z k) :
    Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k sampleBound 0 fallback).predictorFamily.predict ↔
      Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_zeroFallbackBits_surjective_iff_surfaceCard_le_sampleBound
    (Z := Z) (k := k) (sampleBound := sampleBound) fallback

example {Z : Type} {k sampleBound : ℕ} [Fintype Z] :
    Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound (Fintype.card (ExactVisiblePostSwitchSurface Z k))
        (exactVisibleRuleDecode (Z := Z) (k := k))).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_surjective_exactVisibleRuleDecode
    (Z := Z) (k := k) (sampleBound := sampleBound)

example {Z : Type} {k fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k) :
    Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 0 fallbackBits fallback).predictorFamily.predict ↔
      Function.Surjective fallback :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_zeroSample_surjective_iff_fallback_surjective
    (Z := Z) (k := k) (fallbackBits := fallbackBits) fallback

example {Z : Type} {k : ℕ} [Fintype Z] :
    Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 0 (Fintype.card (ExactVisiblePostSwitchSurface Z k))
        (exactVisibleRuleDecode (Z := Z) (k := k))).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_surjective_zeroSample_exactVisibleRuleDecode
    (Z := Z) (k := k)

example {Z : Type} {k sampleBound fallbackBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k sampleBound fallbackBits fallback).predictorFamily.predict) :
    2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      2 ^ fallbackBits *
        ((sampleBound + 1) *
          (Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1) ^ sampleBound) :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_boolClassifierSpace_card_le_bitCode_mul_sampleBound_succ_mul_surfaceCard_succ_pow_of_surjective
    (Z := Z) (k := k) (sampleBound := sampleBound) (fallbackBits := fallbackBits)
    fallback hsurj

example {Z : Type} {k sampleBound fallbackBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hcard :
      2 ^ fallbackBits *
          ((sampleBound + 1) *
            (Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1) ^ sampleBound) <
        2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound fallbackBits fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_bitCode_mul_sampleBound_succ_mul_surfaceCard_succ_pow_lt_boolClassifierSpace
    (Z := Z) (k := k) (sampleBound := sampleBound) (fallbackBits := fallbackBits)
    fallback hcard

example {Z : Type} {k sampleBound fallbackBits overheadBits : ℕ} [Fintype Z]
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
      fallbackBits + overheadBits :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_fallbackBits_add_overheadBits_ge_surfaceCard_of_polynomialEnvelope_le_twoPow_surjective
    (Z := Z) (k := k) (sampleBound := sampleBound) (fallbackBits := fallbackBits)
    (overheadBits := overheadBits) fallback henvelope hsurj

example {Z : Type} {k sampleBound fallbackBits overheadBits : ℕ} [Fintype Z]
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
        Z k sampleBound fallbackBits fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_polynomialEnvelope_le_twoPow_and_fallbackBits_add_overheadBits_lt_surfaceCard
    (Z := Z) (k := k) (sampleBound := sampleBound) (fallbackBits := fallbackBits)
    (overheadBits := overheadBits) fallback henvelope hbits

example {Z : Type} {k sampleBound fallbackBits radiusBits baseBits : ℕ} [Fintype Z]
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
      fallbackBits + radiusBits + baseBits * sampleBound :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_fallbackBits_add_radiusBits_add_baseBits_mul_sampleBound_ge_surfaceCard_of_envelopeFactors_le_twoPow_surjective
    (Z := Z) (k := k) (sampleBound := sampleBound) (fallbackBits := fallbackBits)
    (radiusBits := radiusBits) (baseBits := baseBits)
    fallback hradius hbase hsurj

example {Z : Type} {k sampleBound fallbackBits radiusBits baseBits : ℕ} [Fintype Z]
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
        Z k sampleBound fallbackBits fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_envelopeFactors_le_twoPow_and_fallbackBits_add_radiusBits_add_baseBits_mul_sampleBound_lt_surfaceCard
    (Z := Z) (k := k) (sampleBound := sampleBound) (fallbackBits := fallbackBits)
    (radiusBits := radiusBits) (baseBits := baseBits)
    fallback hradius hbase hbits

example {Z : Type} {k sampleBound fallbackBits radiusBits baseBits : ℕ} [Fintype Z]
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
      fallbackBits + (radiusBits + 1) + baseBits * sampleBound :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_fallbackBits_add_radiusBits_succ_add_baseBits_mul_sampleBound_ge_surfaceCard_of_sampleBound_le_twoPow_and_base_le_twoPow_surjective
    (Z := Z) (k := k) (sampleBound := sampleBound) (fallbackBits := fallbackBits)
    (radiusBits := radiusBits) (baseBits := baseBits)
    fallback hradius hbase hsurj

example {Z : Type} {k sampleBound fallbackBits radiusBits baseBits : ℕ} [Fintype Z]
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
        Z k sampleBound fallbackBits fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_sampleBound_le_twoPow_and_base_le_twoPow_and_fallbackBits_add_radiusBits_succ_add_baseBits_mul_sampleBound_lt_surfaceCard
    (Z := Z) (k := k) (sampleBound := sampleBound) (fallbackBits := fallbackBits)
    (radiusBits := radiusBits) (baseBits := baseBits)
    fallback hradius hbase hbits

example {Z : Type} {k sampleBound fallbackBits radiusBits baseBits : ℕ} [Fintype Z]
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
      fallbackBits + (radiusBits + 1) + (baseBits + 1) * sampleBound :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_fallbackBits_add_radiusBits_succ_add_baseBits_succ_mul_sampleBound_ge_surfaceCard_of_sampleBound_le_twoPow_and_surfaceCard_le_twoPow_surjective
    (Z := Z) (k := k) (sampleBound := sampleBound) (fallbackBits := fallbackBits)
    (radiusBits := radiusBits) (baseBits := baseBits)
    fallback hradius hbase hsurj

example {Z : Type} {k sampleBound fallbackBits radiusBits baseBits : ℕ} [Fintype Z]
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
        Z k sampleBound fallbackBits fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_sampleBound_le_twoPow_and_surfaceCard_le_twoPow_and_fallbackBits_add_radiusBits_succ_add_baseBits_succ_mul_sampleBound_lt_surfaceCard
    (Z := Z) (k := k) (sampleBound := sampleBound) (fallbackBits := fallbackBits)
    (radiusBits := radiusBits) (baseBits := baseBits)
    fallback hradius hbase hbits

example {Z : Type} {k fallbackBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 0 fallbackBits fallback).predictorFamily.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ fallbackBits :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_fallbackBits_ge_surfaceCard_of_zeroSample_surjective
    (Z := Z) (k := k) (fallbackBits := fallbackBits) fallback hsurj

example {Z : Type} {k fallbackBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hbits : fallbackBits < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 0 fallbackBits fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_zeroSample_of_fallbackBits_lt_surfaceCard
    (Z := Z) (k := k) (fallbackBits := fallbackBits) fallback hbits

example {Z : Type} {k fallbackBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 1 fallbackBits fallback).predictorFamily.predict) :
    2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      2 ^ fallbackBits *
        (Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1) :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_boolClassifierSpace_card_le_bitCode_mul_surfaceCard_succ_of_oneSample_surjective
    (Z := Z) (k := k) (fallbackBits := fallbackBits) fallback hsurj

example {Z : Type} {k fallbackBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hcard :
      2 ^ fallbackBits *
          (Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1) <
        2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 1 fallbackBits fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_oneSample_of_bitCode_mul_surfaceCard_succ_lt_boolClassifierSpace
    (Z := Z) (k := k) (fallbackBits := fallbackBits) fallback hcard

example {Z : Type} {k fallbackBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 2 fallbackBits fallback).predictorFamily.predict) :
    2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      2 ^ fallbackBits *
        (1 + Fintype.card (ExactVisiblePostSwitchSurface Z k) +
          (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose 2) :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_boolClassifierSpace_card_le_bitCode_mul_one_add_surfaceCard_add_choose_two_of_twoSample_surjective
    (Z := Z) (k := k) (fallbackBits := fallbackBits) fallback hsurj

example {Z : Type} {k fallbackBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hcard :
      2 ^ fallbackBits *
          (1 + Fintype.card (ExactVisiblePostSwitchSurface Z k) +
            (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose 2) <
        2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 2 fallbackBits fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_twoSample_of_bitCode_mul_one_add_surfaceCard_add_choose_two_lt_boolClassifierSpace
    (Z := Z) (k := k) (fallbackBits := fallbackBits) fallback hcard

example {Z : Type} {k fallbackBits overheadBits : ℕ} [Fintype Z]
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
      fallbackBits + overheadBits :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_fallbackBits_add_overheadBits_ge_surfaceCard_of_twoSample_quadraticEnvelope_le_twoPow_surjective
    (Z := Z) (k := k) (fallbackBits := fallbackBits) (overheadBits := overheadBits)
    fallback henvelope hsurj

example {Z : Type} {k fallbackBits overheadBits : ℕ} [Fintype Z]
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
        Z k 2 fallbackBits fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_twoSample_of_quadraticEnvelope_le_twoPow_and_fallbackBits_add_overheadBits_lt_surfaceCard
    (Z := Z) (k := k) (fallbackBits := fallbackBits) (overheadBits := overheadBits)
    fallback henvelope hbits

example {Z : Type} {k fallbackBits baseBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hbase :
      Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1 ≤
        2 ^ baseBits)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 1 fallbackBits fallback).predictorFamily.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      fallbackBits + baseBits :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_fallbackBits_add_baseBits_ge_surfaceCard_of_oneSample_surfaceCard_succ_le_twoPow_surjective
    (Z := Z) (k := k) (fallbackBits := fallbackBits) (baseBits := baseBits)
    fallback hbase hsurj

example {Z : Type} {k fallbackBits baseBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hbase :
      Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1 ≤
        2 ^ baseBits)
    (hbits :
      fallbackBits + baseBits <
        Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 1 fallbackBits fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_oneSample_of_surfaceCard_succ_le_twoPow_and_fallbackBits_add_baseBits_lt_surfaceCard
    (Z := Z) (k := k) (fallbackBits := fallbackBits) (baseBits := baseBits)
    fallback hbase hbits

example {Z : Type} {k fallbackBits baseBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hbase :
      Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
        2 ^ baseBits)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 1 fallbackBits fallback).predictorFamily.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      fallbackBits + (baseBits + 1) :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_fallbackBits_add_baseBits_succ_ge_surfaceCard_of_oneSample_surfaceCard_le_twoPow_surjective
    (Z := Z) (k := k) (fallbackBits := fallbackBits) (baseBits := baseBits)
    fallback hbase hsurj

example {Z : Type} {k fallbackBits baseBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hbase :
      Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
        2 ^ baseBits)
    (hbits :
      fallbackBits + (baseBits + 1) <
        Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 1 fallbackBits fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_oneSample_of_surfaceCard_le_twoPow_and_fallbackBits_add_baseBits_succ_lt_surfaceCard
    (Z := Z) (k := k) (fallbackBits := fallbackBits) (baseBits := baseBits)
    fallback hbase hbits

example {Z : Type} {k s sampleBound : ℕ} [Fintype Z]
    (hbound : Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).predictorFamily.FinitePredictorCover
        (2 ^ s) :=
  boundedSamplePluginMajorityActualSwitchedLocalInterface_not_finitePredictorCover_of_lt_surfaceCard
    (Z := Z) (k := k) (s := s) (sampleBound := sampleBound) hbound hs

example {Z : Type} {k s sampleBound clock : ℕ} [Fintype Z]
    (hbound : Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ClockedKpolyFiniteLearningPayload
        (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).predictorFamily
        s clock :=
  boundedSamplePluginMajorityActualSwitchedLocalInterface_not_clockedKpolyFiniteLearningPayload_of_lt_surfaceCard
    (Z := Z) (k := k) (s := s) (sampleBound := sampleBound) (clock := clock) hbound hs

example {Z : Type} {k s sampleBound : ℕ} [Fintype Z]
    (hbound : Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.BitCodeData
          (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound) s) :=
  boundedSamplePluginMajorityActualSwitchedLocalInterface_not_bitCodeData_of_lt_surfaceCard
    (Z := Z) (k := k) (s := s) (sampleBound := sampleBound) hbound hs

example {Z : Type} {k r sampleBound : ℕ} [Fintype Z]
    (hbound : Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound)
    (zfeat : Z → BitVec r)
    (hs : r + 2 * k + 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.ZABDecisionListData
          (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound) zfeat) :=
  boundedSamplePluginMajorityActualSwitchedLocalInterface_not_zabDecisionListData_of_lt_surfaceCard
    (Z := Z) (k := k) (r := r) (sampleBound := sampleBound) hbound zfeat hs

end Mettapedia.Computability.PNP.BoundedSampleMajorityObstructionRegression
