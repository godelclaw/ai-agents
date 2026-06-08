import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoveryDataRegression
import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoveryPayloadObstruction
import Mathlib.Tactic

namespace Mettapedia.Computability.PNP

/-- Positive boundary canary: on the two-point `Bool, k = 0` visible surface,
the existing recovery witness still supplies the clocked finite-learning
payload.  So the new obstruction is not vacuous. -/
theorem fullRuleActualSwitchedLocalInterface_sharedExactZABSparseThresholdERMRecoveryData_clockedKpolyFiniteLearningPayload_bool0_payload_regression :
    ClockedKpolyFiniteLearningPayload
      (fullRuleActualSwitchedLocalInterface Bool 0).predictorFamily
      (2 * allAffinePointBlockFeatureCount (1 + (0 + 0)))
      0 := by
  exact
    fullRuleActualSwitchedLocalInterface_sharedExactZABSparseThresholdERMRecoveryData_clockedKpolyFiniteLearningPayload_bool0_regression

def fin3ToBitVec0ActualSparseRecoveryPayload : Fin 3 → BitVec 0 := fun _ => zeroVec

noncomputable def fin3ZeroVisiblePointActualSparseRecoveryPayload :
    ExactVisiblePostSwitchSurface (Fin 3) 0 :=
  ⟨0, zeroVec, zeroVec⟩

noncomputable def fin3OneVisiblePointActualSparseRecoveryPayload :
    ExactVisiblePostSwitchSurface (Fin 3) 0 :=
  ⟨1, zeroVec, zeroVec⟩

noncomputable def fin3TwoVisiblePointActualSparseRecoveryPayload :
    ExactVisiblePostSwitchSurface (Fin 3) 0 :=
  ⟨2, zeroVec, zeroVec⟩

noncomputable def fin3PureMeasureActualSparseRecoveryPayload :
    PMF (ExactVisiblePostSwitchSurface (Fin 3) 0) :=
  PMF.pure fin3ZeroVisiblePointActualSparseRecoveryPayload

theorem fullRuleActualSwitchedLocalInterface_lt_predictorCard_fin3k0r0_payload_regression :
    2 ^ (2 * allAffinePointBlockFeatureCount (0 + (0 + 0))) <
      2 ^ Fintype.card (ExactVisiblePostSwitchSurface (Fin 3) 0) := by
  rw [card_exactVisiblePostSwitchSurface (Z := Fin 3) (k := 0)]
  norm_num [allAffinePointBlockFeatureCount_eq]

def fin5ProbeFamilyActualSparseRecoveryPayload
    (p : Fin 5) :
    ExactVisiblePostSwitchSurface (Fin 3) 0 → Bool :=
  match p.1 with
  | 0 => fun _ => false
  | 1 => fun u => decide (u.z = 0)
  | 2 => fun u => decide (u.z = 1)
  | 3 => fun u => decide (u.z = 2)
  | _ => fun _ => true

theorem fin5ProbeFamilyActualSparseRecoveryPayload_injective :
    Function.Injective fin5ProbeFamilyActualSparseRecoveryPayload := by
  decide

def fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayload :
    ActualSwitchedLocalInterface
      (Fin 3)
      0
      (Fin 5)
      (ExactVisiblePostSwitchSurface (Fin 3) 0) where
  zOf := fun u => u.z
  aOf := fun _ u => u.a
  bOf := fun u => u.b
  localRule := fin5ProbeFamilyActualSparseRecoveryPayload
  output := fun p u => fin5ProbeFamilyActualSparseRecoveryPayload p u
  output_eq_local := by
    intro p u
    rfl

def fin3TwoPointRuleActualSparseRecoveryPayload :
    ExactVisiblePostSwitchSurface (Fin 3) 0 → Bool :=
  fun u => decide (u.z = 0 ∨ u.z = 1)

theorem fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayload_not_surjective :
    ¬ Function.Surjective
        fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayload.predictorFamily.predict := by
  intro hsurj
  rcases hsurj fin3TwoPointRuleActualSparseRecoveryPayload with ⟨p, hp⟩
  fin_cases p
  all_goals
    have h0 := congrFun hp fin3ZeroVisiblePointActualSparseRecoveryPayload
    have h1 := congrFun hp fin3OneVisiblePointActualSparseRecoveryPayload
    have h2 := congrFun hp fin3TwoVisiblePointActualSparseRecoveryPayload
    simp [fin3TwoPointRuleActualSparseRecoveryPayload,
      fin3ZeroVisiblePointActualSparseRecoveryPayload,
      fin3OneVisiblePointActualSparseRecoveryPayload,
      fin3TwoVisiblePointActualSparseRecoveryPayload] at h0 h1 h2
    contradiction

theorem fin5ProbeFamilyActualSparseRecoveryPayload_lt_card_regression :
    2 ^ (2 * allAffinePointBlockFeatureCount (0 + (0 + 0))) < Fintype.card (Fin 5) := by
  norm_num [allAffinePointBlockFeatureCount_eq]

theorem fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayload_injective_predict :
    Function.Injective
      fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayload.predictorFamily.predict := by
  exact fin5ProbeFamilyActualSparseRecoveryPayload_injective

/-- Negative canary: on a three-point visible surface, the manuscript-facing
full-rule recovery packet would force a 2-bit finite-learning payload, but the
full Boolean rule family has size `2^3 = 8`, so the route is blocked. -/
theorem fullRuleActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_fin3k0r0_payload_regression :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          fin3PureMeasureActualSparseRecoveryPayload
          (fullRuleActualSwitchedLocalInterface (Fin 3) 0)
          fin3ToBitVec0ActualSparseRecoveryPayload
          0) := by
  exact
    ActualSwitchedLocalInterface.fullRuleActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_lt_predictorCard
      (μ := fin3PureMeasureActualSparseRecoveryPayload)
      (k := 0)
      (r := 0)
      (q := 0)
      fin3ToBitVec0ActualSparseRecoveryPayload
      fullRuleActualSwitchedLocalInterface_lt_predictorCard_fin3k0r0_payload_regression

/-- The full-rule payload obstruction already removes the extractor choice on
the three-point visible surface: below the payload budget there is no
`Fin 3 → BitVec 0` extractor at all supporting the manuscript-facing recovery
packet. -/
theorem fullRuleActualSwitchedLocalInterface_not_exists_sharedExactZABSparseThresholdERMRecoveryData_fin3k0r0_payload_regression :
    ¬ ∃ zfeat : Fin 3 → BitVec 0,
        Nonempty
          (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
            fin3PureMeasureActualSparseRecoveryPayload
            (fullRuleActualSwitchedLocalInterface (Fin 3) 0)
            zfeat
            0) := by
  exact
    ActualSwitchedLocalInterface.fullRuleActualSwitchedLocalInterface_not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_lt_predictorCard
      (μ := fin3PureMeasureActualSparseRecoveryPayload)
      (Z := Fin 3)
      (k := 0)
      (r := 0)
      (q := 0)
      fullRuleActualSwitchedLocalInterface_lt_predictorCard_fin3k0r0_payload_regression

/-- Distinct-axis negative canary: even a genuinely non-surjective actual-local
family is blocked once it already realizes five distinct visible predictors on
the three-point surface, because the recovery payload budget there only permits
at most four predictors. -/
theorem fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayload_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_regression :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          fin3PureMeasureActualSparseRecoveryPayload
          fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayload
          fin3ToBitVec0ActualSparseRecoveryPayload
          0) := by
  exact
    ActualSwitchedLocalInterface.not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_injective_predict_of_lt_indexCard
      (μ := fin3PureMeasureActualSparseRecoveryPayload)
      (T := fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayload)
      (Index := Fin 5)
      (r := 0)
      (zfeat := fin3ToBitVec0ActualSparseRecoveryPayload)
      fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayload_injective_predict
      fin5ProbeFamilyActualSparseRecoveryPayload_lt_card_regression

/-- The same non-surjective five-predictor family also cannot be rescued by
changing the extractor: once the realized predictor image is already too large,
no `Fin 3 → BitVec 0` extractor can support the manuscript-facing recovery
packet. -/
theorem fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayload_not_exists_sharedExactZABSparseThresholdERMRecoveryData_regression :
    ¬ ∃ zfeat : Fin 3 → BitVec 0,
        Nonempty
          (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
            fin3PureMeasureActualSparseRecoveryPayload
            fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayload
            zfeat
            0) := by
  exact
    ActualSwitchedLocalInterface.not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_injective_predict_of_lt_indexCard
      (μ := fin3PureMeasureActualSparseRecoveryPayload)
      (T := fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayload)
      (Index := Fin 5)
      (r := 0)
      (q := 0)
      fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayload_injective_predict
      fin5ProbeFamilyActualSparseRecoveryPayload_lt_card_regression

end Mettapedia.Computability.PNP
