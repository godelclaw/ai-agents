import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoveryDataRegression
import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoveryPayloadObstructionRegression
import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoveryQuotientObstruction
import Mathlib.Tactic

namespace Mettapedia.Computability.PNP

def fin4RuleFamilyBool0Quotient
    (p : Fin 4) :
    ExactVisiblePostSwitchSurface Bool 0 → Bool :=
  match p.1 with
  | 0 => fun _ => false
  | 1 => fun u => decide (u.z = false)
  | 2 => fun u => decide (u.z = true)
  | _ => fun _ => true

theorem fin4RuleFamilyBool0Quotient_injective :
    Function.Injective fin4RuleFamilyBool0Quotient := by
  decide

/-- Positive canary: on the two-point `Bool, k = 0` visible surface, the
existing full-rule recovery witness already forces the full realized rule space
to fit inside the point-block quotient budget. -/
theorem fullRuleActualSwitchedLocalInterface_card_le_pointBlockQuotientBudget_bool0_quotient_regression :
    Fintype.card (Fin 4) ≤
      2 ^ (2 * allAffinePointBlockFeatureCount (1 + (0 + 0))) := by
  rcases
    fullRuleActualSwitchedLocalInterface_nonempty_sharedExactZABSparseThresholdERMRecoveryData_bool0_regression
    with ⟨h⟩
  exact
    h.card_le_pointBlockQuotientBudget_of_injective_realization
      (Probe := Fin 4)
      (target := fin4RuleFamilyBool0Quotient)
      fin4RuleFamilyBool0Quotient_injective
      (by
        intro p
        exact fullRuleActualSwitchedLocalInterface_surjective Bool 0
          (fin4RuleFamilyBool0Quotient p))

/-- Distinct-axis negative canary: the same genuinely non-surjective `Fin 5`
actual-local family from the payload regressions is already blocked at the
quotient-code layer, because recovery would force a four-code quotient while
the actual predictor map is injective on five indices. -/
theorem fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayload_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_quotient_regression :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          fin3PureMeasureActualSparseRecoveryPayload
          fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayload
          fin3ToBitVec0ActualSparseRecoveryPayload
          0) := by
  exact
    ActualSwitchedLocalInterface.not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_injective_predict_of_pointBlockQuotientBudget_lt_indexCard
      (μ := fin3PureMeasureActualSparseRecoveryPayload)
      (T := fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayload)
      (Index := Fin 5)
      (r := 0)
      (zfeat := fin3ToBitVec0ActualSparseRecoveryPayload)
      fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayload_injective_predict
      fin5ProbeFamilyActualSparseRecoveryPayload_lt_card_regression

/-- The same non-surjective five-index family also cannot be rescued by
changing the extractor at the quotient layer: once the realized predictor image
already exceeds the four-code quotient budget, no `Fin 3 → BitVec 0` extractor
can support the manuscript-facing recovery packet. -/
theorem fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayload_not_exists_sharedExactZABSparseThresholdERMRecoveryData_quotient_regression :
    ¬ ∃ zfeat : Fin 3 → BitVec 0,
        Nonempty
          (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
            fin3PureMeasureActualSparseRecoveryPayload
            fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayload
            zfeat
            0) := by
  exact
    ActualSwitchedLocalInterface.not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_injective_predict_of_pointBlockQuotientBudget_lt_indexCard
      (μ := fin3PureMeasureActualSparseRecoveryPayload)
      (T := fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayload)
      (Index := Fin 5)
      (r := 0)
      (q := 0)
      fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayload_injective_predict
      fin5ProbeFamilyActualSparseRecoveryPayload_lt_card_regression

end Mettapedia.Computability.PNP
