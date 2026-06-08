import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoveryHeavyRegionCardinalityObstruction
import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoveryPayloadObstructionRegression
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic

namespace Mettapedia.Computability.PNP

open scoped ENNReal

def exactVisiblePostSwitchSurfaceFin30EquivActualSparseRecoveryHeavyRegionCardinality :
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

noncomputable def fin3ZeroOneHalfMeasureActualSparseRecoveryHeavyRegionCardinality :
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
            exactVisiblePostSwitchSurfaceFin30EquivActualSparseRecoveryHeavyRegionCardinality
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

noncomputable def fin3ZeroOneRegionActualSparseRecoveryHeavyRegionCardinality :
    Finset (ExactVisiblePostSwitchSurface (Fin 3) 0) :=
  by
    classical
    exact
      insert
        fin3ZeroVisiblePointActualSparseRecoveryPayload
        {fin3OneVisiblePointActualSparseRecoveryPayload}

theorem fin3ZeroOneRegionActualSparseRecoveryHeavyRegionCardinality_card :
    fin3ZeroOneRegionActualSparseRecoveryHeavyRegionCardinality.card = 2 := by
  simp [fin3ZeroOneRegionActualSparseRecoveryHeavyRegionCardinality,
    fin3ZeroVisiblePointActualSparseRecoveryPayload,
    fin3OneVisiblePointActualSparseRecoveryPayload]

theorem fin3ZeroOneRegionActualSparseRecoveryHeavyRegionCardinality_mass_eq_one :
    fin3ZeroOneRegionActualSparseRecoveryHeavyRegionCardinality.sum
        (fun x => fin3ZeroOneHalfMeasureActualSparseRecoveryHeavyRegionCardinality x)
      = 1 := by
  calc
    fin3ZeroOneRegionActualSparseRecoveryHeavyRegionCardinality.sum
        (fun x => fin3ZeroOneHalfMeasureActualSparseRecoveryHeavyRegionCardinality x)
      = (2 : ℝ≥0∞)⁻¹ + (2 : ℝ≥0∞)⁻¹ := by
          simp [fin3ZeroOneRegionActualSparseRecoveryHeavyRegionCardinality,
            fin3ZeroOneHalfMeasureActualSparseRecoveryHeavyRegionCardinality,
            fin3ZeroVisiblePointActualSparseRecoveryPayload,
            fin3OneVisiblePointActualSparseRecoveryPayload]
    _ = 1 := by
      simpa [two_mul] using ENNReal.inv_two_add_inv_two

private noncomputable def fin3ThreeQuartersActualSparseRecoveryHeavyRegionCardinality :
    ℝ≥0∞ :=
  (3 : ℝ≥0∞) / 4

private theorem fin3ThreeQuartersActualSparseRecoveryHeavyRegionCardinality_lt_one :
    fin3ThreeQuartersActualSparseRecoveryHeavyRegionCardinality < 1 := by
  have h₁ :
      fin3ThreeQuartersActualSparseRecoveryHeavyRegionCardinality = (3 : ℝ≥0∞) / 4 := by
    rfl
  have h₂ : (1 : ℝ≥0∞) = (4 : ℝ≥0∞) / 4 := by
    rw [ENNReal.div_self (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by simp)]
  rw [h₁, h₂]
  exact ENNReal.div_lt_div_right (by norm_num) (by simp) (by norm_num)

private theorem fin3ThreeQuartersActualSparseRecoveryHeavyRegionCardinality_lt_regionMass :
    fin3ThreeQuartersActualSparseRecoveryHeavyRegionCardinality <
      fin3ZeroOneRegionActualSparseRecoveryHeavyRegionCardinality.sum
        (fun x => fin3ZeroOneHalfMeasureActualSparseRecoveryHeavyRegionCardinality x) := by
  rw [fin3ZeroOneRegionActualSparseRecoveryHeavyRegionCardinality_mass_eq_one]
  exact fin3ThreeQuartersActualSparseRecoveryHeavyRegionCardinality_lt_one

/-- The theorem-shape canary: on a two-point heavy region of the three-point
visible surface, any hypothetical recovery packet on the genuinely non-surjective
`Fin 5` family already forces that injective family to fit inside the Boolean
trace space on the region. -/
theorem fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayload_card_le_two_pow_regionCard_of_nonempty_recovery_regression
    {q : ℝ≥0∞}
    (hmass :
      q <
        fin3ZeroOneRegionActualSparseRecoveryHeavyRegionCardinality.sum
          (fun x => fin3ZeroOneHalfMeasureActualSparseRecoveryHeavyRegionCardinality x))
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          fin3ZeroOneHalfMeasureActualSparseRecoveryHeavyRegionCardinality
          fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayload
          fin3ToBitVec0ActualSparseRecoveryPayload
          q)) :
    Fintype.card (Fin 5) ≤
      2 ^ fin3ZeroOneRegionActualSparseRecoveryHeavyRegionCardinality.card := by
  rcases h with ⟨h⟩
  exact
    h.card_le_two_pow_regionCard_of_injective_predict_of_lt_regionMass
      fin3ZeroOneRegionActualSparseRecoveryHeavyRegionCardinality
      hmass
      fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayload_injective_predict

/-- Distinct-axis negative canary: with the split measure `1/2, 1/2, 0`, no
single atom exceeds `3/4`, but the two-point region already has mass `1`, so the
genuinely non-surjective `Fin 5` family is blocked by the new `2 ^ |region|`
bound. -/
theorem fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayload_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_heavyRegionCardinality_regression :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          fin3ZeroOneHalfMeasureActualSparseRecoveryHeavyRegionCardinality
          fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayload
          fin3ToBitVec0ActualSparseRecoveryPayload
          fin3ThreeQuartersActualSparseRecoveryHeavyRegionCardinality) := by
  have hcard :
      2 ^ fin3ZeroOneRegionActualSparseRecoveryHeavyRegionCardinality.card <
        Fintype.card (Fin 5) := by
    rw [fin3ZeroOneRegionActualSparseRecoveryHeavyRegionCardinality_card]
    norm_num
  exact
    ActualSwitchedLocalInterface.not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_lt_regionCard_of_injective_predict_of_lt_regionMass
      (μ := fin3ZeroOneHalfMeasureActualSparseRecoveryHeavyRegionCardinality)
      (T := fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayload)
      (r := 0)
      (Index := Fin 5)
      (zfeat := fin3ToBitVec0ActualSparseRecoveryPayload)
      fin3ZeroOneRegionActualSparseRecoveryHeavyRegionCardinality
      fin5ProbeActualSwitchedLocalInterfaceActualSparseRecoveryPayload_injective_predict
      fin3ThreeQuartersActualSparseRecoveryHeavyRegionCardinality_lt_regionMass
      hcard

end Mettapedia.Computability.PNP
