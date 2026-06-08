import Mettapedia.QuantumTheory.YangMills.ExtractionProjection

/-!
# Yang-Mills Extraction Observable Audit

The Yang-Mills manuscript uses the extended extraction `P≤dmax` for the RG
bootstrap, while the coupling/observable flow is read off from the standard
projection `P≤4`.

This file packages the downstream consequence of that split: any observable
that depends only on the standard extraction is unchanged by the higher
`5..dmax` extracted block.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills

/-- An observable on coefficient families is determined by the standard
extraction if two inputs with the same `P≤4` projection always produce the same
output. -/
def DeterminedByStandardExtraction
    {α β : Type*} [Zero α]
    (F : DimensionCoefficients α → β) : Prop :=
  ∀ ⦃coeff₁ coeff₂ : DimensionCoefficients α⦄,
    standardExtraction (α := α) coeff₁ =
        standardExtraction (α := α) coeff₂ →
      F coeff₁ = F coeff₂

/-- A pointwise factorization through `P≤4` is enough to show that an
observable is determined by the standard extraction. -/
theorem DeterminedByStandardExtraction.of_eq_on_standardExtraction
    {α β : Type*} [Zero α]
    {F : DimensionCoefficients α → β}
    (hF : ∀ coeff : DimensionCoefficients α,
      F coeff = F (standardExtraction (α := α) coeff)) :
    DeterminedByStandardExtraction (α := α) F := by
  intro coeff₁ coeff₂ hstd
  rw [hF coeff₁, hF coeff₂, hstd]

/-- An observable determined by `P≤4` cannot distinguish the extended
extraction from the original coefficients once `dmax ≥ 4`. -/
theorem DeterminedByStandardExtraction.extendedExtraction_eq
    {α β : Type*} [Zero α]
    {F : DimensionCoefficients α → β}
    (hF : DeterminedByStandardExtraction (α := α) F)
    {dmax : CanonicalDimension}
    (hd : 4 ≤ dmax) (coeff : DimensionCoefficients α) :
    F (extendedExtraction dmax coeff) = F coeff := by
  apply hF
  exact standardExtraction_after_extendedExtraction_of_four_le (α := α) hd coeff

/-- An observable determined by `P≤4` ignores the addition of a pure higher
extracted block. -/
theorem DeterminedByStandardExtraction.add_higherExtractionBlock_eq
    {α β : Type*} [AddMonoid α]
    {F : DimensionCoefficients α → β}
    (hF : DeterminedByStandardExtraction (α := α) F)
    (dmax : CanonicalDimension)
    (coeff extra : DimensionCoefficients α) :
    F (coeff + higherExtractionBlock dmax extra) = F coeff := by
  apply hF
  exact standardExtraction_add_higherExtractionBlock_eq (α := α) dmax coeff extra

/-- A `P≤4`-determined observable sends the pure higher extracted block to the
same value as the zero coefficient family. -/
theorem DeterminedByStandardExtraction.higherExtractionBlock_eq_zero
    {α β : Type*} [AddMonoid α]
    {F : DimensionCoefficients α → β}
    (hF : DeterminedByStandardExtraction (α := α) F)
    (dmax : CanonicalDimension)
    (coeff : DimensionCoefficients α) :
    F (higherExtractionBlock dmax coeff) = F 0 := by
  apply hF
  calc
    standardExtraction (α := α) (higherExtractionBlock dmax coeff) = 0 := by
      exact standardExtraction_higherExtractionBlock_eq_zero (α := α) dmax coeff
    _ = standardExtraction (α := α) (0 : DimensionCoefficients α) := by
      symm
      simpa [standardExtraction] using (extractLE_zero (α := α) 4)

/-- Residual form: after subtracting the standard extraction from the extended
one, a `P≤4`-determined observable sees only the zero family. -/
theorem DeterminedByStandardExtraction.extendedExtraction_sub_standard_eq_zero
    {α β : Type*} [AddGroup α]
    {F : DimensionCoefficients α → β}
    (hF : DeterminedByStandardExtraction (α := α) F)
    {dmax : CanonicalDimension}
    (hd : 4 ≤ dmax) (coeff : DimensionCoefficients α) :
    F (extendedExtraction dmax coeff - standardExtraction (α := α) coeff) = F 0 := by
  apply hF
  calc
    standardExtraction (α := α)
        (extendedExtraction dmax coeff - standardExtraction (α := α) coeff) = 0 := by
          exact standardExtraction_extendedExtraction_sub_standard_eq_zero_of_four_le
            (α := α) hd coeff
    _ = standardExtraction (α := α) (0 : DimensionCoefficients α) := by
      symm
      simpa [standardExtraction] using (extractLE_zero (α := α) 4)

/-- If an observable splits as a standard-extraction part plus an error term,
then adding a pure higher extracted block changes only the error term. -/
theorem difference_eq_errorDifference_of_add_higherExtractionBlock
    {α β : Type*} [AddMonoid α] [AddCommGroup β]
    {G F E : DimensionCoefficients α → β}
    (hF : DeterminedByStandardExtraction (α := α) F)
    (hdecomp : ∀ coeff : DimensionCoefficients α, G coeff = F coeff + E coeff)
    (dmax : CanonicalDimension)
    (coeff extra : DimensionCoefficients α) :
    G (coeff + higherExtractionBlock dmax extra) - G coeff =
      E (coeff + higherExtractionBlock dmax extra) - E coeff := by
  rw [hdecomp, hdecomp]
  rw [hF.add_higherExtractionBlock_eq dmax coeff extra]
  abel

/-- If an observable splits as a standard-extraction part plus an error term,
then replacing coefficients by their extended extraction changes only the error
term. -/
theorem difference_eq_errorDifference_of_extendedExtraction
    {α β : Type*} [Zero α] [AddCommGroup β]
    {G F E : DimensionCoefficients α → β}
    (hF : DeterminedByStandardExtraction (α := α) F)
    (hdecomp : ∀ coeff : DimensionCoefficients α, G coeff = F coeff + E coeff)
    {dmax : CanonicalDimension}
    (hd : 4 ≤ dmax) (coeff : DimensionCoefficients α) :
    G (extendedExtraction dmax coeff) - G coeff =
      E (extendedExtraction dmax coeff) - E coeff := by
  rw [hdecomp, hdecomp]
  rw [hF.extendedExtraction_eq hd coeff]
  abel

/-- Residual form: once the standard-extraction contribution is split off, the
extended-minus-standard residue contributes only through the error term. -/
theorem difference_from_zero_eq_errorDifference_of_extendedExtraction_sub_standard
    {α β : Type*} [AddGroup α] [AddCommGroup β]
    {G F E : DimensionCoefficients α → β}
    (hF : DeterminedByStandardExtraction (α := α) F)
    (hdecomp : ∀ coeff : DimensionCoefficients α, G coeff = F coeff + E coeff)
    {dmax : CanonicalDimension}
    (hd : 4 ≤ dmax) (coeff : DimensionCoefficients α) :
    G (extendedExtraction dmax coeff - standardExtraction (α := α) coeff) - G 0 =
      E (extendedExtraction dmax coeff - standardExtraction (α := α) coeff) - E 0 := by
  rw [hdecomp, hdecomp]
  rw [hF.extendedExtraction_sub_standard_eq_zero hd coeff]
  abel

/-- Any norm bound for the error-term response to a higher extracted block is
automatically the same norm bound for the full observable. -/
theorem norm_difference_le_of_add_higherExtractionBlock_errorBound
    {α β : Type*} [AddMonoid α] [NormedAddCommGroup β]
    {G F E : DimensionCoefficients α → β}
    (hF : DeterminedByStandardExtraction (α := α) F)
    (hdecomp : ∀ coeff : DimensionCoefficients α, G coeff = F coeff + E coeff)
    (dmax : CanonicalDimension)
    (coeff extra : DimensionCoefficients α)
    {B : ℝ}
    (hE : ‖E (coeff + higherExtractionBlock dmax extra) - E coeff‖ ≤ B) :
    ‖G (coeff + higherExtractionBlock dmax extra) - G coeff‖ ≤ B := by
  rw [difference_eq_errorDifference_of_add_higherExtractionBlock
    (α := α) (β := β) hF hdecomp dmax coeff extra]
  exact hE

/-- Any norm bound for the error-term response to extended extraction is
automatically the same norm bound for the full observable. -/
theorem norm_difference_le_of_extendedExtraction_errorBound
    {α β : Type*} [Zero α] [NormedAddCommGroup β]
    {G F E : DimensionCoefficients α → β}
    (hF : DeterminedByStandardExtraction (α := α) F)
    (hdecomp : ∀ coeff : DimensionCoefficients α, G coeff = F coeff + E coeff)
    {dmax : CanonicalDimension}
    (hd : 4 ≤ dmax) (coeff : DimensionCoefficients α)
    {B : ℝ}
    (hE : ‖E (extendedExtraction dmax coeff) - E coeff‖ ≤ B) :
    ‖G (extendedExtraction dmax coeff) - G coeff‖ ≤ B := by
  rw [difference_eq_errorDifference_of_extendedExtraction
    (α := α) (β := β) hF hdecomp hd coeff]
  exact hE

/-- Real-valued specialization: if the error-term response to extended
extraction is bounded by `B`, then the full observable changes by at most `B`
in absolute value. -/
theorem abs_difference_le_of_extendedExtraction_errorBound
    {α : Type*} [Zero α]
    {G F E : DimensionCoefficients α → ℝ}
    (hF : DeterminedByStandardExtraction (α := α) F)
    (hdecomp : ∀ coeff : DimensionCoefficients α, G coeff = F coeff + E coeff)
    {dmax : CanonicalDimension}
    (hd : 4 ≤ dmax) (coeff : DimensionCoefficients α)
    {B : ℝ}
    (hE : |E (extendedExtraction dmax coeff) - E coeff| ≤ B) :
    |G (extendedExtraction dmax coeff) - G coeff| ≤ B := by
  simpa [Real.norm_eq_abs] using
    (norm_difference_le_of_extendedExtraction_errorBound
      (α := α) (β := ℝ) hF hdecomp hd coeff
      (by simpa [Real.norm_eq_abs] using hE))

/-- Quantitative route blocker: if the original real-valued observable is
already at least `B` below a target `T`, then extended extraction cannot raise
it above `T` unless the error-term response exceeds `B`. -/
theorem extendedExtraction_le_target_of_le_target_sub_of_errorBound
    {α : Type*} [Zero α]
    {G F E : DimensionCoefficients α → ℝ}
    (hF : DeterminedByStandardExtraction (α := α) F)
    (hdecomp : ∀ coeff : DimensionCoefficients α, G coeff = F coeff + E coeff)
    {dmax : CanonicalDimension}
    (hd : 4 ≤ dmax) (coeff : DimensionCoefficients α)
    {T B : ℝ}
    (hG : G coeff ≤ T - B)
    (hE : |E (extendedExtraction dmax coeff) - E coeff| ≤ B) :
    G (extendedExtraction dmax coeff) ≤ T := by
  have hdiff :
      |G (extendedExtraction dmax coeff) - G coeff| ≤ B :=
    abs_difference_le_of_extendedExtraction_errorBound
      (α := α) hF hdecomp hd coeff hE
  have hupper : G (extendedExtraction dmax coeff) - G coeff ≤ B :=
    (abs_le.mp hdiff).2
  linarith

/-- Strict version of
`extendedExtraction_le_target_of_le_target_sub_of_errorBound`.  If the original
observable misses the target by a strict margin at least `B`, then extended
extraction still leaves it strictly below the target under the same error
bound. -/
theorem extendedExtraction_lt_target_of_lt_target_sub_of_errorBound
    {α : Type*} [Zero α]
    {G F E : DimensionCoefficients α → ℝ}
    (hF : DeterminedByStandardExtraction (α := α) F)
    (hdecomp : ∀ coeff : DimensionCoefficients α, G coeff = F coeff + E coeff)
    {dmax : CanonicalDimension}
    (hd : 4 ≤ dmax) (coeff : DimensionCoefficients α)
    {T B : ℝ}
    (hG : G coeff < T - B)
    (hE : |E (extendedExtraction dmax coeff) - E coeff| ≤ B) :
    G (extendedExtraction dmax coeff) < T := by
  have hdiff :
      |G (extendedExtraction dmax coeff) - G coeff| ≤ B :=
    abs_difference_le_of_extendedExtraction_errorBound
      (α := α) hF hdecomp hd coeff hE
  have hupper : G (extendedExtraction dmax coeff) - G coeff ≤ B :=
    (abs_le.mp hdiff).2
  linarith

/-- Residual norm form: any norm bound for the error-term contribution of the
extended-minus-standard residue is automatically the same bound for the full
observable. -/
theorem norm_difference_le_of_extendedExtraction_sub_standard_errorBound
    {α β : Type*} [AddGroup α] [NormedAddCommGroup β]
    {G F E : DimensionCoefficients α → β}
    (hF : DeterminedByStandardExtraction (α := α) F)
    (hdecomp : ∀ coeff : DimensionCoefficients α, G coeff = F coeff + E coeff)
    {dmax : CanonicalDimension}
    (hd : 4 ≤ dmax) (coeff : DimensionCoefficients α)
    {B : ℝ}
    (hE : ‖E (extendedExtraction dmax coeff - standardExtraction (α := α) coeff) - E 0‖ ≤ B) :
    ‖G (extendedExtraction dmax coeff - standardExtraction (α := α) coeff) - G 0‖ ≤ B := by
  rw [difference_from_zero_eq_errorDifference_of_extendedExtraction_sub_standard
    (α := α) (β := β) hF hdecomp hd coeff]
  exact hE

/-- Step-drift form: the change in a beta-like observable caused by switching
from standard coefficients to extended-extracted coefficients is exactly the
change in the error term between the two RG steps. -/
theorem stepDifference_eq_errorStepDifference_of_extendedExtraction
    {α β : Type*} [Zero α] [AddCommGroup β]
    {G F E : DimensionCoefficients α → β}
    (hF : DeterminedByStandardExtraction (α := α) F)
    (hdecomp : ∀ coeff : DimensionCoefficients α, G coeff = F coeff + E coeff)
    {dmax : CanonicalDimension}
    (hd : 4 ≤ dmax)
    (coeffNext coeffCur : DimensionCoefficients α) :
    (G (extendedExtraction dmax coeffNext) - G (extendedExtraction dmax coeffCur)) -
        (G coeffNext - G coeffCur) =
      (E (extendedExtraction dmax coeffNext) - E coeffNext) -
        (E (extendedExtraction dmax coeffCur) - E coeffCur) := by
  have hnext :=
    difference_eq_errorDifference_of_extendedExtraction
      (α := α) (β := β) hF hdecomp hd coeffNext
  have hcur :=
    difference_eq_errorDifference_of_extendedExtraction
      (α := α) (β := β) hF hdecomp hd coeffCur
  calc
    (G (extendedExtraction dmax coeffNext) - G (extendedExtraction dmax coeffCur)) -
        (G coeffNext - G coeffCur)
      = (G (extendedExtraction dmax coeffNext) - G coeffNext) -
          (G (extendedExtraction dmax coeffCur) - G coeffCur) := by
            abel
    _ = (E (extendedExtraction dmax coeffNext) - E coeffNext) -
          (E (extendedExtraction dmax coeffCur) - E coeffCur) := by
            rw [hnext, hcur]

/-- Norm form of the step-drift audit: if the error-term responses at the two
steps satisfy bounds `Bnext` and `Bcur`, then the full drift perturbation is
bounded by `Bnext + Bcur`. -/
theorem norm_stepDifference_le_of_extendedExtraction_errorBounds
    {α β : Type*} [Zero α] [NormedAddCommGroup β]
    {G F E : DimensionCoefficients α → β}
    (hF : DeterminedByStandardExtraction (α := α) F)
    (hdecomp : ∀ coeff : DimensionCoefficients α, G coeff = F coeff + E coeff)
    {dmax : CanonicalDimension}
    (hd : 4 ≤ dmax)
    (coeffNext coeffCur : DimensionCoefficients α)
    {Bnext Bcur : ℝ}
    (hEnext : ‖E (extendedExtraction dmax coeffNext) - E coeffNext‖ ≤ Bnext)
    (hEcur : ‖E (extendedExtraction dmax coeffCur) - E coeffCur‖ ≤ Bcur) :
    ‖(G (extendedExtraction dmax coeffNext) - G (extendedExtraction dmax coeffCur)) -
        (G coeffNext - G coeffCur)‖ ≤ Bnext + Bcur := by
  rw [stepDifference_eq_errorStepDifference_of_extendedExtraction
    (α := α) (β := β) hF hdecomp hd coeffNext coeffCur]
  calc
    ‖(E (extendedExtraction dmax coeffNext) - E coeffNext) -
        (E (extendedExtraction dmax coeffCur) - E coeffCur)‖
      ≤ ‖E (extendedExtraction dmax coeffNext) - E coeffNext‖ +
          ‖E (extendedExtraction dmax coeffCur) - E coeffCur‖ := by
            exact norm_sub_le _ _
    _ ≤ Bnext + Bcur := add_le_add hEnext hEcur

/-- Quantitative step-drift blocker: if the original real-valued drift already
lies at least `Bnext + Bcur` below a target `T`, then extended extraction
cannot raise that drift above `T` unless the combined error responses exceed
the same margin. -/
theorem stepDifference_le_target_of_le_target_sub_of_errorBounds
    {α : Type*} [Zero α]
    {G F E : DimensionCoefficients α → ℝ}
    (hF : DeterminedByStandardExtraction (α := α) F)
    (hdecomp : ∀ coeff : DimensionCoefficients α, G coeff = F coeff + E coeff)
    {dmax : CanonicalDimension}
    (hd : 4 ≤ dmax)
    (coeffNext coeffCur : DimensionCoefficients α)
    {T Bnext Bcur : ℝ}
    (hG : G coeffNext - G coeffCur ≤ T - (Bnext + Bcur))
    (hEnext : |E (extendedExtraction dmax coeffNext) - E coeffNext| ≤ Bnext)
    (hEcur : |E (extendedExtraction dmax coeffCur) - E coeffCur| ≤ Bcur) :
    G (extendedExtraction dmax coeffNext) - G (extendedExtraction dmax coeffCur) ≤ T := by
  have hdiff :
      |(G (extendedExtraction dmax coeffNext) - G (extendedExtraction dmax coeffCur)) -
          (G coeffNext - G coeffCur)| ≤ Bnext + Bcur := by
    simpa [Real.norm_eq_abs] using
      (norm_stepDifference_le_of_extendedExtraction_errorBounds
        (α := α) (β := ℝ) hF hdecomp hd coeffNext coeffCur
        (by simpa [Real.norm_eq_abs] using hEnext)
        (by simpa [Real.norm_eq_abs] using hEcur))
  have hupper :
      (G (extendedExtraction dmax coeffNext) - G (extendedExtraction dmax coeffCur)) -
          (G coeffNext - G coeffCur) ≤ Bnext + Bcur :=
    (abs_le.mp hdiff).2
  linarith

/-- Strict version of
`stepDifference_le_target_of_le_target_sub_of_errorBounds`.  A strict drift
failure with margin exceeding the combined error responses survives extended
extraction. -/
theorem stepDifference_lt_target_of_lt_target_sub_of_errorBounds
    {α : Type*} [Zero α]
    {G F E : DimensionCoefficients α → ℝ}
    (hF : DeterminedByStandardExtraction (α := α) F)
    (hdecomp : ∀ coeff : DimensionCoefficients α, G coeff = F coeff + E coeff)
    {dmax : CanonicalDimension}
    (hd : 4 ≤ dmax)
    (coeffNext coeffCur : DimensionCoefficients α)
    {T Bnext Bcur : ℝ}
    (hG : G coeffNext - G coeffCur < T - (Bnext + Bcur))
    (hEnext : |E (extendedExtraction dmax coeffNext) - E coeffNext| ≤ Bnext)
    (hEcur : |E (extendedExtraction dmax coeffCur) - E coeffCur| ≤ Bcur) :
    G (extendedExtraction dmax coeffNext) - G (extendedExtraction dmax coeffCur) < T := by
  have hdiff :
      |(G (extendedExtraction dmax coeffNext) - G (extendedExtraction dmax coeffCur)) -
          (G coeffNext - G coeffCur)| ≤ Bnext + Bcur := by
    simpa [Real.norm_eq_abs] using
      (norm_stepDifference_le_of_extendedExtraction_errorBounds
        (α := α) (β := ℝ) hF hdecomp hd coeffNext coeffCur
        (by simpa [Real.norm_eq_abs] using hEnext)
        (by simpa [Real.norm_eq_abs] using hEcur))
  have hupper :
      (G (extendedExtraction dmax coeffNext) - G (extendedExtraction dmax coeffCur)) -
          (G coeffNext - G coeffCur) ≤ Bnext + Bcur :=
    (abs_le.mp hdiff).2
  linarith

end YangMills
end QuantumTheory
end Mettapedia
