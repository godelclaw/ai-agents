import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoveryPairwiseAgreementObstruction
import Mettapedia.Computability.PNP.FiniteIIDAgreement
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi

/-!
# P vs NP route obstruction: any heavy finite region bounds the realized family

The pairwise recovery obstruction says that distinct realized predictors in a
manuscript-facing sparse-threshold recovery packet must have agreement mass at
most `q`.

If one finite visible region already has total mass `> q`, then two distinct
realized predictors cannot agree on that whole region: otherwise their mutual
agreement mass would already exceed `q`.

So under a recovery packet, restriction to any such heavy region is separating.
An injectively indexed actual switched family must therefore inject into the
Boolean trace space on that region, yielding the cardinality bound

* `|Index| ≤ 2 ^ region.card`.

This is a genuine measure-side obstruction that does not rely on the bit-budget
or quotient-budget wrappers, and it is stronger than the single-heavy-point
collapse whenever no individual atom is heavier than `q` but some finite region
is.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

universe u v w

namespace ActualSwitchedLocalInterface

section Abstract

variable {Z : Type v} [Fintype Z] {k r : ℕ} {Index : Type u}
variable {Block : Type w}
variable {T : ActualSwitchedLocalInterface Z k Index Block}
variable {μ : PMF (ExactVisiblePostSwitchSurface Z k)} {zfeat : Z → BitVec r}
variable {q : ℝ≥0∞}

/-- On any finite region of mass `> q`, equality of realized predictors on that
region already forces global equality inside a manuscript-facing sparse-threshold
recovery packet. -/
theorem SharedExactZABSparseThresholdERMRecoveryData.predict_eq_of_agrees_on_region_of_lt_regionMass
    (h : SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q)
    {region : Finset (ExactVisiblePostSwitchSurface Z k)} {i j : Index}
    (hmass : q < region.sum (fun x => μ x))
    (hagree :
      ∀ x, x ∈ region →
        T.predictorFamily.predict i x = T.predictorFamily.predict j x) :
    T.predictorFamily.predict i = T.predictorFamily.predict j := by
  by_contra hneq
  have hbound :
      agreementMass μ (T.predictorFamily.predict i) (T.predictorFamily.predict j) ≤ q := by
    exact
      h.agreementMass_le_of_predict_ne
        (i := i) (j := j)
        (by
          intro hEq
          exact hneq hEq.symm)
  rcases
      exists_pos_mass_disagreement_in_region_of_agreementMass_le_of_lt_regionMass
        (μ := μ)
        (target := T.predictorFamily.predict i)
        (predict := T.predictorFamily.predict j)
        region
        hbound
        hmass
      with ⟨x, hx, _, hdisagree⟩
  exact hdisagree ((hagree x hx).symm)

/-- Therefore an injectively indexed actual switched family can support such a
recovery packet only if its region traces fit inside the Boolean trace space on
every finite region of mass `> q`. -/
theorem SharedExactZABSparseThresholdERMRecoveryData.injective_restrict_region_of_injective_predict_of_lt_regionMass
    (h : SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q)
    (region : Finset (ExactVisiblePostSwitchSurface Z k))
    (hmass : q < region.sum (fun x => μ x))
    (hinj : Function.Injective T.predictorFamily.predict) :
    Function.Injective
      (fun i : Index => fun x : ↥region => T.predictorFamily.predict i x.1) := by
  intro i j hij
  apply hinj
  exact
    h.predict_eq_of_agrees_on_region_of_lt_regionMass
      (region := region)
      hmass
      (by
        intro x hx
        exact congrFun hij ⟨x, hx⟩)

/-- Cardinality form: any injectively indexed actual switched family supporting
recovery has at most `2 ^ region.card` predictors once one finite region already
has mass `> q`. -/
theorem SharedExactZABSparseThresholdERMRecoveryData.card_le_two_pow_regionCard_of_injective_predict_of_lt_regionMass
    [Fintype Index]
    (h : SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q)
    (region : Finset (ExactVisiblePostSwitchSurface Z k))
    (hmass : q < region.sum (fun x => μ x))
    (hinj : Function.Injective T.predictorFamily.predict) :
    Fintype.card Index ≤ 2 ^ region.card := by
  classical
  letI : Fintype ↥region := Finset.fintypeCoeSort region
  letI : DecidableEq ↥region := Classical.decEq _
  have hrestrict :
      Function.Injective
        (fun i : Index => fun x : ↥region => T.predictorFamily.predict i x.1) :=
    h.injective_restrict_region_of_injective_predict_of_lt_regionMass
      region hmass hinj
  calc
    Fintype.card Index ≤ Fintype.card (↥region → Bool) := by
      simpa using
        Fintype.card_le_of_injective
          (fun i : Index => fun x : ↥region => T.predictorFamily.predict i x.1)
          hrestrict
    _ = Fintype.card Bool ^ Fintype.card ↥region := by
      rw [Fintype.card_fun]
    _ = 2 ^ region.card := by
      rw [Fintype.card_bool, Fintype.card_coe]

/-- Contrapositive form: if an injectively indexed actual switched family is
larger than the Boolean trace space on one finite region of mass `> q`, then
the manuscript-facing sparse-threshold recovery packet is impossible. -/
theorem not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_lt_regionCard_of_injective_predict_of_lt_regionMass
    [Fintype Index]
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (zfeat : Z → BitVec r)
    (region : Finset (ExactVisiblePostSwitchSurface Z k))
    (hinj : Function.Injective T.predictorFamily.predict)
    (hmass : q < region.sum (fun x => μ x))
    (hcard : 2 ^ region.card < Fintype.card Index) :
    ¬ Nonempty (SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q) := by
  rintro ⟨h⟩
  exact not_le_of_gt hcard <|
    h.card_le_two_pow_regionCard_of_injective_predict_of_lt_regionMass
      region hmass hinj

end Abstract

end ActualSwitchedLocalInterface

end Mettapedia.Computability.PNP
