import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoveryHeavyRegionCardinalityObstruction

/-!
# P vs NP route obstruction: the full-rule recovery endpoint cannot hide heavy
  proper regions

The earlier injective-branch region obstruction showed that if `zfeat` is
injective, then any proper visible region of mass above `q` kills the
manuscript-facing full-rule sparse-threshold recovery packet.

This file removes that extra branch assumption for the full-rule endpoint
itself. If a full-rule recovery packet existed and one finite visible region had
mass above `q`, then the recent heavy-region trace bound would force the full
Boolean rule family on the whole exact visible surface to inject into the
Boolean trace space on that region. That is impossible for a proper region,
because the full rule family has size `2^|surface|` while the region trace space
has size only `2^|region|`.

So on the full-rule endpoint, every proper finite visible region already has
mass at most `q`, with no injectivity or width hypothesis on `zfeat`.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

universe v

namespace ActualSwitchedLocalInterface

section FullRule

variable {Z : Type v} [Fintype Z] {k r : ℕ}
variable {μ : PMF (ExactVisiblePostSwitchSurface Z k)} {zfeat : Z → BitVec r}
variable {q : ℝ≥0∞}

namespace SharedExactZABSparseThresholdERMRecoveryData

/-- On the manuscript-facing full-rule endpoint, any finite visible region whose
cardinality is strictly below the full exact visible surface must already have
mass at most `q`. Otherwise the recent heavy-region trace bound would force the
full Boolean rule family on the whole surface to fit inside the smaller Boolean
trace space on that region. -/
theorem regionMass_le_of_lt_surfaceCard
    (h :
      SharedExactZABSparseThresholdERMRecoveryData
        μ
        (fullRuleActualSwitchedLocalInterface Z k)
        zfeat
        q)
    (region : Finset (ExactVisiblePostSwitchSurface Z k))
    (hcard : region.card < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    region.sum (fun x => μ x) ≤ q := by
  classical
  letI : Fintype (ExactVisibleRule Z k) := by
    dsimp [ExactVisibleRule]
    infer_instance
  by_contra hq
  have hmass : q < region.sum (fun x => μ x) := lt_of_not_ge hq
  have hinj :
      Function.Injective
        (fullRuleActualSwitchedLocalInterface Z k).predictorFamily.predict := by
    intro i j hij
    exact hij
  have hbound :
      Fintype.card (ExactVisibleRule Z k) ≤ 2 ^ region.card := by
    simpa [ExactVisibleRule, Fintype.card_fun, Fintype.card_bool] using
      h.card_le_two_pow_regionCard_of_injective_predict_of_lt_regionMass
        region hmass hinj
  have hlt :
      2 ^ region.card < Fintype.card (ExactVisibleRule Z k) := by
    simpa [ExactVisibleRule, Fintype.card_fun, Fintype.card_bool] using
      (Nat.pow_lt_pow_right Nat.one_lt_two hcard)
  exact (not_le_of_gt hlt) hbound

/-- Proper-region form of the same obstruction: on the full-rule endpoint, any
finite region with a visible point outside it already has mass at most `q`. -/
theorem regionMass_le_of_exists_not_mem
    (h :
      SharedExactZABSparseThresholdERMRecoveryData
        μ
        (fullRuleActualSwitchedLocalInterface Z k)
        zfeat
        q)
    (region : Finset (ExactVisiblePostSwitchSurface Z k))
    (hout : ∃ x₀ : ExactVisiblePostSwitchSurface Z k, x₀ ∉ region) :
    region.sum (fun x => μ x) ≤ q := by
  apply h.regionMass_le_of_lt_surfaceCard region
  rcases hout with ⟨x₀, hx₀⟩
  have hne : region ≠ (Finset.univ : Finset (ExactVisiblePostSwitchSurface Z k)) := by
    intro hEq
    exact hx₀ (by simp [hEq])
  have hssub : region ⊂ (Finset.univ : Finset (ExactVisiblePostSwitchSurface Z k)) :=
    Finset.ssubset_univ_iff.mpr hne
  simpa using Finset.card_lt_card hssub

end SharedExactZABSparseThresholdERMRecoveryData

/-- Contrapositive form: on the manuscript-facing full-rule endpoint, any
finite visible region of mass above `q` and smaller cardinality than the whole
exact visible surface already refutes sparse-threshold recovery. -/
theorem fullRuleActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_lt_regionCard_of_lt_regionMass
    (zfeat : Z → BitVec r)
    (region : Finset (ExactVisiblePostSwitchSurface Z k))
    (hcard : region.card < Fintype.card (ExactVisiblePostSwitchSurface Z k))
    (hmass : q < region.sum (fun x => μ x)) :
    ¬ Nonempty
        (SharedExactZABSparseThresholdERMRecoveryData
          μ
          (fullRuleActualSwitchedLocalInterface Z k)
          zfeat
          q) := by
  rintro ⟨h⟩
  exact not_le_of_gt hmass (h.regionMass_le_of_lt_surfaceCard region hcard)

/-- Proper-region corollary: the full-rule endpoint is impossible as soon as one
proper finite visible region carries mass above `q`. This closes the earlier
heavy-region loophole without any injective-branch assumption on `zfeat`. -/
theorem fullRuleActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_exists_not_mem_of_lt_regionMass
    (zfeat : Z → BitVec r)
    (region : Finset (ExactVisiblePostSwitchSurface Z k))
    (hout : ∃ x₀ : ExactVisiblePostSwitchSurface Z k, x₀ ∉ region)
    (hmass : q < region.sum (fun x => μ x)) :
    ¬ Nonempty
        (SharedExactZABSparseThresholdERMRecoveryData
          μ
          (fullRuleActualSwitchedLocalInterface Z k)
          zfeat
          q) := by
  rintro ⟨h⟩
  exact not_le_of_gt hmass (h.regionMass_le_of_exists_not_mem region hout)

end FullRule

end ActualSwitchedLocalInterface

end Mettapedia.Computability.PNP
