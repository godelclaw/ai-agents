import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoveryHeavyRegionCardinalityObstruction

/-!
# P vs NP route obstruction: surjective recovery packets cannot hide heavy proper
  regions

The earlier proper-region obstruction used the injective `zfeat` branch to
realize, inside the shared sparse-threshold family, a bad code that flips one
point outside a chosen finite region.

This file removes that extra realization burden whenever the *actual switched
family itself* is already surjective onto all Boolean rules on the exact visible
surface. In that case Lean can choose two realized predictors directly:

* a reference rule, and
* the same rule flipped at one visible point outside the region.

These two realized predictors agree on the whole region, so the recent
heavy-region rigidity theorem forces them to be equal globally whenever the
region mass exceeds `q`. That is impossible by construction.

Therefore every proper finite visible region already has mass at most `q` on any
surjective manuscript-facing sparse-threshold recovery packet, with no
injective-branch hypothesis on `zfeat` and no injectivity assumption on the
actual family index.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

universe u v w

namespace ActualSwitchedLocalInterface

section Abstract

variable {Z : Type v} [Fintype Z] {k r : ℕ} {Index : Type u} {Block : Type w}
variable {T : ActualSwitchedLocalInterface Z k Index Block}
variable {μ : PMF (ExactVisiblePostSwitchSurface Z k)} {zfeat : Z → BitVec r}
variable {q : ℝ≥0∞}

namespace SharedExactZABSparseThresholdERMRecoveryData

/-- If the actual switched family is already surjective onto all Boolean rules
on the exact visible surface, then any finite visible region with one point
outside it must already have total mass at most `q`. Otherwise the region would
hide two distinct realized predictors that agree on it. -/
theorem regionMass_le_of_surjective_predict_of_not_mem
    (h : SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    (region : Finset (ExactVisiblePostSwitchSurface Z k))
    {x₀ : ExactVisiblePostSwitchSurface Z k}
    (hx₀ : x₀ ∉ region) :
    region.sum (fun x => μ x) ≤ q := by
  classical
  by_contra hq
  have hmass : q < region.sum (fun x => μ x) := lt_of_not_ge hq
  let target : ExactVisiblePostSwitchSurface Z k → Bool := fun _ => false
  let altered : ExactVisiblePostSwitchSurface Z k → Bool :=
    fun x => if x = x₀ then true else false
  obtain ⟨i, hi⟩ := hsurj target
  obtain ⟨j, hj⟩ := hsurj altered
  have hagree :
      ∀ x, x ∈ region →
        T.predictorFamily.predict i x = T.predictorFamily.predict j x := by
    intro x hx
    have hxne : x ≠ x₀ := by
      intro hEq
      subst hEq
      exact hx₀ hx
    calc
      T.predictorFamily.predict i x = target x := congrFun hi x
      _ = false := by simp [target]
      _ = altered x := by simp [altered, hxne]
      _ = T.predictorFamily.predict j x := (congrFun hj x).symm
  have hneq : T.predictorFamily.predict i ≠ T.predictorFamily.predict j := by
    intro hij
    have hi₀ : T.predictorFamily.predict i x₀ = false := by
      simpa [target] using congrFun hi x₀
    have hj₀ : T.predictorFamily.predict j x₀ = true := by
      simpa [altered] using congrFun hj x₀
    have hEq₀ : T.predictorFamily.predict i x₀ = T.predictorFamily.predict j x₀ := by
      exact congrFun hij x₀
    rw [hi₀, hj₀] at hEq₀
    simp at hEq₀
  exact
    hneq <|
      h.predict_eq_of_agrees_on_region_of_lt_regionMass
        (region := region)
        hmass
        hagree

/-- Existential form: the same surjective obstruction applies to any proper
finite visible region. -/
theorem regionMass_le_of_surjective_predict_of_exists_not_mem
    (h : SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    (region : Finset (ExactVisiblePostSwitchSurface Z k))
    (hout : ∃ x₀ : ExactVisiblePostSwitchSurface Z k, x₀ ∉ region) :
    region.sum (fun x => μ x) ≤ q := by
  rcases hout with ⟨x₀, hx₀⟩
  exact h.regionMass_le_of_surjective_predict_of_not_mem hsurj region hx₀

end SharedExactZABSparseThresholdERMRecoveryData

/-- Contrapositive form: a surjective actual switched family cannot support the
manuscript-facing sparse-threshold recovery packet if one finite visible region
has a point outside it and mass above `q`. -/
theorem not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_surjective_predict_of_not_mem_of_lt_regionMass
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (zfeat : Z → BitVec r)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    (region : Finset (ExactVisiblePostSwitchSurface Z k))
    {x₀ : ExactVisiblePostSwitchSurface Z k}
    (hx₀ : x₀ ∉ region)
    (hmass : q < region.sum (fun x => μ x)) :
    ¬ Nonempty (SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q) := by
  rintro ⟨h⟩
  exact not_le_of_gt hmass <|
    h.regionMass_le_of_surjective_predict_of_not_mem hsurj region hx₀

/-- The same surjective-region obstruction already removes the extractor
choice: once some proper visible region has mass above `q`, no extractor at all
can support the manuscript-facing recovery packet on that surjective actual
switched family. -/
theorem not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_surjective_predict_of_not_mem_of_lt_regionMass
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    (region : Finset (ExactVisiblePostSwitchSurface Z k))
    {x₀ : ExactVisiblePostSwitchSurface Z k}
    (hx₀ : x₀ ∉ region)
    (hmass : q < region.sum (fun x => μ x)) :
    ¬ ∃ zfeat : Z → BitVec r,
        Nonempty (SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q) := by
  rintro ⟨zfeat, hdata⟩
  exact
    not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_surjective_predict_of_not_mem_of_lt_regionMass
      (μ := μ)
      (T := T)
      (zfeat := zfeat)
      hsurj
      region
      hx₀
      hmass
      hdata

/-- Proper-region form of the same contradiction. -/
theorem not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_surjective_predict_of_exists_not_mem_of_lt_regionMass
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (zfeat : Z → BitVec r)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    (region : Finset (ExactVisiblePostSwitchSurface Z k))
    (hout : ∃ x₀ : ExactVisiblePostSwitchSurface Z k, x₀ ∉ region)
    (hmass : q < region.sum (fun x => μ x)) :
    ¬ Nonempty (SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q) := by
  rintro ⟨h⟩
  exact not_le_of_gt hmass <|
    h.regionMass_le_of_surjective_predict_of_exists_not_mem hsurj region hout

/-- Proper-region existential form: the same obstruction rules out every
extractor at once whenever some proper visible region has mass above `q`. -/
theorem not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_surjective_predict_of_exists_not_mem_of_lt_regionMass
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    (region : Finset (ExactVisiblePostSwitchSurface Z k))
    (hout : ∃ x₀ : ExactVisiblePostSwitchSurface Z k, x₀ ∉ region)
    (hmass : q < region.sum (fun x => μ x)) :
    ¬ ∃ zfeat : Z → BitVec r,
        Nonempty (SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q) := by
  rintro ⟨zfeat, hdata⟩
  exact
    not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_surjective_predict_of_exists_not_mem_of_lt_regionMass
      (μ := μ)
      (T := T)
      (zfeat := zfeat)
      hsurj
      region
      hout
      hmass
      hdata

end Abstract

end ActualSwitchedLocalInterface

end Mettapedia.Computability.PNP
