import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoveryInjectiveConcentrationObstruction
import Mettapedia.Computability.PNP.FinitePMFHeavyRegionCharacterization

/-!
# P vs NP route characterization: heavy proper regions are exactly heavy
  point-complements

`ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoveryRegionObstruction`
showed that on the injective branch, any proper finite region of exact-visible
mass above `q` blocks the manuscript-facing sparse-threshold recovery packet.

This file identifies the intrinsic content of that obstruction.  For a finite
PMF, there exists a proper finite region of mass `> q` if and only if some
single visible point already has complement mass `> q`, i.e.

* `q < 1 - μ y`.

So the injective recovery blocker does not require searching over arbitrary
finite regions: the route is obstructed exactly when one point is too light.
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

/-- On the finite exact-visible surface, having some proper region of mass
above `q` is equivalent to having some point whose complement already has mass
above `q`. -/
theorem exists_heavyProperRegion_iff_exists_lt_one_sub_apply :
    (∃ region : Finset (ExactVisiblePostSwitchSurface Z k),
        (∃ x₀ : ExactVisiblePostSwitchSurface Z k, x₀ ∉ region) ∧
          q < region.sum (fun x => μ x)) ↔
      ∃ y : ExactVisiblePostSwitchSurface Z k, q < 1 - μ y := by
  classical
  simpa using
    (PMF.exists_heavyProperRegion_iff_exists_lt_one_sub_apply (μ := μ) (q := q))

/-- On the finite exact-visible surface, the same obstruction is already
equivalent to a single sharp threshold determined by the lightest visible
point. -/
theorem exists_heavyProperRegion_iff_lt_one_sub_apply_lightestPoint
    [Nonempty (ExactVisiblePostSwitchSurface Z k)] :
    (∃ region : Finset (ExactVisiblePostSwitchSurface Z k),
        (∃ x₀ : ExactVisiblePostSwitchSurface Z k, x₀ ∉ region) ∧
          q < region.sum (fun x => μ x)) ↔
      q < 1 - μ (PMF.lightestPoint μ) := by
  classical
  simpa using
    (PMF.exists_heavyProperRegion_iff_lt_one_sub_apply_lightestPoint (μ := μ) (q := q))

/-- The whole family of proper-region mass bounds collapses to the single
lightest-point threshold.  So the strongest proper-region obstruction is the
region omitting the lightest visible point. -/
theorem allProperRegionMass_le_iff_one_sub_apply_lightestPoint_le
    [Nonempty (ExactVisiblePostSwitchSurface Z k)] :
    (∀ region : Finset (ExactVisiblePostSwitchSurface Z k),
        (∃ x₀ : ExactVisiblePostSwitchSurface Z k, x₀ ∉ region) →
          region.sum (fun x => μ x) ≤ q) ↔
      1 - μ (PMF.lightestPoint μ) ≤ q := by
  classical
  simpa using
    (PMF.allProperRegionMass_le_iff_one_sub_apply_lightestPoint_le
      (μ := μ) (q := q))

/-- Therefore, on the injective branch, a single visible point with complement
mass above `q` already blocks the manuscript-facing sparse-threshold recovery
packet. -/
theorem not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_injective_zfeat_of_lt_one_sub_apply
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (zfeat : Z → BitVec r)
    (hinj : Function.Injective zfeat)
    (hwidth : 0 < r + (k + k))
    (i : Index)
    {y : ExactVisiblePostSwitchSurface Z k}
    (hq_lt : q < 1 - μ y) :
    ¬ Nonempty (SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q) := by
  rintro ⟨h⟩
  exact
    not_lt_of_ge
      (h.one_sub_apply_le_of_injective_zfeat hinj hwidth i y)
      hq_lt

/-- Therefore every injective manuscript-facing recovery packet already forces
`q` above the complement mass of the lightest visible point. -/
theorem one_sub_apply_lightestPoint_le_of_injective_zfeat
    [Nonempty (ExactVisiblePostSwitchSurface Z k)]
    (h : SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q)
    (hinj : Function.Injective zfeat)
    (hwidth : 0 < r + (k + k))
    (i : Index) :
    1 - μ (PMF.lightestPoint μ) ≤ q :=
  h.one_sub_apply_le_of_injective_zfeat hinj hwidth i (PMF.lightestPoint μ)

/-- Therefore an injective recovery packet already enforces the entire proper-
region mass family exactly up to the lightest-point threshold. -/
theorem allProperRegionMass_le_of_injective_zfeat
    [Nonempty (ExactVisiblePostSwitchSurface Z k)]
    (h : SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q)
    (hinj : Function.Injective zfeat)
    (hwidth : 0 < r + (k + k))
    (i : Index) :
    ∀ region : Finset (ExactVisiblePostSwitchSurface Z k),
      (∃ x₀ : ExactVisiblePostSwitchSurface Z k, x₀ ∉ region) →
        region.sum (fun x => μ x) ≤ q := by
  intro region hout
  exact
    ((allProperRegionMass_le_iff_one_sub_apply_lightestPoint_le
      (μ := μ) (q := q)).2 <|
        one_sub_apply_lightestPoint_le_of_injective_zfeat
          (μ := μ) (T := T) (zfeat := zfeat) h hinj hwidth i)
      region
      hout

/-- On the bounded-sample plug-in-majority endpoint, the empty sample already
forces `q` above the lightest-point complement on the injective branch. -/
theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_one_sub_apply_lightestPoint_le_of_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_injective_zfeat
    [Nonempty (ExactVisiblePostSwitchSurface Z k)]
    {sampleBound : ℕ}
    (h :
      SharedExactZABSparseThresholdERMRecoveryData
        μ
        (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound)
        zfeat
        q)
    (hinj : Function.Injective zfeat)
    (hwidth : 0 < r + (k + k)) :
    1 - μ (PMF.lightestPoint μ) ≤ q := by
  exact
    one_sub_apply_lightestPoint_le_of_injective_zfeat
      (μ := μ)
      (T := boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound)
      (zfeat := zfeat)
      h
      hinj
      hwidth
      (⟨[], by simp⟩)

/-- Existential point-complement form of the same injective obstruction. -/
theorem not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_injective_zfeat_of_exists_lt_one_sub_apply
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (zfeat : Z → BitVec r)
    (hinj : Function.Injective zfeat)
    (hwidth : 0 < r + (k + k))
    (i : Index)
    (hlight :
      ∃ y : ExactVisiblePostSwitchSurface Z k, q < 1 - μ y) :
    ¬ Nonempty (SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q) := by
  rcases hlight with ⟨y, hy⟩
  exact
    not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_injective_zfeat_of_lt_one_sub_apply
      (μ := μ) T zfeat hinj hwidth i hy

/-- So on the injective branch, falling below the lightest-point threshold is
already impossible. -/
theorem not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_injective_zfeat_of_lt_one_sub_apply_lightestPoint
    [Nonempty (ExactVisiblePostSwitchSurface Z k)]
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (zfeat : Z → BitVec r)
    (hinj : Function.Injective zfeat)
    (hwidth : 0 < r + (k + k))
    (i : Index)
    (hq_lt : q < 1 - μ (PMF.lightestPoint μ)) :
    ¬ Nonempty (SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q) := by
  rintro ⟨h⟩
  exact
    not_lt_of_ge
      (one_sub_apply_lightestPoint_le_of_injective_zfeat
        (μ := μ) (T := T) (zfeat := zfeat) h hinj hwidth i)
      hq_lt

/-- Therefore bounded-sample plug-in-majority recovery is already impossible
below the lightest-point threshold on the injective branch; no surjectivity
assumption is needed because the empty sample supplies the challenged index. -/
theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_injective_zfeat_of_lt_one_sub_apply_lightestPoint
    [Nonempty (ExactVisiblePostSwitchSurface Z k)]
    {sampleBound : ℕ}
    (hinj : Function.Injective zfeat)
    (hwidth : 0 < r + (k + k))
    (hq_lt : q < 1 - μ (PMF.lightestPoint μ)) :
    ¬ Nonempty
        (SharedExactZABSparseThresholdERMRecoveryData
          μ
          (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound)
          zfeat
          q) := by
  exact
    not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_injective_zfeat_of_lt_one_sub_apply_lightestPoint
      (μ := μ)
      (T := boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound)
      (zfeat := zfeat)
      hinj
      hwidth
      (⟨[], by simp⟩)
      hq_lt

/-- So the earlier arbitrary-region injective obstruction can be reduced to the
canonical point-complement criterion. -/
theorem not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_injective_zfeat_of_exists_heavyProperRegion
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (zfeat : Z → BitVec r)
    (hinj : Function.Injective zfeat)
    (hwidth : 0 < r + (k + k))
    (i : Index)
    (hregion :
      ∃ region : Finset (ExactVisiblePostSwitchSurface Z k),
        (∃ x₀ : ExactVisiblePostSwitchSurface Z k, x₀ ∉ region) ∧
          q < region.sum (fun x => μ x)) :
    ¬ Nonempty (SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q) := by
  classical
  exact
    not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_injective_zfeat_of_exists_lt_one_sub_apply
      (μ := μ) T zfeat hinj hwidth i <|
        (exists_heavyProperRegion_iff_exists_lt_one_sub_apply
          (μ := μ) (q := q)).1 hregion

end Abstract

end ActualSwitchedLocalInterface

end Mettapedia.Computability.PNP
