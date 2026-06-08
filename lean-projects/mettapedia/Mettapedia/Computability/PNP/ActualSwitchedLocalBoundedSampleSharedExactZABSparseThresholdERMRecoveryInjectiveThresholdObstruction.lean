import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoveryInjectiveConcentrationObstruction
import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoveryThresholdWidthObstruction
import Mathlib.Tactic

/-!
# P vs NP route obstruction: injective bounded-sample recovery thresholds need
  no surjectivity hypothesis

The earlier bounded-sample recovery-threshold obstruction passed through the
surjective branch: it first assumed the sample bound was large enough to realize
every Boolean rule, then imported the surjective concentration/cardinality
floor.

The injective concentration obstruction removes that detour.  Every bounded-
sample plug-in-majority interface has a canonical predictor index, namely the
empty sample `[]`.  Once `zfeat` is injective, the shared exact sparse-threshold
class can already challenge that single predictor strongly enough to force

* `1 - 2^-(n + 2*k) ≤ q`

with no lower bound on `sampleBound`.

As before, any stricter threshold

* `q < 1 - 2^-p`

therefore implies

* `n + 2*k < p`.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

namespace ActualSwitchedLocalInterface

section BitVec

variable {n k r : ℕ}
variable {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
variable {q : ℝ≥0∞} {zfeat : BitVec n → BitVec r}

/-- On the injective branch, even a bounded-sample plug-in-majority endpoint
with arbitrarily small sample budget already forces the uniform-complement
threshold `q ≥ 1 - 2^-(n + 2*k)`. -/
theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_one_sub_pow_inv_le_of_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_injective_zfeat
    {sampleBound : ℕ}
    (h : SharedExactZABSparseThresholdERMRecoveryData
      μ
      (boundedSamplePluginMajorityActualSwitchedLocalInterface (BitVec n) k sampleBound)
      zfeat
      q)
    (hinj : Function.Injective zfeat)
    (hwidth : 0 < r + (k + k)) :
    1 - (2 ^ (n + 2 * k) : ℝ≥0∞)⁻¹ ≤ q := by
  exact
    one_sub_pow_inv_le_of_injective_zfeat
      (μ := μ)
      (T := boundedSamplePluginMajorityActualSwitchedLocalInterface (BitVec n) k sampleBound)
      (zfeat := zfeat)
      h
      hinj
      hwidth
      (⟨[], by simp⟩)

/-- Therefore a bounded-sample plug-in-majority recovery packet is impossible
below `1 - 2^-(n + 2*k)` on the injective branch, with no sample-size
surjectivity assumption. -/
theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_injective_zfeat_of_lt_one_sub_pow_inv
    {sampleBound : ℕ}
    (hinj : Function.Injective zfeat)
    (hwidth : 0 < r + (k + k))
    (hq_lt : q < 1 - (2 ^ (n + 2 * k) : ℝ≥0∞)⁻¹) :
    ¬ Nonempty
        (SharedExactZABSparseThresholdERMRecoveryData
          μ
          (boundedSamplePluginMajorityActualSwitchedLocalInterface (BitVec n) k sampleBound)
          zfeat
          q) := by
  exact
    not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_injective_zfeat_of_lt_one_sub_pow_inv
      (μ := μ)
      (T := boundedSamplePluginMajorityActualSwitchedLocalInterface (BitVec n) k sampleBound)
      (zfeat := zfeat)
      hinj
      hwidth
      (⟨[], by simp⟩)
      hq_lt

/-- Any bounded-sample injective recovery packet below `1 - 2^-p` forces the
exact visible width to satisfy `n + 2*k < p`, even when the sample budget is
too small for surjectivity. -/
theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_visibleWidth_lt_of_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_injective_zfeat_of_lt_one_sub_pow_inv
    {sampleBound p : ℕ}
    (h : SharedExactZABSparseThresholdERMRecoveryData
      μ
      (boundedSamplePluginMajorityActualSwitchedLocalInterface (BitVec n) k sampleBound)
      zfeat
      q)
    (hinj : Function.Injective zfeat)
    (hwidth : 0 < r + (k + k))
    (hq_lt : q < 1 - (2 ^ p : ℝ≥0∞)⁻¹) :
    n + 2 * k < p := by
  by_contra hnot
  have hle : p ≤ n + 2 * k := Nat.not_lt.mp hnot
  have hbound : 1 - (2 ^ p : ℝ≥0∞)⁻¹ ≤ q := by
    exact le_trans
      (one_sub_pow_inv_monotone hle)
      (boundedSamplePluginMajorityActualSwitchedLocalInterface_one_sub_pow_inv_le_of_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_injective_zfeat
        (μ := μ)
        (k := k)
        (sampleBound := sampleBound)
        (zfeat := zfeat)
        h
        hinj
        hwidth)
  exact not_lt_of_ge hbound hq_lt

/-- Therefore the bounded-sample injective recovery route is impossible below
`1 - 2^-p` whenever `p ≤ n + 2*k`, again without any sample-size surjectivity
assumption. -/
theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_injective_zfeat_of_lt_one_sub_pow_inv_of_le_visibleWidth
    {sampleBound p : ℕ}
    (hinj : Function.Injective zfeat)
    (hwidth : 0 < r + (k + k))
    (hvisible : p ≤ n + 2 * k)
    (hq_lt : q < 1 - (2 ^ p : ℝ≥0∞)⁻¹) :
    ¬ Nonempty
        (SharedExactZABSparseThresholdERMRecoveryData
          μ
          (boundedSamplePluginMajorityActualSwitchedLocalInterface (BitVec n) k sampleBound)
          zfeat
          q) := by
  rintro ⟨h⟩
  exact Nat.not_lt_of_ge hvisible <|
    boundedSamplePluginMajorityActualSwitchedLocalInterface_visibleWidth_lt_of_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_injective_zfeat_of_lt_one_sub_pow_inv
      (μ := μ)
      (k := k)
      (sampleBound := sampleBound)
      (zfeat := zfeat)
      (p := p)
      h
      hinj
      hwidth
      hq_lt

end BitVec

end ActualSwitchedLocalInterface

end Mettapedia.Computability.PNP
