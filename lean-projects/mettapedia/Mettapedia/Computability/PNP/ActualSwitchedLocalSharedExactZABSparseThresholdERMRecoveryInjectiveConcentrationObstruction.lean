import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoveryRegionObstruction
import Mettapedia.Computability.PNP.BitVecZABCompressionObstruction
import Mettapedia.Computability.PNP.FinitePMFPointMassBound
import Mathlib.Data.ENNReal.Inv
import Mathlib.Tactic

/-!
# P vs NP route obstruction: injective recovery packets still force large `q`

The earlier recovery concentration/cardinality obstructions worked on the
surjective branch: if the actual switched-local predictor family can realize
every Boolean rule, then each point complement already has mass at most the
advertised bad-code agreement threshold `q`.

The injective-region obstruction is strong enough to recover the same
conclusion without any surjectivity assumption.  Once `zfeat` is injective,
the shared exact sparse-threshold family can flip one chosen target predictor
at one chosen visible point while leaving every other point unchanged.  Taking
the agreement region to be the complement of one visible point `y` yields

* `1 - μ y ≤ q`.

Combining that with the finite pigeonhole point-mass bound recovers the same
uniform-complement threshold

* `1 - |surface|⁻¹ ≤ q`

for every injective manuscript-facing recovery packet, even on non-surjective
actual-local interfaces.
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

/-- On the injective branch, the mass outside any chosen visible point `y`
already has to be at most `q`. -/
theorem one_sub_apply_le_of_injective_zfeat
    (h : SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q)
    (hinj : Function.Injective zfeat)
    (hwidth : 0 < r + (k + k))
    (i : Index)
    (y : ExactVisiblePostSwitchSurface Z k) :
    1 - μ y ≤ q := by
  classical
  have hregion :
      (Finset.univ.erase y).sum (fun u => μ u) ≤ q :=
    h.regionMass_le_of_injective_zfeat_of_not_mem
      (x₀ := y) hinj hwidth i (Finset.univ.erase y) (by simp)
  have hsum :
      (1 : ℝ≥0∞) =
        (Finset.univ.erase y).sum (fun u => μ u) + μ y := by
    simpa [pmf_sum_univ_eq_one μ, add_comm] using
      (Finset.sum_erase_add
        (s := (Finset.univ : Finset (ExactVisiblePostSwitchSurface Z k)))
        (a := y)
        (f := fun u : ExactVisiblePostSwitchSurface Z k => μ u)
        (Finset.mem_univ y)).symm
  simpa [ENNReal.sub_eq_of_eq_add (μ.apply_ne_top y) hsum] using hregion

/-- Therefore every injective manuscript-facing recovery packet already forces
`q` above the complement of the uniform point mass. -/
theorem one_sub_inv_card_le_of_injective_zfeat
    [Nonempty (ExactVisiblePostSwitchSurface Z k)]
    (h : SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q)
    (hinj : Function.Injective zfeat)
    (hwidth : 0 < r + (k + k))
    (i : Index) :
    1 - (Fintype.card (ExactVisiblePostSwitchSurface Z k) : ℝ≥0∞)⁻¹ ≤ q := by
  obtain ⟨y, hy⟩ := PMF.exists_apply_le_inv_card μ
  exact le_trans
    (tsub_le_tsub_left hy 1)
    (h.one_sub_apply_le_of_injective_zfeat hinj hwidth i y)

end SharedExactZABSparseThresholdERMRecoveryData

/-- No injective manuscript-facing recovery packet can exist below the
uniform-complement threshold `1 - |surface|⁻¹`. -/
theorem not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_injective_zfeat_of_lt_one_sub_inv_card
    [Nonempty (ExactVisiblePostSwitchSurface Z k)]
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (zfeat : Z → BitVec r)
    (hinj : Function.Injective zfeat)
    (hwidth : 0 < r + (k + k))
    (i : Index)
    (hq_lt :
      q < 1 - (Fintype.card (ExactVisiblePostSwitchSurface Z k) : ℝ≥0∞)⁻¹) :
    ¬ Nonempty (SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q) := by
  rintro ⟨h⟩
  exact not_lt_of_ge
    (h.one_sub_inv_card_le_of_injective_zfeat hinj hwidth i)
    hq_lt

end Abstract

section BitVec

variable {n k r : ℕ} {Index : Type u} {Block : Type w}
variable {T : ActualSwitchedLocalInterface (BitVec n) k Index Block}
variable {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
variable {zfeat : BitVec n → BitVec r} {q : ℝ≥0∞}

local instance exactVisiblePostSwitchSurfaceNonemptyBitVec :
    Nonempty (ExactVisiblePostSwitchSurface (BitVec n) k) :=
  ⟨⟨zeroVec, zeroVec, zeroVec⟩⟩

/-- On the `BitVec n` exact visible surface, every injective manuscript-facing
recovery packet already forces `q ≥ 1 - 2^-(n + 2*k)`. -/
theorem one_sub_pow_inv_le_of_injective_zfeat
    (h : SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q)
    (hinj : Function.Injective zfeat)
    (hwidth : 0 < r + (k + k))
    (i : Index) :
    1 - (2 ^ (n + 2 * k) : ℝ≥0∞)⁻¹ ≤ q := by
  simpa [card_exactVisiblePostSwitchSurface_bitVec] using
    (h.one_sub_inv_card_le_of_injective_zfeat hinj hwidth i)

/-- Therefore the injective `BitVec n` recovery route is impossible below the
same uniform-complement threshold. -/
theorem not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_injective_zfeat_of_lt_one_sub_pow_inv
    (T : ActualSwitchedLocalInterface (BitVec n) k Index Block)
    (zfeat : BitVec n → BitVec r)
    (hinj : Function.Injective zfeat)
    (hwidth : 0 < r + (k + k))
    (i : Index)
    (hq_lt : q < 1 - (2 ^ (n + 2 * k) : ℝ≥0∞)⁻¹) :
    ¬ Nonempty (SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q) := by
  rintro ⟨h⟩
  exact not_lt_of_ge
    (one_sub_pow_inv_le_of_injective_zfeat
      (μ := μ) (T := T) (zfeat := zfeat) h hinj hwidth i)
    hq_lt

end BitVec

end ActualSwitchedLocalInterface

end Mettapedia.Computability.PNP
