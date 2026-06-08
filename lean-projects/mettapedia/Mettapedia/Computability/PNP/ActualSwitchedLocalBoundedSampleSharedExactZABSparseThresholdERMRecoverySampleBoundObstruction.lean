import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleSharedExactZABSparseThresholdERMSampleBound
import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoveryData

/-!
# P vs NP route bridge: bounded-sample actual locality forces a large
  sparse-threshold recovery sample-bound packet

`ActualSwitchedLocalBoundedSampleSharedExactZABSparseThresholdERMSampleBound`
already proves the counting-gap lower bound for bounded-sample actual-local
shared exact sparse-threshold ERM data.

This file lifts that same burden directly to the manuscript-facing recovery
packet.  No new counting argument is needed: recovery data already contains the
underlying exact-family data, so once the bounded-sample endpoint is large
enough for surjectivity, the same point-block counting-gap packet still forces
the bounded sample budget to exceed `2^(2*(n + 2*k) + 1)` on `BitVec n`.

This is still conditional route-diagnostic work, not a closure theorem for the
surviving injective sparse-threshold branch.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

namespace ActualSwitchedLocalInterface

section BitVec

variable {n k r sampleBound : ℕ}
variable {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
variable {zfeat : BitVec n → BitVec r}
variable {q : ℝ≥0∞}

/-- The bounded-sample manuscript-facing recovery endpoint inherits the same
counting-gap sample-growth burden as the underlying exact-family packet. -/
theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_visibleWidthBudget_lt_sampleBound_of_nonempty_sharedExactZABSparseThresholdERMRecoveryData
    (h :
      Nonempty
        (SharedExactZABSparseThresholdERMRecoveryData
          μ
          (boundedSamplePluginMajorityActualSwitchedLocalInterface
            (BitVec n) k sampleBound)
          zfeat
          q))
    (hsample :
      Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k) ≤ sampleBound)
    (hvis : 0 < n + (k + k))
    (hbound :
      2 ^ (2 * allAffinePointBlockFeatureCount (r + (k + k))) *
          (Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k) - 1) ^ sampleBound <
        Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k) ^ sampleBound) :
    2 ^ (2 * (n + (k + k)) + 1) < sampleBound := by
  rcases h with ⟨h⟩
  exact
    boundedSamplePluginMajorityActualSwitchedLocalInterface_visibleWidthBudget_lt_sampleBound_of_nonempty_sharedExactZABSparseThresholdERMData
      (n := n) (r := r) (k := k) (sampleBound := sampleBound)
      (zfeat := zfeat)
      ⟨h.data⟩
      hsample
      hvis
      hbound

/-- Therefore the bounded-sample manuscript-facing recovery endpoint cannot
exist at or below the visible-width budget, provided the same point-block
counting-gap packet is demanded at that sample bound. -/
theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_sampleBound_le_visibleWidthBudget
    (hsample :
      Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k) ≤ sampleBound)
    (hvis : 0 < n + (k + k))
    (hbound :
      2 ^ (2 * allAffinePointBlockFeatureCount (r + (k + k))) *
          (Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k) - 1) ^ sampleBound <
        Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k) ^ sampleBound)
    (hsmall : sampleBound ≤ 2 ^ (2 * (n + (k + k)) + 1)) :
    ¬ Nonempty
        (SharedExactZABSparseThresholdERMRecoveryData
          μ
          (boundedSamplePluginMajorityActualSwitchedLocalInterface
            (BitVec n) k sampleBound)
          zfeat
          q) := by
  rintro ⟨h⟩
  have hlt :
      2 ^ (2 * (n + (k + k)) + 1) < sampleBound :=
    boundedSamplePluginMajorityActualSwitchedLocalInterface_visibleWidthBudget_lt_sampleBound_of_nonempty_sharedExactZABSparseThresholdERMRecoveryData
      (n := n) (r := r) (k := k) (sampleBound := sampleBound)
      (μ := μ) (zfeat := zfeat) (q := q)
      ⟨h⟩
      hsample
      hvis
      hbound
  exact Nat.not_lt_of_ge hsmall hlt

end BitVec

end ActualSwitchedLocalInterface

end Mettapedia.Computability.PNP
