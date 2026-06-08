import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleMajorityObstruction
import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMSampleLowerBound

/-!
# P vs NP route bridge: bounded-sample actual locality forces a large
  sparse-threshold sample-bound packet

`ActualSwitchedLocalSharedExactZABSparseThresholdERMSampleLowerBound` extracted
the counting-gap burden for any surjective actual switched-local sparse-threshold
ERM packet.  `ActualSwitchedLocalBoundedSampleMajorityObstruction` separately
showed that bounded sample-level plug-in majority is surjective exactly when the
sample bound reaches the exact-visible alphabet size.

This file composes those facts at the manuscript-facing actual-local endpoint.
If the bounded-sample plug-in-majority interface is still full-rule expressive
and is identified with one shared exact sparse-threshold ERM family, then the
same point-block counting-gap packet forces the bounded sample budget itself to
exceed `2^(2*(n + 2k) + 1)` on `BitVec n`.

This is still conditional route-diagnostic work, not a full closure theorem for
the surviving injective sparse-threshold branch.
-/

namespace Mettapedia.Computability.PNP

namespace ActualSwitchedLocalInterface

section BitVec

variable {n k r sampleBound : ℕ}

/-- If bounded sample-level plug-in majority on `BitVec n` is full-rule
expressive and simultaneously one shared exact sparse-threshold ERM family, then
the current point-block counting-gap packet already forces the bounded sample
budget itself to exceed `2^(2*(n + 2k) + 1)`. -/
theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_visibleWidthBudget_lt_sampleBound_of_nonempty_sharedExactZABSparseThresholdERMData
    {zfeat : BitVec n → BitVec r}
    (hdata :
      Nonempty
        (SharedExactZABSparseThresholdERMData
          (boundedSamplePluginMajorityActualSwitchedLocalInterface
            (BitVec n) k sampleBound)
          zfeat))
    (hsample :
      Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k) ≤ sampleBound)
    (hvis : 0 < n + (k + k))
    (hbound :
      2 ^ (2 * allAffinePointBlockFeatureCount (r + (k + k))) *
          (Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k) - 1) ^ sampleBound <
        Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k) ^ sampleBound) :
    2 ^ (2 * (n + (k + k)) + 1) < sampleBound := by
  exact
    visibleWidthBudget_lt_sampleSize_of_nonempty_sharedExactZABSparseThresholdERMData_of_surjective_predict
      (n := n) (r := r) (k := k) (m := sampleBound)
      (T := boundedSamplePluginMajorityActualSwitchedLocalInterface
        (BitVec n) k sampleBound)
      (zfeat := zfeat)
      hdata
      (boundedSamplePluginMajorityActualSwitchedLocalInterface_surjective
        (BitVec n) k sampleBound hsample)
      hvis
      hbound

/-- On the injective-width branch, once bounded sample-level plug-in majority
is large enough to be full-rule expressive, the same counting-gap packet forces
the bounded sample budget above the visible-width threshold without assuming a
pre-existing manuscript-facing sparse-threshold ERM witness. -/
theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_visibleWidthBudget_lt_sampleBound_of_visibleSurfaceCard_le_of_width_le
    (hnr : n ≤ r)
    (hsample :
      Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k) ≤ sampleBound)
    (hvis : 0 < n + (k + k))
    (hwidth : 0 < r + (k + k))
    (hbound :
      2 ^ (2 * allAffinePointBlockFeatureCount (r + (k + k))) *
          (Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k) - 1) ^ sampleBound <
        Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k) ^ sampleBound) :
    2 ^ (2 * (n + (k + k)) + 1) < sampleBound := by
  let zfeat : BitVec n → BitVec r := bitVecPrefixEmbedding (n := n) (r := r)
  have hdata :
      Nonempty
        (SharedExactZABSparseThresholdERMData
          (boundedSamplePluginMajorityActualSwitchedLocalInterface
            (BitVec n) k sampleBound)
          zfeat) := by
    exact
      nonempty_sharedExactZABSparseThresholdERMData_of_injective_zfeat
        (T := boundedSamplePluginMajorityActualSwitchedLocalInterface
          (BitVec n) k sampleBound)
        zfeat
        (injective_bitVecPrefixEmbedding (n := n) (r := r) hnr)
        hwidth
        hbound
  exact
    boundedSamplePluginMajorityActualSwitchedLocalInterface_visibleWidthBudget_lt_sampleBound_of_nonempty_sharedExactZABSparseThresholdERMData
      (n := n) (r := r) (k := k) (sampleBound := sampleBound)
      (zfeat := zfeat)
      hdata hsample hvis hbound

/-- Therefore the bounded-sample plug-in-majority actual-local endpoint cannot
carry shared exact sparse-threshold ERM data at or below the visible-width
budget, provided the same point-block counting-gap packet is demanded at that
sample bound. -/
theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMData_of_sampleBound_le_visibleWidthBudget
    {zfeat : BitVec n → BitVec r}
    (hsample :
      Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k) ≤ sampleBound)
    (hvis : 0 < n + (k + k))
    (hbound :
      2 ^ (2 * allAffinePointBlockFeatureCount (r + (k + k))) *
          (Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k) - 1) ^ sampleBound <
        Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k) ^ sampleBound)
    (hsmall : sampleBound ≤ 2 ^ (2 * (n + (k + k)) + 1)) :
    ¬ Nonempty
        (SharedExactZABSparseThresholdERMData
          (boundedSamplePluginMajorityActualSwitchedLocalInterface
            (BitVec n) k sampleBound)
          zfeat) := by
  intro hdata
  have hlt :
      2 ^ (2 * (n + (k + k)) + 1) < sampleBound :=
    boundedSamplePluginMajorityActualSwitchedLocalInterface_visibleWidthBudget_lt_sampleBound_of_nonempty_sharedExactZABSparseThresholdERMData
      (n := n) (r := r) (k := k) (sampleBound := sampleBound)
      (zfeat := zfeat)
      hdata hsample hvis hbound
  exact Nat.not_lt_of_ge hsmall hlt

end BitVec

end ActualSwitchedLocalInterface

end Mettapedia.Computability.PNP
