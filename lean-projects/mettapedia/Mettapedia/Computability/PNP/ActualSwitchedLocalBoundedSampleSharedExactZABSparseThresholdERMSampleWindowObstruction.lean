import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleSharedExactZABSparseThresholdERMSampleBound
import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoveryData
import Mathlib.Tactic

/-!
# P vs NP route obstruction: bounded-sample sparse-threshold packets have a
  forbidden sample-size window

`ActualSwitchedLocalBoundedSampleSharedExactZABSparseThresholdERMSampleBound`
already proves a conditional lower bound on the bounded sample budget:
whenever the bounded-sample endpoint is large enough to be full-rule expressive
and the point-block counting-gap packet holds at that same sample bound, Lean
forces

* `sampleBound > 2^(2*(n + 2*k) + 1)`.

This file packages that consequence into a cleaner manuscript-facing gap
statement.  Under the same counting-gap hypothesis, any bounded-sample
actual-local shared exact sparse-threshold packet on `BitVec n` must fall into
one of two regimes:

* either `sampleBound < 2^(n + 2*k)`, so the endpoint is too small even to see
  the whole exact-visible alphabet;
* or `2^(2*(n + 2*k) + 1) < sampleBound`, so the sample bound already exceeds
  the point-block bit budget by an exponential margin.

Hence no such packet can live in the intermediate window

* `2^(n + 2*k) ≤ sampleBound ≤ 2^(2*(n + 2*k) + 1)`.

The same forbidden window automatically blocks the manuscript-facing recovery
packet, since recovery data already contains the exact-family data.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

namespace ActualSwitchedLocalInterface

section BitVec

variable {n k r sampleBound : ℕ}
variable {zfeat : BitVec n → BitVec r}
variable {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
variable {q : ℝ≥0∞}

/-- Under the current point-block counting-gap packet, any bounded-sample
actual-local shared exact sparse-threshold ERM packet on `BitVec n` either
stays below the exact-visible alphabet size or jumps above the full
visible-width budget. -/
theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_sampleBound_lt_visibleSurfaceCard_or_visibleWidthBudget_lt_sampleBound_of_nonempty_sharedExactZABSparseThresholdERMData
    (hdata :
      Nonempty
        (SharedExactZABSparseThresholdERMData
          (boundedSamplePluginMajorityActualSwitchedLocalInterface
            (BitVec n) k sampleBound)
          zfeat))
    (hvis : 0 < n + (k + k))
    (hbound :
      2 ^ (2 * allAffinePointBlockFeatureCount (r + (k + k))) *
          (Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k) - 1) ^ sampleBound <
        Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k) ^ sampleBound) :
    sampleBound < 2 ^ (n + 2 * k) ∨
      2 ^ (2 * (n + (k + k)) + 1) < sampleBound := by
  by_cases hsample :
      Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k) ≤ sampleBound
  · right
    exact
      boundedSamplePluginMajorityActualSwitchedLocalInterface_visibleWidthBudget_lt_sampleBound_of_nonempty_sharedExactZABSparseThresholdERMData
        (n := n)
        (r := r)
        (k := k)
        (sampleBound := sampleBound)
        (zfeat := zfeat)
        hdata
        hsample
        hvis
        hbound
  · left
    exact Nat.lt_of_not_ge <| by
      simpa [card_exactVisiblePostSwitchSurface_bitVec] using hsample

/-- Therefore no bounded-sample actual-local shared exact sparse-threshold ERM
packet can exist inside the forbidden sample-size window between the exact-
visible alphabet size and the point-block visible-width budget. -/
theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMData_of_visibleSurfaceCard_le_sampleBound_of_sampleBound_le_visibleWidthBudget
    (hlower : 2 ^ (n + 2 * k) ≤ sampleBound)
    (hvis : 0 < n + (k + k))
    (hbound :
      2 ^ (2 * allAffinePointBlockFeatureCount (r + (k + k))) *
          (Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k) - 1) ^ sampleBound <
        Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k) ^ sampleBound)
    (hupper : sampleBound ≤ 2 ^ (2 * (n + (k + k)) + 1)) :
    ¬ Nonempty
        (SharedExactZABSparseThresholdERMData
          (boundedSamplePluginMajorityActualSwitchedLocalInterface
            (BitVec n) k sampleBound)
          zfeat) := by
  rintro hdata
  rcases
      boundedSamplePluginMajorityActualSwitchedLocalInterface_sampleBound_lt_visibleSurfaceCard_or_visibleWidthBudget_lt_sampleBound_of_nonempty_sharedExactZABSparseThresholdERMData
        (n := n)
        (r := r)
        (k := k)
        (sampleBound := sampleBound)
        (zfeat := zfeat)
        hdata
        hvis
        hbound
    with hsmall | hlarge
  · exact Nat.not_lt_of_ge hlower hsmall
  · exact Nat.not_lt_of_ge hupper hlarge

/-- The same forbidden sample-size window also blocks the manuscript-facing
recovery packet, because recovery data already contains the exact-family ERM
data. -/
theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_visibleSurfaceCard_sampleWindow
    (hlower : 2 ^ (n + 2 * k) ≤ sampleBound)
    (hvis : 0 < n + (k + k))
    (hbound :
      2 ^ (2 * allAffinePointBlockFeatureCount (r + (k + k))) *
          (Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k) - 1) ^ sampleBound <
        Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k) ^ sampleBound)
    (hupper : sampleBound ≤ 2 ^ (2 * (n + (k + k)) + 1)) :
    ¬ Nonempty
        (SharedExactZABSparseThresholdERMRecoveryData
          μ
          (boundedSamplePluginMajorityActualSwitchedLocalInterface
            (BitVec n) k sampleBound)
          zfeat
          q) := by
  rintro ⟨h⟩
  exact
    boundedSamplePluginMajorityActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMData_of_visibleSurfaceCard_le_sampleBound_of_sampleBound_le_visibleWidthBudget
      (n := n)
      (r := r)
      (k := k)
      (sampleBound := sampleBound)
      (zfeat := zfeat)
      hlower
      hvis
      hbound
      hupper
      ⟨h.data⟩

end BitVec

end ActualSwitchedLocalInterface

end Mettapedia.Computability.PNP
