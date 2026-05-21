import Mettapedia.Computability.PNP.ClockedKpolyTargetInterface

/-!
# PNP clocked `Kpoly` bridge equivalence

This file closes a bookkeeping escape hatch in the clocked `Kpoly` interface.
At the current abstraction level, a clocked realization family is neither
weaker nor stronger than an exact bit-budget witness: it is exactly the same
finite family, with a clock parameter carried as external bookkeeping.

Consequently, the remaining manuscript burden cannot be discharged merely by
renaming an exact visible compression target as a clocked decoder.  One still
has to prove the strict-subclass / small-bit-budget theorem for the actual
post-switch predictor family.
-/

namespace Mettapedia.Computability.PNP

universe u v

namespace IndexedPredictorFamily

variable {Index : Type u} {Input : Type v} {s clock clock' : ℕ}
variable {G : IndexedPredictorFamily Index Input}

/-- The canonical clocked family constructed from an exact bit budget realizes
the whole indexed predictor family. -/
theorem realizedByClockedBitFamily_clockedBitCodeFamilyOfHasBitBudget
    (clock : ℕ) (hbudget : G.HasBitBudget s) :
    G.RealizedByClockedBitFamily
      (clockedBitCodeFamilyOfHasBitBudget (G := G) (s := s) clock hbudget) := by
  intro i
  exact clockedBitCodeFamilyOfHasBitBudget_realizes
    (G := G) (s := s) clock hbudget i

/-- A clocked realization family is exactly an exact `s`-bit budget witness.
The clock parameter adds no additional expressivity at this abstraction level. -/
theorem exists_clockedBitFamily_iff_hasBitBudget :
    (∃ F : ClockedBitCodeFamily Input s clock, G.RealizedByClockedBitFamily F) ↔
      G.HasBitBudget s := by
  constructor
  · rintro ⟨F, hreal⟩
    exact hasBitBudget_of_realizedByClockedBitFamily hreal
  · intro hbudget
    refine ⟨clockedBitCodeFamilyOfHasBitBudget (G := G) (s := s) clock hbudget, ?_⟩
    exact realizedByClockedBitFamily_clockedBitCodeFamilyOfHasBitBudget
      (G := G) (s := s) clock hbudget

/-- Changing the external clock bound does not change which indexed predictor
families can be realized by `s` program bits. -/
theorem exists_clockedBitFamily_iff_exists_clockedBitFamily_of_clock :
    (∃ F : ClockedBitCodeFamily Input s clock, G.RealizedByClockedBitFamily F) ↔
      ∃ F : ClockedBitCodeFamily Input s clock', G.RealizedByClockedBitFamily F := by
  rw [exists_clockedBitFamily_iff_hasBitBudget,
    exists_clockedBitFamily_iff_hasBitBudget]

/-- A failed exact bit-budget theorem is equivalently a failed clocked
realization theorem. -/
theorem not_exists_clockedBitFamily_iff_not_hasBitBudget :
    (¬ ∃ F : ClockedBitCodeFamily Input s clock, G.RealizedByClockedBitFamily F) ↔
      ¬ G.HasBitBudget s := by
  rw [exists_clockedBitFamily_iff_hasBitBudget]

end IndexedPredictorFamily

section ExactPostSwitch

variable {Z : Type*} {k s clock clock' : ℕ} {Index : Type u}
variable {G : ExactVisibleSwitchedFamily Z k Index}

/-- On the exact visible post-switch surface, clocked realization is exactly the
existing exact visible compression target. -/
theorem exists_clockedExactVisibleRealization_iff_exactVisibleCompressionTarget :
    (∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F) ↔
      ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s := by
  exact IndexedPredictorFamily.exists_clockedBitFamily_iff_hasBitBudget
    (G := G) (s := s) (clock := clock)

/-- The clock parameter is expressivity-irrelevant for exact visible switched
families. -/
theorem exists_clockedExactVisibleRealization_iff_of_clock :
    (∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F) ↔
      ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock',
        G.RealizedByClockedBitFamily F := by
  exact IndexedPredictorFamily.exists_clockedBitFamily_iff_exists_clockedBitFamily_of_clock
    (G := G) (s := s) (clock := clock) (clock' := clock')

/-- Failing to prove an exact visible compression target is the same as failing
to produce a clocked realization family with the same bit budget. -/
theorem not_exists_clockedExactVisibleRealization_iff_not_exactVisibleCompressionTarget :
    (¬ ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F) ↔
      ¬ ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s := by
  rw [exists_clockedExactVisibleRealization_iff_exactVisibleCompressionTarget]

/-- A clocked realization family is enough to recover the same exact visible
compression target used by the rest of the `Kpoly` ledger. -/
theorem exactVisibleCompressionTarget_of_exists_clockedExactVisibleRealization
    (hclocked :
      ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s :=
  (exists_clockedExactVisibleRealization_iff_exactVisibleCompressionTarget
    (G := G) (s := s) (clock := clock)).1 hclocked

/-- Conversely, an exact visible compression target canonically supplies a
clocked realization family for any chosen external clock. -/
theorem exists_clockedExactVisibleRealization_of_exactVisibleCompressionTarget
    (hsmall : ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s) :
    ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
      G.RealizedByClockedBitFamily F :=
  (exists_clockedExactVisibleRealization_iff_exactVisibleCompressionTarget
    (G := G) (s := s) (clock := clock)).2 hsmall

/-- The canonical clocked family supplied by an exact visible compression
target realizes every exact visible switched predictor. -/
theorem realizedByClockedExactVisibleFamily_of_exactVisibleCompressionTarget
    (hsmall : ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s) :
    G.RealizedByClockedBitFamily
      (IndexedPredictorFamily.clockedBitCodeFamilyOfHasBitBudget
        (G := G) (s := s) clock hsmall) :=
  IndexedPredictorFamily.realizedByClockedBitFamily_clockedBitCodeFamilyOfHasBitBudget
    (G := G) (s := s) clock hsmall

end ExactPostSwitch

end Mettapedia.Computability.PNP
