import Mettapedia.Computability.PNP.ActualSwitchedLocalStructure

/-!
# PNP grassroots: plug-in lookup obstruction for the actual switched family

The v11/arXiv finite-alphabet paragraph says that the post-switch local rule is
implemented as a plug-in majority/hash-table lookup on the finite alphabet
`u = (z, a_i, b)`, with no hypothesis enumeration.  This file records the exact
Lean consequence of that endpoint: if the lookup table is not further restricted
to the ZAB decision-list/code family, then the endpoint still permits every
Boolean rule on the exact visible post-switch surface.

Thus the existing ERM and explicit-code constructors are sufficient closure
routes only after the manuscript proves that its local lookup tables are exactly
those constructors' ZAB rules.  A bare finite-alphabet lookup implementation does
not imply the small predictor-image theorem.
-/

namespace Mettapedia.Computability.PNP

universe v

/-- The manuscript plug-in endpoint, read literally as an unrestricted lookup
table on the exact post-switch alphabet `u = (z, a, b)`.  Indices are lookup
tables themselves, so this is the finite-alphabet rule class before any
additional ZAB decision-list/code restriction is imposed. -/
abbrev pluginLookupActualSwitchedLocalInterface (Z : Type v) (k : ℕ) :
    ActualSwitchedLocalInterface
      Z k (ExactVisibleRule Z k) (ExactVisiblePostSwitchSurface Z k) :=
  fullRuleActualSwitchedLocalInterface Z k

@[simp] theorem pluginLookupActualSwitchedLocalInterface_predictorFamily
    (Z : Type v) (k : ℕ) :
    (pluginLookupActualSwitchedLocalInterface Z k).predictorFamily =
      fullExactVisibleRuleFamily Z k := by
  rfl

/-- Every Boolean lookup table on the post-switch alphabet occurs as one of the
plug-in endpoint predictors. -/
theorem pluginLookupActualSwitchedLocalInterface_realizes_every_lookupTable
    {Z : Type v} {k : ℕ} (rule : ExactVisibleRule Z k) :
    ∃ i,
      (pluginLookupActualSwitchedLocalInterface Z k).predictorFamily.predict i =
        rule := by
  exact ⟨rule, rfl⟩

/-- The plug-in endpoint is therefore surjective onto all Boolean rules on the
exact visible post-switch alphabet. -/
theorem pluginLookupActualSwitchedLocalInterface_surjective
    (Z : Type v) (k : ℕ) :
    Function.Surjective
      (pluginLookupActualSwitchedLocalInterface Z k).predictorFamily.predict := by
  intro rule
  exact pluginLookupActualSwitchedLocalInterface_realizes_every_lookupTable rule

/-- A bare plug-in lookup endpoint has no small finite predictor cover below the
exact visible truth-table budget. -/
theorem pluginLookupActualSwitchedLocalInterface_not_finitePredictorCover_of_lt_surfaceCard
    {Z : Type v} {k s : ℕ} [Fintype Z]
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (pluginLookupActualSwitchedLocalInterface Z k).predictorFamily.FinitePredictorCover
        (2 ^ s) := by
  simpa [pluginLookupActualSwitchedLocalInterface] using
    fullRuleActualSwitchedLocalInterface_not_finitePredictorCover_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) hs

/-- A bare plug-in lookup endpoint does not provide the clocked finite-learning
payload below the exact visible truth-table budget. -/
theorem pluginLookupActualSwitchedLocalInterface_not_clockedKpolyFiniteLearningPayload_of_lt_surfaceCard
    {Z : Type v} {k s clock : ℕ} [Fintype Z]
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ClockedKpolyFiniteLearningPayload
        (pluginLookupActualSwitchedLocalInterface Z k).predictorFamily s clock := by
  simpa [pluginLookupActualSwitchedLocalInterface] using
    fullRuleActualSwitchedLocalInterface_not_clockedKpolyFiniteLearningPayload_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) (clock := clock) hs

/-- Consequently, a bare plug-in lookup endpoint cannot supply the bounded-code
minimal missing assumption below the exact visible truth-table budget. -/
theorem pluginLookupActualSwitchedLocalInterface_not_bitCodeData_of_lt_surfaceCard
    {Z : Type v} {k s : ℕ} [Fintype Z]
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.BitCodeData
          (pluginLookupActualSwitchedLocalInterface Z k) s) := by
  simpa [pluginLookupActualSwitchedLocalInterface] using
    fullRuleActualSwitchedLocalInterface_not_bitCodeData_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) hs

/-- Nor can a bare plug-in lookup endpoint supply the ZAB decision-list
constructor data at a budget smaller than the full exact visible truth-table
budget.  This is the formal obstruction to treating hash-table plug-in ERM as
the already-closed ZAB/code route without an additional identification theorem. -/
theorem pluginLookupActualSwitchedLocalInterface_not_zabDecisionListData_of_lt_surfaceCard
    {Z : Type v} {k r : ℕ} [Fintype Z]
    (zfeat : Z → BitVec r)
    (hs : r + 2 * k + 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.ZABDecisionListData
          (pluginLookupActualSwitchedLocalInterface Z k) zfeat) := by
  simpa [pluginLookupActualSwitchedLocalInterface] using
    fullRuleActualSwitchedLocalInterface_not_zabDecisionListData_of_lt_surfaceCard
      (Z := Z) (k := k) (r := r) zfeat hs

end Mettapedia.Computability.PNP
