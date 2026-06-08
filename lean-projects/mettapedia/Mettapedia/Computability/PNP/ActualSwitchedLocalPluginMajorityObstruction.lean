import Mettapedia.Computability.PNP.ActualSwitchedLocalPluginLookupObstruction

/-!
# PNP grassroots: plug-in majority still permits full local rules

`ActualSwitchedLocalPluginLookupObstruction` records the literal hash-table
endpoint.  This file strengthens the obstruction to the manuscript's plug-in
majority phrasing.  A plug-in majority rule is determined, on each visible
post-switch input `u = (z, a, b)`, by the number of training labels voting
`true` and `false`.  If no further ZAB/code restriction is imposed, those vote
counts can realize any Boolean lookup table by placing one vote on the desired
side for every visible input.

Thus the blocker is not an artifact of replacing ERM by an arbitrary lookup
table: the counted majority endpoint itself is already fully expressive.
-/

namespace Mettapedia.Computability.PNP

universe v

/-- The per-visible-input vote counts used by a plug-in majority rule on a
finite alphabet.  The fields are the aggregated counts after grouping the
training sample by the visible input `u`. -/
structure PluginMajorityCounts (U : Type v) where
  trueVotes : U → ℕ
  falseVotes : U → ℕ

namespace PluginMajorityCounts

variable {U : Type v}

/-- The plug-in majority prediction induced by the aggregated vote counts.
Ties are broken toward `true`; the full-expressivity theorem below uses no
ties. -/
def predict (C : PluginMajorityCounts U) (u : U) : Bool :=
  decide (C.falseVotes u ≤ C.trueVotes u)

/-- Vote counts realizing a prescribed Boolean rule: one vote on the rule's
side for every visible input. -/
def ofRule (rule : U → Bool) : PluginMajorityCounts U where
  trueVotes := fun u => if rule u then 1 else 0
  falseVotes := fun u => if rule u then 0 else 1

@[simp] theorem predict_ofRule (rule : U → Bool) (u : U) :
    (PluginMajorityCounts.ofRule rule).predict u = rule u := by
  cases h : rule u <;> simp [PluginMajorityCounts.ofRule, predict, h]

end PluginMajorityCounts

/-- The actual switched-local interface induced by unrestricted plug-in
majority vote counts on the exact visible post-switch alphabet. -/
def pluginMajorityActualSwitchedLocalInterface (Z : Type v) (k : ℕ) :
    ActualSwitchedLocalInterface
      Z k
      (PluginMajorityCounts (ExactVisiblePostSwitchSurface Z k))
      (ExactVisiblePostSwitchSurface Z k) where
  zOf := fun u => u.z
  aOf := fun _ u => u.a
  bOf := fun u => u.b
  localRule := fun counts u => counts.predict u
  output := fun counts u => counts.predict u
  output_eq_local := by
    intro counts u
    rfl

/-- Every Boolean lookup table on the post-switch alphabet occurs as a plug-in
majority rule, using one vote on the desired side at each input. -/
theorem pluginMajorityActualSwitchedLocalInterface_realizes_every_lookupTable
    {Z : Type v} {k : ℕ} (rule : ExactVisibleRule Z k) :
    ∃ counts,
      (pluginMajorityActualSwitchedLocalInterface Z k).predictorFamily.predict
          counts =
        rule := by
  refine ⟨PluginMajorityCounts.ofRule rule, ?_⟩
  funext u
  simp [pluginMajorityActualSwitchedLocalInterface,
    ActualSwitchedLocalInterface.predictorFamily]

/-- The counted plug-in majority endpoint is surjective onto all Boolean rules
on the exact visible post-switch alphabet. -/
theorem pluginMajorityActualSwitchedLocalInterface_surjective
    (Z : Type v) (k : ℕ) :
    Function.Surjective
      (pluginMajorityActualSwitchedLocalInterface Z k).predictorFamily.predict := by
  intro rule
  exact pluginMajorityActualSwitchedLocalInterface_realizes_every_lookupTable rule

/-- Counted plug-in majority has no small finite predictor cover below the
exact visible truth-table budget. -/
theorem pluginMajorityActualSwitchedLocalInterface_not_finitePredictorCover_of_lt_surfaceCard
    {Z : Type v} {k s : ℕ} [Fintype Z]
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (pluginMajorityActualSwitchedLocalInterface Z k).predictorFamily.FinitePredictorCover
        (2 ^ s) := by
  intro hcover
  have hsmall :
      ExactVisibleCompressionTarget
        (Z := Z) (k := k)
        (Index := PluginMajorityCounts (ExactVisiblePostSwitchSurface Z k))
        (pluginMajorityActualSwitchedLocalInterface Z k).predictorFamily s :=
    (exactVisibleCompressionTarget_iff_finitePredictorCover
      (Z := Z) (k := k) (s := s)
      (Index := PluginMajorityCounts (ExactVisiblePostSwitchSurface Z k))
      (G := (pluginMajorityActualSwitchedLocalInterface Z k).predictorFamily)).2
      hcover
  exact
    (not_exactVisibleCompressionTarget_of_surjective_predict
      (Z := Z) (k := k) (s := s)
      (Index := PluginMajorityCounts (ExactVisiblePostSwitchSurface Z k))
      (G := (pluginMajorityActualSwitchedLocalInterface Z k).predictorFamily)
      hs (pluginMajorityActualSwitchedLocalInterface_surjective Z k)) hsmall

/-- Counted plug-in majority does not provide the clocked finite-learning
payload below the exact visible truth-table budget. -/
theorem pluginMajorityActualSwitchedLocalInterface_not_clockedKpolyFiniteLearningPayload_of_lt_surfaceCard
    {Z : Type v} {k s clock : ℕ} [Fintype Z]
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ClockedKpolyFiniteLearningPayload
        (pluginMajorityActualSwitchedLocalInterface Z k).predictorFamily s clock := by
  intro hpayload
  have hsmall :
      ExactVisibleCompressionTarget
        (Z := Z) (k := k)
        (Index := PluginMajorityCounts (ExactVisiblePostSwitchSurface Z k))
        (pluginMajorityActualSwitchedLocalInterface Z k).predictorFamily s :=
    exactVisibleCompressionTarget_of_clockedKpolyFiniteLearningPayload
      (Z := Z) (k := k) (s := s) (clock := clock)
      (Index := PluginMajorityCounts (ExactVisiblePostSwitchSurface Z k))
      hpayload
  exact
    (not_exactVisibleCompressionTarget_of_surjective_predict
      (Z := Z) (k := k) (s := s)
      (Index := PluginMajorityCounts (ExactVisiblePostSwitchSurface Z k))
      (G := (pluginMajorityActualSwitchedLocalInterface Z k).predictorFamily)
      hs (pluginMajorityActualSwitchedLocalInterface_surjective Z k)) hsmall

/-- Counted plug-in majority cannot supply the bounded-code minimal missing
assumption below the exact visible truth-table budget. -/
theorem pluginMajorityActualSwitchedLocalInterface_not_bitCodeData_of_lt_surfaceCard
    {Z : Type v} {k s : ℕ} [Fintype Z]
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.BitCodeData
          (pluginMajorityActualSwitchedLocalInterface Z k) s) := by
  rintro ⟨hcode⟩
  exact
    pluginMajorityActualSwitchedLocalInterface_not_finitePredictorCover_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) hs hcode.finitePredictorCover

/-- Counted plug-in majority also cannot supply the ZAB decision-list
constructor data below the exact visible truth-table budget. -/
theorem pluginMajorityActualSwitchedLocalInterface_not_zabDecisionListData_of_lt_surfaceCard
    {Z : Type v} {k r : ℕ} [Fintype Z]
    (zfeat : Z → BitVec r)
    (hs : r + 2 * k + 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.ZABDecisionListData
          (pluginMajorityActualSwitchedLocalInterface Z k) zfeat) := by
  rintro ⟨hzab⟩
  exact
    hzab.not_surjective_predict_of_lt_surfaceCard hs
      (pluginMajorityActualSwitchedLocalInterface_surjective Z k)

end Mettapedia.Computability.PNP
