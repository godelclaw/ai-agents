import Mettapedia.Computability.PNP.ActualSwitchedLocalPluginMajorityObstruction

/-!
# PNP grassroots: sample-level plug-in majority still permits full local rules

`ActualSwitchedLocalPluginMajorityObstruction` shows that aggregated vote counts
can realize every Boolean lookup table on the manuscript-visible alphabet
`u = (z, a, b)`.  This file removes one remaining abstraction: the vote counts
are obtained from an actual finite labeled sample by the plug-in majority rule.

For any Boolean rule on the finite exact-visible surface, take the graph sample
with one labeled example `(u, rule u)` for every visible input `u`.  The plug-in
majority predictor then recovers `rule` at every input.  Hence an unrestricted
sample-selected plug-in majority family is still the full Boolean rule family.

The small-image route therefore needs more than "finite alphabet plus empirical
majority": it must prove that the samples/rules land in a bounded code class,
such as the existing exact ZAB ERM or code constructors.
-/

namespace Mettapedia.Computability.PNP

universe v

namespace PluginSampleMajority

variable {U : Type v}

/-- Number of `true` labels in the sample with visible input exactly `u`. -/
def trueVotes [DecidableEq U] (sample : Sample U Bool) (u : U) : ℕ :=
  sample.countP (fun ex : U × Bool => ex.1 = u ∧ ex.2 = true)

/-- Number of `false` labels in the sample with visible input exactly `u`. -/
def falseVotes [DecidableEq U] (sample : Sample U Bool) (u : U) : ℕ :=
  sample.countP (fun ex : U × Bool => ex.1 = u ∧ ex.2 = false)

/-- Aggregated plug-in majority counts obtained from a finite labeled sample. -/
def counts [DecidableEq U] (sample : Sample U Bool) : PluginMajorityCounts U where
  trueVotes := trueVotes sample
  falseVotes := falseVotes sample

/-- The sample-level plug-in majority predictor.  Ties inherit the counted
majority convention and break toward `true`. -/
def predict [DecidableEq U] (sample : Sample U Bool) (u : U) : Bool :=
  (counts sample).predict u

/-- The graph sample of a rule: one labeled example for each visible input. -/
noncomputable def graphSample [Fintype U] (rule : U → Bool) : Sample U Bool :=
  (Finset.univ : Finset U).toList.map (fun u => (u, rule u))

theorem trueVotes_graphSample [Fintype U] [DecidableEq U]
    (rule : U → Bool) (u : U) :
    trueVotes (graphSample rule) u = if rule u then 1 else 0 := by
  by_cases h : rule u
  · have hcount : ((Finset.univ : Finset U).toList.count u) = 1 := by
      exact List.count_eq_one_of_mem
        (Finset.nodup_toList (Finset.univ : Finset U)) (by simp)
    rw [List.count_eq_countP] at hcount
    rw [trueVotes, graphSample, List.countP_map]
    have hcongr :
        List.countP
            ((fun ex : U × Bool => decide (ex.1 = u ∧ ex.2 = true)) ∘
              fun v => (v, rule v))
            (Finset.univ : Finset U).toList =
          List.countP (fun v => v == u) (Finset.univ : Finset U).toList := by
      apply List.countP_congr
      intro v _hv
      by_cases hvu : v = u
      · subst hvu
        simp [h]
      · simp [hvu]
    rw [hcongr]
    simpa [h] using hcount
  · rw [trueVotes, graphSample, List.countP_map]
    simp [h]

theorem falseVotes_graphSample [Fintype U] [DecidableEq U]
    (rule : U → Bool) (u : U) :
    falseVotes (graphSample rule) u = if rule u then 0 else 1 := by
  by_cases h : rule u
  · rw [falseVotes, graphSample, List.countP_map]
    simp [h]
  · have hcount : ((Finset.univ : Finset U).toList.count u) = 1 := by
      exact List.count_eq_one_of_mem
        (Finset.nodup_toList (Finset.univ : Finset U)) (by simp)
    rw [List.count_eq_countP] at hcount
    rw [falseVotes, graphSample, List.countP_map]
    have hcongr :
        List.countP
            ((fun ex : U × Bool => decide (ex.1 = u ∧ ex.2 = false)) ∘
              fun v => (v, rule v))
            (Finset.univ : Finset U).toList =
          List.countP (fun v => v == u) (Finset.univ : Finset U).toList := by
      apply List.countP_congr
      intro v _hv
      by_cases hvu : v = u
      · subst hvu
        simp [h]
      · simp [hvu]
    rw [hcongr]
    simpa [h] using hcount

/-- A graph sample makes sample-level plug-in majority recover the rule exactly. -/
@[simp] theorem predict_graphSample [Fintype U] [DecidableEq U]
    (rule : U → Bool) (u : U) :
    predict (graphSample rule) u = rule u := by
  cases h : rule u <;>
    simp [predict, counts, PluginMajorityCounts.predict,
      trueVotes_graphSample, falseVotes_graphSample, h]

end PluginSampleMajority

/-- The actual switched-local interface induced by unrestricted finite samples
and sample-level plug-in majority on the exact visible post-switch alphabet. -/
noncomputable def pluginSampleMajorityActualSwitchedLocalInterface
    (Z : Type v) (k : ℕ) :
    ActualSwitchedLocalInterface
      Z k
      (Sample (ExactVisiblePostSwitchSurface Z k) Bool)
      (ExactVisiblePostSwitchSurface Z k) where
  zOf := fun u => u.z
  aOf := fun _ u => u.a
  bOf := fun u => u.b
  localRule := fun sample u =>
    letI := Classical.decEq (ExactVisiblePostSwitchSurface Z k)
    PluginSampleMajority.predict sample u
  output := fun sample u =>
    letI := Classical.decEq (ExactVisiblePostSwitchSurface Z k)
    PluginSampleMajority.predict sample u
  output_eq_local := by
    intro sample u
    rfl

/-- Every Boolean lookup table on the post-switch alphabet occurs as a
sample-level plug-in majority rule, using the graph sample of that rule. -/
theorem pluginSampleMajorityActualSwitchedLocalInterface_realizes_every_lookupTable
    {Z : Type v} {k : ℕ} [Fintype Z] (rule : ExactVisibleRule Z k) :
    ∃ sample,
      (pluginSampleMajorityActualSwitchedLocalInterface Z k).predictorFamily.predict
          sample =
        rule := by
  classical
  refine ⟨PluginSampleMajority.graphSample rule, ?_⟩
  funext u
  simp [pluginSampleMajorityActualSwitchedLocalInterface,
    ActualSwitchedLocalInterface.predictorFamily]

/-- The unrestricted sample-level plug-in majority endpoint is surjective onto
all Boolean rules on the exact visible post-switch alphabet. -/
theorem pluginSampleMajorityActualSwitchedLocalInterface_surjective
    (Z : Type v) (k : ℕ) [Fintype Z] :
    Function.Surjective
      (pluginSampleMajorityActualSwitchedLocalInterface Z k).predictorFamily.predict := by
  intro rule
  exact pluginSampleMajorityActualSwitchedLocalInterface_realizes_every_lookupTable rule

/-- Sample-level plug-in majority has no small finite predictor cover below the
exact visible truth-table budget. -/
theorem pluginSampleMajorityActualSwitchedLocalInterface_not_finitePredictorCover_of_lt_surfaceCard
    {Z : Type v} {k s : ℕ} [Fintype Z]
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (pluginSampleMajorityActualSwitchedLocalInterface Z k).predictorFamily.FinitePredictorCover
        (2 ^ s) := by
  intro hcover
  have hsmall :
      ExactVisibleCompressionTarget
        (Z := Z) (k := k)
        (Index := Sample (ExactVisiblePostSwitchSurface Z k) Bool)
        (pluginSampleMajorityActualSwitchedLocalInterface Z k).predictorFamily s :=
    (exactVisibleCompressionTarget_iff_finitePredictorCover
      (Z := Z) (k := k) (s := s)
      (Index := Sample (ExactVisiblePostSwitchSurface Z k) Bool)
      (G := (pluginSampleMajorityActualSwitchedLocalInterface Z k).predictorFamily)).2
      hcover
  exact
    (not_exactVisibleCompressionTarget_of_surjective_predict
      (Z := Z) (k := k) (s := s)
      (Index := Sample (ExactVisiblePostSwitchSurface Z k) Bool)
      (G := (pluginSampleMajorityActualSwitchedLocalInterface Z k).predictorFamily)
      hs (pluginSampleMajorityActualSwitchedLocalInterface_surjective Z k)) hsmall

/-- Sample-level plug-in majority does not provide the clocked finite-learning
payload below the exact visible truth-table budget. -/
theorem pluginSampleMajorityActualSwitchedLocalInterface_not_clockedKpolyFiniteLearningPayload_of_lt_surfaceCard
    {Z : Type v} {k s clock : ℕ} [Fintype Z]
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ClockedKpolyFiniteLearningPayload
        (pluginSampleMajorityActualSwitchedLocalInterface Z k).predictorFamily s clock := by
  intro hpayload
  have hsmall :
      ExactVisibleCompressionTarget
        (Z := Z) (k := k)
        (Index := Sample (ExactVisiblePostSwitchSurface Z k) Bool)
        (pluginSampleMajorityActualSwitchedLocalInterface Z k).predictorFamily s :=
    exactVisibleCompressionTarget_of_clockedKpolyFiniteLearningPayload
      (Z := Z) (k := k) (s := s) (clock := clock)
      (Index := Sample (ExactVisiblePostSwitchSurface Z k) Bool)
      hpayload
  exact
    (not_exactVisibleCompressionTarget_of_surjective_predict
      (Z := Z) (k := k) (s := s)
      (Index := Sample (ExactVisiblePostSwitchSurface Z k) Bool)
      (G := (pluginSampleMajorityActualSwitchedLocalInterface Z k).predictorFamily)
      hs (pluginSampleMajorityActualSwitchedLocalInterface_surjective Z k)) hsmall

/-- Sample-level plug-in majority cannot supply the bounded-code minimal missing
assumption below the exact visible truth-table budget. -/
theorem pluginSampleMajorityActualSwitchedLocalInterface_not_bitCodeData_of_lt_surfaceCard
    {Z : Type v} {k s : ℕ} [Fintype Z]
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.BitCodeData
          (pluginSampleMajorityActualSwitchedLocalInterface Z k) s) := by
  rintro ⟨hcode⟩
  exact
    pluginSampleMajorityActualSwitchedLocalInterface_not_finitePredictorCover_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) hs hcode.finitePredictorCover

/-- Sample-level plug-in majority also cannot supply the ZAB decision-list
constructor data below the exact visible truth-table budget. -/
theorem pluginSampleMajorityActualSwitchedLocalInterface_not_zabDecisionListData_of_lt_surfaceCard
    {Z : Type v} {k r : ℕ} [Fintype Z]
    (zfeat : Z → BitVec r)
    (hs : r + 2 * k + 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.ZABDecisionListData
          (pluginSampleMajorityActualSwitchedLocalInterface Z k) zfeat) := by
  rintro ⟨hzab⟩
  exact
    hzab.not_surjective_predict_of_lt_surfaceCard hs
      (pluginSampleMajorityActualSwitchedLocalInterface_surjective Z k)

end Mettapedia.Computability.PNP
