import Mettapedia.Computability.PNP.ActualSwitchedLocalPluginSampleMajorityObstruction

/-!
# PNP grassroots: bounded sample size still does not force a small image

`ActualSwitchedLocalPluginSampleMajorityObstruction` shows that unrestricted
finite-sample plug-in majority can realize every Boolean rule on the exact
visible alphabet `u = (z, a, b)`.  This file checks the next natural repair:
what if the training sample is bounded?

The graph sample of a rule has exactly one labeled example for each visible
input.  Therefore any sample bound at least the size of the exact visible
alphabet still realizes the full Boolean rule family.  This blocks the repair
"the local plug-in majority is finite and polynomial-sized" unless the
polynomial bound is proven to be below the visible alphabet size or the samples
are otherwise restricted into the existing ZAB ERM/code family.
-/

namespace Mettapedia.Computability.PNP

universe v

/-- The exact-visible Boolean rule cube is finite whenever the hidden alphabet
is finite.  The global function-space instance needs decidable equality on the
domain; this instance packages the classical choice at the exact-visible layer. -/
noncomputable instance instFintypeExactVisibleRule
    (Z : Type v) (k : ℕ) [Fintype Z] :
    Fintype (ExactVisibleRule Z k) := by
  classical
  unfold ExactVisibleRule ExactVisiblePostSwitchSurface
  infer_instance

namespace PluginSampleMajority

/-- The graph sample uses exactly one labeled example for each input. -/
theorem length_graphSample {U : Type v} [Fintype U] (rule : U → Bool) :
    (graphSample rule).length = Fintype.card U := by
  simp [graphSample]

/-- Sample-level plug-in majority with an explicit tie-breaking default. -/
def predictWithDefault {U : Type v} [DecidableEq U]
    (default : Bool) (sample : Sample U Bool) (u : U) : Bool :=
  if trueVotes sample u = falseVotes sample u then
    default
  else if falseVotes sample u < trueVotes sample u then
    true
  else
    false

/-- Sample-level plug-in majority with an input-dependent fallback used only on
ties.  This is the natural formal target for attempts to repair a bad fixed
tie-break by choosing the tie-break as a visible-input function. -/
def predictWithFallback {U : Type v} [DecidableEq U]
    (fallback : U → Bool) (sample : Sample U Bool) (u : U) : Bool :=
  if trueVotes sample u = falseVotes sample u then
    fallback u
  else if falseVotes sample u < trueVotes sample u then
    true
  else
    false

@[simp] theorem predictWithDefault_graphSample
    {U : Type v} [Fintype U] [DecidableEq U]
    (default : Bool) (rule : U → Bool) (u : U) :
    predictWithDefault default (graphSample rule) u = rule u := by
  cases h : rule u <;>
    simp [predictWithDefault, trueVotes_graphSample, falseVotes_graphSample, h]

@[simp] theorem predictWithFallback_graphSample
    {U : Type v} [Fintype U] [DecidableEq U]
    (fallback rule : U → Bool) (u : U) :
    predictWithFallback fallback (graphSample rule) u = rule u := by
  cases h : rule u <;>
    simp [predictWithFallback, trueVotes_graphSample, falseVotes_graphSample, h]

@[simp] theorem predictWithFallback_nil
    {U : Type v} [DecidableEq U] (fallback : U → Bool) (u : U) :
    predictWithFallback fallback ([] : Sample U Bool) u = fallback u := by
  simp [predictWithFallback, trueVotes, falseVotes]

/-- The sample that labels exactly the points in a chosen finite support. -/
noncomputable def supportSample {U : Type v}
    (support : Finset U) (rule : U → Bool) : Sample U Bool :=
  support.toList.map (fun u => (u, rule u))

@[simp] theorem length_supportSample {U : Type v}
    (support : Finset U) (rule : U → Bool) :
    (supportSample support rule).length = support.card := by
  simp [supportSample]

@[simp] theorem mem_map_fst_supportSample
    {U : Type v} {support : Finset U} {rule : U → Bool} {u : U} :
    u ∈ (supportSample support rule).map Prod.fst ↔ u ∈ support := by
  simp [supportSample]

theorem trueVotes_supportSample {U : Type v} [DecidableEq U]
    (support : Finset U) (rule : U → Bool) (u : U) :
    trueVotes (supportSample support rule) u =
      if u ∈ support then
        if rule u then 1 else 0
      else 0 := by
  by_cases hu : u ∈ support
  · by_cases h : rule u
    · have hcount : support.toList.count u = 1 := by
        exact List.count_eq_one_of_mem
          support.nodup_toList (by simpa using hu)
      rw [List.count_eq_countP] at hcount
      rw [trueVotes, supportSample, List.countP_map]
      have hcongr :
          List.countP
              ((fun ex : U × Bool => decide (ex.1 = u ∧ ex.2 = true)) ∘
                fun v => (v, rule v))
              support.toList =
            List.countP (fun v => v == u) support.toList := by
        apply List.countP_congr
        intro v _hv
        by_cases hvu : v = u
        · subst hvu
          simp [h]
        · simp [hvu]
      rw [hcongr]
      simpa [hu, h] using hcount
    · rw [trueVotes, supportSample, List.countP_map]
      simp [hu, h]
      intro v _hv hvu
      subst hvu
      exact Bool.eq_false_of_not_eq_true h
  · have hzero :
        trueVotes (supportSample support rule) u = 0 := by
      rw [trueVotes]
      exact List.countP_eq_zero.mpr (by
        intro ex hex hp
        rcases List.mem_map.mp hex with ⟨v, hv, rfl⟩
        have hp' : v = u ∧ rule v = true := of_decide_eq_true hp
        exact hu (by
          simpa [hp'.1] using hv))
    simpa [hu] using hzero

theorem falseVotes_supportSample {U : Type v} [DecidableEq U]
    (support : Finset U) (rule : U → Bool) (u : U) :
    falseVotes (supportSample support rule) u =
      if u ∈ support then
        if rule u then 0 else 1
      else 0 := by
  by_cases hu : u ∈ support
  · by_cases h : rule u
    · rw [falseVotes, supportSample, List.countP_map]
      simp [hu, h]
      intro v _hv hvu
      subst hvu
      exact h
    · have hcount : support.toList.count u = 1 := by
        exact List.count_eq_one_of_mem
          support.nodup_toList (by simpa using hu)
      rw [List.count_eq_countP] at hcount
      rw [falseVotes, supportSample, List.countP_map]
      have hcongr :
          List.countP
              ((fun ex : U × Bool => decide (ex.1 = u ∧ ex.2 = false)) ∘
                fun v => (v, rule v))
              support.toList =
            List.countP (fun v => v == u) support.toList := by
        apply List.countP_congr
        intro v _hv
        by_cases hvu : v = u
        · subst hvu
          simp [h]
        · simp [hvu]
      rw [hcongr]
      simpa [hu, h] using hcount
  · have hzero :
        falseVotes (supportSample support rule) u = 0 := by
      rw [falseVotes]
      exact List.countP_eq_zero.mpr (by
        intro ex hex hp
        rcases List.mem_map.mp hex with ⟨v, hv, rfl⟩
        have hp' : v = u ∧ rule v = false := of_decide_eq_true hp
        exact hu (by
          simpa [hp'.1] using hv))
    simpa [hu] using hzero

/-- Sampling exactly an override support realizes any rule that agrees with
the fallback off that support. -/
theorem predictWithFallback_supportSample_eq_of_eq_off_support
    {U : Type v} [DecidableEq U]
    (fallback rule : U → Bool) (support : Finset U)
    (hoff : ∀ u : U, u ∉ support → fallback u = rule u) :
    predictWithFallback fallback (supportSample support rule) = rule := by
  funext u
  by_cases hu : u ∈ support
  · cases h : rule u <;>
      simp [predictWithFallback, trueVotes_supportSample,
        falseVotes_supportSample, hu, h]
  · simp [predictWithFallback, trueVotes_supportSample,
      falseVotes_supportSample, hu, hoff u hu]

/-- A sample shorter than a finite input alphabet omits some input. -/
theorem exists_not_mem_map_fst_of_length_lt_card {U : Type v} [Fintype U] [DecidableEq U]
    {sample : Sample U Bool} (hlen : sample.length < Fintype.card U) :
    ∃ u : U, u ∉ sample.map Prod.fst := by
  by_contra hnone
  push_neg at hnone
  have huniv : (sample.map Prod.fst).toFinset = (Finset.univ : Finset U) := by
    exact Finset.eq_univ_iff_forall.mpr (by
      intro x
      simpa using hnone x)
  have hcard : Fintype.card U ≤ sample.length := by
    calc
      Fintype.card U = ((sample.map Prod.fst).toFinset).card := by
        simp [huniv]
      _ ≤ (sample.map Prod.fst).length := List.toFinset_card_le (sample.map Prod.fst)
      _ = sample.length := by
        simp
  exact (not_lt_of_ge hcard) hlen

/-- If an input never occurs in the sample, it has no true votes. -/
theorem trueVotes_eq_zero_of_not_mem_map_fst {U : Type v} [DecidableEq U]
    {sample : Sample U Bool} {u : U} (h : u ∉ sample.map Prod.fst) :
    trueVotes sample u = 0 := by
  rw [trueVotes]
  exact List.countP_eq_zero.mpr (by
    intro ex hex hp
    have hp' : ex.1 = u ∧ ex.2 = true := by
      simpa using hp
    exact h (List.mem_map.mpr ⟨ex, hex, hp'.1⟩))

/-- If an input never occurs in the sample, it has no false votes. -/
theorem falseVotes_eq_zero_of_not_mem_map_fst {U : Type v} [DecidableEq U]
    {sample : Sample U Bool} {u : U} (h : u ∉ sample.map Prod.fst) :
    falseVotes sample u = 0 := by
  rw [falseVotes]
  exact List.countP_eq_zero.mpr (by
    intro ex hex hp
    have hp' : ex.1 = u ∧ ex.2 = false := by
      simpa using hp
    exact h (List.mem_map.mpr ⟨ex, hex, hp'.1⟩))

/-- On an input omitted by the sample, the tie-breaking plug-in majority
predicts `true`. -/
theorem predict_eq_true_of_not_mem_map_fst {U : Type v} [DecidableEq U]
    {sample : Sample U Bool} {u : U} (h : u ∉ sample.map Prod.fst) :
    predict sample u = true := by
  have hf : falseVotes sample u = 0 := falseVotes_eq_zero_of_not_mem_map_fst h
  simp [predict, counts, PluginMajorityCounts.predict, hf]

/-- On an input omitted by the sample, the explicit-default plug-in majority
returns exactly the default. -/
theorem predictWithDefault_eq_default_of_not_mem_map_fst
    {U : Type v} [DecidableEq U] {default : Bool}
    {sample : Sample U Bool} {u : U} (h : u ∉ sample.map Prod.fst) :
    predictWithDefault default sample u = default := by
  have ht : trueVotes sample u = 0 := trueVotes_eq_zero_of_not_mem_map_fst h
  have hf : falseVotes sample u = 0 := falseVotes_eq_zero_of_not_mem_map_fst h
  simp [predictWithDefault, ht, hf]

/-- On an input omitted by the sample, an input-dependent fallback plug-in
majority returns the fallback rule. -/
theorem predictWithFallback_eq_fallback_of_not_mem_map_fst
    {U : Type v} [DecidableEq U] {fallback : U → Bool}
    {sample : Sample U Bool} {u : U} (h : u ∉ sample.map Prod.fst) :
    predictWithFallback fallback sample u = fallback u := by
  have ht : trueVotes sample u = 0 := trueVotes_eq_zero_of_not_mem_map_fst h
  have hf : falseVotes sample u = 0 := falseVotes_eq_zero_of_not_mem_map_fst h
  simp [predictWithFallback, ht, hf]

/-- Every sample shorter than the finite alphabet has at least one input on
which plug-in majority predicts `true`. -/
theorem exists_true_prediction_of_length_lt_card {U : Type v} [Fintype U] [DecidableEq U]
    {sample : Sample U Bool} (hlen : sample.length < Fintype.card U) :
    ∃ u : U, predict sample u = true := by
  rcases exists_not_mem_map_fst_of_length_lt_card (sample := sample) hlen with ⟨u, hu⟩
  exact ⟨u, predict_eq_true_of_not_mem_map_fst hu⟩

/-- The finite set of inputs on which a Boolean rule returns `false`. -/
def falseSupport {U : Type v} [Fintype U] (rule : U → Bool) :
    Finset U :=
  (Finset.univ : Finset U).filter (fun u => rule u = false)

@[simp] theorem mem_falseSupport {U : Type v} [Fintype U]
    {rule : U → Bool} {u : U} :
    u ∈ falseSupport rule ↔ rule u = false := by
  simp [falseSupport]

/-- The finite set of inputs on which a Boolean rule differs from a chosen
default value. -/
def nondefaultSupport {U : Type v} [Fintype U] (default : Bool) (rule : U → Bool) :
    Finset U :=
  (Finset.univ : Finset U).filter (fun u => rule u ≠ default)

/-- The finite set of inputs on which one Boolean rule differs from a reference
rule. -/
def disagreementSupport {U : Type v} [Fintype U] (reference rule : U → Bool) :
    Finset U :=
  (Finset.univ : Finset U).filter (fun u => rule u ≠ reference u)

@[simp] theorem mem_nondefaultSupport {U : Type v} [Fintype U]
    {default : Bool} {rule : U → Bool} {u : U} :
    u ∈ nondefaultSupport default rule ↔ rule u ≠ default := by
  simp [nondefaultSupport]

@[simp] theorem mem_disagreementSupport {U : Type v} [Fintype U]
    {reference rule : U → Bool} {u : U} :
    u ∈ disagreementSupport reference rule ↔ rule u ≠ reference u := by
  simp [disagreementSupport]

/-- A disagreement support never has more points than the finite input
alphabet. -/
theorem disagreementSupport_card_le_card {U : Type v} [Fintype U]
    (reference rule : U → Bool) :
    (disagreementSupport reference rule).card ≤ Fintype.card U := by
  classical
  simpa [Finset.card_univ] using
    (Finset.card_le_univ (s := disagreementSupport reference rule))

/-- The rule constantly opposite to the chosen default differs from that default
at every finite input. -/
theorem nondefaultSupport_const_not_card
    {U : Type v} [Fintype U] (default : Bool) :
    (nondefaultSupport default (fun _ : U => !default)).card = Fintype.card U := by
  cases default <;> simp [nondefaultSupport]

/-- If sample-level plug-in majority predicts `false` at an input, then that
input must occur in the sample.  Omitted inputs tie at zero votes and therefore
predict `true`. -/
theorem mem_map_fst_of_predict_eq_false {U : Type v} [DecidableEq U]
    {sample : Sample U Bool} {u : U} (hfalse : predict sample u = false) :
    u ∈ sample.map Prod.fst := by
  by_contra hmissing
  have htrue : predict sample u = true :=
    predict_eq_true_of_not_mem_map_fst (sample := sample) (u := u) hmissing
  rw [hfalse] at htrue
  cases htrue

/-- If explicit-default sample-level plug-in majority differs from the default
at an input, then that input must occur in the sample. -/
theorem mem_map_fst_of_predictWithDefault_ne_default
    {U : Type v} [DecidableEq U] {default : Bool}
    {sample : Sample U Bool} {u : U}
    (hne : predictWithDefault default sample u ≠ default) :
    u ∈ sample.map Prod.fst := by
  by_contra hmissing
  exact hne (predictWithDefault_eq_default_of_not_mem_map_fst hmissing)

/-- If input-dependent fallback plug-in majority differs from its fallback at
an input, then that input must occur in the sample. -/
theorem mem_map_fst_of_predictWithFallback_ne_fallback
    {U : Type v} [DecidableEq U] {fallback : U → Bool}
    {sample : Sample U Bool} {u : U}
    (hne : predictWithFallback fallback sample u ≠ fallback u) :
    u ∈ sample.map Prod.fst := by
  by_contra hmissing
  exact hne (predictWithFallback_eq_fallback_of_not_mem_map_fst hmissing)

/-- The false-support of any sample-level plug-in majority prediction is
contained in the set of visible inputs that appear in the sample. -/
theorem falseSupport_predict_subset_sampleInputs
    {U : Type v} [Fintype U] [DecidableEq U] (sample : Sample U Bool) :
    falseSupport (fun u : U => predict sample u) ⊆
      (sample.map Prod.fst).toFinset := by
  intro u hu
  have hfalse : predict sample u = false := by
    simpa using (mem_falseSupport (rule := fun u : U => predict sample u) (u := u)).1 hu
  have hmem : u ∈ sample.map Prod.fst :=
    mem_map_fst_of_predict_eq_false (sample := sample) (u := u) hfalse
  simpa using hmem

/-- Therefore a sample-level plug-in majority predictor can be false on at most
`sample.length` distinct inputs. -/
theorem falseSupport_predict_card_le_length
    {U : Type v} [Fintype U] [DecidableEq U] (sample : Sample U Bool) :
    (falseSupport (fun u : U => predict sample u)).card ≤ sample.length := by
  calc
    (falseSupport (fun u : U => predict sample u)).card
        ≤ ((sample.map Prod.fst).toFinset).card :=
          Finset.card_le_card (falseSupport_predict_subset_sampleInputs sample)
    _ ≤ (sample.map Prod.fst).length := List.toFinset_card_le (sample.map Prod.fst)
    _ = sample.length := by
          simp

/-- The nondefault support of any explicit-default sample-level plug-in majority
prediction is contained in the set of visible inputs that appear in the sample. -/
theorem nondefaultSupport_predictWithDefault_subset_sampleInputs
    {U : Type v} [Fintype U] [DecidableEq U]
    (default : Bool) (sample : Sample U Bool) :
    nondefaultSupport default (fun u : U => predictWithDefault default sample u) ⊆
      (sample.map Prod.fst).toFinset := by
  intro u hu
  have hne : predictWithDefault default sample u ≠ default := by
    simpa using
      (mem_nondefaultSupport
        (default := default)
        (rule := fun u : U => predictWithDefault default sample u) (u := u)).1 hu
  have hmem : u ∈ sample.map Prod.fst :=
    mem_map_fst_of_predictWithDefault_ne_default
      (default := default) (sample := sample) (u := u) hne
  simpa using hmem

/-- The disagreement support of an input-dependent fallback plug-in majority
prediction is contained in the set of visible inputs that appear in the sample. -/
theorem disagreementSupport_predictWithFallback_subset_sampleInputs
    {U : Type v} [Fintype U] [DecidableEq U]
    (fallback : U → Bool) (sample : Sample U Bool) :
    disagreementSupport fallback (fun u : U => predictWithFallback fallback sample u) ⊆
      (sample.map Prod.fst).toFinset := by
  intro u hu
  have hne : predictWithFallback fallback sample u ≠ fallback u := by
    simpa using
      (mem_disagreementSupport
        (reference := fallback)
        (rule := fun u : U => predictWithFallback fallback sample u) (u := u)).1 hu
  have hmem : u ∈ sample.map Prod.fst :=
    mem_map_fst_of_predictWithFallback_ne_fallback
      (fallback := fallback) (sample := sample) (u := u) hne
  simpa using hmem

/-- Therefore an explicit-default sample-level plug-in majority predictor can
differ from the default on at most `sample.length` distinct inputs. -/
theorem nondefaultSupport_predictWithDefault_card_le_length
    {U : Type v} [Fintype U] [DecidableEq U]
    (default : Bool) (sample : Sample U Bool) :
    (nondefaultSupport default
      (fun u : U => predictWithDefault default sample u)).card ≤ sample.length := by
  calc
    (nondefaultSupport default
        (fun u : U => predictWithDefault default sample u)).card
        ≤ ((sample.map Prod.fst).toFinset).card :=
          Finset.card_le_card
            (nondefaultSupport_predictWithDefault_subset_sampleInputs default sample)
    _ ≤ (sample.map Prod.fst).length := List.toFinset_card_le (sample.map Prod.fst)
    _ = sample.length := by
          simp

/-- Therefore an input-dependent fallback plug-in majority predictor can differ
from its fallback on at most `sample.length` distinct inputs. -/
theorem disagreementSupport_predictWithFallback_card_le_length
    {U : Type v} [Fintype U] [DecidableEq U]
    (fallback : U → Bool) (sample : Sample U Bool) :
    (disagreementSupport fallback
      (fun u : U => predictWithFallback fallback sample u)).card ≤ sample.length := by
  calc
    (disagreementSupport fallback
        (fun u : U => predictWithFallback fallback sample u)).card
        ≤ ((sample.map Prod.fst).toFinset).card :=
          Finset.card_le_card
            (disagreementSupport_predictWithFallback_subset_sampleInputs fallback sample)
    _ ≤ (sample.map Prod.fst).length := List.toFinset_card_le (sample.map Prod.fst)
    _ = sample.length := by
          simp

end PluginSampleMajority

/-- Samples over `U` whose length is bounded by `sampleBound`. -/
abbrev BoundedSampleIndex (U : Type v) (sampleBound : ℕ) :=
  { sample : Sample U Bool // sample.length ≤ sampleBound }

/-- A bounded sample together with an input-dependent fallback rule.  The
fallback component is itself a full Boolean lookup table on the input surface;
the theorems below make that side-channel explicit. -/
abbrev BoundedSampleFallbackIndex (U : Type v) (sampleBound : ℕ) :=
  (U → Bool) × BoundedSampleIndex U sampleBound

/-- A bounded sample together with a code selecting a fallback rule from a
structured fallback family. -/
abbrev BoundedSampleFallbackFamilyIndex
    (FallbackIndex U : Type v) (sampleBound : ℕ) :=
  FallbackIndex × BoundedSampleIndex U sampleBound

namespace PluginSampleMajority

/-- A bounded sample-level plug-in majority predictor can be false on at most
`sampleBound` inputs. -/
theorem falseSupport_predict_card_le_bound
    {U : Type v} [Fintype U] [DecidableEq U] {sampleBound : ℕ}
    (sample : BoundedSampleIndex U sampleBound) :
    (falseSupport (fun u : U => predict sample.1 u)).card ≤ sampleBound :=
  le_trans (falseSupport_predict_card_le_length sample.1) sample.2

/-- A bounded explicit-default sample-level plug-in majority predictor can
differ from the default on at most `sampleBound` inputs. -/
theorem nondefaultSupport_predictWithDefault_card_le_bound
    {U : Type v} [Fintype U] [DecidableEq U] {sampleBound : ℕ}
    (default : Bool) (sample : BoundedSampleIndex U sampleBound) :
    (nondefaultSupport default
      (fun u : U => predictWithDefault default sample.1 u)).card ≤ sampleBound :=
  le_trans (nondefaultSupport_predictWithDefault_card_le_length default sample.1) sample.2

/-- A bounded input-dependent fallback plug-in majority predictor can differ
from its fallback on at most `sampleBound` inputs. -/
theorem disagreementSupport_predictWithFallback_card_le_bound
    {U : Type v} [Fintype U] [DecidableEq U] {sampleBound : ℕ}
    (fallback : U → Bool) (sample : BoundedSampleIndex U sampleBound) :
    (disagreementSupport fallback
      (fun u : U => predictWithFallback fallback sample.1 u)).card ≤ sampleBound :=
  le_trans (disagreementSupport_predictWithFallback_card_le_length fallback sample.1) sample.2

/-- Flip a Boolean reference rule exactly on a finite set of inputs. -/
noncomputable def flipOn {U : Type v}
    (reference : U → Bool) (s : Finset U) : U → Bool := by
  classical
  exact fun u => if u ∈ s then !reference u else reference u

/-- Small subsets of a finite input alphabet, used to count Hamming balls of
Boolean rules. -/
noncomputable def smallSubsets (U : Type v) [Fintype U] (radius : ℕ) :
    Finset (Finset U) := by
  classical
  exact (Finset.univ : Finset (Finset U)).filter (fun s => s.card ≤ radius)

@[simp] theorem mem_smallSubsets {U : Type v} [Fintype U]
    {radius : ℕ} {s : Finset U} :
    s ∈ smallSubsets U radius ↔ s.card ≤ radius := by
  classical
  simp [smallSubsets]

/-- At radius zero the only allowed sparse override support is the empty set. -/
@[simp] theorem smallSubsets_zero {U : Type v} [Fintype U] :
    smallSubsets U 0 = ({∅} : Finset (Finset U)) := by
  classical
  ext s
  simp [smallSubsets]

/-- There is exactly one radius-zero sparse override support. -/
@[simp] theorem card_smallSubsets_zero {U : Type v} [Fintype U] :
    (smallSubsets U 0).card = 1 := by
  classical
  simp

/-- At radius one the allowed sparse override supports are exactly the empty
set and all singleton supports. -/
theorem smallSubsets_one {U : Type v} [Fintype U] [DecidableEq U] :
    smallSubsets U 1 =
      insert ∅ ((Finset.univ : Finset U).image (fun u => ({u} : Finset U))) := by
  classical
  ext s
  constructor
  · intro hs
    have hcard : s.card ≤ 1 := by
      simpa using
        (mem_smallSubsets (U := U) (radius := 1) (s := s)).1 hs
    by_cases hempty : s = ∅
    · simp [hempty]
    · have hpos : 0 < s.card :=
        Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hempty)
      have hone : s.card = 1 := le_antisymm hcard (Nat.succ_le_of_lt hpos)
      rcases Finset.card_eq_one.mp hone with ⟨u, rfl⟩
      simp
  · intro hs
    rw [mem_smallSubsets]
    rcases Finset.mem_insert.mp hs with hempty | hsingle
    · subst s
      simp
    · rcases Finset.mem_image.mp hsingle with ⟨u, _hu, rfl⟩
      simp

/-- There are exactly `#U + 1` radius-one sparse override supports: the empty
support and one singleton support for each input. -/
@[simp] theorem card_smallSubsets_one {U : Type v} [Fintype U] :
    (smallSubsets U 1).card = Fintype.card U + 1 := by
  classical
  rw [smallSubsets_one]
  have hnot :
      ∅ ∉ ((Finset.univ : Finset U).image (fun u => ({u} : Finset U))) := by
    intro hmem
    rcases Finset.mem_image.mp hmem with ⟨u, _hu, hsingle⟩
    have hcard := congrArg Finset.card hsingle
    simp at hcard
  rw [Finset.card_insert_of_notMem hnot]
  have hinj : Function.Injective (fun u : U => ({u} : Finset U)) := by
    intro u v hsingle
    have hu : u ∈ ({v} : Finset U) := by
      simp [← hsingle]
    simpa using hu
  rw [Finset.card_image_of_injective _ hinj]
  simp

/-- Small subsets are the disjoint union of fixed-cardinality powersets up to
the radius.  This is the exact finite Hamming-ball support partition. -/
theorem smallSubsets_eq_biUnion_powersetCard_range
    {U : Type v} [Fintype U] [DecidableEq U] (radius : ℕ) :
    smallSubsets U radius =
      (Finset.range (radius + 1)).biUnion
        (fun i => (Finset.univ : Finset U).powersetCard i) := by
  classical
  ext s
  constructor
  · intro hs
    have hcard : s.card ≤ radius := by
      simpa using
        (mem_smallSubsets (U := U) (radius := radius) (s := s)).1 hs
    exact Finset.mem_biUnion.mpr
      ⟨s.card, by simpa [Nat.lt_succ_iff] using hcard, by
        rw [Finset.mem_powersetCard]
        exact ⟨by simp, rfl⟩⟩
  · intro hs
    rw [mem_smallSubsets]
    rcases Finset.mem_biUnion.mp hs with ⟨i, hi, hsi⟩
    have hi_le : i ≤ radius := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hcard : s.card = i := (Finset.mem_powersetCard.mp hsi).2
    exact hcard.trans_le hi_le

/-- Exact cardinality of the radius-`radius` sparse support family.  A sampled
override budget of radius `r` buys exactly the finite Hamming-ball support count
`∑ i ≤ r, (#U choose i)`. -/
theorem card_smallSubsets_eq_sum_range_choose
    {U : Type v} [Fintype U] (radius : ℕ) :
    (smallSubsets U radius).card =
      ∑ i ∈ Finset.range (radius + 1), (Fintype.card U).choose i := by
  classical
  rw [smallSubsets_eq_biUnion_powersetCard_range (U := U) radius]
  rw [Finset.card_biUnion]
  · simp [Finset.card_powersetCard]
  · exact ((Finset.univ : Finset U).pairwise_disjoint_powersetCard.set_pairwise _)

/-- Exact cardinality of the two-sample sparse support family.  With at most
two sampled overrides, the support budget is the empty support, one overwritten
input, or an unordered pair of overwritten inputs. -/
@[simp] theorem card_smallSubsets_two
    {U : Type v} [Fintype U] :
    (smallSubsets U 2).card =
      1 + Fintype.card U + (Fintype.card U).choose 2 := by
  rw [card_smallSubsets_eq_sum_range_choose]
  simp [Finset.sum_range_succ, Nat.choose_one_right, Nat.add_assoc]

/-- Coarse polynomial upper bound for the finite Hamming-ball support count.
The `+ 1` in the base makes the statement valid even for empty finite types. -/
theorem sum_range_choose_le_succ_mul_succ_pow (n radius : ℕ) :
    (∑ i ∈ Finset.range (radius + 1), n.choose i) ≤
      (radius + 1) * (n + 1) ^ radius := by
  classical
  calc
    (∑ i ∈ Finset.range (radius + 1), n.choose i) ≤
        ∑ _i ∈ Finset.range (radius + 1), (n + 1) ^ radius := by
      refine Finset.sum_le_sum ?_
      intro i hi
      have hi_le : i ≤ radius := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      calc
        n.choose i ≤ n ^ i := Nat.choose_le_pow n i
        _ ≤ (n + 1) ^ i := Nat.pow_le_pow_left (Nat.le_succ n) i
        _ ≤ (n + 1) ^ radius := Nat.pow_le_pow_right (Nat.succ_pos n) hi_le
    _ = (radius + 1) * (n + 1) ^ radius := by
      simp [Finset.card_range]

/-- Coarse polynomial upper bound for the number of sparse override supports. -/
theorem card_smallSubsets_le_succ_mul_succ_card_pow
    {U : Type v} [Fintype U] (radius : ℕ) :
    (smallSubsets U radius).card ≤
      (radius + 1) * (Fintype.card U + 1) ^ radius := by
  rw [card_smallSubsets_eq_sum_range_choose]
  exact sum_range_choose_le_succ_mul_succ_pow (Fintype.card U) radius

/-- If the sparse support radius is below the finite alphabet size, then the
Hamming-ball support family is a proper subfamily of all finite subsets. -/
theorem smallSubsets_ssubset_univ_of_radius_lt_card
    {U : Type v} [Fintype U] {radius : ℕ}
    (hradius : radius < Fintype.card U) :
    smallSubsets U radius ⊂ (Finset.univ : Finset (Finset U)) := by
  classical
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro s _hs
    simp
  · intro hsmall
    have hmem : (Finset.univ : Finset U) ∈ smallSubsets U radius := by
      rw [hsmall]
      simp
    have hcard :
        Fintype.card U ≤ radius := by
      simpa [Finset.card_univ] using
        (mem_smallSubsets
          (U := U) (radius := radius) (s := (Finset.univ : Finset U))).1 hmem
    exact (not_lt_of_ge hcard) hradius

/-- Strict Hamming-ball support count: below full radius, the sparse support
family is strictly smaller than the full Boolean truth-table cube. -/
theorem card_smallSubsets_lt_twoPow_card_of_radius_lt_card
    {U : Type v} [Fintype U] {radius : ℕ}
    (hradius : radius < Fintype.card U) :
    (smallSubsets U radius).card < 2 ^ Fintype.card U := by
  classical
  have hlt :
      (smallSubsets U radius).card <
        (Finset.univ : Finset (Finset U)).card :=
    Finset.card_lt_card
      (smallSubsets_ssubset_univ_of_radius_lt_card
        (U := U) (radius := radius) hradius)
  simpa [Finset.card_univ, Fintype.card_finset] using hlt

/-- Strict binomial-prefix form of the Hamming-ball support count. -/
theorem sum_range_choose_lt_twoPow_of_lt {n radius : ℕ}
    (hradius : radius < n) :
    (∑ i ∈ Finset.range (radius + 1), n.choose i) < 2 ^ n := by
  classical
  have hlt :=
    card_smallSubsets_lt_twoPow_card_of_radius_lt_card
      (U := Fin n) (radius := radius) (by simpa using hradius)
  simpa [card_smallSubsets_eq_sum_range_choose] using hlt

/-- Bit-cost certificate for the coarse polynomial Hamming-ball envelope.  If
the radius multiplier and input-alphabet base each fit in explicit powers of
two, then the whole envelope fits in their additive exponent budget. -/
theorem succ_mul_succ_pow_le_twoPow_add_mul
    {n radius radiusBits baseBits : ℕ}
    (hradius : radius + 1 ≤ 2 ^ radiusBits)
    (hbase : n + 1 ≤ 2 ^ baseBits) :
    (radius + 1) * (n + 1) ^ radius ≤
      2 ^ (radiusBits + baseBits * radius) := by
  have hpow : (n + 1) ^ radius ≤ (2 ^ baseBits) ^ radius :=
    Nat.pow_le_pow_left hbase radius
  calc
    (radius + 1) * (n + 1) ^ radius ≤
        2 ^ radiusBits * (2 ^ baseBits) ^ radius :=
      Nat.mul_le_mul hradius hpow
    _ = 2 ^ (radiusBits + baseBits * radius) := by
      rw [← pow_mul, ← pow_add]

/-- If a radius is bounded by `2 ^ bits`, then its successor is bounded by the
next power of two.  This is the precise one-bit overhead needed when the
Hamming-ball envelope carries the factor `radius + 1`. -/
theorem succ_le_twoPow_succ_of_le_twoPow {radius bits : ℕ}
    (h : radius ≤ 2 ^ bits) :
    radius + 1 ≤ 2 ^ (bits + 1) := by
  have hsucc : radius + 1 ≤ 2 ^ bits + 1 := Nat.succ_le_succ h
  calc
    radius + 1 ≤ 2 ^ bits + 1 := hsucc
    _ ≤ 2 ^ bits + 2 ^ bits := Nat.add_le_add_left Nat.one_le_two_pow (2 ^ bits)
    _ = 2 ^ (bits + 1) := by
      rw [← Nat.mul_two, ← Nat.pow_succ]

/-- Variant of `succ_mul_succ_pow_le_twoPow_add_mul` for routes that state the
sample radius itself, rather than its successor, as fitting in a bit budget. -/
theorem succ_mul_succ_pow_le_twoPow_succ_add_mul
    {n radius radiusBits baseBits : ℕ}
    (hradius : radius ≤ 2 ^ radiusBits)
    (hbase : n + 1 ≤ 2 ^ baseBits) :
    (radius + 1) * (n + 1) ^ radius ≤
      2 ^ ((radiusBits + 1) + baseBits * radius) :=
  succ_mul_succ_pow_le_twoPow_add_mul
    (radiusBits := radiusBits + 1)
    (succ_le_twoPow_succ_of_le_twoPow hradius) hbase

/-- Flipping a reference rule on `s` creates disagreement support exactly `s`. -/
theorem disagreementSupport_flipOn
    {U : Type v} [Fintype U] (reference : U → Bool) (s : Finset U) :
    disagreementSupport reference (flipOn reference s) = s := by
  classical
  ext u
  by_cases hu : u ∈ s <;> cases reference u <;> simp [disagreementSupport, flipOn, hu]

/-- Any Boolean rule is the reference rule flipped on its disagreement support. -/
theorem flipOn_disagreementSupport_eq
    {U : Type v} [Fintype U] (reference rule : U → Bool) :
    flipOn reference (disagreementSupport reference rule) = rule := by
  classical
  funext u
  by_cases hmem : u ∈ disagreementSupport reference rule
  · have hne : rule u ≠ reference u := by
      simpa using
        (mem_disagreementSupport
          (reference := reference) (rule := rule) (u := u)).1 hmem
    have hflip : Bool.not (reference u) = rule u := by
      cases href : reference u <;> cases hrule : rule u <;> simp [href, hrule] at hne ⊢
    change (if u ∈ disagreementSupport reference rule then Bool.not (reference u) else reference u) =
      rule u
    rw [if_pos hmem]
    exact hflip
  · have hnot : ¬ rule u ≠ reference u := by
      simpa using
        mt
          ((mem_disagreementSupport
            (reference := reference) (rule := rule) (u := u)).2) hmem
    have heq : rule u = reference u := not_not.mp hnot
    change (if u ∈ disagreementSupport reference rule then Bool.not (reference u) else reference u) =
      rule u
    rw [if_neg hmem]
    exact heq.symm

/-- Boolean rules within `radius` point changes of a reference rule. -/
noncomputable def disagreementBall
    {U : Type v} [Fintype U] (reference : U → Bool) (radius : ℕ) :
    Finset (U → Bool) := by
  classical
  exact (Finset.univ : Finset (U → Bool)).filter
    (fun rule => (disagreementSupport reference rule).card ≤ radius)

@[simp] theorem mem_disagreementBall
    {U : Type v} [Fintype U] {reference rule : U → Bool} {radius : ℕ} :
    rule ∈ disagreementBall reference radius ↔
      (disagreementSupport reference rule).card ≤ radius := by
  classical
  simp [disagreementBall]

/-- A Hamming ball is covered by flipping the center on one small subset of
inputs. -/
theorem disagreementBall_subset_image_smallSubsets
    {U : Type v} [Fintype U] (reference : U → Bool) (radius : ℕ) :
    disagreementBall reference radius ⊆
      (smallSubsets U radius).image (flipOn reference) := by
  classical
  intro rule hrule
  have hsmall :
      disagreementSupport reference rule ∈ smallSubsets U radius := by
    simpa using
      (mem_disagreementBall
        (reference := reference) (rule := rule) (radius := radius)).1 hrule
  rw [← flipOn_disagreementSupport_eq reference rule]
  exact Finset.mem_image.mpr ⟨disagreementSupport reference rule, hsmall, rfl⟩

/-- The number of Boolean rules within `radius` point changes of one reference
rule is at most the number of input subsets of size at most `radius`. -/
theorem disagreementBall_card_le_smallSubsets_card
    {U : Type v} [Fintype U] (reference : U → Bool) (radius : ℕ) :
    (disagreementBall reference radius).card ≤ (smallSubsets U radius).card := by
  classical
  calc
    (disagreementBall reference radius).card
        ≤ ((smallSubsets U radius).image (flipOn reference)).card :=
          Finset.card_le_card
            (disagreementBall_subset_image_smallSubsets reference radius)
    _ ≤ (smallSubsets U radius).card := Finset.card_image_le

/-- The union of radius-`radius` Hamming balls around a structured fallback
family. -/
noncomputable def fallbackFamilyRadiusCover
    {FallbackIndex U : Type v} [Fintype FallbackIndex] [Fintype U]
    (fallback : FallbackIndex → U → Bool) (radius : ℕ) :
    Finset (U → Bool) := by
  classical
  exact (Finset.univ : Finset FallbackIndex).biUnion
    (fun code => disagreementBall (fallback code) radius)

@[simp] theorem mem_fallbackFamilyRadiusCover
    {FallbackIndex U : Type v} [Fintype FallbackIndex] [Fintype U]
    {fallback : FallbackIndex → U → Bool} {radius : ℕ} {rule : U → Bool} :
    rule ∈ fallbackFamilyRadiusCover fallback radius ↔
      ∃ code : FallbackIndex,
        (disagreementSupport (fallback code) rule).card ≤ radius := by
  classical
  simp [fallbackFamilyRadiusCover, disagreementBall]

/-- If the radius reaches the whole finite input alphabet, every Boolean rule
lies in the radius cover of any nonempty fallback family.  The membership form
keeps the theorem independent of extra function-space `Fintype` synthesis. -/
theorem mem_fallbackFamilyRadiusCover_of_nonempty_of_card_le_radius
    {FallbackIndex U : Type v} [Fintype FallbackIndex] [Nonempty FallbackIndex]
    [Fintype U] (fallback : FallbackIndex → U → Bool) {radius : ℕ}
    (hcard : Fintype.card U ≤ radius) (rule : U → Bool) :
    rule ∈ fallbackFamilyRadiusCover fallback radius := by
  classical
  exact
    (mem_fallbackFamilyRadiusCover
      (fallback := fallback) (radius := radius) (rule := rule)).2
      ⟨Classical.arbitrary FallbackIndex,
        (disagreementSupport_card_le_card
          (fallback (Classical.arbitrary FallbackIndex)) rule).trans hcard⟩

/-- A finite fallback family plus radius-`radius` sparse overrides covers at
most `#FallbackIndex` times the number of small input subsets. -/
theorem fallbackFamilyRadiusCover_card_le
    {FallbackIndex U : Type v} [Fintype FallbackIndex] [Fintype U]
    (fallback : FallbackIndex → U → Bool) (radius : ℕ) :
    (fallbackFamilyRadiusCover fallback radius).card ≤
      Fintype.card FallbackIndex * (smallSubsets U radius).card := by
  classical
  simpa [fallbackFamilyRadiusCover] using
    Finset.card_biUnion_le_card_mul
      (s := (Finset.univ : Finset FallbackIndex))
      (f := fun code => disagreementBall (fallback code) radius)
      (n := (smallSubsets U radius).card)
      (by
        intro code _hcode
        exact disagreementBall_card_le_smallSubsets_card (fallback code) radius)

/-- If a finite fallback-family radius cover is the whole Boolean rule cube,
then the number of fallback codes times the number of sparse supports must be
at least the full Boolean truth-table count. -/
theorem boolClassifierSpace_card_le_code_mul_smallSubsets_card_of_radiusCover_eq_univ
    {FallbackIndex U : Type v} [Fintype FallbackIndex] [Fintype U] [DecidableEq U]
    (fallback : FallbackIndex → U → Bool) {radius : ℕ}
    (hcover :
      fallbackFamilyRadiusCover fallback radius =
        (Finset.univ : Finset (U → Bool))) :
    2 ^ Fintype.card U ≤
      Fintype.card FallbackIndex * (smallSubsets U radius).card := by
  classical
  calc
    2 ^ Fintype.card U
        = (fallbackFamilyRadiusCover fallback radius).card := by
          rw [hcover]
          simp [Finset.card_univ, card_boolClassifierSpace U]
    _ ≤ Fintype.card FallbackIndex * (smallSubsets U radius).card :=
          fallbackFamilyRadiusCover_card_le fallback radius

/-- If the radius-cover union is smaller than the full Boolean rule space, some
rule is farther than `radius` from every fallback code. -/
theorem exists_rule_forall_radius_lt_disagreementSupport_card_of_radiusCover_card_lt
    {FallbackIndex U : Type v} [Fintype FallbackIndex] [Fintype U]
    (fallback : FallbackIndex → U → Bool) {radius : ℕ}
    (hcard : (fallbackFamilyRadiusCover fallback radius).card < 2 ^ Fintype.card U) :
    ∃ rule : U → Bool,
      ∀ code : FallbackIndex,
        radius < (disagreementSupport (fallback code) rule).card := by
  classical
  have hspace :
      (Finset.univ : Finset (U → Bool)).card = 2 ^ Fintype.card U := by
    simp [Finset.card_univ, card_boolClassifierSpace U]
  have hlt :
      (fallbackFamilyRadiusCover fallback radius).card <
        (Finset.univ : Finset (U → Bool)).card := by
    simpa [hspace] using hcard
  rcases Finset.exists_mem_notMem_of_card_lt_card hlt with ⟨rule, _hrule, hnotmem⟩
  refine ⟨rule, ?_⟩
  intro code
  exact Nat.lt_of_not_ge (by
    intro hle
    exact hnotmem
      ((mem_fallbackFamilyRadiusCover
        (fallback := fallback) (radius := radius) (rule := rule)).2
          ⟨code, hle⟩))

/-- Product-count form of the previous obstruction: if fallback codes times
small override supports are fewer than all Boolean rules, one target rule is
outside every radius ball. -/
theorem exists_rule_forall_radius_lt_disagreementSupport_card_of_code_mul_smallSubsets_card_lt
    {FallbackIndex U : Type v} [Fintype FallbackIndex] [Fintype U]
    (fallback : FallbackIndex → U → Bool) {radius : ℕ}
    (hcard :
      Fintype.card FallbackIndex * (smallSubsets U radius).card <
        2 ^ Fintype.card U) :
    ∃ rule : U → Bool,
      ∀ code : FallbackIndex,
        radius < (disagreementSupport (fallback code) rule).card :=
  exists_rule_forall_radius_lt_disagreementSupport_card_of_radiusCover_card_lt
    fallback
    (lt_of_le_of_lt (fallbackFamilyRadiusCover_card_le fallback radius) hcard)

end PluginSampleMajority

/-- The actual switched-local interface induced by sample-level plug-in
majority, with indices restricted to samples of length at most `sampleBound`. -/
noncomputable def boundedSamplePluginMajorityActualSwitchedLocalInterface
    (Z : Type v) (k sampleBound : ℕ) :
    ActualSwitchedLocalInterface
      Z k
      (BoundedSampleIndex (ExactVisiblePostSwitchSurface Z k) sampleBound)
      (ExactVisiblePostSwitchSurface Z k) where
  zOf := fun u => u.z
  aOf := fun _ u => u.a
  bOf := fun u => u.b
  localRule := fun sample u =>
    letI := Classical.decEq (ExactVisiblePostSwitchSurface Z k)
    PluginSampleMajority.predict sample.1 u
  output := fun sample u =>
    letI := Classical.decEq (ExactVisiblePostSwitchSurface Z k)
    PluginSampleMajority.predict sample.1 u
  output_eq_local := by
    intro sample u
    rfl

/-- If the sample bound reaches the alphabet size, every Boolean lookup table
is still realized by the graph sample of that lookup table. -/
theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_realizes_every_lookupTable
    {Z : Type v} {k sampleBound : ℕ} [Fintype Z]
    (hbound : Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound)
    (rule : ExactVisibleRule Z k) :
    ∃ sample,
      (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).predictorFamily.predict
          sample =
        rule := by
  classical
  refine ⟨⟨PluginSampleMajority.graphSample rule, ?_⟩, ?_⟩
  · rw [PluginSampleMajority.length_graphSample]
    exact hbound
  · funext u
    simp [boundedSamplePluginMajorityActualSwitchedLocalInterface,
      ActualSwitchedLocalInterface.predictorFamily]

/-- Bounded sample-level plug-in majority remains surjective once the bound is
at least the exact-visible alphabet size. -/
theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_surjective
    (Z : Type v) (k sampleBound : ℕ) [Fintype Z]
    (hbound : Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound) :
    Function.Surjective
      (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).predictorFamily.predict := by
  intro rule
  exact
    boundedSamplePluginMajorityActualSwitchedLocalInterface_realizes_every_lookupTable
      (Z := Z) (k := k) (sampleBound := sampleBound) hbound rule

/-- If the sample bound is below the exact-visible alphabet size, bounded
sample-level plug-in majority is not surjective: every bounded sample omits an
input, where the tie-breaking majority predicts `true`, so the all-false rule is
not realizable. -/
theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_not_surjective_of_sampleBound_lt_surfaceCard
    {Z : Type v} {k sampleBound : ℕ} [Fintype Z]
    (hbound : sampleBound < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).predictorFamily.predict := by
  classical
  intro hsurj
  let allFalse : ExactVisibleRule Z k := fun _ => false
  rcases hsurj allFalse with ⟨sample, hsample⟩
  have hlen : sample.1.length < Fintype.card (ExactVisiblePostSwitchSurface Z k) :=
    lt_of_le_of_lt sample.2 hbound
  rcases PluginSampleMajority.exists_true_prediction_of_length_lt_card
      (sample := sample.1) hlen with ⟨u, hu⟩
  have hfalse :
      (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).predictorFamily.predict
          sample u = false := by
    simpa [allFalse] using congrFun hsample u
  rw [boundedSamplePluginMajorityActualSwitchedLocalInterface,
    ActualSwitchedLocalInterface.predictorFamily] at hfalse
  simp [hu] at hfalse

/-- Exact surjectivity dichotomy for bounded sample-level plug-in majority: it
is full-rule expressive exactly when the sample bound reaches the exact-visible
alphabet size. -/
theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_surjective_iff
    (Z : Type v) (k sampleBound : ℕ) [Fintype Z] :
    Function.Surjective
        (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).predictorFamily.predict ↔
      Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound := by
  constructor
  · intro hsurj
    by_contra hnot
    exact
      boundedSamplePluginMajorityActualSwitchedLocalInterface_not_surjective_of_sampleBound_lt_surfaceCard
        (Z := Z) (k := k) (sampleBound := sampleBound)
        (Nat.lt_of_not_ge hnot) hsurj
  · intro hbound
    exact boundedSamplePluginMajorityActualSwitchedLocalInterface_surjective
      Z k sampleBound hbound

/-- Any predictor selected by bounded sample-level plug-in majority is false on
at most `sampleBound` exact-visible inputs. -/
theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_falseSupport_card_le_sampleBound
    {Z : Type v} {k sampleBound : ℕ} [Fintype Z]
    (sample :
      BoundedSampleIndex (ExactVisiblePostSwitchSurface Z k) sampleBound) :
    (PluginSampleMajority.falseSupport
      (fun u : ExactVisiblePostSwitchSurface Z k =>
        (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).predictorFamily.predict
          sample u)).card ≤ sampleBound := by
  classical
  simpa [boundedSamplePluginMajorityActualSwitchedLocalInterface,
    ActualSwitchedLocalInterface.predictorFamily] using
    PluginSampleMajority.falseSupport_predict_card_le_bound
      (sample := sample)

/-- Consequently, any target rule whose false-support is larger than the sample
bound is not realized by the bounded sample-level plug-in majority endpoint. -/
theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_not_realizes_rule_of_sampleBound_lt_falseSupport_card
    {Z : Type v} {k sampleBound : ℕ} [Fintype Z]
    (rule : ExactVisibleRule Z k)
    (hcard : sampleBound < (PluginSampleMajority.falseSupport rule).card) :
    ¬ ∃ sample,
      (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).predictorFamily.predict
          sample =
        rule := by
  classical
  rintro ⟨sample, hsample⟩
  have hle :=
    boundedSamplePluginMajorityActualSwitchedLocalInterface_falseSupport_card_le_sampleBound
      (Z := Z) (k := k) (sampleBound := sampleBound) sample
  have hsupport :
      PluginSampleMajority.falseSupport
          (fun u : ExactVisiblePostSwitchSurface Z k =>
            (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).predictorFamily.predict
              sample u) =
        PluginSampleMajority.falseSupport rule := by
    ext u
    have hu :
        (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).localRule
            sample u =
          rule u := by
      simpa [ActualSwitchedLocalInterface.predictorFamily_predict] using congrFun hsample u
    simp [PluginSampleMajority.falseSupport, hu]
  rw [hsupport] at hle
  exact (not_lt_of_ge hle) hcard

/-- The actual switched-local interface induced by bounded sample-level
plug-in majority with an explicit tie-breaking default. -/
noncomputable def boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface
    (default : Bool) (Z : Type v) (k sampleBound : ℕ) :
    ActualSwitchedLocalInterface
      Z k
      (BoundedSampleIndex (ExactVisiblePostSwitchSurface Z k) sampleBound)
      (ExactVisiblePostSwitchSurface Z k) where
  zOf := fun u => u.z
  aOf := fun _ u => u.a
  bOf := fun u => u.b
  localRule := fun sample u =>
    letI := Classical.decEq (ExactVisiblePostSwitchSurface Z k)
    PluginSampleMajority.predictWithDefault default sample.1 u
  output := fun sample u =>
    letI := Classical.decEq (ExactVisiblePostSwitchSurface Z k)
    PluginSampleMajority.predictWithDefault default sample.1 u
  output_eq_local := by
    intro sample u
    rfl

/-- If the sample bound reaches the alphabet size, explicit-default bounded
sample-level plug-in majority realizes every Boolean lookup table. -/
theorem boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface_realizes_every_lookupTable
    {Z : Type v} {k sampleBound : ℕ} [Fintype Z]
    (default : Bool)
    (hbound : Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound)
    (rule : ExactVisibleRule Z k) :
    ∃ sample,
      (boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface
          default Z k sampleBound).predictorFamily.predict sample =
        rule := by
  classical
  refine ⟨⟨PluginSampleMajority.graphSample rule, ?_⟩, ?_⟩
  · rw [PluginSampleMajority.length_graphSample]
    exact hbound
  · funext u
    simp [boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface,
      ActualSwitchedLocalInterface.predictorFamily]

/-- Explicit-default bounded sample-level plug-in majority is surjective once
the sample bound reaches the exact-visible alphabet size. -/
theorem boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface_surjective
    (default : Bool) (Z : Type v) (k sampleBound : ℕ) [Fintype Z]
    (hbound : Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound) :
    Function.Surjective
      (boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface
        default Z k sampleBound).predictorFamily.predict := by
  intro rule
  exact
    boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface_realizes_every_lookupTable
      (Z := Z) (k := k) (sampleBound := sampleBound) default hbound rule

/-- Any predictor selected by explicit-default bounded sample-level plug-in
majority differs from the default on at most `sampleBound` exact-visible inputs. -/
theorem boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface_nondefaultSupport_card_le_sampleBound
    {Z : Type v} {k sampleBound : ℕ} [Fintype Z]
    (default : Bool)
    (sample :
      BoundedSampleIndex (ExactVisiblePostSwitchSurface Z k) sampleBound) :
    (PluginSampleMajority.nondefaultSupport default
      (fun u : ExactVisiblePostSwitchSurface Z k =>
        (boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface
          default Z k sampleBound).predictorFamily.predict sample u)).card ≤ sampleBound := by
  classical
  simpa [boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface,
    ActualSwitchedLocalInterface.predictorFamily] using
    PluginSampleMajority.nondefaultSupport_predictWithDefault_card_le_bound
      default (sample := sample)

/-- Consequently, any target rule whose nondefault support is larger than the
sample bound is not realized by the explicit-default bounded sample-level
plug-in majority endpoint. -/
theorem boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface_not_realizes_rule_of_sampleBound_lt_nondefaultSupport_card
    {Z : Type v} {k sampleBound : ℕ} [Fintype Z]
    (default : Bool) (rule : ExactVisibleRule Z k)
    (hcard : sampleBound < (PluginSampleMajority.nondefaultSupport default rule).card) :
    ¬ ∃ sample,
      (boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface
          default Z k sampleBound).predictorFamily.predict sample =
        rule := by
  classical
  rintro ⟨sample, hsample⟩
  have hle :=
    boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface_nondefaultSupport_card_le_sampleBound
      (Z := Z) (k := k) (sampleBound := sampleBound) default sample
  have hsupport :
      PluginSampleMajority.nondefaultSupport default
          (fun u : ExactVisiblePostSwitchSurface Z k =>
            (boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface
              default Z k sampleBound).predictorFamily.predict sample u) =
        PluginSampleMajority.nondefaultSupport default rule := by
    ext u
    have hu :
        (boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface
            default Z k sampleBound).localRule sample u =
          rule u := by
      simpa [ActualSwitchedLocalInterface.predictorFamily_predict] using congrFun hsample u
    simp [PluginSampleMajority.nondefaultSupport, hu]
  rw [hsupport] at hle
  exact (not_lt_of_ge hle) hcard

/-- Below the exact-visible alphabet size, no explicit-default bounded sample
endpoint is surjective: the rule constantly opposite to the default has
nondefault support equal to the whole surface. -/
theorem boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface_not_surjective_of_sampleBound_lt_surfaceCard
    {Z : Type v} {k sampleBound : ℕ} [Fintype Z]
    (default : Bool)
    (hbound : sampleBound < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface
        default Z k sampleBound).predictorFamily.predict := by
  classical
  intro hsurj
  let antiDefault : ExactVisibleRule Z k := fun _ => !default
  have hcard :
      sampleBound < (PluginSampleMajority.nondefaultSupport default antiDefault).card := by
    simpa [antiDefault, PluginSampleMajority.nondefaultSupport_const_not_card] using hbound
  exact
    (boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface_not_realizes_rule_of_sampleBound_lt_nondefaultSupport_card
      (Z := Z) (k := k) (sampleBound := sampleBound) default antiDefault hcard)
      (hsurj antiDefault)

/-- Exact surjectivity dichotomy for explicit-default bounded sample-level
plug-in majority: the tie-breaking convention does not change the threshold. -/
theorem boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface_surjective_iff
    (default : Bool) (Z : Type v) (k sampleBound : ℕ) [Fintype Z] :
    Function.Surjective
        (boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface
          default Z k sampleBound).predictorFamily.predict ↔
      Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound := by
  constructor
  · intro hsurj
    by_contra hnot
    exact
      boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface_not_surjective_of_sampleBound_lt_surfaceCard
        (Z := Z) (k := k) (sampleBound := sampleBound)
        default (Nat.lt_of_not_ge hnot) hsurj
  · intro hbound
    exact boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface_surjective
      default Z k sampleBound hbound

/-- The actual switched-local interface induced by bounded sample-level
plug-in majority with an input-dependent fallback for ties.  The index carries a
fallback function over the whole exact-visible surface. -/
noncomputable def boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
    (Z : Type v) (k sampleBound : ℕ) :
    ActualSwitchedLocalInterface
      Z k
      (BoundedSampleFallbackIndex (ExactVisiblePostSwitchSurface Z k) sampleBound)
      (ExactVisiblePostSwitchSurface Z k) where
  zOf := fun u => u.z
  aOf := fun _ u => u.a
  bOf := fun u => u.b
  localRule := fun index u =>
    letI := Classical.decEq (ExactVisiblePostSwitchSurface Z k)
    PluginSampleMajority.predictWithFallback index.1 index.2.1 u
  output := fun index u =>
    letI := Classical.decEq (ExactVisiblePostSwitchSurface Z k)
    PluginSampleMajority.predictWithFallback index.1 index.2.1 u
  output_eq_local := by
    intro index u
    rfl

/-- With an input-dependent fallback, the empty sample already realizes the
fallback rule exactly. -/
theorem boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface_emptySample_predict
    {Z : Type v} {k sampleBound : ℕ}
    (fallback : ExactVisibleRule Z k) :
    (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
        Z k sampleBound).predictorFamily.predict
        (fallback, ⟨[], by simp⟩) =
      fallback := by
  classical
  funext u
  simp [boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface,
    ActualSwitchedLocalInterface.predictorFamily]

/-- Therefore an input-dependent fallback is already full-rule expressive for
every sample bound, including zero. -/
theorem boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface_realizes_every_lookupTable
    {Z : Type v} {k sampleBound : ℕ}
    (rule : ExactVisibleRule Z k) :
    ∃ index,
      (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
          Z k sampleBound).predictorFamily.predict index =
        rule := by
  exact ⟨(rule, ⟨[], by simp⟩),
    boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface_emptySample_predict
      (Z := Z) (k := k) (sampleBound := sampleBound) rule⟩

/-- Bounded sample-level plug-in majority with an input-dependent fallback is
surjective onto all exact-visible Boolean rules independently of the sample
bound. -/
theorem boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface_surjective
    (Z : Type v) (k sampleBound : ℕ) :
    Function.Surjective
      (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
        Z k sampleBound).predictorFamily.predict := by
  intro rule
  exact
    boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface_realizes_every_lookupTable
      (Z := Z) (k := k) (sampleBound := sampleBound) rule

/-- Consequently the fallback-rule endpoint has no small finite predictor
cover below the exact visible truth-table budget.  The obstruction no longer
depends on the sample bound, because the fallback is already a full rule. -/
theorem boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface_not_finitePredictorCover_of_lt_surfaceCard
    {Z : Type v} {k s sampleBound : ℕ} [Fintype Z]
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
        Z k sampleBound).predictorFamily.FinitePredictorCover (2 ^ s) := by
  intro hcover
  have hsmall :
      ExactVisibleCompressionTarget
        (Z := Z) (k := k)
        (Index := BoundedSampleFallbackIndex
          (ExactVisiblePostSwitchSurface Z k) sampleBound)
        (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
          Z k sampleBound).predictorFamily s :=
    (exactVisibleCompressionTarget_iff_finitePredictorCover
      (Z := Z) (k := k) (s := s)
      (Index := BoundedSampleFallbackIndex
        (ExactVisiblePostSwitchSurface Z k) sampleBound)
      (G := (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
        Z k sampleBound).predictorFamily)).2
      hcover
  exact
    (not_exactVisibleCompressionTarget_of_surjective_predict
      (Z := Z) (k := k) (s := s)
      (Index := BoundedSampleFallbackIndex
        (ExactVisiblePostSwitchSurface Z k) sampleBound)
      (G := (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
        Z k sampleBound).predictorFamily)
      hs
      (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface_surjective
        Z k sampleBound)) hsmall

/-- The same side-channel endpoint cannot supply the clocked finite-learning
payload below the exact visible truth-table budget. -/
theorem boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface_not_clockedKpolyFiniteLearningPayload_of_lt_surfaceCard
    {Z : Type v} {k s sampleBound clock : ℕ} [Fintype Z]
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ClockedKpolyFiniteLearningPayload
        (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
          Z k sampleBound).predictorFamily s clock := by
  intro hpayload
  have hsmall :
      ExactVisibleCompressionTarget
        (Z := Z) (k := k)
        (Index := BoundedSampleFallbackIndex
          (ExactVisiblePostSwitchSurface Z k) sampleBound)
        (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
          Z k sampleBound).predictorFamily s :=
    exactVisibleCompressionTarget_of_clockedKpolyFiniteLearningPayload
      (Z := Z) (k := k) (s := s) (clock := clock)
      (Index := BoundedSampleFallbackIndex
        (ExactVisiblePostSwitchSurface Z k) sampleBound)
      hpayload
  exact
    (not_exactVisibleCompressionTarget_of_surjective_predict
      (Z := Z) (k := k) (s := s)
      (Index := BoundedSampleFallbackIndex
        (ExactVisiblePostSwitchSurface Z k) sampleBound)
      (G := (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
        Z k sampleBound).predictorFamily)
      hs
      (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface_surjective
        Z k sampleBound)) hsmall

/-- The actual switched-local interface induced by bounded sample-level
plug-in majority with a fallback chosen from a structured fallback family. -/
noncomputable def boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
    (FallbackIndex : Type v)
    (Z : Type v) (k sampleBound : ℕ)
    (fallback : FallbackIndex → ExactVisibleRule Z k) :
    ActualSwitchedLocalInterface
      Z k
      (BoundedSampleFallbackFamilyIndex
        FallbackIndex (ExactVisiblePostSwitchSurface Z k) sampleBound)
      (ExactVisiblePostSwitchSurface Z k) where
  zOf := fun u => u.z
  aOf := fun _ u => u.a
  bOf := fun u => u.b
  localRule := fun index u =>
    letI := Classical.decEq (ExactVisiblePostSwitchSurface Z k)
    PluginSampleMajority.predictWithFallback (fallback index.1) index.2.1 u
  output := fun index u =>
    letI := Classical.decEq (ExactVisiblePostSwitchSurface Z k)
    PluginSampleMajority.predictWithFallback (fallback index.1) index.2.1 u
  output_eq_local := by
    intro index u
    rfl

/-- The structured fallback-family endpoint with the fallback family indexed by
`fallbackBits` Boolean bits.  The internal index is universe-lifted so the
construction remains available for arbitrary finite hidden alphabets `Z`. -/
noncomputable def boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
    (Z : Type v) (k sampleBound fallbackBits : ℕ)
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k) :
    ActualSwitchedLocalInterface
      Z k
      (BoundedSampleFallbackFamilyIndex
        (ULift.{v} (BitCode fallbackBits))
        (ExactVisiblePostSwitchSurface Z k) sampleBound)
      (ExactVisiblePostSwitchSurface Z k) :=
  boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
    (ULift.{v} (BitCode fallbackBits)) Z k sampleBound
    (fun code => fallback code.down)

/-- For a structured fallback family, bounded samples can only change the
chosen fallback rule on sampled exact-visible inputs. -/
theorem boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_disagreementSupport_card_le_sampleBound
    {FallbackIndex : Type v} {Z : Type v} {k sampleBound : ℕ} [Fintype Z]
    (fallback : FallbackIndex → ExactVisibleRule Z k)
    (index :
      BoundedSampleFallbackFamilyIndex
        FallbackIndex (ExactVisiblePostSwitchSurface Z k) sampleBound) :
    (PluginSampleMajority.disagreementSupport (fallback index.1)
      (fun u : ExactVisiblePostSwitchSurface Z k =>
        (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k sampleBound fallback).predictorFamily.predict index u)).card ≤
        sampleBound := by
  classical
  simpa [boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface,
    ActualSwitchedLocalInterface.predictorFamily] using
    PluginSampleMajority.disagreementSupport_predictWithFallback_card_le_bound
      (fallback index.1) (sample := index.2)

/-- If the structured fallback family selects a rule and the bounded sample is
empty, the plug-in predictor is exactly that fallback rule. -/
theorem boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_emptySample_predict
    {FallbackIndex : Type v} {Z : Type v} {k sampleBound : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k) (code : FallbackIndex) :
    (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
        FallbackIndex Z k sampleBound fallback).predictorFamily.predict
        (code, ⟨[], by simp⟩) =
      fallback code := by
  classical
  funext u
  simp [boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface,
    ActualSwitchedLocalInterface.predictorFamily]

/-- A bounded-sample structured fallback endpoint is already full-rule
expressive whenever the fallback family itself is full-rule expressive.  The
sample bound is irrelevant: the empty sample leaves the selected fallback
unchanged. -/
theorem boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_surjective_of_fallback_surjective
    {FallbackIndex : Type v} {Z : Type v} {k sampleBound : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k)
    (hsurj : Function.Surjective fallback) :
    Function.Surjective
      (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
        FallbackIndex Z k sampleBound fallback).predictorFamily.predict := by
  classical
  intro rule
  rcases hsurj rule with ⟨code, hcode⟩
  refine ⟨(code, ⟨[], by simp⟩), ?_⟩
  simpa [hcode] using
    boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_emptySample_predict
      (Z := Z) (k := k) (sampleBound := sampleBound) fallback code

/-- With zero sampled overrides, a structured fallback endpoint is full-rule
expressive exactly when the fallback family itself is full-rule expressive. -/
theorem boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_zeroSample_surjective_iff_fallback_surjective
    {FallbackIndex : Type v} {Z : Type v} {k : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k) :
    Function.Surjective
        (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k 0 fallback).predictorFamily.predict ↔
      Function.Surjective fallback := by
  classical
  constructor
  · intro hsurj rule
    rcases hsurj rule with ⟨index, hindex⟩
    refine ⟨index.1, ?_⟩
    have hsample : index.2.1 = [] := by
      apply List.eq_nil_of_length_eq_zero
      exact Nat.eq_zero_of_le_zero index.2.2
    funext u
    have hu := congrFun hindex u
    simpa [boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface,
      ActualSwitchedLocalInterface.predictorFamily, hsample] using hu
  · intro hfallback
    exact
      boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_surjective_of_fallback_surjective
        (Z := Z) (k := k) (sampleBound := 0) fallback hfallback

/-- Thus a structured fallback family can realize a target rule only if some
fallback code is within `sampleBound` point changes of that target. -/
theorem boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_not_realizes_rule_of_forall_sampleBound_lt_disagreementSupport_card
    {FallbackIndex : Type v} {Z : Type v} {k sampleBound : ℕ} [Fintype Z]
    (fallback : FallbackIndex → ExactVisibleRule Z k)
    (rule : ExactVisibleRule Z k)
    (hcard :
      ∀ code : FallbackIndex,
        sampleBound <
          (PluginSampleMajority.disagreementSupport (fallback code) rule).card) :
    ¬ ∃ index,
      (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k sampleBound fallback).predictorFamily.predict index =
        rule := by
  classical
  rintro ⟨index, hindex⟩
  have hle :=
    boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_disagreementSupport_card_le_sampleBound
      (Z := Z) (k := k) (sampleBound := sampleBound) fallback index
  have hsupport :
      PluginSampleMajority.disagreementSupport (fallback index.1)
          (fun u : ExactVisiblePostSwitchSurface Z k =>
            (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
              FallbackIndex Z k sampleBound fallback).predictorFamily.predict index u) =
        PluginSampleMajority.disagreementSupport (fallback index.1) rule := by
    ext u
    have hu :
        (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
            FallbackIndex Z k sampleBound fallback).localRule index u =
          rule u := by
      simpa [ActualSwitchedLocalInterface.predictorFamily_predict] using congrFun hindex u
    simp [PluginSampleMajority.disagreementSupport, hu]
  rw [hsupport] at hle
  exact (not_lt_of_ge hle) (hcard index.1)

/-- Every rule in the fallback-family radius cover is realized by sampling
exactly the points where it differs from the chosen fallback rule. -/
theorem boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_realizes_rule_of_mem_fallbackFamilyRadiusCover
    {FallbackIndex : Type v} {Z : Type v} {k sampleBound : ℕ}
    [Fintype FallbackIndex] [Fintype Z]
    (fallback : FallbackIndex → ExactVisibleRule Z k)
    (rule : ExactVisibleRule Z k)
    (hmem :
      rule ∈ PluginSampleMajority.fallbackFamilyRadiusCover fallback sampleBound) :
    ∃ index,
      (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k sampleBound fallback).predictorFamily.predict index =
        rule := by
  classical
  rcases
      (PluginSampleMajority.mem_fallbackFamilyRadiusCover
        (fallback := fallback) (radius := sampleBound) (rule := rule)).1 hmem with
    ⟨code, hcard⟩
  let support :=
    PluginSampleMajority.disagreementSupport (fallback code) rule
  let sample := PluginSampleMajority.supportSample support rule
  have hlen : sample.length ≤ sampleBound := by
    simpa [sample, support] using hcard
  refine ⟨⟨code, ⟨sample, hlen⟩⟩, ?_⟩
  have hoff : ∀ u : ExactVisiblePostSwitchSurface Z k,
      u ∉ support → fallback code u = rule u := by
    intro u hu
    have hnot : ¬ rule u ≠ fallback code u := by
      simpa [support] using
        mt
          ((PluginSampleMajority.mem_disagreementSupport
            (reference := fallback code) (rule := rule) (u := u)).2) hu
    exact (not_not.mp hnot).symm
  have hpredict :
      PluginSampleMajority.predictWithFallback (fallback code) sample = rule := by
    simpa [sample] using
      PluginSampleMajority.predictWithFallback_supportSample_eq_of_eq_off_support
        (fallback code) rule support hoff
  funext u
  simpa [boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface,
    ActualSwitchedLocalInterface.predictorFamily] using congrFun hpredict u

/-- A structured fallback family plus bounded samples realizes precisely the
finite Hamming-radius cover around its fallback codes. -/
theorem boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_realizes_rule_iff_mem_fallbackFamilyRadiusCover
    {FallbackIndex : Type v} {Z : Type v} {k sampleBound : ℕ}
    [Fintype FallbackIndex] [Fintype Z]
    (fallback : FallbackIndex → ExactVisibleRule Z k)
    (rule : ExactVisibleRule Z k) :
    (∃ index,
      (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k sampleBound fallback).predictorFamily.predict index =
        rule) ↔
      rule ∈ PluginSampleMajority.fallbackFamilyRadiusCover fallback sampleBound := by
  classical
  constructor
  · rintro ⟨index, hindex⟩
    have hle :=
      boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_disagreementSupport_card_le_sampleBound
        (Z := Z) (k := k) (sampleBound := sampleBound) fallback index
    have hsupport :
        PluginSampleMajority.disagreementSupport (fallback index.1)
            (fun u : ExactVisiblePostSwitchSurface Z k =>
              (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
                FallbackIndex Z k sampleBound fallback).predictorFamily.predict index u) =
          PluginSampleMajority.disagreementSupport (fallback index.1) rule := by
      ext u
      have hu :
          (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
              FallbackIndex Z k sampleBound fallback).localRule index u =
            rule u := by
        simpa [ActualSwitchedLocalInterface.predictorFamily_predict] using congrFun hindex u
      simp [PluginSampleMajority.disagreementSupport, hu]
    rw [hsupport] at hle
    exact
      (PluginSampleMajority.mem_fallbackFamilyRadiusCover
        (fallback := fallback) (radius := sampleBound) (rule := rule)).2
        ⟨index.1, hle⟩
  · intro hmem
    exact
      boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_realizes_rule_of_mem_fallbackFamilyRadiusCover
        (Z := Z) (k := k) (sampleBound := sampleBound)
        fallback rule hmem

/-- A structured fallback family plus bounded samples is surjective precisely
when its finite Hamming-radius cover is the full exact-visible rule space. -/
theorem boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_surjective_iff_fallbackFamilyRadiusCover_eq_univ
    {FallbackIndex : Type v} {Z : Type v} {k sampleBound : ℕ}
    [Fintype FallbackIndex] [Fintype Z]
    (fallback : FallbackIndex → ExactVisibleRule Z k) :
    Function.Surjective
        (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k sampleBound fallback).predictorFamily.predict ↔
      PluginSampleMajority.fallbackFamilyRadiusCover fallback sampleBound =
        (Finset.univ : Finset (ExactVisibleRule Z k)) := by
  classical
  constructor
  · intro hsurj
    apply Finset.eq_univ_iff_forall.mpr
    intro rule
    rcases hsurj rule with ⟨index, hindex⟩
    exact
      (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_realizes_rule_iff_mem_fallbackFamilyRadiusCover
        (Z := Z) (k := k) (sampleBound := sampleBound) fallback rule).1
        ⟨index, hindex⟩
  · intro hcover rule
    have hmem :
        rule ∈ PluginSampleMajority.fallbackFamilyRadiusCover fallback sampleBound := by
      simp [hcover]
    exact
      (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_realizes_rule_iff_mem_fallbackFamilyRadiusCover
        (Z := Z) (k := k) (sampleBound := sampleBound) fallback rule).2
        hmem

/-- Once the sample radius reaches the exact-visible alphabet size, any
nonempty structured fallback family becomes full-rule expressive.  This is the
sharp full-radius repair side of the bounded-sample Hamming-cover boundary. -/
theorem boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_surjective_of_nonempty_of_surfaceCard_le_sampleBound
    {FallbackIndex : Type v} {Z : Type v} {k sampleBound : ℕ}
    [Fintype FallbackIndex] [Nonempty FallbackIndex] [Fintype Z]
    (fallback : FallbackIndex → ExactVisibleRule Z k)
    (hbound : Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound) :
    Function.Surjective
        (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k sampleBound fallback).predictorFamily.predict := by
  classical
  intro rule
  exact
    (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_realizes_rule_iff_mem_fallbackFamilyRadiusCover
      (Z := Z) (k := k) (sampleBound := sampleBound) fallback rule).2
      (PluginSampleMajority.mem_fallbackFamilyRadiusCover_of_nonempty_of_card_le_radius
        (fallback := fallback) hbound rule)

/-- Pointwise form of the exact repair condition: surjectivity requires and is
required by every exact-visible rule lying within `sampleBound` of some
fallback code. -/
theorem boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_surjective_iff_forall_exists_disagreementSupport_card_le_sampleBound
    {FallbackIndex : Type v} {Z : Type v} {k sampleBound : ℕ}
    [Fintype FallbackIndex] [Fintype Z]
    (fallback : FallbackIndex → ExactVisibleRule Z k) :
    Function.Surjective
        (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k sampleBound fallback).predictorFamily.predict ↔
      ∀ rule : ExactVisibleRule Z k,
        ∃ code : FallbackIndex,
          (PluginSampleMajority.disagreementSupport (fallback code) rule).card ≤
            sampleBound := by
  classical
  rw [
    boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_surjective_iff_fallbackFamilyRadiusCover_eq_univ
      (Z := Z) (k := k) (sampleBound := sampleBound) fallback]
  constructor
  · intro hcover rule
    have hmem :
        rule ∈ PluginSampleMajority.fallbackFamilyRadiusCover fallback sampleBound := by
      simp [hcover]
    exact
      (PluginSampleMajority.mem_fallbackFamilyRadiusCover
        (fallback := fallback) (radius := sampleBound) (rule := rule)).1 hmem
  · intro hforall
    apply Finset.eq_univ_iff_forall.mpr
    intro rule
    exact
      (PluginSampleMajority.mem_fallbackFamilyRadiusCover
        (fallback := fallback) (radius := sampleBound) (rule := rule)).2
        (hforall rule)

/-- A structured fallback family plus bounded samples has an explicit finite
predictor-image cover: one radius-`sampleBound` Hamming ball around each
fallback code. -/
theorem boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_finitePredictorCover
    {FallbackIndex : Type v} {Z : Type v} {k sampleBound : ℕ}
    [Fintype FallbackIndex] [Fintype Z]
    (fallback : FallbackIndex → ExactVisibleRule Z k) :
    (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
        FallbackIndex Z k sampleBound fallback).predictorFamily.FinitePredictorCover
      (Fintype.card FallbackIndex *
        (PluginSampleMajority.smallSubsets
          (ExactVisiblePostSwitchSurface Z k) sampleBound).card) := by
  classical
  refine
    ⟨PluginSampleMajority.fallbackFamilyRadiusCover fallback sampleBound, ?_, ?_⟩
  · intro index
    have hle :=
      boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_disagreementSupport_card_le_sampleBound
        (Z := Z) (k := k) (sampleBound := sampleBound) fallback index
    exact
      (PluginSampleMajority.mem_fallbackFamilyRadiusCover
        (fallback := fallback) (radius := sampleBound)
        (rule :=
          (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
            FallbackIndex Z k sampleBound fallback).predictorFamily.predict index)).2
        ⟨index.1, hle⟩
  · exact PluginSampleMajority.fallbackFamilyRadiusCover_card_le
      fallback sampleBound

/-- If the fallback-code count times the number of possible sparse override
supports is below the full Boolean truth-table space, then the structured
fallback-family endpoint cannot realize every exact-visible rule. -/
theorem boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_code_mul_smallSubsets_card_lt_boolClassifierSpace
    {FallbackIndex : Type v} {Z : Type v} {k sampleBound : ℕ}
    [Fintype FallbackIndex] [Fintype Z]
    (fallback : FallbackIndex → ExactVisibleRule Z k)
    (hcard :
      Fintype.card FallbackIndex *
          (PluginSampleMajority.smallSubsets
            (ExactVisiblePostSwitchSurface Z k) sampleBound).card <
        2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
        FallbackIndex Z k sampleBound fallback).predictorFamily.predict := by
  classical
  rcases
      PluginSampleMajority.exists_rule_forall_radius_lt_disagreementSupport_card_of_code_mul_smallSubsets_card_lt
        (U := ExactVisiblePostSwitchSurface Z k)
        fallback hcard with
    ⟨rule, hfar⟩
  intro hsurj
  rcases hsurj rule with ⟨index, hindex⟩
  exact
    boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_not_realizes_rule_of_forall_sampleBound_lt_disagreementSupport_card
      (Z := Z) (k := k) (sampleBound := sampleBound)
      fallback rule hfar ⟨index, hindex⟩

/-- Direct quantitative repair burden: if the structured fallback-family
endpoint is full-rule expressive, then fallback codes times sparse override
supports must be at least the full exact-visible Boolean truth-table count. -/
theorem boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_boolClassifierSpace_card_le_code_mul_smallSubsets_card_of_surjective
    {FallbackIndex : Type v} {Z : Type v} {k sampleBound : ℕ}
    [Fintype FallbackIndex] [Fintype Z]
    (fallback : FallbackIndex → ExactVisibleRule Z k)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k sampleBound fallback).predictorFamily.predict) :
    2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      Fintype.card FallbackIndex *
        (PluginSampleMajority.smallSubsets
          (ExactVisiblePostSwitchSurface Z k) sampleBound).card := by
  classical
  have hcover :=
    (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_surjective_iff_fallbackFamilyRadiusCover_eq_univ
      (Z := Z) (k := k) (sampleBound := sampleBound) fallback).1 hsurj
  exact
    PluginSampleMajority.boolClassifierSpace_card_le_code_mul_smallSubsets_card_of_radiusCover_eq_univ
      (fallback := fallback) (radius := sampleBound) hcover

/-- Bit-budget repair burden: if the structured fallback-family endpoint with
`fallbackBits`-bit fallback codes is full-rule expressive, then those codes
times the sparse override supports must cover the full exact-visible Boolean
truth-table cube. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_boolClassifierSpace_card_le_bitCode_mul_smallSubsets_card_of_surjective
    {Z : Type v} {k sampleBound fallbackBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k sampleBound fallbackBits fallback).predictorFamily.predict) :
    2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      2 ^ fallbackBits *
        (PluginSampleMajority.smallSubsets
          (ExactVisiblePostSwitchSurface Z k) sampleBound).card := by
  classical
  have hlower :
      2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
        Fintype.card (ULift.{v} (BitCode fallbackBits)) *
          (PluginSampleMajority.smallSubsets
            (ExactVisiblePostSwitchSurface Z k) sampleBound).card :=
    boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_boolClassifierSpace_card_le_code_mul_smallSubsets_card_of_surjective
      (FallbackIndex := ULift.{v} (BitCode fallbackBits))
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fun code => fallback code.down) hsurj
  simpa [boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface,
    card_bitCode] using hlower

/-- Bit-coded fallback families are already full-rule expressive once the
sample bound reaches the exact-visible alphabet size.  Extra fallback bits are
irrelevant at this full-radius endpoint. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_surjective_of_surfaceCard_le_sampleBound
    {Z : Type v} {k sampleBound fallbackBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hbound : Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound) :
    Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound fallbackBits fallback).predictorFamily.predict := by
  classical
  exact
    boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_surjective_of_nonempty_of_surfaceCard_le_sampleBound
      (FallbackIndex := ULift.{v} (BitCode fallbackBits))
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fun code => fallback code.down) hbound

/-- If the bit-code budget times sparse override supports is still below the
exact-visible Boolean truth-table cube, then the `fallbackBits`-bit structured
fallback endpoint cannot be full-rule expressive. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_bitCode_mul_smallSubsets_card_lt_boolClassifierSpace
    {Z : Type v} {k sampleBound fallbackBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hcard :
      2 ^ fallbackBits *
          (PluginSampleMajority.smallSubsets
            (ExactVisiblePostSwitchSurface Z k) sampleBound).card <
        2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound fallbackBits fallback).predictorFamily.predict := by
  classical
  apply
    boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_code_mul_smallSubsets_card_lt_boolClassifierSpace
      (FallbackIndex := ULift.{v} (BitCode fallbackBits))
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fun code => fallback code.down)
  simpa [card_bitCode] using hcard

/-- Binomial-prefix form of the bit-budget repair burden: full-rule
expressivity forces the fallback code count times the exact radius-`sampleBound`
Hamming-ball support count to cover the Boolean rule cube. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_boolClassifierSpace_card_le_bitCode_mul_sum_choose_of_surjective
    {Z : Type v} {k sampleBound fallbackBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k sampleBound fallbackBits fallback).predictorFamily.predict) :
    2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      2 ^ fallbackBits *
        ∑ i ∈ Finset.range (sampleBound + 1),
          (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose i := by
  classical
  simpa [PluginSampleMajority.card_smallSubsets_eq_sum_range_choose] using
    boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_boolClassifierSpace_card_le_bitCode_mul_smallSubsets_card_of_surjective
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) fallback hsurj

/-- If the fallback bits times the binomial-prefix Hamming-ball support count
is still below the Boolean rule cube, then the bit-coded structured fallback
endpoint cannot be full-rule expressive. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_bitCode_mul_sum_choose_lt_boolClassifierSpace
    {Z : Type v} {k sampleBound fallbackBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hcard :
      2 ^ fallbackBits *
          (∑ i ∈ Finset.range (sampleBound + 1),
            (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose i) <
        2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound fallbackBits fallback).predictorFamily.predict := by
  classical
  apply
    boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_bitCode_mul_smallSubsets_card_lt_boolClassifierSpace
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) fallback
  simpa [PluginSampleMajority.card_smallSubsets_eq_sum_range_choose] using hcard

/-- Exact binomial-prefix bit-budget form: if the radius-`sampleBound`
Hamming-ball support count fits into `overheadBits` bits, then full-rule
expressivity forces the total fallback-plus-overhead bit budget to reach the
exact-visible input alphabet size. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_fallbackBits_add_overheadBits_ge_surfaceCard_of_sumChooseEnvelope_le_twoPow_surjective
    {Z : Type v} {k sampleBound fallbackBits overheadBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (henvelope :
      (∑ i ∈ Finset.range (sampleBound + 1),
        (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose i) ≤
        2 ^ overheadBits)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k sampleBound fallbackBits fallback).predictorFamily.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      fallbackBits + overheadBits := by
  classical
  have hbinom :=
    boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_boolClassifierSpace_card_le_bitCode_mul_sum_choose_of_surjective
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) fallback hsurj
  have hprod :
      2 ^ fallbackBits *
          (∑ i ∈ Finset.range (sampleBound + 1),
            (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose i) ≤
        2 ^ (fallbackBits + overheadBits) := by
    calc
      2 ^ fallbackBits *
          (∑ i ∈ Finset.range (sampleBound + 1),
            (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose i) ≤
          2 ^ fallbackBits * 2 ^ overheadBits :=
        Nat.mul_le_mul_left (2 ^ fallbackBits) henvelope
      _ = 2 ^ (fallbackBits + overheadBits) := by
        rw [← pow_add]
  exact (Nat.pow_le_pow_iff_right Nat.one_lt_two).1 (hbinom.trans hprod)

/-- Strict bit-deficit form for the exact binomial-prefix Hamming-ball support
envelope. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_sumChooseEnvelope_le_twoPow_and_fallbackBits_add_overheadBits_lt_surfaceCard
    {Z : Type v} {k sampleBound fallbackBits overheadBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (henvelope :
      (∑ i ∈ Finset.range (sampleBound + 1),
        (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose i) ≤
        2 ^ overheadBits)
    (hbits :
      fallbackBits + overheadBits <
        Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound fallbackBits fallback).predictorFamily.predict := by
  classical
  apply
    boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_bitCode_mul_sum_choose_lt_boolClassifierSpace
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) fallback
  have hprod :
      2 ^ fallbackBits *
          (∑ i ∈ Finset.range (sampleBound + 1),
            (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose i) ≤
        2 ^ (fallbackBits + overheadBits) := by
    calc
      2 ^ fallbackBits *
          (∑ i ∈ Finset.range (sampleBound + 1),
            (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose i) ≤
          2 ^ fallbackBits * 2 ^ overheadBits :=
        Nat.mul_le_mul_left (2 ^ fallbackBits) henvelope
      _ = 2 ^ (fallbackBits + overheadBits) := by
        rw [← pow_add]
  exact hprod.trans_lt ((Nat.pow_lt_pow_iff_right Nat.one_lt_two).2 hbits)

/-- With zero fallback bits, bounded sampled overrides below the exact-visible
alphabet size cannot be full-rule expressive: one Hamming ball of proper radius
is a strict subset of the Boolean rule cube. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_zeroFallbackBits_of_sampleBound_lt_surfaceCard
    {Z : Type v} {k sampleBound : ℕ} [Fintype Z]
    (fallback : BitCode 0 → ExactVisibleRule Z k)
    (hbound :
      sampleBound < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound 0 fallback).predictorFamily.predict := by
  classical
  apply
    boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_bitCode_mul_sum_choose_lt_boolClassifierSpace
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := 0) fallback
  simpa using
    PluginSampleMajority.sum_range_choose_lt_twoPow_of_lt
      (n := Fintype.card (ExactVisiblePostSwitchSurface Z k))
      (radius := sampleBound) hbound

/-- Exact zero-fallback boundary: with no fallback bits, the bit-coded
bounded-sample fallback endpoint is full-rule expressive exactly when the sample
bound reaches the exact-visible alphabet size. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_zeroFallbackBits_surjective_iff_surfaceCard_le_sampleBound
    {Z : Type v} {k sampleBound : ℕ} [Fintype Z]
    (fallback : BitCode 0 → ExactVisibleRule Z k) :
    Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k sampleBound 0 fallback).predictorFamily.predict ↔
      Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound := by
  classical
  constructor
  · intro hsurj
    by_contra hnot
    have hlt :
        sampleBound < Fintype.card (ExactVisiblePostSwitchSurface Z k) :=
      Nat.lt_of_not_ge hnot
    exact
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_zeroFallbackBits_of_sampleBound_lt_surfaceCard
        (Z := Z) (k := k) (sampleBound := sampleBound)
        fallback hlt) hsurj
  · intro hbound
    exact
      boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_surjective_of_surfaceCard_le_sampleBound
        (Z := Z) (k := k) (sampleBound := sampleBound)
        (fallbackBits := 0) fallback hbound

/-- Coarse polynomial form of the bit-budget repair burden: full-rule
expressivity forces the fallback code count times a polynomial upper envelope on
the sparse override support count to cover the Boolean rule cube. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_boolClassifierSpace_card_le_bitCode_mul_sampleBound_succ_mul_surfaceCard_succ_pow_of_surjective
    {Z : Type v} {k sampleBound fallbackBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k sampleBound fallbackBits fallback).predictorFamily.predict) :
    2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      2 ^ fallbackBits *
        ((sampleBound + 1) *
          (Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1) ^ sampleBound) := by
  classical
  have hbinom :=
    boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_boolClassifierSpace_card_le_bitCode_mul_sum_choose_of_surjective
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) fallback hsurj
  have hsum :
      (∑ i ∈ Finset.range (sampleBound + 1),
        (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose i) ≤
        (sampleBound + 1) *
          (Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1) ^ sampleBound :=
    PluginSampleMajority.sum_range_choose_le_succ_mul_succ_pow
      (Fintype.card (ExactVisiblePostSwitchSurface Z k)) sampleBound
  exact hbinom.trans (Nat.mul_le_mul_left (2 ^ fallbackBits) hsum)

/-- If even the coarse polynomial fallback-bit envelope is still below the full
Boolean rule cube, then the bit-coded structured fallback endpoint cannot be
full-rule expressive. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_bitCode_mul_sampleBound_succ_mul_surfaceCard_succ_pow_lt_boolClassifierSpace
    {Z : Type v} {k sampleBound fallbackBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hcard :
      2 ^ fallbackBits *
          ((sampleBound + 1) *
            (Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1) ^ sampleBound) <
        2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound fallbackBits fallback).predictorFamily.predict := by
  classical
  apply
    boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_bitCode_mul_sum_choose_lt_boolClassifierSpace
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) fallback
  have hsum :
      (∑ i ∈ Finset.range (sampleBound + 1),
        (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose i) ≤
        (sampleBound + 1) *
          (Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1) ^ sampleBound :=
    PluginSampleMajority.sum_range_choose_le_succ_mul_succ_pow
      (Fintype.card (ExactVisiblePostSwitchSurface Z k)) sampleBound
  exact (Nat.mul_le_mul_left (2 ^ fallbackBits) hsum).trans_lt hcard

/-- If the coarse polynomial sparse-override envelope fits into
`overheadBits` bits, then full-rule expressivity forces the total fallback-plus-
override bit budget to reach the exact-visible input alphabet size. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_fallbackBits_add_overheadBits_ge_surfaceCard_of_polynomialEnvelope_le_twoPow_surjective
    {Z : Type v} {k sampleBound fallbackBits overheadBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (henvelope :
      (sampleBound + 1) *
          (Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1) ^ sampleBound ≤
        2 ^ overheadBits)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k sampleBound fallbackBits fallback).predictorFamily.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      fallbackBits + overheadBits := by
  classical
  have hpoly :=
    boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_boolClassifierSpace_card_le_bitCode_mul_sampleBound_succ_mul_surfaceCard_succ_pow_of_surjective
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) fallback hsurj
  have hprod :
      2 ^ fallbackBits *
          ((sampleBound + 1) *
            (Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1) ^ sampleBound) ≤
        2 ^ (fallbackBits + overheadBits) := by
    calc
      2 ^ fallbackBits *
          ((sampleBound + 1) *
            (Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1) ^ sampleBound) ≤
          2 ^ fallbackBits * 2 ^ overheadBits :=
        Nat.mul_le_mul_left (2 ^ fallbackBits) henvelope
      _ = 2 ^ (fallbackBits + overheadBits) := by
        rw [← pow_add]
  exact (Nat.pow_le_pow_iff_right Nat.one_lt_two).1 (hpoly.trans hprod)

/-- If the coarse polynomial sparse-override envelope fits into
`overheadBits` bits, but fallback bits plus those overhead bits are still below
the exact-visible alphabet size, then the bit-coded structured fallback endpoint
cannot be full-rule expressive. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_polynomialEnvelope_le_twoPow_and_fallbackBits_add_overheadBits_lt_surfaceCard
    {Z : Type v} {k sampleBound fallbackBits overheadBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (henvelope :
      (sampleBound + 1) *
          (Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1) ^ sampleBound ≤
        2 ^ overheadBits)
    (hbits :
      fallbackBits + overheadBits <
        Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound fallbackBits fallback).predictorFamily.predict := by
  classical
  apply
    boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_bitCode_mul_sampleBound_succ_mul_surfaceCard_succ_pow_lt_boolClassifierSpace
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) fallback
  have hprod :
      2 ^ fallbackBits *
          ((sampleBound + 1) *
            (Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1) ^ sampleBound) ≤
        2 ^ (fallbackBits + overheadBits) := by
    calc
      2 ^ fallbackBits *
          ((sampleBound + 1) *
            (Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1) ^ sampleBound) ≤
          2 ^ fallbackBits * 2 ^ overheadBits :=
        Nat.mul_le_mul_left (2 ^ fallbackBits) henvelope
      _ = 2 ^ (fallbackBits + overheadBits) := by
        rw [← pow_add]
  exact hprod.trans_lt ((Nat.pow_lt_pow_iff_right Nat.one_lt_two).2 hbits)

/-- If the radius multiplier and exact-visible alphabet base have explicit
bit bounds, then full-rule expressivity forces the fallback bits plus those
certified envelope bits to reach the exact-visible alphabet size. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_fallbackBits_add_radiusBits_add_baseBits_mul_sampleBound_ge_surfaceCard_of_envelopeFactors_le_twoPow_surjective
    {Z : Type v} {k sampleBound fallbackBits radiusBits baseBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hradius : sampleBound + 1 ≤ 2 ^ radiusBits)
    (hbase :
      Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1 ≤
        2 ^ baseBits)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k sampleBound fallbackBits fallback).predictorFamily.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      fallbackBits + radiusBits + baseBits * sampleBound := by
  classical
  have henvelope :
      (sampleBound + 1) *
          (Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1) ^ sampleBound ≤
        2 ^ (radiusBits + baseBits * sampleBound) :=
    PluginSampleMajority.succ_mul_succ_pow_le_twoPow_add_mul
      (n := Fintype.card (ExactVisiblePostSwitchSurface Z k))
      (radius := sampleBound) hradius hbase
  have htotal :=
    boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_fallbackBits_add_overheadBits_ge_surfaceCard_of_polynomialEnvelope_le_twoPow_surjective
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits)
      (overheadBits := radiusBits + baseBits * sampleBound)
      fallback henvelope hsurj
  simpa [Nat.add_assoc] using htotal

/-- Strict total-bit deficit form using explicit bit bounds for both factors of
the sparse-override polynomial envelope. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_envelopeFactors_le_twoPow_and_fallbackBits_add_radiusBits_add_baseBits_mul_sampleBound_lt_surfaceCard
    {Z : Type v} {k sampleBound fallbackBits radiusBits baseBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hradius : sampleBound + 1 ≤ 2 ^ radiusBits)
    (hbase :
      Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1 ≤
        2 ^ baseBits)
    (hbits :
      fallbackBits + radiusBits + baseBits * sampleBound <
        Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound fallbackBits fallback).predictorFamily.predict := by
  classical
  have henvelope :
      (sampleBound + 1) *
          (Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1) ^ sampleBound ≤
        2 ^ (radiusBits + baseBits * sampleBound) :=
    PluginSampleMajority.succ_mul_succ_pow_le_twoPow_add_mul
      (n := Fintype.card (ExactVisiblePostSwitchSurface Z k))
      (radius := sampleBound) hradius hbase
  apply
    boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_polynomialEnvelope_le_twoPow_and_fallbackBits_add_overheadBits_lt_surfaceCard
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits)
      (overheadBits := radiusBits + baseBits * sampleBound)
      fallback henvelope
  simpa [Nat.add_assoc] using hbits

/-- If the sample bound itself fits in `radiusBits` bits, full-rule
expressivity still has to pay one more bit for the successor factor
`sampleBound + 1` in the sparse-override envelope. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_fallbackBits_add_radiusBits_succ_add_baseBits_mul_sampleBound_ge_surfaceCard_of_sampleBound_le_twoPow_and_base_le_twoPow_surjective
    {Z : Type v} {k sampleBound fallbackBits radiusBits baseBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hradius : sampleBound ≤ 2 ^ radiusBits)
    (hbase :
      Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1 ≤
        2 ^ baseBits)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k sampleBound fallbackBits fallback).predictorFamily.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      fallbackBits + (radiusBits + 1) + baseBits * sampleBound := by
  exact
    boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_fallbackBits_add_radiusBits_add_baseBits_mul_sampleBound_ge_surfaceCard_of_envelopeFactors_le_twoPow_surjective
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) (radiusBits := radiusBits + 1) (baseBits := baseBits)
      fallback
      (PluginSampleMajority.succ_le_twoPow_succ_of_le_twoPow hradius)
      hbase hsurj

/-- Strict deficit form for the common encoding claim `sampleBound ≤
2 ^ radiusBits`: the extra successor bit is explicit, so it cannot be hidden in
the sparse-override repair budget. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_sampleBound_le_twoPow_and_base_le_twoPow_and_fallbackBits_add_radiusBits_succ_add_baseBits_mul_sampleBound_lt_surfaceCard
    {Z : Type v} {k sampleBound fallbackBits radiusBits baseBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hradius : sampleBound ≤ 2 ^ radiusBits)
    (hbase :
      Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1 ≤
        2 ^ baseBits)
    (hbits :
      fallbackBits + (radiusBits + 1) + baseBits * sampleBound <
        Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound fallbackBits fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_envelopeFactors_le_twoPow_and_fallbackBits_add_radiusBits_add_baseBits_mul_sampleBound_lt_surfaceCard
    (Z := Z) (k := k) (sampleBound := sampleBound)
    (fallbackBits := fallbackBits) (radiusBits := radiusBits + 1) (baseBits := baseBits)
    fallback
    (PluginSampleMajority.succ_le_twoPow_succ_of_le_twoPow hradius)
    hbase hbits

/-- If the route bounds the sample size and the exact-visible alphabet size
themselves by powers of two, full-rule expressivity still has to pay one extra
bit for each successor appearing in the sparse-override envelope:
`sampleBound + 1` and `surfaceCard + 1`. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_fallbackBits_add_radiusBits_succ_add_baseBits_succ_mul_sampleBound_ge_surfaceCard_of_sampleBound_le_twoPow_and_surfaceCard_le_twoPow_surjective
    {Z : Type v} {k sampleBound fallbackBits radiusBits baseBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hradius : sampleBound ≤ 2 ^ radiusBits)
    (hbase :
      Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
        2 ^ baseBits)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k sampleBound fallbackBits fallback).predictorFamily.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      fallbackBits + (radiusBits + 1) + (baseBits + 1) * sampleBound := by
  exact
    boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_fallbackBits_add_radiusBits_add_baseBits_mul_sampleBound_ge_surfaceCard_of_envelopeFactors_le_twoPow_surjective
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) (radiusBits := radiusBits + 1) (baseBits := baseBits + 1)
      fallback
      (PluginSampleMajority.succ_le_twoPow_succ_of_le_twoPow hradius)
      (PluginSampleMajority.succ_le_twoPow_succ_of_le_twoPow hbase)
      hsurj

/-- Strict deficit form when both route-level bit bounds are stated for the
raw sample bound and raw surface-cardinality, rather than their successors. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_sampleBound_le_twoPow_and_surfaceCard_le_twoPow_and_fallbackBits_add_radiusBits_succ_add_baseBits_succ_mul_sampleBound_lt_surfaceCard
    {Z : Type v} {k sampleBound fallbackBits radiusBits baseBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hradius : sampleBound ≤ 2 ^ radiusBits)
    (hbase :
      Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
        2 ^ baseBits)
    (hbits :
      fallbackBits + (radiusBits + 1) + (baseBits + 1) * sampleBound <
        Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound fallbackBits fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_envelopeFactors_le_twoPow_and_fallbackBits_add_radiusBits_add_baseBits_mul_sampleBound_lt_surfaceCard
    (Z := Z) (k := k) (sampleBound := sampleBound)
    (fallbackBits := fallbackBits) (radiusBits := radiusBits + 1) (baseBits := baseBits + 1)
    fallback
    (PluginSampleMajority.succ_le_twoPow_succ_of_le_twoPow hradius)
    (PluginSampleMajority.succ_le_twoPow_succ_of_le_twoPow hbase)
    hbits

/-- With no sampled overrides, a bit-coded structured fallback family can be
full-rule expressive only if its bit budget reaches the exact-visible input
alphabet size. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_fallbackBits_ge_surfaceCard_of_zeroSample_surjective
    {Z : Type v} {k fallbackBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 0 fallbackBits fallback).predictorFamily.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ fallbackBits := by
  classical
  have hpow :
      2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
        2 ^ fallbackBits :=
    by
      simpa using
        boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_boolClassifierSpace_card_le_bitCode_mul_smallSubsets_card_of_surjective
          (Z := Z) (k := k) (sampleBound := 0)
          (fallbackBits := fallbackBits) fallback hsurj
  exact (Nat.pow_le_pow_iff_right Nat.one_lt_two).1 hpow

/-- Equivalently, if the zero-sample structured fallback bit budget is below
the exact-visible input alphabet size, the endpoint cannot be full-rule
expressive. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_zeroSample_of_fallbackBits_lt_surfaceCard
    {Z : Type v} {k fallbackBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hbits : fallbackBits < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 0 fallbackBits fallback).predictorFamily.predict := by
  classical
  apply
    boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_bitCode_mul_smallSubsets_card_lt_boolClassifierSpace
      (Z := Z) (k := k) (sampleBound := 0)
      (fallbackBits := fallbackBits) fallback
  simpa using (Nat.pow_lt_pow_iff_right Nat.one_lt_two).2 hbits

/-- With zero sampled overrides, the bit-coded fallback endpoint is surjective
exactly when the bit-coded fallback decoder itself is surjective. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_zeroSample_surjective_iff_fallback_surjective
    {Z : Type v} {k fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k) :
    Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 0 fallbackBits fallback).predictorFamily.predict ↔
      Function.Surjective fallback := by
  classical
  constructor
  · intro hsurj rule
    have hfallback :
        Function.Surjective
          (fun code : ULift.{v} (BitCode fallbackBits) => fallback code.down) :=
      (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_zeroSample_surjective_iff_fallback_surjective
        (FallbackIndex := ULift.{v} (BitCode fallbackBits))
        (Z := Z) (k := k)
        (fallback := fun code : ULift.{v} (BitCode fallbackBits) => fallback code.down)).1
        (by
          simpa [boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface]
            using hsurj)
    rcases hfallback rule with ⟨code, hcode⟩
    exact ⟨code.down, hcode⟩
  · intro hfallback
    have hwrapped :
        Function.Surjective
          (fun code : ULift.{v} (BitCode fallbackBits) => fallback code.down) := by
      intro rule
      rcases hfallback rule with ⟨code, hcode⟩
      exact ⟨ULift.up code, hcode⟩
    simpa [boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface] using
      (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_zeroSample_surjective_iff_fallback_surjective
        (FallbackIndex := ULift.{v} (BitCode fallbackBits))
        (Z := Z) (k := k)
        (fallback := fun code : ULift.{v} (BitCode fallbackBits) => fallback code.down)).2
        hwrapped

/-- At the full exact-visible truth-table bit budget, the canonical decoder is
full-rule expressive for every sample bound.  The proof uses the empty sample,
so bounded sampled overrides do not contribute to expressivity here. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_surjective_exactVisibleRuleDecode
    {Z : Type v} {k sampleBound : ℕ} [Fintype Z] :
    Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound (Fintype.card (ExactVisiblePostSwitchSurface Z k))
        (exactVisibleRuleDecode (Z := Z) (k := k))).predictorFamily.predict := by
  classical
  simpa [boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface] using
    (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_surjective_of_fallback_surjective
      (FallbackIndex :=
        ULift.{v} (BitCode (Fintype.card (ExactVisiblePostSwitchSurface Z k))))
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallback := fun code =>
        exactVisibleRuleDecode (Z := Z) (k := k) code.down)
      (by
        intro rule
        refine ⟨ULift.up (exactVisibleRuleEncode (Z := Z) (k := k) rule), ?_⟩
        simpa using exactVisibleRuleDecode_encode (Z := Z) (k := k) rule))

/-- The zero-sample lower bound is sharp for the canonical full truth-table
fallback decoder: with exactly one bit per exact-visible input, the empty
sample leaves the decoded fallback rule unchanged. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_surjective_zeroSample_exactVisibleRuleDecode
    {Z : Type v} {k : ℕ} [Fintype Z] :
    Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 0 (Fintype.card (ExactVisiblePostSwitchSurface Z k))
        (exactVisibleRuleDecode (Z := Z) (k := k))).predictorFamily.predict := by
  exact
    boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_surjective_exactVisibleRuleDecode
      (Z := Z) (k := k) (sampleBound := 0)

/-- With one sampled override, full-rule expressivity of a bit-coded structured
fallback family forces the explicit multiplier `surfaceCard + 1`: either no
override is used, or exactly one exact-visible input is overwritten. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_boolClassifierSpace_card_le_bitCode_mul_surfaceCard_succ_of_oneSample_surjective
    {Z : Type v} {k fallbackBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 1 fallbackBits fallback).predictorFamily.predict) :
    2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      2 ^ fallbackBits *
        (Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1) := by
  classical
  simpa using
    boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_boolClassifierSpace_card_le_bitCode_mul_smallSubsets_card_of_surjective
      (Z := Z) (k := k) (sampleBound := 1)
      (fallbackBits := fallbackBits) fallback hsurj

/-- Consequently, if the one-sample bit-code budget times `surfaceCard + 1` is
still below the full exact-visible Boolean rule cube, the endpoint cannot be
full-rule expressive. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_oneSample_of_bitCode_mul_surfaceCard_succ_lt_boolClassifierSpace
    {Z : Type v} {k fallbackBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hcard :
      2 ^ fallbackBits *
          (Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1) <
        2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 1 fallbackBits fallback).predictorFamily.predict := by
  classical
  apply
    boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_bitCode_mul_smallSubsets_card_lt_boolClassifierSpace
      (Z := Z) (k := k) (sampleBound := 1)
      (fallbackBits := fallbackBits) fallback
  simpa using hcard

/-- With two sampled overrides, full-rule expressivity of a bit-coded
structured fallback family forces the explicit quadratic sparse-support
multiplier `1 + surfaceCard + choose surfaceCard 2`. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_boolClassifierSpace_card_le_bitCode_mul_one_add_surfaceCard_add_choose_two_of_twoSample_surjective
    {Z : Type v} {k fallbackBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 2 fallbackBits fallback).predictorFamily.predict) :
    2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      2 ^ fallbackBits *
        (1 + Fintype.card (ExactVisiblePostSwitchSurface Z k) +
          (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose 2) := by
  classical
  simpa [PluginSampleMajority.card_smallSubsets_two, Nat.add_assoc] using
    boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_boolClassifierSpace_card_le_bitCode_mul_smallSubsets_card_of_surjective
      (Z := Z) (k := k) (sampleBound := 2)
      (fallbackBits := fallbackBits) fallback hsurj

/-- Strict product-deficit form for the exact two-sample quadratic sparse
support envelope. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_twoSample_of_bitCode_mul_one_add_surfaceCard_add_choose_two_lt_boolClassifierSpace
    {Z : Type v} {k fallbackBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hcard :
      2 ^ fallbackBits *
          (1 + Fintype.card (ExactVisiblePostSwitchSurface Z k) +
            (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose 2) <
        2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 2 fallbackBits fallback).predictorFamily.predict := by
  classical
  apply
    boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_bitCode_mul_smallSubsets_card_lt_boolClassifierSpace
      (Z := Z) (k := k) (sampleBound := 2)
      (fallbackBits := fallbackBits) fallback
  simpa [PluginSampleMajority.card_smallSubsets_two, Nat.add_assoc] using hcard

/-- If the exact two-sample quadratic sparse-support envelope fits into
`overheadBits` bits, full-rule expressivity forces the total
fallback-plus-overhead bit budget to reach the exact-visible alphabet size. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_fallbackBits_add_overheadBits_ge_surfaceCard_of_twoSample_quadraticEnvelope_le_twoPow_surjective
    {Z : Type v} {k fallbackBits overheadBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (henvelope :
      1 + Fintype.card (ExactVisiblePostSwitchSurface Z k) +
          (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose 2 ≤
        2 ^ overheadBits)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 2 fallbackBits fallback).predictorFamily.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      fallbackBits + overheadBits := by
  classical
  have hquad :=
    boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_boolClassifierSpace_card_le_bitCode_mul_one_add_surfaceCard_add_choose_two_of_twoSample_surjective
      (Z := Z) (k := k) (fallbackBits := fallbackBits) fallback hsurj
  have hprod :
      2 ^ fallbackBits *
          (1 + Fintype.card (ExactVisiblePostSwitchSurface Z k) +
            (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose 2) ≤
        2 ^ (fallbackBits + overheadBits) := by
    calc
      2 ^ fallbackBits *
          (1 + Fintype.card (ExactVisiblePostSwitchSurface Z k) +
            (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose 2) ≤
          2 ^ fallbackBits * 2 ^ overheadBits :=
        Nat.mul_le_mul_left (2 ^ fallbackBits) henvelope
      _ = 2 ^ (fallbackBits + overheadBits) := by
        rw [← pow_add]
  exact (Nat.pow_le_pow_iff_right Nat.one_lt_two).1 (hquad.trans hprod)

/-- Strict bit-deficit form for the exact two-sample quadratic sparse-support
envelope. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_twoSample_of_quadraticEnvelope_le_twoPow_and_fallbackBits_add_overheadBits_lt_surfaceCard
    {Z : Type v} {k fallbackBits overheadBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (henvelope :
      1 + Fintype.card (ExactVisiblePostSwitchSurface Z k) +
          (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose 2 ≤
        2 ^ overheadBits)
    (hbits :
      fallbackBits + overheadBits <
        Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 2 fallbackBits fallback).predictorFamily.predict := by
  classical
  apply
    boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_twoSample_of_bitCode_mul_one_add_surfaceCard_add_choose_two_lt_boolClassifierSpace
      (Z := Z) (k := k) (fallbackBits := fallbackBits) fallback
  have hprod :
      2 ^ fallbackBits *
          (1 + Fintype.card (ExactVisiblePostSwitchSurface Z k) +
            (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose 2) ≤
        2 ^ (fallbackBits + overheadBits) := by
    calc
      2 ^ fallbackBits *
          (1 + Fintype.card (ExactVisiblePostSwitchSurface Z k) +
            (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose 2) ≤
          2 ^ fallbackBits * 2 ^ overheadBits :=
        Nat.mul_le_mul_left (2 ^ fallbackBits) henvelope
      _ = 2 ^ (fallbackBits + overheadBits) := by
        rw [← pow_add]
  exact hprod.trans_lt ((Nat.pow_lt_pow_iff_right Nat.one_lt_two).2 hbits)

/-- One sampled override has the exact sparse-support count `surfaceCard + 1`.
Thus, if that successor count fits in `baseBits` bits, full-rule expressivity
forces `fallbackBits + baseBits` to reach the exact-visible alphabet size. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_fallbackBits_add_baseBits_ge_surfaceCard_of_oneSample_surfaceCard_succ_le_twoPow_surjective
    {Z : Type v} {k fallbackBits baseBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hbase :
      Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1 ≤
        2 ^ baseBits)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 1 fallbackBits fallback).predictorFamily.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      fallbackBits + baseBits := by
  classical
  have hcover :=
    boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_boolClassifierSpace_card_le_bitCode_mul_surfaceCard_succ_of_oneSample_surjective
      (Z := Z) (k := k) (fallbackBits := fallbackBits) fallback hsurj
  have hprod :
      2 ^ fallbackBits *
          (Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1) ≤
        2 ^ (fallbackBits + baseBits) := by
    calc
      2 ^ fallbackBits *
          (Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1) ≤
          2 ^ fallbackBits * 2 ^ baseBits :=
        Nat.mul_le_mul_left (2 ^ fallbackBits) hbase
      _ = 2 ^ (fallbackBits + baseBits) := by
        rw [← pow_add]
  exact (Nat.pow_le_pow_iff_right Nat.one_lt_two).1 (hcover.trans hprod)

/-- Strict bit-deficit form for the exact one-sample successor-count envelope. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_oneSample_of_surfaceCard_succ_le_twoPow_and_fallbackBits_add_baseBits_lt_surfaceCard
    {Z : Type v} {k fallbackBits baseBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hbase :
      Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1 ≤
        2 ^ baseBits)
    (hbits :
      fallbackBits + baseBits <
        Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 1 fallbackBits fallback).predictorFamily.predict := by
  classical
  apply
    boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_oneSample_of_bitCode_mul_surfaceCard_succ_lt_boolClassifierSpace
      (Z := Z) (k := k) (fallbackBits := fallbackBits) fallback
  have hprod :
      2 ^ fallbackBits *
          (Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1) ≤
        2 ^ (fallbackBits + baseBits) := by
    calc
      2 ^ fallbackBits *
          (Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1) ≤
          2 ^ fallbackBits * 2 ^ baseBits :=
        Nat.mul_le_mul_left (2 ^ fallbackBits) hbase
      _ = 2 ^ (fallbackBits + baseBits) := by
        rw [← pow_add]
  exact hprod.trans_lt ((Nat.pow_lt_pow_iff_right Nat.one_lt_two).2 hbits)

/-- If the route states only a raw bit bound on `surfaceCard`, the one-sample
successor count still costs one additional bit. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_fallbackBits_add_baseBits_succ_ge_surfaceCard_of_oneSample_surfaceCard_le_twoPow_surjective
    {Z : Type v} {k fallbackBits baseBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hbase :
      Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
        2 ^ baseBits)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 1 fallbackBits fallback).predictorFamily.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      fallbackBits + (baseBits + 1) :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_fallbackBits_add_baseBits_ge_surfaceCard_of_oneSample_surfaceCard_succ_le_twoPow_surjective
    (Z := Z) (k := k) (fallbackBits := fallbackBits) (baseBits := baseBits + 1)
    fallback
    (PluginSampleMajority.succ_le_twoPow_succ_of_le_twoPow hbase)
    hsurj

/-- Strict bit-deficit form for the raw one-sample surface-cardinality bound. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_oneSample_of_surfaceCard_le_twoPow_and_fallbackBits_add_baseBits_succ_lt_surfaceCard
    {Z : Type v} {k fallbackBits baseBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hbase :
      Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
        2 ^ baseBits)
    (hbits :
      fallbackBits + (baseBits + 1) <
        Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 1 fallbackBits fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_oneSample_of_surfaceCard_succ_le_twoPow_and_fallbackBits_add_baseBits_lt_surfaceCard
    (Z := Z) (k := k) (fallbackBits := fallbackBits) (baseBits := baseBits + 1)
    fallback
    (PluginSampleMajority.succ_le_twoPow_succ_of_le_twoPow hbase)
    hbits

/-- A sample-size bound at least the visible alphabet size still gives no small
finite predictor cover below the exact visible truth-table budget. -/
theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_not_finitePredictorCover_of_lt_surfaceCard
    {Z : Type v} {k s sampleBound : ℕ} [Fintype Z]
    (hbound : Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).predictorFamily.FinitePredictorCover
        (2 ^ s) := by
  intro hcover
  have hsmall :
      ExactVisibleCompressionTarget
        (Z := Z) (k := k)
        (Index := BoundedSampleIndex (ExactVisiblePostSwitchSurface Z k) sampleBound)
        (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).predictorFamily s :=
    (exactVisibleCompressionTarget_iff_finitePredictorCover
      (Z := Z) (k := k) (s := s)
      (Index := BoundedSampleIndex (ExactVisiblePostSwitchSurface Z k) sampleBound)
      (G := (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).predictorFamily)).2
      hcover
  exact
    (not_exactVisibleCompressionTarget_of_surjective_predict
      (Z := Z) (k := k) (s := s)
      (Index := BoundedSampleIndex (ExactVisiblePostSwitchSurface Z k) sampleBound)
      (G := (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).predictorFamily)
      hs
      (boundedSamplePluginMajorityActualSwitchedLocalInterface_surjective
        Z k sampleBound hbound)) hsmall

/-- Consequently the same bounded-sample endpoint cannot provide the clocked
finite-learning payload below the exact visible truth-table budget. -/
theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_not_clockedKpolyFiniteLearningPayload_of_lt_surfaceCard
    {Z : Type v} {k s sampleBound clock : ℕ} [Fintype Z]
    (hbound : Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ClockedKpolyFiniteLearningPayload
        (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).predictorFamily
        s clock := by
  intro hpayload
  have hsmall :
      ExactVisibleCompressionTarget
        (Z := Z) (k := k)
        (Index := BoundedSampleIndex (ExactVisiblePostSwitchSurface Z k) sampleBound)
        (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).predictorFamily s :=
    exactVisibleCompressionTarget_of_clockedKpolyFiniteLearningPayload
      (Z := Z) (k := k) (s := s) (clock := clock)
      (Index := BoundedSampleIndex (ExactVisiblePostSwitchSurface Z k) sampleBound)
      hpayload
  exact
    (not_exactVisibleCompressionTarget_of_surjective_predict
      (Z := Z) (k := k) (s := s)
      (Index := BoundedSampleIndex (ExactVisiblePostSwitchSurface Z k) sampleBound)
      (G := (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).predictorFamily)
      hs
      (boundedSamplePluginMajorityActualSwitchedLocalInterface_surjective
        Z k sampleBound hbound)) hsmall

/-- Such a sample-size bound is also insufficient for the bounded-code minimal
missing assumption below the exact visible truth-table budget. -/
theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_not_bitCodeData_of_lt_surfaceCard
    {Z : Type v} {k s sampleBound : ℕ} [Fintype Z]
    (hbound : Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.BitCodeData
          (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound) s) := by
  rintro ⟨hcode⟩
  exact
    boundedSamplePluginMajorityActualSwitchedLocalInterface_not_finitePredictorCover_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) (sampleBound := sampleBound)
      hbound hs hcode.finitePredictorCover

/-- Such a sample-size bound is insufficient for the ZAB decision-list
constructor data below the exact visible truth-table budget. -/
theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_not_zabDecisionListData_of_lt_surfaceCard
    {Z : Type v} {k r sampleBound : ℕ} [Fintype Z]
    (hbound : Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound)
    (zfeat : Z → BitVec r)
    (hs : r + 2 * k + 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.ZABDecisionListData
          (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound) zfeat) := by
  rintro ⟨hzab⟩
  exact
    hzab.not_surjective_predict_of_lt_surfaceCard hs
      (boundedSamplePluginMajorityActualSwitchedLocalInterface_surjective
        Z k sampleBound hbound)

end Mettapedia.Computability.PNP
