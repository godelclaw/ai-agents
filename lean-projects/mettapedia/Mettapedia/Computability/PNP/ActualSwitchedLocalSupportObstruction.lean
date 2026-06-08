import Mettapedia.Computability.PNP.ActualSwitchedLocalFamily

/-!
# PNP crux: observed support does not control the full exact-visible rule image

The actual switched-local interface constrains the output of each local rule
only on visible inputs that are produced by blocks.  The `Kpoly` compression
target, however, controls each selected local rule as a Boolean function on the
entire exact visible post-switch surface.

This file records the gap.  A one-block interface has only two possible
observed output behaviours, hence a one-bit observed-output budget.  But the
same interface can still carry the full Boolean rule family off support, so it
has no small exact-visible predictor cover below the full truth-table budget.
-/

namespace Mettapedia.Computability.PNP

universe v u w

namespace ActualSwitchedLocalInterface

variable {Z : Type v} {k : ℕ} {Index : Type*} {Block : Type*}

/-- The family of actually observed output functions over blocks. -/
def outputFamily (T : ActualSwitchedLocalInterface Z k Index Block) :
    IndexedPredictorFamily Index Block where
  predict := T.output

@[simp] theorem outputFamily_predict
    (T : ActualSwitchedLocalInterface Z k Index Block) (i : Index) (phi : Block) :
    T.outputFamily.predict i phi = T.output i phi := rfl

/-- A uniform section from exact visible inputs back to actual blocks.  This is
the missing reachability hypothesis needed to transfer an observed-output
compression theorem to the full exact-visible local-rule family. -/
def HasUniformVisibleSection
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (sec : ExactVisiblePostSwitchSurface Z k → Block) : Prop :=
  ∀ i u, T.visibleInput i (sec u) = u

/-- With a uniform visible section, the exact-visible predictor family is the
pullback of the actually observed block-output family. -/
theorem predictorFamily_factorsThrough_outputFamily_of_uniformVisibleSection
    (T : ActualSwitchedLocalInterface Z k Index Block)
    {sec : ExactVisiblePostSwitchSurface Z k → Block}
    (hsec : T.HasUniformVisibleSection sec) :
    T.predictorFamily.FactorsThrough sec T.outputFamily := by
  intro i u
  calc
    T.predictorFamily.predict i u = T.localRule i u := rfl
    _ = T.localRule i (T.visibleInput i (sec u)) := by
      rw [hsec i u]
    _ = T.output i (sec u) := (T.output_eq_visibleInput i (sec u)).symm
    _ = T.outputFamily.predict i (sec u) := rfl

/-- Therefore any finite observed-output cover transfers to the exact-visible
predictor family once the uniform visible section is supplied. -/
theorem predictorFamily_finitePredictorCover_of_outputFamily_finitePredictorCover
    (T : ActualSwitchedLocalInterface Z k Index Block)
    {sec : ExactVisiblePostSwitchSurface Z k → Block} {N : ℕ}
    (hsec : T.HasUniformVisibleSection sec)
    (hcover : T.outputFamily.FinitePredictorCover N) :
    T.predictorFamily.FinitePredictorCover N := by
  exact
    IndexedPredictorFamily.finitePredictorCover_of_factorsThrough
      (G := T.predictorFamily) (H := T.outputFamily) (view := sec)
      (T.predictorFamily_factorsThrough_outputFamily_of_uniformVisibleSection hsec)
      hcover

/-- The same transfer stated as an exact bit-budget theorem. -/
theorem predictorFamily_hasBitBudget_of_outputFamily_hasBitBudget
    (T : ActualSwitchedLocalInterface Z k Index Block)
    {sec : ExactVisiblePostSwitchSurface Z k → Block} {s : ℕ}
    (hsec : T.HasUniformVisibleSection sec)
    (hbudget : T.outputFamily.HasBitBudget s) :
    T.predictorFamily.HasBitBudget s := by
  exact
    IndexedPredictorFamily.hasBitBudget_of_factorsThrough
      (G := T.predictorFamily) (H := T.outputFamily) (view := sec)
      (T.predictorFamily_factorsThrough_outputFamily_of_uniformVisibleSection hsec)
      hbudget

/-- Consequently the current clocked `Kpoly` finite-learning payload follows
from an observed-output bit budget only under the uniform visible section
hypothesis. -/
theorem clockedKpolyFiniteLearningPayload_of_outputFamily_hasBitBudget
    [Fintype Z]
    (T : ActualSwitchedLocalInterface Z k Index Block)
    {sec : ExactVisiblePostSwitchSurface Z k → Block} {s clock : ℕ}
    (hsec : T.HasUniformVisibleSection sec)
    (hbudget : T.outputFamily.HasBitBudget s) :
    ClockedKpolyFiniteLearningPayload T.predictorFamily s clock := by
  exact
    clockedKpolyFiniteLearningPayload_of_exactVisibleCompressionTarget
      (G := T.predictorFamily) (s := s) (clock := clock)
      (T.predictorFamily_hasBitBudget_of_outputFamily_hasBitBudget hsec hbudget)

end ActualSwitchedLocalInterface

/-- A finite adaptive Boolean query tree over an oracle
`Surface → Bool`.  A node queries one surface point and selects the next
subtree according to the Boolean answer. -/
inductive AdaptiveBoolQueryTree (Surface : Type u) (α : Type w) : Type (max u w) where
  | leaf : α → AdaptiveBoolQueryTree Surface α
  | query :
      Surface →
      AdaptiveBoolQueryTree Surface α →
      AdaptiveBoolQueryTree Surface α →
      AdaptiveBoolQueryTree Surface α

namespace AdaptiveBoolQueryTree

variable {Surface : Type*} {α : Type*} {Block : Type*}

/-- Evaluate an adaptive query tree against a Boolean oracle.  The second
subtree is followed on a `true` answer. -/
def eval (oracle : Surface → Bool) :
    AdaptiveBoolQueryTree Surface α → α
  | leaf value => value
  | query u ifFalse ifTrue =>
      if oracle u then eval oracle ifTrue else eval oracle ifFalse

/-- Every query node in the tree asks a point reached by the support map. -/
def AllQueriesReachable (visibleOf : Block → Surface) :
    AdaptiveBoolQueryTree Surface α → Prop
  | leaf _ => True
  | query u ifFalse ifTrue =>
      (∃ phi, visibleOf phi = u) ∧
        AllQueriesReachable visibleOf ifFalse ∧
        AllQueriesReachable visibleOf ifTrue

/-- If every adaptive query is reachable, the whole adaptive transcript can be
simulated from the observed block-output trace. -/
theorem exists_traceDecoder_of_allQueriesReachable
    (visibleOf : Block → Surface)
    (tree : AdaptiveBoolQueryTree Surface α)
    (hreach : AllQueriesReachable visibleOf tree) :
    ∃ decode : (Block → Bool) → α,
      ∀ oracle : Surface → Bool,
        decode (fun phi => oracle (visibleOf phi)) = eval oracle tree := by
  induction tree with
  | leaf value =>
      exact ⟨fun _ => value, by intro oracle; rfl⟩
  | query u ifFalse ifTrue ihFalse ihTrue =>
      rcases hreach with ⟨⟨phi, hphi⟩, hFalse, hTrue⟩
      rcases ihFalse hFalse with ⟨decodeFalse, hdecodeFalse⟩
      rcases ihTrue hTrue with ⟨decodeTrue, hdecodeTrue⟩
      refine
        ⟨fun trace => if trace phi then decodeTrue trace else decodeFalse trace, ?_⟩
      intro oracle
      by_cases hu : oracle u
      · simp [eval, hphi, hu, hdecodeTrue]
      · simp [eval, hphi, hu, hdecodeFalse]

end AdaptiveBoolQueryTree

section FiniteObservedSupportFullRule

variable {Z : Type v} {k : ℕ}
variable {Block : Type*}

/-- An actual-local interface over an arbitrary block support whose selected
local rules are still the full exact-visible Boolean rule family.  The observed
block output only probes `rule` through `visibleOf`; all values outside the
image of `visibleOf` remain unconstrained by the observed output. -/
def supportFullRuleActualSwitchedLocalInterface
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k) :
    ActualSwitchedLocalInterface
      Z k (ExactVisibleRule Z k) Block where
  zOf := fun phi => (visibleOf phi).z
  aOf := fun _ phi => (visibleOf phi).a
  bOf := fun phi => (visibleOf phi).b
  localRule := fun rule u => rule u
  output := fun rule phi => rule (visibleOf phi)
  output_eq_local := by
    intro rule phi
    cases visibleOf phi
    rfl

@[simp] theorem supportFullRule_predictorFamily
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k) :
    (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily =
      fullExactVisibleRuleFamily Z k := by
  rfl

theorem supportFullRule_surjective
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k) :
    Function.Surjective
      (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily.predict := by
  simpa using fullExactVisibleRuleFamily_surjective Z k

/-- The observed block-output family has a truth-table budget bounded by the
size of the actual block support. -/
theorem supportFullRule_outputFamily_hasBitBudget_card
    [Fintype Block] (visibleOf : Block → ExactVisiblePostSwitchSurface Z k) :
    (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.HasBitBudget
      (Fintype.card Block) := by
  simpa using
    (IndexedPredictorFamily.hasBitBudget_card_of_fintype
      (Index := ExactVisibleRule Z k) (View := Block)
      ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily))

/-- Equivalently, the observed block-output family has a predictor cover of
size at most `2 ^ |Block|`. -/
theorem supportFullRule_outputFamily_finitePredictorCover_card
    [Fintype Block] (visibleOf : Block → ExactVisiblePostSwitchSurface Z k) :
    (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.FinitePredictorCover
      (2 ^ Fintype.card Block) := by
  have hbudget :=
    supportFullRule_outputFamily_hasBitBudget_card
      (Z := Z) (k := k) (Block := Block) visibleOf
  simpa using
    (IndexedPredictorFamily.hasBitBudget_iff_finitePredictorCover.mp hbudget)

/-- The observed block-output family is exactly the pullback of the full
exact-visible local-rule family along the reachable-support map `visibleOf`. -/
theorem supportFullRule_outputFamily_factorsThrough_predictorFamily
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k) :
    (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.FactorsThrough
      visibleOf (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily := by
  intro rule phi
  rfl

/-- If the reachable-support map misses an exact-visible input, two distinct
exact-visible rules have identical observed block-output behaviour. -/
theorem supportFullRule_exists_distinct_rules_same_outputFamily_of_not_surjective
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (hnot : ¬ Function.Surjective visibleOf) :
    ∃ rule₀ rule₁ : ExactVisibleRule Z k,
      rule₀ ≠ rule₁ ∧
        (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₀ =
          (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₁ ∧
        (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily.predict rule₀ ≠
          (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily.predict rule₁ := by
  classical
  simp only [Function.Surjective, not_forall] at hnot
  rcases hnot with ⟨u₀, hmissExists⟩
  have hmiss : ∀ phi, visibleOf phi ≠ u₀ := by
    intro phi hphi
    exact hmissExists ⟨phi, hphi⟩
  let rule₀ : ExactVisibleRule Z k := fun _ => false
  let rule₁ : ExactVisibleRule Z k := fun u => if u = u₀ then true else false
  refine ⟨rule₀, rule₁, ?_, ?_, ?_⟩
  · intro heq
    have hpoint := congrFun heq u₀
    simp [rule₀, rule₁] at hpoint
  · funext phi
    simp [ActualSwitchedLocalInterface.outputFamily,
      supportFullRuleActualSwitchedLocalInterface, rule₀, rule₁, hmiss phi]
  · intro heq
    have hpoint := congrFun heq u₀
    simp [supportFullRuleActualSwitchedLocalInterface, rule₀, rule₁] at hpoint

/-- Exact recovery from observed block-output behaviour forces the support map
to hit every exact-visible input. -/
theorem supportFullRule_observedRuleMap_injective_forces_visibleOf_surjective
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (hinj :
      Function.Injective
        (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict) :
    Function.Surjective visibleOf := by
  by_contra hnot
  rcases
    supportFullRule_exists_distinct_rules_same_outputFamily_of_not_surjective
      (Z := Z) (k := k) (Block := Block) visibleOf hnot with
    ⟨rule₀, rule₁, hne, hsame, _hdiff⟩
  exact hne (hinj hsame)

/-- Any decoder that reconstructs every full exact-visible rule from its
observed block-output trace forces the support map to hit every exact-visible
input.  This is the decoder form of the quotient-loss obstruction. -/
theorem supportFullRule_exactDecoder_forces_visibleOf_surjective
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (decode : (Block → Bool) → ExactVisibleRule Z k)
    (hdecode :
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          rule) :
    Function.Surjective visibleOf := by
  by_contra hnot
  rcases
    supportFullRule_exists_distinct_rules_same_outputFamily_of_not_surjective
      (Z := Z) (k := k) (Block := Block) visibleOf hnot with
    ⟨rule₀, rule₁, hne, hsame, _hdiff⟩
  have heq : rule₀ = rule₁ := by
    calc
      rule₀ =
          decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict
              rule₀) := (hdecode rule₀).symm
      _ =
          decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict
              rule₁) := by rw [hsame]
      _ = rule₁ := hdecode rule₁
  exact hne heq

/-- If the support map misses an exact-visible input, no post-processing
decoder can reconstruct all full exact-visible rules from observed block
outputs. -/
theorem supportFullRule_not_exists_exactDecoder_of_not_surjective
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (hnot : ¬ Function.Surjective visibleOf) :
    ¬ ∃ decode : (Block → Bool) → ExactVisibleRule Z k,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          rule := by
  rintro ⟨decode, hdecode⟩
  exact hnot
    (supportFullRule_exactDecoder_forces_visibleOf_surjective
      (Z := Z) (k := k) (Block := Block) visibleOf decode hdecode)

/-- More generally, any downstream property decoded from observed block-output
traces must be constant on the fibers of the observed quotient map. -/
theorem supportFullRule_propertyDecoder_constant_on_observedFibers
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    {α : Type*} (property : ExactVisibleRule Z k → α)
    (decode : (Block → Bool) → α)
    (hdecode :
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          property rule) :
    ∀ {rule₀ rule₁ : ExactVisibleRule Z k},
      (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₀ =
        (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₁ →
      property rule₀ = property rule₁ := by
  intro rule₀ rule₁ hsame
  calc
    property rule₀ =
        decode
          ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict
            rule₀) := (hdecode rule₀).symm
    _ =
        decode
          ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict
            rule₁) := by rw [hsame]
    _ = property rule₁ := hdecode rule₁

/-- A downstream property is decodable from observed block-output traces
exactly when it is constant on the fibers of the observed quotient map.  This
is the precise factorization criterion for replacing a full-rule target by a
reachable-support quotient. -/
theorem supportFullRule_exists_propertyDecoder_iff_constant_on_observedFibers
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    {α : Type*} (property : ExactVisibleRule Z k → α) :
    (∃ decode : (Block → Bool) → α,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          property rule) ↔
      ∀ {rule₀ rule₁ : ExactVisibleRule Z k},
        (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₀ =
          (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₁ →
        property rule₀ = property rule₁ := by
  constructor
  · rintro ⟨decode, hdecode⟩
    exact
      supportFullRule_propertyDecoder_constant_on_observedFibers
        (Z := Z) (k := k) (Block := Block) visibleOf property decode hdecode
  · intro hconstant
    classical
    refine
      ⟨fun trace =>
          if h :
              ∃ rule : ExactVisibleRule Z k,
                (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule =
                  trace
          then property (Classical.choose h)
          else property (fun _ => false), ?_⟩
    intro rule
    have htrace :
        ∃ rule' : ExactVisibleRule Z k,
          (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule' =
            (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule :=
      ⟨rule, rfl⟩
    dsimp
    rw [dif_pos htrace]
    exact hconstant (Classical.choose_spec htrace)

/-- Therefore any property separating two rules in the same observed-output
fiber cannot be decoded from observed block outputs. -/
theorem supportFullRule_not_exists_propertyDecoder_of_same_output_ne
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    {α : Type*} (property : ExactVisibleRule Z k → α)
    {rule₀ rule₁ : ExactVisibleRule Z k}
    (hsame :
      (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₀ =
        (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₁)
    (hprop : property rule₀ ≠ property rule₁) :
    ¬ ∃ decode : (Block → Bool) → α,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          property rule := by
  rintro ⟨decode, hdecode⟩
  exact hprop
    (supportFullRule_propertyDecoder_constant_on_observedFibers
      (Z := Z) (k := k) (Block := Block) visibleOf property decode hdecode hsame)

/-- If an exact-visible input is outside the reachable support, even the single
bit "what is the rule value at this input?" cannot be decoded from observed
block outputs. -/
theorem supportFullRule_not_exists_evalDecoder_of_missed_point
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (u₀ : ExactVisiblePostSwitchSurface Z k)
    (hmiss : ∀ phi, visibleOf phi ≠ u₀) :
    ¬ ∃ decode : (Block → Bool) → Bool,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          rule u₀ := by
  classical
  let rule₀ : ExactVisibleRule Z k := fun _ => false
  let rule₁ : ExactVisibleRule Z k := fun u => if u = u₀ then true else false
  have hsame :
      (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₀ =
        (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₁ := by
    funext phi
    simp [ActualSwitchedLocalInterface.outputFamily,
      supportFullRuleActualSwitchedLocalInterface, rule₀, rule₁, hmiss phi]
  have hprop : (fun rule : ExactVisibleRule Z k => rule u₀) rule₀ ≠
      (fun rule : ExactVisibleRule Z k => rule u₀) rule₁ := by
    simp [rule₀, rule₁]
  exact
    supportFullRule_not_exists_propertyDecoder_of_same_output_ne
      (Z := Z) (k := k) (Block := Block) visibleOf
      (fun rule : ExactVisibleRule Z k => rule u₀) hsame hprop

/-- Conversely, a single exact-visible rule bit is decodable from observed
block outputs exactly when that exact-visible input is actually reached by
some block. -/
theorem supportFullRule_exists_evalDecoder_iff_mem_range
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (u₀ : ExactVisiblePostSwitchSurface Z k) :
    (∃ decode : (Block → Bool) → Bool,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          rule u₀) ↔ ∃ phi, visibleOf phi = u₀ := by
  constructor
  · intro hdecode
    by_contra hnot
    exact
      (supportFullRule_not_exists_evalDecoder_of_missed_point
        (Z := Z) (k := k) (Block := Block) visibleOf u₀
        (by
          intro phi hphi
          exact hnot ⟨phi, hphi⟩)) hdecode
  · rintro ⟨phi₀, hphi₀⟩
    refine ⟨fun trace => trace phi₀, ?_⟩
    intro rule
    simp [ActualSwitchedLocalInterface.outputFamily,
      supportFullRuleActualSwitchedLocalInterface, hphi₀]

/-- A decoder for every exact-visible point query exists exactly when the
reachable support hits the whole exact-visible surface. -/
theorem supportFullRule_all_evalDecoders_iff_visibleOf_surjective
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k) :
    (∀ u₀ : ExactVisiblePostSwitchSurface Z k,
      ∃ decode : (Block → Bool) → Bool,
        ∀ rule : ExactVisibleRule Z k,
          decode
              ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
            rule u₀) ↔ Function.Surjective visibleOf := by
  constructor
  · intro hdecode u₀
    exact
      (supportFullRule_exists_evalDecoder_iff_mem_range
        (Z := Z) (k := k) (Block := Block) visibleOf u₀).1 (hdecode u₀)
  · intro hsurj u₀
    exact
      (supportFullRule_exists_evalDecoder_iff_mem_range
        (Z := Z) (k := k) (Block := Block) visibleOf u₀).2 (hsurj u₀)

/-- More generally, a whole family of exact-visible point queries is decodable
from observed block outputs exactly when every queried exact-visible point is
in the reachable support. -/
theorem supportFullRule_exists_queryDecoder_iff_forall_mem_range
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    {Query : Type*} (queryOf : Query → ExactVisiblePostSwitchSurface Z k) :
    (∃ decode : (Block → Bool) → Query → Bool,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          fun q => rule (queryOf q)) ↔ ∀ q, ∃ phi, visibleOf phi = queryOf q := by
  constructor
  · rintro ⟨decode, hdecode⟩ q
    exact
      (supportFullRule_exists_evalDecoder_iff_mem_range
        (Z := Z) (k := k) (Block := Block) visibleOf (queryOf q)).1
        ⟨fun trace => decode trace q, by
          intro rule
          exact congrFun (hdecode rule) q⟩
  · intro hreach
    classical
    refine ⟨fun trace q => trace (Classical.choose (hreach q)), ?_⟩
    intro rule
    funext q
    have hq : visibleOf (Classical.choose (hreach q)) = queryOf q :=
      Classical.choose_spec (hreach q)
    simp [ActualSwitchedLocalInterface.outputFamily,
      supportFullRuleActualSwitchedLocalInterface, hq]

/-- Hence a query family containing even one unreachable exact-visible point
cannot be decoded from observed block outputs. -/
theorem supportFullRule_not_exists_queryDecoder_of_missed_query
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    {Query : Type*} (queryOf : Query → ExactVisiblePostSwitchSurface Z k)
    (q₀ : Query) (hmiss : ∀ phi, visibleOf phi ≠ queryOf q₀) :
    ¬ ∃ decode : (Block → Bool) → Query → Bool,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          fun q => rule (queryOf q) := by
  intro hdecode
  have hreach :
      ∀ q, ∃ phi, visibleOf phi = queryOf q :=
    (supportFullRule_exists_queryDecoder_iff_forall_mem_range
      (Z := Z) (k := k) (Block := Block) visibleOf queryOf).1 hdecode
  rcases hreach q₀ with ⟨phi, hphi⟩
  exact hmiss phi hphi

/-- An adaptive query tree over exact-visible points is decodable from observed
block outputs whenever every point it may query lies in the reachable support.
This covers downstream algorithms whose later probes depend on earlier rule
answers. -/
theorem supportFullRule_exists_adaptiveQueryDecoder_of_allQueriesReachable
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    {α : Type*}
    (tree : AdaptiveBoolQueryTree (ExactVisiblePostSwitchSurface Z k) α)
    (hreach : AdaptiveBoolQueryTree.AllQueriesReachable visibleOf tree) :
    ∃ decode : (Block → Bool) → α,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          AdaptiveBoolQueryTree.eval rule tree := by
  rcases
    AdaptiveBoolQueryTree.exists_traceDecoder_of_allQueriesReachable
      visibleOf tree hreach with
    ⟨decode, hdecode⟩
  refine ⟨decode, ?_⟩
  intro rule
  simpa [ActualSwitchedLocalInterface.outputFamily,
    supportFullRuleActualSwitchedLocalInterface] using hdecode rule

/-- Exact adaptive decodability is still just quotient factorization: an
adaptive query tree can be decoded from observed traces exactly when its final
output is constant on observed-output fibers. -/
theorem supportFullRule_exists_adaptiveQueryDecoder_iff_constant_on_observedFibers
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    {α : Type*}
    (tree : AdaptiveBoolQueryTree (ExactVisiblePostSwitchSurface Z k) α) :
    (∃ decode : (Block → Bool) → α,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          AdaptiveBoolQueryTree.eval rule tree) ↔
      ∀ {rule₀ rule₁ : ExactVisibleRule Z k},
        (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₀ =
          (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₁ →
        AdaptiveBoolQueryTree.eval rule₀ tree =
          AdaptiveBoolQueryTree.eval rule₁ tree := by
  exact
    supportFullRule_exists_propertyDecoder_iff_constant_on_observedFibers
      (Z := Z) (k := k) (Block := Block) visibleOf
      (fun rule : ExactVisibleRule Z k => AdaptiveBoolQueryTree.eval rule tree)

/-- Any pair of full exact-visible rules with the same observed block trace
but different adaptive-tree outputs is a complete certificate that the
adaptive computation cannot be decoded from observed traces. -/
theorem supportFullRule_not_exists_adaptiveQueryDecoder_of_same_output_eval_ne
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    {α : Type*}
    (tree : AdaptiveBoolQueryTree (ExactVisiblePostSwitchSurface Z k) α)
    {rule₀ rule₁ : ExactVisibleRule Z k}
    (hsame :
      (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₀ =
        (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₁)
    (hne :
      AdaptiveBoolQueryTree.eval rule₀ tree ≠
        AdaptiveBoolQueryTree.eval rule₁ tree) :
    ¬ ∃ decode : (Block → Bool) → α,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          AdaptiveBoolQueryTree.eval rule tree := by
  exact
    supportFullRule_not_exists_propertyDecoder_of_same_output_ne
      (Z := Z) (k := k) (Block := Block) visibleOf
      (fun rule : ExactVisibleRule Z k => AdaptiveBoolQueryTree.eval rule tree)
      hsame hne

/-- A one-step adaptive query at an unreachable root already cannot be decoded
when its two root branches produce different final outputs. -/
theorem supportFullRule_not_exists_rootAdaptiveQueryDecoder_of_missed_point_ne
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (u₀ : ExactVisiblePostSwitchSurface Z k)
    {α : Type*} {valueFalse valueTrue : α}
    (hmiss : ∀ phi, visibleOf phi ≠ u₀)
    (hne : valueFalse ≠ valueTrue) :
    ¬ ∃ decode : (Block → Bool) → α,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          AdaptiveBoolQueryTree.eval rule
            (AdaptiveBoolQueryTree.query u₀
              (AdaptiveBoolQueryTree.leaf valueFalse)
              (AdaptiveBoolQueryTree.leaf valueTrue)) := by
  classical
  let rule₀ : ExactVisibleRule Z k := fun _ => false
  let rule₁ : ExactVisibleRule Z k := fun u => if u = u₀ then true else false
  have hsame :
      (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₀ =
        (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₁ := by
    funext phi
    simp [ActualSwitchedLocalInterface.outputFamily,
      supportFullRuleActualSwitchedLocalInterface, rule₀, rule₁, hmiss phi]
  rintro ⟨decode, hdecode⟩
  have heq : valueFalse = valueTrue := by
    calc
      valueFalse =
          AdaptiveBoolQueryTree.eval rule₀
            (AdaptiveBoolQueryTree.query u₀
              (AdaptiveBoolQueryTree.leaf valueFalse)
              (AdaptiveBoolQueryTree.leaf valueTrue)) := by
        simp [AdaptiveBoolQueryTree.eval, rule₀]
      _ =
          decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict
              rule₀) := (hdecode rule₀).symm
      _ =
          decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict
              rule₁) := by rw [hsame]
      _ =
          AdaptiveBoolQueryTree.eval rule₁
            (AdaptiveBoolQueryTree.query u₀
              (AdaptiveBoolQueryTree.leaf valueFalse)
              (AdaptiveBoolQueryTree.leaf valueTrue)) := hdecode rule₁
      _ = valueTrue := by
        simp [AdaptiveBoolQueryTree.eval, rule₁]
  exact hne heq

/-- If the support map is not surjective, some exact-visible bit is not
observable from the block-output quotient. -/
theorem supportFullRule_exists_unobservable_eval_of_not_surjective
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (hnot : ¬ Function.Surjective visibleOf) :
    ∃ u₀ : ExactVisiblePostSwitchSurface Z k,
      ¬ ∃ decode : (Block → Bool) → Bool,
        ∀ rule : ExactVisibleRule Z k,
          decode
              ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
            rule u₀ := by
  classical
  simp only [Function.Surjective, not_forall] at hnot
  rcases hnot with ⟨u₀, hmissExists⟩
  have hmiss : ∀ phi, visibleOf phi ≠ u₀ := by
    intro phi hphi
    exact hmissExists ⟨phi, hphi⟩
  exact
    ⟨u₀,
      supportFullRule_not_exists_evalDecoder_of_missed_point
        (Z := Z) (k := k) (Block := Block) visibleOf u₀ hmiss⟩

/-- Therefore a reachable-support quotient with smaller support than the full
surface cannot identify exact-visible rules by their observed outputs. -/
theorem supportFullRule_not_observedRuleMap_injective_of_card_lt_surfaceCard
    [Fintype Z] [Fintype Block]
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (hcard :
      Fintype.card Block < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Injective
        (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict := by
  intro hinj
  have hsurj :
      Function.Surjective visibleOf :=
    supportFullRule_observedRuleMap_injective_forces_visibleOf_surjective
      (Z := Z) (k := k) (Block := Block) visibleOf hinj
  exact (not_lt_of_ge (Fintype.card_le_of_surjective visibleOf hsurj)) hcard

/-- Cardinally small support gives an explicit pair of distinct exact-visible
rules that the observed block-output quotient cannot distinguish. -/
theorem supportFullRule_exists_distinct_rules_same_outputFamily_of_card_lt_surfaceCard
    [Fintype Z] [Fintype Block]
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (hcard :
      Fintype.card Block < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ∃ rule₀ rule₁ : ExactVisibleRule Z k,
      rule₀ ≠ rule₁ ∧
        (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₀ =
          (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₁ ∧
        (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily.predict rule₀ ≠
          (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily.predict rule₁ := by
  have hnot : ¬ Function.Surjective visibleOf := by
    intro hsurj
    exact (not_lt_of_ge (Fintype.card_le_of_surjective visibleOf hsurj)) hcard
  exact
    supportFullRule_exists_distinct_rules_same_outputFamily_of_not_surjective
      (Z := Z) (k := k) (Block := Block) visibleOf hnot

/-- Cardinally small support rules out every exact decoder from observed block
outputs to full exact-visible rules. -/
theorem supportFullRule_not_exists_exactDecoder_of_card_lt_surfaceCard
    [Fintype Z] [Fintype Block]
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (hcard :
      Fintype.card Block < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ∃ decode : (Block → Bool) → ExactVisibleRule Z k,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          rule := by
  have hnot : ¬ Function.Surjective visibleOf := by
    intro hsurj
    exact (not_lt_of_ge (Fintype.card_le_of_surjective visibleOf hsurj)) hcard
  exact
    supportFullRule_not_exists_exactDecoder_of_not_surjective
      (Z := Z) (k := k) (Block := Block) visibleOf hnot

/-- Cardinally small support leaves at least one exact-visible rule bit
unobservable from the observed block-output quotient. -/
theorem supportFullRule_exists_unobservable_eval_of_card_lt_surfaceCard
    [Fintype Z] [Fintype Block]
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (hcard :
      Fintype.card Block < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ∃ u₀ : ExactVisiblePostSwitchSurface Z k,
      ¬ ∃ decode : (Block → Bool) → Bool,
        ∀ rule : ExactVisibleRule Z k,
          decode
              ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
            rule u₀ := by
  have hnot : ¬ Function.Surjective visibleOf := by
    intro hsurj
    exact (not_lt_of_ge (Fintype.card_le_of_surjective visibleOf hsurj)) hcard
  exact
    supportFullRule_exists_unobservable_eval_of_not_surjective
      (Z := Z) (k := k) (Block := Block) visibleOf hnot

/-- If every exact-visible input has an actual block realizing it uniformly in
the output index, the observed finite cover really does transfer to the full
exact-visible family. -/
theorem supportFullRule_predictorFamily_finitePredictorCover_card_of_uniformVisibleSection
    [Fintype Block] (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    {sec : ExactVisiblePostSwitchSurface Z k → Block}
    (hsec :
      (supportFullRuleActualSwitchedLocalInterface visibleOf).HasUniformVisibleSection sec) :
    (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily.FinitePredictorCover
      (2 ^ Fintype.card Block) := by
  exact
    ActualSwitchedLocalInterface.predictorFamily_finitePredictorCover_of_outputFamily_finitePredictorCover
      (supportFullRuleActualSwitchedLocalInterface visibleOf) hsec
      (supportFullRule_outputFamily_finitePredictorCover_card
        (Z := Z) (k := k) (Block := Block) visibleOf)

/-- The corresponding clocked payload follows at the block truth-table budget
when the uniform visible section exists. -/
theorem supportFullRule_clockedKpolyFiniteLearningPayload_card_of_uniformVisibleSection
    [Fintype Z] [Fintype Block]
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    {sec : ExactVisiblePostSwitchSurface Z k → Block} {clock : ℕ}
    (hsec :
      (supportFullRuleActualSwitchedLocalInterface visibleOf).HasUniformVisibleSection sec) :
    ClockedKpolyFiniteLearningPayload
      (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily
      (Fintype.card Block) clock := by
  exact
    ActualSwitchedLocalInterface.clockedKpolyFiniteLearningPayload_of_outputFamily_hasBitBudget
      (supportFullRuleActualSwitchedLocalInterface visibleOf) hsec
      (supportFullRule_outputFamily_hasBitBudget_card
        (Z := Z) (k := k) (Block := Block) visibleOf)

/-- For the finite-support full-rule construction, a uniform visible section
forces `visibleOf` to be surjective, hence the support must be at least as
large as the full exact-visible surface. -/
theorem supportFullRule_surfaceCard_le_blockCard_of_uniformVisibleSection
    [Fintype Z] [Fintype Block]
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    {sec : ExactVisiblePostSwitchSurface Z k → Block}
    (hsec :
      (supportFullRuleActualSwitchedLocalInterface visibleOf).HasUniformVisibleSection sec) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ Fintype.card Block := by
  classical
  have hsurj : Function.Surjective visibleOf := by
    intro u
    refine ⟨sec u, ?_⟩
    have h := hsec (fun _ => false) u
    simpa [supportFullRuleActualSwitchedLocalInterface,
      ActualSwitchedLocalInterface.visibleInput] using h
  exact Fintype.card_le_of_surjective visibleOf hsurj

/-- Thus the finite-support repair is impossible when the observed block
support is smaller than the exact-visible surface. -/
theorem supportFullRule_not_hasUniformVisibleSection_of_card_lt_surfaceCard
    [Fintype Z] [Fintype Block]
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (hcard :
      Fintype.card Block < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ∃ sec : ExactVisiblePostSwitchSurface Z k → Block,
      (supportFullRuleActualSwitchedLocalInterface visibleOf).HasUniformVisibleSection sec := by
  rintro ⟨sec, hsec⟩
  exact
    (not_lt_of_ge
      (supportFullRule_surfaceCard_le_blockCard_of_uniformVisibleSection
        (Z := Z) (k := k) (Block := Block) visibleOf hsec)) hcard

/-- But the selected local-rule image is still the full exact-visible Boolean
rule family, so it has no below-surface finite predictor cover. -/
theorem supportFullRule_not_finitePredictorCover_of_lt_surfaceCard
    [Fintype Z] {s : ℕ} (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily.FinitePredictorCover
        (2 ^ s) := by
  simpa using
    (fullExactVisibleRuleFamily_not_finitePredictorCover_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) hs)

/-- Therefore a finite observed support bound does not imply a full
exact-visible predictor-image bound. -/
theorem supportFullRule_observedSmall_and_not_exactVisibleCover
    [Fintype Z] [Fintype Block] {s : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.FinitePredictorCover
        (2 ^ Fintype.card Block) ∧
      ¬ (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily.FinitePredictorCover
        (2 ^ s) := by
  exact
    ⟨supportFullRule_outputFamily_finitePredictorCover_card
        (Z := Z) (k := k) (Block := Block) visibleOf,
      supportFullRule_not_finitePredictorCover_of_lt_surfaceCard
        (Z := Z) (k := k) (s := s) visibleOf hs⟩

/-- Likewise, finite observed support does not give the clocked finite-learning
payload for the full exact-visible local-rule family. -/
theorem supportFullRule_not_clockedKpolyFiniteLearningPayload_of_lt_surfaceCard
    [Fintype Z] {s clock : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ClockedKpolyFiniteLearningPayload
        (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily s clock := by
  simpa using
    (fullExactVisibleRuleFamily_not_clockedKpolyFiniteLearningPayload_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) (clock := clock) hs)

end FiniteObservedSupportFullRule

section OneBlockFullRule

variable {Z : Type v} {k : ℕ}

/-- A one-block actual-local interface whose selected local rules are still the
full exact-visible Boolean rule family.  The block support is the single visible
point `u0`; all off-support values are unconstrained by the observed output. -/
abbrev oneBlockFullRuleActualSwitchedLocalInterface
    (u0 : ExactVisiblePostSwitchSurface Z k) :
    ActualSwitchedLocalInterface
      Z k (ExactVisibleRule Z k) Unit :=
  supportFullRuleActualSwitchedLocalInterface (Block := Unit) (fun _ => u0)

@[simp] theorem oneBlockFullRule_predictorFamily
    (u0 : ExactVisiblePostSwitchSurface Z k) :
    (oneBlockFullRuleActualSwitchedLocalInterface u0).predictorFamily =
      fullExactVisibleRuleFamily Z k := by
  rfl

theorem oneBlockFullRule_surjective
    (u0 : ExactVisiblePostSwitchSurface Z k) :
    Function.Surjective
      (oneBlockFullRuleActualSwitchedLocalInterface u0).predictorFamily.predict := by
  exact supportFullRule_surjective (Block := Unit) (fun _ => u0)

/-- The observed block-output family has a one-bit truth-table budget, because
the block space is a singleton. -/
theorem oneBlockFullRule_outputFamily_hasBitBudget_one
    (u0 : ExactVisiblePostSwitchSurface Z k) :
    (oneBlockFullRuleActualSwitchedLocalInterface u0).outputFamily.HasBitBudget 1 := by
  simpa using
    (supportFullRule_outputFamily_hasBitBudget_card
      (Z := Z) (k := k) (Block := Unit) (fun _ => u0))

/-- Equivalently, the observed block-output family has a predictor cover of
size at most two. -/
theorem oneBlockFullRule_outputFamily_finitePredictorCover_two
    (u0 : ExactVisiblePostSwitchSurface Z k) :
    (oneBlockFullRuleActualSwitchedLocalInterface u0).outputFamily.FinitePredictorCover 2 := by
  have hbudget :=
    oneBlockFullRule_outputFamily_hasBitBudget_one (Z := Z) (k := k) u0
  simpa using
    (IndexedPredictorFamily.hasBitBudget_iff_finitePredictorCover.mp hbudget)

/-- A one-block full-rule construction cannot have a uniform visible section
once the exact-visible surface has more than one point. -/
theorem oneBlockFullRule_not_hasUniformVisibleSection_of_one_lt_surfaceCard
    [Fintype Z] (u0 : ExactVisiblePostSwitchSurface Z k)
    (hcard : 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ∃ sec : ExactVisiblePostSwitchSurface Z k → Unit,
      (oneBlockFullRuleActualSwitchedLocalInterface u0).HasUniformVisibleSection sec := by
  simpa using
    (supportFullRule_not_hasUniformVisibleSection_of_card_lt_surfaceCard
      (Z := Z) (k := k) (Block := Unit) (fun _ => u0) hcard)

/-- A one-block reachable-support quotient cannot distinguish full
exact-visible rules once the exact-visible surface has more than one point. -/
theorem oneBlockFullRule_exists_distinct_rules_same_outputFamily_of_one_lt_surfaceCard
    [Fintype Z] (u0 : ExactVisiblePostSwitchSurface Z k)
    (hcard : 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ∃ rule₀ rule₁ : ExactVisibleRule Z k,
      rule₀ ≠ rule₁ ∧
        (oneBlockFullRuleActualSwitchedLocalInterface u0).outputFamily.predict rule₀ =
          (oneBlockFullRuleActualSwitchedLocalInterface u0).outputFamily.predict rule₁ ∧
        (oneBlockFullRuleActualSwitchedLocalInterface u0).predictorFamily.predict rule₀ ≠
          (oneBlockFullRuleActualSwitchedLocalInterface u0).predictorFamily.predict rule₁ := by
  simpa using
    (supportFullRule_exists_distinct_rules_same_outputFamily_of_card_lt_surfaceCard
      (Z := Z) (k := k) (Block := Unit) (fun _ => u0) hcard)

/-- No decoder from a singleton observed trace can reconstruct every full
exact-visible rule once the exact-visible surface has more than one point. -/
theorem oneBlockFullRule_not_exists_exactDecoder_of_one_lt_surfaceCard
    [Fintype Z] (u0 : ExactVisiblePostSwitchSurface Z k)
    (hcard : 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ∃ decode : (Unit → Bool) → ExactVisibleRule Z k,
      ∀ rule : ExactVisibleRule Z k,
        decode ((oneBlockFullRuleActualSwitchedLocalInterface u0).outputFamily.predict rule) =
          rule := by
  simpa using
    (supportFullRule_not_exists_exactDecoder_of_card_lt_surfaceCard
      (Z := Z) (k := k) (Block := Unit) (fun _ => u0) hcard)

/-- In the one-block case, some exact-visible bit is unobservable whenever the
exact-visible surface has more than one point. -/
theorem oneBlockFullRule_exists_unobservable_eval_of_one_lt_surfaceCard
    [Fintype Z] (u0 : ExactVisiblePostSwitchSurface Z k)
    (hcard : 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ∃ u : ExactVisiblePostSwitchSurface Z k,
      ¬ ∃ decode : (Unit → Bool) → Bool,
        ∀ rule : ExactVisibleRule Z k,
          decode ((oneBlockFullRuleActualSwitchedLocalInterface u0).outputFamily.predict rule) =
            rule u := by
  simpa using
    (supportFullRule_exists_unobservable_eval_of_card_lt_surfaceCard
      (Z := Z) (k := k) (Block := Unit) (fun _ => u0) hcard)

/-- But the full exact-visible local-rule image is still the full Boolean rule
family, so it has no below-surface finite predictor cover. -/
theorem oneBlockFullRule_not_finitePredictorCover_of_lt_surfaceCard
    [Fintype Z] {s : ℕ} (u0 : ExactVisiblePostSwitchSurface Z k)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (oneBlockFullRuleActualSwitchedLocalInterface u0).predictorFamily.FinitePredictorCover
        (2 ^ s) := by
  exact
    supportFullRule_not_finitePredictorCover_of_lt_surfaceCard
      (Z := Z) (k := k) (Block := Unit) (s := s) (fun _ => u0) hs

/-- The one-block interface therefore refutes the move from a tiny observed
output image to a full exact-visible predictor-image bound. -/
theorem oneBlockFullRule_observedSmall_and_not_exactVisibleCover
    [Fintype Z] {s : ℕ} (u0 : ExactVisiblePostSwitchSurface Z k)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    (oneBlockFullRuleActualSwitchedLocalInterface u0).outputFamily.FinitePredictorCover 2 ∧
      ¬ (oneBlockFullRuleActualSwitchedLocalInterface u0).predictorFamily.FinitePredictorCover
        (2 ^ s) := by
  exact
    ⟨oneBlockFullRule_outputFamily_finitePredictorCover_two (Z := Z) (k := k) u0,
      oneBlockFullRule_not_finitePredictorCover_of_lt_surfaceCard
        (Z := Z) (k := k) (s := s) u0 hs⟩

/-- Likewise, tiny observed support does not give the clocked finite-learning
payload for the full exact-visible local-rule family. -/
theorem oneBlockFullRule_not_clockedKpolyFiniteLearningPayload_of_lt_surfaceCard
    [Fintype Z] {s clock : ℕ} (u0 : ExactVisiblePostSwitchSurface Z k)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ClockedKpolyFiniteLearningPayload
        (oneBlockFullRuleActualSwitchedLocalInterface u0).predictorFamily s clock := by
  exact
    supportFullRule_not_clockedKpolyFiniteLearningPayload_of_lt_surfaceCard
      (Z := Z) (k := k) (Block := Unit) (s := s) (clock := clock) (fun _ => u0) hs

end OneBlockFullRule

end Mettapedia.Computability.PNP
