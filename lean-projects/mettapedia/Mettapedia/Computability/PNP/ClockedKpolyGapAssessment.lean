import Mettapedia.Computability.PNP.ExactVisibleImageBudget

/-!
# PNP clocked `Kpoly` gap assessment

The clocked `Kpoly` bridge now supplies construction, target-interface, rate,
and concrete good-sample theorems.  This file bundles those finite-learning
consequences and records the remaining gap precisely: the whole payload is
available exactly when the exact visible family has the corresponding finite
predictor-image cover.

Thus the accumulated bridge work closes the local bookkeeping and
finite-counting layers.  It does not by itself prove the manuscript-specific
small-image theorem for the actual switched predictors.
-/

namespace Mettapedia.Computability.PNP

universe u

section ExactVisible

variable {Z : Type*} [Fintype Z] {k s clock : ℕ} {Index : Type u}

/-- The finite-learning payload supplied by a clocked exact-visible `s`-bit
family: a clocked realization family plus, below the usual finite-count
threshold, both a non-deceptive point sample and an exact ERM recovery sample
for every selected predictor. -/
def ClockedKpolyFiniteLearningPayload
    (G : ExactVisibleSwitchedFamily Z k Index) (s clock : ℕ) : Prop :=
  ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
    G.RealizedByClockedBitFamily F ∧
      ∀ (i : Index) (m : ℕ),
        2 ^ s * (Fintype.card (ExactVisiblePostSwitchSurface Z k) - 1) ^ m <
            Fintype.card (ExactVisiblePostSwitchSurface Z k) ^ m →
          (∃ sample : PointSample (ExactVisiblePostSwitchSurface Z k) m,
            ¬ EncodedFamily.IsDeceptiveSample
                (BitEncodedClassifierFamily.toEncodedFamily
                  (ClockedBitCodeFamily.toBitEncodedClassifierFamily F))
                (G.predict i) sample) ∧
            ∃ sample : PointSample (ExactVisiblePostSwitchSurface Z k) m,
              ClockedBitCodeFamily.empiricalRiskPredictor F
                  (labeledByTarget (G.predict i) sample) =
                G.predict i

/-- An exact visible compression target supplies the full current clocked
finite-learning payload. -/
theorem clockedKpolyFiniteLearningPayload_of_exactVisibleCompressionTarget
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hsmall : ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s) :
    ClockedKpolyFiniteLearningPayload G s clock := by
  let F :=
    IndexedPredictorFamily.clockedBitCodeFamilyOfHasBitBudget
      (G := G) (s := s) clock hsmall
  have hreal : G.RealizedByClockedBitFamily F :=
    realizedByClockedExactVisibleFamily_of_exactVisibleCompressionTarget
      (Z := Z) (k := k) (s := s) (clock := clock) (Index := Index) hsmall
  refine ⟨F, hreal, ?_⟩
  intro i m hbound
  constructor
  · exact
      ClockedBitCodeFamily.exists_nondeceptiveSample_of_bitBudget_bound_lt
        (F := F) (target := G.predict i) (m := m) hbound
  · exact
      ClockedBitCodeFamily.exists_sample_empiricalRiskPredictor_eq_target_of_bitBudget_bound_lt
        (F := F) (target := G.predict i) (m := m) (hreal i) hbound

/-- Any payload strong enough to include a clocked realization family gives
back the exact visible compression target. -/
theorem exactVisibleCompressionTarget_of_clockedKpolyFiniteLearningPayload
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hpayload : ClockedKpolyFiniteLearningPayload G s clock) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s := by
  rcases hpayload with ⟨F, hreal, _⟩
  exact
    exactVisibleCompressionTarget_of_exists_clockedExactVisibleRealization
      (Z := Z) (k := k) (s := s) (clock := clock) (Index := Index)
      ⟨F, hreal⟩

/-- The accumulated clocked finite-learning payload closes no more and no less
than the exact visible compression target. -/
theorem clockedKpolyFiniteLearningPayload_iff_exactVisibleCompressionTarget
    {G : ExactVisibleSwitchedFamily Z k Index} :
    ClockedKpolyFiniteLearningPayload G s clock ↔
      ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s :=
  ⟨exactVisibleCompressionTarget_of_clockedKpolyFiniteLearningPayload,
    clockedKpolyFiniteLearningPayload_of_exactVisibleCompressionTarget⟩

/-- Equivalently, the full current payload is exactly a finite predictor-image
cover of size at most `2^s`. -/
theorem clockedKpolyFiniteLearningPayload_iff_finitePredictorCover
    {G : ExactVisibleSwitchedFamily Z k Index} :
    ClockedKpolyFiniteLearningPayload G s clock ↔
      G.FinitePredictorCover (2 ^ s) := by
  rw [clockedKpolyFiniteLearningPayload_iff_exactVisibleCompressionTarget,
    exactVisibleCompressionTarget_iff_finitePredictorCover]

/-- If the exact visible family is still fully expressive, then even the bundled
finite-learning payload is impossible below the full Boolean predictor-space
cardinality. -/
theorem not_clockedKpolyFiniteLearningPayload_of_surjective_predict_of_lt_predictorCard
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hs : 2 ^ s < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k))
    (hsurj : Function.Surjective G.predict) :
    ¬ ClockedKpolyFiniteLearningPayload G s clock := by
  intro hpayload
  have hcover : G.FinitePredictorCover (2 ^ s) :=
    (clockedKpolyFiniteLearningPayload_iff_finitePredictorCover
      (Z := Z) (k := k) (s := s) (clock := clock) (Index := Index)).1 hpayload
  exact not_exactVisible_finitePredictorCover_of_surjective_predict hs hsurj hcover

/-- Any injectively realized finite probe family is already an obstacle to the
full bundled payload below the probe-cardinality threshold. -/
theorem not_clockedKpolyFiniteLearningPayload_of_injective_realization_of_lt_card
    {Probe : Type*} [Fintype Probe]
    {G : ExactVisibleSwitchedFamily Z k Index}
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hs : 2 ^ s < Fintype.card Probe) :
    ¬ ClockedKpolyFiniteLearningPayload G s clock := by
  intro hpayload
  have hcover : G.FinitePredictorCover (2 ^ s) :=
    (clockedKpolyFiniteLearningPayload_iff_finitePredictorCover
      (Z := Z) (k := k) (s := s) (clock := clock) (Index := Index)).1 hpayload
  exact
    not_exactVisible_finitePredictorCover_of_injective_realization_of_lt_card
      target hinj hreal hs hcover

end ExactVisible

end Mettapedia.Computability.PNP
