import Mettapedia.Computability.PNP.ClockedKpolyGapAssessment

/-!
# Regression checks for clocked `Kpoly` gap assessment

These wrappers pin the assessment that the accumulated clocked finite-learning
payload is exactly the existing finite predictor-image obligation, together
with the corresponding finite-image obstruction forms.
-/

namespace Mettapedia.Computability.PNP.ClockedKpolyGapAssessmentRegression

universe u

theorem payload_of_exactVisibleCompressionTarget_regression
    {Z : Type*} [Fintype Z] {k s clock : ℕ} {Index : Type u}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hsmall : ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s) :
    ClockedKpolyFiniteLearningPayload G s clock :=
  clockedKpolyFiniteLearningPayload_of_exactVisibleCompressionTarget
    (Z := Z) (k := k) (s := s) (clock := clock) (Index := Index) hsmall

theorem exactVisibleCompressionTarget_of_payload_regression
    {Z : Type*} [Fintype Z] {k s clock : ℕ} {Index : Type u}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hpayload : ClockedKpolyFiniteLearningPayload G s clock) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s :=
  exactVisibleCompressionTarget_of_clockedKpolyFiniteLearningPayload
    (Z := Z) (k := k) (s := s) (clock := clock) (Index := Index) hpayload

theorem payload_iff_exactVisibleCompressionTarget_regression
    {Z : Type*} [Fintype Z] {k s clock : ℕ} {Index : Type u}
    {G : ExactVisibleSwitchedFamily Z k Index} :
    ClockedKpolyFiniteLearningPayload G s clock ↔
      ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s :=
  clockedKpolyFiniteLearningPayload_iff_exactVisibleCompressionTarget
    (Z := Z) (k := k) (s := s) (clock := clock) (Index := Index)

theorem payload_iff_finitePredictorCover_regression
    {Z : Type*} [Fintype Z] {k s clock : ℕ} {Index : Type u}
    {G : ExactVisibleSwitchedFamily Z k Index} :
    ClockedKpolyFiniteLearningPayload G s clock ↔
      G.FinitePredictorCover (2 ^ s) :=
  clockedKpolyFiniteLearningPayload_iff_finitePredictorCover
    (Z := Z) (k := k) (s := s) (clock := clock) (Index := Index)

theorem not_payload_of_surjective_predict_of_lt_predictorCard_regression
    {Z : Type*} [Fintype Z] {k s clock : ℕ} {Index : Type u}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hs : 2 ^ s < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k))
    (hsurj : Function.Surjective G.predict) :
    ¬ ClockedKpolyFiniteLearningPayload G s clock :=
  not_clockedKpolyFiniteLearningPayload_of_surjective_predict_of_lt_predictorCard
    (Z := Z) (k := k) (s := s) (clock := clock) (Index := Index) hs hsurj

theorem not_payload_of_injective_realization_of_lt_card_regression
    {Probe Z : Type*} [Fintype Probe] [Fintype Z]
    {k s clock : ℕ} {Index : Type u}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hs : 2 ^ s < Fintype.card Probe) :
    ¬ ClockedKpolyFiniteLearningPayload G s clock :=
  not_clockedKpolyFiniteLearningPayload_of_injective_realization_of_lt_card
    (Z := Z) (k := k) (s := s) (clock := clock) (Index := Index)
    target hinj hreal hs

end Mettapedia.Computability.PNP.ClockedKpolyGapAssessmentRegression
