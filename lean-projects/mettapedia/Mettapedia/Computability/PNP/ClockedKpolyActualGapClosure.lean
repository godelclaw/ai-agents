import Mettapedia.Computability.PNP.BitVecZABERMInterface
import Mettapedia.Computability.PNP.ClockedKpolyGapAssessment
import Mettapedia.Computability.PNP.ExactZABERMRoute
import Mettapedia.Computability.PNP.ProductSuccessKpolyBridgeObstruction

/-!
# PNP clocked `Kpoly`: actual exact-visible family gap closure

The clocked bridge payload is equivalent to a finite predictor-image cover.
For the concrete exact `(zfeat(z), a, b)` ERM family already present in the
grassroots route, that finite image is not an extra assumption: it is supplied
by the decision-list code family itself.

This file keeps the closure narrow.  It proves the clocked payload for the
actual ERM-selected exact-visible families, and records the complementary
counterexample showing that the bare `ExactVisibleSwitchedFamily` interface
alone cannot imply the same theorem.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

universe u v

section ExactZABERM

variable {Z : Type v} [Fintype Z] {r k clock : ℕ} {Index : Type u}

/-- The concrete exact `(zfeat(z), a, b)` ERM-selected switched family has the
full clocked finite-learning payload at the decision-list bit budget. -/
theorem exactZABDecisionListERMClockedKpolyFiniteLearningPayload
    (zfeat : Z → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    ClockedKpolyFiniteLearningPayload
      (exactZABDecisionListERMFamily
        (Z := Z) (r := r) (k := k) (Index := Index) zfeat samples)
      (r + 2 * k + 1) clock := by
  exact
    clockedKpolyFiniteLearningPayload_of_exactVisibleCompressionTarget
      (Z := Z) (k := k) (s := r + 2 * k + 1) (clock := clock)
      (Index := Index)
      (exactZABDecisionListERMCompressionTarget_twoMul
        (Z := Z) (r := r) (k := k) (Index := Index) zfeat samples)

/-- If a manuscript-facing exact family is identified with the concrete
decision-list ERM family, that identification is sufficient to close the
clocked payload target. -/
theorem clockedKpolyFiniteLearningPayload_of_eq_exactZABDecisionListERMFamily
    (zfeat : Z → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hG :
      G =
        exactZABDecisionListERMFamily
          (Z := Z) (r := r) (k := k) (Index := Index) zfeat samples) :
    ClockedKpolyFiniteLearningPayload G (r + 2 * k + 1) clock := by
  subst G
  exact
    exactZABDecisionListERMClockedKpolyFiniteLearningPayload
      (Z := Z) (r := r) (k := k) (clock := clock) (Index := Index)
      zfeat samples

end ExactZABERM

section BitVecZABERM

variable {r k clock : ℕ} {Index : Type u}

/-- On the raw bit-valued visible surface, the concrete exact ERM-selected
family has the full clocked finite-learning payload. -/
theorem bitVecZABDecisionListERMClockedKpolyFiniteLearningPayload
    [Fintype (BitVec r)]
    (samples :
      Index → Sample (ExactVisiblePostSwitchSurface (BitVec r) k) Bool) :
    ClockedKpolyFiniteLearningPayload
      (bitVecZABDecisionListERMFamily
        (r := r) (k := k) (Index := Index) samples)
      (r + 2 * k + 1) clock := by
  simpa [bitVecZABDecisionListERMFamily, identityZExtractor] using
    (exactZABDecisionListERMClockedKpolyFiniteLearningPayload
      (Z := BitVec r) (r := r) (k := k) (clock := clock)
      (Index := Index) identityZExtractor samples)

/-- Equality with the bit-valued exact ERM-selected family is the minimal
small-image assumption needed to transfer the clocked payload to an arbitrary
family variable `G`. -/
theorem clockedKpolyFiniteLearningPayload_of_eq_bitVecZABDecisionListERMFamily
    [Fintype (BitVec r)]
    (samples :
      Index → Sample (ExactVisiblePostSwitchSurface (BitVec r) k) Bool)
    {G : ExactVisibleSwitchedFamily (BitVec r) k Index}
    (hG :
      G =
        bitVecZABDecisionListERMFamily
          (r := r) (k := k) (Index := Index) samples) :
    ClockedKpolyFiniteLearningPayload G (r + 2 * k + 1) clock := by
  subst G
  exact
    bitVecZABDecisionListERMClockedKpolyFiniteLearningPayload
      (r := r) (k := k) (clock := clock) (Index := Index) samples

/-- The existing recovery-data package also closes the clocked payload target,
because it contains the exact-family identification and therefore the exact
visible compression target. -/
theorem BitVecZABERMRecoveryData.clockedKpolyFiniteLearningPayload
    [Fintype (BitVec r)]
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec r) k)}
    {G : ExactVisibleSwitchedFamily (BitVec r) k Index}
    {q : ℝ≥0∞}
    (h : BitVecZABERMRecoveryData
      (r := r) (k := k) (Index := Index) μ G q) :
    ClockedKpolyFiniteLearningPayload G (r + 2 * k + 1) clock := by
  exact
    clockedKpolyFiniteLearningPayload_of_exactVisibleCompressionTarget
      (Z := BitVec r) (k := k) (s := r + 2 * k + 1) (clock := clock)
      (Index := Index) h.compressionTarget

end BitVecZABERM

section CurrentInterfaceObstruction

variable {Z : Type v} [Fintype Z] {k s clock : ℕ}

/-- The full exact-visible Boolean family allowed by the current interface has
no finite predictor cover of size `2^s` below the full visible truth-table
budget. -/
theorem fullExactVisibleRuleFamily_not_finitePredictorCover_of_lt_surfaceCard
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (fullExactVisibleRuleFamily Z k).FinitePredictorCover (2 ^ s) := by
  intro hcover
  have hsmall :
      ExactVisibleCompressionTarget
        (Z := Z) (k := k) (Index := ExactVisibleRule Z k)
        (fullExactVisibleRuleFamily Z k) s :=
    (exactVisibleCompressionTarget_iff_finitePredictorCover
      (Z := Z) (k := k) (s := s) (Index := ExactVisibleRule Z k)
      (G := fullExactVisibleRuleFamily Z k)).2 hcover
  exact
    (not_exactVisibleCompressionTarget_of_surjective_predict
      (Z := Z) (k := k) (s := s) (Index := ExactVisibleRule Z k)
      (G := fullExactVisibleRuleFamily Z k)
      hs (fullExactVisibleRuleFamily_surjective Z k)) hsmall

/-- The same full exact-visible Boolean family refutes the clocked finite
learning payload below the full visible truth-table budget. -/
theorem fullExactVisibleRuleFamily_not_clockedKpolyFiniteLearningPayload_of_lt_surfaceCard
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ClockedKpolyFiniteLearningPayload
        (fullExactVisibleRuleFamily Z k) s clock := by
  intro hpayload
  have hsmall :
      ExactVisibleCompressionTarget
        (Z := Z) (k := k) (Index := ExactVisibleRule Z k)
        (fullExactVisibleRuleFamily Z k) s :=
    exactVisibleCompressionTarget_of_clockedKpolyFiniteLearningPayload
      (Z := Z) (k := k) (s := s) (clock := clock)
      (Index := ExactVisibleRule Z k) hpayload
  exact
    (not_exactVisibleCompressionTarget_of_surjective_predict
      (Z := Z) (k := k) (s := s) (Index := ExactVisibleRule Z k)
      (G := fullExactVisibleRuleFamily Z k)
      hs (fullExactVisibleRuleFamily_surjective Z k)) hsmall

/-- Therefore the bare exact-visible family interface cannot imply the small
finite predictor-image theorem for every switched family. -/
theorem currentExactVisibleInterface_not_forall_finitePredictorCover_of_lt_surfaceCard
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (∀ {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index),
        G.FinitePredictorCover (2 ^ s)) := by
  intro hforall
  exact
    fullExactVisibleRuleFamily_not_finitePredictorCover_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) hs
      (hforall (Index := ExactVisibleRule Z k) (fullExactVisibleRuleFamily Z k))

/-- Therefore the bare exact-visible family interface cannot imply the clocked
finite-learning payload for every switched family. -/
theorem currentExactVisibleInterface_not_forall_clockedKpolyFiniteLearningPayload_of_lt_surfaceCard
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (∀ {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index),
        ClockedKpolyFiniteLearningPayload G s clock) := by
  intro hforall
  exact
    fullExactVisibleRuleFamily_not_clockedKpolyFiniteLearningPayload_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) (clock := clock) hs
      (hforall (Index := ExactVisibleRule Z k) (fullExactVisibleRuleFamily Z k))

end CurrentInterfaceObstruction

end Mettapedia.Computability.PNP
