import Mettapedia.Computability.PNP.BitVecZABCompressionObstruction
import Mettapedia.Computability.PNP.CanonicalABERMInterface

/-!
# P vs NP crux: canonical raw `(a, b)` routes still face truth-table explosion

This file specializes the exact visible compression obstruction to the
canonical raw `(a, b)` route on `BitVec n`.

Even after quotienting through the raw visible `(a, b)` surface and even after
choosing the class by ERM, surjectivity onto the full exact rule class still
has to pay for the full exact visible surface on `BitVec n`.

So any canonical raw `(a, b)` route with budget `2k + 1` can only be
surjective if `2k + 1` already reaches the truth-table threshold
`2^(n + 2k)`.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {n k : ℕ} {Index : Type*}

/-- A canonical raw `(a, b)` candidate on `BitVec n` still has to pay the full
exact visible surface cardinality `2^(n + 2k)` if it were surjective. -/
theorem CanonicalABDecisionListCandidateData.bitVecSurfaceCard_le_of_surjective_predict
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    (h :
      CanonicalABDecisionListCandidateData
        (Z := BitVec n) (k := k) (Index := Index) G)
    (hsurj : Function.Surjective G.predict) :
    2 ^ (n + 2 * k) ≤ 2 * k + 1 := by
  exact
    exactVisibleCompressionTarget_bitVecSurfaceCard_le_of_surjective_predict
      (r := n) (k := k) (s := 2 * k + 1) (Index := Index)
      hsurj h.compressionTarget

/-- Therefore any canonical raw `(a, b)` candidate with budget below the full
exact-surface threshold cannot be surjective. -/
theorem CanonicalABDecisionListCandidateData.not_surjective_predict_of_budget_lt
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    (h :
      CanonicalABDecisionListCandidateData
        (Z := BitVec n) (k := k) (Index := Index) G)
    (hbudget : 2 * k + 1 < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective G.predict := by
  intro hsurj
  exact Nat.not_le_of_lt hbudget <|
    h.bitVecSurfaceCard_le_of_surjective_predict hsurj

/-- The canonical raw `(a, b)` budget `2k + 1` is strictly below the full
`BitVec n` truth-table threshold as soon as the raw visible width `n + 2k` is
at least `2`. -/
theorem canonicalABDecisionListBudget_lt_bitVecTruthTable_of_two_le
    (hwidth : 2 ≤ n + 2 * k) :
    2 * k + 1 < 2 ^ (n + 2 * k) := by
  have hle : 2 * k + 1 ≤ n + 2 * k + 1 := by
    exact Nat.succ_le_succ (Nat.le_add_left (2 * k) n)
  exact lt_of_le_of_lt hle <|
    exactZABDecisionListBudget_lt_bitVecTruthTable_of_two_le
      (r := n) (k := k) hwidth

/-- Hence a canonical raw `(a, b)` candidate on `BitVec n` cannot be surjective
once the full exact visible width `n + 2k` is at least `2`. -/
theorem CanonicalABDecisionListCandidateData.not_surjective_predict_of_two_le
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    (h :
      CanonicalABDecisionListCandidateData
        (Z := BitVec n) (k := k) (Index := Index) G)
    (hwidth : 2 ≤ n + 2 * k) :
    ¬ Function.Surjective G.predict := by
  exact
    h.not_surjective_predict_of_budget_lt
      (canonicalABDecisionListBudget_lt_bitVecTruthTable_of_two_le
        (n := n) (k := k) hwidth)

/-- The same contradiction applies to the canonical recovery wrapper, since it
already packages the same exact compression target. -/
theorem CanonicalABDecisionListRecoveryData.not_surjective_predict_of_budget_lt
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      CanonicalABDecisionListRecoveryData
        (Z := BitVec n) (k := k) (Index := Index) μ G q)
    (hbudget : 2 * k + 1 < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective G.predict := by
  exact h.candidateData.not_surjective_predict_of_budget_lt hbudget

/-- Likewise under the natural width hypothesis `2 ≤ n + 2k`. -/
theorem CanonicalABDecisionListRecoveryData.not_surjective_predict_of_two_le
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      CanonicalABDecisionListRecoveryData
        (Z := BitVec n) (k := k) (Index := Index) μ G q)
    (hwidth : 2 ≤ n + 2 * k) :
    ¬ Function.Surjective G.predict := by
  exact h.candidateData.not_surjective_predict_of_two_le hwidth

/-- The same exact-surface lower bound for the named canonical raw `(a, b)` ERM
family wrapper itself. -/
theorem canonicalABDecisionListERMFamily_bitVecSurfaceCard_le_of_surjective_predict
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool)
    (hsurj :
      Function.Surjective
        (canonicalABDecisionListERMFamily
          (Z := BitVec n) (k := k) samples).predict) :
    2 ^ (n + 2 * k) ≤ 2 * k + 1 := by
  exact
    (canonicalABDecisionListERMCandidateData
      (Z := BitVec n) (k := k) (Index := Index) samples).bitVecSurfaceCard_le_of_surjective_predict
      hsurj

/-- Therefore the named canonical raw `(a, b)` ERM family cannot be surjective
once its budget sits below the full exact-surface threshold. -/
theorem canonicalABDecisionListERMFamily_not_surjective_of_budget_lt
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool)
    (hbudget : 2 * k + 1 < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective
        (canonicalABDecisionListERMFamily
          (Z := BitVec n) (k := k) samples).predict := by
  intro hsurj
  exact Nat.not_le_of_lt hbudget <|
    canonicalABDecisionListERMFamily_bitVecSurfaceCard_le_of_surjective_predict
      (n := n) (k := k) (Index := Index) samples hsurj

/-- In particular, the canonical raw `(a, b)` ERM family itself cannot be
surjective once the full exact visible width `n + 2k` is at least `2`. -/
theorem canonicalABDecisionListERMFamily_not_surjective_of_two_le
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool)
    (hwidth : 2 ≤ n + 2 * k) :
    ¬ Function.Surjective
        (canonicalABDecisionListERMFamily
          (Z := BitVec n) (k := k) samples).predict := by
  exact
    canonicalABDecisionListERMFamily_not_surjective_of_budget_lt
      (n := n) (k := k) (Index := Index) samples
      (canonicalABDecisionListBudget_lt_bitVecTruthTable_of_two_le
        (n := n) (k := k) hwidth)

/-- The final canonical raw `(a, b)` ERM recovery interface inherits the same
budget-threshold obstruction. -/
theorem CanonicalABERMRecoveryData.not_surjective_predict_of_budget_lt
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      CanonicalABERMRecoveryData
        (Z := BitVec n) (k := k) (Index := Index) μ G q)
    (hbudget : 2 * k + 1 < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective G.predict := by
  exact h.candidateData.not_surjective_predict_of_budget_lt hbudget

/-- And likewise once the full exact visible width `n + 2k` is at least `2`. -/
theorem CanonicalABERMRecoveryData.not_surjective_predict_of_two_le
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      CanonicalABERMRecoveryData
        (Z := BitVec n) (k := k) (Index := Index) μ G q)
    (hwidth : 2 ≤ n + 2 * k) :
    ¬ Function.Surjective G.predict := by
  exact h.candidateData.not_surjective_predict_of_two_le hwidth

end

end Mettapedia.Computability.PNP
