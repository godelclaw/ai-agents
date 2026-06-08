import Mettapedia.Computability.PNP.BitVecZABCompressionObstruction
import Mettapedia.Computability.PNP.CanonicalZABERMInterface

/-!
# P vs NP crux: canonical exact `(zfeat(z), a, b)` routes still face truth-table explosion

This file specializes the exact visible compression obstruction to the
canonical exact `z+a+b` route on `BitVec n`.

Even after fixing one extractor `zfeat : BitVec n → BitVec r` and even after
choosing the class by ERM, surjectivity onto the full exact rule class still
has to pay for the full exact visible surface on `BitVec n`.

So any canonical exact route with budget `r + 2k + 1` can only be surjective if
that budget already reaches the truth-table threshold `2^(n + 2k)`.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {n r k : ℕ} {Index : Type*}

/-- A canonical exact `(zfeat(z), a, b)` candidate on `BitVec n` still has to
pay the full exact visible surface cardinality `2^(n + 2k)` if it were
surjective. -/
theorem CanonicalZABDecisionListCandidateData.bitVecSurfaceCard_le_of_surjective_predict
    {zfeat : BitVec n → BitVec r}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    (h :
      CanonicalZABDecisionListCandidateData
        (Z := BitVec n) (r := r) (k := k) (Index := Index) zfeat G)
    (hsurj : Function.Surjective G.predict) :
    2 ^ (n + 2 * k) ≤ r + 2 * k + 1 := by
  exact
    exactVisibleCompressionTarget_bitVecSurfaceCard_le_of_surjective_predict
      (r := n) (k := k) (s := r + 2 * k + 1) (Index := Index)
      hsurj h.compressionTarget

/-- Therefore any canonical exact `(zfeat(z), a, b)` candidate with budget
below the full exact-surface threshold cannot be surjective. -/
theorem CanonicalZABDecisionListCandidateData.not_surjective_predict_of_budget_lt
    {zfeat : BitVec n → BitVec r}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    (h :
      CanonicalZABDecisionListCandidateData
        (Z := BitVec n) (r := r) (k := k) (Index := Index) zfeat G)
    (hbudget : r + 2 * k + 1 < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective G.predict := by
  intro hsurj
  exact Nat.not_le_of_lt hbudget <|
    h.bitVecSurfaceCard_le_of_surjective_predict hsurj

/-- When the extractor keeps at most `n` bits, the canonical exact budget
`r + 2k + 1` is still below the full `BitVec n` truth-table threshold as soon
as the raw visible width `n + 2k` is at least `2`. -/
theorem canonicalZABDecisionListBudget_lt_bitVecTruthTable_of_le_of_two_le
    (hproj : r ≤ n)
    (hwidth : 2 ≤ n + 2 * k) :
    r + 2 * k + 1 < 2 ^ (n + 2 * k) := by
  have hle : r + 2 * k + 1 ≤ n + 2 * k + 1 := by
    omega
  exact lt_of_le_of_lt hle <|
    exactZABDecisionListBudget_lt_bitVecTruthTable_of_two_le
      (r := n) (k := k) hwidth

/-- Hence a canonical exact `(zfeat(z), a, b)` candidate on `BitVec n)` cannot
be surjective once `r ≤ n` and the full exact visible width `n + 2k` is at
least `2`. -/
theorem CanonicalZABDecisionListCandidateData.not_surjective_predict_of_le_of_two_le
    {zfeat : BitVec n → BitVec r}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    (h :
      CanonicalZABDecisionListCandidateData
        (Z := BitVec n) (r := r) (k := k) (Index := Index) zfeat G)
    (hproj : r ≤ n)
    (hwidth : 2 ≤ n + 2 * k) :
    ¬ Function.Surjective G.predict := by
  exact
    h.not_surjective_predict_of_budget_lt
      (canonicalZABDecisionListBudget_lt_bitVecTruthTable_of_le_of_two_le
        (n := n) (r := r) (k := k) hproj hwidth)

/-- The same contradiction applies to the canonical recovery wrapper, since it
already packages the same exact compression target. -/
theorem CanonicalZABDecisionListRecoveryData.not_surjective_predict_of_budget_lt
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {zfeat : BitVec n → BitVec r}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      CanonicalZABDecisionListRecoveryData
        (Z := BitVec n) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hbudget : r + 2 * k + 1 < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective G.predict := by
  exact h.candidateData.not_surjective_predict_of_budget_lt hbudget

/-- Likewise under the natural width hypotheses `r ≤ n` and `2 ≤ n + 2k`. -/
theorem CanonicalZABDecisionListRecoveryData.not_surjective_predict_of_le_of_two_le
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {zfeat : BitVec n → BitVec r}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      CanonicalZABDecisionListRecoveryData
        (Z := BitVec n) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hproj : r ≤ n)
    (hwidth : 2 ≤ n + 2 * k) :
    ¬ Function.Surjective G.predict := by
  exact h.candidateData.not_surjective_predict_of_le_of_two_le hproj hwidth

/-- The same exact-surface lower bound for the named canonical exact ERM family
wrapper itself. -/
theorem canonicalZABDecisionListERMFamily_bitVecSurfaceCard_le_of_surjective_predict
    (zfeat : BitVec n → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool)
    (hsurj :
      Function.Surjective
        (exactZABDecisionListERMFamily
          (Z := BitVec n) (r := r) (k := k) zfeat samples).predict) :
    2 ^ (n + 2 * k) ≤ r + 2 * k + 1 := by
  exact
    (canonicalZABDecisionListERMCandidateData
      (Z := BitVec n) (r := r) (k := k) (Index := Index) zfeat samples).bitVecSurfaceCard_le_of_surjective_predict
      hsurj

/-- Therefore the named canonical exact ERM family cannot be surjective once
its linear budget sits below the full exact-surface threshold. -/
theorem canonicalZABDecisionListERMFamily_not_surjective_of_budget_lt
    (zfeat : BitVec n → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool)
    (hbudget : r + 2 * k + 1 < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective
        (exactZABDecisionListERMFamily
          (Z := BitVec n) (r := r) (k := k) zfeat samples).predict := by
  intro hsurj
  exact Nat.not_le_of_lt hbudget <|
    canonicalZABDecisionListERMFamily_bitVecSurfaceCard_le_of_surjective_predict
      (n := n) (r := r) (k := k) (Index := Index) zfeat samples hsurj

/-- In particular, the canonical exact ERM family itself cannot be surjective
once `r ≤ n` and the full exact visible width `n + 2k` is at least `2`. -/
theorem canonicalZABDecisionListERMFamily_not_surjective_of_le_of_two_le
    (zfeat : BitVec n → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool)
    (hproj : r ≤ n)
    (hwidth : 2 ≤ n + 2 * k) :
    ¬ Function.Surjective
        (exactZABDecisionListERMFamily
          (Z := BitVec n) (r := r) (k := k) zfeat samples).predict := by
  exact
    canonicalZABDecisionListERMFamily_not_surjective_of_budget_lt
      (n := n) (r := r) (k := k) (Index := Index) zfeat samples
      (canonicalZABDecisionListBudget_lt_bitVecTruthTable_of_le_of_two_le
        (n := n) (r := r) (k := k) hproj hwidth)

/-- The final canonical exact ERM recovery interface inherits the same
budget-threshold obstruction. -/
theorem CanonicalZABERMRecoveryData.not_surjective_predict_of_budget_lt
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {zfeat : BitVec n → BitVec r}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      CanonicalZABERMRecoveryData
        (Z := BitVec n) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hbudget : r + 2 * k + 1 < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective G.predict := by
  exact h.candidateData.not_surjective_predict_of_budget_lt hbudget

/-- And likewise once `r ≤ n` and the full exact visible width `n + 2k` is at
least `2`. -/
theorem CanonicalZABERMRecoveryData.not_surjective_predict_of_le_of_two_le
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {zfeat : BitVec n → BitVec r}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      CanonicalZABERMRecoveryData
        (Z := BitVec n) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hproj : r ≤ n)
    (hwidth : 2 ≤ n + 2 * k) :
    ¬ Function.Surjective G.predict := by
  exact h.candidateData.not_surjective_predict_of_le_of_two_le hproj hwidth

end

end Mettapedia.Computability.PNP
