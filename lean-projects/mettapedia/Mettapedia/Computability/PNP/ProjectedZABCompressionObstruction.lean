import Mettapedia.Computability.PNP.BitVecZABCompressionObstruction
import Mettapedia.Computability.PNP.ProjectedZABERMInterface
import Mathlib.Tactic

/-!
# P vs NP crux: projected exact `(z, a, b)` routes still face the full surface size

This file specializes the exact visible compression obstruction to projected
extractors `BitVec n → BitVec r`.

Even if the route only looks at `r` chosen coordinates of `z`, the underlying
exact manuscript-visible surface is still the full `(z, a, b)` surface on
`BitVec n`.  So any surjective projected route must still pay the full
truth-table threshold `2^(n + 2k)`.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {n r k : ℕ} {Index : Type*}

/-- A projected exact `(z, a, b)` ERM route on `BitVec n` still has to pay the
full exact visible surface cardinality `2^(n + 2k)` if it were surjective. -/
theorem projectedZABERMFamily_bitVecSurfaceCard_le_of_surjective_predict
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {coords : Fin r → Fin n}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h : ProjectedZABERMRecoveryData
      (n := n) (r := r) (k := k) (Index := Index) μ coords G q)
    (hsurj : Function.Surjective G.predict) :
    2 ^ (n + 2 * k) ≤ r + 2 * k + 1 := by
  exact
    exactVisibleCompressionTarget_bitVecSurfaceCard_le_of_surjective_predict
      (r := n) (k := k) (s := r + 2 * k + 1) (Index := Index)
      hsurj h.compressionTarget

/-- The same exact-surface lower bound for the named projected ERM family
wrapper itself. -/
theorem projectedZABDecisionListERMFamily_bitVecSurfaceCard_le_of_surjective_predict
    (coords : Fin r → Fin n)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool)
    (hsurj :
      Function.Surjective
        (projectedZABDecisionListERMFamily
          (n := n) (r := r) (k := k) (Index := Index) coords samples).predict) :
    2 ^ (n + 2 * k) ≤ r + 2 * k + 1 := by
  exact
    exactVisibleCompressionTarget_bitVecSurfaceCard_le_of_surjective_predict
      (r := n) (k := k) (s := r + 2 * k + 1) (Index := Index)
      hsurj
      (projectedZABDecisionListERMCompressionTarget
        (n := n) (r := r) (k := k) (Index := Index) coords samples)

/-- If the projected route budget is already known to sit below the full
`BitVec n` truth-table threshold, then surjectivity onto the full exact rule
class is impossible. -/
theorem ProjectedZABERMRecoveryData.not_surjective_predict_of_budget_lt
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {coords : Fin r → Fin n}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h : ProjectedZABERMRecoveryData
      (n := n) (r := r) (k := k) (Index := Index) μ coords G q)
    (hbudget : r + 2 * k + 1 < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective G.predict := by
  intro hsurj
  exact Nat.not_le_of_lt hbudget <|
    projectedZABERMFamily_bitVecSurfaceCard_le_of_surjective_predict
      (n := n) (r := r) (k := k) (Index := Index) h hsurj

/-- Direct family-level non-surjectivity once the projected linear budget is
known to fall below the full `BitVec n` truth-table threshold. -/
theorem projectedZABDecisionListERMFamily_not_surjective_of_budget_lt
    (coords : Fin r → Fin n)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool)
    (hbudget : r + 2 * k + 1 < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective
        (projectedZABDecisionListERMFamily
          (n := n) (r := r) (k := k) (Index := Index) coords samples).predict := by
  intro hsurj
  exact Nat.not_le_of_lt hbudget <|
    projectedZABDecisionListERMFamily_bitVecSurfaceCard_le_of_surjective_predict
      (n := n) (r := r) (k := k) (Index := Index) coords samples hsurj

/-- When the projected extractor keeps at most `n` coordinates, the linear
budget `r + 2k + 1` is still below the full `BitVec n` truth-table threshold as
soon as the raw visible width `n + 2k` is at least `2`. -/
theorem projectedZABDecisionListBudget_lt_bitVecTruthTable_of_le_of_two_le
    (hproj : r ≤ n)
    (hwidth : 2 ≤ n + 2 * k) :
    r + 2 * k + 1 < 2 ^ (n + 2 * k) := by
  have hle : r + 2 * k + 1 ≤ n + 2 * k + 1 := by
    omega
  exact lt_of_le_of_lt hle <|
    exactZABDecisionListBudget_lt_bitVecTruthTable_of_two_le
      (r := n) (k := k) hwidth

/-- Hence a projected exact `(z, a, b)` ERM route cannot be surjective once
`r ≤ n` and the full raw visible width `n + 2k` is at least `2`. -/
theorem ProjectedZABERMRecoveryData.not_surjective_predict_of_le_of_two_le
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {coords : Fin r → Fin n}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h : ProjectedZABERMRecoveryData
      (n := n) (r := r) (k := k) (Index := Index) μ coords G q)
    (hproj : r ≤ n)
    (hwidth : 2 ≤ n + 2 * k) :
    ¬ Function.Surjective G.predict := by
  exact
    h.not_surjective_predict_of_budget_lt
      (projectedZABDecisionListBudget_lt_bitVecTruthTable_of_le_of_two_le
        (n := n) (r := r) (k := k) hproj hwidth)

/-- Hence the named projected ERM family itself cannot be surjective under the
same natural width hypotheses `r ≤ n` and `2 ≤ n + 2k`. -/
theorem projectedZABDecisionListERMFamily_not_surjective_of_le_of_two_le
    (coords : Fin r → Fin n)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool)
    (hproj : r ≤ n)
    (hwidth : 2 ≤ n + 2 * k) :
    ¬ Function.Surjective
        (projectedZABDecisionListERMFamily
          (n := n) (r := r) (k := k) (Index := Index) coords samples).predict := by
  exact
    projectedZABDecisionListERMFamily_not_surjective_of_budget_lt
      (n := n) (r := r) (k := k) (Index := Index) coords samples
      (projectedZABDecisionListBudget_lt_bitVecTruthTable_of_le_of_two_le
        (n := n) (r := r) (k := k) hproj hwidth)

end

end Mettapedia.Computability.PNP
