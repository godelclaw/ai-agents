import Mettapedia.Computability.PNP.BitVecZABCompressionObstruction
import Mettapedia.Computability.PNP.ExactABERMInterface

/-!
# P vs NP crux: exact raw `(a, b)` affine-family routes still face truth-table explosion

This file specializes the exact visible compression obstruction to the
non-shared exact raw `(a, b)` affine-family route on `BitVec n`.

Even after passing to the exact raw visible bits `(a, b)`, any surjective route
still has to pay for the full exact visible surface on `BitVec n`.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {n r k : ℕ} {Index : Type*}

theorem ExactABAffineFeatureTargetData.bitVecSurfaceCard_le_of_surjective_predict
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    (h :
      ExactABAffineFeatureTargetData
        (Z := BitVec n) (r := r) (k := k) (Index := Index) G)
    (hsurj : Function.Surjective G.predict) :
    2 ^ (n + 2 * k) ≤ r * ((k + k) + 1) + 2 ^ r := by
  exact
    exactVisibleCompressionTarget_bitVecSurfaceCard_le_of_surjective_predict
      (r := n) (k := k) (s := r * ((k + k) + 1) + 2 ^ r) (Index := Index)
      hsurj h.compressionTarget

theorem ExactABAffineFeatureTargetData.not_surjective_predict_of_budget_lt
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    (h :
      ExactABAffineFeatureTargetData
        (Z := BitVec n) (r := r) (k := k) (Index := Index) G)
    (hbudget : r * ((k + k) + 1) + 2 ^ r < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective G.predict := by
  intro hsurj
  exact Nat.not_le_of_lt hbudget <|
    h.bitVecSurfaceCard_le_of_surjective_predict hsurj

theorem ExactABAffineFeatureRecoveryData.bitVecSurfaceCard_le_of_surjective_predict
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      ExactABAffineFeatureRecoveryData
        (Z := BitVec n) (r := r) (k := k) (Index := Index) μ G q)
    (hsurj : Function.Surjective G.predict) :
    2 ^ (n + 2 * k) ≤ r * ((k + k) + 1) + 2 ^ r := by
  exact h.targetData.bitVecSurfaceCard_le_of_surjective_predict hsurj

theorem ExactABAffineFeatureRecoveryData.not_surjective_predict_of_budget_lt
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      ExactABAffineFeatureRecoveryData
        (Z := BitVec n) (r := r) (k := k) (Index := Index) μ G q)
    (hbudget : r * ((k + k) + 1) + 2 ^ r < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective G.predict := by
  exact h.targetData.not_surjective_predict_of_budget_lt hbudget

theorem exactABAffineFeatureERMFamily_bitVecSurfaceCard_le_of_surjective_predict
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool)
    (hsurj :
      Function.Surjective
        (exactABAffineFeatureERMFamily
          (Z := BitVec n) (r := r) (k := k) samples).predict) :
    2 ^ (n + 2 * k) ≤ r * ((k + k) + 1) + 2 ^ r := by
  exact
    (exactABAffineFeatureERMTargetData
      (Z := BitVec n) (r := r) (k := k) (Index := Index) samples).bitVecSurfaceCard_le_of_surjective_predict
      hsurj

theorem exactABAffineFeatureERMFamily_not_surjective_of_budget_lt
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool)
    (hbudget : r * ((k + k) + 1) + 2 ^ r < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective
        (exactABAffineFeatureERMFamily
          (Z := BitVec n) (r := r) (k := k) samples).predict := by
  intro hsurj
  exact Nat.not_le_of_lt hbudget <|
    exactABAffineFeatureERMFamily_bitVecSurfaceCard_le_of_surjective_predict
      (n := n) (r := r) (k := k) (Index := Index) samples hsurj

theorem ExactABAffineFeatureERMRecoveryData.not_surjective_predict_of_budget_lt
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      ExactABAffineFeatureERMRecoveryData
        (Z := BitVec n) (r := r) (k := k) (Index := Index) μ G q)
    (hbudget : r * ((k + k) + 1) + 2 ^ r < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective G.predict := by
  exact h.targetData.not_surjective_predict_of_budget_lt hbudget

theorem ExactABSparseThresholdTargetData.bitVecSurfaceCard_le_of_surjective_predict
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    (h :
      ExactABSparseThresholdTargetData
        (Z := BitVec n) (r := r) (k := k) (Index := Index) G)
    (hsurj : Function.Surjective G.predict) :
    2 ^ (n + 2 * k) ≤ r * ((k + k) + 3) := by
  exact
    exactVisibleCompressionTarget_bitVecSurfaceCard_le_of_surjective_predict
      (r := n) (k := k) (s := r * ((k + k) + 3)) (Index := Index)
      hsurj h.compressionTarget

theorem ExactABSparseThresholdTargetData.not_surjective_predict_of_budget_lt
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    (h :
      ExactABSparseThresholdTargetData
        (Z := BitVec n) (r := r) (k := k) (Index := Index) G)
    (hbudget : r * ((k + k) + 3) < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective G.predict := by
  intro hsurj
  exact Nat.not_le_of_lt hbudget <|
    h.bitVecSurfaceCard_le_of_surjective_predict hsurj

theorem ExactABSparseThresholdRecoveryData.bitVecSurfaceCard_le_of_surjective_predict
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      ExactABSparseThresholdRecoveryData
        (Z := BitVec n) (r := r) (k := k) (Index := Index) μ G q)
    (hsurj : Function.Surjective G.predict) :
    2 ^ (n + 2 * k) ≤ r * ((k + k) + 3) := by
  exact h.targetData.bitVecSurfaceCard_le_of_surjective_predict hsurj

theorem ExactABSparseThresholdRecoveryData.not_surjective_predict_of_budget_lt
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      ExactABSparseThresholdRecoveryData
        (Z := BitVec n) (r := r) (k := k) (Index := Index) μ G q)
    (hbudget : r * ((k + k) + 3) < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective G.predict := by
  exact h.targetData.not_surjective_predict_of_budget_lt hbudget

theorem exactABSparseThresholdAffineERMFamily_bitVecSurfaceCard_le_of_surjective_predict
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool)
    (hsurj :
      Function.Surjective
        (exactABSparseThresholdAffineERMFamily
          (Z := BitVec n) (r := r) (k := k) samples).predict) :
    2 ^ (n + 2 * k) ≤ r * ((k + k) + 3) := by
  exact
    (exactABSparseThresholdAffineERMTargetData
      (Z := BitVec n) (r := r) (k := k) (Index := Index) samples).bitVecSurfaceCard_le_of_surjective_predict
      hsurj

theorem exactABSparseThresholdAffineERMFamily_not_surjective_of_budget_lt
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool)
    (hbudget : r * ((k + k) + 3) < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective
        (exactABSparseThresholdAffineERMFamily
          (Z := BitVec n) (r := r) (k := k) samples).predict := by
  intro hsurj
  exact Nat.not_le_of_lt hbudget <|
    exactABSparseThresholdAffineERMFamily_bitVecSurfaceCard_le_of_surjective_predict
      (n := n) (r := r) (k := k) (Index := Index) samples hsurj

theorem ExactABSparseThresholdERMRecoveryData.not_surjective_predict_of_budget_lt
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      ExactABSparseThresholdERMRecoveryData
        (Z := BitVec n) (r := r) (k := k) (Index := Index) μ G q)
    (hbudget : r * ((k + k) + 3) < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective G.predict := by
  exact h.targetData.not_surjective_predict_of_budget_lt hbudget

theorem ExactABAffineDecisionListTargetData.bitVecSurfaceCard_le_of_surjective_predict
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    (h :
      ExactABAffineDecisionListTargetData
        (Z := BitVec n) (r := r) (k := k) (Index := Index) G)
    (hsurj : Function.Surjective G.predict) :
    2 ^ (n + 2 * k) ≤ r * ((k + k) + 2) + 1 := by
  exact
    exactVisibleCompressionTarget_bitVecSurfaceCard_le_of_surjective_predict
      (r := n) (k := k) (s := r * ((k + k) + 2) + 1) (Index := Index)
      hsurj h.compressionTarget

theorem ExactABAffineDecisionListTargetData.not_surjective_predict_of_budget_lt
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    (h :
      ExactABAffineDecisionListTargetData
        (Z := BitVec n) (r := r) (k := k) (Index := Index) G)
    (hbudget : r * ((k + k) + 2) + 1 < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective G.predict := by
  intro hsurj
  exact Nat.not_le_of_lt hbudget <|
    h.bitVecSurfaceCard_le_of_surjective_predict hsurj

theorem ExactABAffineDecisionListRecoveryData.bitVecSurfaceCard_le_of_surjective_predict
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      ExactABAffineDecisionListRecoveryData
        (Z := BitVec n) (r := r) (k := k) (Index := Index) μ G q)
    (hsurj : Function.Surjective G.predict) :
    2 ^ (n + 2 * k) ≤ r * ((k + k) + 2) + 1 := by
  exact h.targetData.bitVecSurfaceCard_le_of_surjective_predict hsurj

theorem ExactABAffineDecisionListRecoveryData.not_surjective_predict_of_budget_lt
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      ExactABAffineDecisionListRecoveryData
        (Z := BitVec n) (r := r) (k := k) (Index := Index) μ G q)
    (hbudget : r * ((k + k) + 2) + 1 < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective G.predict := by
  exact h.targetData.not_surjective_predict_of_budget_lt hbudget

theorem exactABAffineDecisionListERMFamily_bitVecSurfaceCard_le_of_surjective_predict
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool)
    (hsurj :
      Function.Surjective
        (exactABAffineDecisionListERMFamily
          (Z := BitVec n) (r := r) (k := k) samples).predict) :
    2 ^ (n + 2 * k) ≤ r * ((k + k) + 2) + 1 := by
  exact
    (exactABAffineDecisionListERMTargetData
      (Z := BitVec n) (r := r) (k := k) (Index := Index) samples).bitVecSurfaceCard_le_of_surjective_predict
      hsurj

theorem exactABAffineDecisionListERMFamily_not_surjective_of_budget_lt
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool)
    (hbudget : r * ((k + k) + 2) + 1 < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective
        (exactABAffineDecisionListERMFamily
          (Z := BitVec n) (r := r) (k := k) samples).predict := by
  intro hsurj
  exact Nat.not_le_of_lt hbudget <|
    exactABAffineDecisionListERMFamily_bitVecSurfaceCard_le_of_surjective_predict
      (n := n) (r := r) (k := k) (Index := Index) samples hsurj

theorem ExactABAffineDecisionListERMRecoveryData.not_surjective_predict_of_budget_lt
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      ExactABAffineDecisionListERMRecoveryData
        (Z := BitVec n) (r := r) (k := k) (Index := Index) μ G q)
    (hbudget : r * ((k + k) + 2) + 1 < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective G.predict := by
  exact h.targetData.not_surjective_predict_of_budget_lt hbudget

end

end Mettapedia.Computability.PNP
