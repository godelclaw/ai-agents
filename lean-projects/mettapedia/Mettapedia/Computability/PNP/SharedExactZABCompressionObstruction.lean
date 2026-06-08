import Mettapedia.Computability.PNP.BitVecZABCompressionObstruction
import Mettapedia.Computability.PNP.SharedExactZABRecoveryInterface
import Mettapedia.Computability.PNP.SharedExactZABFeatureERMInterface
import Mettapedia.Computability.PNP.SharedExactZABERMInterface

/-!
# P vs NP crux: shared-basis exact `(zfeat(z), a, b)` routes still face truth-table explosion

This file specializes the exact visible compression obstruction to the
shared-basis exact `z+a+b` route on `BitVec n`.

Even if the switched family is represented only through one fixed shared affine
basis on the extracted visible bits `(zfeat(z), a, b)`, surjectivity onto the
full exact rule class still has to pay for the full exact visible surface on
`BitVec n`.

So any shared-basis exact route with budget `p + 1` can only be surjective if
`p + 1` already reaches the truth-table threshold `2^(n + 2k)`.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {n p r k : ℕ} {Index : Type*}

/-- A shared-basis exact `(zfeat(z), a, b)` affine-feature target on `BitVec n`
still has to pay the full exact visible surface cardinality `2^(n + 2k)` if it
were surjective. -/
theorem SharedExactZABAffineFeatureTargetData.bitVecSurfaceCard_le_of_surjective_predict
    {zfeat : BitVec n → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    (h :
      SharedExactZABAffineFeatureTargetData
        (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index)
        zfeat features G)
    (hsurj : Function.Surjective G.predict) :
    2 ^ (n + 2 * k) ≤ 2 ^ p := by
  exact
    exactVisibleCompressionTarget_bitVecSurfaceCard_le_of_surjective_predict
      (r := n) (k := k) (s := 2 ^ p) (Index := Index)
      hsurj h.compressionTarget

/-- Hence any shared-basis exact `(zfeat(z), a, b)` affine-feature target
cannot be surjective once its exponential feature budget sits below the full
exact-surface threshold. -/
theorem SharedExactZABAffineFeatureTargetData.not_surjective_predict_of_budget_lt
    {zfeat : BitVec n → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    (h :
      SharedExactZABAffineFeatureTargetData
        (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index)
        zfeat features G)
    (hbudget : 2 ^ p < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective G.predict := by
  intro hsurj
  exact Nat.not_le_of_lt hbudget <|
    h.bitVecSurfaceCard_le_of_surjective_predict hsurj

/-- In particular, a shared-basis exact `(zfeat(z), a, b)` affine-feature
target cannot be surjective whenever its shared affine width is strictly
smaller than the full exact visible width. -/
theorem SharedExactZABAffineFeatureTargetData.not_surjective_predict_of_lt_visibleWidth
    {zfeat : BitVec n → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    (h :
      SharedExactZABAffineFeatureTargetData
        (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index)
        zfeat features G)
    (hfeat : p < n + 2 * k) :
    ¬ Function.Surjective G.predict := by
  exact
    h.not_surjective_predict_of_budget_lt
      (Nat.pow_lt_pow_right Nat.one_lt_two hfeat)

/-- A shared-basis exact `(zfeat(z), a, b)` sparse-threshold target on
`BitVec n` still has to pay the full exact visible surface cardinality
`2^(n + 2k)` if it were surjective. -/
theorem SharedExactZABSparseThresholdTargetData.bitVecSurfaceCard_le_of_surjective_predict
    {zfeat : BitVec n → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    (h :
      SharedExactZABSparseThresholdTargetData
        (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index)
        zfeat features G)
    (hsurj : Function.Surjective G.predict) :
    2 ^ (n + 2 * k) ≤ 2 * p := by
  exact
    exactVisibleCompressionTarget_bitVecSurfaceCard_le_of_surjective_predict
      (r := n) (k := k) (s := 2 * p) (Index := Index)
      hsurj h.compressionTarget

/-- Hence any shared-basis exact `(zfeat(z), a, b)` sparse-threshold target
cannot be surjective once its linear threshold budget sits below the full
exact-surface threshold. -/
theorem SharedExactZABSparseThresholdTargetData.not_surjective_predict_of_budget_lt
    {zfeat : BitVec n → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    (h :
      SharedExactZABSparseThresholdTargetData
        (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index)
        zfeat features G)
    (hbudget : 2 * p < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective G.predict := by
  intro hsurj
  exact Nat.not_le_of_lt hbudget <|
    h.bitVecSurfaceCard_le_of_surjective_predict hsurj

/-- The shared-basis exact `(zfeat(z), a, b)` affine-feature recovery interface
inherits the same exact-surface lower bound on `BitVec n`. -/
theorem SharedExactZABAffineFeatureRecoveryData.bitVecSurfaceCard_le_of_surjective_predict
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {zfeat : BitVec n → BitVec r}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABAffineFeatureRecoveryData
        (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hsurj : Function.Surjective G.predict) :
    2 ^ (n + 2 * k) ≤ 2 ^ p := by
  exact h.targetData.bitVecSurfaceCard_le_of_surjective_predict hsurj

/-- Hence the shared-basis exact `(zfeat(z), a, b)` affine-feature recovery
interface cannot be surjective once its exponential feature budget sits below
the full exact-surface threshold. -/
theorem SharedExactZABAffineFeatureRecoveryData.not_surjective_predict_of_budget_lt
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {zfeat : BitVec n → BitVec r}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABAffineFeatureRecoveryData
        (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hbudget : 2 ^ p < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective G.predict := by
  exact h.targetData.not_surjective_predict_of_budget_lt hbudget

/-- In particular, the shared-basis exact `(zfeat(z), a, b)` affine-feature
recovery interface cannot be surjective when its shared affine width is
strictly smaller than the full exact visible width. -/
theorem SharedExactZABAffineFeatureRecoveryData.not_surjective_predict_of_lt_visibleWidth
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {zfeat : BitVec n → BitVec r}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABAffineFeatureRecoveryData
        (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hfeat : p < n + 2 * k) :
    ¬ Function.Surjective G.predict := by
  exact h.targetData.not_surjective_predict_of_lt_visibleWidth hfeat

/-- The shared-basis exact `(zfeat(z), a, b)` sparse-threshold recovery
interface inherits the same exact-surface lower bound on `BitVec n`. -/
theorem SharedExactZABSparseThresholdRecoveryData.bitVecSurfaceCard_le_of_surjective_predict
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {zfeat : BitVec n → BitVec r}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABSparseThresholdRecoveryData
        (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hsurj : Function.Surjective G.predict) :
    2 ^ (n + 2 * k) ≤ 2 * p := by
  exact h.targetData.bitVecSurfaceCard_le_of_surjective_predict hsurj

/-- Hence the shared-basis exact `(zfeat(z), a, b)` sparse-threshold recovery
interface cannot be surjective once its linear threshold budget sits below the
full exact-surface threshold. -/
theorem SharedExactZABSparseThresholdRecoveryData.not_surjective_predict_of_budget_lt
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {zfeat : BitVec n → BitVec r}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABSparseThresholdRecoveryData
        (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hbudget : 2 * p < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective G.predict := by
  exact h.targetData.not_surjective_predict_of_budget_lt hbudget

/-- The final shared-basis exact `(zfeat(z), a, b)` affine-feature ERM
interface inherits the same exact-surface lower bound on `BitVec n`. -/
theorem SharedExactZABAffineFeatureERMRecoveryData.bitVecSurfaceCard_le_of_surjective_predict
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {zfeat : BitVec n → BitVec r}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABAffineFeatureERMRecoveryData
        (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hsurj : Function.Surjective G.predict) :
    2 ^ (n + 2 * k) ≤ 2 ^ p := by
  exact h.targetData.bitVecSurfaceCard_le_of_surjective_predict hsurj

/-- Hence the final shared-basis exact `(zfeat(z), a, b)` affine-feature ERM
interface cannot be surjective once its exponential feature budget sits below
the full exact-surface threshold. -/
theorem SharedExactZABAffineFeatureERMRecoveryData.not_surjective_predict_of_budget_lt
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {zfeat : BitVec n → BitVec r}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABAffineFeatureERMRecoveryData
        (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hbudget : 2 ^ p < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective G.predict := by
  exact h.targetData.not_surjective_predict_of_budget_lt hbudget

/-- In particular, the final shared-basis exact `(zfeat(z), a, b)`
affine-feature ERM interface cannot be surjective when its shared affine width
is strictly smaller than the full exact visible width. -/
theorem SharedExactZABAffineFeatureERMRecoveryData.not_surjective_predict_of_lt_visibleWidth
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {zfeat : BitVec n → BitVec r}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABAffineFeatureERMRecoveryData
        (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hfeat : p < n + 2 * k) :
    ¬ Function.Surjective G.predict := by
  exact h.targetData.not_surjective_predict_of_lt_visibleWidth hfeat

/-- The final shared-basis exact `(zfeat(z), a, b)` sparse-threshold ERM
interface inherits the same exact-surface lower bound on `BitVec n`. -/
theorem SharedExactZABSparseThresholdERMRecoveryData.bitVecSurfaceCard_le_of_surjective_predict
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {zfeat : BitVec n → BitVec r}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABSparseThresholdERMRecoveryData
        (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hsurj : Function.Surjective G.predict) :
    2 ^ (n + 2 * k) ≤ 2 * p := by
  exact h.targetData.bitVecSurfaceCard_le_of_surjective_predict hsurj

/-- Hence the final shared-basis exact `(zfeat(z), a, b)` sparse-threshold ERM
interface cannot be surjective once its linear threshold budget sits below the
full exact-surface threshold. -/
theorem SharedExactZABSparseThresholdERMRecoveryData.not_surjective_predict_of_budget_lt
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {zfeat : BitVec n → BitVec r}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABSparseThresholdERMRecoveryData
        (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hbudget : 2 * p < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective G.predict := by
  exact h.targetData.not_surjective_predict_of_budget_lt hbudget

/-- A shared-basis exact `(zfeat(z), a, b)` decision-list target on `BitVec n`
still has to pay the full exact visible surface cardinality `2^(n + 2k)` if it
were surjective. -/
theorem SharedExactZABDecisionListTargetData.bitVecSurfaceCard_le_of_surjective_predict
    {zfeat : BitVec n → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    (h :
      SharedExactZABDecisionListTargetData
        (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index)
        zfeat features G)
    (hsurj : Function.Surjective G.predict) :
    2 ^ (n + 2 * k) ≤ p + 1 := by
  exact
    exactVisibleCompressionTarget_bitVecSurfaceCard_le_of_surjective_predict
      (r := n) (k := k) (s := p + 1) (Index := Index)
      hsurj h.compressionTarget

/-- Hence any shared-basis exact `(zfeat(z), a, b)` target with budget below
the full exact-surface threshold cannot be surjective. -/
theorem SharedExactZABDecisionListTargetData.not_surjective_predict_of_budget_lt
    {zfeat : BitVec n → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    (h :
      SharedExactZABDecisionListTargetData
        (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index)
        zfeat features G)
    (hbudget : p + 1 < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective G.predict := by
  intro hsurj
  exact Nat.not_le_of_lt hbudget <|
    h.bitVecSurfaceCard_le_of_surjective_predict hsurj

/-- A simple sufficient condition for the shared-basis exact budget `p + 1` to
sit below the full `BitVec n` truth-table threshold. -/
theorem sharedExactZABDecisionListBudget_lt_bitVecTruthTable_of_le_of_two_le
    (hfeat : p ≤ n + 2 * k)
    (hwidth : 2 ≤ n + 2 * k) :
    p + 1 < 2 ^ (n + 2 * k) := by
  have hle : p + 1 ≤ n + 2 * k + 1 := Nat.succ_le_succ hfeat
  exact lt_of_le_of_lt hle <|
    exactZABDecisionListBudget_lt_bitVecTruthTable_of_two_le
      (r := n) (k := k) hwidth

/-- Hence a shared-basis exact `(zfeat(z), a, b)` target cannot be surjective
when the shared-feature count is at most the full exact visible width
`n + 2k` and that width is at least `2`. -/
theorem SharedExactZABDecisionListTargetData.not_surjective_predict_of_le_of_two_le
    {zfeat : BitVec n → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    (h :
      SharedExactZABDecisionListTargetData
        (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index)
        zfeat features G)
    (hfeat : p ≤ n + 2 * k)
    (hwidth : 2 ≤ n + 2 * k) :
    ¬ Function.Surjective G.predict := by
  exact
    h.not_surjective_predict_of_budget_lt
      (sharedExactZABDecisionListBudget_lt_bitVecTruthTable_of_le_of_two_le
        (n := n) (p := p) (k := k) hfeat hwidth)

/-- The same contradiction applies to the recovery wrapper, since it already
packages the same exact compression target. -/
theorem SharedExactZABDecisionListRecoveryData.not_surjective_predict_of_budget_lt
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {zfeat : BitVec n → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABDecisionListRecoveryData
        (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index)
        μ zfeat features G q)
    (hbudget : p + 1 < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective G.predict := by
  exact h.targetData.not_surjective_predict_of_budget_lt hbudget

/-- And likewise under the natural width hypothesis `p ≤ n + 2k` with
`2 ≤ n + 2k`. -/
theorem SharedExactZABDecisionListRecoveryData.not_surjective_predict_of_le_of_two_le
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {zfeat : BitVec n → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABDecisionListRecoveryData
        (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index)
        μ zfeat features G q)
    (hfeat : p ≤ n + 2 * k)
    (hwidth : 2 ≤ n + 2 * k) :
    ¬ Function.Surjective G.predict := by
  exact h.targetData.not_surjective_predict_of_le_of_two_le hfeat hwidth

/-- The same exact-surface lower bound for the named shared-basis exact ERM
family wrapper itself. -/
theorem sharedExactZABAffineDecisionListERMFamily_bitVecSurfaceCard_le_of_surjective_predict
    (zfeat : BitVec n → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool)
    (hsurj :
      Function.Surjective
        (sharedExactZABAffineDecisionListERMFamily
          (Z := BitVec n) (p := p) (r := r) (k := k)
          zfeat features samples).predict) :
    2 ^ (n + 2 * k) ≤ p + 1 := by
  exact
    (sharedExactZABAffineDecisionListERMTargetData
      (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index)
      zfeat features samples).bitVecSurfaceCard_le_of_surjective_predict
      hsurj

/-- Therefore the named shared-basis exact ERM family cannot be surjective once
its linear budget sits below the full exact-surface threshold. -/
theorem sharedExactZABAffineDecisionListERMFamily_not_surjective_of_budget_lt
    (zfeat : BitVec n → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool)
    (hbudget : p + 1 < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective
        (sharedExactZABAffineDecisionListERMFamily
          (Z := BitVec n) (p := p) (r := r) (k := k)
          zfeat features samples).predict := by
  intro hsurj
  exact Nat.not_le_of_lt hbudget <|
    sharedExactZABAffineDecisionListERMFamily_bitVecSurfaceCard_le_of_surjective_predict
      (n := n) (p := p) (r := r) (k := k) (Index := Index)
      zfeat features samples hsurj

/-- In particular, the shared-basis exact ERM family itself cannot be
surjective when `p ≤ n + 2k` and the full exact visible width `n + 2k` is at
least `2`. -/
theorem sharedExactZABAffineDecisionListERMFamily_not_surjective_of_le_of_two_le
    (zfeat : BitVec n → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool)
    (hfeat : p ≤ n + 2 * k)
    (hwidth : 2 ≤ n + 2 * k) :
    ¬ Function.Surjective
        (sharedExactZABAffineDecisionListERMFamily
          (Z := BitVec n) (p := p) (r := r) (k := k)
          zfeat features samples).predict := by
  exact
    sharedExactZABAffineDecisionListERMFamily_not_surjective_of_budget_lt
      (n := n) (p := p) (r := r) (k := k) (Index := Index)
      zfeat features samples
      (sharedExactZABDecisionListBudget_lt_bitVecTruthTable_of_le_of_two_le
        (n := n) (p := p) (k := k) hfeat hwidth)

/-- The final shared-basis exact ERM interface inherits the same
budget-threshold obstruction. -/
theorem SharedExactZABERMRecoveryData.not_surjective_predict_of_budget_lt
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {zfeat : BitVec n → BitVec r}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABERMRecoveryData
        (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hbudget : p + 1 < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective G.predict := by
  exact h.targetData.not_surjective_predict_of_budget_lt hbudget

/-- And likewise under the natural width hypotheses `p ≤ n + 2k` and
`2 ≤ n + 2k`. -/
theorem SharedExactZABERMRecoveryData.not_surjective_predict_of_le_of_two_le
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {zfeat : BitVec n → BitVec r}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABERMRecoveryData
        (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hfeat : p ≤ n + 2 * k)
    (hwidth : 2 ≤ n + 2 * k) :
    ¬ Function.Surjective G.predict := by
  exact h.targetData.not_surjective_predict_of_le_of_two_le hfeat hwidth

end

end Mettapedia.Computability.PNP
