import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleMajorityObstruction
import Mettapedia.Computability.PNP.BadCodeAgreementObstruction
import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoveryData
import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMSampleLowerBound
import Mathlib.Data.ENNReal.Inv
import Mathlib.Tactic

/-!
# P vs NP route obstruction: concentrated recovery measures force large `q`

`ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoveryData` packages the
manuscript-facing point-block sparse-threshold ERM route together with one
uniform bad-code agreement bound `q`.

The atomic obstruction already shows that one overly heavy atom can refute such
data.  This file extracts the sharper complementary phenomenon: because the
full-rule family can realize the singleton spike at any visible point `y`, a
surjective recovery packet must also tolerate the bad code that agrees with the
constant-false target everywhere except possibly at `y`.

Therefore every visible point must carry mass at least `1 - q`.  In
particular, once the exact visible surface has two distinct points, the route
already forces `q ≥ 1/2`.  So no manuscript-facing actual-local sparse-
threshold recovery packet can exist with `q < 1/2` on any nontrivial visible
surface.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

namespace ActualSwitchedLocalInterface

section Abstract

universe u v w

variable {Z : Type v} [Fintype Z] {k : ℕ} {Index : Type u} {Block : Type w}
variable {T : ActualSwitchedLocalInterface Z k Index Block} {r : ℕ}
variable {μ : PMF (ExactVisiblePostSwitchSurface Z k)} {zfeat : Z → BitVec r}
variable {q : ℝ≥0∞}

/-- Visible-point form of the same obstruction: on a surjective actual-local
sparse-threshold recovery packet, the mass outside any chosen point `y` must be
at most `q`. -/
theorem not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_surjective_predict_of_lt_one_sub_apply
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (zfeat : Z → BitVec r)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    (y : ExactVisiblePostSwitchSurface Z k)
    (hmass : q < 1 - μ y) :
    ¬ Nonempty (SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q) := by
  classical
  rintro ⟨h⟩
  let target : ExactVisiblePostSwitchSurface Z k → Bool := fun _ => false
  let spike : ExactVisiblePostSwitchSurface Z k → Bool := fun u => decide (u = y)
  obtain ⟨i, hi⟩ := hsurj target
  obtain ⟨j, hj⟩ := hsurj spike
  rcases h.targetData.realized j with ⟨code, hcode⟩
  have hdecode :
      (sharedExactZABSparseThresholdAffineBitFamily
        Z
        zfeat
        (allAffinePointBlockFeatures (r + (k + k)))).decode
          (sharedSparseThresholdCodeEquivBitCode
            (allAffinePointBlockFeatureCount (r + (k + k))) code) =
        T.predictorFamily.predict j := by
    calc
      (sharedExactZABSparseThresholdAffineBitFamily
        Z
        zfeat
        (allAffinePointBlockFeatures (r + (k + k)))).decode
          (sharedSparseThresholdCodeEquivBitCode
            (allAffinePointBlockFeatureCount (r + (k + k))) code)
          =
        sharedExactZABSparseThresholdAffinePredict
          (Z := Z)
          (p := allAffinePointBlockFeatureCount (r + (k + k)))
          (r := r) (k := k)
          zfeat
          (allAffinePointBlockFeatures (r + (k + k)))
          code := by
            exact
              sharedExactZABSparseThresholdAffineBitFamily_decode_code
                (Z := Z)
                (p := allAffinePointBlockFeatureCount (r + (k + k)))
                (r := r) (k := k)
                zfeat
                (allAffinePointBlockFeatures (r + (k + k)))
                code
      _ = T.predictorFamily.predict j := hcode.symm
  have hagree :
      ∀ u, u ∈ Finset.univ.erase y →
        (sharedExactZABSparseThresholdAffineBitFamily
          Z
          zfeat
          (allAffinePointBlockFeatures (r + (k + k)))).decode
            (sharedSparseThresholdCodeEquivBitCode
              (allAffinePointBlockFeatureCount (r + (k + k))) code) u =
          T.predictorFamily.predict i u := by
    intro u hu
    have huy : u ≠ y := (Finset.mem_erase.mp hu).1
    calc
      (sharedExactZABSparseThresholdAffineBitFamily
        Z
        zfeat
        (allAffinePointBlockFeatures (r + (k + k)))).decode
          (sharedSparseThresholdCodeEquivBitCode
            (allAffinePointBlockFeatureCount (r + (k + k))) code) u
          = T.predictorFamily.predict j u := congrFun hdecode u
      _ = spike u := congrFun hj u
      _ = false := by simp [spike, huy]
      _ = target u := by simp [target]
      _ = T.predictorFamily.predict i u := (congrFun hi u).symm
  have hbad :
      (sharedExactZABSparseThresholdAffineBitFamily
        Z
        zfeat
        (allAffinePointBlockFeatures (r + (k + k)))).decode
          (sharedSparseThresholdCodeEquivBitCode
            (allAffinePointBlockFeatureCount (r + (k + k))) code) ≠
        T.predictorFamily.predict i := by
    intro heq
    have hyeq : T.predictorFamily.predict j y = T.predictorFamily.predict i y := by
      exact congrFun (hdecode.symm.trans heq) y
    have hytrue : T.predictorFamily.predict j y = true := by
      calc
        T.predictorFamily.predict j y = spike y := congrFun hj y
        _ = true := by simp [spike]
    have hyfalse : T.predictorFamily.predict i y = false := by
      calc
        T.predictorFamily.predict i y = target y := congrFun hi y
        _ = false := by simp [target]
    have hicontra : T.predictorFamily.predict i y = true := by
      exact hyeq.symm.trans hytrue
    exact Bool.false_ne_true (hyfalse.symm.trans hicontra)
  let c :
      (sharedExactZABSparseThresholdAffineBitFamily
        Z
        zfeat
        (allAffinePointBlockFeatures (r + (k + k)))).toEncodedFamily.BadCodes
          (T.predictorFamily.predict i) :=
    ⟨sharedSparseThresholdCodeEquivBitCode
        (allAffinePointBlockFeatureCount (r + (k + k))) code,
      hbad⟩
  have hsum :
      (1 : ℝ≥0∞) =
        (Finset.univ.erase y).sum (fun u => μ u) + μ y := by
    simpa [pmf_sum_univ_eq_one μ, add_comm] using
      (Finset.sum_erase_add
        (s := (Finset.univ : Finset (ExactVisiblePostSwitchSurface Z k)))
        (a := y)
        (f := fun u : ExactVisiblePostSwitchSurface Z k => μ u)
        (Finset.mem_univ y)).symm
  have hregion :
      q < (Finset.univ.erase y).sum (fun u => μ u) := by
    rw [ENNReal.sub_eq_of_eq_add (μ.apply_ne_top y) hsum] at hmass
    exact hmass
  exact
    ((sharedExactZABSparseThresholdAffineBitFamily
      Z
      zfeat
      (allAffinePointBlockFeatures (r + (k + k)))).not_badCodeAgreementBound_of_agrees_on_region_gt
        (μ := μ)
        (target := T.predictorFamily.predict i)
        (q := q)
        c
        (Finset.univ.erase y)
        (by
          intro u hu
          simpa [c, ActualSwitchedLocalInterface.predictorFamily] using hagree u hu)
        hregion)
      (h.agreement_le i)

namespace SharedExactZABSparseThresholdERMRecoveryData

/-- Any surjective actual-local sparse-threshold recovery packet forces the mass
outside every visible point `y` to be at most `q`. -/
theorem one_sub_apply_le_of_surjective_predict
    (h : SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    (y : ExactVisiblePostSwitchSurface Z k) :
    1 - μ y ≤ q := by
  exact le_of_not_gt <| by
    intro hlt
    exact
      not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_surjective_predict_of_lt_one_sub_apply
        (μ := μ) T zfeat hsurj y hlt ⟨h⟩

/-- On any visible surface with two distinct points, surjective actual-local
sparse-threshold recovery packets must satisfy `q ≥ 1/2`. -/
theorem half_le_of_surjective_predict_of_exists_ne
    (h : SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    {x y : ExactVisiblePostSwitchSurface Z k}
    (hxy : x ≠ y) :
    (2 : ℝ≥0∞)⁻¹ ≤ q := by
  classical
  have hsumxy : μ x + μ y ≤ 1 := by
    calc
      μ x + μ y
          = (insert x ({y} : Finset (ExactVisiblePostSwitchSurface Z k))).sum
              (fun u => μ u) := by
                simp [hxy]
      _ ≤ ∑ u : ExactVisiblePostSwitchSurface Z k, μ u := by
            simpa using
              (Finset.sum_le_univ_sum_of_nonneg
                (s := insert x ({y} : Finset (ExactVisiblePostSwitchSurface Z k)))
                (f := fun u : ExactVisiblePostSwitchSurface Z k => μ u)
                (by
                  intro u
                  exact zero_le (μ u)))
      _ = 1 := pmf_sum_univ_eq_one μ
  have hsmall : μ x ≤ (2 : ℝ≥0∞)⁻¹ ∨ μ y ≤ (2 : ℝ≥0∞)⁻¹ := by
    by_contra hsmall
    simp only [not_or, not_le] at hsmall
    have hgt : 1 < μ x + μ y := by
      calc
        1 = (2 : ℝ≥0∞)⁻¹ + (2 : ℝ≥0∞)⁻¹ := by
              simpa using ENNReal.inv_two_add_inv_two.symm
        _ < μ x + μ y := ENNReal.add_lt_add hsmall.1 hsmall.2
    exact not_lt_of_ge hsumxy hgt
  cases hsmall with
  | inl hxhalf =>
      have hhalf_le :
          (2 : ℝ≥0∞)⁻¹ ≤ 1 - μ x := by
        rw [ENNReal.le_sub_iff_add_le_right (μ.apply_ne_top x) (μ.coe_le_one x)]
        have haux :
            (2 : ℝ≥0∞)⁻¹ + μ x ≤ (2 : ℝ≥0∞)⁻¹ + (2 : ℝ≥0∞)⁻¹ :=
          by
            simpa [add_comm] using add_le_add_right hxhalf ((2 : ℝ≥0∞)⁻¹)
        exact le_trans haux <| by
          simpa using (le_of_eq ENNReal.inv_two_add_inv_two)
      exact le_trans hhalf_le (h.one_sub_apply_le_of_surjective_predict hsurj x)
  | inr hyhalf =>
      have hhalf_le :
          (2 : ℝ≥0∞)⁻¹ ≤ 1 - μ y := by
        rw [ENNReal.le_sub_iff_add_le_right (μ.apply_ne_top y) (μ.coe_le_one y)]
        have haux :
            (2 : ℝ≥0∞)⁻¹ + μ y ≤ (2 : ℝ≥0∞)⁻¹ + (2 : ℝ≥0∞)⁻¹ :=
          by
            simpa [add_comm] using add_le_add_right hyhalf ((2 : ℝ≥0∞)⁻¹)
        exact le_trans haux <| by
          simpa using (le_of_eq ENNReal.inv_two_add_inv_two)
      exact le_trans hhalf_le (h.one_sub_apply_le_of_surjective_predict hsurj y)

end SharedExactZABSparseThresholdERMRecoveryData

/-- Therefore no surjective actual-local sparse-threshold recovery packet can
exist with `q < 1/2` on a visible surface containing two distinct points. -/
theorem not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_surjective_predict_of_lt_half_of_exists_ne
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (zfeat : Z → BitVec r)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    {x y : ExactVisiblePostSwitchSurface Z k}
    (hxy : x ≠ y)
    (hq_lt : q < (2 : ℝ≥0∞)⁻¹) :
    ¬ Nonempty (SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q) := by
  rintro ⟨h⟩
  exact not_le_of_gt hq_lt <|
    h.half_le_of_surjective_predict_of_exists_ne hsurj hxy

end Abstract

section Endpoints

universe v

variable {Z : Type v} [Fintype Z] {k r sampleBound : ℕ}
variable {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
variable {zfeat : Z → BitVec r} {q : ℝ≥0∞}

/-- The half-mass obstruction lifts to the bounded-sample plug-in-majority
endpoint once the sample bound is large enough for surjectivity. -/
theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_lt_half_of_exists_ne
    (hsample : Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound)
    {x y : ExactVisiblePostSwitchSurface Z k}
    (hxy : x ≠ y)
    (hq_lt : q < (2 : ℝ≥0∞)⁻¹) :
    ¬ Nonempty
        (SharedExactZABSparseThresholdERMRecoveryData
          μ
          (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound)
          zfeat
          q) := by
  exact
    not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_surjective_predict_of_lt_half_of_exists_ne
      (μ := μ)
      (T := boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound)
      zfeat
      (boundedSamplePluginMajorityActualSwitchedLocalInterface_surjective
        Z k sampleBound hsample)
      hxy
      hq_lt

/-- The same half-mass obstruction specializes to the full-rule actual-local
endpoint on any visible surface with two distinct points. -/
theorem fullRuleActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_lt_half_of_exists_ne
    {x y : ExactVisiblePostSwitchSurface Z k}
    {zfeat : Z → BitVec r}
    (hxy : x ≠ y)
    (hq_lt : q < (2 : ℝ≥0∞)⁻¹) :
    ¬ Nonempty
        (SharedExactZABSparseThresholdERMRecoveryData
          μ
          (fullRuleActualSwitchedLocalInterface Z k)
          zfeat
          q) := by
  exact
    not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_surjective_predict_of_lt_half_of_exists_ne
      (μ := μ)
      (T := fullRuleActualSwitchedLocalInterface Z k)
      zfeat
      (fullRuleActualSwitchedLocalInterface_surjective Z k)
      hxy
      hq_lt

end Endpoints

section BitVec

variable {n k r : ℕ} {q : ℝ≥0∞}
variable {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
variable {zfeat : BitVec n → BitVec r}

/-- On any nontrivial `BitVec` visible surface, the full-rule actual-local
sparse-threshold recovery packet already fails for every `q < 1/2`. -/
theorem fullRuleActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_lt_half_of_visibleWidth_pos
    (hvis : 0 < n + (k + k))
    (hq_lt : q < (2 : ℝ≥0∞)⁻¹) :
    ¬ Nonempty
        (SharedExactZABSparseThresholdERMRecoveryData
          μ
          (fullRuleActualSwitchedLocalInterface (BitVec n) k)
          zfeat
          q) := by
  have htwo :
      2 ≤ Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k) :=
    two_le_card_exactVisiblePostSwitchSurface_bitVec_of_width_pos
      (n := n) (k := k) hvis
  have hone :
      1 < Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k) := by
    omega
  let x : ExactVisiblePostSwitchSurface (BitVec n) k :=
    ⟨zeroVec, zeroVec, zeroVec⟩
  obtain ⟨y, hy⟩ :=
    Fintype.exists_ne_of_one_lt_card
      (α := ExactVisiblePostSwitchSurface (BitVec n) k)
      hone x
  exact
    fullRuleActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_lt_half_of_exists_ne
      (μ := μ)
      (x := x)
      (y := y)
      (zfeat := zfeat)
      (by exact fun h => hy h.symm)
      hq_lt

/-- Equivalently, any nonempty full-rule `BitVec` sparse-threshold recovery
packet on a nontrivial visible surface must satisfy `q ≥ 1/2`. -/
theorem half_le_of_nonempty_fullRuleActualSwitchedLocalInterface_sharedExactZABSparseThresholdERMRecoveryData_of_visibleWidth_pos
    (h : SharedExactZABSparseThresholdERMRecoveryData
      μ
      (fullRuleActualSwitchedLocalInterface (BitVec n) k)
      zfeat
      q)
    (hvis : 0 < n + (k + k)) :
    (2 : ℝ≥0∞)⁻¹ ≤ q := by
  exact le_of_not_gt <| by
    intro hq_lt
    exact
      fullRuleActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_lt_half_of_visibleWidth_pos
        (μ := μ)
        (zfeat := zfeat)
        hvis
        hq_lt
        ⟨h⟩

end BitVec

end ActualSwitchedLocalInterface

end Mettapedia.Computability.PNP
