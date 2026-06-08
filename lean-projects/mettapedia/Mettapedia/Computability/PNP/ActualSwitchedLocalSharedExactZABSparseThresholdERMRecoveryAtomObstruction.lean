import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleMajorityObstruction
import Mettapedia.Computability.PNP.BadCodeAgreementObstruction
import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoveryData
import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMSampleLowerBound
import Mathlib.Tactic

/-!
# P vs NP route obstruction: atomic-measure failure for surjective actual-local
  sparse-threshold recovery packets

`ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoveryData` transports the
manuscript-facing sparse-threshold ERM recovery packet to the actual
switched-local layer.  The remaining burden there is a uniform bad-code
agreement bound.

This file tests that burden against atomic sampling laws.  If the actual local
family is still surjective on the exact visible surface and that surface has two
distinct points `x ≠ y`, then one can choose:

* one realized target rule that is identically `false`, and
* one realized bad code that is `true` only at `y`.

That bad code still agrees with the target at `x`.  Hence any atom at `x` whose
mass already exceeds `q` refutes the claimed bad-code agreement bound by `q`.

So the sparse-threshold recovery wrapper itself cannot certify strict recovery
on a pure atom, or more generally on any measure with one overly heavy atom,
as long as the actual-local family remains fully expressive on a nontrivial
visible surface.
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

/-- If a surjective actual switched-local sparse-threshold recovery packet is
sampled from a measure with one atom already heavier than the claimed bad-code
agreement bound, and the exact visible surface has another distinct point, then
the packet is impossible: the full-rule family can realize a bad code that
agrees at the heavy atom and differs elsewhere. -/
theorem not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_surjective_predict_of_atom_gt
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (zfeat : Z → BitVec r)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    {x y : ExactVisiblePostSwitchSurface Z k}
    (hxy : x ≠ y)
    (hmass : q < μ x) :
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
  have hxagree :
      (sharedExactZABSparseThresholdAffineBitFamily
        Z
        zfeat
        (allAffinePointBlockFeatures (r + (k + k)))).decode
          (sharedSparseThresholdCodeEquivBitCode
            (allAffinePointBlockFeatureCount (r + (k + k))) code) x =
        T.predictorFamily.predict i x := by
    calc
      (sharedExactZABSparseThresholdAffineBitFamily
        Z
        zfeat
        (allAffinePointBlockFeatures (r + (k + k)))).decode
          (sharedSparseThresholdCodeEquivBitCode
            (allAffinePointBlockFeatureCount (r + (k + k))) code) x
          = T.predictorFamily.predict j x := congrFun hdecode x
      _ = spike x := congrFun hj x
      _ = false := by simp [spike, hxy]
      _ = target x := by simp [target]
      _ = T.predictorFamily.predict i x := (congrFun hi x).symm
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
  have hregion :
      q <
        ({x} : Finset (ExactVisiblePostSwitchSurface Z k)).sum
          (fun u => μ u) := by
    simpa using hmass
  exact
    (BitEncodedClassifierFamily.not_badCodeAgreementBound_of_agrees_on_region_gt
        (F := sharedExactZABSparseThresholdAffineBitFamily
          Z
          zfeat
          (allAffinePointBlockFeatures (r + (k + k))))
        (μ := μ)
        (target := T.predictorFamily.predict i)
        (q := q)
        c
        {x}
        (by
          intro u hu
          have hux : u = x := by simpa using hu
          subst hux
          simpa [c, ActualSwitchedLocalInterface.predictorFamily] using hxagree)
        hregion)
      (h.agreement_le i)

/-- Pure-atom specialization: on any nontrivial exact visible surface, a
surjective actual switched-local sparse-threshold recovery packet cannot satisfy
any strict bound `q < 1` against the pure distribution at one atom. -/
theorem not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_surjective_predict_of_pure_atom_lt_one
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (zfeat : Z → BitVec r)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    {x y : ExactVisiblePostSwitchSurface Z k}
    (hxy : x ≠ y)
    (hq_lt : q < 1) :
    ¬ Nonempty
        (SharedExactZABSparseThresholdERMRecoveryData (PMF.pure x) T zfeat q) := by
  exact
    not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_surjective_predict_of_atom_gt
      (μ := PMF.pure x)
      T zfeat hsurj hxy
      (by simpa using hq_lt)

end Abstract

section Endpoints

universe v

variable {Z : Type v} [Fintype Z] {k r sampleBound : ℕ}
variable {zfeat : Z → BitVec r} {q : ℝ≥0∞}

/-- The pure-atom obstruction lifts immediately to the bounded-sample
plug-in-majority actual-local endpoint once the sample bound is large enough to
make that endpoint surjective on the exact visible surface. -/
theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_pure_atom_lt_one
    (hsample : Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound)
    {x y : ExactVisiblePostSwitchSurface Z k}
    (hxy : x ≠ y)
    (hq_lt : q < 1) :
    ¬ Nonempty
        (SharedExactZABSparseThresholdERMRecoveryData
          (PMF.pure x)
          (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound)
          zfeat
          q) := by
  exact
    not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_surjective_predict_of_pure_atom_lt_one
      (T := boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound)
      zfeat
      (boundedSamplePluginMajorityActualSwitchedLocalInterface_surjective
        Z k sampleBound hsample)
      hxy
      hq_lt

/-- The same pure-atom obstruction specializes to the full-rule actual-local
counterexample surface on any exact visible type with two distinct points. -/
theorem fullRuleActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_pure_atom_lt_one
    {x y : ExactVisiblePostSwitchSurface Z k}
    {zfeat : Z → BitVec r}
    (hxy : x ≠ y)
    (hq_lt : q < 1) :
    ¬ Nonempty
        (SharedExactZABSparseThresholdERMRecoveryData
          (PMF.pure x)
          (fullRuleActualSwitchedLocalInterface Z k)
          zfeat
          q) := by
  exact
    not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_surjective_predict_of_pure_atom_lt_one
      (T := fullRuleActualSwitchedLocalInterface Z k)
      zfeat
      (fullRuleActualSwitchedLocalInterface_surjective Z k)
      hxy
      hq_lt

end Endpoints

section BitVec

variable {n k r : ℕ} {q : ℝ≥0∞}
variable {zfeat : BitVec n → BitVec r}
variable {x : ExactVisiblePostSwitchSurface (BitVec n) k}

/-- On any nontrivial `BitVec` exact visible surface, the full-rule actual-local
counterexample already rules out pure-atom strict recovery for the sparse-
threshold ERM packet. -/
theorem fullRuleActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_pure_atom_lt_one_of_visibleWidth_pos
    (hvis : 0 < n + (k + k))
    (hq_lt : q < 1) :
    ¬ Nonempty
        (SharedExactZABSparseThresholdERMRecoveryData
          (PMF.pure x)
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
  obtain ⟨y, hy⟩ :=
    Fintype.exists_ne_of_one_lt_card
      (α := ExactVisiblePostSwitchSurface (BitVec n) k)
      hone x
  exact
    fullRuleActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_pure_atom_lt_one
      (k := k)
      (x := x)
      (y := y)
      (zfeat := zfeat)
      (by exact fun h => hy h.symm)
      hq_lt

end BitVec

end ActualSwitchedLocalInterface

end Mettapedia.Computability.PNP
