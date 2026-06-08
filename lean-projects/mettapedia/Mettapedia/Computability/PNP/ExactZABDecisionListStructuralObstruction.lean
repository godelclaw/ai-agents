import Mettapedia.Computability.PNP.ActualSwitchedLocalStructure
import Mettapedia.Computability.PNP.PostSwitchInputObstruction
import Mathlib.Tactic

/-!
# PNP crux: the raw exact `(zfeat(z), a, b)` decision-list route is structurally
  too weak

The previous exact-ZAB packets lower-bounded the route by cardinality.  This
file records a stronger obstruction for the raw exact decision-list branch
itself.

For positive latent width `n > 0` and positive visible width `k > 0`, every
predictor in the raw exact `(zfeat(z), a, b)` family falls into one of two bad
cases:

* some `z0` activates a `zfeat` bit early, so the predictor is constant across
  the whole `(a,b)` fiber above `z0`;
* or every `zfeat z` is zero, so the predictor ignores `z` entirely.

Either way, the route cannot realize a surjective exact family, hence cannot
support the manuscript's full-rule actual-local interface.
-/

namespace Mettapedia.Computability.PNP

section FirstActive

open Fin

theorem firstActiveFeature?_eq_some_iff
    {r : ℕ} (featureVec : BitVec r) (j : Fin r) :
    firstActiveFeature? featureVec = some j ↔
      featureVec j = true ∧ ∀ i, i < j → featureVec i = false := by
  classical
  let active : Finset (Fin r) := (Finset.univ : Finset (Fin r)).filter fun i => featureVec i
  by_cases hne : active.Nonempty
  · constructor
    · intro h
      have hmin : active.min' hne = j := by
        simpa [firstActiveFeature?, active, hne] using h
      have hjmem : j ∈ active := by
        simpa [hmin] using Finset.min'_mem active hne
      have hjtrue : featureVec j = true := by
        simpa [active, Finset.mem_filter] using hjmem
      refine ⟨hjtrue, ?_⟩
      intro i hij
      by_contra htrue
      have hiTrue : featureVec i = true := by
        cases hfi : featureVec i <;> simp [hfi] at htrue ⊢
      have himem : i ∈ active := by
        simp [active, Finset.mem_filter, hiTrue]
      have hle : active.min' hne ≤ i := Finset.min'_le active i himem
      rw [hmin] at hle
      exact (not_le_of_gt hij) hle
    · rintro ⟨hjtrue, hbefore⟩
      have hjmem : j ∈ active := by
        simp [active, Finset.mem_filter, hjtrue]
      have hle : active.min' hne ≤ j := Finset.min'_le active j hjmem
      have hge : j ≤ active.min' hne := by
        by_contra hjlt
        have hminmem : active.min' hne ∈ active := Finset.min'_mem active hne
        have hmintrue : featureVec (active.min' hne) = true := by
          simpa [active, Finset.mem_filter] using hminmem
        have hminfalse : featureVec (active.min' hne) = false := hbefore _ (lt_of_not_ge hjlt)
        simp [hmintrue] at hminfalse
      have hmin : active.min' hne = j := le_antisymm hle hge
      simp [firstActiveFeature?, active, hne, hmin]
  · constructor
    · intro h
      simp [firstActiveFeature?, active, hne] at h
    · rintro ⟨hjtrue, _⟩
      exfalso
      exact hne ⟨j, by simp [active, Finset.mem_filter, hjtrue]⟩

theorem firstActiveFeature?_eq_none_iff
    {r : ℕ} (featureVec : BitVec r) :
    firstActiveFeature? featureVec = none ↔ ∀ j, featureVec j = false := by
  classical
  let active : Finset (Fin r) := (Finset.univ : Finset (Fin r)).filter fun i => featureVec i
  by_cases hne : active.Nonempty
  · constructor
    · simp [firstActiveFeature?, active, hne]
    · intro hall
      exfalso
      rcases hne with ⟨j, hj⟩
      have hjtrue : featureVec j = true := by
        simpa [active, Finset.mem_filter] using hj
      simp [hall j] at hjtrue
  · constructor
    · intro h j
      by_contra hj
      apply hne
      exact ⟨j, by simp [active, Finset.mem_filter, hj]⟩
    · simp [firstActiveFeature?, active, hne]

theorem firstActiveFeature?_zeroVec
    {r : ℕ} :
    firstActiveFeature? (zeroVec : BitVec r) = none := by
  refine (firstActiveFeature?_eq_none_iff (featureVec := (zeroVec : BitVec r))).2 ?_
  intro j
  simp [zeroVec]

theorem exists_firstActiveFeature?_eq_some_of_ne_zero
    {r : ℕ} {featureVec : BitVec r}
    (hvec : featureVec ≠ zeroVec) :
    ∃ j, firstActiveFeature? featureVec = some j := by
  by_cases hnone : firstActiveFeature? featureVec = none
  · exfalso
    apply hvec
    funext j
    exact (firstActiveFeature?_eq_none_iff (featureVec := featureVec)).1 hnone j
  · exact Option.ne_none_iff_exists'.1 hnone

theorem firstActiveFeature?_append_left
    {m n : ℕ} {x : BitVec m} {y : BitVec n} {j : Fin m}
    (hx : firstActiveFeature? x = some j) :
    firstActiveFeature? (Fin.append x y) = some (Fin.castAdd n j) := by
  apply (firstActiveFeature?_eq_some_iff (featureVec := Fin.append x y) (j := Fin.castAdd n j)).2
  have hxspec := (firstActiveFeature?_eq_some_iff (featureVec := x) (j := j)).1 hx
  refine ⟨?_, ?_⟩
  · simpa using (show Fin.append x y (Fin.castAdd n j) = true by
      simpa using hxspec.1)
  · intro i hi
    cases i using Fin.addCases with
    | left i =>
        have hi' : i < j := by
          simpa using hi
        simpa using hxspec.2 i hi'
    | right i =>
        have hge : (Fin.castAdd n j : Fin (m + n)) ≤ Fin.natAdd m i := by
          refine Fin.le_iff_val_le_val.mpr ?_
          exact Nat.le_trans (Nat.le_of_lt (Fin.castAdd_lt n j)) (Fin.le_coe_natAdd m i)
        exact (not_lt_of_ge hge hi).elim

theorem firstActiveFeature?_append_right
    {m n : ℕ} {x : BitVec m} {y : BitVec n} {j : Fin n}
    (hx : firstActiveFeature? x = none)
    (hy : firstActiveFeature? y = some j) :
    firstActiveFeature? (Fin.append x y) = some (Fin.natAdd m j) := by
  apply (firstActiveFeature?_eq_some_iff (featureVec := Fin.append x y) (j := Fin.natAdd m j)).2
  have hxspec := (firstActiveFeature?_eq_none_iff (featureVec := x)).1 hx
  have hyspec := (firstActiveFeature?_eq_some_iff (featureVec := y) (j := j)).1 hy
  refine ⟨?_, ?_⟩
  · simpa using (show Fin.append x y (Fin.natAdd m j) = true by
      simpa using hyspec.1)
  · intro i hi
    cases i using Fin.addCases with
    | left i =>
        simpa using hxspec i
    | right i =>
        have hi' : i < j := by
          simpa using hi
        simpa using hyspec.2 i hi'

end FirstActive

section Structural

open Fin

variable {Z : Type*} [DecidableEq Z]

def headOneVec {n : ℕ} (hn : 0 < n) : BitVec n :=
  fun i => decide (i = ⟨0, hn⟩)

@[simp] theorem headOneVec_head {n : ℕ} (hn : 0 < n) :
    headOneVec hn ⟨0, hn⟩ = true := by
  simp [headOneVec]

@[simp] theorem headOneVec_zeroVec_ne {n : ℕ} (hn : 0 < n) :
    headOneVec hn ≠ zeroVec := by
  intro h
  have : headOneVec hn ⟨0, hn⟩ = false := by
    simpa [zeroVec] using congrFun h ⟨0, hn⟩
  simp [headOneVec] at this

def zFiberAHeadRule
    {k : ℕ} (hk : 0 < k) (z0 : Z) :
    ExactVisibleRule Z k :=
  fun u => if u.z = z0 then u.a ⟨0, hk⟩ else false

def zHeadRule
    {n k : ℕ} (hn : 0 < n) :
    ExactVisibleRule (BitVec n) k :=
  fun u => u.z ⟨0, hn⟩

omit [DecidableEq Z] in
theorem rawExactZABDecisionListPredict_eq_of_firstActive_z
    {r k : ℕ}
    (zfeat : Z → BitVec r)
    (code : SharedAffineDecisionListCode (r + (k + k)))
    {z : Z} {j : Fin r}
    (hz : firstActiveFeature? (zfeat z) = some j)
    (a b : BitVec k) :
    rawExactZABDecisionListPredict (Z := Z) (r := r) (k := k) zfeat code ⟨z, a, b⟩ =
      code.1 (Fin.castAdd (k + k) j) := by
  simp [rawExactZABDecisionListPredict, exactZABVisibleData, exactABVisibleData,
    firstActiveFeature?_append_left hz]

theorem zFiberAHeadRule_not_eq_rawExactZABDecisionListPredict_of_firstActive_z
    {r k : ℕ}
    (zfeat : Z → BitVec r)
    (hk : 0 < k)
    (z0 : Z)
    {j : Fin r}
    (hz : firstActiveFeature? (zfeat z0) = some j)
    (code : SharedAffineDecisionListCode (r + (k + k))) :
    zFiberAHeadRule (Z := Z) (k := k) hk z0 ≠
      rawExactZABDecisionListPredict (Z := Z) (r := r) (k := k) zfeat code := by
  intro heq
  let u0 : ExactVisiblePostSwitchSurface Z k := ⟨z0, zeroVec, zeroVec⟩
  let u1 : ExactVisiblePostSwitchSurface Z k := ⟨z0, headOneVec hk, zeroVec⟩
  have hpred0 :
      rawExactZABDecisionListPredict (Z := Z) (r := r) (k := k) zfeat code u0 =
        code.1 (Fin.castAdd (k + k) j) := by
    simpa [u0] using
      rawExactZABDecisionListPredict_eq_of_firstActive_z
        (Z := Z) (r := r) (k := k) zfeat code hz zeroVec zeroVec
  have hpred1 :
      rawExactZABDecisionListPredict (Z := Z) (r := r) (k := k) zfeat code u1 =
        code.1 (Fin.castAdd (k + k) j) := by
    simpa [u1] using
      rawExactZABDecisionListPredict_eq_of_firstActive_z
        (Z := Z) (r := r) (k := k) zfeat code hz (headOneVec hk) zeroVec
  have hsamePred :
      rawExactZABDecisionListPredict (Z := Z) (r := r) (k := k) zfeat code u0 =
        rawExactZABDecisionListPredict (Z := Z) (r := r) (k := k) zfeat code u1 := by
    rw [hpred0, hpred1]
  have hsameRule : zFiberAHeadRule (Z := Z) (k := k) hk z0 u0 =
      zFiberAHeadRule (Z := Z) (k := k) hk z0 u1 := by
    simpa [heq] using hsamePred
  have hu0 : zFiberAHeadRule (Z := Z) (k := k) hk z0 u0 = false := by
    simp [zFiberAHeadRule, u0, zeroVec]
  have hu1 : zFiberAHeadRule (Z := Z) (k := k) hk z0 u1 = true := by
    simp [zFiberAHeadRule, u1, headOneVec]
  simp [hu0, hu1] at hsameRule

theorem zHeadRule_not_eq_rawExactZABDecisionListPredict_of_forall_zero
    {n r k : ℕ}
    (zfeat : BitVec n → BitVec r)
    (hn : 0 < n)
    (hzero : ∀ z, zfeat z = zeroVec)
    (code : SharedAffineDecisionListCode (r + (k + k))) :
    zHeadRule (n := n) (k := k) hn ≠
      rawExactZABDecisionListPredict (Z := BitVec n) (r := r) (k := k) zfeat code := by
  intro heq
  let z0 : BitVec n := zeroVec
  let z1 : BitVec n := headOneVec hn
  let u0 : ExactVisiblePostSwitchSurface (BitVec n) k := ⟨z0, zeroVec, zeroVec⟩
  let u1 : ExactVisiblePostSwitchSurface (BitVec n) k := ⟨z1, zeroVec, zeroVec⟩
  have hpred :
      rawExactZABDecisionListPredict (Z := BitVec n) (r := r) (k := k) zfeat code u0 =
        rawExactZABDecisionListPredict (Z := BitVec n) (r := r) (k := k) zfeat code u1 := by
    simp [rawExactZABDecisionListPredict, exactZABVisibleData, exactABVisibleData, u0, u1, hzero]
  have hsameRule :
      zHeadRule (n := n) (k := k) hn u0 = zHeadRule (n := n) (k := k) hn u1 := by
    simpa [heq] using hpred
  have hu0 : zHeadRule (n := n) (k := k) hn u0 = false := by
    simp [zHeadRule, u0, z0, zeroVec]
  have hu1 : zHeadRule (n := n) (k := k) hn u1 = true := by
    simp [zHeadRule, u1, z1]
  simp [hu0, hu1] at hsameRule

theorem not_realizedByRawExactZABDecisionListFamily_of_surjective_predict_of_pos_widths
    {n r k : ℕ} {Index : Type*}
    (zfeat : BitVec n → BitVec r)
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    (hn : 0 < n)
    (hk : 0 < k)
    (hsurj : Function.Surjective G.predict) :
    ¬ RealizedByRawExactZABDecisionListFamily
        (Z := BitVec n) (r := r) (k := k) zfeat G := by
  intro hreal
  by_cases hzero : ∀ z, zfeat z = zeroVec
  · rcases hsurj (zHeadRule (n := n) (k := k) hn) with ⟨i, hi⟩
    rcases hreal i with ⟨code, hcode⟩
    have hcode' :
        rawExactZABDecisionListPredict (Z := BitVec n) (r := r) (k := k) zfeat code =
          zHeadRule (n := n) (k := k) hn := by
      exact hcode.symm.trans hi
    exact
      zHeadRule_not_eq_rawExactZABDecisionListPredict_of_forall_zero
        (r := r) (k := k) zfeat hn hzero code hcode'.symm
  · have hnotzero : ∃ z0, zfeat z0 ≠ zeroVec := by
      exact not_forall.mp hzero
    rcases hnotzero with ⟨z0, hz0⟩
    rcases exists_firstActiveFeature?_eq_some_of_ne_zero hz0 with ⟨j, hj⟩
    rcases hsurj (zFiberAHeadRule (Z := BitVec n) (k := k) hk z0) with ⟨i, hi⟩
    rcases hreal i with ⟨code, hcode⟩
    have hcode' :
        rawExactZABDecisionListPredict (Z := BitVec n) (r := r) (k := k) zfeat code =
          zFiberAHeadRule (Z := BitVec n) (k := k) hk z0 := by
      exact hcode.symm.trans hi
    exact
      zFiberAHeadRule_not_eq_rawExactZABDecisionListPredict_of_firstActive_z
        (Z := BitVec n) (r := r) (k := k) zfeat hk z0 hj code hcode'.symm

theorem fullExactVisibleRuleFamily_not_realizedByRawExactZABDecisionListFamily_of_pos_widths
    {n r k : ℕ}
    (zfeat : BitVec n → BitVec r)
    (hn : 0 < n)
    (hk : 0 < k) :
    ¬ RealizedByRawExactZABDecisionListFamily
        (Z := BitVec n) (r := r) (k := k) zfeat
        (fullExactVisibleRuleFamily (BitVec n) k) := by
  exact
    not_realizedByRawExactZABDecisionListFamily_of_surjective_predict_of_pos_widths
      (n := n) (r := r) (k := k) zfeat hn hk
      (fullExactVisibleRuleFamily_surjective (BitVec n) k)

end Structural

namespace ActualSwitchedLocalInterface

theorem not_nonempty_zabDecisionListData_of_surjective_predict_of_pos_widths
    {n r k : ℕ} {Index Block : Type*}
    {T : ActualSwitchedLocalInterface (BitVec n) k Index Block}
    (zfeat : BitVec n → BitVec r)
    (hn : 0 < n)
    (hk : 0 < k)
    (hsurj : Function.Surjective T.predictorFamily.predict) :
    ¬ Nonempty (ZABDecisionListData T zfeat) := by
  rintro ⟨hdata⟩
  exact
    not_realizedByRawExactZABDecisionListFamily_of_surjective_predict_of_pos_widths
      (n := n) (r := r) (k := k) zfeat hn hk hsurj hdata.realized

theorem fullRuleActualSwitchedLocalInterface_not_zabDecisionListData_of_pos_widths
    {n r k : ℕ}
    (zfeat : BitVec n → BitVec r)
    (hn : 0 < n)
    (hk : 0 < k) :
    ¬ Nonempty
        (ZABDecisionListData
          (fullRuleActualSwitchedLocalInterface (BitVec n) k) zfeat) := by
  exact
    not_nonempty_zabDecisionListData_of_surjective_predict_of_pos_widths
      (n := n) (r := r) (k := k)
      (T := fullRuleActualSwitchedLocalInterface (BitVec n) k)
      zfeat hn hk
      (fullRuleActualSwitchedLocalInterface_surjective (BitVec n) k)

end ActualSwitchedLocalInterface

end Mettapedia.Computability.PNP
