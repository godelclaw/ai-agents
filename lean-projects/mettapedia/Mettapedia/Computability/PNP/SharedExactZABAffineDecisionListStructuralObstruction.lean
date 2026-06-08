import Mettapedia.Computability.PNP.BitVecZABCompressionObstruction
import Mettapedia.Computability.PNP.ExactZABDecisionListStructuralObstruction
import Mettapedia.Computability.PNP.SharedExactZABAffineDecisionListCharacterization
import Mettapedia.Computability.PNP.SharedExactZABAffineFeatureSharpness
import Mathlib.Tactic

/-!
# P vs NP crux: shared affine decision-list signatures are structurally
  noninjective on visible width above one

The shared exact affine decision-list branch was reduced earlier to one precise
condition: its first-active signature on the exact visible surface must be
injective.

This file proves a strong structural obstruction on the raw `BitVec` surface.
For any family of affine GF(2)-style probes on `BitVec d`, once `d > 1` the
first-active signature

`x ↦ firstActiveFeature? (affineFeatureVector features x)`

is never injective.  The reason is simple:

* if every affine probe is empty, the signature is constantly `none`;
* otherwise the earliest nonempty probe has a truth set of size at least `2`,
  because an affine parity test on more than one bit can never be true at
  exactly one point.

Pushed back through the exact visible-data bijection for identity extractors,
this closes the identity-extractor shared affine decision-list branch on every
bit-valued exact ZAB surface with visible width `n + 2k > 1`, independently of
the combiner width `p`.
-/

namespace Mettapedia.Computability.PNP

section RawBitVec

open Fin

def toggleBit {d : ℕ} (x : BitVec d) (i : Fin d) : BitVec d :=
  fun j => if j = i then !(x i) else x j

def singletonVec {d : ℕ} (i : Fin d) : BitVec d :=
  fun j => decide (j = i)

def pairVec {d : ℕ} (i j : Fin d) : BitVec d :=
  fun t => decide (t = i ∨ t = j)

@[simp] theorem toggleBit_apply_same {d : ℕ} (x : BitVec d) (i : Fin d) :
    toggleBit x i i = !(x i) := by
  simp [toggleBit]

@[simp] theorem toggleBit_apply_of_ne {d : ℕ} (x : BitVec d) {i j : Fin d}
    (hij : j ≠ i) :
    toggleBit x i j = x j := by
  simp [toggleBit, hij]

theorem toggleBit_ne_self {d : ℕ} (x : BitVec d) (i : Fin d) :
    toggleBit x i ≠ x := by
  intro h
  have hi := congrFun h i
  cases hxi : x i <;> simp [toggleBit, hxi] at hi

@[simp] theorem singletonVec_apply_self {d : ℕ} (i : Fin d) :
    singletonVec i i = true := by
  simp [singletonVec]

@[simp] theorem singletonVec_apply_of_ne {d : ℕ} {i j : Fin d} (hij : j ≠ i) :
    singletonVec i j = false := by
  simp [singletonVec, hij]

theorem singletonVec_ne_zeroVec {d : ℕ} (i : Fin d) :
    singletonVec i ≠ zeroVec := by
  intro h
  have hi : singletonVec i i = false := by
    simpa [zeroVec] using congrFun h i
  simp [singletonVec] at hi

theorem singletonVec_ne_singletonVec {d : ℕ} {i j : Fin d} (hij : i ≠ j) :
    singletonVec i ≠ singletonVec j := by
  intro h
  have hi : singletonVec i i = singletonVec j i := congrFun h i
  simp [singletonVec, hij] at hi

theorem pairVec_ne_zeroVec {d : ℕ} {i j : Fin d} (hij : i ≠ j) :
    pairVec i j ≠ zeroVec := by
  intro h
  have hi : pairVec i j i = false := by
    simpa [zeroVec] using congrFun h i
  simp [pairVec, hij] at hi

theorem columnParity_toggleBit_of_coeff_false
    {d : ℕ} (coeff x : BitVec d) (i : Fin d)
    (hcoeff : coeff i = false) :
    columnParity coeff (toggleBit x i) = columnParity coeff x := by
  rw [columnParity]
  congr
  ext j
  by_cases hji : j = i
  · subst hji
    simp [toggleBit, hcoeff]
  · simp [toggleBit, hji]

theorem affineColumnPredict_toggleBit_of_coeff_false
    {d : ℕ} (coeff : BitVec d) (bias : Bool) (x : BitVec d) (i : Fin d)
    (hcoeff : coeff i = false) :
    affineColumnPredict coeff bias (toggleBit x i) =
      affineColumnPredict coeff bias x := by
  simp [affineColumnPredict, columnParity_toggleBit_of_coeff_false, hcoeff]

theorem singleton_support_of_all_true
    {d : ℕ} {coeff : BitVec d}
    (hall : ∀ t, coeff t = true) (i : Fin d) :
    ((Finset.univ : Finset (Fin d)).filter fun t => coeff t && singletonVec i t) = {i} := by
  ext t
  by_cases hti : t = i
  · subst hti
    simp [hall, singletonVec]
  · simp [hall, singletonVec, hti]

theorem pair_support_of_all_true
    {d : ℕ} {coeff : BitVec d}
    (hall : ∀ t, coeff t = true) {i j : Fin d} (hij : i ≠ j) :
    ((Finset.univ : Finset (Fin d)).filter fun t => coeff t && pairVec i j t) = {i, j} := by
  ext t
  by_cases hti : t = i
  · subst hti
    simp [hall, pairVec, hij]
  · by_cases htj : t = j
    · subst htj
      simp [hall, pairVec, hti]
    · simp [hall, pairVec, hti, htj]

theorem columnParity_all_true_singletonVec
    {d : ℕ} {coeff : BitVec d}
    (hall : ∀ t, coeff t = true) (i : Fin d) :
    columnParity coeff (singletonVec i) = true := by
  rw [columnParity, singleton_support_of_all_true hall i]
  simp

theorem columnParity_all_true_pairVec
    {d : ℕ} {coeff : BitVec d}
    (hall : ∀ t, coeff t = true) {i j : Fin d} (hij : i ≠ j) :
    columnParity coeff (pairVec i j) = false := by
  rw [columnParity, pair_support_of_all_true hall hij]
  simp [hij]

theorem columnParity_zeroVec
    {d : ℕ} (coeff : BitVec d) :
    columnParity coeff (zeroVec : BitVec d) = false := by
  simp [columnParity, zeroVec]

theorem affineColumnPredict_eq_false_of_not_exists_true
    {d : ℕ} {coeff : BitVec d} {bias : Bool}
    (hno : ¬ ∃ x, affineColumnPredict coeff bias x = true)
    (x : BitVec d) :
    affineColumnPredict coeff bias x = false := by
  cases hx : affineColumnPredict coeff bias x with
  | false =>
      rfl
  | true =>
      exact False.elim <| hno ⟨x, hx⟩

theorem exists_two_distinct_affineColumnPredict_true_of_one_lt
    {d : ℕ} {coeff : BitVec d} {bias : Bool}
    (hd : 1 < d)
    (hw : ∃ x, affineColumnPredict coeff bias x = true) :
    ∃ x y : BitVec d,
      x ≠ y ∧
      affineColumnPredict coeff bias x = true ∧
      affineColumnPredict coeff bias y = true := by
  classical
  by_cases hall : ∀ t, coeff t = true
  · let i0 : Fin d := ⟨0, Nat.lt_trans Nat.zero_lt_one hd⟩
    let i1 : Fin d := ⟨1, hd⟩
    have hi01 : i0 ≠ i1 := by
      simp [i0, i1]
    cases bias with
    | false =>
        refine ⟨singletonVec i0, singletonVec i1, ?_, ?_, ?_⟩
        · exact singletonVec_ne_singletonVec hi01
        · simp [affineColumnPredict, columnParity_all_true_singletonVec, hall]
        · simp [affineColumnPredict, columnParity_all_true_singletonVec, hall]
    | true =>
        refine ⟨(zeroVec : BitVec d), pairVec i0 i1, ?_, ?_, ?_⟩
        · exact fun h => pairVec_ne_zeroVec hi01 h.symm
        · simp [affineColumnPredict, columnParity_zeroVec]
        · simp [affineColumnPredict, columnParity_all_true_pairVec, hall, hi01]
  · push_neg at hall
    rcases hall with ⟨i, hi⟩
    cases hcoeff : coeff i with
    | false =>
        rcases hw with ⟨x, hx⟩
        refine ⟨x, toggleBit x i, ?_, hx, ?_⟩
        · exact (toggleBit_ne_self x i).symm
        · calc
            affineColumnPredict coeff bias (toggleBit x i)
              = affineColumnPredict coeff bias x := by
                  simpa [hcoeff] using
                    affineColumnPredict_toggleBit_of_coeff_false coeff bias x i hcoeff
            _ = true := hx
    | true =>
        exact False.elim (hi hcoeff)

theorem not_injective_firstActiveFeature_affineFeatureVector_of_one_lt
    {p d : ℕ}
    (features : Fin p → AffineColumnCode d)
    (hd : 1 < d) :
    ¬ Function.Injective
      (fun x : BitVec d => firstActiveFeature? (affineFeatureVector features x)) := by
  classical
  let active : Finset (Fin p) :=
    (Finset.univ : Finset (Fin p)).filter fun j =>
      ∃ x, affineColumnPredict (features j).1 (features j).2 x = true
  by_cases hne : active.Nonempty
  · let j : Fin p := active.min' hne
    have hjmem : j ∈ active := Finset.min'_mem active hne
    have hjtrue : ∃ x, affineColumnPredict (features j).1 (features j).2 x = true := by
      simpa [active] using hjmem
    rcases exists_two_distinct_affineColumnPredict_true_of_one_lt
        (coeff := (features j).1) (bias := (features j).2) hd hjtrue with
      ⟨x, y, hxy, hx, hy⟩
    have hxsig :
        firstActiveFeature? (affineFeatureVector features x) = some j := by
      apply (firstActiveFeature?_eq_some_iff (featureVec := affineFeatureVector features x) (j := j)).2
      refine ⟨?_, ?_⟩
      · simpa [affineFeatureVector] using hx
      · intro i hij
        have himem : i ∉ active := by
          intro hi
          exact (not_le_of_gt hij) (Finset.min'_le active i hi)
        have hiempty : ¬ ∃ z, affineColumnPredict (features i).1 (features i).2 z = true := by
          simpa [active] using himem
        simpa [affineFeatureVector] using
          affineColumnPredict_eq_false_of_not_exists_true hiempty x
    have hysig :
        firstActiveFeature? (affineFeatureVector features y) = some j := by
      apply (firstActiveFeature?_eq_some_iff (featureVec := affineFeatureVector features y) (j := j)).2
      refine ⟨?_, ?_⟩
      · simpa [affineFeatureVector] using hy
      · intro i hij
        have himem : i ∉ active := by
          intro hi
          exact (not_le_of_gt hij) (Finset.min'_le active i hi)
        have hiempty : ¬ ∃ z, affineColumnPredict (features i).1 (features i).2 z = true := by
          simpa [active] using himem
        simpa [affineFeatureVector] using
          affineColumnPredict_eq_false_of_not_exists_true hiempty y
    intro hinj
    exact hxy (hinj (hxsig.trans hysig.symm))
  · let i0 : Fin d := ⟨0, Nat.lt_trans Nat.zero_lt_one hd⟩
    have hallfalse :
        ∀ j x, affineColumnPredict (features j).1 (features j).2 x = false := by
      intro j x
      have hjmem : j ∉ active := by
        intro hj
        exact hne ⟨j, hj⟩
      have hjempty : ¬ ∃ z, affineColumnPredict (features j).1 (features j).2 z = true := by
        simpa [active] using hjmem
      exact affineColumnPredict_eq_false_of_not_exists_true hjempty x
    have hnone0 :
        firstActiveFeature? (affineFeatureVector features (zeroVec : BitVec d)) = none := by
      refine (firstActiveFeature?_eq_none_iff
        (featureVec := affineFeatureVector features (zeroVec : BitVec d))).2 ?_
      intro j
      simpa [affineFeatureVector] using hallfalse j (zeroVec : BitVec d)
    have hnone1 :
        firstActiveFeature? (affineFeatureVector features (singletonVec i0)) = none := by
      refine (firstActiveFeature?_eq_none_iff
        (featureVec := affineFeatureVector features (singletonVec i0))).2 ?_
      intro j
      simpa [affineFeatureVector] using hallfalse j (singletonVec i0)
    intro hinj
    exact singletonVec_ne_zeroVec i0 <| hinj (hnone1.trans hnone0.symm)

end RawBitVec

section ExactZAB

theorem bitVecZABVisibleData_bijective {n k : ℕ} :
    Function.Bijective (bitVecZABVisibleData (r := n) (k := k)) := by
  refine (Fintype.bijective_iff_injective_and_card
    (bitVecZABVisibleData (r := n) (k := k))).2 ?_
  refine ⟨bitVecZABVisibleData_injective (n := n) (k := k), ?_⟩
  rw [card_exactVisiblePostSwitchSurface_bitVec, card_bitVecZABVisibleSurface]

theorem not_injective_exactZABAffineDecisionListSignature_id_of_one_lt
    {n p k : ℕ}
    (features : Fin p → AffineColumnCode (n + (k + k)))
    (hwidth : 1 < n + (k + k)) :
    ¬ Function.Injective
      (exactZABAffineDecisionListSignature
        (Z := BitVec n) (p := p) (r := n) (k := k)
        (fun z => z) features) := by
  let g : BitVec (n + (k + k)) → Option (Fin p) :=
    fun x => firstActiveFeature? (affineFeatureVector features x)
  have hginj :
      ¬ Function.Injective g :=
    not_injective_firstActiveFeature_affineFeatureVector_of_one_lt
      (features := features) hwidth
  have hsurj :
      Function.Surjective (bitVecZABVisibleData (r := n) (k := k)) :=
    (bitVecZABVisibleData_bijective (n := n) (k := k)).2
  intro hinj
  apply hginj
  intro x y hxy
  rcases hsurj x with ⟨u, rfl⟩
  rcases hsurj y with ⟨v, rfl⟩
  have huv : u = v := by
    apply hinj
    simpa [g, exactZABAffineDecisionListSignature, exactZABAffineFeatureSummary] using hxy
  simp [huv]

theorem fullExactVisibleRuleFamily_not_realizedBySharedExactZABAffineDecisionListFamily_id_of_one_lt
    {n p k : ℕ}
    (features : Fin p → AffineColumnCode (n + (k + k)))
    (hwidth : 1 < n + (k + k)) :
    ¬ RealizedBySharedExactZABAffineDecisionListFamily
        (Z := BitVec n) (p := p) (r := n) (k := k)
        (fun z => z) features
        (fullExactVisibleRuleFamily (BitVec n) k) := by
  exact
    fullExactVisibleRuleFamily_not_realizedBySharedExactZABAffineDecisionListFamily_of_not_injective_signature
      (Z := BitVec n) (p := p) (r := n) (k := k)
      (fun z => z) features
      (not_injective_exactZABAffineDecisionListSignature_id_of_one_lt
        (p := p) (k := k) features hwidth)

end ExactZAB

end Mettapedia.Computability.PNP
