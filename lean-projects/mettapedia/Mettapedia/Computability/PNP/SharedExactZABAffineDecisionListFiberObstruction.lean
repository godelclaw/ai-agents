import Mettapedia.Computability.PNP.SharedExactZABAffineDecisionListStructuralObstruction
import Mettapedia.Computability.PNP.SharedExactZABTargetInterface
import Mathlib.Tactic

/-!
# P vs NP crux: shared exact affine decision-list signatures already fail on
  every fixed-`z` fiber

The earlier characterization reduced the shared exact affine decision-list route
to one question: is the first-active shared signature injective on the exact
visible surface?

This file proves a stronger structural obstruction than the identity-extractor
packet. For any fixed latent datum `z0`, restricting the signature to the fiber
above `z0` turns it into an ordinary first-active affine signature on the
visible `(a, b)` bits alone. Once `k > 0`, that fiber has width `2k > 1`, and
the previously proved raw `BitVec` obstruction applies immediately.

So for every nonempty latent type `Z`, every extractor `zfeat : Z → BitVec r`,
and every shared affine basis, the shared affine decision-list route is already
noninjective as soon as `k > 0`. Hence it cannot realize the full exact rule
family and cannot support a surjective exact switched family.
-/

namespace Mettapedia.Computability.PNP

open Fin
open scoped ENNReal

section FiberReduction

def prefixSlice {r m : ℕ} (coeff : BitVec (r + m)) : BitVec r :=
  fun i => coeff (Fin.castAdd m i)

def suffixSlice {r m : ℕ} (coeff : BitVec (r + m)) : BitVec m :=
  fun i => coeff (Fin.natAdd r i)

def fiberAffineColumnCode {r m : ℕ}
    (head : BitVec r) (code : AffineColumnCode (r + m)) : AffineColumnCode m :=
  (suffixSlice code.1, Bool.xor (columnParity (prefixSlice code.1) head) code.2)

def leftBits {k : ℕ} (x : BitVec (k + k)) : BitVec k :=
  fun i => x (Fin.castAdd k i)

def rightBits {k : ℕ} (x : BitVec (k + k)) : BitVec k :=
  fun i => x (Fin.natAdd k i)

def fiberPoint {Z : Type*} {k : ℕ} (z : Z) (x : BitVec (k + k)) :
    ExactVisiblePostSwitchSurface Z k :=
  ⟨z, leftBits x, rightBits x⟩

@[simp] theorem append_leftBits_rightBits {k : ℕ} (x : BitVec (k + k)) :
    Fin.append (leftBits x) (rightBits x) = x := by
  funext i
  cases i using Fin.addCases with
  | left i =>
      simp [leftBits]
  | right i =>
      rw [Fin.append_right]
      rfl

theorem filteredSupportCard_append
    {r m : ℕ} (coeff : BitVec (r + m)) (head : BitVec r) (tail : BitVec m) :
    (((Finset.univ : Finset (Fin (r + m))).filter
        fun i => coeff i && Fin.append head tail i).card)
      =
        (((Finset.univ : Finset (Fin r)).filter
          fun i => prefixSlice coeff i && head i).card)
        +
        (((Finset.univ : Finset (Fin m)).filter
          fun i => suffixSlice coeff i && tail i).card) := by
  let leftSet : Finset (Fin (r + m)) :=
    (((Finset.univ : Finset (Fin r)).filter
      fun i => prefixSlice coeff i && head i).map (Fin.castAddEmb m))
  let rightSet : Finset (Fin (r + m)) :=
    (((Finset.univ : Finset (Fin m)).filter
      fun i => suffixSlice coeff i && tail i).map (Fin.natAddEmb r))
  have hdisj : Disjoint leftSet rightSet := by
    refine Finset.disjoint_left.mpr ?_
    intro i hiL hiR
    rcases Finset.mem_map.mp hiL with ⟨j, hj, hjEq⟩
    rcases Finset.mem_map.mp hiR with ⟨j', hj', hjEq'⟩
    have hEq : (Fin.castAdd m j : Fin (r + m)) = Fin.natAdd r j' := by
      simpa using hjEq.trans hjEq'.symm
    have hlt : (Fin.castAdd m j : Fin (r + m)) < Fin.natAdd r j' := by
      exact Fin.lt_def.mpr
        (lt_of_lt_of_le (Fin.castAdd_lt m j) (Fin.le_coe_natAdd r j'))
    exact (ne_of_lt hlt) hEq
  have hunion :
      ((Finset.univ : Finset (Fin (r + m))).filter
          fun i => coeff i && Fin.append head tail i)
        =
        leftSet.disjUnion rightSet hdisj := by
    ext i
    cases i using Fin.addCases with
    | left j =>
        simp [leftSet, rightSet, prefixSlice]
        intro x hxCoeff hxTail hEq
        have hlt : (Fin.castAdd m j : Fin (r + m)) < Fin.natAdd r x := by
          exact Fin.lt_def.mpr
            (lt_of_lt_of_le (Fin.castAdd_lt m j) (Fin.le_coe_natAdd r x))
        exact False.elim ((ne_of_lt hlt) hEq.symm)
    | right j =>
        simp [leftSet, rightSet, suffixSlice]
        intro x hxCoeff hxHead hEq
        have hlt : (Fin.castAdd m x : Fin (r + m)) < Fin.natAdd r j := by
          exact Fin.lt_def.mpr
            (lt_of_lt_of_le (Fin.castAdd_lt m x) (Fin.le_coe_natAdd r j))
        exact False.elim ((ne_of_lt hlt) hEq)
  calc
    (((Finset.univ : Finset (Fin (r + m))).filter
        fun i => coeff i && Fin.append head tail i).card)
      = (leftSet.disjUnion rightSet hdisj).card := by
          rw [hunion]
    _ = leftSet.card + rightSet.card := Finset.card_disjUnion _ _ _
    _ =
        (((Finset.univ : Finset (Fin r)).filter
          fun i => prefixSlice coeff i && head i).card)
        +
        (((Finset.univ : Finset (Fin m)).filter
          fun i => suffixSlice coeff i && tail i).card) := by
            simp [leftSet, rightSet]

theorem decide_odd_add_eq_xor (a b : ℕ) :
    decide (Odd (a + b)) = Bool.xor (decide (Odd a)) (decide (Odd b)) := by
  by_cases ha : Odd a
  · by_cases hb : Odd b
    · simp [ha, hb, Nat.odd_add, Bool.xor]
    · have hbEven : Even b := Nat.not_odd_iff_even.mp hb
      simp [ha, hb, hbEven, Nat.odd_add, Bool.xor]
  · have haEven : Even a := Nat.not_odd_iff_even.mp ha
    by_cases hb : Odd b
    · simp [ha, hb, Nat.odd_add, Bool.xor]
    · have hbEven : Even b := Nat.not_odd_iff_even.mp hb
      simp [ha, hb, hbEven, Nat.odd_add, Bool.xor]

theorem columnParity_append
    {r m : ℕ} (coeff : BitVec (r + m)) (head : BitVec r) (tail : BitVec m) :
    columnParity coeff (Fin.append head tail) =
      Bool.xor (columnParity (prefixSlice coeff) head)
        (columnParity (suffixSlice coeff) tail) := by
  let a : ℕ :=
    (((Finset.univ : Finset (Fin r)).filter
      fun i => prefixSlice coeff i && head i).card)
  let b : ℕ :=
    (((Finset.univ : Finset (Fin m)).filter
      fun i => suffixSlice coeff i && tail i).card)
  have hcard :
      (((Finset.univ : Finset (Fin (r + m))).filter
          fun i => coeff i && Fin.append head tail i).card) = a + b := by
    simpa [a, b] using filteredSupportCard_append coeff head tail
  unfold columnParity
  rw [hcard]
  simpa [a, b] using decide_odd_add_eq_xor a b

theorem affineColumnPredict_append
    {r m : ℕ} (code : AffineColumnCode (r + m))
    (head : BitVec r) (tail : BitVec m) :
    affineColumnPredict code.1 code.2 (Fin.append head tail) =
      affineColumnPredict (fiberAffineColumnCode head code).1
        (fiberAffineColumnCode head code).2 tail := by
  rw [affineColumnPredict, affineColumnPredict, fiberAffineColumnCode, columnParity_append]
  cases hp : columnParity (prefixSlice code.1) head <;>
    cases hs : columnParity (suffixSlice code.1) tail <;>
    cases hb : code.2 <;> rfl

theorem affineFeatureVector_append
    {p r m : ℕ} (features : Fin p → AffineColumnCode (r + m))
    (head : BitVec r) (tail : BitVec m) :
    affineFeatureVector features (Fin.append head tail) =
      affineFeatureVector (fun j => fiberAffineColumnCode head (features j)) tail := by
  funext j
  simpa [affineFeatureVector] using
    affineColumnPredict_append (code := features j) head tail

@[simp] theorem exactZABVisibleData_fiberPoint
    {Z : Type*} {r k : ℕ} (zfeat : Z → BitVec r) (z : Z) (x : BitVec (k + k)) :
    exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat (fiberPoint z x) =
      Fin.append (zfeat z) x := by
  simp [fiberPoint, exactZABVisibleData, exactABVisibleData, append_leftBits_rightBits]

theorem exactZABAffineDecisionListSignature_fiberPoint
    {Z : Type*} {p r k : ℕ}
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (z : Z) (x : BitVec (k + k)) :
    exactZABAffineDecisionListSignature
        (Z := Z) (p := p) (r := r) (k := k) zfeat features
        (fiberPoint z x)
      =
        firstActiveFeature?
          (affineFeatureVector
            (fun j => fiberAffineColumnCode (zfeat z) (features j)) x) := by
  simp [exactZABAffineDecisionListSignature, exactZABAffineFeatureSummary,
    affineFeatureVector_append]

end FiberReduction

section Obstruction

theorem not_injective_exactZABAffineDecisionListSignature_of_pos
    {Z : Type*} [Nonempty Z]
    {p r k : ℕ}
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (hk : 0 < k) :
    ¬ Function.Injective
      (exactZABAffineDecisionListSignature
        (Z := Z) (p := p) (r := r) (k := k) zfeat features) := by
  classical
  let z0 : Z := Classical.choice ‹Nonempty Z›
  let fiberFeatures : Fin p → AffineColumnCode (k + k) :=
    fun j => fiberAffineColumnCode (zfeat z0) (features j)
  have hwidth : 1 < k + k := by
    omega
  have hfiber :
      ¬ Function.Injective
        (fun x : BitVec (k + k) =>
          firstActiveFeature? (affineFeatureVector fiberFeatures x)) := by
    exact
      not_injective_firstActiveFeature_affineFeatureVector_of_one_lt
        (features := fiberFeatures) hwidth
  intro hinj
  apply hfiber
  intro x y hxy
  have huv : fiberPoint z0 x = fiberPoint z0 y := by
    apply hinj
    rw [exactZABAffineDecisionListSignature_fiberPoint,
      exactZABAffineDecisionListSignature_fiberPoint]
    simpa [fiberFeatures, z0] using hxy
  have hab :
      Fin.append (fiberPoint z0 x).a (fiberPoint z0 x).b =
        Fin.append (fiberPoint z0 y).a (fiberPoint z0 y).b := by
    simpa using congrArg
      (fun u : ExactVisiblePostSwitchSurface Z k => Fin.append u.a u.b) huv
  simpa [fiberPoint, append_leftBits_rightBits] using hab

theorem fullExactVisibleRuleFamily_not_realizedBySharedExactZABAffineDecisionListFamily_of_pos
    {Z : Type*} [Nonempty Z]
    {p r k : ℕ}
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (hk : 0 < k) :
    ¬ RealizedBySharedExactZABAffineDecisionListFamily
        (Z := Z) (p := p) (r := r) (k := k)
        zfeat features
        (fullExactVisibleRuleFamily Z k) := by
  exact
    fullExactVisibleRuleFamily_not_realizedBySharedExactZABAffineDecisionListFamily_of_not_injective_signature
      (Z := Z) (p := p) (r := r) (k := k) zfeat features
      (not_injective_exactZABAffineDecisionListSignature_of_pos
        (Z := Z) (p := p) (r := r) (k := k) zfeat features hk)

theorem SharedExactZABDecisionListTargetData.not_surjective_predict_of_pos
    {Z : Type*} [Nonempty Z]
    {p r k : ℕ} {Index : Type*}
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h :
      SharedExactZABDecisionListTargetData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
        zfeat features G)
    (hk : 0 < k) :
    ¬ Function.Surjective G.predict := by
  intro hsurj
  exact
    (not_injective_exactZABAffineDecisionListSignature_of_pos
      (Z := Z) (p := p) (r := r) (k := k) zfeat features hk)
      (injective_signature_of_surjective_predict_of_realizedBySharedExactZABAffineDecisionListFamily
        (Z := Z) (p := p) (r := r) (k := k)
        (G := G) h.realized hsurj)

theorem SharedExactZABDecisionListRecoveryData.not_surjective_predict_of_pos
    {Z : Type*} [Fintype Z] [Nonempty Z]
    {p r k : ℕ} {Index : Type*}
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABDecisionListRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
        μ zfeat features G q)
    (hk : 0 < k) :
    ¬ Function.Surjective G.predict := by
  exact (h.targetData).not_surjective_predict_of_pos hk

end Obstruction

end Mettapedia.Computability.PNP
