import Mettapedia.Computability.PNP.SharedExactZABSparseThresholdSharpness

/-!
# P vs NP route liveness: injective exact `z+a+b` summaries keep the shared
  sparse-threshold branch alive

`SharedExactZABSparseThresholdSharpness.lean` proved that the shared exact
sparse-threshold route is fully expressive on the native identity-extractor
surface `Z = BitVec n`.

This file lifts that witness to the general exact surface.  If the visible map
`exactZABVisibleData zfeat : (z,a,b) ↦ (zfeat z,a,b)` is injective, then any
Boolean rule on the exact surface can be extended to an arbitrary Boolean rule
on the ambient bitvector space `BitVec (r + 2k)`.  The point-block
sparse-threshold witness then realizes that ambient rule, and injectivity pulls
the result back to the exact surface.

So the shared exact sparse-threshold branch is not merely alive for identity
extractors.  It stays alive for every injective extractor `zfeat`.
-/

namespace Mettapedia.Computability.PNP

section VisibleData

variable {Z : Type*} {r k : ℕ}

theorem exactZABVisibleData_injective_of_injective_zfeat
    (zfeat : Z → BitVec r)
    (hinj : Function.Injective zfeat) :
    Function.Injective (exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat) := by
  intro u v huv
  cases u with
  | mk uz ua ub =>
      cases v with
      | mk vz va vb =>
          have hz : uz = vz := by
            apply hinj
            funext i
            have h := congrFun huv (Fin.castAdd (k + k) i)
            simpa [exactZABVisibleData, exactABVisibleData, Fin.append_left] using h
          have hab : Fin.append ua ub = Fin.append va vb := by
            funext j
            have h := congrFun huv (Fin.natAdd r j)
            simpa [exactZABVisibleData, exactABVisibleData, Fin.append_right] using h
          have ha : ua = va := by
            funext i
            have h := congrFun hab (Fin.castAdd k i)
            simpa [Fin.append_left] using h
          have hb : ub = vb := by
            funext i
            have h := congrFun hab (Fin.natAdd k i)
            rw [Fin.append_right, Fin.append_right] at h
            exact h
          cases hz
          cases ha
          cases hb
          rfl

end VisibleData

section ExactZAB

variable {Z : Type*} {r k : ℕ}

@[simp] theorem sharedExactZABSparseThresholdAffinePredict_allAffinePointBlockFeatures_eq_raw
    (zfeat : Z → BitVec r)
    (code : SharedSparseThresholdCode
      (allAffinePointBlockFeatureCount (r + (k + k))))
    (u : ExactVisiblePostSwitchSurface Z k) :
    sharedExactZABSparseThresholdAffinePredict
        (Z := Z)
        (p := allAffinePointBlockFeatureCount (r + (k + k)))
        (r := r) (k := k)
        zfeat
        (allAffinePointBlockFeatures (r + (k + k))) code u =
      rawSharedSparseThresholdPredict
        (allAffinePointBlockFeatures (r + (k + k))) code
        (exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat u) := by
  simp [sharedExactZABSparseThresholdAffinePredict, rawSharedSparseThresholdPredict]

theorem fullExactVisibleRuleFamily_realizedBySharedExactZABSparseThresholdAffineFamily_of_injective_exactZABVisibleData
    (zfeat : Z → BitVec r)
    (hinj :
      Function.Injective (exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat))
    (hwidth : 0 < r + (k + k)) :
    RealizedBySharedExactZABSparseThresholdAffineFamily
      (Z := Z)
      (p := allAffinePointBlockFeatureCount (r + (k + k)))
      (r := r) (k := k)
      zfeat
      (allAffinePointBlockFeatures (r + (k + k)))
      (fullExactVisibleRuleFamily Z k) := by
  classical
  intro rule
  let summary :=
    exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat
  let rawRule : BitVec (r + (k + k)) → Bool := fun x =>
    if h : ∃ u, summary u = x then
      rule (Classical.choose h)
    else
      false
  refine ⟨pointBlockSparseThresholdCode (d := r + (k + k)) hwidth rawRule, ?_⟩
  funext u
  have hlookup : rawRule (summary u) = rule u := by
    dsimp [rawRule]
    split_ifs with h
    · have hchoose : Classical.choose h = u := by
        apply hinj
        exact Classical.choose_spec h
      simp [hchoose]
    · exfalso
      exact h ⟨u, rfl⟩
  have hraw :
      rawSharedSparseThresholdPredict
          (allAffinePointBlockFeatures (r + (k + k)))
          (pointBlockSparseThresholdCode (d := r + (k + k)) hwidth rawRule)
          (summary u) =
        rawRule (summary u) := by
    simpa [summary, rawRule] using
      congrFun
        (rawSharedSparseThresholdPredict_allAffinePointBlockFeatures_eq
          (d := r + (k + k)) hwidth rawRule)
        (summary u)
  calc
    (fullExactVisibleRuleFamily Z k).predict rule u = rule u := by
      rfl
    _ = rawRule (summary u) := by
      symm
      exact hlookup
    _ =
        rawSharedSparseThresholdPredict
          (allAffinePointBlockFeatures (r + (k + k)))
          (pointBlockSparseThresholdCode (d := r + (k + k)) hwidth rawRule)
          (summary u) := by
            symm
            exact hraw
    _ =
        sharedExactZABSparseThresholdAffinePredict
          (Z := Z)
          (p := allAffinePointBlockFeatureCount (r + (k + k)))
          (r := r) (k := k)
          zfeat
          (allAffinePointBlockFeatures (r + (k + k)))
          (pointBlockSparseThresholdCode (d := r + (k + k)) hwidth rawRule) u := by
            change
              rawSharedSparseThresholdPredict
                  (allAffinePointBlockFeatures (r + (k + k)))
                  (pointBlockSparseThresholdCode (d := r + (k + k)) hwidth rawRule)
                  (exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat u) =
                sharedExactZABSparseThresholdAffinePredict
                  (Z := Z)
                  (p := allAffinePointBlockFeatureCount (r + (k + k)))
                  (r := r) (k := k)
                  zfeat
                  (allAffinePointBlockFeatures (r + (k + k)))
                  (pointBlockSparseThresholdCode (d := r + (k + k)) hwidth rawRule) u
            exact
              (sharedExactZABSparseThresholdAffinePredict_allAffinePointBlockFeatures_eq_raw
                (Z := Z) (r := r) (k := k) zfeat
                (pointBlockSparseThresholdCode (d := r + (k + k)) hwidth rawRule) u).symm

theorem fullExactVisibleRuleFamily_realizedBySharedExactZABSparseThresholdAffineFamily_of_injective_zfeat
    (zfeat : Z → BitVec r)
    (hinj : Function.Injective zfeat)
    (hwidth : 0 < r + (k + k)) :
    RealizedBySharedExactZABSparseThresholdAffineFamily
      (Z := Z)
      (p := allAffinePointBlockFeatureCount (r + (k + k)))
      (r := r) (k := k)
      zfeat
      (allAffinePointBlockFeatures (r + (k + k)))
      (fullExactVisibleRuleFamily Z k) := by
  exact
    fullExactVisibleRuleFamily_realizedBySharedExactZABSparseThresholdAffineFamily_of_injective_exactZABVisibleData
      (Z := Z) (r := r) (k := k) zfeat
      (exactZABVisibleData_injective_of_injective_zfeat
        (Z := Z) (r := r) (k := k) zfeat hinj)
      hwidth

end ExactZAB

end Mettapedia.Computability.PNP
