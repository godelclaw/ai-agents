import Mettapedia.Computability.PNP.CanonicalABTargetRoute
import Mettapedia.Computability.PNP.ExactZABDecisionListStructuralObstruction
import Mettapedia.Computability.PNP.SharedExactZABAffineDecisionListCharacterization

namespace Mettapedia.Computability.PNP

theorem fullExactVisibleRuleFamily_realizedBySharedExactZABAffineDecisionListFamily_bool0_regression :
    RealizedBySharedExactZABAffineDecisionListFamily
      (Z := Bool) (p := 1) (r := 1) (k := 0)
      (fun z _ => z)
      (canonicalAffineBasis 1)
      (fullExactVisibleRuleFamily Bool 0) := by
  exact
    fullExactVisibleRuleFamily_realizedBySharedExactZABAffineDecisionListFamily_of_injective_signature
      (Z := Bool) (p := 1) (r := 1) (k := 0)
      (fun z _ => z)
      (canonicalAffineBasis 1)
      (by
        intro u v huv
        cases u with
        | mk uz ua ub =>
            cases v with
            | mk vz va vb =>
                cases uz <;> cases vz
                · have ha : ua = va := by
                    funext i
                    exact Fin.elim0 i
                  have hb : ub = vb := by
                    funext i
                    exact Fin.elim0 i
                  cases ha
                  cases hb
                  rfl
                · simp [exactZABAffineDecisionListSignature, exactZABAffineFeatureSummary,
                    affineFeatureVector_canonicalAffineBasis, exactZABVisibleData] at huv
                  have hfalse :
                      firstActiveFeature? (r := 1)
                        (Fin.append (fun _ : Fin 1 => false)
                          (exactABVisibleData (Z := Bool) (k := 0) ⟨false, ua, ub⟩)) =
                        (none : Option (Fin 1)) := by
                    have happend :
                        Fin.append (fun _ : Fin 1 => false)
                          (exactABVisibleData (Z := Bool) (k := 0) ⟨false, ua, ub⟩) =
                          (zeroVec : BitVec 1) := by
                      funext i
                      fin_cases i
                      rfl
                    rw [happend]
                    exact firstActiveFeature?_zeroVec
                  have htrue :
                      firstActiveFeature? (r := 1)
                        (Fin.append (fun _ : Fin 1 => true)
                          (exactABVisibleData (Z := Bool) (k := 0) ⟨true, va, vb⟩)) =
                        some (0 : Fin 1) := by
                    apply
                      (firstActiveFeature?_eq_some_iff
                        (featureVec := Fin.append (fun _ : Fin 1 => true)
                          (exactABVisibleData (Z := Bool) (k := 0) ⟨true, va, vb⟩))
                        (j := (0 : Fin 1))).2
                    constructor
                    · rfl
                    · intro i hi
                      fin_cases i
                      exact (Nat.not_lt_zero _ hi).elim
                  rw [hfalse, htrue] at huv
                  cases huv
                · simp [exactZABAffineDecisionListSignature, exactZABAffineFeatureSummary,
                    affineFeatureVector_canonicalAffineBasis, exactZABVisibleData] at huv
                  have htrue :
                      firstActiveFeature? (r := 1)
                        (Fin.append (fun _ : Fin 1 => true)
                          (exactABVisibleData (Z := Bool) (k := 0) ⟨true, ua, ub⟩)) =
                        some (0 : Fin 1) := by
                    apply
                      (firstActiveFeature?_eq_some_iff
                        (featureVec := Fin.append (fun _ : Fin 1 => true)
                          (exactABVisibleData (Z := Bool) (k := 0) ⟨true, ua, ub⟩))
                        (j := (0 : Fin 1))).2
                    constructor
                    · rfl
                    · intro i hi
                      fin_cases i
                      exact (Nat.not_lt_zero _ hi).elim
                  have hfalse :
                      firstActiveFeature? (r := 1)
                        (Fin.append (fun _ : Fin 1 => false)
                          (exactABVisibleData (Z := Bool) (k := 0) ⟨false, va, vb⟩)) =
                        (none : Option (Fin 1)) := by
                    have happend :
                        Fin.append (fun _ : Fin 1 => false)
                          (exactABVisibleData (Z := Bool) (k := 0) ⟨false, va, vb⟩) =
                          (zeroVec : BitVec 1) := by
                      funext i
                      fin_cases i
                      rfl
                    rw [happend]
                    exact firstActiveFeature?_zeroVec
                  rw [htrue, hfalse] at huv
                  cases huv
                · have ha : ua = va := by
                    funext i
                    exact Fin.elim0 i
                  have hb : ub = vb := by
                    funext i
                    exact Fin.elim0 i
                  cases ha
                  cases hb
                  rfl)

theorem fullExactVisibleRuleFamily_not_realizedBySharedExactZABAffineDecisionListFamily_bool0_p0_regression :
    ¬ RealizedBySharedExactZABAffineDecisionListFamily
        (Z := Bool) (p := 0) (r := 0) (k := 0)
        (fun _ => zeroVec)
        (fun i => nomatch i)
        (fullExactVisibleRuleFamily Bool 0) := by
  exact
    fullExactVisibleRuleFamily_not_realizedBySharedExactZABAffineDecisionListFamily_of_not_injective_signature
      (Z := Bool) (p := 0) (r := 0) (k := 0)
      (fun _ => zeroVec)
      (fun i => nomatch i)
      (by
        intro hinj
        let uTrue : ExactVisiblePostSwitchSurface Bool 0 := ⟨true, zeroVec, zeroVec⟩
        let uFalse : ExactVisiblePostSwitchSurface Bool 0 := ⟨false, zeroVec, zeroVec⟩
        have heqSig :
            exactZABAffineDecisionListSignature
              (Z := Bool) (p := 0) (r := 0) (k := 0)
              (fun _ => zeroVec) (fun i => nomatch i) uTrue =
            exactZABAffineDecisionListSignature
              (Z := Bool) (p := 0) (r := 0) (k := 0)
              (fun _ => zeroVec) (fun i => nomatch i) uFalse := by
          rfl
        have hu : uTrue = uFalse := hinj heqSig
        have hz : true = false := by
          simpa [uTrue, uFalse] using congrArg PostSwitchInput.z hu
        cases hz)

end Mettapedia.Computability.PNP
