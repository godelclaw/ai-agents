import Mettapedia.Computability.PNP.SharedExactZABAffineFeatureCharacterization

namespace Mettapedia.Computability.PNP

theorem fullExactVisibleRuleFamily_realizedBySharedExactZABAffineFeatureFamily_unit0_regression :
    RealizedBySharedExactZABAffineFeatureFamily
      (Z := Unit) (p := 0) (r := 0) (k := 0)
      (fun _ => zeroVec)
      (fun i => nomatch i)
      (fullExactVisibleRuleFamily Unit 0) := by
  refine
    fullExactVisibleRuleFamily_realizedBySharedExactZABAffineFeatureFamily_of_injective_summary
      (Z := Unit) (p := 0) (r := 0) (k := 0)
      (fun _ => zeroVec) (fun i => nomatch i) ?_
  intro u v huv
  cases u with
  | mk z1 a1 b1 =>
      cases v with
      | mk z2 a2 b2 =>
          have hz : z1 = z2 := by
            cases z1
            cases z2
            rfl
          have ha : a1 = a2 := by
            funext i
            exact nomatch i
          have hb : b1 = b2 := by
            funext i
            exact nomatch i
          cases hz
          cases ha
          cases hb
          rfl

theorem fullExactVisibleRuleFamily_not_realizedBySharedExactZABAffineFeatureFamily_bool0_regression :
    ¬ RealizedBySharedExactZABAffineFeatureFamily
        (Z := Bool) (p := 0) (r := 0) (k := 0)
        (fun _ => zeroVec)
        (fun i => nomatch i)
        (fullExactVisibleRuleFamily Bool 0) := by
  refine
    fullExactVisibleRuleFamily_not_realizedBySharedExactZABAffineFeatureFamily_of_not_injective_summary
      (Z := Bool) (p := 0) (r := 0) (k := 0)
      (fun _ => zeroVec) (fun i => nomatch i) ?_
  intro hinj
  let u0 : ExactVisiblePostSwitchSurface Bool 0 := ⟨false, zeroVec, zeroVec⟩
  let u1 : ExactVisiblePostSwitchSurface Bool 0 := ⟨true, zeroVec, zeroVec⟩
  have hsame :
      exactZABAffineFeatureSummary
          (Z := Bool) (p := 0) (r := 0) (k := 0)
          (fun _ => zeroVec) (fun i => nomatch i) u0 =
        exactZABAffineFeatureSummary
          (Z := Bool) (p := 0) (r := 0) (k := 0)
          (fun _ => zeroVec) (fun i => nomatch i) u1 := rfl
  have hneq : u0 ≠ u1 := by
    intro h
    have hz : (false : Bool) = true := by
      simpa [u0, u1] using congrArg PostSwitchInput.z h
    cases hz
  exact hneq (hinj hsame)

theorem fullExactVisibleRuleFamily_realizedBySharedExactZABAffineFeatureFamily_iff_injective_summary_unit0_regression :
    Function.Injective
      (exactZABAffineFeatureSummary
        (Z := Unit) (p := 0) (r := 0) (k := 0)
        (fun _ => zeroVec) (fun i => nomatch i)) := by
  exact
    (fullExactVisibleRuleFamily_realizedBySharedExactZABAffineFeatureFamily_iff_injective_summary
      (Z := Unit) (p := 0) (r := 0) (k := 0)
      (fun _ => zeroVec) (fun i => nomatch i)).mp
      fullExactVisibleRuleFamily_realizedBySharedExactZABAffineFeatureFamily_unit0_regression

end Mettapedia.Computability.PNP
