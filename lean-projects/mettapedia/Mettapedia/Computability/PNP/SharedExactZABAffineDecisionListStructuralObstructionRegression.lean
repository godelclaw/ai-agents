import Mettapedia.Computability.PNP.SharedExactZABAffineDecisionListStructuralObstruction

namespace Mettapedia.Computability.PNP

theorem not_injective_firstActiveFeature_affineFeatureVector_of_one_lt_p0_regression :
    ¬ Function.Injective
      (fun x : BitVec 2 =>
        firstActiveFeature? (affineFeatureVector (fun i : Fin 0 => nomatch i) x)) := by
  exact
    not_injective_firstActiveFeature_affineFeatureVector_of_one_lt
      (features := fun i : Fin 0 => nomatch i)
      (by decide : 1 < 2)

theorem not_injective_exactZABAffineDecisionListSignature_id_of_one_lt_canonical_regression :
    ¬ Function.Injective
      (exactZABAffineDecisionListSignature
        (Z := BitVec 0) (p := 2) (r := 0) (k := 1)
        (fun z => z) (canonicalAffineBasis 2)) := by
  exact
    not_injective_exactZABAffineDecisionListSignature_id_of_one_lt
      (n := 0) (p := 2) (k := 1)
      (canonicalAffineBasis 2)
      (by decide : 1 < 0 + (1 + 1))

theorem fullExactVisibleRuleFamily_not_realizedBySharedExactZABAffineDecisionListFamily_id_of_one_lt_canonical_regression :
    ¬ RealizedBySharedExactZABAffineDecisionListFamily
        (Z := BitVec 0) (p := 2) (r := 0) (k := 1)
        (fun z => z) (canonicalAffineBasis 2)
        (fullExactVisibleRuleFamily (BitVec 0) 1) := by
  exact
    fullExactVisibleRuleFamily_not_realizedBySharedExactZABAffineDecisionListFamily_id_of_one_lt
      (n := 0) (p := 2) (k := 1)
      (canonicalAffineBasis 2)
      (by decide : 1 < 0 + (1 + 1))

end Mettapedia.Computability.PNP
