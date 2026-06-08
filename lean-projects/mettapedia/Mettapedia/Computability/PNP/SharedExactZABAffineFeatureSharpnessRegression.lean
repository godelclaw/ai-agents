import Mettapedia.Computability.PNP.SharedExactZABAffineFeatureSharpness

namespace Mettapedia.Computability.PNP

theorem fullExactVisibleRuleFamily_realizedBySharedExactZABAffineFeatureFamily_id_canonical_regression :
    RealizedBySharedExactZABAffineFeatureFamily
      (Z := BitVec 1) (p := 1 + (1 + 1)) (r := 1) (k := 1)
      (fun z => z)
      (canonicalAffineBasis (1 + (1 + 1)))
      (fullExactVisibleRuleFamily (BitVec 1) 1) := by
  exact fullExactVisibleRuleFamily_realizedBySharedExactZABAffineFeatureFamily_id_canonical

theorem bitVecZABVisibleData_injective_regression :
    Function.Injective (bitVecZABVisibleData (r := 1) (k := 1)) := by
  exact bitVecZABVisibleData_injective

end Mettapedia.Computability.PNP
