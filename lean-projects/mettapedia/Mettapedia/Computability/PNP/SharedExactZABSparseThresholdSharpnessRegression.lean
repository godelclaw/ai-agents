import Mettapedia.Computability.PNP.SharedExactZABSparseThresholdSharpness

namespace Mettapedia.Computability.PNP

theorem fullExactVisibleRuleFamily_realizedBySharedExactZABSparseThresholdAffineFamily_id_allAffinePointBlockFeatures_regression :
    RealizedBySharedExactZABSparseThresholdAffineFamily
      (Z := BitVec 1)
      (p := allAffinePointBlockFeatureCount (1 + (0 + 0)))
      (r := 1) (k := 0)
      (fun z => z)
      (allAffinePointBlockFeatures (1 + (0 + 0)))
      (fullExactVisibleRuleFamily (BitVec 1) 0) := by
  exact
    fullExactVisibleRuleFamily_realizedBySharedExactZABSparseThresholdAffineFamily_id_allAffinePointBlockFeatures
      (n := 1) (k := 0) (by decide)

end Mettapedia.Computability.PNP
