import Mettapedia.Computability.PNP.SharedExactZABSparseThresholdInjectiveLiveness

namespace Mettapedia.Computability.PNP

def boolToBitVec1 : Bool → BitVec 1 := fun b _ => b

theorem boolToBitVec1_injective : Function.Injective boolToBitVec1 := by
  intro a b hab
  have h := congrFun hab 0
  simpa using h

theorem fullExactVisibleRuleFamily_realizedBySharedExactZABSparseThresholdAffineFamily_bool0_regression :
    RealizedBySharedExactZABSparseThresholdAffineFamily
      (Z := Bool)
      (p := allAffinePointBlockFeatureCount (1 + (0 + 0)))
      (r := 1) (k := 0)
      boolToBitVec1
      (allAffinePointBlockFeatures (1 + (0 + 0)))
      (fullExactVisibleRuleFamily Bool 0) := by
  exact
    fullExactVisibleRuleFamily_realizedBySharedExactZABSparseThresholdAffineFamily_of_injective_zfeat
      (Z := Bool) (r := 1) (k := 0)
      boolToBitVec1 boolToBitVec1_injective (by decide)

end Mettapedia.Computability.PNP
