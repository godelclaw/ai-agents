import Mettapedia.Computability.PNP.SharedExactZABAffineDecisionListFiberObstruction

namespace Mettapedia.Computability.PNP

example (features : Fin 3 → AffineColumnCode (2 + (1 + 1))) :
    ¬ Function.Injective
      (exactZABAffineDecisionListSignature
        (Z := Unit) (p := 3) (r := 2) (k := 1)
        (fun _ => (zeroVec : BitVec 2)) features) := by
  exact
    not_injective_exactZABAffineDecisionListSignature_of_pos
      (Z := Unit) (p := 3) (r := 2) (k := 1)
      (fun _ => (zeroVec : BitVec 2)) features (by decide)

example (features : Fin 2 → AffineColumnCode (1 + (1 + 1))) :
    ¬ RealizedBySharedExactZABAffineDecisionListFamily
        (Z := Unit) (p := 2) (r := 1) (k := 1)
        (fun _ => (zeroVec : BitVec 1)) features
        (fullExactVisibleRuleFamily Unit 1) := by
  exact
    fullExactVisibleRuleFamily_not_realizedBySharedExactZABAffineDecisionListFamily_of_pos
      (Z := Unit) (p := 2) (r := 1) (k := 1)
      (fun _ => (zeroVec : BitVec 1)) features (by decide)

end Mettapedia.Computability.PNP
