import Mettapedia.Computability.PNP.BitVecZABVisibleSurface
import Mettapedia.Computability.PNP.CanonicalABTargetRoute
import Mettapedia.Computability.PNP.SharedExactZABAffineFeatureCharacterization

/-!
# P vs NP route sharpness: the shared exact affine-feature lower bound is tight

The previous obstruction packets show that the shared exact affine-feature class
cannot realize the full exact-visible Boolean rule family below `p < n + 2k`
when `Z = BitVec n`.

This file proves the converse sharpness statement.  If the latent visible datum
is already bit-valued, the identity extractor together with the canonical
coordinate affine basis on the full visible bit vector `(z, a, b)` makes the
shared summary map literally equal to that raw bitvector view.  Hence the
summary is injective, and the arbitrary truth-table combiner realizes the full
exact-visible Boolean rule family.

So the affine-feature lower bound is exact: this branch stays fully alive at the
threshold `p = n + 2k`.
-/

namespace Mettapedia.Computability.PNP

section

variable {n k : ℕ}

theorem bitVecZABVisibleData_injective :
    Function.Injective (bitVecZABVisibleData (r := n) (k := k)) := by
  intro u v huv
  cases u with
  | mk uz ua ub =>
      cases v with
      | mk vz va vb =>
          have hz : uz = vz := by
            funext i
            have h := congrFun huv (Fin.castAdd (k + k) i)
            simpa [bitVecZABVisibleData_eq, Fin.append_left] using h
          have hab : Fin.append ua ub = Fin.append va vb := by
            funext j
            have h := congrFun huv (Fin.natAdd n j)
            simpa [bitVecZABVisibleData_eq, Fin.append_right] using h
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

@[simp] theorem exactZABAffineFeatureSummary_id_canonical
    (u : ExactVisiblePostSwitchSurface (BitVec n) k) :
    exactZABAffineFeatureSummary
        (Z := BitVec n) (p := n + (k + k)) (r := n) (k := k)
        (fun z => z) (canonicalAffineBasis (n + (k + k))) u =
      bitVecZABVisibleData (r := n) (k := k) u := by
  simp [exactZABAffineFeatureSummary, bitVecZABVisibleData, affineFeatureVector_canonicalAffineBasis]

theorem fullExactVisibleRuleFamily_realizedBySharedExactZABAffineFeatureFamily_id_canonical
    :
    RealizedBySharedExactZABAffineFeatureFamily
      (Z := BitVec n) (p := n + (k + k)) (r := n) (k := k)
      (fun z => z)
      (canonicalAffineBasis (n + (k + k)))
      (fullExactVisibleRuleFamily (BitVec n) k) := by
  refine
    fullExactVisibleRuleFamily_realizedBySharedExactZABAffineFeatureFamily_of_injective_summary
      (Z := BitVec n) (p := n + (k + k)) (r := n) (k := k)
      (fun z => z) (canonicalAffineBasis (n + (k + k))) ?_
  intro u v huv
  exact bitVecZABVisibleData_injective <| by
    simpa using huv

end

end Mettapedia.Computability.PNP
