import Mettapedia.Computability.PNP.ExactZABExtractorCollisionObstruction

/-!
# Regression checks for exact ZAB extractor-collision obstructions

These wrappers keep the noninjective-extractor route blocker small and
reusable on the exact `(zfeat(z), a, b)` decision-list surface.
-/

namespace Mettapedia.Computability.PNP.ExactZABExtractorCollisionObstructionRegression

open Mettapedia.Computability.PNP
open scoped ENNReal

abbrev zeroExtractor : Bool → BitVec 0 := fun _ => default

theorem zeroExtractor_not_injective :
    ¬ Function.Injective zeroExtractor := by
  intro hinj
  have hsame : zeroExtractor false = zeroExtractor true := rfl
  exact Bool.false_ne_true (hinj hsame)

example {Index : Type}
    {G : ExactVisibleSwitchedFamily Bool 0 Index}
    (hreal :
      RealizedByRawExactZABDecisionListFamily
        (Z := Bool) (r := 0) (k := 0) zeroExtractor G) :
    ¬ Function.Surjective G.predict :=
  not_surjective_predict_of_not_injective_of_realizedByRawExactZABDecisionListFamily
    (Z := Bool) (r := 0) (k := 0) hreal zeroExtractor_not_injective

example {Index : Type}
    {G : ExactVisibleSwitchedFamily Bool 0 Index}
    (h :
      ExactZABDecisionListTargetData
        (Z := Bool) (r := 0) (k := 0) (Index := Index) zeroExtractor G) :
    ¬ Function.Surjective G.predict :=
  h.not_surjective_predict_of_not_injective_zfeat zeroExtractor_not_injective

example {Index : Type}
    {μ : PMF (ExactVisiblePostSwitchSurface Bool 0)}
    {G : ExactVisibleSwitchedFamily Bool 0 Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABDecisionListRecoveryData
        (Z := Bool) (r := 0) (k := 0) (Index := Index) μ zeroExtractor G q) :
    ¬ Function.Surjective G.predict :=
  h.not_surjective_predict_of_not_injective_zfeat zeroExtractor_not_injective

example {Index : Type}
    {G : ExactVisibleSwitchedFamily (Fin 2) 0 Index}
    (h :
      ExactZABDecisionListTargetData
        (Z := Fin 2) (r := 0) (k := 0) (Index := Index) (fun _ => (default : BitVec 0)) G) :
    ¬ Function.Surjective G.predict :=
  h.not_surjective_predict_of_card_gt_bitVec (by decide)

example {Index : Type}
    {G : ExactVisibleSwitchedFamily Bool 0 Index}
    (h :
      CanonicalZABDecisionListCandidateData
        (Z := Bool) (r := 0) (k := 0) (Index := Index) zeroExtractor G) :
    ¬ Function.Surjective G.predict :=
  h.not_surjective_predict_of_not_injective_zfeat zeroExtractor_not_injective

example {Index : Type}
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Bool 0) Bool) :
    ¬ Function.Surjective
        (exactZABDecisionListERMFamily
          (Z := Bool) (r := 0) (k := 0) zeroExtractor samples).predict :=
  exactZABDecisionListERMFamily_not_surjective_of_not_injective_zfeat
    (Z := Bool) (r := 0) (k := 0) (Index := Index) zeroExtractor samples
    zeroExtractor_not_injective

end Mettapedia.Computability.PNP.ExactZABExtractorCollisionObstructionRegression
