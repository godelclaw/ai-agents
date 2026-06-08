import Mettapedia.Computability.PNP.ABDecisionListRoute
import Mettapedia.Computability.PNP.SharedExactABFeatureFamilies

/-!
# P vs NP grassroots: quotient routes for shared raw `(a, b)` feature families

This file connects the reduced raw visible surface `(a, b)` to the shared-basis
exact-surface families.

If a switched family factors through the reduced surface and the reduced family
is realized using one shared affine basis on the raw `(a, b)` bits, then the
exact-surface family inherits the corresponding combiner-only budget.
-/

namespace Mettapedia.Computability.PNP

section

variable {Z : Type*} {r k : ℕ}

/-- Shared affine-feature predictor on the reduced raw surface `(a, b)`. -/
noncomputable def sharedABAffineFeaturePredict
    (features : Fin r → AffineColumnCode (k + k))
    (table : BitCode (2 ^ r))
    (x : ABVisibleSurface k) : Bool :=
  table ((Fintype.equivFinOfCardEq (by simp [BitVec] : Fintype.card (BitVec r) = 2 ^ r))
    (affineFeatureVector features (abVisibleBits (k := k) x)))

/-- Shared sparse-threshold predictor on the reduced raw surface `(a, b)`. -/
noncomputable def sharedABSparseThresholdAffinePredict
    (features : Fin r → AffineColumnCode (k + k))
    (code : SharedSparseThresholdCode r)
    (x : ABVisibleSurface k) : Bool :=
  decide (thresholdCodeValue (r := r) code.2 ≤
    maskedAffineFeatureCount (k := k + k) features code.1 (abVisibleBits (k := k) x))

/-- Shared decision-list predictor on the reduced raw surface `(a, b)`. -/
noncomputable def sharedABAffineDecisionListPredict
    (features : Fin r → AffineColumnCode (k + k))
    (code : SharedAffineDecisionListCode r)
    (x : ABVisibleSurface k) : Bool :=
  match firstActiveFeature? (affineFeatureVector features (abVisibleBits (k := k) x)) with
  | some j => code.1 j
  | none => code.2

theorem sharedExactABAffineFeaturePredict_eq_sharedABAffineFeaturePredict_comp_abVisibleData
    (features : Fin r → AffineColumnCode (k + k))
    (table : BitCode (2 ^ r)) :
    sharedExactABAffineFeaturePredict (Z := Z) (k := k) features table =
      fun u => sharedABAffineFeaturePredict (k := k) features table (abVisibleData u) := by
  funext u
  cases u
  rfl

theorem sharedExactABSparseThresholdAffinePredict_eq_sharedABSparseThresholdAffinePredict_comp_abVisibleData
    (features : Fin r → AffineColumnCode (k + k))
    (code : SharedSparseThresholdCode r) :
    sharedExactABSparseThresholdAffinePredict (Z := Z) (k := k) features code =
      fun u => sharedABSparseThresholdAffinePredict (k := k) features code (abVisibleData u) := by
  funext u
  cases u
  rfl

theorem sharedExactABAffineDecisionListPredict_eq_sharedABAffineDecisionListPredict_comp_abVisibleData
    (features : Fin r → AffineColumnCode (k + k))
    (code : SharedAffineDecisionListCode r) :
    sharedExactABAffineDecisionListPredict (Z := Z) (k := k) features code =
      fun u => sharedABAffineDecisionListPredict (k := k) features code (abVisibleData u) := by
  funext u
  cases u
  rfl

/-- Reduced-surface family using one shared raw `(a, b)` affine basis and an
arbitrary truth-table combiner. -/
def RealizedBySharedABAffineFeatureFamily
    {Index : Type*} (features : Fin r → AffineColumnCode (k + k))
    (H : ABVisibleSwitchedFamily k Index) : Prop :=
  ∀ i, ∃ table : BitCode (2 ^ r),
    H.predict i = sharedABAffineFeaturePredict (k := k) features table

/-- Reduced-surface family using one shared raw `(a, b)` affine basis and a
sparse-threshold combiner. -/
def RealizedBySharedABSparseThresholdAffineFamily
    {Index : Type*} (features : Fin r → AffineColumnCode (k + k))
    (H : ABVisibleSwitchedFamily k Index) : Prop :=
  ∀ i, ∃ code : SharedSparseThresholdCode r,
    H.predict i = sharedABSparseThresholdAffinePredict (k := k) features code

/-- Reduced-surface family using one shared raw `(a, b)` affine basis and a
fixed-order decision-list combiner. -/
def RealizedBySharedABAffineDecisionListFamily
    {Index : Type*} (features : Fin r → AffineColumnCode (k + k))
    (H : ABVisibleSwitchedFamily k Index) : Prop :=
  ∀ i, ∃ code : SharedAffineDecisionListCode r,
    H.predict i = sharedABAffineDecisionListPredict (k := k) features code

/-- Shared truth-table family directly on the reduced raw `(a, b)` surface. -/
noncomputable def sharedABAffineFeatureBitFamily
    (features : Fin r → AffineColumnCode (k + k)) :
    BitEncodedClassifierFamily (ABVisibleSurface k) (2 ^ r) where
  decode table := sharedABAffineFeaturePredict (k := k) features table

/-- Shared sparse-threshold family directly on the reduced raw `(a, b)` surface. -/
noncomputable def sharedABSparseThresholdAffineBitFamily
    (features : Fin r → AffineColumnCode (k + k)) :
    BitEncodedClassifierFamily (ABVisibleSurface k) (2 * r) where
  decode raw x :=
    let code := (sharedSparseThresholdCodeEquivBitCode r).symm raw
    sharedABSparseThresholdAffinePredict (k := k) features code x

/-- Shared decision-list family directly on the reduced raw `(a, b)` surface. -/
noncomputable def sharedABAffineDecisionListBitFamily
    (features : Fin r → AffineColumnCode (k + k)) :
    BitEncodedClassifierFamily (ABVisibleSurface k) (r + 1) where
  decode raw x :=
    let code := (sharedAffineDecisionListCodeEquivBitCode r).symm raw
    sharedABAffineDecisionListPredict (k := k) features code x

@[simp] theorem sharedABAffineFeatureBitFamily_decode
    (features : Fin r → AffineColumnCode (k + k)) (table : BitCode (2 ^ r)) :
    (sharedABAffineFeatureBitFamily (r := r) (k := k) features).decode table =
      sharedABAffineFeaturePredict (k := k) features table := rfl

@[simp] theorem sharedABSparseThresholdAffineBitFamily_decode_code
    (features : Fin r → AffineColumnCode (k + k)) (code : SharedSparseThresholdCode r) :
    (sharedABSparseThresholdAffineBitFamily (r := r) (k := k) features).decode
        (sharedSparseThresholdCodeEquivBitCode r code) =
      sharedABSparseThresholdAffinePredict (k := k) features code := by
  funext x
  simp [sharedABSparseThresholdAffineBitFamily, sharedSparseThresholdCodeEquivBitCode]

@[simp] theorem sharedABAffineDecisionListBitFamily_decode_code
    (features : Fin r → AffineColumnCode (k + k)) (code : SharedAffineDecisionListCode r) :
    (sharedABAffineDecisionListBitFamily (r := r) (k := k) features).decode
        (sharedAffineDecisionListCodeEquivBitCode r code) =
      sharedABAffineDecisionListPredict (k := k) features code := by
  funext x
  simp [sharedABAffineDecisionListBitFamily, sharedAffineDecisionListCodeEquivBitCode]

theorem abVisibleHasBitBudget_of_realizedBySharedABAffineFeatureFamily
    {Index : Type*}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hreal : RealizedBySharedABAffineFeatureFamily (r := r) (k := k) features H) :
    H.HasBitBudget (2 ^ r) := by
  refine ⟨sharedABAffineFeatureBitFamily (r := r) (k := k) features, ?_⟩
  intro i
  rcases hreal i with ⟨table, hi⟩
  refine ⟨table, ?_⟩
  exact (sharedABAffineFeatureBitFamily_decode (r := r) (k := k) features table).trans hi.symm

theorem abVisibleHasBitBudget_of_realizedBySharedABSparseThresholdAffineFamily
    {Index : Type*}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hreal : RealizedBySharedABSparseThresholdAffineFamily (r := r) (k := k) features H) :
    H.HasBitBudget (2 * r) := by
  refine ⟨sharedABSparseThresholdAffineBitFamily (r := r) (k := k) features, ?_⟩
  intro i
  rcases hreal i with ⟨code, hi⟩
  refine ⟨sharedSparseThresholdCodeEquivBitCode r code, ?_⟩
  exact
    (sharedABSparseThresholdAffineBitFamily_decode_code
      (r := r) (k := k) features code).trans hi.symm

theorem abVisibleHasBitBudget_of_realizedBySharedABAffineDecisionListFamily
    {Index : Type*}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hreal : RealizedBySharedABAffineDecisionListFamily (r := r) (k := k) features H) :
    H.HasBitBudget (r + 1) := by
  refine ⟨sharedABAffineDecisionListBitFamily (r := r) (k := k) features, ?_⟩
  intro i
  rcases hreal i with ⟨code, hi⟩
  refine ⟨sharedAffineDecisionListCodeEquivBitCode r code, ?_⟩
  exact
    (sharedABAffineDecisionListBitFamily_decode_code
      (r := r) (k := k) features code).trans hi.symm

theorem abVisible_surfaceCard_le_of_surjective_predict_of_realizedBySharedABAffineFeatureFamily
    {Index : Type*}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hsurj : Function.Surjective H.predict)
    (hreal : RealizedBySharedABAffineFeatureFamily (r := r) (k := k) features H) :
    Fintype.card (ABVisibleSurface k) ≤ 2 ^ r := by
  exact
    IndexedPredictorFamily.bitBudget_lowerBound_of_surjective_predict_fintype
      (G := H) (s := 2 ^ r) hsurj
      (abVisibleHasBitBudget_of_realizedBySharedABAffineFeatureFamily
        (r := r) (k := k) hreal)

theorem abVisible_surfaceCard_le_of_surjective_predict_of_realizedBySharedABSparseThresholdAffineFamily
    {Index : Type*}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hsurj : Function.Surjective H.predict)
    (hreal : RealizedBySharedABSparseThresholdAffineFamily (r := r) (k := k) features H) :
    Fintype.card (ABVisibleSurface k) ≤ 2 * r := by
  exact
    IndexedPredictorFamily.bitBudget_lowerBound_of_surjective_predict_fintype
      (G := H) (s := 2 * r) hsurj
      (abVisibleHasBitBudget_of_realizedBySharedABSparseThresholdAffineFamily
        (r := r) (k := k) hreal)

theorem abVisible_surfaceCard_le_of_surjective_predict_of_realizedBySharedABAffineDecisionListFamily
    {Index : Type*}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hsurj : Function.Surjective H.predict)
    (hreal : RealizedBySharedABAffineDecisionListFamily (r := r) (k := k) features H) :
    Fintype.card (ABVisibleSurface k) ≤ r + 1 := by
  exact
    IndexedPredictorFamily.bitBudget_lowerBound_of_surjective_predict_fintype
      (G := H) (s := r + 1) hsurj
      (abVisibleHasBitBudget_of_realizedBySharedABAffineDecisionListFamily
        (r := r) (k := k) hreal)

theorem not_realizedBySharedABAffineFeatureFamily_of_surjective_predict_of_lt_surfaceCard
    {Index : Type*}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hs : 2 ^ r < Fintype.card (ABVisibleSurface k))
    (hsurj : Function.Surjective H.predict) :
    ¬ RealizedBySharedABAffineFeatureFamily (r := r) (k := k) features H := by
  intro hreal
  exact Nat.not_le_of_lt hs <|
    abVisible_surfaceCard_le_of_surjective_predict_of_realizedBySharedABAffineFeatureFamily
      (r := r) (k := k) hsurj hreal

theorem not_realizedBySharedABSparseThresholdAffineFamily_of_surjective_predict_of_lt_surfaceCard
    {Index : Type*}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hs : 2 * r < Fintype.card (ABVisibleSurface k))
    (hsurj : Function.Surjective H.predict) :
    ¬ RealizedBySharedABSparseThresholdAffineFamily (r := r) (k := k) features H := by
  intro hreal
  exact Nat.not_le_of_lt hs <|
    abVisible_surfaceCard_le_of_surjective_predict_of_realizedBySharedABSparseThresholdAffineFamily
      (r := r) (k := k) hsurj hreal

theorem not_realizedBySharedABAffineDecisionListFamily_of_surjective_predict_of_lt_surfaceCard
    {Index : Type*}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hs : r + 1 < Fintype.card (ABVisibleSurface k))
    (hsurj : Function.Surjective H.predict) :
    ¬ RealizedBySharedABAffineDecisionListFamily (r := r) (k := k) features H := by
  intro hreal
  exact Nat.not_le_of_lt hs <|
    abVisible_surfaceCard_le_of_surjective_predict_of_realizedBySharedABAffineDecisionListFamily
      (r := r) (k := k) hsurj hreal

theorem realizedBySharedExactABAffineFeatureFamily_of_factorsThrough_ab
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hfactor : G.FactorsThrough abVisibleData H)
    (hreal : RealizedBySharedABAffineFeatureFamily (r := r) (k := k) features H) :
    RealizedBySharedExactABAffineFeatureFamily (Z := Z) (r := r) (k := k) features G := by
  intro i
  rcases hreal i with ⟨table, hi⟩
  refine ⟨table, ?_⟩
  funext u
  calc
    G.predict i u = H.predict i (abVisibleData u) := hfactor i u
    _ = sharedABAffineFeaturePredict (k := k) features table (abVisibleData u) := by
          exact congrFun hi (abVisibleData u)
    _ = sharedExactABAffineFeaturePredict (Z := Z) (k := k) features table u := by
          symm
          exact congrFun
            (sharedExactABAffineFeaturePredict_eq_sharedABAffineFeaturePredict_comp_abVisibleData
              (Z := Z) (r := r) (k := k) features table) u

theorem realizedBySharedExactABSparseThresholdAffineFamily_of_factorsThrough_ab
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hfactor : G.FactorsThrough abVisibleData H)
    (hreal : RealizedBySharedABSparseThresholdAffineFamily (r := r) (k := k) features H) :
    RealizedBySharedExactABSparseThresholdAffineFamily (Z := Z) (r := r) (k := k) features G := by
  intro i
  rcases hreal i with ⟨code, hi⟩
  refine ⟨code, ?_⟩
  funext u
  calc
    G.predict i u = H.predict i (abVisibleData u) := hfactor i u
    _ = sharedABSparseThresholdAffinePredict (k := k) features code (abVisibleData u) := by
          exact congrFun hi (abVisibleData u)
    _ = sharedExactABSparseThresholdAffinePredict (Z := Z) (k := k) features code u := by
          symm
          exact congrFun
            (sharedExactABSparseThresholdAffinePredict_eq_sharedABSparseThresholdAffinePredict_comp_abVisibleData
              (Z := Z) (r := r) (k := k) features code) u

theorem realizedBySharedExactABAffineDecisionListFamily_of_factorsThrough_ab
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hfactor : G.FactorsThrough abVisibleData H)
    (hreal : RealizedBySharedABAffineDecisionListFamily (r := r) (k := k) features H) :
    RealizedBySharedExactABAffineDecisionListFamily (Z := Z) (r := r) (k := k) features G := by
  intro i
  rcases hreal i with ⟨code, hi⟩
  refine ⟨code, ?_⟩
  funext u
  calc
    G.predict i u = H.predict i (abVisibleData u) := hfactor i u
    _ = sharedABAffineDecisionListPredict (k := k) features code (abVisibleData u) := by
          exact congrFun hi (abVisibleData u)
    _ = sharedExactABAffineDecisionListPredict (Z := Z) (k := k) features code u := by
          symm
          exact congrFun
            (sharedExactABAffineDecisionListPredict_eq_sharedABAffineDecisionListPredict_comp_abVisibleData
              (Z := Z) (r := r) (k := k) features code) u

theorem exactVisibleCompressionTarget_of_factorsThrough_ab_and_sharedAffineFeature
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hfactor : G.FactorsThrough abVisibleData H)
    (hreal : RealizedBySharedABAffineFeatureFamily (r := r) (k := k) features H) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (2 ^ r) := by
  exact exactVisibleCompressionTarget_of_realizedBySharedExactABAffineFeatureFamily
    (Z := Z) (r := r) (k := k) features
    (realizedBySharedExactABAffineFeatureFamily_of_factorsThrough_ab
      (Z := Z) (r := r) (k := k) hfactor hreal)

theorem exactVisibleCompressionTarget_of_factorsThrough_ab_and_sharedSparseThreshold
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hfactor : G.FactorsThrough abVisibleData H)
    (hreal : RealizedBySharedABSparseThresholdAffineFamily (r := r) (k := k) features H) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (2 * r) := by
  exact exactVisibleCompressionTarget_of_realizedBySharedExactABSparseThresholdAffineFamily
    (Z := Z) (r := r) (k := k) features
    (realizedBySharedExactABSparseThresholdAffineFamily_of_factorsThrough_ab
      (Z := Z) (r := r) (k := k) hfactor hreal)

theorem exactVisibleCompressionTarget_of_factorsThrough_ab_and_sharedDecisionList
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hfactor : G.FactorsThrough abVisibleData H)
    (hreal : RealizedBySharedABAffineDecisionListFamily (r := r) (k := k) features H) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (r + 1) := by
  exact exactVisibleCompressionTarget_of_realizedBySharedExactABAffineDecisionListFamily
    (Z := Z) (r := r) (k := k) features
    (realizedBySharedExactABAffineDecisionListFamily_of_factorsThrough_ab
      (Z := Z) (r := r) (k := k) hfactor hreal)

section Lift

variable [Inhabited Z]

theorem exactVisibleCompressionTarget_of_invariant_and_sharedAffineFeature
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hinv : ABVisibleInvariant (Z := Z) (k := k) G)
    (hreal :
      RealizedBySharedABAffineFeatureFamily (r := r) (k := k) features
        (liftToABVisibleFamily (Z := Z) (k := k) G)) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (2 ^ r) := by
  exact exactVisibleCompressionTarget_of_factorsThrough_ab_and_sharedAffineFeature
    (Z := Z) (r := r) (k := k)
    (factorsThrough_abVisibleData_of_invariant (Z := Z) (k := k) hinv)
    hreal

theorem exactVisibleCompressionTarget_of_invariant_and_sharedSparseThreshold
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hinv : ABVisibleInvariant (Z := Z) (k := k) G)
    (hreal :
      RealizedBySharedABSparseThresholdAffineFamily (r := r) (k := k) features
        (liftToABVisibleFamily (Z := Z) (k := k) G)) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (2 * r) := by
  exact exactVisibleCompressionTarget_of_factorsThrough_ab_and_sharedSparseThreshold
    (Z := Z) (r := r) (k := k)
    (factorsThrough_abVisibleData_of_invariant (Z := Z) (k := k) hinv)
    hreal

theorem exactVisibleCompressionTarget_of_invariant_and_sharedDecisionList
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hinv : ABVisibleInvariant (Z := Z) (k := k) G)
    (hreal :
      RealizedBySharedABAffineDecisionListFamily (r := r) (k := k) features
        (liftToABVisibleFamily (Z := Z) (k := k) G)) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (r + 1) := by
  exact exactVisibleCompressionTarget_of_factorsThrough_ab_and_sharedDecisionList
    (Z := Z) (r := r) (k := k)
    (factorsThrough_abVisibleData_of_invariant (Z := Z) (k := k) hinv)
    hreal

end Lift

end

end Mettapedia.Computability.PNP
