import Mettapedia.Computability.PNP.ABDecisionListRoute
import Mettapedia.Computability.PNP.ExactVisibleImageBudget

/-!
# P vs NP crux: raw `(a, b)` factorization alone does not rescue compression

The exact visible post-switch obstruction can still look too generous: perhaps
the actual switched predictor ignores the latent local datum `z` and depends
only on the reduced raw visible surface `(a, b)`.

This file records the corresponding reduced-surface barrier.  If an exact
switched family factors through `abVisibleData`, then any exact or clocked
realization budget for the exact family already induces the same budget for the
reduced `(a, b)` family.  So if that reduced family is still fully expressive
on `ABVisibleSurface k`, the truth-table threshold `2^(2k)` is unavoidable.
-/

namespace Mettapedia.Computability.PNP

section

variable {Z : Type*} {k s : ℕ} {Index : Type*}

theorem abVisibleHasBitBudget_of_exactVisibleCompressionTarget_of_factorsThrough
    [Inhabited Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    (hfactor : G.FactorsThrough abVisibleData H)
    (hsmall : ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s) :
    H.HasBitBudget s := by
  exact IndexedPredictorFamily.hasBitBudget_of_factorsThrough_of_rightInverse
    (G := G) (H := H) (view := abVisibleData)
    (sec := abVisibleSection (Z := Z) (k := k))
    hfactor
    (by
      intro x
      exact abVisibleData_section (Z := Z) (k := k) x)
    hsmall

theorem abVisible_surfaceCard_le_of_exactVisibleCompressionTarget_of_factorsThrough
    [Inhabited Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    (hfactor : G.FactorsThrough abVisibleData H)
    (hsurj : Function.Surjective H.predict)
    (hsmall : ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s) :
    Fintype.card (ABVisibleSurface k) ≤ s := by
  exact
    IndexedPredictorFamily.bitBudget_lowerBound_of_surjective_predict_fintype
      (G := H) (s := s) hsurj
      (abVisibleHasBitBudget_of_exactVisibleCompressionTarget_of_factorsThrough
        (Z := Z) (k := k) (s := s) hfactor hsmall)

theorem not_exactVisibleCompressionTarget_of_factorsThrough_ab_and_surjective_predict
    [Inhabited Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    (hs : s < Fintype.card (ABVisibleSurface k))
    (hfactor : G.FactorsThrough abVisibleData H)
    (hsurj : Function.Surjective H.predict) :
    ¬ ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s := by
  intro hsmall
  exact Nat.not_le_of_lt hs <|
    abVisible_surfaceCard_le_of_exactVisibleCompressionTarget_of_factorsThrough
      (Z := Z) (k := k) (s := s) hfactor hsurj hsmall

theorem not_exactVisibleCompressionTarget_of_factorsThrough_ab_and_surjective_predict_of_lt_cardFormula
    [Inhabited Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    (hs : s < 2 ^ (2 * k))
    (hfactor : G.FactorsThrough abVisibleData H)
    (hsurj : Function.Surjective H.predict) :
    ¬ ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s := by
  exact
    not_exactVisibleCompressionTarget_of_factorsThrough_ab_and_surjective_predict
      (Z := Z) (k := k) (s := s) (Index := Index)
      (by simpa [card_abVisibleSurface (k := k)] using hs)
      hfactor hsurj

/-- Finite-image form of the reduced `(a,b)` obstruction: if the exact family
factors through `(a,b)` and the reduced family is still fully expressive, any
finite predictor-image cover of the exact family must contain at least the full
Boolean classifier space on `(a,b)`. -/
theorem abVisible_finitePredictorCover_card_le_of_factorsThrough
    [Inhabited Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index} {N : ℕ}
    (hfactor : G.FactorsThrough abVisibleData H)
    (hsurj : Function.Surjective H.predict)
    (hcover : G.FinitePredictorCover N) :
    2 ^ Fintype.card (ABVisibleSurface k) ≤ N := by
  exact
    IndexedPredictorFamily.finitePredictorCover_card_le_of_factorsThrough_of_rightInverse_of_surjective_predict
      (G := G) (H := H) (view := abVisibleData)
      (sec := abVisibleSection (Z := Z) (k := k))
      hfactor
      (by
        intro x
        exact abVisibleData_section (Z := Z) (k := k) x)
      hsurj hcover

/-- Below the full reduced Boolean classifier-space cardinality, a factored
exact family whose reduced family is fully expressive has no finite
predictor-image cover. -/
theorem not_finitePredictorCover_of_factorsThrough_ab_and_surjective_predict
    [Inhabited Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index} {N : ℕ}
    (hN : N < 2 ^ Fintype.card (ABVisibleSurface k))
    (hfactor : G.FactorsThrough abVisibleData H)
    (hsurj : Function.Surjective H.predict) :
    ¬ G.FinitePredictorCover N := by
  intro hcover
  exact Nat.not_le_of_lt hN <|
    abVisible_finitePredictorCover_card_le_of_factorsThrough
      (Z := Z) (k := k) (Index := Index) hfactor hsurj hcover

/-- Formula form of the finite-image reduced `(a,b)` obstruction. -/
theorem not_finitePredictorCover_of_factorsThrough_ab_and_surjective_predict_of_lt_cardFormula
    [Inhabited Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index} {N : ℕ}
    (hN : N < 2 ^ (2 ^ (2 * k)))
    (hfactor : G.FactorsThrough abVisibleData H)
    (hsurj : Function.Surjective H.predict) :
    ¬ G.FinitePredictorCover N := by
  exact
    not_finitePredictorCover_of_factorsThrough_ab_and_surjective_predict
      (Z := Z) (k := k) (Index := Index)
      (by simpa [card_abVisibleSurface (k := k)] using hN)
      hfactor hsurj

/-- Partial-image form of the reduced `(a,b)` obstruction: full expressivity is
not needed.  Any injectively indexed finite probe family already realized by
the reduced `(a,b)` predictors gives the same lower bound after pullback to the
exact surface. -/
theorem abVisible_finitePredictorCover_card_le_of_factorsThrough_of_injective_realization
    [Inhabited Z] {Probe : Type*} [Fintype Probe]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index} {N : ℕ}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hfactor : G.FactorsThrough abVisibleData H)
    (hcover : G.FinitePredictorCover N) :
    Fintype.card Probe ≤ N :=
  IndexedPredictorFamily.finitePredictorCover_card_le_of_factorsThrough_of_rightInverse_of_injective_realization
    (G := G) (H := H) (view := abVisibleData)
    (sec := abVisibleSection (Z := Z) (k := k))
    target hinj hreal hfactor
    (by
      intro x
      exact abVisibleData_section (Z := Z) (k := k) x)
    hcover

/-- Negative finite-cover form of the partial-image reduced `(a,b)` obstruction. -/
theorem not_finitePredictorCover_of_factorsThrough_ab_and_injective_realization_of_lt_card
    [Inhabited Z] {Probe : Type*} [Fintype Probe]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index} {N : ℕ}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hN : N < Fintype.card Probe)
    (hfactor : G.FactorsThrough abVisibleData H) :
    ¬ G.FinitePredictorCover N :=
  IndexedPredictorFamily.not_finitePredictorCover_of_factorsThrough_of_rightInverse_of_injective_realization_of_lt_card
    (G := G) (H := H) (view := abVisibleData)
    (sec := abVisibleSection (Z := Z) (k := k))
    target hinj hreal hN hfactor
    (by
      intro x
      exact abVisibleData_section (Z := Z) (k := k) x)

/-- Exact visible compression is impossible below any finite probe family
already realized on the reduced `(a,b)` view. -/
theorem not_exactVisibleCompressionTarget_of_factorsThrough_ab_and_injective_realization_of_lt_card
    [Inhabited Z] {Probe : Type*} [Fintype Probe]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hs : 2 ^ s < Fintype.card Probe)
    (hfactor : G.FactorsThrough abVisibleData H) :
    ¬ ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s := by
  rw [exactVisibleCompressionTarget_iff_finitePredictorCover]
  exact
    not_finitePredictorCover_of_factorsThrough_ab_and_injective_realization_of_lt_card
      (Z := Z) (k := k) (Index := Index)
      target hinj hreal hs hfactor

/-- Representative-index form of the reduced `(a,b)` finite-image obstruction. -/
theorem abVisible_finiteIndexRepresentativeCover_card_le_of_factorsThrough
    [Inhabited Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index} {N : ℕ}
    (hfactor : G.FactorsThrough abVisibleData H)
    (hsurj : Function.Surjective H.predict)
    (hrep : G.FiniteIndexRepresentativeCover N) :
    2 ^ Fintype.card (ABVisibleSurface k) ≤ N := by
  exact
    IndexedPredictorFamily.finiteIndexRepresentativeCover_card_le_of_factorsThrough_of_rightInverse_of_surjective_predict
      (G := G) (H := H) (view := abVisibleData)
      (sec := abVisibleSection (Z := Z) (k := k))
      hfactor
      (by
        intro x
        exact abVisibleData_section (Z := Z) (k := k) x)
      hsurj hrep

/-- Below the full reduced Boolean classifier-space cardinality, a factored
exact family whose reduced family is fully expressive has no finite
representative-index cover. -/
theorem not_finiteIndexRepresentativeCover_of_factorsThrough_ab_and_surjective_predict
    [Inhabited Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index} {N : ℕ}
    (hN : N < 2 ^ Fintype.card (ABVisibleSurface k))
    (hfactor : G.FactorsThrough abVisibleData H)
    (hsurj : Function.Surjective H.predict) :
    ¬ G.FiniteIndexRepresentativeCover N := by
  intro hrep
  exact Nat.not_le_of_lt hN <|
    abVisible_finiteIndexRepresentativeCover_card_le_of_factorsThrough
      (Z := Z) (k := k) (Index := Index) hfactor hsurj hrep

/-- Representative-index form of the partial-image reduced `(a,b)` obstruction. -/
theorem abVisible_finiteIndexRepresentativeCover_card_le_of_factorsThrough_of_injective_realization
    [Inhabited Z] {Probe : Type*} [Fintype Probe]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index} {N : ℕ}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hfactor : G.FactorsThrough abVisibleData H)
    (hrep : G.FiniteIndexRepresentativeCover N) :
    Fintype.card Probe ≤ N :=
  IndexedPredictorFamily.finiteIndexRepresentativeCover_card_le_of_factorsThrough_of_rightInverse_of_injective_realization
    (G := G) (H := H) (view := abVisibleData)
    (sec := abVisibleSection (Z := Z) (k := k))
    target hinj hreal hfactor
    (by
      intro x
      exact abVisibleData_section (Z := Z) (k := k) x)
    hrep

/-- Negative representative-index form of the partial-image reduced `(a,b)`
obstruction. -/
theorem not_finiteIndexRepresentativeCover_of_factorsThrough_ab_and_injective_realization_of_lt_card
    [Inhabited Z] {Probe : Type*} [Fintype Probe]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index} {N : ℕ}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hN : N < Fintype.card Probe)
    (hfactor : G.FactorsThrough abVisibleData H) :
    ¬ G.FiniteIndexRepresentativeCover N :=
  IndexedPredictorFamily.not_finiteIndexRepresentativeCover_of_factorsThrough_of_rightInverse_of_injective_realization_of_lt_card
    (G := G) (H := H) (view := abVisibleData)
    (sec := abVisibleSection (Z := Z) (k := k))
    target hinj hreal hN hfactor
    (by
      intro x
      exact abVisibleData_section (Z := Z) (k := k) x)

/-- Quotient-code form of the reduced `(a,b)` finite-image obstruction. -/
theorem abVisible_finitePredictorQuotient_card_le_of_factorsThrough
    [Inhabited Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index} {N : ℕ}
    (hfactor : G.FactorsThrough abVisibleData H)
    (hsurj : Function.Surjective H.predict)
    (hquot : G.FinitePredictorQuotient N) :
    2 ^ Fintype.card (ABVisibleSurface k) ≤ N := by
  exact
    IndexedPredictorFamily.finitePredictorQuotient_card_le_of_factorsThrough_of_rightInverse_of_surjective_predict
      (G := G) (H := H) (view := abVisibleData)
      (sec := abVisibleSection (Z := Z) (k := k))
      hfactor
      (by
        intro x
        exact abVisibleData_section (Z := Z) (k := k) x)
      hsurj hquot

/-- Below the full reduced Boolean classifier-space cardinality, a factored
exact family whose reduced family is fully expressive has no finite
quotient-code presentation. -/
theorem not_finitePredictorQuotient_of_factorsThrough_ab_and_surjective_predict
    [Inhabited Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index} {N : ℕ}
    (hN : N < 2 ^ Fintype.card (ABVisibleSurface k))
    (hfactor : G.FactorsThrough abVisibleData H)
    (hsurj : Function.Surjective H.predict) :
    ¬ G.FinitePredictorQuotient N := by
  intro hquot
  exact Nat.not_le_of_lt hN <|
    abVisible_finitePredictorQuotient_card_le_of_factorsThrough
      (Z := Z) (k := k) (Index := Index) hfactor hsurj hquot

/-- Formula form of the quotient-code reduced `(a,b)` obstruction. -/
theorem not_finitePredictorQuotient_of_factorsThrough_ab_and_surjective_predict_of_lt_cardFormula
    [Inhabited Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index} {N : ℕ}
    (hN : N < 2 ^ (2 ^ (2 * k)))
    (hfactor : G.FactorsThrough abVisibleData H)
    (hsurj : Function.Surjective H.predict) :
    ¬ G.FinitePredictorQuotient N := by
  exact
    not_finitePredictorQuotient_of_factorsThrough_ab_and_surjective_predict
      (Z := Z) (k := k) (Index := Index)
      (by simpa [card_abVisibleSurface (k := k)] using hN)
      hfactor hsurj

/-- Quotient-code form of the partial-image reduced `(a,b)` obstruction. -/
theorem abVisible_finitePredictorQuotient_card_le_of_factorsThrough_of_injective_realization
    [Inhabited Z] {Probe : Type*} [Fintype Probe]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index} {N : ℕ}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hfactor : G.FactorsThrough abVisibleData H)
    (hquot : G.FinitePredictorQuotient N) :
    Fintype.card Probe ≤ N :=
  IndexedPredictorFamily.finitePredictorQuotient_card_le_of_factorsThrough_of_rightInverse_of_injective_realization
    (G := G) (H := H) (view := abVisibleData)
    (sec := abVisibleSection (Z := Z) (k := k))
    target hinj hreal hfactor
    (by
      intro x
      exact abVisibleData_section (Z := Z) (k := k) x)
    hquot

/-- Negative quotient-code form of the partial-image reduced `(a,b)`
obstruction. -/
theorem not_finitePredictorQuotient_of_factorsThrough_ab_and_injective_realization_of_lt_card
    [Inhabited Z] {Probe : Type*} [Fintype Probe]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index} {N : ℕ}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hN : N < Fintype.card Probe)
    (hfactor : G.FactorsThrough abVisibleData H) :
    ¬ G.FinitePredictorQuotient N :=
  IndexedPredictorFamily.not_finitePredictorQuotient_of_factorsThrough_of_rightInverse_of_injective_realization_of_lt_card
    (G := G) (H := H) (view := abVisibleData)
    (sec := abVisibleSection (Z := Z) (k := k))
    target hinj hreal hN hfactor
    (by
      intro x
      exact abVisibleData_section (Z := Z) (k := k) x)

theorem invariantCompressionTarget_abSurfaceCard_le_of_factorsThrough_ab_and_surjective_predict
    [Inhabited Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    (hfactor : G.FactorsThrough abVisibleData H)
    (hsurj : Function.Surjective H.predict)
    (hsmall : InvariantCompressionTarget (Z := Z) (k := k) (Index := Index) G s) :
    Fintype.card (ABVisibleSurface k) ≤ s := by
  exact
    abVisible_surfaceCard_le_of_exactVisibleCompressionTarget_of_factorsThrough
      (Z := Z) (k := k) (s := s) hfactor hsurj
      (exactVisibleCompressionTarget_of_invariantCompressionTarget hsmall)

theorem not_invariantCompressionTarget_of_factorsThrough_ab_and_surjective_predict
    [Inhabited Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    (hs : s < Fintype.card (ABVisibleSurface k))
    (hfactor : G.FactorsThrough abVisibleData H)
    (hsurj : Function.Surjective H.predict) :
    ¬ InvariantCompressionTarget (Z := Z) (k := k) (Index := Index) G s := by
  intro hsmall
  exact Nat.not_le_of_lt hs <|
    invariantCompressionTarget_abSurfaceCard_le_of_factorsThrough_ab_and_surjective_predict
      (Z := Z) (k := k) (s := s) hfactor hsurj hsmall

theorem forkCompressionTarget_abSurfaceCard_le_of_factorsThrough_ab_and_surjective_predict
    [Inhabited Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    (hfactor : G.FactorsThrough abVisibleData H)
    (hsurj : Function.Surjective H.predict)
    (hsmall : ForkCompressionTarget (Z := Z) (k := k) (Index := Index) G s) :
    Fintype.card (ABVisibleSurface k) ≤ s := by
  exact
    abVisible_surfaceCard_le_of_exactVisibleCompressionTarget_of_factorsThrough
      (Z := Z) (k := k) (s := s) hfactor hsurj
      (exactVisibleCompressionTarget_of_forkCompressionTarget hsmall)

theorem not_forkCompressionTarget_of_factorsThrough_ab_and_surjective_predict
    [Inhabited Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    (hs : s < Fintype.card (ABVisibleSurface k))
    (hfactor : G.FactorsThrough abVisibleData H)
    (hsurj : Function.Surjective H.predict) :
    ¬ ForkCompressionTarget (Z := Z) (k := k) (Index := Index) G s := by
  intro hsmall
  exact Nat.not_le_of_lt hs <|
    forkCompressionTarget_abSurfaceCard_le_of_factorsThrough_ab_and_surjective_predict
      (Z := Z) (k := k) (s := s) hfactor hsurj hsmall

end

section

variable {Z : Type*} {k s clock : ℕ} {Index : Type*}

theorem abVisible_surfaceCard_le_of_clockedRealization_of_factorsThrough
    [Inhabited Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    (hfactor : G.FactorsThrough abVisibleData H)
    (hsurj : Function.Surjective H.predict)
    (hclocked :
      ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F) :
    Fintype.card (ABVisibleSurface k) ≤ s := by
  rcases hclocked with ⟨F, hreal⟩
  exact
    abVisible_surfaceCard_le_of_exactVisibleCompressionTarget_of_factorsThrough
      (Z := Z) (k := k) (s := s) hfactor hsurj
      (IndexedPredictorFamily.hasBitBudget_of_realizedByClockedBitFamily
        (G := G) (s := s) (clock := clock) hreal)

theorem not_exists_clockedExactVisibleRealization_of_factorsThrough_ab_and_surjective_predict
    [Inhabited Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    (hs : s < Fintype.card (ABVisibleSurface k))
    (hfactor : G.FactorsThrough abVisibleData H)
    (hsurj : Function.Surjective H.predict) :
    ¬ ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F := by
  intro hclocked
  exact Nat.not_le_of_lt hs <|
    abVisible_surfaceCard_le_of_clockedRealization_of_factorsThrough
      (Z := Z) (k := k) (s := s) (clock := clock) hfactor hsurj hclocked

theorem not_exists_clockedExactVisibleRealization_of_factorsThrough_ab_and_surjective_predict_of_lt_cardFormula
    [Inhabited Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    (hs : s < 2 ^ (2 * k))
    (hfactor : G.FactorsThrough abVisibleData H)
    (hsurj : Function.Surjective H.predict) :
    ¬ ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F := by
  exact
    not_exists_clockedExactVisibleRealization_of_factorsThrough_ab_and_surjective_predict
      (Z := Z) (k := k) (s := s) (clock := clock) (Index := Index)
      (by simpa [card_abVisibleSurface (k := k)] using hs)
      hfactor hsurj

/-- Clocked exact-visible realization is impossible below any finite probe
family already realized on the reduced `(a,b)` view. -/
theorem not_exists_clockedExactVisibleRealization_of_factorsThrough_ab_and_injective_realization_of_lt_card
    [Inhabited Z] {Probe : Type*} [Fintype Probe]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hs : 2 ^ s < Fintype.card Probe)
    (hfactor : G.FactorsThrough abVisibleData H) :
    ¬ ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F := by
  rw [exists_clockedExactVisibleRealization_iff_finitePredictorCover]
  exact
    not_finitePredictorCover_of_factorsThrough_ab_and_injective_realization_of_lt_card
      (Z := Z) (k := k) (Index := Index)
      target hinj hreal hs hfactor

end

end Mettapedia.Computability.PNP
