import Mettapedia.Computability.PNP.ExactVisibleImageBudget

/-!
# Regression checks for exact visible predictor-image budgets
-/

namespace Mettapedia.Computability.PNP.ExactVisibleImageBudgetRegression

open Mettapedia.Computability.PNP

universe u v w

variable {Index : Type u} {Input : Type v}
variable {View : Type w}
variable {Z : Type*} {k s clock : ℕ}

theorem indexed_hasBitBudget_iff_finitePredictorCover_regression
    {G : IndexedPredictorFamily Index Input} :
    G.HasBitBudget s ↔ G.FinitePredictorCover (2 ^ s) := by
  exact IndexedPredictorFamily.hasBitBudget_iff_finitePredictorCover

theorem indexed_finitePredictorCover_of_hasBitBudget_regression
    {G : IndexedPredictorFamily Index Input}
    (hsmall : G.HasBitBudget s) :
    G.FinitePredictorCover (2 ^ s) := by
  exact IndexedPredictorFamily.finitePredictorCover_of_hasBitBudget hsmall

theorem indexed_hasBitBudget_of_finitePredictorCover_regression
    {G : IndexedPredictorFamily Index Input}
    (hcover : G.FinitePredictorCover (2 ^ s)) :
    G.HasBitBudget s := by
  exact IndexedPredictorFamily.hasBitBudget_of_finitePredictorCover hcover

theorem indexed_finitePredictorCover_mono_regression
    {G : IndexedPredictorFamily Index Input} {N M : ℕ}
    (hNM : N ≤ M) (hcover : G.FinitePredictorCover N) :
    G.FinitePredictorCover M := by
  exact IndexedPredictorFamily.finitePredictorCover_mono hNM hcover

theorem indexed_finitePredictorCover_of_factorsThrough_regression
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View} {view : Input → View} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hcover : H.FinitePredictorCover N) :
    G.FinitePredictorCover N := by
  exact IndexedPredictorFamily.finitePredictorCover_of_factorsThrough
    hfactor hcover

theorem indexed_finitePredictorCover_of_factorsThrough_of_rightInverse_regression
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View} {view : Input → View}
    {sec : View → Input} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hcover : G.FinitePredictorCover N) :
    H.FinitePredictorCover N := by
  exact IndexedPredictorFamily.finitePredictorCover_of_factorsThrough_of_rightInverse
    hfactor hsection hcover

theorem indexed_finitePredictorCover_iff_finiteIndexRepresentativeCover_regression
    {G : IndexedPredictorFamily Index Input} {N : ℕ} :
    G.FinitePredictorCover N ↔ G.FiniteIndexRepresentativeCover N := by
  exact IndexedPredictorFamily.finitePredictorCover_iff_finiteIndexRepresentativeCover

theorem indexed_hasBitBudget_iff_finiteIndexRepresentativeCover_regression
    {G : IndexedPredictorFamily Index Input} :
    G.HasBitBudget s ↔ G.FiniteIndexRepresentativeCover (2 ^ s) := by
  exact IndexedPredictorFamily.hasBitBudget_iff_finiteIndexRepresentativeCover

theorem indexed_hasBitBudget_iff_finitePredictorQuotient_regression
    {G : IndexedPredictorFamily Index Input} :
    G.HasBitBudget s ↔ G.FinitePredictorQuotient (2 ^ s) := by
  exact IndexedPredictorFamily.hasBitBudget_iff_finitePredictorQuotient

theorem indexed_finitePredictorCover_of_finiteIndexRepresentativeCover_regression
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (hrep : G.FiniteIndexRepresentativeCover N) :
    G.FinitePredictorCover N := by
  exact IndexedPredictorFamily.finitePredictorCover_of_finiteIndexRepresentativeCover hrep

theorem indexed_finiteIndexRepresentativeCover_of_finitePredictorCover_regression
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (hcover : G.FinitePredictorCover N) :
    G.FiniteIndexRepresentativeCover N := by
  exact IndexedPredictorFamily.finiteIndexRepresentativeCover_of_finitePredictorCover
    hcover

theorem indexed_finitePredictorCover_iff_finitePredictorQuotient_regression
    {G : IndexedPredictorFamily Index Input} {N : ℕ} :
    G.FinitePredictorCover N ↔ G.FinitePredictorQuotient N := by
  exact IndexedPredictorFamily.finitePredictorCover_iff_finitePredictorQuotient

theorem indexed_finiteIndexRepresentativeCover_iff_finitePredictorQuotient_regression
    {G : IndexedPredictorFamily Index Input} {N : ℕ} :
    G.FiniteIndexRepresentativeCover N ↔ G.FinitePredictorQuotient N := by
  exact IndexedPredictorFamily.finiteIndexRepresentativeCover_iff_finitePredictorQuotient

theorem indexed_finitePredictorCover_of_finitePredictorQuotient_regression
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (hquot : G.FinitePredictorQuotient N) :
    G.FinitePredictorCover N := by
  exact IndexedPredictorFamily.finitePredictorCover_of_finitePredictorQuotient
    hquot

theorem indexed_finitePredictorQuotient_of_finitePredictorCover_regression
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (hcover : G.FinitePredictorCover N) :
    G.FinitePredictorQuotient N := by
  exact IndexedPredictorFamily.finitePredictorQuotient_of_finitePredictorCover
    hcover

theorem indexed_finiteIndexRepresentativeCover_mono_regression
    {G : IndexedPredictorFamily Index Input} {N M : ℕ}
    (hNM : N ≤ M) (hrep : G.FiniteIndexRepresentativeCover N) :
    G.FiniteIndexRepresentativeCover M := by
  exact IndexedPredictorFamily.finiteIndexRepresentativeCover_mono hNM hrep

theorem indexed_finiteIndexRepresentativeCover_of_factorsThrough_regression
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View} {view : Input → View} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hrep : H.FiniteIndexRepresentativeCover N) :
    G.FiniteIndexRepresentativeCover N := by
  exact IndexedPredictorFamily.finiteIndexRepresentativeCover_of_factorsThrough
    hfactor hrep

theorem indexed_finiteIndexRepresentativeCover_of_factorsThrough_of_rightInverse_regression
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View} {view : Input → View}
    {sec : View → Input} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hrep : G.FiniteIndexRepresentativeCover N) :
    H.FiniteIndexRepresentativeCover N := by
  exact IndexedPredictorFamily.finiteIndexRepresentativeCover_of_factorsThrough_of_rightInverse
    hfactor hsection hrep

theorem indexed_finitePredictorQuotient_mono_regression
    {G : IndexedPredictorFamily Index Input} {N M : ℕ}
    (hNM : N ≤ M) (hquot : G.FinitePredictorQuotient N) :
    G.FinitePredictorQuotient M := by
  exact IndexedPredictorFamily.finitePredictorQuotient_mono hNM hquot

theorem indexed_finitePredictorQuotient_of_factorsThrough_regression
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View} {view : Input → View} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hquot : H.FinitePredictorQuotient N) :
    G.FinitePredictorQuotient N := by
  exact IndexedPredictorFamily.finitePredictorQuotient_of_factorsThrough
    hfactor hquot

theorem indexed_finitePredictorQuotient_of_factorsThrough_of_rightInverse_regression
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View} {view : Input → View}
    {sec : View → Input} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hquot : G.FinitePredictorQuotient N) :
    H.FinitePredictorQuotient N := by
  exact IndexedPredictorFamily.finitePredictorQuotient_of_factorsThrough_of_rightInverse
    hfactor hsection hquot

theorem indexed_finitePredictorCover_card_le_of_injective_realization_regression
    {Probe : Type*} [Fintype Probe]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (target : Probe → Input → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hcover : G.FinitePredictorCover N) :
    Fintype.card Probe ≤ N := by
  exact IndexedPredictorFamily.finitePredictorCover_card_le_of_injective_realization
    target hinj hreal hcover

theorem indexed_not_finitePredictorCover_of_injective_realization_of_lt_card_regression
    {Probe : Type*} [Fintype Probe]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (target : Probe → Input → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hN : N < Fintype.card Probe) :
    ¬ G.FinitePredictorCover N := by
  exact IndexedPredictorFamily.not_finitePredictorCover_of_injective_realization_of_lt_card
    target hinj hreal hN

theorem indexed_finiteIndexRepresentativeCover_card_le_of_injective_realization_regression
    {Probe : Type*} [Fintype Probe]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (target : Probe → Input → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hrep : G.FiniteIndexRepresentativeCover N) :
    Fintype.card Probe ≤ N := by
  exact IndexedPredictorFamily.finiteIndexRepresentativeCover_card_le_of_injective_realization
    target hinj hreal hrep

theorem indexed_not_finiteIndexRepresentativeCover_of_injective_realization_of_lt_card_regression
    {Probe : Type*} [Fintype Probe]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (target : Probe → Input → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hN : N < Fintype.card Probe) :
    ¬ G.FiniteIndexRepresentativeCover N := by
  exact
    IndexedPredictorFamily.not_finiteIndexRepresentativeCover_of_injective_realization_of_lt_card
      target hinj hreal hN

theorem indexed_finitePredictorQuotient_card_le_of_injective_realization_regression
    {Probe : Type*} [Fintype Probe]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (target : Probe → Input → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hquot : G.FinitePredictorQuotient N) :
    Fintype.card Probe ≤ N := by
  exact IndexedPredictorFamily.finitePredictorQuotient_card_le_of_injective_realization
    target hinj hreal hquot

theorem indexed_not_finitePredictorQuotient_of_injective_realization_of_lt_card_regression
    {Probe : Type*} [Fintype Probe]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (target : Probe → Input → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hN : N < Fintype.card Probe) :
    ¬ G.FinitePredictorQuotient N := by
  exact IndexedPredictorFamily.not_finitePredictorQuotient_of_injective_realization_of_lt_card
    target hinj hreal hN

theorem indexed_finitePredictorCover_card_le_of_surjective_predict_regression
    [Fintype Input]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (hsurj : Function.Surjective G.predict)
    (hcover : G.FinitePredictorCover N) :
    2 ^ Fintype.card Input ≤ N := by
  exact IndexedPredictorFamily.finitePredictorCover_card_le_of_surjective_predict
    hsurj hcover

theorem indexed_not_finitePredictorCover_of_surjective_predict_regression
    [Fintype Input]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (hN : N < 2 ^ Fintype.card Input)
    (hsurj : Function.Surjective G.predict) :
    ¬ G.FinitePredictorCover N := by
  exact IndexedPredictorFamily.not_finitePredictorCover_of_surjective_predict
    hN hsurj

theorem indexed_finitePredictorCover_card_le_of_factorsThrough_of_rightInverse_of_surjective_predict_regression
    [Fintype View]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hsurj : Function.Surjective H.predict)
    (hcover : G.FinitePredictorCover N) :
    2 ^ Fintype.card View ≤ N := by
  exact
    IndexedPredictorFamily.finitePredictorCover_card_le_of_factorsThrough_of_rightInverse_of_surjective_predict
      hfactor hsection hsurj hcover

theorem indexed_not_finitePredictorCover_of_factorsThrough_of_rightInverse_of_surjective_predict_regression
    [Fintype View]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (hN : N < 2 ^ Fintype.card View)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hsurj : Function.Surjective H.predict) :
    ¬ G.FinitePredictorCover N := by
  exact
    IndexedPredictorFamily.not_finitePredictorCover_of_factorsThrough_of_rightInverse_of_surjective_predict
      hN hfactor hsection hsurj

theorem indexed_finitePredictorCover_card_le_of_factorsThrough_of_rightInverse_of_injective_realization_regression
    {Probe : Type*} [Fintype Probe]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (target : Probe → View → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hcover : G.FinitePredictorCover N) :
    Fintype.card Probe ≤ N := by
  exact
    IndexedPredictorFamily.finitePredictorCover_card_le_of_factorsThrough_of_rightInverse_of_injective_realization
      target hinj hreal hfactor hsection hcover

theorem indexed_not_finitePredictorCover_of_factorsThrough_of_rightInverse_of_injective_realization_of_lt_card_regression
    {Probe : Type*} [Fintype Probe]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (target : Probe → View → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hN : N < Fintype.card Probe)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view) :
    ¬ G.FinitePredictorCover N := by
  exact
    IndexedPredictorFamily.not_finitePredictorCover_of_factorsThrough_of_rightInverse_of_injective_realization_of_lt_card
      target hinj hreal hN hfactor hsection

theorem indexed_finiteIndexRepresentativeCover_card_le_of_factorsThrough_of_rightInverse_of_surjective_predict_regression
    [Fintype View]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hsurj : Function.Surjective H.predict)
    (hrep : G.FiniteIndexRepresentativeCover N) :
    2 ^ Fintype.card View ≤ N := by
  exact
    IndexedPredictorFamily.finiteIndexRepresentativeCover_card_le_of_factorsThrough_of_rightInverse_of_surjective_predict
      hfactor hsection hsurj hrep

theorem indexed_not_finiteIndexRepresentativeCover_of_factorsThrough_of_rightInverse_of_surjective_predict_regression
    [Fintype View]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (hN : N < 2 ^ Fintype.card View)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hsurj : Function.Surjective H.predict) :
    ¬ G.FiniteIndexRepresentativeCover N := by
  exact
    IndexedPredictorFamily.not_finiteIndexRepresentativeCover_of_factorsThrough_of_rightInverse_of_surjective_predict
      hN hfactor hsection hsurj

theorem indexed_finiteIndexRepresentativeCover_card_le_of_factorsThrough_of_rightInverse_of_injective_realization_regression
    {Probe : Type*} [Fintype Probe]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (target : Probe → View → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hrep : G.FiniteIndexRepresentativeCover N) :
    Fintype.card Probe ≤ N := by
  exact
    IndexedPredictorFamily.finiteIndexRepresentativeCover_card_le_of_factorsThrough_of_rightInverse_of_injective_realization
      target hinj hreal hfactor hsection hrep

theorem indexed_not_finiteIndexRepresentativeCover_of_factorsThrough_of_rightInverse_of_injective_realization_of_lt_card_regression
    {Probe : Type*} [Fintype Probe]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (target : Probe → View → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hN : N < Fintype.card Probe)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view) :
    ¬ G.FiniteIndexRepresentativeCover N := by
  exact
    IndexedPredictorFamily.not_finiteIndexRepresentativeCover_of_factorsThrough_of_rightInverse_of_injective_realization_of_lt_card
      target hinj hreal hN hfactor hsection

theorem indexed_finitePredictorQuotient_card_le_of_surjective_predict_regression
    [Fintype Input]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (hsurj : Function.Surjective G.predict)
    (hquot : G.FinitePredictorQuotient N) :
    2 ^ Fintype.card Input ≤ N := by
  exact IndexedPredictorFamily.finitePredictorQuotient_card_le_of_surjective_predict
    hsurj hquot

theorem indexed_not_finitePredictorQuotient_of_surjective_predict_regression
    [Fintype Input]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (hN : N < 2 ^ Fintype.card Input)
    (hsurj : Function.Surjective G.predict) :
    ¬ G.FinitePredictorQuotient N := by
  exact IndexedPredictorFamily.not_finitePredictorQuotient_of_surjective_predict
    hN hsurj

theorem indexed_finitePredictorQuotient_card_le_of_factorsThrough_of_rightInverse_of_surjective_predict_regression
    [Fintype View]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hsurj : Function.Surjective H.predict)
    (hquot : G.FinitePredictorQuotient N) :
    2 ^ Fintype.card View ≤ N := by
  exact
    IndexedPredictorFamily.finitePredictorQuotient_card_le_of_factorsThrough_of_rightInverse_of_surjective_predict
      hfactor hsection hsurj hquot

theorem indexed_not_finitePredictorQuotient_of_factorsThrough_of_rightInverse_of_surjective_predict_regression
    [Fintype View]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (hN : N < 2 ^ Fintype.card View)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hsurj : Function.Surjective H.predict) :
    ¬ G.FinitePredictorQuotient N := by
  exact
    IndexedPredictorFamily.not_finitePredictorQuotient_of_factorsThrough_of_rightInverse_of_surjective_predict
      hN hfactor hsection hsurj

theorem indexed_finitePredictorQuotient_card_le_of_factorsThrough_of_rightInverse_of_injective_realization_regression
    {Probe : Type*} [Fintype Probe]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (target : Probe → View → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hquot : G.FinitePredictorQuotient N) :
    Fintype.card Probe ≤ N := by
  exact
    IndexedPredictorFamily.finitePredictorQuotient_card_le_of_factorsThrough_of_rightInverse_of_injective_realization
      target hinj hreal hfactor hsection hquot

theorem indexed_not_finitePredictorQuotient_of_factorsThrough_of_rightInverse_of_injective_realization_of_lt_card_regression
    {Probe : Type*} [Fintype Probe]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (target : Probe → View → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hN : N < Fintype.card Probe)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view) :
    ¬ G.FinitePredictorQuotient N := by
  exact
    IndexedPredictorFamily.not_finitePredictorQuotient_of_factorsThrough_of_rightInverse_of_injective_realization_of_lt_card
      target hinj hreal hN hfactor hsection

theorem exact_visible_compressionTarget_iff_finitePredictorCover_regression
    {G : ExactVisibleSwitchedFamily Z k Index} :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s ↔
      G.FinitePredictorCover (2 ^ s) := by
  exact exactVisibleCompressionTarget_iff_finitePredictorCover

theorem exact_visible_compressionTarget_iff_finiteIndexRepresentativeCover_regression
    {G : ExactVisibleSwitchedFamily Z k Index} :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s ↔
      G.FiniteIndexRepresentativeCover (2 ^ s) := by
  exact exactVisibleCompressionTarget_iff_finiteIndexRepresentativeCover

theorem exact_visible_compressionTarget_iff_finitePredictorQuotient_regression
    {G : ExactVisibleSwitchedFamily Z k Index} :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s ↔
      G.FinitePredictorQuotient (2 ^ s) := by
  exact exactVisibleCompressionTarget_iff_finitePredictorQuotient

theorem exact_visible_clockedRealization_iff_finitePredictorCover_regression
    {G : ExactVisibleSwitchedFamily Z k Index} :
    (∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F) ↔
      G.FinitePredictorCover (2 ^ s) := by
  exact exists_clockedExactVisibleRealization_iff_finitePredictorCover

theorem exact_visible_clockedRealization_iff_finiteIndexRepresentativeCover_regression
    {G : ExactVisibleSwitchedFamily Z k Index} :
    (∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F) ↔
      G.FiniteIndexRepresentativeCover (2 ^ s) := by
  exact exists_clockedExactVisibleRealization_iff_finiteIndexRepresentativeCover

theorem exact_visible_clockedRealization_iff_finitePredictorQuotient_regression
    {G : ExactVisibleSwitchedFamily Z k Index} :
    (∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F) ↔
      G.FinitePredictorQuotient (2 ^ s) := by
  exact exists_clockedExactVisibleRealization_iff_finitePredictorQuotient

theorem exact_visible_not_clockedRealization_iff_not_finitePredictorCover_regression
    {G : ExactVisibleSwitchedFamily Z k Index} :
    (¬ ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F) ↔
      ¬ G.FinitePredictorCover (2 ^ s) := by
  exact not_exists_clockedExactVisibleRealization_iff_not_finitePredictorCover

theorem exact_visible_not_clockedRealization_iff_not_finiteIndexRepresentativeCover_regression
    {G : ExactVisibleSwitchedFamily Z k Index} :
    (¬ ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F) ↔
      ¬ G.FiniteIndexRepresentativeCover (2 ^ s) := by
  exact not_exists_clockedExactVisibleRealization_iff_not_finiteIndexRepresentativeCover

theorem exact_visible_not_clockedRealization_iff_not_finitePredictorQuotient_regression
    {G : ExactVisibleSwitchedFamily Z k Index} :
    (¬ ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F) ↔
      ¬ G.FinitePredictorQuotient (2 ^ s) := by
  exact not_exists_clockedExactVisibleRealization_iff_not_finitePredictorQuotient

theorem exact_visible_finitePredictorCover_card_le_of_injective_realization_regression
    {Probe : Type*} [Fintype Probe]
    {G : ExactVisibleSwitchedFamily Z k Index} {N : ℕ}
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hcover : G.FinitePredictorCover N) :
    Fintype.card Probe ≤ N := by
  exact exactVisible_finitePredictorCover_card_le_of_injective_realization
    target hinj hreal hcover

theorem exact_visible_finiteIndexRepresentativeCover_card_le_of_injective_realization_regression
    {Probe : Type*} [Fintype Probe]
    {G : ExactVisibleSwitchedFamily Z k Index} {N : ℕ}
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hrep : G.FiniteIndexRepresentativeCover N) :
    Fintype.card Probe ≤ N := by
  exact exactVisible_finiteIndexRepresentativeCover_card_le_of_injective_realization
    target hinj hreal hrep

theorem exact_visible_finitePredictorQuotient_card_le_of_injective_realization_regression
    {Probe : Type*} [Fintype Probe]
    {G : ExactVisibleSwitchedFamily Z k Index} {N : ℕ}
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hquot : G.FinitePredictorQuotient N) :
    Fintype.card Probe ≤ N := by
  exact exactVisible_finitePredictorQuotient_card_le_of_injective_realization
    target hinj hreal hquot

theorem exact_visible_not_finitePredictorCover_of_injective_realization_of_lt_card_regression
    {Probe : Type*} [Fintype Probe]
    {G : ExactVisibleSwitchedFamily Z k Index} {N : ℕ}
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hN : N < Fintype.card Probe) :
    ¬ G.FinitePredictorCover N := by
  exact not_exactVisible_finitePredictorCover_of_injective_realization_of_lt_card
    target hinj hreal hN

theorem exact_visible_not_finiteIndexRepresentativeCover_of_injective_realization_of_lt_card_regression
    {Probe : Type*} [Fintype Probe]
    {G : ExactVisibleSwitchedFamily Z k Index} {N : ℕ}
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hN : N < Fintype.card Probe) :
    ¬ G.FiniteIndexRepresentativeCover N := by
  exact
    not_exactVisible_finiteIndexRepresentativeCover_of_injective_realization_of_lt_card
      target hinj hreal hN

theorem exact_visible_not_finitePredictorQuotient_of_injective_realization_of_lt_card_regression
    {Probe : Type*} [Fintype Probe]
    {G : ExactVisibleSwitchedFamily Z k Index} {N : ℕ}
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hN : N < Fintype.card Probe) :
    ¬ G.FinitePredictorQuotient N := by
  exact not_exactVisible_finitePredictorQuotient_of_injective_realization_of_lt_card
    target hinj hreal hN

theorem exact_visible_not_compressionTarget_of_injective_realization_of_lt_card_regression
    {Probe : Type*} [Fintype Probe]
    {G : ExactVisibleSwitchedFamily Z k Index}
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hs : 2 ^ s < Fintype.card Probe) :
    ¬ ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s := by
  exact not_exactVisibleCompressionTarget_of_injective_realization_of_lt_card
    target hinj hreal hs

theorem exact_visible_not_clockedRealization_of_injective_realization_of_lt_card_regression
    {Probe : Type*} [Fintype Probe]
    {G : ExactVisibleSwitchedFamily Z k Index}
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hs : 2 ^ s < Fintype.card Probe) :
    ¬ ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F := by
  exact
    not_exists_clockedExactVisibleRealization_of_injective_realization_of_lt_card
      target hinj hreal hs

theorem exact_visible_finitePredictorCover_card_le_of_surjective_predict_regression
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index} {N : ℕ}
    (hsurj : Function.Surjective G.predict)
    (hcover : G.FinitePredictorCover N) :
    2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ N := by
  exact exactVisible_finitePredictorCover_card_le_of_surjective_predict
    hsurj hcover

theorem exact_visible_finiteIndexRepresentativeCover_card_le_of_surjective_predict_regression
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index} {N : ℕ}
    (hsurj : Function.Surjective G.predict)
    (hrep : G.FiniteIndexRepresentativeCover N) :
    2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ N := by
  exact exactVisible_finiteIndexRepresentativeCover_card_le_of_surjective_predict
    hsurj hrep

theorem exact_visible_finitePredictorQuotient_card_le_of_surjective_predict_regression
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index} {N : ℕ}
    (hsurj : Function.Surjective G.predict)
    (hquot : G.FinitePredictorQuotient N) :
    2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ N := by
  exact exactVisible_finitePredictorQuotient_card_le_of_surjective_predict
    hsurj hquot

theorem exact_visible_not_finitePredictorCover_of_surjective_predict_regression
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index} {N : ℕ}
    (hN : N < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k))
    (hsurj : Function.Surjective G.predict) :
    ¬ G.FinitePredictorCover N := by
  exact not_exactVisible_finitePredictorCover_of_surjective_predict hN hsurj

theorem exact_visible_not_finiteIndexRepresentativeCover_of_surjective_predict_regression
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index} {N : ℕ}
    (hN : N < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k))
    (hsurj : Function.Surjective G.predict) :
    ¬ G.FiniteIndexRepresentativeCover N := by
  exact not_exactVisible_finiteIndexRepresentativeCover_of_surjective_predict hN hsurj

theorem exact_visible_not_finitePredictorQuotient_of_surjective_predict_regression
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index} {N : ℕ}
    (hN : N < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k))
    (hsurj : Function.Surjective G.predict) :
    ¬ G.FinitePredictorQuotient N := by
  exact not_exactVisible_finitePredictorQuotient_of_surjective_predict hN hsurj

theorem exact_visible_not_compressionTarget_of_surjective_predict_of_lt_predictorCard_regression
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hs : 2 ^ s < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k))
    (hsurj : Function.Surjective G.predict) :
    ¬ ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s := by
  exact not_exactVisibleCompressionTarget_of_surjective_predict_of_lt_predictorCard
    hs hsurj

theorem exact_visible_not_clockedRealization_of_surjective_predict_of_lt_predictorCard_regression
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hs : 2 ^ s < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k))
    (hsurj : Function.Surjective G.predict) :
    ¬ ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F := by
  exact not_exists_clockedExactVisibleRealization_of_surjective_predict_of_lt_predictorCard
    hs hsurj

end Mettapedia.Computability.PNP.ExactVisibleImageBudgetRegression
