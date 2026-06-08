import Mettapedia.Computability.PNP.ExactVisibleCompressionObstruction
import Mettapedia.Computability.PNP.ExactVisibleImageBudget
import Mettapedia.Computability.PNP.ClockedKpolyGapAssessment
import Mettapedia.Computability.PNP.PNPv13RouteSynthesis

/-!
# P vs NP crux: product success alone does not give Kpoly compression

The v13 switching layer proves finite product-success bounds from fielded
half-success certificates.  Those facts live over finite event histories.  The
exact-visible `Kpoly` compression target, however, is a statement about the
image of a predictor family on the post-switch surface `u = (z, a, b)`.

This file formalizes the missing bridge as a counterexample: a bridge that uses
only the product bound, or only a fielded switching certificate, would have to
compress every exact-visible switched family.  The full Boolean family on the
exact visible surface refutes that below the surface-cardinality threshold.
-/

namespace Mettapedia.Computability.PNP

universe u v

/-- The fielded v13 finite tower product bound from an existing history. -/
def V13FieldedProductBoundFrom (Ω : Type u) [Fintype Ω]
    (hist : List (FiniteEvent Ω)) (items : List (V13FieldedStep Ω)) : Prop :=
  2 ^ items.length *
      finiteHistoryCount Ω (hist ++ v13FieldedSuccessEvents items) ≤
    finiteHistoryCount Ω hist

/-- The full Boolean-rule family on the exact manuscript-visible post-switch
surface.  Its index is the rule itself. -/
def fullExactVisibleRuleFamily (Z : Type v) (k : ℕ) :
    ExactVisibleSwitchedFamily Z k (ExactVisibleRule Z k) where
  predict rule := rule

/-- The full exact-visible family realizes every Boolean rule on the visible
post-switch surface. -/
theorem fullExactVisibleRuleFamily_surjective (Z : Type v) (k : ℕ) :
    Function.Surjective (fullExactVisibleRuleFamily Z k).predict := by
  intro rule
  exact ⟨rule, rfl⟩

/-- A product-bound-only `Kpoly` bridge would assert that the finite tower
product bound, without any semantic relation to the exact-visible predictor
family, forces an `s`-bit exact visible compression target for every family. -/
def ProductBoundOnlyExactVisibleCompressionBridge
    (Ω : Type u) [Fintype Ω] (Z : Type v) (k s : ℕ)
    (hist : List (FiniteEvent Ω)) (items : List (V13FieldedStep Ω)) : Prop :=
  ∀ {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index),
    V13FieldedProductBoundFrom Ω hist items →
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s

/-- The finite-image semantic content that a product-bound bridge must supply
for one fixed exact-visible predictor family. -/
def ProductBoundSemanticFiniteImageBridge
    (Ω : Type u) [Fintype Ω] (Z : Type v) (k s : ℕ)
    (hist : List (FiniteEvent Ω)) (items : List (V13FieldedStep Ω))
    {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index) : Prop :=
  V13FieldedProductBoundFrom Ω hist items → G.FinitePredictorCover (2 ^ s)

/-- A fielded-switching-only `Kpoly` bridge would assert that a fixed-field v13
certificate, without any semantic relation to the exact-visible predictor
family, forces an `s`-bit exact visible compression target for every family. -/
def FieldedSwitchingOnlyExactVisibleCompressionBridge
    (Ω : Type u) [Fintype Ω] (Z : Type v) (k s : ℕ)
    (hist : List (FiniteEvent Ω)) (items : List (V13FieldedStep Ω)) : Prop :=
  ∀ {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index),
    V13FieldSwitchingInstantiatedFrom hist items →
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s

/-- The finite-image semantic content that a fielded-switching bridge must
supply for one fixed exact-visible predictor family. -/
def FieldedSwitchingSemanticFiniteImageBridge
    (Ω : Type u) [Fintype Ω] (Z : Type v) (k s : ℕ)
    (hist : List (FiniteEvent Ω)) (items : List (V13FieldedStep Ω))
    {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index) : Prop :=
  V13FieldSwitchingInstantiatedFrom hist items →
    G.FinitePredictorCover (2 ^ s)

/-- A product-bound-only bridge to the full clocked finite-learning payload
would assert that the finite tower product bound, without any semantic relation
to the exact-visible predictor family, forces the full payload for every
family. -/
def ProductBoundOnlyClockedKpolyFiniteLearningBridge
    (Ω : Type u) [Fintype Ω] (Z : Type v) [Fintype Z] (k s clock : ℕ)
    (hist : List (FiniteEvent Ω)) (items : List (V13FieldedStep Ω)) : Prop :=
  ∀ {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index),
    V13FieldedProductBoundFrom Ω hist items →
    ClockedKpolyFiniteLearningPayload G s clock

/-- A fielded-switching-only bridge to the full clocked finite-learning payload
would assert that the fixed-field certificate, without any semantic relation to
the exact-visible predictor family, forces the full payload for every family. -/
def FieldedSwitchingOnlyClockedKpolyFiniteLearningBridge
    (Ω : Type u) [Fintype Ω] (Z : Type v) [Fintype Z] (k s clock : ℕ)
    (hist : List (FiniteEvent Ω)) (items : List (V13FieldedStep Ω)) : Prop :=
  ∀ {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index),
    V13FieldSwitchingInstantiatedFrom hist items →
    ClockedKpolyFiniteLearningPayload G s clock

/-- For one fixed exact-visible family, a product-bound-to-compression bridge
has exactly the same mathematical content as a product-bound-to-finite-image
bridge. -/
theorem productBoundSemanticFiniteImageBridge_iff_exactVisibleCompressionBridge
    {Ω : Type u} [Fintype Ω] {Z : Type v} {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} {G : ExactVisibleSwitchedFamily Z k Index} :
    ProductBoundSemanticFiniteImageBridge Ω Z k s hist items G ↔
      (V13FieldedProductBoundFrom Ω hist items →
        ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s) := by
  constructor
  · intro h hprod
    exact
      (exactVisibleCompressionTarget_iff_finitePredictorCover
        (Z := Z) (k := k) (s := s) (Index := Index) (G := G)).mpr
        (h hprod)
  · intro h hprod
    exact
      (exactVisibleCompressionTarget_iff_finitePredictorCover
        (Z := Z) (k := k) (s := s) (Index := Index) (G := G)).mp
        (h hprod)

/-- Once the product bound is actually true, deriving exact-visible compression
from that product bound is equivalent to giving the finite predictor-image
cover itself. -/
theorem productBound_true_exactVisibleCompressionBridge_iff_finitePredictorCover
    {Ω : Type u} [Fintype Ω] {Z : Type v} {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} {G : ExactVisibleSwitchedFamily Z k Index}
    (hprod : V13FieldedProductBoundFrom Ω hist items) :
    (V13FieldedProductBoundFrom Ω hist items →
        ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s) ↔
      G.FinitePredictorCover (2 ^ s) := by
  constructor
  · intro h
    exact
      (exactVisibleCompressionTarget_iff_finitePredictorCover
        (Z := Z) (k := k) (s := s) (Index := Index) (G := G)).mp
        (h hprod)
  · intro hcover _hprod
    exact
      (exactVisibleCompressionTarget_iff_finitePredictorCover
        (Z := Z) (k := k) (s := s) (Index := Index) (G := G)).mpr
        hcover

/-- The global product-bound-only bridge is exactly a demand for finite
predictor-image covers for every exact-visible family. -/
theorem productBoundOnlyExactVisibleCompressionBridge_iff_forall_semanticFiniteImageBridge
    {Ω : Type u} [Fintype Ω] {Z : Type v} {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)} :
    ProductBoundOnlyExactVisibleCompressionBridge Ω Z k s hist items ↔
      ∀ {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index),
        ProductBoundSemanticFiniteImageBridge Ω Z k s hist items G := by
  constructor
  · intro hbridge Index G hprod
    exact
      (exactVisibleCompressionTarget_iff_finitePredictorCover
        (Z := Z) (k := k) (s := s) (Index := Index) (G := G)).mp
        (hbridge (Index := Index) G hprod)
  · intro hbridge Index G hprod
    exact
      (exactVisibleCompressionTarget_iff_finitePredictorCover
        (Z := Z) (k := k) (s := s) (Index := Index) (G := G)).mpr
        (hbridge (Index := Index) G hprod)

/-- For one fixed exact-visible family, a fielded-certificate-to-compression
bridge has exactly the same mathematical content as a
fielded-certificate-to-finite-image bridge. -/
theorem fieldedSwitchingSemanticFiniteImageBridge_iff_exactVisibleCompressionBridge
    {Ω : Type u} [Fintype Ω] {Z : Type v} {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} {G : ExactVisibleSwitchedFamily Z k Index} :
    FieldedSwitchingSemanticFiniteImageBridge Ω Z k s hist items G ↔
      (V13FieldSwitchingInstantiatedFrom hist items →
        ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s) := by
  constructor
  · intro h hfield
    exact
      (exactVisibleCompressionTarget_iff_finitePredictorCover
        (Z := Z) (k := k) (s := s) (Index := Index) (G := G)).mpr
        (h hfield)
  · intro h hfield
    exact
      (exactVisibleCompressionTarget_iff_finitePredictorCover
        (Z := Z) (k := k) (s := s) (Index := Index) (G := G)).mp
        (h hfield)

/-- Once the fielded switching certificate is actually true, deriving
exact-visible compression from that certificate is equivalent to giving the
finite predictor-image cover itself. -/
theorem fieldedSwitching_true_exactVisibleCompressionBridge_iff_finitePredictorCover
    {Ω : Type u} [Fintype Ω] {Z : Type v} {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} {G : ExactVisibleSwitchedFamily Z k Index}
    (hfield : V13FieldSwitchingInstantiatedFrom hist items) :
    (V13FieldSwitchingInstantiatedFrom hist items →
        ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s) ↔
      G.FinitePredictorCover (2 ^ s) := by
  constructor
  · intro h
    exact
      (exactVisibleCompressionTarget_iff_finitePredictorCover
        (Z := Z) (k := k) (s := s) (Index := Index) (G := G)).mp
        (h hfield)
  · intro hcover _hfield
    exact
      (exactVisibleCompressionTarget_iff_finitePredictorCover
        (Z := Z) (k := k) (s := s) (Index := Index) (G := G)).mpr
        hcover

/-- The global fielded-switching-only bridge is exactly a demand for finite
predictor-image covers for every exact-visible family. -/
theorem fieldedSwitchingOnlyExactVisibleCompressionBridge_iff_forall_semanticFiniteImageBridge
    {Ω : Type u} [Fintype Ω] {Z : Type v} {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)} :
    FieldedSwitchingOnlyExactVisibleCompressionBridge Ω Z k s hist items ↔
      ∀ {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index),
        FieldedSwitchingSemanticFiniteImageBridge Ω Z k s hist items G := by
  constructor
  · intro hbridge Index G hfield
    exact
      (exactVisibleCompressionTarget_iff_finitePredictorCover
        (Z := Z) (k := k) (s := s) (Index := Index) (G := G)).mp
        (hbridge (Index := Index) G hfield)
  · intro hbridge Index G hfield
    exact
      (exactVisibleCompressionTarget_iff_finitePredictorCover
        (Z := Z) (k := k) (s := s) (Index := Index) (G := G)).mpr
        (hbridge (Index := Index) G hfield)

/-- A product-bound-only bridge to the full clocked finite-learning payload has
exactly the same semantic content as finite predictor-image covers for every
exact-visible family.  Rephrasing the target as a bundled learning payload does
not remove the missing finite-image theorem. -/
theorem productBoundOnlyClockedKpolyFiniteLearningBridge_iff_forall_semanticFiniteImageBridge
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s clock : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)} :
    ProductBoundOnlyClockedKpolyFiniteLearningBridge Ω Z k s clock hist items ↔
      ∀ {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index),
        ProductBoundSemanticFiniteImageBridge Ω Z k s hist items G := by
  constructor
  · intro hbridge Index G hprod
    exact
      (clockedKpolyFiniteLearningPayload_iff_finitePredictorCover
        (Z := Z) (k := k) (s := s) (clock := clock) (Index := Index)
        (G := G)).mp
        (hbridge (Index := Index) G hprod)
  · intro hbridge Index G hprod
    exact
      (clockedKpolyFiniteLearningPayload_iff_finitePredictorCover
        (Z := Z) (k := k) (s := s) (clock := clock) (Index := Index)
        (G := G)).mpr
        (hbridge (Index := Index) G hprod)

/-- A fielded-switching-only bridge to the full clocked finite-learning payload
has exactly the same semantic content as finite predictor-image covers for
every exact-visible family. -/
theorem fieldedSwitchingOnlyClockedKpolyFiniteLearningBridge_iff_forall_semanticFiniteImageBridge
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s clock : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)} :
    FieldedSwitchingOnlyClockedKpolyFiniteLearningBridge Ω Z k s clock hist items ↔
      ∀ {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index),
        FieldedSwitchingSemanticFiniteImageBridge Ω Z k s hist items G := by
  constructor
  · intro hbridge Index G hfield
    exact
      (clockedKpolyFiniteLearningPayload_iff_finitePredictorCover
        (Z := Z) (k := k) (s := s) (clock := clock) (Index := Index)
        (G := G)).mp
        (hbridge (Index := Index) G hfield)
  · intro hbridge Index G hfield
    exact
      (clockedKpolyFiniteLearningPayload_iff_finitePredictorCover
        (Z := Z) (k := k) (s := s) (clock := clock) (Index := Index)
        (G := G)).mpr
        (hbridge (Index := Index) G hfield)

/-- Any product-bound-only clocked-payload bridge immediately gives the older
exact-visible compression bridge. -/
theorem productBoundOnlyExactVisibleCompressionBridge_of_clockedKpolyFiniteLearningBridge
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s clock : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hbridge :
      ProductBoundOnlyClockedKpolyFiniteLearningBridge Ω Z k s clock hist items) :
    ProductBoundOnlyExactVisibleCompressionBridge Ω Z k s hist items := by
  intro Index G hprod
  exact
    exactVisibleCompressionTarget_of_clockedKpolyFiniteLearningPayload
      (Z := Z) (k := k) (s := s) (clock := clock) (Index := Index)
      (G := G) (hbridge (Index := Index) G hprod)

/-- Any fielded-switching-only clocked-payload bridge immediately gives the
older exact-visible compression bridge. -/
theorem fieldedSwitchingOnlyExactVisibleCompressionBridge_of_clockedKpolyFiniteLearningBridge
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s clock : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hbridge :
      FieldedSwitchingOnlyClockedKpolyFiniteLearningBridge Ω Z k s clock hist items) :
    FieldedSwitchingOnlyExactVisibleCompressionBridge Ω Z k s hist items := by
  intro Index G hfield
  exact
    exactVisibleCompressionTarget_of_clockedKpolyFiniteLearningPayload
      (Z := Z) (k := k) (s := s) (clock := clock) (Index := Index)
      (G := G) (hbridge (Index := Index) G hfield)

/-- Any true product-bound-only bridge supplies a finite predictor-image cover
for the chosen exact-visible family. -/
theorem finitePredictorCover_of_productBoundOnlyExactVisibleCompressionBridge
    {Ω : Type u} [Fintype Ω] {Z : Type v} {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index)
    (hbridge : ProductBoundOnlyExactVisibleCompressionBridge Ω Z k s hist items)
    (hprod : V13FieldedProductBoundFrom Ω hist items) :
    G.FinitePredictorCover (2 ^ s) :=
  (exactVisibleCompressionTarget_iff_finitePredictorCover
    (Z := Z) (k := k) (s := s) (Index := Index) (G := G)).mp
    (hbridge G hprod)

/-- Any true product-bound-only bridge supplies an actual finite representative
index cover for the chosen exact-visible family. -/
theorem finiteIndexRepresentativeCover_of_productBoundOnlyExactVisibleCompressionBridge
    {Ω : Type u} [Fintype Ω] {Z : Type v} {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index)
    (hbridge : ProductBoundOnlyExactVisibleCompressionBridge Ω Z k s hist items)
    (hprod : V13FieldedProductBoundFrom Ω hist items) :
    G.FiniteIndexRepresentativeCover (2 ^ s) :=
  (exactVisibleCompressionTarget_iff_finiteIndexRepresentativeCover
    (Z := Z) (k := k) (s := s) (Index := Index) (G := G)).mp
    (hbridge G hprod)

/-- Any true product-bound-only bridge supplies a finite quotient-code
presentation for the chosen exact-visible family. -/
theorem finitePredictorQuotient_of_productBoundOnlyExactVisibleCompressionBridge
    {Ω : Type u} [Fintype Ω] {Z : Type v} {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index)
    (hbridge : ProductBoundOnlyExactVisibleCompressionBridge Ω Z k s hist items)
    (hprod : V13FieldedProductBoundFrom Ω hist items) :
    G.FinitePredictorQuotient (2 ^ s) :=
  (exactVisibleCompressionTarget_iff_finitePredictorQuotient
    (Z := Z) (k := k) (s := s) (Index := Index) (G := G)).mp
    (hbridge G hprod)

/-- Any true fielded-switching-only bridge supplies a finite predictor-image
cover for the chosen exact-visible family. -/
theorem finitePredictorCover_of_fieldedSwitchingOnlyExactVisibleCompressionBridge
    {Ω : Type u} [Fintype Ω] {Z : Type v} {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index)
    (hbridge : FieldedSwitchingOnlyExactVisibleCompressionBridge Ω Z k s hist items)
    (hfield : V13FieldSwitchingInstantiatedFrom hist items) :
    G.FinitePredictorCover (2 ^ s) :=
  (exactVisibleCompressionTarget_iff_finitePredictorCover
    (Z := Z) (k := k) (s := s) (Index := Index) (G := G)).mp
    (hbridge G hfield)

/-- Any true fielded-switching-only bridge supplies an actual finite
representative index cover for the chosen exact-visible family. -/
theorem finiteIndexRepresentativeCover_of_fieldedSwitchingOnlyExactVisibleCompressionBridge
    {Ω : Type u} [Fintype Ω] {Z : Type v} {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index)
    (hbridge : FieldedSwitchingOnlyExactVisibleCompressionBridge Ω Z k s hist items)
    (hfield : V13FieldSwitchingInstantiatedFrom hist items) :
    G.FiniteIndexRepresentativeCover (2 ^ s) :=
  (exactVisibleCompressionTarget_iff_finiteIndexRepresentativeCover
    (Z := Z) (k := k) (s := s) (Index := Index) (G := G)).mp
    (hbridge G hfield)

/-- Any true fielded-switching-only bridge supplies a finite quotient-code
presentation for the chosen exact-visible family. -/
theorem finitePredictorQuotient_of_fieldedSwitchingOnlyExactVisibleCompressionBridge
    {Ω : Type u} [Fintype Ω] {Z : Type v} {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index)
    (hbridge : FieldedSwitchingOnlyExactVisibleCompressionBridge Ω Z k s hist items)
    (hfield : V13FieldSwitchingInstantiatedFrom hist items) :
    G.FinitePredictorQuotient (2 ^ s) :=
  (exactVisibleCompressionTarget_iff_finitePredictorQuotient
    (Z := Z) (k := k) (s := s) (Index := Index) (G := G)).mp
    (hbridge G hfield)

/-- If the chosen exact-visible family is already fully expressive, then a true
product-bound premise cannot imply below-surface exact-visible compression for
that family. -/
theorem not_productBoundExactVisibleCompressionBridge_of_true_productBound_of_surjective_predict_of_lt_surfaceCard
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} {G : ExactVisibleSwitchedFamily Z k Index}
    (hprod : V13FieldedProductBoundFrom Ω hist items)
    (hsurj : Function.Surjective G.predict)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (V13FieldedProductBoundFrom Ω hist items →
        ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s) := by
  intro hbridge
  exact
    (not_exactVisibleCompressionTarget_of_surjective_predict
      (Z := Z) (k := k) (s := s) (Index := Index) (G := G) hs hsurj)
      (hbridge hprod)

/-- If the chosen exact-visible family is already fully expressive, then a true
fixed-field switching premise cannot imply below-surface exact-visible
compression for that family. -/
theorem not_fieldedSwitchingExactVisibleCompressionBridge_of_true_fieldedSwitching_of_surjective_predict_of_lt_surfaceCard
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} {G : ExactVisibleSwitchedFamily Z k Index}
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hsurj : Function.Surjective G.predict)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (V13FieldSwitchingInstantiatedFrom hist items →
        ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s) := by
  intro hbridge
  exact
    (not_exactVisibleCompressionTarget_of_surjective_predict
      (Z := Z) (k := k) (s := s) (Index := Index) (G := G) hs hsurj)
      (hbridge hfield)

/-- Equivalently at the semantic-boundary layer, a true product-bound premise
cannot supply a below-cardinality finite predictor-image cover for a fully
expressive exact-visible family. -/
theorem not_productBoundSemanticFiniteImageBridge_of_true_productBound_of_surjective_predict_of_lt_predictorCard
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} {G : ExactVisibleSwitchedFamily Z k Index}
    (hprod : V13FieldedProductBoundFrom Ω hist items)
    (hsurj : Function.Surjective G.predict)
    (hs : 2 ^ s < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ProductBoundSemanticFiniteImageBridge Ω Z k s hist items G := by
  intro hbridge
  exact
    (not_exactVisible_finitePredictorCover_of_surjective_predict
      (Z := Z) (k := k) (Index := Index) (G := G) hs hsurj)
      (hbridge hprod)

/-- Equivalently at the semantic-boundary layer, a true fixed-field switching
premise cannot supply a below-cardinality finite predictor-image cover for a
fully expressive exact-visible family. -/
theorem not_fieldedSwitchingSemanticFiniteImageBridge_of_true_fieldedSwitching_of_surjective_predict_of_lt_predictorCard
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} {G : ExactVisibleSwitchedFamily Z k Index}
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hsurj : Function.Surjective G.predict)
    (hs : 2 ^ s < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ FieldedSwitchingSemanticFiniteImageBridge Ω Z k s hist items G := by
  intro hbridge
  exact
    (not_exactVisible_finitePredictorCover_of_surjective_predict
      (Z := Z) (k := k) (Index := Index) (G := G) hs hsurj)
      (hbridge hfield)

/-- A true product-bound-only bridge is impossible whenever any exact-visible
family in its scope is already fully expressive below the surface threshold. -/
theorem not_productBoundOnlyExactVisibleCompressionBridge_of_true_productBound_of_surjective_predict_of_lt_surfaceCard
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index)
    (hprod : V13FieldedProductBoundFrom Ω hist items)
    (hsurj : Function.Surjective G.predict)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ProductBoundOnlyExactVisibleCompressionBridge Ω Z k s hist items := by
  intro hbridge
  exact
    (not_exactVisibleCompressionTarget_of_surjective_predict
      (Z := Z) (k := k) (s := s) (Index := Index) (G := G) hs hsurj)
      (hbridge G hprod)

/-- A true fixed-field-switching-only bridge is impossible whenever any
exact-visible family in its scope is already fully expressive below the surface
threshold. -/
theorem not_fieldedSwitchingOnlyExactVisibleCompressionBridge_of_true_fieldedSwitching_of_surjective_predict_of_lt_surfaceCard
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index)
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hsurj : Function.Surjective G.predict)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ FieldedSwitchingOnlyExactVisibleCompressionBridge Ω Z k s hist items := by
  intro hbridge
  exact
    (not_exactVisibleCompressionTarget_of_surjective_predict
      (Z := Z) (k := k) (s := s) (Index := Index) (G := G) hs hsurj)
      (hbridge G hfield)

/-- Even the empty product-bound instance cannot imply a below-surface exact
visible compression theorem.  The product fact is true, but the full visible
Boolean family still needs the full truth-table budget. -/
theorem not_productBoundOnlyExactVisibleCompressionBridge_nil_of_lt_surfaceCard
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ProductBoundOnlyExactVisibleCompressionBridge
        Ω Z k s ([] : List (FiniteEvent Ω)) ([] : List (V13FieldedStep Ω)) := by
  intro hbridge
  have hbound :
      2 ^ ([] : List (V13FieldedStep Ω)).length *
          finiteHistoryCount Ω
            (([] : List (FiniteEvent Ω)) ++
              v13FieldedSuccessEvents ([] : List (V13FieldedStep Ω))) ≤
        finiteHistoryCount Ω ([] : List (FiniteEvent Ω)) := by
    simp [v13FieldedSuccessEvents]
  have hsmall :
      ExactVisibleCompressionTarget
        (Z := Z) (k := k) (Index := ExactVisibleRule Z k)
        (fullExactVisibleRuleFamily Z k) s :=
    hbridge (Index := ExactVisibleRule Z k) (fullExactVisibleRuleFamily Z k)
      hbound
  exact
    (not_exactVisibleCompressionTarget_of_surjective_predict
      (Z := Z) (k := k) (s := s) (Index := ExactVisibleRule Z k)
      (G := fullExactVisibleRuleFamily Z k)
      hs (fullExactVisibleRuleFamily_surjective Z k)) hsmall

/-- Even an empty fielded switching certificate cannot imply below-surface exact
visible compression.  The certificate is true but has no information about the
predictor-family image. -/
theorem not_fieldedSwitchingOnlyExactVisibleCompressionBridge_nil_of_lt_surfaceCard
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ FieldedSwitchingOnlyExactVisibleCompressionBridge
        Ω Z k s ([] : List (FiniteEvent Ω)) ([] : List (V13FieldedStep Ω)) := by
  intro hbridge
  have hfield :
      V13FieldSwitchingInstantiatedFrom
        ([] : List (FiniteEvent Ω)) ([] : List (V13FieldedStep Ω)) := by
    trivial
  have hsmall :
      ExactVisibleCompressionTarget
        (Z := Z) (k := k) (Index := ExactVisibleRule Z k)
        (fullExactVisibleRuleFamily Z k) s :=
    hbridge (Index := ExactVisibleRule Z k) (fullExactVisibleRuleFamily Z k)
      hfield
  exact
    (not_exactVisibleCompressionTarget_of_surjective_predict
      (Z := Z) (k := k) (s := s) (Index := ExactVisibleRule Z k)
      (G := fullExactVisibleRuleFamily Z k)
      hs (fullExactVisibleRuleFamily_surjective Z k)) hsmall

/-- A nontrivial one-step Boolean-square product-bound certificate still cannot
force below-surface exact-visible compression without a semantic image theorem
for the predictor family. -/
theorem not_productBoundOnlyExactVisibleCompressionBridge_boolPair_one_step_of_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k s : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ProductBoundOnlyExactVisibleCompressionBridge
        (Bool × Bool) Z k s
        ([] : List (FiniteEvent (Bool × Bool)))
        [v13BoolPairUnitFieldedStep] := by
  intro hbridge
  have hfield :
      V13FieldSwitchingInstantiatedFrom
        ([] : List (FiniteEvent (Bool × Bool)))
        [v13BoolPairUnitFieldedStep] := by
    exact ⟨v13FieldPrefixInstantiation_unitField_empty, trivial⟩
  have hbound :
      2 ^ [v13BoolPairUnitFieldedStep].length *
          finiteHistoryCount (Bool × Bool)
            (([] : List (FiniteEvent (Bool × Bool))) ++
              v13FieldedSuccessEvents [v13BoolPairUnitFieldedStep]) ≤
        finiteHistoryCount (Bool × Bool)
          ([] : List (FiniteEvent (Bool × Bool))) :=
    v13_product_bound_of_fieldInstantiatedFrom
      ([] : List (FiniteEvent (Bool × Bool)))
      [v13BoolPairUnitFieldedStep] hfield
  have hsmall :
      ExactVisibleCompressionTarget
        (Z := Z) (k := k) (Index := ExactVisibleRule Z k)
        (fullExactVisibleRuleFamily Z k) s :=
    hbridge (Index := ExactVisibleRule Z k) (fullExactVisibleRuleFamily Z k)
      hbound
  exact
    (not_exactVisibleCompressionTarget_of_surjective_predict
      (Z := Z) (k := k) (s := s) (Index := ExactVisibleRule Z k)
      (G := fullExactVisibleRuleFamily Z k)
      hs (fullExactVisibleRuleFamily_surjective Z k)) hsmall

/-- A nontrivial one-step fixed-field certificate itself also cannot force
below-surface exact-visible compression unless it is connected to a concrete
small predictor image. -/
theorem not_fieldedSwitchingOnlyExactVisibleCompressionBridge_boolPair_one_step_of_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k s : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ FieldedSwitchingOnlyExactVisibleCompressionBridge
        (Bool × Bool) Z k s
        ([] : List (FiniteEvent (Bool × Bool)))
        [v13BoolPairUnitFieldedStep] := by
  intro hbridge
  have hfield :
      V13FieldSwitchingInstantiatedFrom
        ([] : List (FiniteEvent (Bool × Bool)))
        [v13BoolPairUnitFieldedStep] := by
    exact ⟨v13FieldPrefixInstantiation_unitField_empty, trivial⟩
  have hsmall :
      ExactVisibleCompressionTarget
        (Z := Z) (k := k) (Index := ExactVisibleRule Z k)
        (fullExactVisibleRuleFamily Z k) s :=
    hbridge (Index := ExactVisibleRule Z k) (fullExactVisibleRuleFamily Z k)
      hfield
  exact
    (not_exactVisibleCompressionTarget_of_surjective_predict
      (Z := Z) (k := k) (s := s) (Index := ExactVisibleRule Z k)
      (G := fullExactVisibleRuleFamily Z k)
      hs (fullExactVisibleRuleFamily_surjective Z k)) hsmall

/-- A true product-bound premise cannot imply the bundled clocked payload for a
fully expressive exact-visible family below the full Boolean predictor-space
cardinality. -/
theorem not_productBoundClockedKpolyFiniteLearningBridge_of_true_productBound_of_surjective_predict_of_lt_predictorCard
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s clock : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} {G : ExactVisibleSwitchedFamily Z k Index}
    (hprod : V13FieldedProductBoundFrom Ω hist items)
    (hsurj : Function.Surjective G.predict)
    (hs : 2 ^ s < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (V13FieldedProductBoundFrom Ω hist items →
        ClockedKpolyFiniteLearningPayload G s clock) := by
  intro hbridge
  exact
    (not_clockedKpolyFiniteLearningPayload_of_surjective_predict_of_lt_predictorCard
      (Z := Z) (k := k) (s := s) (clock := clock) (Index := Index)
      (G := G) hs hsurj)
      (hbridge hprod)

/-- A true fixed-field switching premise cannot imply the bundled clocked
payload for a fully expressive exact-visible family below the full Boolean
predictor-space cardinality. -/
theorem not_fieldedSwitchingClockedKpolyFiniteLearningBridge_of_true_fieldedSwitching_of_surjective_predict_of_lt_predictorCard
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s clock : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} {G : ExactVisibleSwitchedFamily Z k Index}
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hsurj : Function.Surjective G.predict)
    (hs : 2 ^ s < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (V13FieldSwitchingInstantiatedFrom hist items →
        ClockedKpolyFiniteLearningPayload G s clock) := by
  intro hbridge
  exact
    (not_clockedKpolyFiniteLearningPayload_of_surjective_predict_of_lt_predictorCard
      (Z := Z) (k := k) (s := s) (clock := clock) (Index := Index)
      (G := G) hs hsurj)
      (hbridge hfield)

/-- A global product-bound-only bridge to the clocked payload is impossible
whenever any exact-visible family in its scope is fully expressive below the
Boolean predictor-space threshold. -/
theorem not_productBoundOnlyClockedKpolyFiniteLearningBridge_of_true_productBound_of_surjective_predict_of_lt_predictorCard
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s clock : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index)
    (hprod : V13FieldedProductBoundFrom Ω hist items)
    (hsurj : Function.Surjective G.predict)
    (hs : 2 ^ s < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ProductBoundOnlyClockedKpolyFiniteLearningBridge
        Ω Z k s clock hist items := by
  intro hbridge
  exact
    (not_clockedKpolyFiniteLearningPayload_of_surjective_predict_of_lt_predictorCard
      (Z := Z) (k := k) (s := s) (clock := clock) (Index := Index)
      (G := G) hs hsurj)
      (hbridge G hprod)

/-- A global fielded-switching-only bridge to the clocked payload is impossible
whenever any exact-visible family in its scope is fully expressive below the
Boolean predictor-space threshold. -/
theorem not_fieldedSwitchingOnlyClockedKpolyFiniteLearningBridge_of_true_fieldedSwitching_of_surjective_predict_of_lt_predictorCard
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s clock : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index)
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hsurj : Function.Surjective G.predict)
    (hs : 2 ^ s < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ FieldedSwitchingOnlyClockedKpolyFiniteLearningBridge
        Ω Z k s clock hist items := by
  intro hbridge
  exact
    (not_clockedKpolyFiniteLearningPayload_of_surjective_predict_of_lt_predictorCard
      (Z := Z) (k := k) (s := s) (clock := clock) (Index := Index)
      (G := G) hs hsurj)
      (hbridge G hfield)

/-- The empty product-bound instance also cannot imply the clocked payload
below the exact-visible surface threshold. -/
theorem not_productBoundOnlyClockedKpolyFiniteLearningBridge_nil_of_lt_surfaceCard
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s clock : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ProductBoundOnlyClockedKpolyFiniteLearningBridge
        Ω Z k s clock
        ([] : List (FiniteEvent Ω)) ([] : List (V13FieldedStep Ω)) := by
  intro hbridge
  exact
    (not_productBoundOnlyExactVisibleCompressionBridge_nil_of_lt_surfaceCard
      (Ω := Ω) (Z := Z) (k := k) (s := s) hs)
      (productBoundOnlyExactVisibleCompressionBridge_of_clockedKpolyFiniteLearningBridge
        (Ω := Ω) (Z := Z) (k := k) (s := s) (clock := clock)
        hbridge)

/-- The empty fielded-switching instance also cannot imply the clocked payload
below the exact-visible surface threshold. -/
theorem not_fieldedSwitchingOnlyClockedKpolyFiniteLearningBridge_nil_of_lt_surfaceCard
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s clock : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ FieldedSwitchingOnlyClockedKpolyFiniteLearningBridge
        Ω Z k s clock
        ([] : List (FiniteEvent Ω)) ([] : List (V13FieldedStep Ω)) := by
  intro hbridge
  exact
    (not_fieldedSwitchingOnlyExactVisibleCompressionBridge_nil_of_lt_surfaceCard
      (Ω := Ω) (Z := Z) (k := k) (s := s) hs)
      (fieldedSwitchingOnlyExactVisibleCompressionBridge_of_clockedKpolyFiniteLearningBridge
        (Ω := Ω) (Z := Z) (k := k) (s := s) (clock := clock)
        hbridge)

/-- The nontrivial Boolean-square one-step product-bound instance cannot imply
the clocked payload below the exact-visible surface threshold. -/
theorem not_productBoundOnlyClockedKpolyFiniteLearningBridge_boolPair_one_step_of_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k s clock : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ProductBoundOnlyClockedKpolyFiniteLearningBridge
        (Bool × Bool) Z k s clock
        ([] : List (FiniteEvent (Bool × Bool)))
        [v13BoolPairUnitFieldedStep] := by
  intro hbridge
  exact
    (not_productBoundOnlyExactVisibleCompressionBridge_boolPair_one_step_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) hs)
      (productBoundOnlyExactVisibleCompressionBridge_of_clockedKpolyFiniteLearningBridge
        (Ω := Bool × Bool) (Z := Z) (k := k) (s := s) (clock := clock)
        hbridge)

/-- The nontrivial Boolean-square one-step fielded-switching instance cannot
imply the clocked payload below the exact-visible surface threshold. -/
theorem not_fieldedSwitchingOnlyClockedKpolyFiniteLearningBridge_boolPair_one_step_of_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k s clock : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ FieldedSwitchingOnlyClockedKpolyFiniteLearningBridge
        (Bool × Bool) Z k s clock
        ([] : List (FiniteEvent (Bool × Bool)))
        [v13BoolPairUnitFieldedStep] := by
  intro hbridge
  exact
    (not_fieldedSwitchingOnlyExactVisibleCompressionBridge_boolPair_one_step_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) hs)
      (fieldedSwitchingOnlyExactVisibleCompressionBridge_of_clockedKpolyFiniteLearningBridge
        (Ω := Bool × Bool) (Z := Z) (k := k) (s := s) (clock := clock)
        hbridge)

end Mettapedia.Computability.PNP
