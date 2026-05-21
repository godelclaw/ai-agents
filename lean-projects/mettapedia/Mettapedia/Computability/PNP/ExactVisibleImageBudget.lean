import Mettapedia.Computability.PNP.ClockedKpolyBridgeEquivalence

/-!
# PNP `Kpoly` bridge: bit budgets are finite predictor-image covers

The clocked `Kpoly` bridge has already been reduced to
`ExactVisibleCompressionTarget`, i.e. to an exact `s`-bit budget for the indexed
visible predictor family.  This file makes the remaining mathematical content
even more explicit: an `s`-bit budget is exactly a finite cover of the predictor
image by at most `2^s` Boolean functions.

This is intentionally not a broad `Kpoly` closure theorem.  It is a foundation
result saying that any proposed bridge must prove a finite predictor-image bound
for the actual switched family.
-/

namespace Mettapedia.Computability.PNP

universe u v w

namespace IndexedPredictorFamily

variable {Index : Type u} {Input : Type v}

/-- A finite family of Boolean predictors covering every predictor selected by
an indexed family.  The numeric parameter is the allowed cover size, not a bit
length. -/
def FinitePredictorCover
    (G : IndexedPredictorFamily Index Input) (N : ℕ) : Prop :=
  ∃ S : Finset (Input → Bool), (∀ i, G.predict i ∈ S) ∧ S.card ≤ N

/-- A finite set of representative indices whose selected predictors cover the
whole predictor image.  This avoids assuming `DecidableEq Index`; the
representatives are carried by an arbitrary finite type. -/
def FiniteIndexRepresentativeCover
    (G : IndexedPredictorFamily Index Input) (N : ℕ) : Prop :=
  ∃ Rep : Type (max u v), ∃ _ : Fintype Rep, ∃ select : Rep → Index,
    (∀ i, ∃ r : Rep, G.predict (select r) = G.predict i) ∧
      Fintype.card Rep ≤ N

/-- A finite quotient-code presentation of the predictor image.  Each index is
encoded into a finite code type, and the decoder assigned to that code is
exactly the predictor selected by the index. -/
def FinitePredictorQuotient
    (G : IndexedPredictorFamily Index Input) (N : ℕ) : Prop :=
  ∃ Code : Type (max u v), ∃ _ : Fintype Code, ∃ encode : Index → Code,
    ∃ decode : Code → Input → Bool,
      (∀ i, decode (encode i) = G.predict i) ∧ Fintype.card Code ≤ N

/-- Any exact `s`-bit budget covers the predictor image by at most `2^s`
functions. -/
theorem finitePredictorCover_of_hasBitBudget
    {G : IndexedPredictorFamily Index Input} {s : ℕ}
    (hsmall : G.HasBitBudget s) :
    G.FinitePredictorCover (2 ^ s) := by
  classical
  rcases hsmall with ⟨F, hF⟩
  refine ⟨Finset.univ.image F.decode, ?_, ?_⟩
  · intro i
    rcases hF i with ⟨c, hc⟩
    rw [← hc]
    exact Finset.mem_image.mpr ⟨c, Finset.mem_univ c, rfl⟩
  · exact le_trans Finset.card_image_le (by simp)

/-- A finite predictor-image cover of size at most `2^s` can be encoded by
`s` bits. -/
theorem hasBitBudget_of_finitePredictorCover
    {G : IndexedPredictorFamily Index Input} {s : ℕ}
    (hcover : G.FinitePredictorCover (2 ^ s)) :
    G.HasBitBudget s := by
  classical
  rcases hcover with ⟨S, hmem, hcard⟩
  have hcardCode : 2 ^ s = Fintype.card (BitCode s) := by
    simp
  let Cover := {f : Input → Bool // f ∈ S}
  have hcoverCard : Fintype.card Cover = S.card := by
    simp [Cover]
  let toFin : Cover → Fin (2 ^ s) :=
    fun f => Fin.castLE hcard (Fin.cast hcoverCard ((Fintype.equivFin Cover) f))
  let toCode : Cover → BitCode s :=
    fun f =>
      (Fintype.equivFin (BitCode s)).symm (Fin.cast hcardCode (toFin f))
  have htoCode_inj : Function.Injective toCode := by
    intro x y hxy
    have hfinCast :
        Fin.cast hcardCode (toFin x) = Fin.cast hcardCode (toFin y) :=
      (Fintype.equivFin (BitCode s)).symm.injective hxy
    have hfin : toFin x = toFin y :=
      Fin.cast_injective hcardCode hfinCast
    have hequiv :
        (Fintype.equivFin Cover) x = (Fintype.equivFin Cover) y := by
      have hcast :
          Fin.cast hcoverCard ((Fintype.equivFin Cover) x) =
            Fin.cast hcoverCard ((Fintype.equivFin Cover) y) :=
        Fin.castLE_injective hcard hfin
      exact Fin.cast_injective hcoverCard hcast
    exact (Fintype.equivFin Cover).injective hequiv
  refine
    ⟨{ decode := fun c =>
          if h : ∃ f : Cover, toCode f = c then
            (Classical.choose h).1
          else
            fun _ => false },
      ?_⟩
  intro i
  let f : Cover := ⟨G.predict i, hmem i⟩
  refine ⟨toCode f, ?_⟩
  let hex : ∃ g : Cover, toCode g = toCode f := ⟨f, rfl⟩
  have hchoose : Classical.choose hex = f :=
    htoCode_inj (Classical.choose_spec hex)
  change
    (if h : ∃ g : Cover, toCode g = toCode f then
        (Classical.choose h).1
      else
        fun _ => false) = G.predict i
  rw [dif_pos hex]
  simp [f, hchoose]

/-- Exact bit budgets are exactly finite predictor-image covers of size at most
`2^s`. -/
theorem hasBitBudget_iff_finitePredictorCover
    {G : IndexedPredictorFamily Index Input} {s : ℕ} :
    G.HasBitBudget s ↔ G.FinitePredictorCover (2 ^ s) :=
  ⟨finitePredictorCover_of_hasBitBudget, hasBitBudget_of_finitePredictorCover⟩

/-- Finite predictor-image covers are monotone in the allowed cover size. -/
theorem finitePredictorCover_mono
    {G : IndexedPredictorFamily Index Input} {N M : ℕ}
    (hNM : N ≤ M) (hcover : G.FinitePredictorCover N) :
    G.FinitePredictorCover M := by
  rcases hcover with ⟨S, hmem, hcard⟩
  exact ⟨S, hmem, le_trans hcard hNM⟩

/-- A cover for a factored summary family pulls back to a cover for the
original indexed family. -/
theorem finitePredictorCover_of_factorsThrough
    {View : Type w} {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View} {view : Input → View} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hcover : H.FinitePredictorCover N) :
    G.FinitePredictorCover N := by
  classical
  rcases hcover with ⟨S, hmem, hcard⟩
  refine ⟨S.image (fun f : View → Bool => fun x : Input => f (view x)), ?_, ?_⟩
  · intro i
    have hpull : (fun x : Input => H.predict i (view x)) = G.predict i := by
      funext x
      exact (hfactor i x).symm
    have hmemImage :
        (fun x : Input => H.predict i (view x)) ∈
          S.image (fun f : View → Bool => fun x : Input => f (view x)) :=
      Finset.mem_image.mpr ⟨H.predict i, hmem i, rfl⟩
    simpa [hpull] using
      hmemImage
  · exact le_trans Finset.card_image_le hcard

/-- If a factor map has a section, a cover of the pulled-back family pushes
back to a cover of the summary family. -/
theorem finitePredictorCover_of_factorsThrough_of_rightInverse
    {View : Type w} {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View} {view : Input → View}
    {sec : View → Input} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hcover : G.FinitePredictorCover N) :
    H.FinitePredictorCover N := by
  classical
  rcases hcover with ⟨S, hmem, hcard⟩
  refine ⟨S.image (fun f : Input → Bool => fun y : View => f (sec y)), ?_, ?_⟩
  · intro i
    have hpush : (fun y : View => G.predict i (sec y)) = H.predict i := by
      funext y
      calc
        G.predict i (sec y) = H.predict i (view (sec y)) := hfactor i (sec y)
        _ = H.predict i y := by simp [hsection y]
    have hmemImage :
        (fun y : View => G.predict i (sec y)) ∈
          S.image (fun f : Input → Bool => fun y : View => f (sec y)) :=
      Finset.mem_image.mpr ⟨G.predict i, hmem i, rfl⟩
    simpa [hpush] using
      hmemImage
  · exact le_trans Finset.card_image_le hcard

/-- A finite representative-index cover induces a finite predictor-image cover. -/
theorem finitePredictorCover_of_finiteIndexRepresentativeCover
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (hrep : G.FiniteIndexRepresentativeCover N) :
    G.FinitePredictorCover N := by
  classical
  rcases hrep with ⟨Rep, hRep, select, hcover, hcard⟩
  letI := hRep
  refine ⟨Finset.univ.image (fun r : Rep => G.predict (select r)), ?_, ?_⟩
  · intro i
    rcases hcover i with ⟨r, hr⟩
    rw [← hr]
    exact Finset.mem_image.mpr ⟨r, Finset.mem_univ r, rfl⟩
  · exact le_trans Finset.card_image_le hcard

/-- A finite predictor-image cover can be represented by finitely many actual
indices from the family. -/
theorem finiteIndexRepresentativeCover_of_finitePredictorCover
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (hcover : G.FinitePredictorCover N) :
    G.FiniteIndexRepresentativeCover N := by
  classical
  rcases hcover with ⟨S, hmem, hcard⟩
  let Cover :=
    {f : {f : Input → Bool // f ∈ S} // ∃ i, G.predict i = (f.1 : Input → Bool)}
  have hcoverCard : Fintype.card Cover ≤ S.card := by
    have hinj : Function.Injective (fun f : Cover => f.1) := by
      intro f g hfg
      exact Subtype.ext hfg
    have hle :
        Fintype.card Cover ≤ Fintype.card {f : Input → Bool // f ∈ S} :=
      Fintype.card_le_of_injective (fun f : Cover => f.1) hinj
    simpa [Cover] using hle
  let Rep := ULift.{max u v, max 0 v} Cover
  refine ⟨Rep, inferInstance, (fun f : Rep => Classical.choose f.down.2), ?_, ?_⟩
  · intro i
    let f : Rep := ULift.up (⟨⟨G.predict i, hmem i⟩, ⟨i, rfl⟩⟩ : Cover)
    refine ⟨f, ?_⟩
    exact Classical.choose_spec f.down.2
  · exact le_trans (by simpa [Rep] using hcoverCard) hcard

/-- Finite predictor covers are exactly finite representative-index covers. -/
theorem finitePredictorCover_iff_finiteIndexRepresentativeCover
    {G : IndexedPredictorFamily Index Input} {N : ℕ} :
    G.FinitePredictorCover N ↔ G.FiniteIndexRepresentativeCover N :=
  ⟨finiteIndexRepresentativeCover_of_finitePredictorCover,
    finitePredictorCover_of_finiteIndexRepresentativeCover⟩

/-- A finite quotient-code presentation induces a finite predictor-image cover. -/
theorem finitePredictorCover_of_finitePredictorQuotient
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (hquot : G.FinitePredictorQuotient N) :
    G.FinitePredictorCover N := by
  classical
  rcases hquot with ⟨Code, hCode, encode, decode, hreal, hcard⟩
  letI := hCode
  refine ⟨Finset.univ.image decode, ?_, ?_⟩
  · intro i
    rw [← hreal i]
    exact Finset.mem_image.mpr ⟨encode i, Finset.mem_univ (encode i), rfl⟩
  · exact le_trans Finset.card_image_le hcard

/-- A finite representative-index cover gives a quotient-code presentation by
using representatives as codes. -/
theorem finitePredictorQuotient_of_finiteIndexRepresentativeCover
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (hrep : G.FiniteIndexRepresentativeCover N) :
    G.FinitePredictorQuotient N := by
  classical
  rcases hrep with ⟨Rep, hRep, select, hcover, hcard⟩
  refine
    ⟨Rep, hRep, (fun i => Classical.choose (hcover i)),
      (fun r => G.predict (select r)), ?_, hcard⟩
  intro i
  exact Classical.choose_spec (hcover i)

/-- A finite predictor-image cover can be repackaged as a finite quotient-code
presentation. -/
theorem finitePredictorQuotient_of_finitePredictorCover
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (hcover : G.FinitePredictorCover N) :
    G.FinitePredictorQuotient N :=
  finitePredictorQuotient_of_finiteIndexRepresentativeCover
    (finiteIndexRepresentativeCover_of_finitePredictorCover hcover)

/-- A finite quotient-code presentation can be represented by actual selected
indices. -/
theorem finiteIndexRepresentativeCover_of_finitePredictorQuotient
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (hquot : G.FinitePredictorQuotient N) :
    G.FiniteIndexRepresentativeCover N :=
  finiteIndexRepresentativeCover_of_finitePredictorCover
    (finitePredictorCover_of_finitePredictorQuotient hquot)

/-- Finite predictor-image covers are exactly finite quotient-code
presentations. -/
theorem finitePredictorCover_iff_finitePredictorQuotient
    {G : IndexedPredictorFamily Index Input} {N : ℕ} :
    G.FinitePredictorCover N ↔ G.FinitePredictorQuotient N :=
  ⟨finitePredictorQuotient_of_finitePredictorCover,
    finitePredictorCover_of_finitePredictorQuotient⟩

/-- Finite representative-index covers are exactly finite quotient-code
presentations. -/
theorem finiteIndexRepresentativeCover_iff_finitePredictorQuotient
    {G : IndexedPredictorFamily Index Input} {N : ℕ} :
    G.FiniteIndexRepresentativeCover N ↔ G.FinitePredictorQuotient N :=
  ⟨finitePredictorQuotient_of_finiteIndexRepresentativeCover,
    finiteIndexRepresentativeCover_of_finitePredictorQuotient⟩

/-- Finite representative-index covers are monotone in the allowed number of
representatives. -/
theorem finiteIndexRepresentativeCover_mono
    {G : IndexedPredictorFamily Index Input} {N M : ℕ}
    (hNM : N ≤ M) (hrep : G.FiniteIndexRepresentativeCover N) :
    G.FiniteIndexRepresentativeCover M := by
  rcases hrep with ⟨Rep, hRep, select, hcover, hcard⟩
  exact ⟨Rep, hRep, select, hcover, le_trans hcard hNM⟩

/-- A representative-index cover for a factored summary family pulls back to
the original indexed family. -/
theorem finiteIndexRepresentativeCover_of_factorsThrough
    {View : Type w} {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View} {view : Input → View} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hrep : H.FiniteIndexRepresentativeCover N) :
    G.FiniteIndexRepresentativeCover N := by
  exact finiteIndexRepresentativeCover_of_finitePredictorCover
    (finitePredictorCover_of_factorsThrough hfactor
      (finitePredictorCover_of_finiteIndexRepresentativeCover hrep))

/-- If a factor map has a section, a representative-index cover of the
pulled-back family pushes back to the summary family. -/
theorem finiteIndexRepresentativeCover_of_factorsThrough_of_rightInverse
    {View : Type w} {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View} {view : Input → View}
    {sec : View → Input} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hrep : G.FiniteIndexRepresentativeCover N) :
    H.FiniteIndexRepresentativeCover N := by
  exact finiteIndexRepresentativeCover_of_finitePredictorCover
    (finitePredictorCover_of_factorsThrough_of_rightInverse hfactor hsection
      (finitePredictorCover_of_finiteIndexRepresentativeCover hrep))

/-- Finite quotient-code presentations are monotone in the allowed code count. -/
theorem finitePredictorQuotient_mono
    {G : IndexedPredictorFamily Index Input} {N M : ℕ}
    (hNM : N ≤ M) (hquot : G.FinitePredictorQuotient N) :
    G.FinitePredictorQuotient M := by
  rcases hquot with ⟨Code, hCode, encode, decode, hreal, hcard⟩
  exact ⟨Code, hCode, encode, decode, hreal, le_trans hcard hNM⟩

/-- A quotient-code presentation for a factored summary family pulls back to
the original indexed family. -/
theorem finitePredictorQuotient_of_factorsThrough
    {View : Type w} {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View} {view : Input → View} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hquot : H.FinitePredictorQuotient N) :
    G.FinitePredictorQuotient N :=
  finitePredictorQuotient_of_finitePredictorCover
    (finitePredictorCover_of_factorsThrough hfactor
      (finitePredictorCover_of_finitePredictorQuotient hquot))

/-- If a factor map has a section, a quotient-code presentation of the pulled
back family pushes back to the summary family. -/
theorem finitePredictorQuotient_of_factorsThrough_of_rightInverse
    {View : Type w} {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View} {view : Input → View}
    {sec : View → Input} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hquot : G.FinitePredictorQuotient N) :
    H.FinitePredictorQuotient N :=
  finitePredictorQuotient_of_finitePredictorCover
    (finitePredictorCover_of_factorsThrough_of_rightInverse hfactor hsection
      (finitePredictorCover_of_finitePredictorQuotient hquot))

/-- Exact bit budgets are equivalently finite representative-index covers by
at most `2^s` selected indices. -/
theorem hasBitBudget_iff_finiteIndexRepresentativeCover
    {G : IndexedPredictorFamily Index Input} {s : ℕ} :
    G.HasBitBudget s ↔ G.FiniteIndexRepresentativeCover (2 ^ s) := by
  rw [hasBitBudget_iff_finitePredictorCover,
    finitePredictorCover_iff_finiteIndexRepresentativeCover]

/-- Exact bit budgets are equivalently finite quotient-code presentations by
at most `2^s` codes. -/
theorem hasBitBudget_iff_finitePredictorQuotient
    {G : IndexedPredictorFamily Index Input} {s : ℕ} :
    G.HasBitBudget s ↔ G.FinitePredictorQuotient (2 ^ s) := by
  rw [hasBitBudget_iff_finitePredictorCover,
    finitePredictorCover_iff_finitePredictorQuotient]

/-- If an indexed family realizes an injectively indexed finite probe family of
Boolean classifiers, then any finite predictor-image cover must contain at
least that many classifiers. -/
theorem finitePredictorCover_card_le_of_injective_realization
    {Probe : Type*} [Fintype Probe]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (target : Probe → Input → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hcover : G.FinitePredictorCover N) :
    Fintype.card Probe ≤ N := by
  classical
  rcases hcover with ⟨S, hmem, hcard⟩
  let toCover : Probe → {f : Input → Bool // f ∈ S} :=
    fun p =>
      ⟨target p, by
        rcases hreal p with ⟨i, hi⟩
        rw [← hi]
        exact hmem i⟩
  have htoCover : Function.Injective toCover := by
    intro p q hpq
    apply hinj
    exact congrArg Subtype.val hpq
  have hle :
      Fintype.card Probe ≤ Fintype.card {f : Input → Bool // f ∈ S} :=
    Fintype.card_le_of_injective toCover htoCover
  have hcoverCard : Fintype.card {f : Input → Bool // f ∈ S} = S.card := by
    simp
  have hsubtypeCard : Fintype.card {f : Input → Bool // f ∈ S} ≤ N := by
    simpa [hcoverCard] using hcard
  exact le_trans hle hsubtypeCard

/-- Negative form of the finite injective-realization lower bound for
predictor-image covers. -/
theorem not_finitePredictorCover_of_injective_realization_of_lt_card
    {Probe : Type*} [Fintype Probe]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (target : Probe → Input → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hN : N < Fintype.card Probe) :
    ¬ G.FinitePredictorCover N := by
  intro hcover
  exact Nat.not_le_of_lt hN
    (finitePredictorCover_card_le_of_injective_realization
      target hinj hreal hcover)

/-- A representative-index cover must contain at least every injectively
realized finite probe family. -/
theorem finiteIndexRepresentativeCover_card_le_of_injective_realization
    {Probe : Type*} [Fintype Probe]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (target : Probe → Input → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hrep : G.FiniteIndexRepresentativeCover N) :
    Fintype.card Probe ≤ N :=
  finitePredictorCover_card_le_of_injective_realization target hinj hreal
    (finitePredictorCover_of_finiteIndexRepresentativeCover hrep)

/-- Negative representative-index form of the finite injective-realization
lower bound. -/
theorem not_finiteIndexRepresentativeCover_of_injective_realization_of_lt_card
    {Probe : Type*} [Fintype Probe]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (target : Probe → Input → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hN : N < Fintype.card Probe) :
    ¬ G.FiniteIndexRepresentativeCover N := by
  intro hrep
  exact Nat.not_le_of_lt hN
    (finiteIndexRepresentativeCover_card_le_of_injective_realization
      target hinj hreal hrep)

/-- A finite quotient-code presentation must contain at least every injectively
realized finite probe family. -/
theorem finitePredictorQuotient_card_le_of_injective_realization
    {Probe : Type*} [Fintype Probe]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (target : Probe → Input → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hquot : G.FinitePredictorQuotient N) :
    Fintype.card Probe ≤ N :=
  finitePredictorCover_card_le_of_injective_realization target hinj hreal
    (finitePredictorCover_of_finitePredictorQuotient hquot)

/-- Negative quotient-code form of the finite injective-realization lower
bound. -/
theorem not_finitePredictorQuotient_of_injective_realization_of_lt_card
    {Probe : Type*} [Fintype Probe]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (target : Probe → Input → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hN : N < Fintype.card Probe) :
    ¬ G.FinitePredictorQuotient N := by
  intro hquot
  exact Nat.not_le_of_lt hN
    (finitePredictorQuotient_card_le_of_injective_realization
      target hinj hreal hquot)

/-- If an indexed family already realizes every Boolean classifier on a finite
input type, then any finite predictor-image cover must contain at least the
full Boolean classifier space. -/
theorem finitePredictorCover_card_le_of_surjective_predict
    [Fintype Input]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (hsurj : Function.Surjective G.predict)
    (hcover : G.FinitePredictorCover N) :
    2 ^ Fintype.card Input ≤ N := by
  classical
  rcases hcover with ⟨S, hmem, hcard⟩
  have hsub : (Finset.univ : Finset (Input → Bool)) ⊆ S := by
    intro f _
    rcases hsurj f with ⟨i, hi⟩
    rw [← hi]
    exact hmem i
  have hclassifierCard : Fintype.card (Input → Bool) ≤ S.card := by
    simpa using Finset.card_le_card hsub
  have hspace : Fintype.card (Input → Bool) = 2 ^ Fintype.card Input :=
    card_boolClassifierSpace Input
  simpa [hspace] using le_trans hclassifierCard hcard

/-- A fully expressive indexed family has no finite predictor-image cover below
the full Boolean classifier-space cardinality. -/
theorem not_finitePredictorCover_of_surjective_predict
    [Fintype Input]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (hN : N < 2 ^ Fintype.card Input)
    (hsurj : Function.Surjective G.predict) :
    ¬ G.FinitePredictorCover N := by
  intro hcover
  exact Nat.not_le_of_lt hN
    (finitePredictorCover_card_le_of_surjective_predict hsurj hcover)

/-- If `G` factors through a finite summary family `H`, the view has a section,
and `H` is still surjective onto all Boolean classifiers on that summary, then
any finite predictor-image cover of `G` must be at least the full Boolean
classifier-space cardinality of the summary. -/
theorem finitePredictorCover_card_le_of_factorsThrough_of_rightInverse_of_surjective_predict
    {View : Type w} [Fintype View]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hsurj : Function.Surjective H.predict)
    (hcover : G.FinitePredictorCover N) :
    2 ^ Fintype.card View ≤ N := by
  exact
    finitePredictorCover_card_le_of_surjective_predict
      (G := H) hsurj
      (finitePredictorCover_of_factorsThrough_of_rightInverse
        hfactor hsection hcover)

/-- Negative form of the section-backed reduced-view finite-image obstruction. -/
theorem not_finitePredictorCover_of_factorsThrough_of_rightInverse_of_surjective_predict
    {View : Type w} [Fintype View]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (hN : N < 2 ^ Fintype.card View)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hsurj : Function.Surjective H.predict) :
    ¬ G.FinitePredictorCover N := by
  intro hcover
  exact Nat.not_le_of_lt hN
    (finitePredictorCover_card_le_of_factorsThrough_of_rightInverse_of_surjective_predict
      hfactor hsection hsurj hcover)

/-- If `G` factors through a summary family `H`, the view has a section, and
`H` already realizes an injectively indexed finite probe family, then any finite
predictor-image cover of `G` must be at least the probe cardinality. -/
theorem finitePredictorCover_card_le_of_factorsThrough_of_rightInverse_of_injective_realization
    {Probe : Type*} [Fintype Probe] {View : Type w}
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (target : Probe → View → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hcover : G.FinitePredictorCover N) :
    Fintype.card Probe ≤ N :=
  finitePredictorCover_card_le_of_injective_realization target hinj hreal
    (finitePredictorCover_of_factorsThrough_of_rightInverse
      hfactor hsection hcover)

/-- Negative form of the section-backed finite-probe lower bound. -/
theorem not_finitePredictorCover_of_factorsThrough_of_rightInverse_of_injective_realization_of_lt_card
    {Probe : Type*} [Fintype Probe] {View : Type w}
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
  intro hcover
  exact Nat.not_le_of_lt hN
    (finitePredictorCover_card_le_of_factorsThrough_of_rightInverse_of_injective_realization
      target hinj hreal hfactor hsection hcover)

/-- The same reduced-view lower bound for representative-index covers. -/
theorem finiteIndexRepresentativeCover_card_le_of_factorsThrough_of_rightInverse_of_surjective_predict
    {View : Type w} [Fintype View]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hsurj : Function.Surjective H.predict)
    (hrep : G.FiniteIndexRepresentativeCover N) :
    2 ^ Fintype.card View ≤ N := by
  exact
    finitePredictorCover_card_le_of_factorsThrough_of_rightInverse_of_surjective_predict
      hfactor hsection hsurj
      (finitePredictorCover_of_finiteIndexRepresentativeCover hrep)

/-- Negative representative-index form of the section-backed reduced-view
finite-image obstruction. -/
theorem not_finiteIndexRepresentativeCover_of_factorsThrough_of_rightInverse_of_surjective_predict
    {View : Type w} [Fintype View]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (hN : N < 2 ^ Fintype.card View)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hsurj : Function.Surjective H.predict) :
    ¬ G.FiniteIndexRepresentativeCover N := by
  intro hrep
  exact Nat.not_le_of_lt hN
    (finiteIndexRepresentativeCover_card_le_of_factorsThrough_of_rightInverse_of_surjective_predict
      hfactor hsection hsurj hrep)

/-- Representative-index covers inherit the same section-backed finite-probe
lower bound. -/
theorem finiteIndexRepresentativeCover_card_le_of_factorsThrough_of_rightInverse_of_injective_realization
    {Probe : Type*} [Fintype Probe] {View : Type w}
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (target : Probe → View → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hrep : G.FiniteIndexRepresentativeCover N) :
    Fintype.card Probe ≤ N :=
  finitePredictorCover_card_le_of_factorsThrough_of_rightInverse_of_injective_realization
    target hinj hreal hfactor hsection
    (finitePredictorCover_of_finiteIndexRepresentativeCover hrep)

/-- Negative representative-index form of the section-backed finite-probe lower
bound. -/
theorem not_finiteIndexRepresentativeCover_of_factorsThrough_of_rightInverse_of_injective_realization_of_lt_card
    {Probe : Type*} [Fintype Probe] {View : Type w}
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
  intro hrep
  exact Nat.not_le_of_lt hN
    (finiteIndexRepresentativeCover_card_le_of_factorsThrough_of_rightInverse_of_injective_realization
      target hinj hreal hfactor hsection hrep)

/-- A fully expressive indexed family forces every finite quotient-code
presentation to have at least the full Boolean classifier-space cardinality. -/
theorem finitePredictorQuotient_card_le_of_surjective_predict
    [Fintype Input]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (hsurj : Function.Surjective G.predict)
    (hquot : G.FinitePredictorQuotient N) :
    2 ^ Fintype.card Input ≤ N :=
  finitePredictorCover_card_le_of_surjective_predict hsurj
    (finitePredictorCover_of_finitePredictorQuotient hquot)

/-- Fully expressive indexed families have no finite quotient-code
presentation below the full Boolean classifier-space cardinality. -/
theorem not_finitePredictorQuotient_of_surjective_predict
    [Fintype Input]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (hN : N < 2 ^ Fintype.card Input)
    (hsurj : Function.Surjective G.predict) :
    ¬ G.FinitePredictorQuotient N := by
  intro hquot
  exact Nat.not_le_of_lt hN
    (finitePredictorQuotient_card_le_of_surjective_predict hsurj hquot)

/-- Section-backed reduced-view lower bound for finite quotient-code
presentations. -/
theorem finitePredictorQuotient_card_le_of_factorsThrough_of_rightInverse_of_surjective_predict
    {View : Type w} [Fintype View]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hsurj : Function.Surjective H.predict)
    (hquot : G.FinitePredictorQuotient N) :
    2 ^ Fintype.card View ≤ N :=
  finitePredictorCover_card_le_of_factorsThrough_of_rightInverse_of_surjective_predict
    hfactor hsection hsurj
    (finitePredictorCover_of_finitePredictorQuotient hquot)

/-- Negative quotient-code form of the section-backed reduced-view finite-image
obstruction. -/
theorem not_finitePredictorQuotient_of_factorsThrough_of_rightInverse_of_surjective_predict
    {View : Type w} [Fintype View]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (hN : N < 2 ^ Fintype.card View)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hsurj : Function.Surjective H.predict) :
    ¬ G.FinitePredictorQuotient N := by
  intro hquot
  exact Nat.not_le_of_lt hN
    (finitePredictorQuotient_card_le_of_factorsThrough_of_rightInverse_of_surjective_predict
      hfactor hsection hsurj hquot)

/-- Quotient-code presentations inherit the same section-backed finite-probe
lower bound. -/
theorem finitePredictorQuotient_card_le_of_factorsThrough_of_rightInverse_of_injective_realization
    {Probe : Type*} [Fintype Probe] {View : Type w}
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (target : Probe → View → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hquot : G.FinitePredictorQuotient N) :
    Fintype.card Probe ≤ N :=
  finitePredictorCover_card_le_of_factorsThrough_of_rightInverse_of_injective_realization
    target hinj hreal hfactor hsection
    (finitePredictorCover_of_finitePredictorQuotient hquot)

/-- Negative quotient-code form of the section-backed finite-probe lower
bound. -/
theorem not_finitePredictorQuotient_of_factorsThrough_of_rightInverse_of_injective_realization_of_lt_card
    {Probe : Type*} [Fintype Probe] {View : Type w}
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
  intro hquot
  exact Nat.not_le_of_lt hN
    (finitePredictorQuotient_card_le_of_factorsThrough_of_rightInverse_of_injective_realization
      target hinj hreal hfactor hsection hquot)

end IndexedPredictorFamily

section ExactVisible

variable {Z : Type*} {k s clock : ℕ} {Index : Type*}

/-- Exact visible compression is just a finite predictor-image cover with
`2^s` allowed predictors. -/
theorem exactVisibleCompressionTarget_iff_finitePredictorCover
    {G : ExactVisibleSwitchedFamily Z k Index} :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s ↔
      G.FinitePredictorCover (2 ^ s) := by
  exact IndexedPredictorFamily.hasBitBudget_iff_finitePredictorCover

/-- Exact visible compression is equivalently represented by at most `2^s`
actual indices from the family. -/
theorem exactVisibleCompressionTarget_iff_finiteIndexRepresentativeCover
    {G : ExactVisibleSwitchedFamily Z k Index} :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s ↔
      G.FiniteIndexRepresentativeCover (2 ^ s) := by
  exact IndexedPredictorFamily.hasBitBudget_iff_finiteIndexRepresentativeCover

/-- Exact visible compression is equivalently represented by a finite
quotient-code presentation of size at most `2^s`. -/
theorem exactVisibleCompressionTarget_iff_finitePredictorQuotient
    {G : ExactVisibleSwitchedFamily Z k Index} :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s ↔
      G.FinitePredictorQuotient (2 ^ s) := by
  exact IndexedPredictorFamily.hasBitBudget_iff_finitePredictorQuotient

/-- The clocked exact-visible realization interface has the same predictor-image
content. -/
theorem exists_clockedExactVisibleRealization_iff_finitePredictorCover
    {G : ExactVisibleSwitchedFamily Z k Index} :
    (∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F) ↔
      G.FinitePredictorCover (2 ^ s) := by
  rw [exists_clockedExactVisibleRealization_iff_exactVisibleCompressionTarget,
    exactVisibleCompressionTarget_iff_finitePredictorCover]

/-- The clocked exact-visible realization interface is equivalently represented
by at most `2^s` actual selected indices. -/
theorem exists_clockedExactVisibleRealization_iff_finiteIndexRepresentativeCover
    {G : ExactVisibleSwitchedFamily Z k Index} :
    (∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F) ↔
      G.FiniteIndexRepresentativeCover (2 ^ s) := by
  rw [exists_clockedExactVisibleRealization_iff_exactVisibleCompressionTarget,
    exactVisibleCompressionTarget_iff_finiteIndexRepresentativeCover]

/-- The clocked exact-visible realization interface is equivalently a finite
quotient-code presentation with at most `2^s` codes. -/
theorem exists_clockedExactVisibleRealization_iff_finitePredictorQuotient
    {G : ExactVisibleSwitchedFamily Z k Index} :
    (∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F) ↔
      G.FinitePredictorQuotient (2 ^ s) := by
  rw [exists_clockedExactVisibleRealization_iff_exactVisibleCompressionTarget,
    exactVisibleCompressionTarget_iff_finitePredictorQuotient]

/-- Negative form of the predictor-image characterization for clocked
exact-visible realization. -/
theorem not_exists_clockedExactVisibleRealization_iff_not_finitePredictorCover
    {G : ExactVisibleSwitchedFamily Z k Index} :
    (¬ ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F) ↔
      ¬ G.FinitePredictorCover (2 ^ s) := by
  rw [exists_clockedExactVisibleRealization_iff_finitePredictorCover]

/-- Negative form of the representative-index characterization for clocked
exact-visible realization. -/
theorem not_exists_clockedExactVisibleRealization_iff_not_finiteIndexRepresentativeCover
    {G : ExactVisibleSwitchedFamily Z k Index} :
    (¬ ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F) ↔
      ¬ G.FiniteIndexRepresentativeCover (2 ^ s) := by
  rw [exists_clockedExactVisibleRealization_iff_finiteIndexRepresentativeCover]

/-- Negative form of the quotient-code characterization for clocked
exact-visible realization. -/
theorem not_exists_clockedExactVisibleRealization_iff_not_finitePredictorQuotient
    {G : ExactVisibleSwitchedFamily Z k Index} :
    (¬ ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F) ↔
      ¬ G.FinitePredictorQuotient (2 ^ s) := by
  rw [exists_clockedExactVisibleRealization_iff_finitePredictorQuotient]

/-- Exact visible finite-image covers must contain every injectively realized
finite probe family of exact-surface classifiers. -/
theorem exactVisible_finitePredictorCover_card_le_of_injective_realization
    {Probe : Type*} [Fintype Probe]
    {G : ExactVisibleSwitchedFamily Z k Index} {N : ℕ}
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hcover : G.FinitePredictorCover N) :
    Fintype.card Probe ≤ N :=
  IndexedPredictorFamily.finitePredictorCover_card_le_of_injective_realization
    target hinj hreal hcover

/-- Exact visible representative-index covers must contain every injectively
realized finite probe family of exact-surface classifiers. -/
theorem exactVisible_finiteIndexRepresentativeCover_card_le_of_injective_realization
    {Probe : Type*} [Fintype Probe]
    {G : ExactVisibleSwitchedFamily Z k Index} {N : ℕ}
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hrep : G.FiniteIndexRepresentativeCover N) :
    Fintype.card Probe ≤ N :=
  IndexedPredictorFamily.finiteIndexRepresentativeCover_card_le_of_injective_realization
    target hinj hreal hrep

/-- Exact visible quotient-code presentations must contain every injectively
realized finite probe family of exact-surface classifiers. -/
theorem exactVisible_finitePredictorQuotient_card_le_of_injective_realization
    {Probe : Type*} [Fintype Probe]
    {G : ExactVisibleSwitchedFamily Z k Index} {N : ℕ}
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hquot : G.FinitePredictorQuotient N) :
    Fintype.card Probe ≤ N :=
  IndexedPredictorFamily.finitePredictorQuotient_card_le_of_injective_realization
    target hinj hreal hquot

/-- Negative exact-visible cover form of the injective finite-probe lower
bound. -/
theorem not_exactVisible_finitePredictorCover_of_injective_realization_of_lt_card
    {Probe : Type*} [Fintype Probe]
    {G : ExactVisibleSwitchedFamily Z k Index} {N : ℕ}
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hN : N < Fintype.card Probe) :
    ¬ G.FinitePredictorCover N :=
  IndexedPredictorFamily.not_finitePredictorCover_of_injective_realization_of_lt_card
    target hinj hreal hN

/-- Negative exact-visible representative-index form of the injective finite
probe lower bound. -/
theorem not_exactVisible_finiteIndexRepresentativeCover_of_injective_realization_of_lt_card
    {Probe : Type*} [Fintype Probe]
    {G : ExactVisibleSwitchedFamily Z k Index} {N : ℕ}
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hN : N < Fintype.card Probe) :
    ¬ G.FiniteIndexRepresentativeCover N :=
  IndexedPredictorFamily.not_finiteIndexRepresentativeCover_of_injective_realization_of_lt_card
    target hinj hreal hN

/-- Negative exact-visible quotient-code form of the injective finite-probe
lower bound. -/
theorem not_exactVisible_finitePredictorQuotient_of_injective_realization_of_lt_card
    {Probe : Type*} [Fintype Probe]
    {G : ExactVisibleSwitchedFamily Z k Index} {N : ℕ}
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hN : N < Fintype.card Probe) :
    ¬ G.FinitePredictorQuotient N :=
  IndexedPredictorFamily.not_finitePredictorQuotient_of_injective_realization_of_lt_card
    target hinj hreal hN

/-- Exact visible compression is impossible below the size of any injectively
realized finite probe family. -/
theorem not_exactVisibleCompressionTarget_of_injective_realization_of_lt_card
    {Probe : Type*} [Fintype Probe]
    {G : ExactVisibleSwitchedFamily Z k Index}
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hs : 2 ^ s < Fintype.card Probe) :
    ¬ ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s := by
  rw [exactVisibleCompressionTarget_iff_finitePredictorCover]
  exact
    not_exactVisible_finitePredictorCover_of_injective_realization_of_lt_card
      target hinj hreal hs

/-- Clocked exact-visible realization is impossible below the size of any
injectively realized finite probe family. -/
theorem not_exists_clockedExactVisibleRealization_of_injective_realization_of_lt_card
    {Probe : Type*} [Fintype Probe]
    {G : ExactVisibleSwitchedFamily Z k Index}
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hs : 2 ^ s < Fintype.card Probe) :
    ¬ ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F := by
  rw [exists_clockedExactVisibleRealization_iff_finitePredictorCover]
  exact
    not_exactVisible_finitePredictorCover_of_injective_realization_of_lt_card
      target hinj hreal hs

/-- If an exact visible family already realizes every Boolean rule on the exact
post-switch surface, then any finite predictor-image cover must be at least the
full Boolean classifier-space cardinality. -/
theorem exactVisible_finitePredictorCover_card_le_of_surjective_predict
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index} {N : ℕ}
    (hsurj : Function.Surjective G.predict)
    (hcover : G.FinitePredictorCover N) :
    2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ N := by
  exact
    IndexedPredictorFamily.finitePredictorCover_card_le_of_surjective_predict
      (G := G) hsurj hcover

/-- If an exact visible family already realizes every Boolean rule on the exact
post-switch surface, then any finite representative-index cover must be at
least the full Boolean classifier-space cardinality. -/
theorem exactVisible_finiteIndexRepresentativeCover_card_le_of_surjective_predict
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index} {N : ℕ}
    (hsurj : Function.Surjective G.predict)
    (hrep : G.FiniteIndexRepresentativeCover N) :
    2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ N := by
  exact
    IndexedPredictorFamily.finiteIndexRepresentativeCover_card_le_of_factorsThrough_of_rightInverse_of_surjective_predict
      (G := G) (H := G) (view := id) (sec := id)
      (by intro i x; rfl)
      (by intro x; rfl)
      hsurj hrep

/-- If an exact visible family already realizes every Boolean rule on the exact
post-switch surface, then any finite quotient-code presentation must be at
least the full Boolean classifier-space cardinality. -/
theorem exactVisible_finitePredictorQuotient_card_le_of_surjective_predict
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index} {N : ℕ}
    (hsurj : Function.Surjective G.predict)
    (hquot : G.FinitePredictorQuotient N) :
    2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ N := by
  exact
    IndexedPredictorFamily.finitePredictorQuotient_card_le_of_surjective_predict
      (G := G) hsurj hquot

/-- Fully expressive exact visible families have no finite predictor-image cover
below the full exact visible Boolean classifier-space cardinality. -/
theorem not_exactVisible_finitePredictorCover_of_surjective_predict
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index} {N : ℕ}
    (hN : N < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k))
    (hsurj : Function.Surjective G.predict) :
    ¬ G.FinitePredictorCover N := by
  exact
    IndexedPredictorFamily.not_finitePredictorCover_of_surjective_predict
      (G := G) hN hsurj

/-- Fully expressive exact visible families have no finite representative-index
cover below the full exact visible Boolean classifier-space cardinality. -/
theorem not_exactVisible_finiteIndexRepresentativeCover_of_surjective_predict
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index} {N : ℕ}
    (hN : N < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k))
    (hsurj : Function.Surjective G.predict) :
    ¬ G.FiniteIndexRepresentativeCover N := by
  intro hrep
  exact Nat.not_le_of_lt hN
    (exactVisible_finiteIndexRepresentativeCover_card_le_of_surjective_predict
      hsurj hrep)

/-- Fully expressive exact visible families have no finite quotient-code
presentation below the full exact visible Boolean classifier-space cardinality. -/
theorem not_exactVisible_finitePredictorQuotient_of_surjective_predict
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index} {N : ℕ}
    (hN : N < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k))
    (hsurj : Function.Surjective G.predict) :
    ¬ G.FinitePredictorQuotient N := by
  intro hquot
  exact Nat.not_le_of_lt hN
    (exactVisible_finitePredictorQuotient_card_le_of_surjective_predict
      hsurj hquot)

/-- Image-cardinality form of the exact visible compression obstruction. -/
theorem not_exactVisibleCompressionTarget_of_surjective_predict_of_lt_predictorCard
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hs : 2 ^ s < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k))
    (hsurj : Function.Surjective G.predict) :
    ¬ ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s := by
  rw [exactVisibleCompressionTarget_iff_finitePredictorCover]
  exact not_exactVisible_finitePredictorCover_of_surjective_predict hs hsurj

/-- Image-cardinality form of the clocked exact-visible realization obstruction. -/
theorem not_exists_clockedExactVisibleRealization_of_surjective_predict_of_lt_predictorCard
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hs : 2 ^ s < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k))
    (hsurj : Function.Surjective G.predict) :
    ¬ ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F := by
  rw [exists_clockedExactVisibleRealization_iff_finitePredictorCover]
  exact not_exactVisible_finitePredictorCover_of_surjective_predict hs hsurj

end ExactVisible

end Mettapedia.Computability.PNP
