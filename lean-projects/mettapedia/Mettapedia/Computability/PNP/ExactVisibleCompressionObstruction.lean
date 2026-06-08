import Mettapedia.Computability.PNP.ExactSwitchedFamily

/-!
# P vs NP crux: exact post-switch compression still needs a real small-class theorem

Once the manuscript-visible post-switch surface has been isolated as the exact
input `u = (z, a, b)`, there is a sharper counting question:

* if the induced switched witness-bit family on that exact surface is still
  unconstrained enough to realize all Boolean rules on `u`,
* then no `s`-bit encoded family can cover it unless `s` is at least the full
  cardinality of the visible exact surface.

So the burden is now precise.  It is not enough to say "we compressed the exact
surface somehow."  One must prove that the actual switched family lands in a
strictly smaller subclass than the full Boolean function space on
`ExactVisiblePostSwitchSurface Z k`.
-/

namespace Mettapedia.Computability.PNP

section

variable {Z : Type*} {k s : ℕ}

/-- A Boolean rule on the exact manuscript-visible post-switch surface. -/
abbrev ExactVisibleRule (Z : Type*) (k : ℕ) := ExactVisiblePostSwitchSurface Z k → Bool

/-- The exact visible post-switch surface has cardinality
`|Z| * 2^k * 2^k = |Z| * 4^k`. -/
theorem card_exactVisiblePostSwitchSurface [Fintype Z] :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) =
      Fintype.card Z * 2 ^ k * 2 ^ k := by
  simpa [ForkPostSwitchSurface, InvariantPostSwitchSurface, BitVec] using
    Fintype.card_congr (forkVisibleEquiv (Z := Z) (k := k))

/-- Enumerate the exact visible post-switch surface by `Fin |surface|`. -/
noncomputable def exactVisibleInputEquivFin [Fintype Z] :
    ExactVisiblePostSwitchSurface Z k ≃
      Fin (Fintype.card (ExactVisiblePostSwitchSurface Z k)) :=
  Fintype.equivFin (ExactVisiblePostSwitchSurface Z k)

/-- Decode a full truth table on the exact visible surface. -/
noncomputable def exactVisibleRuleDecode [Fintype Z] :
    BitCode (Fintype.card (ExactVisiblePostSwitchSurface Z k)) → ExactVisibleRule Z k :=
  fun code u => code (exactVisibleInputEquivFin (Z := Z) (k := k) u)

/-- Encode an exact visible rule by its full truth table. -/
noncomputable def exactVisibleRuleEncode [Fintype Z] :
    ExactVisibleRule Z k → BitCode (Fintype.card (ExactVisiblePostSwitchSurface Z k)) :=
  fun rule i => rule ((exactVisibleInputEquivFin (Z := Z) (k := k)).symm i)

lemma exactVisibleRuleDecode_encode [Fintype Z] (rule : ExactVisibleRule Z k) :
    exactVisibleRuleDecode (Z := Z) (k := k)
      (exactVisibleRuleEncode (Z := Z) (k := k) rule) = rule := by
  funext u
  simp [exactVisibleRuleDecode, exactVisibleRuleEncode]

lemma exactVisibleRuleEncode_decode [Fintype Z]
    (code : BitCode (Fintype.card (ExactVisiblePostSwitchSurface Z k))) :
    exactVisibleRuleEncode (Z := Z) (k := k)
      (exactVisibleRuleDecode (Z := Z) (k := k) code) = code := by
  funext i
  simp [exactVisibleRuleDecode, exactVisibleRuleEncode]

/-- Exact visible rules are in bijection with full truth tables on the exact
visible surface. -/
noncomputable def exactVisibleRuleEquivBitCode [Fintype Z] :
    ExactVisibleRule Z k ≃ BitCode (Fintype.card (ExactVisiblePostSwitchSurface Z k)) where
  toFun := exactVisibleRuleEncode (Z := Z) (k := k)
  invFun := exactVisibleRuleDecode (Z := Z) (k := k)
  left_inv := exactVisibleRuleDecode_encode (Z := Z) (k := k)
  right_inv := exactVisibleRuleEncode_decode (Z := Z) (k := k)

/-- If `s` is below the full exact-surface cardinality, then `s`-bit codes
cannot injectively represent all exact visible rules. -/
theorem no_injective_bitCode_to_fullExactVisibleRule_of_lt
    [Fintype Z] (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ∃ f : ExactVisibleRule Z k → BitCode s, Function.Injective f := by
  classical
  simpa [ExactVisibleRule] using
    (no_injective_bitCode_of_lt_card
      (Input := ExactVisiblePostSwitchSurface Z k) (s := s) hs)

/-- Equivalently, no `s`-bit decoder can surject onto the full exact visible
rule class below the exact-surface cardinality threshold. -/
theorem not_surjective_decode_to_fullExactVisibleRule_of_lt
    [Fintype Z] (decode : BitCode s → ExactVisibleRule Z k)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective decode := by
  classical
  simpa [ExactVisibleRule] using
    (not_surjective_decode_to_fullClassifier_of_lt
      (Input := ExactVisiblePostSwitchSurface Z k) (decode := decode) hs)

end

section ExactFamily

variable {Z : Type*} {k s : ℕ} {Index : Type*}

/-- Every exact switched family admits the explicit truth-table bit budget given
by the full exact visible surface cardinality. -/
theorem exactVisibleCompressionTarget_card_of_fintype
    [Fintype Z]
    (G : ExactVisibleSwitchedFamily Z k Index) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G
      (Fintype.card (ExactVisiblePostSwitchSurface Z k)) := by
  exact IndexedPredictorFamily.hasBitBudget_card_of_fintype G

/-- Quantitative form: if an exact switched family on the full visible
post-switch surface already realizes every Boolean rule there, then any exact
bit budget must be at least the full surface cardinality. -/
theorem exactVisibleCompressionTarget_surfaceCard_le_of_surjective_predict
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hsurj : Function.Surjective G.predict)
    (hsmall : ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ s := by
  classical
  exact
    IndexedPredictorFamily.bitBudget_lowerBound_of_surjective_predict_fintype
      (G := G) (s := s) (Input := ExactVisiblePostSwitchSurface Z k) hsurj hsmall

/-- Sharpness form: under surjectivity onto the full exact visible rule class,
the truth-table budget is achievable and no smaller exact budget exists. -/
theorem exactVisibleCompressionTarget_card_isSharp_of_surjective_predict
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hsurj : Function.Surjective G.predict) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G
        (Fintype.card (ExactVisiblePostSwitchSurface Z k)) ∧
      ∀ {t : ℕ},
        ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G t →
          Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ t := by
  refine ⟨exactVisibleCompressionTarget_card_of_fintype (Z := Z) (k := k) G, ?_⟩
  intro t hsmall
  exact
    exactVisibleCompressionTarget_surfaceCard_le_of_surjective_predict
      (Z := Z) (k := k) (s := t) (Index := Index) hsurj hsmall

/-- If an exact switched family already realizes every Boolean rule on the full
visible post-switch surface, then any `s`-bit compression theorem below the
surface-cardinality threshold is impossible. -/
theorem not_exactVisibleCompressionTarget_of_surjective_predict
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k))
    (hsurj : Function.Surjective G.predict) :
    ¬ ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s := by
  intro hsmall
  exact Nat.not_le_of_lt hs <|
    exactVisibleCompressionTarget_surfaceCard_le_of_surjective_predict
      (Z := Z) (k := k) (s := s) (Index := Index) hsurj hsmall

/-- The same obstruction applies to the charitable invariant-view repair, since
that repair still has to realize the full exact family after pullback. -/
theorem not_invariantCompressionTarget_of_surjective_predict
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k))
    (hsurj : Function.Surjective G.predict) :
    ¬ InvariantCompressionTarget (Z := Z) (k := k) (Index := Index) G s := by
  intro h
  exact
    not_exactVisibleCompressionTarget_of_surjective_predict
      (Z := Z) (k := k) (s := s) (Index := Index) hs hsurj
      (exactVisibleCompressionTarget_of_invariantCompressionTarget h)

/-- The invariant-view repair inherits the same surface-cardinality lower bound,
because any such repair induces an exact compression target. -/
theorem invariantCompressionTarget_surfaceCard_le_of_surjective_predict
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hsurj : Function.Surjective G.predict)
    (hsmall : InvariantCompressionTarget (Z := Z) (k := k) (Index := Index) G s) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ s := by
  exact
    exactVisibleCompressionTarget_surfaceCard_le_of_surjective_predict
      (Z := Z) (k := k) (s := s) (Index := Index) hsurj
      (exactVisibleCompressionTarget_of_invariantCompressionTarget hsmall)

/-- Likewise for the charitable fork-view repair. -/
theorem not_forkCompressionTarget_of_surjective_predict
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k))
    (hsurj : Function.Surjective G.predict) :
    ¬ ForkCompressionTarget (Z := Z) (k := k) (Index := Index) G s := by
  intro h
  exact
    not_exactVisibleCompressionTarget_of_surjective_predict
      (Z := Z) (k := k) (s := s) (Index := Index) hs hsurj
      (exactVisibleCompressionTarget_of_forkCompressionTarget h)

/-- The fork-view repair likewise inherits the same exact-surface lower bound. -/
theorem forkCompressionTarget_surfaceCard_le_of_surjective_predict
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hsurj : Function.Surjective G.predict)
    (hsmall : ForkCompressionTarget (Z := Z) (k := k) (Index := Index) G s) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ s := by
  exact
    exactVisibleCompressionTarget_surfaceCard_le_of_surjective_predict
      (Z := Z) (k := k) (s := s) (Index := Index) hsurj
      (exactVisibleCompressionTarget_of_forkCompressionTarget hsmall)

end ExactFamily

end Mettapedia.Computability.PNP
