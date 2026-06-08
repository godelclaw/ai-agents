import Mettapedia.Computability.PNP.ProductSuccessKpolyBridgeObstruction
import Mettapedia.Computability.PNP.SharedExactZABFeatureFamilies

/-!
# P vs NP route characterization: shared exact affine decision lists are exactly
  an injective first-active-signature route

The shared exact affine decision-list branch fixes

* one shared extractor `zfeat`,
* one shared affine basis on `(zfeat(z), a, b)`,
* and lets only the downstream fixed-order decision-list code vary.

That means every predictor in the branch depends only on the first active
feature in the shared summary.  This file records the exact boundary:

* if that first-active signature is injective on the exact visible surface,
  then the branch realizes the full exact Boolean rule family;
* if it is not injective, then the branch cannot be surjective onto the full
  exact rule family.

So this route is not a standalone compression theorem.  It is exactly an
injective first-active-signature requirement on the shared summary map.
-/

namespace Mettapedia.Computability.PNP

section SignatureInvariant

variable {Z : Type*} {S : Type*} {p r k : ℕ}

/-- A rule is signature-invariant if it depends only on one fixed signature
map on the exact visible surface. -/
def ExactVisibleSignatureInvariantRule
    (signature : ExactVisiblePostSwitchSurface Z k → S)
    (rule : ExactVisibleRule Z k) : Prop :=
  ∀ u v, signature u = signature v → rule u = rule v

theorem not_surjective_predict_of_all_exactVisibleSignatureInvariant
    {Index : Type*}
    {signature : ExactVisiblePostSwitchSurface Z k → S}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hinv :
      ∀ i, ExactVisibleSignatureInvariantRule
        (Z := Z) (S := S) (k := k) signature (G.predict i))
    (hni : ¬ Function.Injective signature) :
    ¬ Function.Surjective G.predict := by
  classical
  rw [Function.Injective] at hni
  push_neg at hni
  rcases hni with ⟨u, v, huv, hne⟩
  let rule : ExactVisibleRule Z k := fun x => if x = u then true else false
  intro hsurj
  rcases hsurj rule with ⟨i, hi⟩
  have hrule :
      ExactVisibleSignatureInvariantRule
        (Z := Z) (S := S) (k := k) signature rule := by
    intro x y hxy
    simpa [hi] using hinv i x y hxy
  have hconst : rule u = rule v := hrule u v huv
  have hvu : v = u := by
    simpa [rule] using hconst
  exact hne hvu.symm

/-- The shared exact affine decision-list signature keeps only the first active
shared feature, if any. -/
noncomputable def exactZABAffineDecisionListSignature
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k))) :
    ExactVisiblePostSwitchSurface Z k → Option (Fin p) :=
  fun u =>
    firstActiveFeature?
      (exactZABAffineFeatureSummary
        (Z := Z) (p := p) (r := r) (k := k) zfeat features u)

theorem all_exactVisibleSignatureInvariant_of_realizedBySharedExactZABAffineDecisionListFamily
    {Index : Type*}
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hreal :
      RealizedBySharedExactZABAffineDecisionListFamily
        (Z := Z) (p := p) (r := r) (k := k) zfeat features G) :
    ∀ i,
      ExactVisibleSignatureInvariantRule
        (Z := Z) (S := Option (Fin p)) (k := k)
        (exactZABAffineDecisionListSignature
          (Z := Z) (p := p) (r := r) (k := k) zfeat features)
        (G.predict i) := by
  intro i u v huv
  rcases hreal i with ⟨code, hcode⟩
  calc
    G.predict i u =
        sharedExactZABAffineDecisionListPredict
          (Z := Z) (p := p) (r := r) (k := k) zfeat features code u := by
            simp [hcode]
    _ =
        match exactZABAffineDecisionListSignature
            (Z := Z) (p := p) (r := r) (k := k) zfeat features u with
        | some j => code.1 j
        | none => code.2 := by
            rfl
    _ =
        match exactZABAffineDecisionListSignature
            (Z := Z) (p := p) (r := r) (k := k) zfeat features v with
        | some j => code.1 j
        | none => code.2 := by
            rw [huv]
    _ =
        sharedExactZABAffineDecisionListPredict
          (Z := Z) (p := p) (r := r) (k := k) zfeat features code v := by
            rfl
    _ = G.predict i v := by
            simp [hcode]

theorem injective_signature_of_surjective_predict_of_realizedBySharedExactZABAffineDecisionListFamily
    {Index : Type*}
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hreal :
      RealizedBySharedExactZABAffineDecisionListFamily
        (Z := Z) (p := p) (r := r) (k := k) zfeat features G)
    (hsurj : Function.Surjective G.predict) :
    Function.Injective
      (exactZABAffineDecisionListSignature
        (Z := Z) (p := p) (r := r) (k := k) zfeat features) := by
  by_contra hni
  exact
    (not_surjective_predict_of_all_exactVisibleSignatureInvariant
      (Z := Z) (S := Option (Fin p)) (k := k)
      (signature := exactZABAffineDecisionListSignature
        (Z := Z) (p := p) (r := r) (k := k) zfeat features)
      (G := G)
      (all_exactVisibleSignatureInvariant_of_realizedBySharedExactZABAffineDecisionListFamily
        (Z := Z) (p := p) (r := r) (k := k) hreal)
      hni) hsurj

end SignatureInvariant

section FullRuleFamily

variable {Z : Type*} {p r k : ℕ}

theorem fullExactVisibleRuleFamily_realizedBySharedExactZABAffineDecisionListFamily_of_injective_signature
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (hinj :
      Function.Injective
        (exactZABAffineDecisionListSignature
          (Z := Z) (p := p) (r := r) (k := k) zfeat features)) :
    RealizedBySharedExactZABAffineDecisionListFamily
      (Z := Z) (p := p) (r := r) (k := k)
      zfeat features (fullExactVisibleRuleFamily Z k) := by
  classical
  intro rule
  let responses : BitCode p := fun j =>
    if h : ∃ u,
        exactZABAffineDecisionListSignature
          (Z := Z) (p := p) (r := r) (k := k) zfeat features u = some j then
      rule (Classical.choose h)
    else
      false
  let default : Bool :=
    if h : ∃ u,
        exactZABAffineDecisionListSignature
          (Z := Z) (p := p) (r := r) (k := k) zfeat features u = none then
      rule (Classical.choose h)
    else
      false
  refine ⟨(responses, default), ?_⟩
  funext u
  simp [fullExactVisibleRuleFamily]
  symm
  change
    (match
        exactZABAffineDecisionListSignature
          (Z := Z) (p := p) (r := r) (k := k) zfeat features u with
      | some j => responses j
      | none => default) = rule u
  cases hsig :
      exactZABAffineDecisionListSignature
        (Z := Z) (p := p) (r := r) (k := k) zfeat features u with
  | none =>
      dsimp [default]
      have hex : ∃ u',
          exactZABAffineDecisionListSignature
            (Z := Z) (p := p) (r := r) (k := k) zfeat features u' = none := ⟨u, hsig⟩
      have hchoose : Classical.choose hex = u := by
        apply hinj
        exact (Classical.choose_spec hex).trans hsig.symm
      simp [hex, hchoose]
  | some j =>
      dsimp [responses]
      have hex : ∃ u',
          exactZABAffineDecisionListSignature
            (Z := Z) (p := p) (r := r) (k := k) zfeat features u' = some j := ⟨u, hsig⟩
      have hchoose : Classical.choose hex = u := by
        apply hinj
        exact (Classical.choose_spec hex).trans hsig.symm
      simp [hex, hchoose]

theorem fullExactVisibleRuleFamily_not_realizedBySharedExactZABAffineDecisionListFamily_of_not_injective_signature
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (hni :
      ¬ Function.Injective
        (exactZABAffineDecisionListSignature
          (Z := Z) (p := p) (r := r) (k := k) zfeat features)) :
    ¬ RealizedBySharedExactZABAffineDecisionListFamily
        (Z := Z) (p := p) (r := r) (k := k)
        zfeat features (fullExactVisibleRuleFamily Z k) := by
  intro hreal
  exact
    hni
      (injective_signature_of_surjective_predict_of_realizedBySharedExactZABAffineDecisionListFamily
        (Z := Z) (p := p) (r := r) (k := k)
        (G := fullExactVisibleRuleFamily Z k)
        hreal (fullExactVisibleRuleFamily_surjective Z k))

theorem fullExactVisibleRuleFamily_realizedBySharedExactZABAffineDecisionListFamily_iff_injective_signature
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k))) :
    RealizedBySharedExactZABAffineDecisionListFamily
        (Z := Z) (p := p) (r := r) (k := k)
        zfeat features (fullExactVisibleRuleFamily Z k) ↔
      Function.Injective
        (exactZABAffineDecisionListSignature
          (Z := Z) (p := p) (r := r) (k := k) zfeat features) := by
  constructor
  · intro hreal
    exact
      injective_signature_of_surjective_predict_of_realizedBySharedExactZABAffineDecisionListFamily
        (Z := Z) (p := p) (r := r) (k := k)
        (G := fullExactVisibleRuleFamily Z k)
        hreal (fullExactVisibleRuleFamily_surjective Z k)
  · intro hinj
    exact
      fullExactVisibleRuleFamily_realizedBySharedExactZABAffineDecisionListFamily_of_injective_signature
        (Z := Z) (p := p) (r := r) (k := k) zfeat features hinj

end FullRuleFamily

end Mettapedia.Computability.PNP
