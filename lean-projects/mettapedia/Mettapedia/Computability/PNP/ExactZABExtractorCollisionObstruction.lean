import Mettapedia.Computability.PNP.CanonicalZABERMInterface

/-!
# P vs NP crux: noninjective shared `z` extractors already block exact surjectivity

The exact `(zfeat(z), a, b)` decision-list route can only see the shared
extractor output `zfeat z` together with the visible `(a, b)` bits. If `zfeat`
identifies two distinct latent states, then every realized predictor is forced
to agree on the corresponding exact-surface fiber.

That is already enough to block surjectivity on the full exact rule class:
there are Boolean rules on the exact surface that separate two such colliding
points, but no predictor realized by the route can do so.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section Core

variable {Z : Type*} {r k : ℕ}

/-- A Boolean rule is invariant on each exact `(zfeat(z), a, b)` fiber when it
only depends on the visible summary `exactZABVisibleData`. -/
def ExactZABFiberInvariantRule
    (zfeat : Z → BitVec r)
    (rule : ExactVisiblePostSwitchSurface Z k → Bool) : Prop :=
  ∀ u v,
    exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat u =
      exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat v →
    rule u = rule v

/-- A Boolean rule separates one exact `(zfeat(z), a, b)` fiber when it
distinguishes two exact inputs with the same visible summary. -/
def ExactZABFiberSeparatingRule
    (zfeat : Z → BitVec r)
    (rule : ExactVisiblePostSwitchSurface Z k → Bool) : Prop :=
  ∃ u v,
    exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat u =
      exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat v ∧
    rule u ≠ rule v

theorem not_exactZABFiberSeparatingRule_of_exactZABFiberInvariantRule
    {zfeat : Z → BitVec r}
    {rule : ExactVisiblePostSwitchSurface Z k → Bool}
    (hinv : ExactZABFiberInvariantRule (Z := Z) (r := r) (k := k) zfeat rule) :
    ¬ ExactZABFiberSeparatingRule (Z := Z) (r := r) (k := k) zfeat rule := by
  rintro ⟨u, v, huv, hneq⟩
  exact hneq (hinv u v huv)

theorem rawExactZABDecisionListPredict_eq_of_exactZABVisibleData_eq
    (zfeat : Z → BitVec r)
    (code : SharedAffineDecisionListCode (r + (k + k)))
    {u v : ExactVisiblePostSwitchSurface Z k}
    (huv :
      exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat u =
        exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat v) :
    rawExactZABDecisionListPredict (Z := Z) (r := r) (k := k) zfeat code u =
      rawExactZABDecisionListPredict (Z := Z) (r := r) (k := k) zfeat code v := by
  simp [rawExactZABDecisionListPredict, huv]

theorem exactZABFiberInvariantRule_of_eq_predict_of_realizedByRawExactZABDecisionListFamily
    {Index : Type*}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hreal :
      RealizedByRawExactZABDecisionListFamily
        (Z := Z) (r := r) (k := k) zfeat G)
    {i : Index}
    {rule : ExactVisiblePostSwitchSurface Z k → Bool}
    (hi : G.predict i = rule) :
    ExactZABFiberInvariantRule (Z := Z) (r := r) (k := k) zfeat rule := by
  rcases hreal i with ⟨code, hcode⟩
  intro u v huv
  calc
    rule u = G.predict i u := by simp [hi]
    _ = rawExactZABDecisionListPredict (Z := Z) (r := r) (k := k) zfeat code u := by
      simp [hcode]
    _ = rawExactZABDecisionListPredict (Z := Z) (r := r) (k := k) zfeat code v := by
      exact rawExactZABDecisionListPredict_eq_of_exactZABVisibleData_eq
        (Z := Z) (r := r) (k := k) zfeat code huv
    _ = G.predict i v := by simp [hcode]
    _ = rule v := by simp [hi]

theorem not_exists_predict_eq_of_realizedByRawExactZABDecisionListFamily_of_exactZABFiberSeparatingRule
    {Index : Type*}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hreal :
      RealizedByRawExactZABDecisionListFamily
        (Z := Z) (r := r) (k := k) zfeat G)
    {rule : ExactVisiblePostSwitchSurface Z k → Bool}
    (hsep : ExactZABFiberSeparatingRule (Z := Z) (r := r) (k := k) zfeat rule) :
    ¬ ∃ i, G.predict i = rule := by
  rintro ⟨i, hi⟩
  exact
    not_exactZABFiberSeparatingRule_of_exactZABFiberInvariantRule
      (Z := Z) (r := r) (k := k)
      (exactZABFiberInvariantRule_of_eq_predict_of_realizedByRawExactZABDecisionListFamily
        (Z := Z) (r := r) (k := k) hreal hi)
      hsep

/-- The point-mass rule at one exact visible input. -/
noncomputable def exactZABPointRule
    (u0 : ExactVisiblePostSwitchSurface Z k) :
    ExactVisiblePostSwitchSurface Z k → Bool :=
  fun u => by
    classical
    exact decide (u = u0)

theorem exactZABPointRule_exactZABFiberSeparatingRule_of_ne_of_eq_visible
    {zfeat : Z → BitVec r}
    {u v : ExactVisiblePostSwitchSurface Z k}
    (huv :
      exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat u =
        exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat v)
    (hneq : u ≠ v) :
    ExactZABFiberSeparatingRule
      (Z := Z) (r := r) (k := k) zfeat (exactZABPointRule (Z := Z) (k := k) u) := by
  classical
  have hvu : v ≠ u := by
    intro h
    exact hneq h.symm
  refine ⟨u, v, huv, ?_⟩
  simp [exactZABPointRule, hvu]

theorem exists_exactZABFiberSeparatingRule_of_not_injective
    (zfeat : Z → BitVec r)
    (hni : ¬ Function.Injective zfeat) :
    ∃ rule,
      ExactZABFiberSeparatingRule (Z := Z) (r := r) (k := k) zfeat rule := by
  classical
  have hcollision : ∃ z0 z1, z0 ≠ z1 ∧ zfeat z0 = zfeat z1 := by
    by_contra hcollision
    apply hni
    intro z0 z1 hz
    by_contra hne
    exact hcollision ⟨z0, z1, hne, hz⟩
  rcases hcollision with ⟨z0, z1, hne, hz⟩
  let a : BitVec k := default
  let b : BitVec k := default
  let u : ExactVisiblePostSwitchSurface Z k := ⟨z0, a, b⟩
  let v : ExactVisiblePostSwitchSurface Z k := ⟨z1, a, b⟩
  have huv :
      exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat u =
        exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat v := by
    simp [u, v, exactZABVisibleData, exactABVisibleData, hz]
  have hneq : u ≠ v := by
    intro huv'
    have hz' : z0 = z1 := by
      simpa [u, v] using congrArg PostSwitchInput.z huv'
    exact hne hz'
  exact
    ⟨exactZABPointRule (Z := Z) (k := k) u,
      exactZABPointRule_exactZABFiberSeparatingRule_of_ne_of_eq_visible
        (Z := Z) (r := r) (k := k) huv hneq⟩

theorem not_surjective_predict_of_not_injective_of_realizedByRawExactZABDecisionListFamily
    {Index : Type*}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hreal :
      RealizedByRawExactZABDecisionListFamily
        (Z := Z) (r := r) (k := k) zfeat G)
    (hni : ¬ Function.Injective zfeat) :
    ¬ Function.Surjective G.predict := by
  classical
  rcases exists_exactZABFiberSeparatingRule_of_not_injective
      (Z := Z) (r := r) (k := k) zfeat hni with ⟨rule, hsep⟩
  intro hsurj
  rcases hsurj rule with ⟨i, hi⟩
  exact
    (not_exists_predict_eq_of_realizedByRawExactZABDecisionListFamily_of_exactZABFiberSeparatingRule
      (Z := Z) (r := r) (k := k) hreal hsep) ⟨i, hi⟩

theorem not_injective_of_card_gt_bitVec
    [Fintype Z]
    (zfeat : Z → BitVec r)
    (hcard : 2 ^ r < Fintype.card Z) :
    ¬ Function.Injective zfeat := by
  intro hinj
  have hle : Fintype.card Z ≤ Fintype.card (BitVec r) :=
    Fintype.card_le_of_injective zfeat hinj
  exact Nat.not_le_of_lt hcard (by simpa [BitVec] using hle)

end Core

section Route

variable {Z : Type*} {r k : ℕ} {Index : Type*}

theorem ExactZABDecisionListTargetData.not_surjective_predict_of_not_injective_zfeat
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h :
      ExactZABDecisionListTargetData
        (Z := Z) (r := r) (k := k) (Index := Index) zfeat G)
    (hni : ¬ Function.Injective zfeat) :
    ¬ Function.Surjective G.predict := by
  exact
    not_surjective_predict_of_not_injective_of_realizedByRawExactZABDecisionListFamily
      (Z := Z) (r := r) (k := k) h.realized hni

theorem ExactZABDecisionListTargetData.not_surjective_predict_of_card_gt_bitVec
    [Fintype Z]
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h :
      ExactZABDecisionListTargetData
        (Z := Z) (r := r) (k := k) (Index := Index) zfeat G)
    (hcard : 2 ^ r < Fintype.card Z) :
    ¬ Function.Surjective G.predict := by
  exact h.not_surjective_predict_of_not_injective_zfeat <|
    not_injective_of_card_gt_bitVec (Z := Z) (r := r) zfeat hcard

theorem ExactZABDecisionListRecoveryData.not_surjective_predict_of_not_injective_zfeat
    [Fintype Z]
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABDecisionListRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hni : ¬ Function.Injective zfeat) :
    ¬ Function.Surjective G.predict := by
  exact (h.targetData).not_surjective_predict_of_not_injective_zfeat hni

theorem CanonicalZABDecisionListCandidateData.not_surjective_predict_of_not_injective_zfeat
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h :
      CanonicalZABDecisionListCandidateData
        (Z := Z) (r := r) (k := k) (Index := Index) zfeat G)
    (hni : ¬ Function.Injective zfeat) :
    ¬ Function.Surjective G.predict := by
  exact (h.targetData).not_surjective_predict_of_not_injective_zfeat hni

theorem exactZABDecisionListERMFamily_not_surjective_of_not_injective_zfeat
    (zfeat : Z → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (hni : ¬ Function.Injective zfeat) :
    ¬ Function.Surjective
        (exactZABDecisionListERMFamily
          (Z := Z) (r := r) (k := k) zfeat samples).predict := by
  exact
    (exactZABDecisionListERMTargetData
      (Z := Z) (r := r) (k := k) (Index := Index) zfeat samples).not_surjective_predict_of_not_injective_zfeat
      hni

theorem exactZABDecisionListERMFamily_not_surjective_of_card_gt_bitVec
    [Fintype Z]
    (zfeat : Z → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (hcard : 2 ^ r < Fintype.card Z) :
    ¬ Function.Surjective
        (exactZABDecisionListERMFamily
          (Z := Z) (r := r) (k := k) zfeat samples).predict := by
  exact
    exactZABDecisionListERMFamily_not_surjective_of_not_injective_zfeat
      (Z := Z) (r := r) (k := k) (Index := Index) zfeat samples <|
      not_injective_of_card_gt_bitVec (Z := Z) (r := r) zfeat hcard

theorem CanonicalZABERMRecoveryData.not_surjective_predict_of_not_injective_zfeat
    [Fintype Z]
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      CanonicalZABERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hni : ¬ Function.Injective zfeat) :
    ¬ Function.Surjective G.predict := by
  exact (h.targetData).not_surjective_predict_of_not_injective_zfeat hni

end Route

end Mettapedia.Computability.PNP
