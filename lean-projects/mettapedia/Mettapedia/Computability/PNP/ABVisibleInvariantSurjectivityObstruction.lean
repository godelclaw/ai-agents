import Mettapedia.Computability.PNP.CanonicalABCodeWitness
import Mettapedia.Computability.PNP.FiniteIIDAgreement
import Mettapedia.Computability.PNP.SharedABRecoveryInterface
import Mettapedia.Computability.PNP.SharedExactABFeatureERMInterface
import Mettapedia.Computability.PNP.SharedExactABERMInterface

/-!
# P vs NP crux: raw `(a, b)` invariance already blocks exact-surface surjectivity

The previous shared-AB route files recorded counting lower bounds once one asks
for small exact-surface realizations.  There is an earlier obstruction.

If an exact switched family is invariant under the raw visible quotient
`(z, a, b) ↦ (a, b)`, then every predictor in the family is constant on each
`z`-fiber over fixed `(a, b)`.  Therefore, whenever the latent datum type `Z`
has at least two values, the family cannot already realize *all* Boolean rules
on the exact visible surface.

So "the switched decoder only depends on `(a, b)`" is not merely a small-class
budget issue.  It already prevents surjectivity on the exact surface outright.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section Core

variable {Z : Type*} {k : ℕ}

/-- A Boolean rule on the exact visible surface is invariant on every raw
`(a,b)` fiber when it gives equal outputs to exact inputs with the same
`abVisibleData`. -/
def ABFiberInvariantRule (rule : ExactVisiblePostSwitchSurface Z k → Bool) : Prop :=
  ∀ u v, abVisibleData u = abVisibleData v → rule u = rule v

/-- A Boolean rule separates the raw `(a,b)` quotient when it distinguishes two
exact inputs with the same raw `(a,b)` data. -/
def ABFiberSeparatingRule (rule : ExactVisiblePostSwitchSurface Z k → Bool) : Prop :=
  ∃ u v, abVisibleData u = abVisibleData v ∧ rule u ≠ rule v

theorem not_abFiberSeparatingRule_of_abFiberInvariantRule
    {rule : ExactVisiblePostSwitchSurface Z k → Bool}
    (hrule : ABFiberInvariantRule (Z := Z) (k := k) rule) :
    ¬ ABFiberSeparatingRule (Z := Z) (k := k) rule := by
  rintro ⟨u, v, hab, hneq⟩
  exact hneq (hrule u v hab)

theorem abFiberInvariantRule_of_eq_predict_of_abVisibleInvariant
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hinv : ABVisibleInvariant (Z := Z) (k := k) G)
    {i : Index} {rule : ExactVisiblePostSwitchSurface Z k → Bool}
    (hi : G.predict i = rule) :
    ABFiberInvariantRule (Z := Z) (k := k) rule := by
  intro u v hab
  simpa [← hi] using hinv i u v hab

theorem not_exists_predict_eq_of_abVisibleInvariant_of_abFiberSeparatingRule
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hinv : ABVisibleInvariant (Z := Z) (k := k) G)
    {rule : ExactVisiblePostSwitchSurface Z k → Bool}
    (hsep : ABFiberSeparatingRule (Z := Z) (k := k) rule) :
    ¬ ∃ i, G.predict i = rule := by
  rintro ⟨i, hi⟩
  exact
    not_abFiberSeparatingRule_of_abFiberInvariantRule
      (abFiberInvariantRule_of_eq_predict_of_abVisibleInvariant
        (Z := Z) (k := k) hinv hi)
      hsep

theorem abVisibleInvariant_of_factorsThrough_abVisibleData
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    (hfactor : G.FactorsThrough abVisibleData H) :
    ABVisibleInvariant (Z := Z) (k := k) G := by
  intro i u v huv
  calc
    G.predict i u = H.predict i (abVisibleData u) := hfactor i u
    _ = H.predict i (abVisibleData v) := by simpa using congrArg (H.predict i) huv
    _ = G.predict i v := (hfactor i v).symm

theorem not_exists_predict_eq_of_factorsThrough_abVisibleData_of_abFiberSeparatingRule
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    (hfactor : G.FactorsThrough abVisibleData H)
    {rule : ExactVisiblePostSwitchSurface Z k → Bool}
    (hsep : ABFiberSeparatingRule (Z := Z) (k := k) rule) :
    ¬ ∃ i, G.predict i = rule :=
  not_exists_predict_eq_of_abVisibleInvariant_of_abFiberSeparatingRule
    (Z := Z) (k := k)
    (abVisibleInvariant_of_factorsThrough_abVisibleData
      (Z := Z) (k := k) hfactor)
    hsep

/-- The concrete rule reading the hidden `z` bit on the exact visible surface. -/
def boolZProjectionRule (u : ExactVisiblePostSwitchSurface Bool k) : Bool := u.z

theorem boolZProjectionRule_abFiberSeparatingRule :
    ABFiberSeparatingRule (Z := Bool) (k := k)
      (boolZProjectionRule (k := k)) := by
  let a : BitVec k := default
  let b : BitVec k := default
  refine ⟨⟨false, a, b⟩, ⟨true, a, b⟩, rfl, ?_⟩
  simp [boolZProjectionRule]

theorem not_exists_predict_eq_boolZProjectionRule_of_abVisibleInvariant
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Bool k Index}
    (hinv : ABVisibleInvariant (Z := Bool) (k := k) G) :
    ¬ ∃ i, G.predict i = boolZProjectionRule (k := k) :=
  not_exists_predict_eq_of_abVisibleInvariant_of_abFiberSeparatingRule
    (Z := Bool) (k := k) hinv
    (boolZProjectionRule_abFiberSeparatingRule (k := k))

theorem not_exists_predict_eq_boolZProjectionRule_of_factorsThrough_abVisibleData
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Bool k Index}
    {H : ABVisibleSwitchedFamily k Index}
    (hfactor : G.FactorsThrough abVisibleData H) :
    ¬ ∃ i, G.predict i = boolZProjectionRule (k := k) :=
  not_exists_predict_eq_of_factorsThrough_abVisibleData_of_abFiberSeparatingRule
    (Z := Bool) (k := k) hfactor
    (boolZProjectionRule_abFiberSeparatingRule (k := k))

/-- An invariant predictor cannot agree with a target on both sides of a
same-`(a,b)` fiber that the target separates. -/
theorem exists_disagreement_of_abFiberInvariantRule_of_abFiberSeparation
    {target predict : ExactVisiblePostSwitchSurface Z k → Bool}
    (hpredict : ABFiberInvariantRule (Z := Z) (k := k) predict)
    {u v : ExactVisiblePostSwitchSurface Z k}
    (hab : abVisibleData u = abVisibleData v)
    (hsep : target u ≠ target v) :
    predict u ≠ target u ∨ predict v ≠ target v := by
  by_cases hu : predict u = target u
  · right
    intro hv
    have hp : predict u = predict v := hpredict u v hab
    exact hsep (hu.symm.trans (hp.trans hv))
  · exact Or.inl hu

/-- Support-level form: if a distribution puts positive mass on both sides of a
same-`(a,b)` fiber separated by the target, an invariant predictor has a
positive-mass disagreement point. -/
theorem exists_pos_mass_disagreement_of_abFiberInvariantRule_of_abFiberSeparation
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {target predict : ExactVisiblePostSwitchSurface Z k → Bool}
    (hpredict : ABFiberInvariantRule (Z := Z) (k := k) predict)
    {u v : ExactVisiblePostSwitchSurface Z k}
    (hab : abVisibleData u = abVisibleData v)
    (hsep : target u ≠ target v)
    (huμ : μ u ≠ 0) (hvμ : μ v ≠ 0) :
    ∃ x, μ x ≠ 0 ∧ predict x ≠ target x := by
  rcases
      exists_disagreement_of_abFiberInvariantRule_of_abFiberSeparation
        (Z := Z) (k := k) (target := target) (predict := predict)
        hpredict hab hsep with hbad | hbad
  · exact ⟨u, huμ, hbad⟩
  · exact ⟨v, hvμ, hbad⟩

/-- Indexed-family support-level form for raw `(a,b)`-invariant exact visible
families. -/
theorem exists_pos_mass_disagreement_of_abVisibleInvariant_predict_of_abFiberSeparation
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hinv : ABVisibleInvariant (Z := Z) (k := k) G)
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {target : ExactVisiblePostSwitchSurface Z k → Bool}
    (i : Index)
    {u v : ExactVisiblePostSwitchSurface Z k}
    (hab : abVisibleData u = abVisibleData v)
    (hsep : target u ≠ target v)
    (huμ : μ u ≠ 0) (hvμ : μ v ≠ 0) :
    ∃ x, μ x ≠ 0 ∧ G.predict i x ≠ target x := by
  exact
    exists_pos_mass_disagreement_of_abFiberInvariantRule_of_abFiberSeparation
      (Z := Z) (k := k) (μ := μ) (target := target) (predict := G.predict i)
      (fun u v hab => hinv i u v hab) hab hsep huμ hvμ

/-- Factor-through form of the support-level obstruction. -/
theorem exists_pos_mass_disagreement_of_factorsThrough_abVisibleData_predict_of_abFiberSeparation
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    (hfactor : G.FactorsThrough abVisibleData H)
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {target : ExactVisiblePostSwitchSurface Z k → Bool}
    (i : Index)
    {u v : ExactVisiblePostSwitchSurface Z k}
    (hab : abVisibleData u = abVisibleData v)
    (hsep : target u ≠ target v)
    (huμ : μ u ≠ 0) (hvμ : μ v ≠ 0) :
    ∃ x, μ x ≠ 0 ∧ G.predict i x ≠ target x := by
  exact
    exists_pos_mass_disagreement_of_abVisibleInvariant_predict_of_abFiberSeparation
      (Z := Z) (k := k)
      (abVisibleInvariant_of_factorsThrough_abVisibleData
        (Z := Z) (k := k) hfactor)
      (μ := μ) (target := target) i hab hsep huμ hvμ

/-- Agreement-mass form: on any positive-mass same-`(a,b)` separating fiber,
an invariant predictor has agreement mass strictly below one. -/
theorem agreementMass_lt_one_of_abVisibleInvariant_predict_of_abFiberSeparation
    [Fintype Z]
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hinv : ABVisibleInvariant (Z := Z) (k := k) G)
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {target : ExactVisiblePostSwitchSurface Z k → Bool}
    (i : Index)
    {u v : ExactVisiblePostSwitchSurface Z k}
    (hab : abVisibleData u = abVisibleData v)
    (hsep : target u ≠ target v)
    (huμ : μ u ≠ 0) (hvμ : μ v ≠ 0) :
    agreementMass μ target (G.predict i) < 1 := by
  rcases
      exists_pos_mass_disagreement_of_abVisibleInvariant_predict_of_abFiberSeparation
        (Z := Z) (k := k) hinv (μ := μ) (target := target) i
        hab hsep huμ hvμ with ⟨x, hxμ, hxdis⟩
  exact agreementMass_lt_one_of_pos_mass_disagreement
    (μ := μ) (target := target) (predict := G.predict i) hxμ hxdis

/-- Factor-through agreement-mass form of the same support obstruction. -/
theorem agreementMass_lt_one_of_factorsThrough_abVisibleData_predict_of_abFiberSeparation
    [Fintype Z]
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    (hfactor : G.FactorsThrough abVisibleData H)
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {target : ExactVisiblePostSwitchSurface Z k → Bool}
    (i : Index)
    {u v : ExactVisiblePostSwitchSurface Z k}
    (hab : abVisibleData u = abVisibleData v)
    (hsep : target u ≠ target v)
    (huμ : μ u ≠ 0) (hvμ : μ v ≠ 0) :
    agreementMass μ target (G.predict i) < 1 := by
  exact
    agreementMass_lt_one_of_abVisibleInvariant_predict_of_abFiberSeparation
      (Z := Z) (k := k)
      (abVisibleInvariant_of_factorsThrough_abVisibleData
        (Z := Z) (k := k) hfactor)
      (μ := μ) (target := target) i hab hsep huμ hvμ

/-- Family-level agreement-mass form: no raw `(a,b)`-invariant exact family can
contain a predictor with perfect agreement mass against a target that separates
two positive-mass points in one same-`(a,b)` fiber. -/
theorem not_exists_agreementMass_eq_one_of_abVisibleInvariant_of_abFiberSeparation
    [Fintype Z]
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hinv : ABVisibleInvariant (Z := Z) (k := k) G)
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {target : ExactVisiblePostSwitchSurface Z k → Bool}
    {u v : ExactVisiblePostSwitchSurface Z k}
    (hab : abVisibleData u = abVisibleData v)
    (hsep : target u ≠ target v)
    (huμ : μ u ≠ 0) (hvμ : μ v ≠ 0) :
    ¬ ∃ i, agreementMass μ target (G.predict i) = 1 := by
  rintro ⟨i, hi⟩
  exact
    (ne_of_lt
      (agreementMass_lt_one_of_abVisibleInvariant_predict_of_abFiberSeparation
        (Z := Z) (k := k) hinv (μ := μ) (target := target) i
        hab hsep huμ hvμ))
      hi

/-- Factor-through family-level agreement-mass obstruction. -/
theorem not_exists_agreementMass_eq_one_of_factorsThrough_abVisibleData_of_abFiberSeparation
    [Fintype Z]
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    (hfactor : G.FactorsThrough abVisibleData H)
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {target : ExactVisiblePostSwitchSurface Z k → Bool}
    {u v : ExactVisiblePostSwitchSurface Z k}
    (hab : abVisibleData u = abVisibleData v)
    (hsep : target u ≠ target v)
    (huμ : μ u ≠ 0) (hvμ : μ v ≠ 0) :
    ¬ ∃ i, agreementMass μ target (G.predict i) = 1 := by
  exact
    not_exists_agreementMass_eq_one_of_abVisibleInvariant_of_abFiberSeparation
      (Z := Z) (k := k)
      (abVisibleInvariant_of_factorsThrough_abVisibleData
        (Z := Z) (k := k) hfactor)
      (μ := μ) (target := target) hab hsep huμ hvμ

/-- Concrete hidden-`z` readout support obstruction: any raw `(a,b)`-invariant
predictor disagrees with the hidden-bit projection on positive mass whenever the
measure gives positive mass to the two hidden-bit points with the same default
raw `(a,b)` data. -/
theorem exists_pos_mass_disagreement_of_abVisibleInvariant_predict_boolZProjectionRule
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Bool k Index}
    (hinv : ABVisibleInvariant (Z := Bool) (k := k) G)
    {μ : PMF (ExactVisiblePostSwitchSurface Bool k)}
    (i : Index)
    (hfalse : μ ⟨false, default, default⟩ ≠ 0)
    (htrue : μ ⟨true, default, default⟩ ≠ 0) :
    ∃ x, μ x ≠ 0 ∧ G.predict i x ≠ boolZProjectionRule (k := k) x := by
  let u : ExactVisiblePostSwitchSurface Bool k := ⟨false, default, default⟩
  let v : ExactVisiblePostSwitchSurface Bool k := ⟨true, default, default⟩
  refine
    exists_pos_mass_disagreement_of_abVisibleInvariant_predict_of_abFiberSeparation
      (Z := Bool) (k := k) (G := G) hinv
      (μ := μ) (target := boolZProjectionRule (k := k)) i
      (u := u) (v := v) ?_ ?_ ?_ ?_
  · rfl
  · simp [boolZProjectionRule, u, v]
  · simpa [u] using hfalse
  · simpa [v] using htrue

/-- Factor-through concrete hidden-`z` readout support obstruction. -/
theorem exists_pos_mass_disagreement_of_factorsThrough_abVisibleData_predict_boolZProjectionRule
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Bool k Index}
    {H : ABVisibleSwitchedFamily k Index}
    (hfactor : G.FactorsThrough abVisibleData H)
    {μ : PMF (ExactVisiblePostSwitchSurface Bool k)}
    (i : Index)
    (hfalse : μ ⟨false, default, default⟩ ≠ 0)
    (htrue : μ ⟨true, default, default⟩ ≠ 0) :
    ∃ x, μ x ≠ 0 ∧ G.predict i x ≠ boolZProjectionRule (k := k) x := by
  exact
    exists_pos_mass_disagreement_of_abVisibleInvariant_predict_boolZProjectionRule
      (k := k)
      (abVisibleInvariant_of_factorsThrough_abVisibleData
        (Z := Bool) (k := k) hfactor)
      (μ := μ) i hfalse htrue

/-- Concrete agreement-mass form for the hidden-`z` readout target. -/
theorem agreementMass_lt_one_of_abVisibleInvariant_predict_boolZProjectionRule
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Bool k Index}
    (hinv : ABVisibleInvariant (Z := Bool) (k := k) G)
    {μ : PMF (ExactVisiblePostSwitchSurface Bool k)}
    (i : Index)
    (hfalse : μ ⟨false, default, default⟩ ≠ 0)
    (htrue : μ ⟨true, default, default⟩ ≠ 0) :
    agreementMass μ (boolZProjectionRule (k := k)) (G.predict i) < 1 := by
  rcases
      exists_pos_mass_disagreement_of_abVisibleInvariant_predict_boolZProjectionRule
        (k := k) hinv (μ := μ) i hfalse htrue with ⟨x, hxμ, hxdis⟩
  exact agreementMass_lt_one_of_pos_mass_disagreement
    (μ := μ) (target := boolZProjectionRule (k := k)) (predict := G.predict i)
    hxμ hxdis

/-- Factor-through concrete agreement-mass form for the hidden-`z` readout
target. -/
theorem agreementMass_lt_one_of_factorsThrough_abVisibleData_predict_boolZProjectionRule
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Bool k Index}
    {H : ABVisibleSwitchedFamily k Index}
    (hfactor : G.FactorsThrough abVisibleData H)
    {μ : PMF (ExactVisiblePostSwitchSurface Bool k)}
    (i : Index)
    (hfalse : μ ⟨false, default, default⟩ ≠ 0)
    (htrue : μ ⟨true, default, default⟩ ≠ 0) :
    agreementMass μ (boolZProjectionRule (k := k)) (G.predict i) < 1 := by
  exact
    agreementMass_lt_one_of_abVisibleInvariant_predict_boolZProjectionRule
      (k := k)
      (abVisibleInvariant_of_factorsThrough_abVisibleData
        (Z := Bool) (k := k) hfactor)
      (μ := μ) i hfalse htrue

/-- Family-level concrete agreement-mass obstruction for the hidden-`z`
readout target. -/
theorem not_exists_agreementMass_eq_one_boolZProjectionRule_of_abVisibleInvariant
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Bool k Index}
    (hinv : ABVisibleInvariant (Z := Bool) (k := k) G)
    {μ : PMF (ExactVisiblePostSwitchSurface Bool k)}
    (hfalse : μ ⟨false, default, default⟩ ≠ 0)
    (htrue : μ ⟨true, default, default⟩ ≠ 0) :
    ¬ ∃ i, agreementMass μ (boolZProjectionRule (k := k)) (G.predict i) = 1 := by
  rintro ⟨i, hi⟩
  exact
    (ne_of_lt
      (agreementMass_lt_one_of_abVisibleInvariant_predict_boolZProjectionRule
        (k := k) hinv (μ := μ) i hfalse htrue))
      hi

/-- Factor-through family-level concrete agreement-mass obstruction for the
hidden-`z` readout target. -/
theorem not_exists_agreementMass_eq_one_boolZProjectionRule_of_factorsThrough_abVisibleData
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Bool k Index}
    {H : ABVisibleSwitchedFamily k Index}
    (hfactor : G.FactorsThrough abVisibleData H)
    {μ : PMF (ExactVisiblePostSwitchSurface Bool k)}
    (hfalse : μ ⟨false, default, default⟩ ≠ 0)
    (htrue : μ ⟨true, default, default⟩ ≠ 0) :
    ¬ ∃ i, agreementMass μ (boolZProjectionRule (k := k)) (G.predict i) = 1 := by
  exact
    not_exists_agreementMass_eq_one_boolZProjectionRule_of_abVisibleInvariant
      (k := k)
      (abVisibleInvariant_of_factorsThrough_abVisibleData
        (Z := Bool) (k := k) hfactor)
      (μ := μ) hfalse htrue

theorem exists_ne_exactVisiblePostSwitchSurface_of_same_abVisibleData
    [Nontrivial Z] :
    ∃ u v : ExactVisiblePostSwitchSurface Z k, u ≠ v ∧ abVisibleData u = abVisibleData v := by
  classical
  obtain ⟨z₀, z₁, hz⟩ := exists_pair_ne Z
  let a : BitVec k := default
  let b : BitVec k := default
  refine ⟨⟨z₀, a, b⟩, ⟨z₁, a, b⟩, ?_, rfl⟩
  intro h
  apply hz
  simpa [a, b] using congrArg (fun u : ExactVisiblePostSwitchSurface Z k => u.z) h

theorem not_surjective_predict_of_abVisibleInvariant_of_nontrivial
    [Nontrivial Z]
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hinv : ABVisibleInvariant (Z := Z) (k := k) G) :
    ¬ Function.Surjective G.predict := by
  classical
  obtain ⟨u, v, huv, hab⟩ :=
    exists_ne_exactVisiblePostSwitchSurface_of_same_abVisibleData (Z := Z) (k := k)
  let rule : ExactVisiblePostSwitchSurface Z k → Bool :=
    fun w => if h : w = u then true else false
  intro hsurj
  rcases hsurj rule with ⟨i, hi⟩
  have hu : G.predict i u = true := by
    simpa [rule] using congrFun hi u
  have hvu : v ≠ u := by
    intro h
    exact huv h.symm
  have hv : G.predict i v = false := by
    simpa [rule, hvu] using congrFun hi v
  have hs : G.predict i u = G.predict i v := hinv i u v hab
  have htf : true = false := hu.symm.trans <| hs.trans hv
  cases htf

theorem not_surjective_predict_of_factorsThrough_abVisibleData_of_nontrivial
    [Nontrivial Z]
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    (hfactor : G.FactorsThrough abVisibleData H) :
    ¬ Function.Surjective G.predict := by
  exact
    not_surjective_predict_of_abVisibleInvariant_of_nontrivial
      (Z := Z) (k := k)
      (abVisibleInvariant_of_factorsThrough_abVisibleData
        (Z := Z) (k := k) hfactor)

end Core

section RouteWrappers

variable {Z : Type*} {r k : ℕ} {Index : Type*}

section

variable [Inhabited Z] [Nontrivial Z]

theorem SharedABAffineFeatureTargetData.not_surjective_predict_of_nontrivial
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h : SharedABAffineFeatureTargetData (Z := Z) (r := r) (k := k) (Index := Index) G) :
    ¬ Function.Surjective G.predict := by
  exact
    not_surjective_predict_of_abVisibleInvariant_of_nontrivial
      (Z := Z) (k := k) h.invariant

theorem SharedABSparseThresholdTargetData.not_surjective_predict_of_nontrivial
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h : SharedABSparseThresholdTargetData (Z := Z) (r := r) (k := k) (Index := Index) G) :
    ¬ Function.Surjective G.predict := by
  exact
    not_surjective_predict_of_abVisibleInvariant_of_nontrivial
      (Z := Z) (k := k) h.invariant

theorem SharedABDecisionListTargetData.not_surjective_predict_of_nontrivial
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h : SharedABDecisionListTargetData (Z := Z) (r := r) (k := k) (Index := Index) G) :
    ¬ Function.Surjective G.predict := by
  exact
    not_surjective_predict_of_abVisibleInvariant_of_nontrivial
      (Z := Z) (k := k) h.invariant

theorem CanonicalABDecisionListCandidateData.not_surjective_predict_of_nontrivial
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h : CanonicalABDecisionListCandidateData (Z := Z) (k := k) (Index := Index) G) :
    ¬ Function.Surjective G.predict := by
  exact
    not_surjective_predict_of_abVisibleInvariant_of_nontrivial
      (Z := Z) (k := k) h.invariant

omit [Inhabited Z] in
theorem canonicalABDecisionList_not_surjective_of_nontrivial
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hinv : ABVisibleInvariant (Z := Z) (k := k) G) :
    ¬ Function.Surjective G.predict := by
  exact
    not_surjective_predict_of_abVisibleInvariant_of_nontrivial
      (Z := Z) (k := k) hinv

omit [Inhabited Z] in
theorem canonicalABCodeFamily_not_surjective_of_nontrivial
    (codes : Index → SharedAffineDecisionListCode (k + k)) :
    ¬ Function.Surjective
        (canonicalABCodeFamily (Z := Z) (k := k) codes).predict := by
  exact
    not_surjective_predict_of_abVisibleInvariant_of_nontrivial
      (Z := Z) (k := k)
      (canonicalABCodeFamily_invariant (Z := Z) (k := k) codes)

end

section BoolTargetWrappers

variable {k : ℕ} {Index : Type*}

theorem CanonicalABDecisionListCandidateData.not_exists_predict_eq_boolZProjectionRule
    {G : ExactVisibleSwitchedFamily Bool k Index}
    (h : CanonicalABDecisionListCandidateData (Z := Bool) (k := k) (Index := Index) G) :
    ¬ ∃ i, G.predict i = boolZProjectionRule (k := k) := by
  exact not_exists_predict_eq_boolZProjectionRule_of_abVisibleInvariant
    (k := k) h.invariant

theorem canonicalABCodeFamily_not_exists_predict_eq_boolZProjectionRule
    (codes : Index → SharedAffineDecisionListCode (k + k)) :
    ¬ ∃ i,
        (canonicalABCodeFamily (Z := Bool) (k := k) codes).predict i =
          boolZProjectionRule (k := k) := by
  exact not_exists_predict_eq_boolZProjectionRule_of_abVisibleInvariant
    (k := k)
    (canonicalABCodeFamily_invariant (Z := Bool) (k := k) codes)

theorem CanonicalABDecisionListCandidateData.exists_pos_mass_disagreement_boolZProjectionRule
    {G : ExactVisibleSwitchedFamily Bool k Index}
    (h : CanonicalABDecisionListCandidateData (Z := Bool) (k := k) (Index := Index) G)
    {μ : PMF (ExactVisiblePostSwitchSurface Bool k)}
    (i : Index)
    (hfalse : μ ⟨false, default, default⟩ ≠ 0)
    (htrue : μ ⟨true, default, default⟩ ≠ 0) :
    ∃ x, μ x ≠ 0 ∧ G.predict i x ≠ boolZProjectionRule (k := k) x := by
  exact
    exists_pos_mass_disagreement_of_abVisibleInvariant_predict_boolZProjectionRule
      (k := k) h.invariant (μ := μ) i hfalse htrue

theorem canonicalABCodeFamily_exists_pos_mass_disagreement_boolZProjectionRule
    (codes : Index → SharedAffineDecisionListCode (k + k))
    {μ : PMF (ExactVisiblePostSwitchSurface Bool k)}
    (i : Index)
    (hfalse : μ ⟨false, default, default⟩ ≠ 0)
    (htrue : μ ⟨true, default, default⟩ ≠ 0) :
    ∃ x, μ x ≠ 0 ∧
      (canonicalABCodeFamily (Z := Bool) (k := k) codes).predict i x ≠
        boolZProjectionRule (k := k) x := by
  exact
    exists_pos_mass_disagreement_of_abVisibleInvariant_predict_boolZProjectionRule
      (k := k)
      (canonicalABCodeFamily_invariant (Z := Bool) (k := k) codes)
      (μ := μ) i hfalse htrue

theorem CanonicalABDecisionListCandidateData.agreementMass_lt_one_boolZProjectionRule
    {G : ExactVisibleSwitchedFamily Bool k Index}
    (h : CanonicalABDecisionListCandidateData (Z := Bool) (k := k) (Index := Index) G)
    {μ : PMF (ExactVisiblePostSwitchSurface Bool k)}
    (i : Index)
    (hfalse : μ ⟨false, default, default⟩ ≠ 0)
    (htrue : μ ⟨true, default, default⟩ ≠ 0) :
    agreementMass μ (boolZProjectionRule (k := k)) (G.predict i) < 1 := by
  exact
    agreementMass_lt_one_of_abVisibleInvariant_predict_boolZProjectionRule
      (k := k) h.invariant (μ := μ) i hfalse htrue

theorem canonicalABCodeFamily_agreementMass_lt_one_boolZProjectionRule
    (codes : Index → SharedAffineDecisionListCode (k + k))
    {μ : PMF (ExactVisiblePostSwitchSurface Bool k)}
    (i : Index)
    (hfalse : μ ⟨false, default, default⟩ ≠ 0)
    (htrue : μ ⟨true, default, default⟩ ≠ 0) :
    agreementMass μ (boolZProjectionRule (k := k))
      ((canonicalABCodeFamily (Z := Bool) (k := k) codes).predict i) < 1 := by
  exact
    agreementMass_lt_one_of_abVisibleInvariant_predict_boolZProjectionRule
      (k := k)
      (canonicalABCodeFamily_invariant (Z := Bool) (k := k) codes)
      (μ := μ) i hfalse htrue

theorem CanonicalABDecisionListCandidateData.not_exists_agreementMass_eq_one_boolZProjectionRule
    {G : ExactVisibleSwitchedFamily Bool k Index}
    (h : CanonicalABDecisionListCandidateData (Z := Bool) (k := k) (Index := Index) G)
    {μ : PMF (ExactVisiblePostSwitchSurface Bool k)}
    (hfalse : μ ⟨false, default, default⟩ ≠ 0)
    (htrue : μ ⟨true, default, default⟩ ≠ 0) :
    ¬ ∃ i, agreementMass μ (boolZProjectionRule (k := k)) (G.predict i) = 1 := by
  exact
    not_exists_agreementMass_eq_one_boolZProjectionRule_of_abVisibleInvariant
      (k := k) h.invariant (μ := μ) hfalse htrue

theorem canonicalABCodeFamily_not_exists_agreementMass_eq_one_boolZProjectionRule
    (codes : Index → SharedAffineDecisionListCode (k + k))
    {μ : PMF (ExactVisiblePostSwitchSurface Bool k)}
    (hfalse : μ ⟨false, default, default⟩ ≠ 0)
    (htrue : μ ⟨true, default, default⟩ ≠ 0) :
    ¬ ∃ i, agreementMass μ (boolZProjectionRule (k := k))
      ((canonicalABCodeFamily (Z := Bool) (k := k) codes).predict i) = 1 := by
  exact
    not_exists_agreementMass_eq_one_boolZProjectionRule_of_abVisibleInvariant
      (k := k)
      (canonicalABCodeFamily_invariant (Z := Bool) (k := k) codes)
      (μ := μ) hfalse htrue

end BoolTargetWrappers

section

variable [Inhabited Z] [Fintype Z] [Nontrivial Z]

theorem SharedABAffineFeatureRecoveryData.not_surjective_predict_of_nontrivial
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedABAffineFeatureRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q) :
    ¬ Function.Surjective G.predict := by
  exact h.targetData.not_surjective_predict_of_nontrivial

theorem SharedABSparseThresholdRecoveryData.not_surjective_predict_of_nontrivial
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedABSparseThresholdRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q) :
    ¬ Function.Surjective G.predict := by
  exact h.targetData.not_surjective_predict_of_nontrivial

theorem SharedABDecisionListRecoveryData.not_surjective_predict_of_nontrivial
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {features : Fin r → AffineColumnCode (k + k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedABDecisionListRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index)
        μ features G q) :
    ¬ Function.Surjective G.predict := by
  exact h.targetData.not_surjective_predict_of_nontrivial

theorem SharedExactABAffineFeatureERMRecoveryData.not_surjective_predict_of_nontrivial
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactABAffineFeatureERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q) :
    ¬ Function.Surjective G.predict := by
  exact h.targetData.not_surjective_predict_of_nontrivial

theorem SharedExactABSparseThresholdERMRecoveryData.not_surjective_predict_of_nontrivial
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactABSparseThresholdERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q) :
    ¬ Function.Surjective G.predict := by
  exact h.targetData.not_surjective_predict_of_nontrivial

theorem SharedExactABERMRecoveryData.not_surjective_predict_of_nontrivial
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactABERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ G q) :
    ¬ Function.Surjective G.predict := by
  exact h.targetData.not_surjective_predict_of_nontrivial

end

end RouteWrappers

end Mettapedia.Computability.PNP
