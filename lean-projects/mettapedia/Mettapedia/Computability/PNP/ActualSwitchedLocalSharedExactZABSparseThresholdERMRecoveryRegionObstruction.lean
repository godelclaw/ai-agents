import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoveryData
import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleMajorityObstruction
import Mettapedia.Computability.PNP.BadCodeAgreementObstruction
import Mettapedia.Computability.PNP.SharedExactZABSparseThresholdInjectiveLiveness
import Mathlib.Tactic

/-!
# P vs NP route obstruction: injective sparse-threshold recovery packets cannot
  hide large agreement regions

`SharedExactZABSparseThresholdInjectiveLiveness.lean` proved that once
`zfeat` is injective, the shared exact sparse-threshold class can realize every
Boolean rule on the exact visible surface.

This file pushes that expressivity directly against the manuscript-facing
recovery layer.  Fix one target predictor from an actual switched-local sparse-
threshold recovery packet and any proper finite region `region` of the exact
visible surface.  Because the shared class is fully expressive on the injective
branch, Lean can build a bad code that agrees with the target everywhere on
`region` and flips at one visible point outside `region`.

Therefore the advertised bad-code agreement threshold `q` must dominate the
sampling mass of every proper region:

* `μ(region) ≤ q`.

So any proper region of mass `> q` is already a direct obstruction to the
injective sparse-threshold recovery route.  This subsumes the earlier atomic
and cardinality corollaries, but applies to arbitrary finite regions and
arbitrary measures.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

universe u v w

section Helpers

variable {U : Type u} [DecidableEq U]

/-- Flip one chosen point of a Boolean rule and leave every other input
unchanged. -/
def flipAt (reference : U → Bool) (x₀ : U) : U → Bool :=
  fun x => if x = x₀ then Bool.not (reference x) else reference x

@[simp] theorem flipAt_apply_self (reference : U → Bool) (x₀ : U) :
    flipAt reference x₀ x₀ = Bool.not (reference x₀) := by
  simp [flipAt]

@[simp] theorem flipAt_apply_of_ne (reference : U → Bool) {x x₀ : U} (h : x ≠ x₀) :
    flipAt reference x₀ x = reference x := by
  simp [flipAt, h]

end Helpers

section ExactVisible

variable {Z : Type v} [Fintype Z] {p r k : ℕ} {Index : Type u}
variable {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
variable {zfeat : Z → BitVec r}
variable {G : ExactVisibleSwitchedFamily Z k Index} {q : ℝ≥0∞}

namespace SharedExactZABSparseThresholdERMRecoveryData

/-- Any finite region on which one bad code agrees with the target already has
mass at most the advertised agreement threshold `q`. -/
theorem regionMass_le_of_badCode_agrees_on
    (h :
      SharedExactZABSparseThresholdERMRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (i : Index)
    (c :
      (sharedExactZABSparseThresholdAffineBitFamily Z zfeat h.features).toEncodedFamily.BadCodes
        (G.predict i))
    (region : Finset (ExactVisiblePostSwitchSurface Z k))
    (hagree :
      ∀ x, x ∈ region →
        (sharedExactZABSparseThresholdAffineBitFamily Z zfeat h.features).decode c.1 x =
          G.predict i x) :
    region.sum (fun x => μ x) ≤ q := by
  exact
    (sharedExactZABSparseThresholdAffineBitFamily Z zfeat h.features).regionMass_le_of_badCode_agrees_on
      (target := G.predict i) (h.agreement_le i) c region hagree

end SharedExactZABSparseThresholdERMRecoveryData

end ExactVisible

namespace ActualSwitchedLocalInterface

section Abstract

variable {Z : Type v} [Fintype Z] {k : ℕ} {Index : Type u} {Block : Type w}
variable {T : ActualSwitchedLocalInterface Z k Index Block} {r : ℕ}
variable {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
variable {zfeat : Z → BitVec r} {q : ℝ≥0∞}

namespace SharedExactZABSparseThresholdERMRecoveryData

/-- On the injective branch, every proper finite region of the exact visible
surface already has mass at most `q`.  The witness bad code is constructed by
flipping the chosen target predictor at one point outside the region. -/
theorem regionMass_le_of_injective_zfeat_of_not_mem
    (h : SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q)
    (hinj : Function.Injective zfeat)
    (hwidth : 0 < r + (k + k))
    (i : Index)
    (region : Finset (ExactVisiblePostSwitchSurface Z k))
    {x₀ : ExactVisiblePostSwitchSurface Z k}
    (hx₀ : x₀ ∉ region) :
    region.sum (fun x => μ x) ≤ q := by
  classical
  let target := T.predictorFamily.predict i
  let altered : ExactVisiblePostSwitchSurface Z k → Bool := flipAt target x₀
  have hreal :
      RealizedBySharedExactZABSparseThresholdAffineFamily
        (Z := Z)
        (p := allAffinePointBlockFeatureCount (r + (k + k)))
        (r := r) (k := k)
        zfeat
        (allAffinePointBlockFeatures (r + (k + k)))
        (fullExactVisibleRuleFamily Z k) :=
    fullExactVisibleRuleFamily_realizedBySharedExactZABSparseThresholdAffineFamily_of_injective_zfeat
      (Z := Z) (r := r) (k := k) zfeat hinj hwidth
  rcases hreal altered with ⟨code, hcode⟩
  let rawCode :=
    sharedSparseThresholdCodeEquivBitCode
      (allAffinePointBlockFeatureCount (r + (k + k))) code
  have hdecode :
      (sharedExactZABSparseThresholdAffineBitFamily
        Z
        zfeat
        (allAffinePointBlockFeatures (r + (k + k)))).decode rawCode =
        altered := by
    calc
      (sharedExactZABSparseThresholdAffineBitFamily
        Z
        zfeat
        (allAffinePointBlockFeatures (r + (k + k)))).decode rawCode
          =
        sharedExactZABSparseThresholdAffinePredict
          (Z := Z)
          (p := allAffinePointBlockFeatureCount (r + (k + k)))
          (r := r) (k := k)
          zfeat
          (allAffinePointBlockFeatures (r + (k + k)))
          code := by
            exact
              sharedExactZABSparseThresholdAffineBitFamily_decode_code
                (Z := Z)
                (p := allAffinePointBlockFeatureCount (r + (k + k)))
                (r := r) (k := k)
                zfeat
                (allAffinePointBlockFeatures (r + (k + k)))
                code
      _ = altered := hcode.symm
  have hbad :
      (sharedExactZABSparseThresholdAffineBitFamily
        Z
        zfeat
        (allAffinePointBlockFeatures (r + (k + k)))).decode rawCode ≠
        target := by
    intro hEq
    have hflip :
        altered x₀ ≠ target x₀ := by
      rw [show altered x₀ = Bool.not (target x₀) by
        simp [altered]]
      simp
    apply hflip
    calc
      altered x₀
          =
        (sharedExactZABSparseThresholdAffineBitFamily
          Z
          zfeat
          (allAffinePointBlockFeatures (r + (k + k)))).decode rawCode x₀ := by
            exact (congrFun hdecode x₀).symm
      _ = target x₀ := congrFun hEq x₀
  let c :
      (sharedExactZABSparseThresholdAffineBitFamily
        Z
        zfeat
        (allAffinePointBlockFeatures (r + (k + k)))).toEncodedFamily.BadCodes target :=
    ⟨rawCode, hbad⟩
  have hagree :
      ∀ x, x ∈ region →
        (sharedExactZABSparseThresholdAffineBitFamily
          Z
          zfeat
          (allAffinePointBlockFeatures (r + (k + k)))).decode c.1 x =
          target x := by
    intro x hx
    have hxne : x ≠ x₀ := by
      intro hxx₀
      subst hxx₀
      exact hx₀ hx
    calc
      (sharedExactZABSparseThresholdAffineBitFamily
        Z
        zfeat
        (allAffinePointBlockFeatures (r + (k + k)))).decode c.1 x
          = altered x := congrFun hdecode x
      _ = target x := by
        simpa [altered] using flipAt_apply_of_ne target hxne
  exact
    h.exactVisibleRecoveryData.regionMass_le_of_badCode_agrees_on
      i c region hagree

/-- Therefore any proper region of mass above `q` directly blocks the injective
actual-local sparse-threshold recovery packet. -/
theorem not_nonempty_of_injective_zfeat_of_not_mem_of_lt_regionMass
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (zfeat : Z → BitVec r)
    (hinj : Function.Injective zfeat)
    (hwidth : 0 < r + (k + k))
    (i : Index)
    (region : Finset (ExactVisiblePostSwitchSurface Z k))
    {x₀ : ExactVisiblePostSwitchSurface Z k}
    (hx₀ : x₀ ∉ region)
    (hmass : q < region.sum (fun x => μ x)) :
    ¬ Nonempty (SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q) := by
  rintro ⟨h⟩
  exact not_le_of_gt hmass <|
    h.regionMass_le_of_injective_zfeat_of_not_mem hinj hwidth i region hx₀

/-- Existential form: any proper region whose complement is nonempty and whose
mass exceeds `q` blocks the injective actual-local sparse-threshold recovery
route. -/
theorem not_nonempty_of_injective_zfeat_of_exists_not_mem_of_lt_regionMass
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (zfeat : Z → BitVec r)
    (hinj : Function.Injective zfeat)
    (hwidth : 0 < r + (k + k))
    (i : Index)
    (region : Finset (ExactVisiblePostSwitchSurface Z k))
    (hout : ∃ x₀ : ExactVisiblePostSwitchSurface Z k, x₀ ∉ region)
    (hmass : q < region.sum (fun x => μ x)) :
    ¬ Nonempty (SharedExactZABSparseThresholdERMRecoveryData μ T zfeat q) := by
  rcases hout with ⟨x₀, hx₀⟩
  exact
    not_nonempty_of_injective_zfeat_of_not_mem_of_lt_regionMass
      (μ := μ) T zfeat hinj hwidth i region hx₀ hmass

end SharedExactZABSparseThresholdERMRecoveryData

/-- Full-rule corollary: on the injective branch, any proper finite region of
the exact visible surface whose mass is above `q` kills the manuscript-facing
full-rule sparse-threshold recovery packet. -/
theorem fullRuleActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_injective_zfeat_of_exists_not_mem_of_lt_regionMass
    (zfeat : Z → BitVec r)
    (hinj : Function.Injective zfeat)
    (hwidth : 0 < r + (k + k))
    (region : Finset (ExactVisiblePostSwitchSurface Z k))
    (hout : ∃ x₀ : ExactVisiblePostSwitchSurface Z k, x₀ ∉ region)
    (hmass : q < region.sum (fun x => μ x)) :
    ¬ Nonempty
        (SharedExactZABSparseThresholdERMRecoveryData
          μ
          (fullRuleActualSwitchedLocalInterface Z k)
          zfeat
          q) := by
  exact
    SharedExactZABSparseThresholdERMRecoveryData.not_nonempty_of_injective_zfeat_of_exists_not_mem_of_lt_regionMass
      (μ := μ)
      (T := fullRuleActualSwitchedLocalInterface Z k)
      zfeat hinj hwidth
      (i := fun _ => false)
      region hout hmass

/-- Bounded-sample corollary: the same proper-region mass obstruction blocks
the bounded sample plug-in-majority endpoint on the injective branch. -/
theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_injective_zfeat_of_exists_not_mem_of_lt_regionMass
    (sampleBound : ℕ)
    (zfeat : Z → BitVec r)
    (hinj : Function.Injective zfeat)
    (hwidth : 0 < r + (k + k))
    (region : Finset (ExactVisiblePostSwitchSurface Z k))
    (hout : ∃ x₀ : ExactVisiblePostSwitchSurface Z k, x₀ ∉ region)
    (hmass : q < region.sum (fun x => μ x)) :
    ¬ Nonempty
        (SharedExactZABSparseThresholdERMRecoveryData
          μ
          (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound)
          zfeat
          q) := by
  exact
    SharedExactZABSparseThresholdERMRecoveryData.not_nonempty_of_injective_zfeat_of_exists_not_mem_of_lt_regionMass
      (μ := μ)
      (T := boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound)
      zfeat hinj hwidth
      (i := ⟨[], by simp⟩)
      region hout hmass

end Abstract

end ActualSwitchedLocalInterface

end Mettapedia.Computability.PNP
