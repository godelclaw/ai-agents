import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityContinuationTarget
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Concrete BKM-Style Continuation Target

This file sharpens the concrete uniform-vorticity continuation surface to a
closer-to-BKM time-integrated envelope criterion.  Instead of requiring a
uniform-in-time pointwise vorticity bound, it asks for an explicit scalar
envelope `Ω(t)` dominating the vorticity on the slab `0 ≤ t ≤ T` and integrable
over that time interval.

The file still does not prove continuation.  It only states the next concrete
criterion on top of the explicit `ℝ × ℝ^3` Navier--Stokes theorem surface and
shows that a full global theorem would subsume it.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section BKMContinuation

/-- A scalar time-envelope for the vorticity on the slab `0 ≤ t ≤ T`. -/
def vorticityEnvelopeOn
    (u : NSVelocityField) (T : ℝ) (Ω : NSTime → ℝ) : Prop :=
  (∀ t, 0 ≤ t → t ≤ T → 0 ≤ Ω t) ∧
    ∀ t x, 0 ≤ t → t ≤ T → ‖spatialVorticity u t x‖ ≤ Ω t

/-- A BKM-style time-integrable envelope on `0 ≤ t ≤ T`. -/
def integrableVorticityEnvelopeOn
    (Ω : NSTime → ℝ) (T B : ℝ) : Prop :=
  0 ≤ B ∧
    MeasureTheory.IntegrableOn Ω (Set.Icc 0 T) ∧
    (∫ t in Set.Icc 0 T, Ω t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) ≤ B

/-- The BKM envelope data does not change the pointwise pressure-residual
necessary condition inherited from the underlying finite-time witness. -/
theorem BKMData_momentumPressureResidual_vorticity_zero_on
    {ν T : ℝ} {u₀ : NSInitialVelocity}
    {W : ExplicitFiniteTimeRegularityWitness ν u₀ T}
    (_hBKM : ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
      vorticityEnvelopeOn W.velocity T Ω ∧
        integrableVorticityEnvelopeOn Ω T B)
    {t : NSTime} {x : NSSpace} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    spatialVorticity (momentumPressureResidual ν W.velocity) t x = 0 :=
  ExplicitFiniteTimeRegularityWitness.spatialVorticity_momentumPressureResidual_zero_on
    (ν := ν) (T := T) (u₀ := u₀) W (t := t) (x := x) ht0 htT

/-- The BKM residual-curl necessary condition can be transported across a
chosen velocity equality. -/
theorem BKMData_momentumPressureResidual_vorticity_of_velocity_eq_zero_on
    {ν T : ℝ} {u₀ : NSInitialVelocity} {u : NSVelocityField}
    {W : ExplicitFiniteTimeRegularityWitness ν u₀ T}
    (hWvel : W.velocity = u)
    (_hBKM : ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
      vorticityEnvelopeOn W.velocity T Ω ∧
        integrableVorticityEnvelopeOn Ω T B)
    {t : NSTime} {x : NSSpace} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    spatialVorticity (momentumPressureResidual ν u) t x = 0 := by
  simpa [← hWvel] using
    (ExplicitFiniteTimeRegularityWitness.spatialVorticity_momentumPressureResidual_zero_on
      (ν := ν) (T := T) (u₀ := u₀) W (t := t) (x := x) ht0 htT)

/-- BKM packaging cannot hide a non-curl-free pressure residual on the certified
slab.  The envelope layer adds no escape hatch once the underlying finite-time
witness velocity is impossible. -/
theorem not_exists_BKMData_velocity_of_momentumPressureResidual_vorticity_ne_zero_on
    {ν T : ℝ} {u₀ : NSInitialVelocity} {u : NSVelocityField}
    (hcurl : ∃ t : NSTime, ∃ x : NSSpace,
      0 ≤ t ∧ t ≤ T ∧
        spatialVorticity (momentumPressureResidual ν u) t x ≠ 0) :
    ¬ ∃ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
      W.velocity = u ∧
        ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
          vorticityEnvelopeOn W.velocity T Ω ∧
            integrableVorticityEnvelopeOn Ω T B := by
  rintro ⟨W, hWvel, Ω, B, hEnv, hInt⟩
  rcases hcurl with ⟨t, x, ht0, htT, hne⟩
  exact hne
    (BKMData_momentumPressureResidual_vorticity_of_velocity_eq_zero_on
      (ν := ν) (T := T) (u₀ := u₀) (u := u) (W := W) hWvel
      ⟨Ω, B, hEnv, hInt⟩ (t := t) (x := x) ht0 htT)

/-- Explicit BKM-style continuation clause: a finite-time smooth witness with a
time-integrable vorticity envelope on `0 ≤ t ≤ T` extends to a global smooth
solution. -/
def ExplicitBKMContinuationClause
    (ν : ℝ) (u₀ : NSInitialVelocity) (T : ℝ) : Prop :=
  0 < ν →
    smoothInitialVelocityData u₀ →
      (∀ x, initialSpatialDivergence u₀ x = 0) →
        ∀ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
          (∃ Ω : NSTime → ℝ, ∃ B : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T B) →
            ExplicitConcreteNavierStokesGlobalOutput ν u₀

/-- Global BKM-style continuation target built from the explicit continuation
clause above. -/
def ExplicitBKMContinuationTarget : Prop :=
  ∀ ν : ℝ, ∀ u₀ : NSInitialVelocity, ∀ T : ℝ,
    ExplicitBKMContinuationClause ν u₀ T

/-- Repaired BKM-style continuation clause: the input side is restricted to
smooth divergence-free initial data with finite initial kinetic energy. -/
def ExplicitFiniteEnergyBKMContinuationClause
    (ν : ℝ) (u₀ : NSInitialVelocity) (T : ℝ) : Prop :=
  0 < ν →
    smoothInitialVelocityData u₀ →
      (∀ x, initialSpatialDivergence u₀ x = 0) →
        finiteInitialKineticEnergy u₀ →
          ∀ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
            (∃ Ω : NSTime → ℝ, ∃ B : ℝ,
              vorticityEnvelopeOn W.velocity T Ω ∧
                integrableVorticityEnvelopeOn Ω T B) →
              ExplicitConcreteNavierStokesGlobalOutput ν u₀

/-- Global repaired BKM-style continuation target built from the finite-energy
continuation clause. -/
def ExplicitFiniteEnergyBKMContinuationTarget : Prop :=
  ∀ ν : ℝ, ∀ u₀ : NSInitialVelocity, ∀ T : ℝ,
    ExplicitFiniteEnergyBKMContinuationClause ν u₀ T

/-- Corrected repaired BKM continuation target: only nonnegative horizons are
admissible. This removes the negative-horizon empty-slab loophole while keeping
the intended finite-energy BKM continuation surface. -/
def ExplicitFiniteEnergyBKMContinuationTargetOnNonnegHorizons : Prop :=
  ∀ ν : ℝ, ∀ u₀ : NSInitialVelocity, ∀ ⦃T : ℝ⦄,
    0 ≤ T → ExplicitFiniteEnergyBKMContinuationClause ν u₀ T

/-- Any explicit whole-space regularity clause immediately yields the
corresponding fixed-horizon BKM continuation clause on the same datum. -/
theorem ExplicitConcreteNavierStokesRegularityClause_implies_ExplicitBKMContinuationClause
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (h : ExplicitConcreteNavierStokesRegularityClause ν u₀) :
    ExplicitBKMContinuationClause ν u₀ T := by
  intro hν hsmooth hdiv _W _hEnv
  exact h hν hsmooth hdiv

/-- The repaired explicit whole-space regularity clause likewise yields the
repaired fixed-horizon BKM continuation clause on the same datum. -/
theorem
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_implies_ExplicitFiniteEnergyBKMContinuationClause
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause ν u₀) :
    ExplicitFiniteEnergyBKMContinuationClause ν u₀ T := by
  intro hν hsmooth hdiv hfinite _W _hEnv
  exact h hν hsmooth hdiv hfinite

/-- The same explicit whole-space regularity clause also yields the whole
fixed-datum family of BKM continuation clauses, one for each horizon. -/
theorem ExplicitConcreteNavierStokesRegularityClause_implies_ExplicitBKMContinuationClause_allHorizons
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (h : ExplicitConcreteNavierStokesRegularityClause ν u₀) :
    ∀ T : ℝ, ExplicitBKMContinuationClause ν u₀ T := by
  intro T
  exact
    ExplicitConcreteNavierStokesRegularityClause_implies_ExplicitBKMContinuationClause
      (T := T) h

/-- Likewise, the repaired explicit whole-space regularity clause yields the
whole fixed-datum family of repaired BKM continuation clauses. -/
theorem
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_implies_ExplicitFiniteEnergyBKMContinuationClause_allHorizons
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause ν u₀) :
    ∀ T : ℝ, ExplicitFiniteEnergyBKMContinuationClause ν u₀ T := by
  intro T
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_implies_ExplicitFiniteEnergyBKMContinuationClause
      (T := T) h

/-- The repaired BKM continuation clause is vacuous outside the finite-energy
input domain: if `u₀` fails that hypothesis, the clause holds for purely
logical reasons. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_of_not_finiteInitialKineticEnergy
    {ν T : ℝ} {u₀ : NSInitialVelocity}
    (hfinite : ¬ finiteInitialKineticEnergy u₀) :
    ExplicitFiniteEnergyBKMContinuationClause ν u₀ T := by
  intro _hν _hsmooth _hdiv hE _W _hEnv
  exact False.elim (hfinite hE)

/-- Direct zero-field envelope for BKM data on every slab. -/
theorem vorticityEnvelopeOn_zero
    (T : ℝ) :
    vorticityEnvelopeOn (0 : NSVelocityField) T (fun _ : NSTime => 0) := by
  refine ⟨?_, ?_⟩
  · intro t ht0 htT
    simp
  · intro t x ht0 htT
    change ‖spatialVorticity (0 : NSVelocityField) t x‖ ≤ 0
    simp [spatialVorticity_zero]

/-- Integrable zero envelope with zero integral bound on every slab. -/
theorem integrableVorticityEnvelopeOn_zero
    (T : ℝ) :
    integrableVorticityEnvelopeOn (fun _ : NSTime => 0) T 0 := by
  refine ⟨le_rfl, ?_, ?_⟩
  · have hs : (MeasureTheory.volume (Set.Icc 0 T)) ≠ (⊤ : ENNReal) := by
      rw [Real.volume_Icc]
      exact ne_of_lt ENNReal.ofReal_lt_top
    exact
      (MeasureTheory.integrableOn_const (s := Set.Icc 0 T)
        (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ)) (C := (0 : ℝ)) (hs := hs))
  · simp

/-- A constant nonnegative envelope on a nonnegative slab `0 ≤ t ≤ T` is
integrable with the explicit linear bound `T * B`. -/
theorem integrableVorticityEnvelopeOn_const
    {T B : ℝ}
    (hT : 0 ≤ T)
    (hB : 0 ≤ B) :
    integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) := by
  refine ⟨mul_nonneg hT hB, ?_, ?_⟩
  · have hs : (MeasureTheory.volume (Set.Icc 0 T)) ≠ (⊤ : ENNReal) := by
      rw [Real.volume_Icc]
      exact ne_of_lt ENNReal.ofReal_lt_top
    exact
      (MeasureTheory.integrableOn_const (s := Set.Icc 0 T)
        (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ)) (C := B) (hs := hs))
  · rw [MeasureTheory.setIntegral_const, smul_eq_mul, MeasureTheory.measureReal_def,
      Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal hT]

/-- Vorticity envelopes add on a fixed slab, provided both velocity fields have
pointwise differentiable spatial slices there. -/
theorem vorticityEnvelopeOn_add
    {u v : NSVelocityField} {T : ℝ} {Ω Ω' : NSTime → ℝ}
    (hu : ∀ t x, 0 ≤ t → t ≤ T → DifferentiableAt ℝ (fun y : NSSpace => u t y) x)
    (hv : ∀ t x, 0 ≤ t → t ≤ T → DifferentiableAt ℝ (fun y : NSSpace => v t y) x)
    (hΩ : vorticityEnvelopeOn u T Ω)
    (hΩ' : vorticityEnvelopeOn v T Ω') :
    vorticityEnvelopeOn (u + v) T (fun t => Ω t + Ω' t) := by
  rcases hΩ with ⟨hΩnonneg, hΩbound⟩
  rcases hΩ' with ⟨hΩ'nonneg, hΩ'bound⟩
  refine ⟨?_, ?_⟩
  · intro t ht0 htT
    exact add_nonneg (hΩnonneg t ht0 htT) (hΩ'nonneg t ht0 htT)
  · intro t x ht0 htT
    rw [spatialVorticity_add (u := u) (v := v) (t := t) (x := x)
      (hu t x ht0 htT) (hv t x ht0 htT)]
    calc
      ‖spatialVorticity u t x + spatialVorticity v t x‖ ≤
          ‖spatialVorticity u t x‖ + ‖spatialVorticity v t x‖ := norm_add_le _ _
      _ ≤ Ω t + Ω' t := add_le_add (hΩbound t x ht0 htT) (hΩ'bound t x ht0 htT)

/-- Vorticity envelopes are stable under constant velocity rescaling: if
`‖ω_u(t,x)‖ ≤ Ω(t)` on a slab, then
`‖ω_{a•u}(t,x)‖ ≤ |a| * Ω(t)` on the same slab. -/
theorem vorticityEnvelopeOn_const_smul
    {u : NSVelocityField} {T : ℝ} {Ω : NSTime → ℝ}
    (a : ℝ)
    (hΩ : vorticityEnvelopeOn u T Ω) :
    vorticityEnvelopeOn (a • u) T (fun t => |a| * Ω t) := by
  rcases hΩ with ⟨hΩnonneg, hΩbound⟩
  refine ⟨?_, ?_⟩
  · intro t ht0 htT
    exact mul_nonneg (abs_nonneg a) (hΩnonneg t ht0 htT)
  · intro t x ht0 htT
    have hsmul :
        spatialVorticity (a • u) t x = a • spatialVorticity u t x := by
      ext i
      fin_cases i <;>
        simp [spatialVorticity, spatialDerivativeComponent_const_smul, mul_sub]
    rw [hsmul]
    calc
      ‖a • spatialVorticity u t x‖ = |a| * ‖spatialVorticity u t x‖ := by
        simp [norm_smul, Real.norm_eq_abs]
      _ ≤ |a| * Ω t := mul_le_mul_of_nonneg_left (hΩbound t x ht0 htT) (abs_nonneg a)

/-- Vorticity envelopes are stable under sign flip of the velocity field. -/
theorem vorticityEnvelopeOn_neg
    {u : NSVelocityField} {T : ℝ} {Ω : NSTime → ℝ}
    (hΩ : vorticityEnvelopeOn u T Ω) :
    vorticityEnvelopeOn (-u) T Ω := by
  simpa using vorticityEnvelopeOn_const_smul (a := (-1 : ℝ)) (u := u) (T := T) (Ω := Ω) hΩ

/-- Vorticity envelope domination is monotone in the envelope function on a
fixed slab. -/
theorem vorticityEnvelopeOn_mono
    {u : NSVelocityField} {T : ℝ} {Ω Ω' : NSTime → ℝ}
    (hΩ : vorticityEnvelopeOn u T Ω)
    (hΩΩ' : ∀ t, 0 ≤ t → t ≤ T → Ω t ≤ Ω' t) :
    vorticityEnvelopeOn u T Ω' := by
  rcases hΩ with ⟨hnonneg, hbound⟩
  refine ⟨?_, ?_⟩
  · intro t ht0 htT
    exact le_trans (hnonneg t ht0 htT) (hΩΩ' t ht0 htT)
  · intro t x ht0 htT
    exact le_trans (hbound t x ht0 htT) (hΩΩ' t ht0 htT)

/-- Smooth space-time velocity fields satisfy the differentiability hypotheses
needed for envelope addition on each fixed time slice. -/
theorem vorticityEnvelopeOn_add_of_smooth
    {u v : NSVelocityField} {T : ℝ} {Ω Ω' : NSTime → ℝ}
    (hu : smoothSpaceTimeVelocity u)
    (hv : smoothSpaceTimeVelocity v)
    (hΩ : vorticityEnvelopeOn u T Ω)
    (hΩ' : vorticityEnvelopeOn v T Ω') :
    vorticityEnvelopeOn (u + v) T (fun t => Ω t + Ω' t) := by
  exact vorticityEnvelopeOn_add
    (hu := fun t x _ht0 _htT => smoothSpaceTimeVelocity_differentiableAt_spatialSlice hu t x)
    (hv := fun t x _ht0 _htT => smoothSpaceTimeVelocity_differentiableAt_spatialSlice hv t x)
    hΩ hΩ'

/-- Smooth slab envelopes are stable under subtraction, with the same additive
bound shape as for addition. -/
theorem vorticityEnvelopeOn_sub_of_smooth
    {u v : NSVelocityField} {T : ℝ} {Ω Ω' : NSTime → ℝ}
    (hu : smoothSpaceTimeVelocity u)
    (hv : smoothSpaceTimeVelocity v)
    (hΩ : vorticityEnvelopeOn u T Ω)
    (hΩ' : vorticityEnvelopeOn v T Ω') :
    vorticityEnvelopeOn (u - v) T (fun t => Ω t + Ω' t) := by
  simpa [sub_eq_add_neg] using
    (vorticityEnvelopeOn_add_of_smooth
      (u := u) (v := -v) (T := T) (Ω := Ω) (Ω' := Ω')
      hu (smoothSpaceTimeVelocity_neg hv) hΩ (vorticityEnvelopeOn_neg hΩ'))

/-- Integrable vorticity envelope bounds are monotone in the scalar integral
bound parameter. -/
theorem integrableVorticityEnvelopeOn_mono
    {Ω : NSTime → ℝ} {T B B' : ℝ}
    (hInt : integrableVorticityEnvelopeOn Ω T B)
    (hBB' : B ≤ B') :
    integrableVorticityEnvelopeOn Ω T B' := by
  rcases hInt with ⟨hB, hΩ, hI⟩
  refine ⟨le_trans hB hBB', hΩ, le_trans hI hBB'⟩

/-- Integrable vorticity envelopes are stable under multiplication by a
nonnegative constant. -/
theorem integrableVorticityEnvelopeOn_const_mul
    {Ω : NSTime → ℝ} {T B a : ℝ}
    (ha : 0 ≤ a)
    (hInt : integrableVorticityEnvelopeOn Ω T B) :
    integrableVorticityEnvelopeOn (fun t => a * Ω t) T (a * B) := by
  rcases hInt with ⟨hB, hΩ, hI⟩
  refine ⟨mul_nonneg ha hB, ?_, ?_⟩
  · simpa [MeasureTheory.IntegrableOn] using hΩ.const_mul a
  · rw [MeasureTheory.integral_const_mul]
    exact mul_le_mul_of_nonneg_left hI ha

/-- Integrable vorticity envelopes are stable under constant velocity rescaling
via the absolute-value factor `|a|`. -/
theorem integrableVorticityEnvelopeOn_abs_const_smul
    {Ω : NSTime → ℝ} {T B a : ℝ}
    (hInt : integrableVorticityEnvelopeOn Ω T B) :
    integrableVorticityEnvelopeOn (fun t => |a| * Ω t) T (|a| * B) := by
  exact integrableVorticityEnvelopeOn_const_mul (a := |a|) (abs_nonneg a) hInt

/-- Integrable vorticity envelopes add, and the corresponding scalar integral
bound adds with them. -/
theorem integrableVorticityEnvelopeOn_add
    {Ω Ω' : NSTime → ℝ} {T B B' : ℝ}
    (hInt : integrableVorticityEnvelopeOn Ω T B)
    (hInt' : integrableVorticityEnvelopeOn Ω' T B') :
    integrableVorticityEnvelopeOn (fun t => Ω t + Ω' t) T (B + B') := by
  rcases hInt with ⟨hB, hΩ, hI⟩
  rcases hInt' with ⟨hB', hΩ', hI'⟩
  refine ⟨add_nonneg hB hB', hΩ.integrable.add hΩ'.integrable, ?_⟩
  calc
    (∫ t in Set.Icc 0 T, (Ω t + Ω' t) ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) =
        (∫ t in Set.Icc 0 T, Ω t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) +
          ∫ t in Set.Icc 0 T, Ω' t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
      simpa [MeasureTheory.IntegrableOn] using
        (MeasureTheory.integral_add hΩ.integrable hΩ'.integrable)
    _ ≤ B + B' := add_le_add hI hI'

/-- Smooth BKM envelope data package for the sum field `u + v`: the concrete
envelope functions add, and so do the corresponding finite integral bounds. -/
theorem BKMEnvelopeData_add_of_smooth
    {u v : NSVelocityField} {T B B' : ℝ} {Ω Ω' : NSTime → ℝ}
    (hu : smoothSpaceTimeVelocity u)
    (hv : smoothSpaceTimeVelocity v)
    (hΩ : vorticityEnvelopeOn u T Ω)
    (hInt : integrableVorticityEnvelopeOn Ω T B)
    (hΩ' : vorticityEnvelopeOn v T Ω')
    (hInt' : integrableVorticityEnvelopeOn Ω' T B') :
    vorticityEnvelopeOn (u + v) T (fun t => Ω t + Ω' t) ∧
      integrableVorticityEnvelopeOn (fun t => Ω t + Ω' t) T (B + B') := by
  exact ⟨vorticityEnvelopeOn_add_of_smooth hu hv hΩ hΩ',
    integrableVorticityEnvelopeOn_add hInt hInt'⟩

/-- Smooth BKM envelope data package for the difference field `u - v`: the
pointwise envelope remains the sum `Ω + Ω'`, and the finite integral bounds add
in the same way. -/
theorem BKMEnvelopeData_sub_of_smooth
    {u v : NSVelocityField} {T B B' : ℝ} {Ω Ω' : NSTime → ℝ}
    (hu : smoothSpaceTimeVelocity u)
    (hv : smoothSpaceTimeVelocity v)
    (hΩ : vorticityEnvelopeOn u T Ω)
    (hInt : integrableVorticityEnvelopeOn Ω T B)
    (hΩ' : vorticityEnvelopeOn v T Ω')
    (hInt' : integrableVorticityEnvelopeOn Ω' T B') :
    vorticityEnvelopeOn (u - v) T (fun t => Ω t + Ω' t) ∧
      integrableVorticityEnvelopeOn (fun t => Ω t + Ω' t) T (B + B') := by
  exact ⟨vorticityEnvelopeOn_sub_of_smooth hu hv hΩ hΩ',
    integrableVorticityEnvelopeOn_add hInt hInt'⟩

/-- Smooth BKM envelope data package for a linear combination `a • u + b • v`:
the pointwise envelope scales by `|a|` and `|b|`, and the finite integral
bound scales in the same way. -/
theorem BKMEnvelopeData_linearCombination_of_smooth
    {u v : NSVelocityField} {T B B' : ℝ} {Ω Ω' : NSTime → ℝ}
    (hu : smoothSpaceTimeVelocity u)
    (hv : smoothSpaceTimeVelocity v)
    (hΩ : vorticityEnvelopeOn u T Ω)
    (hInt : integrableVorticityEnvelopeOn Ω T B)
    (hΩ' : vorticityEnvelopeOn v T Ω')
    (hInt' : integrableVorticityEnvelopeOn Ω' T B')
    (a b : ℝ) :
    vorticityEnvelopeOn (a • u + b • v) T (fun t => |a| * Ω t + |b| * Ω' t) ∧
      integrableVorticityEnvelopeOn (fun t => |a| * Ω t + |b| * Ω' t) T
        (|a| * B + |b| * B') := by
  have hΩa : vorticityEnvelopeOn (a • u) T (fun t => |a| * Ω t) :=
    vorticityEnvelopeOn_const_smul (a := a) hΩ
  have hInta :
      integrableVorticityEnvelopeOn (fun t => |a| * Ω t) T (|a| * B) :=
    integrableVorticityEnvelopeOn_abs_const_smul (a := a) hInt
  have hΩb : vorticityEnvelopeOn (b • v) T (fun t => |b| * Ω' t) :=
    vorticityEnvelopeOn_const_smul (a := b) hΩ'
  have hIntb :
      integrableVorticityEnvelopeOn (fun t => |b| * Ω' t) T (|b| * B') :=
    integrableVorticityEnvelopeOn_abs_const_smul (a := b) hInt'
  simpa using
    (BKMEnvelopeData_add_of_smooth
      (u := a • u) (v := b • v) (T := T)
      (Ω := fun t => |a| * Ω t) (Ω' := fun t => |b| * Ω' t)
      (B := |a| * B) (B' := |b| * B')
      (smoothSpaceTimeVelocity_const_smul a hu)
      (smoothSpaceTimeVelocity_const_smul b hv)
      hΩa hInta hΩb hIntb)

/-- Integrable vorticity-envelope data restrict to any shorter slab
`0 ≤ t ≤ T'` with `T' ≤ T`; the restricted integral itself gives an explicit
admissible scalar bound. -/
theorem integrableVorticityEnvelopeOn_restrict
    {Ω : NSTime → ℝ} {T T' B : ℝ}
    (hInt : integrableVorticityEnvelopeOn Ω T B)
    (hT : T' ≤ T) :
    integrableVorticityEnvelopeOn Ω T'
      (|∫ t in Set.Icc 0 T', Ω t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)|) := by
  rcases hInt with ⟨_hB, hΩ, _hI⟩
  refine ⟨abs_nonneg _, ?_, ?_⟩
  · exact hΩ.mono_set (Set.Icc_subset_Icc le_rfl hT)
  · exact le_abs_self _

/-- If an envelope is nonnegative on the slab, then restricting to a shorter
slab admits the sharper restricted-integral bound, without an absolute value. -/
theorem vorticityEnvelopeOn.integrable_restrict
    {u : NSVelocityField} {T T' B : ℝ} {Ω : NSTime → ℝ}
    (hV : vorticityEnvelopeOn u T Ω)
    (hInt : integrableVorticityEnvelopeOn Ω T B)
    (hT : T' ≤ T) :
    integrableVorticityEnvelopeOn Ω T'
      (∫ t in Set.Icc 0 T', Ω t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) := by
  rcases hV with ⟨hnonneg, _hbound⟩
  rcases hInt with ⟨_hB, hΩInt, _hI⟩
  refine ⟨?_, ?_, le_rfl⟩
  · have hnonneg_ae :
      ∀ᵐ t ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Icc 0 T')),
        0 ≤ Ω t := by
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
      exact MeasureTheory.ae_of_all _ (fun t ht => hnonneg t ht.1 (le_trans ht.2 hT))
    exact MeasureTheory.integral_nonneg_of_ae hnonneg_ae
  · exact hΩInt.mono_set (Set.Icc_subset_Icc le_rfl hT)

/-- A vorticity envelope valid on a slab `0 ≤ t ≤ T` restricts to any shorter
slab `0 ≤ t ≤ T'` with `T' ≤ T`. -/
theorem vorticityEnvelopeOn_restrict
    {u : NSVelocityField} {T T' : ℝ} {Ω : NSTime → ℝ}
    (hΩ : vorticityEnvelopeOn u T Ω)
    (hT : T' ≤ T) :
    vorticityEnvelopeOn u T' Ω := by
  rcases hΩ with ⟨hnonneg, hbound⟩
  refine ⟨?_, ?_⟩
  · intro t ht0 htT'
    exact hnonneg t ht0 (le_trans htT' hT)
  · intro t x ht0 htT'
    exact hbound t x ht0 (le_trans htT' hT)

/-- Combined restriction of concrete BKM envelope data to a shorter slab. -/
theorem BKMEnvelopeData_restrict
    {u : NSVelocityField} {T T' B : ℝ} {Ω : NSTime → ℝ}
    (hV : vorticityEnvelopeOn u T Ω)
    (hInt : integrableVorticityEnvelopeOn Ω T B)
    (hT : T' ≤ T) :
    vorticityEnvelopeOn u T' Ω ∧
      integrableVorticityEnvelopeOn Ω T'
        (∫ t in Set.Icc 0 T', Ω t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) := by
  exact ⟨vorticityEnvelopeOn_restrict hV hT, hV.integrable_restrict hInt hT⟩

/-- Smooth BKM envelope data for a linear combination restrict directly to any
shorter slab `0 ≤ t ≤ T' ≤ T`. -/
theorem BKMEnvelopeData_linearCombination_restrict_of_smooth
    {u v : NSVelocityField} {T T' B B' : ℝ} {Ω Ω' : NSTime → ℝ}
    (hu : smoothSpaceTimeVelocity u)
    (hv : smoothSpaceTimeVelocity v)
    (hΩ : vorticityEnvelopeOn u T Ω)
    (hInt : integrableVorticityEnvelopeOn Ω T B)
    (hΩ' : vorticityEnvelopeOn v T Ω')
    (hInt' : integrableVorticityEnvelopeOn Ω' T B')
    (a b : ℝ)
    (hT : T' ≤ T) :
    vorticityEnvelopeOn (a • u + b • v) T' (fun t => |a| * Ω t + |b| * Ω' t) ∧
      integrableVorticityEnvelopeOn (fun t => |a| * Ω t + |b| * Ω' t) T'
        (∫ t in Set.Icc 0 T', (|a| * Ω t + |b| * Ω' t)
          ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) := by
  have hData :
      vorticityEnvelopeOn (a • u + b • v) T (fun t => |a| * Ω t + |b| * Ω' t) ∧
        integrableVorticityEnvelopeOn (fun t => |a| * Ω t + |b| * Ω' t) T
          (|a| * B + |b| * B') := by
    exact BKMEnvelopeData_linearCombination_of_smooth hu hv hΩ hInt hΩ' hInt' a b
  exact BKMEnvelopeData_restrict hData.1 hData.2 hT

/-- A uniform slab vorticity bound yields an explicit integrable BKM envelope by
taking `Ω` constant in time. -/
theorem uniformVorticityBoundUpTo_implies_BKMEnvelope
    {u : NSVelocityField} {T B : ℝ}
    (hω : uniformVorticityBoundUpTo u T B) :
    ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
      vorticityEnvelopeOn u T Ω ∧
        integrableVorticityEnvelopeOn Ω T Bint := by
  rcases hω with ⟨hB, hbound⟩
  refine ⟨fun _ => B, ∫ t in Set.Icc 0 T, B ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro t ht0 htT
      simpa using hB
    · intro t x ht0 htT
      simpa using hbound t x ht0 htT
  · refine ⟨?_, ?_, ?_⟩
    · exact MeasureTheory.integral_nonneg (fun _ => hB)
    · have hs : (MeasureTheory.volume (Set.Icc 0 T)) ≠ (⊤ : ENNReal) := by
        rw [Real.volume_Icc]
        exact ne_of_lt ENNReal.ofReal_lt_top
      exact
        (MeasureTheory.integrableOn_const (s := Set.Icc 0 T)
          (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ)) (C := B) (hs := hs))
    · change
        (∫ t in Set.Icc 0 T, B ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) ≤
          ∫ t in Set.Icc 0 T, B ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)
      exact le_rfl

/-- On a nonnegative slab, a uniform vorticity bound yields the explicit
constant BKM envelope `Ω(t) = B` with linear integral bound `T * B`. -/
theorem uniformVorticityBoundUpTo_implies_constantBKMEnvelope
    {u : NSVelocityField} {T B : ℝ}
    (hT : 0 ≤ T)
    (hω : uniformVorticityBoundUpTo u T B) :
    vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) := by
  rcases hω with ⟨hB, hbound⟩
  refine ⟨?_, integrableVorticityEnvelopeOn_const hT hB⟩
  refine ⟨?_, ?_⟩
  · intro t ht0 htT'
    simpa using hB
  · intro t x ht0 htT'
    simpa using hbound t x ht0 htT'

/-- Two smooth uniform slab bounds combine into one explicit BKM envelope for
the summed field. -/
theorem uniformVorticityBoundUpTo_add_implies_BKMEnvelope
    {u v : NSVelocityField} {T B B' : ℝ}
    (hu : smoothSpaceTimeVelocity u)
    (hv : smoothSpaceTimeVelocity v)
    (hω : uniformVorticityBoundUpTo u T B)
    (hω' : uniformVorticityBoundUpTo v T B') :
    ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
      vorticityEnvelopeOn (u + v) T Ω ∧
        integrableVorticityEnvelopeOn Ω T Bint := by
  exact uniformVorticityBoundUpTo_implies_BKMEnvelope
    (u := u + v) (T := T) (B := B + B')
    (uniformVorticityBoundUpTo_add hu hv hω hω')

/-- On a nonnegative slab, two smooth uniform slab bounds combine into the
explicit constant BKM envelope for the summed field. -/
theorem uniformVorticityBoundUpTo_add_implies_constantBKMEnvelope
    {u v : NSVelocityField} {T B B' : ℝ}
    (hT : 0 ≤ T)
    (hu : smoothSpaceTimeVelocity u)
    (hv : smoothSpaceTimeVelocity v)
    (hω : uniformVorticityBoundUpTo u T B)
    (hω' : uniformVorticityBoundUpTo v T B') :
    vorticityEnvelopeOn (u + v) T (fun _ : NSTime => B + B') ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B + B') T (T * (B + B')) := by
  exact uniformVorticityBoundUpTo_implies_constantBKMEnvelope
    (u := u + v) (T := T) (B := B + B') hT
    (uniformVorticityBoundUpTo_add hu hv hω hω')

/-- Two smooth uniform slab bounds combine into explicit BKM-envelope data for
the difference field `u - v`. -/
theorem uniformVorticityBoundUpTo_sub_implies_BKMEnvelope
    {u v : NSVelocityField} {T B B' : ℝ}
    (hu : smoothSpaceTimeVelocity u)
    (hv : smoothSpaceTimeVelocity v)
    (hω : uniformVorticityBoundUpTo u T B)
    (hω' : uniformVorticityBoundUpTo v T B') :
    ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
      vorticityEnvelopeOn (u - v) T Ω ∧
        integrableVorticityEnvelopeOn Ω T Bint := by
  exact uniformVorticityBoundUpTo_implies_BKMEnvelope
    (u := u - v) (T := T) (B := B + B')
    (uniformVorticityBoundUpTo_sub hu hv hω hω')

/-- On a nonnegative slab, two smooth uniform slab bounds combine into the
explicit constant BKM envelope for the difference field `u - v`. -/
theorem uniformVorticityBoundUpTo_sub_implies_constantBKMEnvelope
    {u v : NSVelocityField} {T B B' : ℝ}
    (hT : 0 ≤ T)
    (hu : smoothSpaceTimeVelocity u)
    (hv : smoothSpaceTimeVelocity v)
    (hω : uniformVorticityBoundUpTo u T B)
    (hω' : uniformVorticityBoundUpTo v T B') :
    vorticityEnvelopeOn (u - v) T (fun _ : NSTime => B + B') ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B + B') T (T * (B + B')) := by
  exact uniformVorticityBoundUpTo_implies_constantBKMEnvelope
    (u := u - v) (T := T) (B := B + B') hT
    (uniformVorticityBoundUpTo_sub hu hv hω hω')

/-- Two smooth uniform slab bounds combine into explicit BKM-envelope data for
the linear combination `a • u + b • v`. -/
theorem uniformVorticityBoundUpTo_linearCombination_implies_BKMEnvelope
    {u v : NSVelocityField} {T B B' : ℝ}
    (hu : smoothSpaceTimeVelocity u)
    (hv : smoothSpaceTimeVelocity v)
    (hω : uniformVorticityBoundUpTo u T B)
    (hω' : uniformVorticityBoundUpTo v T B')
    (a b : ℝ) :
    ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
      vorticityEnvelopeOn (a • u + b • v) T Ω ∧
        integrableVorticityEnvelopeOn Ω T Bint := by
  exact uniformVorticityBoundUpTo_implies_BKMEnvelope
    (u := a • u + b • v) (T := T) (B := |a| * B + |b| * B')
    (uniformVorticityBoundUpTo_linearCombination hu hv hω hω' a b)

/-- On a nonnegative slab, two smooth uniform slab bounds combine into the
explicit constant BKM envelope for the linear combination `a • u + b • v`. -/
theorem uniformVorticityBoundUpTo_linearCombination_implies_constantBKMEnvelope
    {u v : NSVelocityField} {T B B' : ℝ}
    (hT : 0 ≤ T)
    (hu : smoothSpaceTimeVelocity u)
    (hv : smoothSpaceTimeVelocity v)
    (hω : uniformVorticityBoundUpTo u T B)
    (hω' : uniformVorticityBoundUpTo v T B')
    (a b : ℝ) :
    vorticityEnvelopeOn (a • u + b • v) T
        (fun _ : NSTime => |a| * B + |b| * B') ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => |a| * B + |b| * B') T
        (T * (|a| * B + |b| * B')) := by
  exact uniformVorticityBoundUpTo_implies_constantBKMEnvelope
    (u := a • u + b • v) (T := T) (B := |a| * B + |b| * B') hT
    (uniformVorticityBoundUpTo_linearCombination hu hv hω hω' a b)

/-- The uniform-to-BKM envelope conversion also restricts to any shorter slab. -/
theorem uniformVorticityBoundUpTo_implies_BKMEnvelope_restrict
    {u : NSVelocityField} {T T' B : ℝ}
    (hω : uniformVorticityBoundUpTo u T B)
    (hT : T' ≤ T) :
    ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
      vorticityEnvelopeOn u T' Ω ∧
        integrableVorticityEnvelopeOn Ω T' Bint := by
  rcases uniformVorticityBoundUpTo_implies_BKMEnvelope (u := u) (T := T) (B := B) hω with
    ⟨Ω, Bint, hEnv, hInt⟩
  refine ⟨Ω, |∫ t in Set.Icc 0 T', Ω t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)|, ?_⟩
  exact ⟨vorticityEnvelopeOn_restrict hEnv hT, integrableVorticityEnvelopeOn_restrict hInt hT⟩

/-- On a nonnegative shorter slab, the uniform-to-BKM conversion restricts to
the explicit constant envelope `Ω(t) = B`. -/
theorem uniformVorticityBoundUpTo_implies_constantBKMEnvelope_restrict
    {u : NSVelocityField} {T T' B : ℝ}
    (hT' : 0 ≤ T')
    (hω : uniformVorticityBoundUpTo u T B)
    (hT : T' ≤ T) :
    vorticityEnvelopeOn u T' (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T' (T' * B) := by
  exact uniformVorticityBoundUpTo_implies_constantBKMEnvelope
    (u := u) (T := T') (B := B) hT'
    (uniformVorticityBoundUpTo_restrict hω hT)

/-- Uniform linear-combination control on a large slab restricts to explicit
BKM-envelope data on every shorter slab. -/
theorem uniformVorticityBoundUpTo_linearCombination_implies_BKMEnvelope_restrict
    {u v : NSVelocityField} {T T' B B' : ℝ}
    (hu : smoothSpaceTimeVelocity u)
    (hv : smoothSpaceTimeVelocity v)
    (hω : uniformVorticityBoundUpTo u T B)
    (hω' : uniformVorticityBoundUpTo v T B')
    (a b : ℝ)
    (hT : T' ≤ T) :
    ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
      vorticityEnvelopeOn (a • u + b • v) T' Ω ∧
        integrableVorticityEnvelopeOn Ω T' Bint := by
  exact uniformVorticityBoundUpTo_implies_BKMEnvelope_restrict
    (u := a • u + b • v) (T := T) (T' := T')
    (B := |a| * B + |b| * B')
    (uniformVorticityBoundUpTo_linearCombination hu hv hω hω' a b) hT

/-- On a nonnegative shorter slab, uniform linear-combination control on a
large slab restricts to the explicit constant BKM envelope. -/
theorem uniformVorticityBoundUpTo_linearCombination_implies_constantBKMEnvelope_restrict
    {u v : NSVelocityField} {T T' B B' : ℝ}
    (hT' : 0 ≤ T')
    (hu : smoothSpaceTimeVelocity u)
    (hv : smoothSpaceTimeVelocity v)
    (hω : uniformVorticityBoundUpTo u T B)
    (hω' : uniformVorticityBoundUpTo v T B')
    (a b : ℝ)
    (hT : T' ≤ T) :
    vorticityEnvelopeOn (a • u + b • v) T'
        (fun _ : NSTime => |a| * B + |b| * B') ∧
      integrableVorticityEnvelopeOn
        (fun _ : NSTime => |a| * B + |b| * B') T'
        (T' * (|a| * B + |b| * B')) := by
  exact uniformVorticityBoundUpTo_implies_constantBKMEnvelope_restrict
    (u := a • u + b • v) (T := T) (T' := T')
    (B := |a| * B + |b| * B') hT'
    (uniformVorticityBoundUpTo_linearCombination hu hv hω hω' a b) hT

/-- A constant velocity field carries the explicit zero BKM envelope on every
nonnegative slab. -/
theorem constantVelocityField_has_constantBKMEnvelope
    (c : NSSpace) (T : ℝ)
    (hT : 0 ≤ T) :
    vorticityEnvelopeOn (constantVelocityField c) T (fun _ : NSTime => 0) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => 0) T 0 := by
  simpa using
    (uniformVorticityBoundUpTo_implies_constantBKMEnvelope
      (u := constantVelocityField c) (T := T) (B := 0) hT
      (uniformVorticityBoundUpTo_constantVelocityField c T))

/-- The steady linear shear field carries the explicit constant BKM envelope
`Ω(t) = |a|` on every nonnegative slab, with integral bound `T * |a|`. -/
theorem linearShearVelocityField_has_constantBKMEnvelope
    (a T : ℝ)
    (hT : 0 ≤ T) :
    vorticityEnvelopeOn (linearShearVelocityField a) T (fun _ : NSTime => |a|) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => |a|) T (T * |a|) := by
  exact uniformVorticityBoundUpTo_implies_constantBKMEnvelope
    (u := linearShearVelocityField a) (T := T) (B := |a|) hT
    (uniformVorticityBoundUpTo_linearShearVelocityField a T)

/-- The steady field `u(t,x) = (a * x₁, 0, b)` carries the same explicit
constant BKM envelope `Ω(t) = |a|` on every nonnegative slab. -/
theorem linearShearVerticalDriftVelocityField_has_constantBKMEnvelope
    (a b T : ℝ)
    (hT : 0 ≤ T) :
    vorticityEnvelopeOn (linearShearVerticalDriftVelocityField a b) T
        (fun _ : NSTime => |a|) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => |a|) T (T * |a|) := by
  exact uniformVorticityBoundUpTo_implies_constantBKMEnvelope
    (u := linearShearVerticalDriftVelocityField a b) (T := T) (B := |a|) hT
    (uniformVorticityBoundUpTo_linearShearVerticalDriftVelocityField a b T)

/-- The steady field `u(t,x) = (a * x₁, b, 0)` carries the same explicit
constant BKM envelope `Ω(t) = |a|` on every nonnegative slab. -/
theorem linearShearHorizontalDriftVelocityField_has_constantBKMEnvelope
    (a b T : ℝ)
    (hT : 0 ≤ T) :
    vorticityEnvelopeOn (linearShearHorizontalDriftVelocityField a b) T
        (fun _ : NSTime => |a|) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => |a|) T (T * |a|) := by
  exact uniformVorticityBoundUpTo_implies_constantBKMEnvelope
    (u := linearShearHorizontalDriftVelocityField a b) (T := T) (B := |a|) hT
    (uniformVorticityBoundUpTo_linearShearHorizontalDriftVelocityField a b T)

/-- The steady field `u(t,x) = (a * x₁, b, c)` carries the same explicit
constant BKM envelope `Ω(t) = |a|` on every nonnegative slab. -/
theorem linearShearFullDriftVelocityField_has_constantBKMEnvelope
    (a b c T : ℝ)
    (hT : 0 ≤ T) :
    vorticityEnvelopeOn (linearShearFullDriftVelocityField a b c) T
        (fun _ : NSTime => |a|) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => |a|) T (T * |a|) := by
  exact uniformVorticityBoundUpTo_implies_constantBKMEnvelope
    (u := linearShearFullDriftVelocityField a b c) (T := T) (B := |a|) hT
    (uniformVorticityBoundUpTo_linearShearFullDriftVelocityField a b c T)

/-- The natural damped heat-shear vorticity envelope.  It keeps the time
dependence that is lost when one immediately passes to the coarser constant
slab bound `|a * k|`. -/
def heatShearExpVorticityEnvelope (ν a k : ℝ) : NSTime → ℝ :=
  fun t : NSTime => |a| * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * |k|

/-- Exact integral of the damped heat-shear vorticity envelope on `0 ≤ t ≤ T`.
For the nondegenerate damped branch (`ν > 0`, `k ≠ 0`) this is the sharp
scalar BKM budget instead of the coarser `T * |a * k|` budget. -/
def heatShearExpVorticityEnvelopeExactIntegralBound (ν a k T : ℝ) : ℝ :=
  |a| * |k| * ((1 - Real.exp (-(ν * k ^ (2 : ℕ)) * T)) / (ν * k ^ (2 : ℕ)))

/-- On a nonnegative-viscosity, nonnegative-time slab, the damped heat-shear
envelope is bounded by the older constant envelope `|a * k|`. -/
theorem heatShearExpVorticityEnvelope_le_const
    (ν a k T : ℝ)
    (hν : 0 ≤ ν) :
    ∀ t : NSTime, 0 ≤ t → t ≤ T →
      heatShearExpVorticityEnvelope ν a k t ≤ |a * k| := by
  intro t ht0 _htT
  have hexp_le : Real.exp (-(ν * k ^ (2 : ℕ)) * t) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have hk2 : 0 ≤ k ^ (2 : ℕ) := by positivity
    have hprod : 0 ≤ ν * k ^ (2 : ℕ) := mul_nonneg hν hk2
    nlinarith
  calc
    heatShearExpVorticityEnvelope ν a k t
        ≤ |a| * 1 * |k| := by
          dsimp [heatShearExpVorticityEnvelope]
          gcongr
    _ = |a * k| := by
          rw [abs_mul]
          ring

private theorem integral_exp_neg_mul_interval
    (lam T : ℝ) (hlam : lam ≠ 0) :
    (∫ t in (0 : ℝ)..T, Real.exp (-(lam) * t)) =
      (1 - Real.exp (-(lam) * T)) / lam := by
  have hne : (-lam) ≠ 0 := by simpa using neg_ne_zero.mpr hlam
  have hcomp := intervalIntegral.integral_comp_mul_left
    (f := fun x : ℝ => Real.exp x) (a := (0 : ℝ)) (b := T) (c := -lam) hne
  rw [integral_exp] at hcomp
  change (∫ t in (0 : ℝ)..T, (fun x : ℝ => Real.exp x) (-lam * t)) =
    (1 - Real.exp (-lam * T)) / lam
  rw [hcomp]
  simp [smul_eq_mul, Real.exp_zero, div_eq_mul_inv]
  field_simp [hlam]
  ring

/-- The damped heat-shear envelope integrates exactly to its closed-form
exponential budget on every nonnegative slab in the nondegenerate damped case. -/
theorem integral_heatShearExpVorticityEnvelope_eq_exactIntegralBound
    (ν a k T : ℝ)
    (hT : 0 ≤ T)
    (hdecay : ν * k ^ (2 : ℕ) ≠ 0) :
    (∫ t in Set.Icc 0 T, heatShearExpVorticityEnvelope ν a k t
        ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) =
      heatShearExpVorticityEnvelopeExactIntegralBound ν a k T := by
  have hset_to_interval :
      (∫ t in Set.Icc 0 T, heatShearExpVorticityEnvelope ν a k t
          ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) =
        ∫ t in (0 : ℝ)..T, heatShearExpVorticityEnvelope ν a k t := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT]
  rw [hset_to_interval]
  dsimp [heatShearExpVorticityEnvelope, heatShearExpVorticityEnvelopeExactIntegralBound]
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul]
  rw [integral_exp_neg_mul_interval (ν * k ^ (2 : ℕ)) T hdecay]
  ring

/-- The exact exponential BKM budget is an admissible integrability certificate
for the nondegenerate damped heat-shear envelope. -/
theorem integrableVorticityEnvelopeOn_heatShearExpVorticityEnvelope_exact
    (ν a k T : ℝ)
    (hν : 0 < ν)
    (hk : k ≠ 0)
    (hT : 0 ≤ T) :
    integrableVorticityEnvelopeOn
      (heatShearExpVorticityEnvelope ν a k) T
      (heatShearExpVorticityEnvelopeExactIntegralBound ν a k T) := by
  have hk2pos : 0 < k ^ (2 : ℕ) := by
    nlinarith [sq_pos_of_ne_zero hk]
  have hdecay_pos : 0 < ν * k ^ (2 : ℕ) := mul_pos hν hk2pos
  have hdecay : ν * k ^ (2 : ℕ) ≠ 0 := ne_of_gt hdecay_pos
  have hΩint :
      MeasureTheory.IntegrableOn
        (heatShearExpVorticityEnvelope ν a k) (Set.Icc 0 T) := by
    have hcont : Continuous (heatShearExpVorticityEnvelope ν a k) := by
      change Continuous
        (fun t : NSTime => |a| * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * |k|)
      continuity
    exact hcont.continuousOn.integrableOn_Icc
  have hint_eq :=
    integral_heatShearExpVorticityEnvelope_eq_exactIntegralBound ν a k T hT hdecay
  have hBnonneg : 0 ≤ heatShearExpVorticityEnvelopeExactIntegralBound ν a k T := by
    rw [← hint_eq]
    have hnonneg_ae :
        ∀ᵐ t ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Icc 0 T)),
          0 ≤ heatShearExpVorticityEnvelope ν a k t := by
      exact MeasureTheory.ae_of_all _ (fun t => by
        dsimp [heatShearExpVorticityEnvelope]
        positivity)
    exact MeasureTheory.integral_nonneg_of_ae hnonneg_ae
  refine ⟨hBnonneg, hΩint, ?_⟩
  rw [hint_eq]

/-- The damped heat-shear envelope is integrable on every nonnegative slab
when viscosity is nonnegative, with the same coarse scalar bound as the
constant envelope. -/
theorem integrableVorticityEnvelopeOn_heatShearExpVorticityEnvelope
    (ν a k T : ℝ)
    (hν : 0 ≤ ν)
    (hT : 0 ≤ T) :
    integrableVorticityEnvelopeOn
      (heatShearExpVorticityEnvelope ν a k) T (T * |a * k|) := by
  have hΩint :
      MeasureTheory.IntegrableOn
        (heatShearExpVorticityEnvelope ν a k) (Set.Icc 0 T) := by
    have hcont : Continuous (heatShearExpVorticityEnvelope ν a k) := by
      change Continuous
        (fun t : NSTime => |a| * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * |k|)
      continuity
    exact hcont.continuousOn.integrableOn_Icc
  have hconstInt :
      MeasureTheory.IntegrableOn (fun _ : NSTime => |a * k|) (Set.Icc 0 T) := by
    have hs : (MeasureTheory.volume (Set.Icc 0 T)) ≠ (⊤ : ENNReal) := by
      rw [Real.volume_Icc]
      exact ne_of_lt ENNReal.ofReal_lt_top
    exact
      (MeasureTheory.integrableOn_const (s := Set.Icc 0 T)
        (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ)) (C := |a * k|) (hs := hs))
  refine ⟨mul_nonneg hT (abs_nonneg (a * k)), hΩint, ?_⟩
  calc
    (∫ t in Set.Icc 0 T, heatShearExpVorticityEnvelope ν a k t
        ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ))
        ≤ ∫ t in Set.Icc 0 T, (fun _ : NSTime => |a * k|) t
            ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
          exact MeasureTheory.setIntegral_mono_on hΩint hconstInt measurableSet_Icc
            (fun t ht => heatShearExpVorticityEnvelope_le_const ν a k T hν t ht.1 ht.2)
    _ = T * |a * k| := by
          rw [MeasureTheory.setIntegral_const, smul_eq_mul, MeasureTheory.measureReal_def,
            Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal hT]

/-- The damped sinusoidal heat-shear field carries its sharper time-dependent
BKM envelope on every nonnegative slab when the viscosity is nonnegative. -/
theorem heatShearVelocityField_has_expBKMEnvelope
    (ν a k T : ℝ)
    (hν : 0 ≤ ν)
    (hT : 0 ≤ T) :
    vorticityEnvelopeOn (heatShearVelocityField ν a k) T
        (heatShearExpVorticityEnvelope ν a k) ∧
      integrableVorticityEnvelopeOn
        (heatShearExpVorticityEnvelope ν a k) T (T * |a * k|) := by
  refine ⟨?_, integrableVorticityEnvelopeOn_heatShearExpVorticityEnvelope ν a k T hν hT⟩
  refine ⟨?_, ?_⟩
  · intro t ht0 _htT
    dsimp [heatShearExpVorticityEnvelope]
    positivity
  · intro t x _ht0 _htT
    exact norm_spatialVorticity_heatShearVelocityField_le_exp_abs ν a k t x

/-- In the nondegenerate damped case, the sinusoidal heat-shear field carries
the same time-dependent envelope with its exact closed-form BKM budget. -/
theorem heatShearVelocityField_has_exactExpBKMEnvelope
    (ν a k T : ℝ)
    (hν : 0 < ν)
    (hk : k ≠ 0)
    (hT : 0 ≤ T) :
    vorticityEnvelopeOn (heatShearVelocityField ν a k) T
        (heatShearExpVorticityEnvelope ν a k) ∧
      integrableVorticityEnvelopeOn
        (heatShearExpVorticityEnvelope ν a k) T
        (heatShearExpVorticityEnvelopeExactIntegralBound ν a k T) := by
  refine ⟨?_, integrableVorticityEnvelopeOn_heatShearExpVorticityEnvelope_exact
    ν a k T hν hk hT⟩
  exact (heatShearVelocityField_has_expBKMEnvelope ν a k T hν.le hT).1

/-- Transported heat shear carries the same sharper time-dependent BKM
envelope as the untransported heat-shear branch. -/
theorem heatShearTransportVelocityField_has_expBKMEnvelope
    (ν a k b T : ℝ)
    (hν : 0 ≤ ν)
    (hT : 0 ≤ T) :
    vorticityEnvelopeOn (heatShearTransportVelocityField ν a k b) T
        (heatShearExpVorticityEnvelope ν a k) ∧
      integrableVorticityEnvelopeOn
        (heatShearExpVorticityEnvelope ν a k) T (T * |a * k|) := by
  refine ⟨?_, integrableVorticityEnvelopeOn_heatShearExpVorticityEnvelope ν a k T hν hT⟩
  refine ⟨?_, ?_⟩
  · intro t ht0 _htT
    dsimp [heatShearExpVorticityEnvelope]
    positivity
  · intro t x _ht0 _htT
    exact norm_spatialVorticity_heatShearTransportVelocityField_le_exp_abs ν a k b t x

/-- In the nondegenerate damped case, transported heat shear carries the exact
closed-form BKM budget for the same time-dependent envelope. -/
theorem heatShearTransportVelocityField_has_exactExpBKMEnvelope
    (ν a k b T : ℝ)
    (hν : 0 < ν)
    (hk : k ≠ 0)
    (hT : 0 ≤ T) :
    vorticityEnvelopeOn (heatShearTransportVelocityField ν a k b) T
        (heatShearExpVorticityEnvelope ν a k) ∧
      integrableVorticityEnvelopeOn
        (heatShearExpVorticityEnvelope ν a k) T
        (heatShearExpVorticityEnvelopeExactIntegralBound ν a k T) := by
  refine ⟨?_, integrableVorticityEnvelopeOn_heatShearExpVorticityEnvelope_exact
    ν a k T hν hk hT⟩
  exact (heatShearTransportVelocityField_has_expBKMEnvelope ν a k b T hν.le hT).1

/-- Transported full-drift heat shear carries the same sharper time-dependent
BKM envelope as the drift-free transported branch. -/
theorem heatShearTransportFullDriftVelocityField_has_expBKMEnvelope
    (ν a k b d c T : ℝ)
    (hν : 0 ≤ ν)
    (hT : 0 ≤ T) :
    vorticityEnvelopeOn (heatShearTransportFullDriftVelocityField ν a k b d c) T
        (heatShearExpVorticityEnvelope ν a k) ∧
      integrableVorticityEnvelopeOn
        (heatShearExpVorticityEnvelope ν a k) T (T * |a * k|) := by
  refine ⟨?_, integrableVorticityEnvelopeOn_heatShearExpVorticityEnvelope ν a k T hν hT⟩
  refine ⟨?_, ?_⟩
  · intro t ht0 _htT
    dsimp [heatShearExpVorticityEnvelope]
    positivity
  · intro t x _ht0 _htT
    exact norm_spatialVorticity_heatShearTransportFullDriftVelocityField_le_exp_abs
      ν a k b d c t x

/-- In the nondegenerate damped case, transported full-drift heat shear carries
the exact closed-form BKM budget for the same time-dependent envelope. -/
theorem heatShearTransportFullDriftVelocityField_has_exactExpBKMEnvelope
    (ν a k b d c T : ℝ)
    (hν : 0 < ν)
    (hk : k ≠ 0)
    (hT : 0 ≤ T) :
    vorticityEnvelopeOn (heatShearTransportFullDriftVelocityField ν a k b d c) T
        (heatShearExpVorticityEnvelope ν a k) ∧
      integrableVorticityEnvelopeOn
        (heatShearExpVorticityEnvelope ν a k) T
        (heatShearExpVorticityEnvelopeExactIntegralBound ν a k T) := by
  refine ⟨?_, integrableVorticityEnvelopeOn_heatShearExpVorticityEnvelope_exact
    ν a k T hν hk hT⟩
  exact
    (heatShearTransportFullDriftVelocityField_has_expBKMEnvelope
      ν a k b d c T hν.le hT).1

/-- The damped sinusoidal heat-shear field carries the explicit constant BKM
envelope `Ω(t) = |a * k|` on every nonnegative slab when the viscosity is
nonnegative. -/
theorem heatShearVelocityField_has_constantBKMEnvelope
    (ν a k T : ℝ)
    (hν : 0 ≤ ν)
    (hT : 0 ≤ T) :
    vorticityEnvelopeOn (heatShearVelocityField ν a k) T
        (fun _ : NSTime => |a * k|) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => |a * k|) T (T * |a * k|) := by
  exact uniformVorticityBoundUpTo_implies_constantBKMEnvelope
    (u := heatShearVelocityField ν a k) (T := T) (B := |a * k|) hT
    (uniformVorticityBoundUpTo_heatShearVelocityField ν a k T hν)

/-- The heat-shear family with constant streamwise drift carries the same
explicit constant BKM envelope `Ω(t) = |a * k|` on every nonnegative slab when
the viscosity is nonnegative. -/
theorem heatShearStreamwiseDriftVelocityField_has_constantBKMEnvelope
    (ν a k d T : ℝ)
    (hν : 0 ≤ ν)
    (hT : 0 ≤ T) :
    vorticityEnvelopeOn (heatShearStreamwiseDriftVelocityField ν a k d) T
        (fun _ : NSTime => |a * k|) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => |a * k|) T (T * |a * k|) := by
  exact uniformVorticityBoundUpTo_implies_constantBKMEnvelope
    (u := heatShearStreamwiseDriftVelocityField ν a k d) (T := T) (B := |a * k|) hT
    (uniformVorticityBoundUpTo_heatShearStreamwiseDriftVelocityField ν a k d T hν)

/-- The heat-shear family with vertical drift carries the same explicit
constant BKM envelope `Ω(t) = |a * k|` on every nonnegative slab when the
viscosity is nonnegative. -/
theorem heatShearVerticalDriftVelocityField_has_constantBKMEnvelope
    (ν a k c T : ℝ)
    (hν : 0 ≤ ν)
    (hT : 0 ≤ T) :
    vorticityEnvelopeOn (heatShearVerticalDriftVelocityField ν a k c) T
        (fun _ : NSTime => |a * k|) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => |a * k|) T (T * |a * k|) := by
  exact uniformVorticityBoundUpTo_implies_constantBKMEnvelope
    (u := heatShearVerticalDriftVelocityField ν a k c) (T := T) (B := |a * k|) hT
    (uniformVorticityBoundUpTo_heatShearVerticalDriftVelocityField ν a k c T hν)

/-- The heat-shear family with full constant drift carries the same explicit
constant BKM envelope `Ω(t) = |a * k|` on every nonnegative slab when the
viscosity is nonnegative. -/
theorem heatShearFullDriftVelocityField_has_constantBKMEnvelope
    (ν a k d c T : ℝ)
    (hν : 0 ≤ ν)
    (hT : 0 ≤ T) :
    vorticityEnvelopeOn (heatShearFullDriftVelocityField ν a k d c) T
        (fun _ : NSTime => |a * k|) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => |a * k|) T (T * |a * k|) := by
  exact uniformVorticityBoundUpTo_implies_constantBKMEnvelope
    (u := heatShearFullDriftVelocityField ν a k d c) (T := T) (B := |a * k|) hT
    (uniformVorticityBoundUpTo_heatShearFullDriftVelocityField ν a k d c T hν)

/-- The transported heat-shear family carries the same explicit constant BKM
envelope `Ω(t) = |a * k|` on every nonnegative slab when the viscosity is
nonnegative. -/
theorem heatShearTransportVelocityField_has_constantBKMEnvelope
    (ν a k b T : ℝ)
    (hν : 0 ≤ ν)
    (hT : 0 ≤ T) :
    vorticityEnvelopeOn (heatShearTransportVelocityField ν a k b) T
        (fun _ : NSTime => |a * k|) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => |a * k|) T (T * |a * k|) := by
  exact uniformVorticityBoundUpTo_implies_constantBKMEnvelope
    (u := heatShearTransportVelocityField ν a k b) (T := T) (B := |a * k|) hT
    (uniformVorticityBoundUpTo_heatShearTransportVelocityField ν a k b T hν)

/-- The transported full-drift heat-shear family carries the same explicit
constant BKM envelope `Ω(t) = |a * k|` on every nonnegative slab when the
viscosity is nonnegative. -/
theorem heatShearTransportFullDriftVelocityField_has_constantBKMEnvelope
    (ν a k b d c T : ℝ)
    (hν : 0 ≤ ν)
    (hT : 0 ≤ T) :
    vorticityEnvelopeOn (heatShearTransportFullDriftVelocityField ν a k b d c) T
        (fun _ : NSTime => |a * k|) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => |a * k|) T (T * |a * k|) := by
  exact uniformVorticityBoundUpTo_implies_constantBKMEnvelope
    (u := heatShearTransportFullDriftVelocityField ν a k b d c) (T := T) (B := |a * k|) hT
    (uniformVorticityBoundUpTo_heatShearTransportFullDriftVelocityField ν a k b d c T hν)

/-- Any explicit slab candidate with a uniform-vorticity bound and missing only
the bounded-energy slot can be repackaged as a BKM candidate by choosing the
constant envelope `Ω(t) = B`. -/
theorem exhibits_BKMCandidate_except_boundedEnergy_of_uniformCandidate
    {ν T : ℝ} {u₀ : NSInitialVelocity}
    (hT : 0 ≤ T)
    (h :
      ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
        smoothSpaceTimeVelocity u ∧
        smoothSpaceTimePressure p ∧
        (∀ t x, 0 ≤ t → t ≤ T →
          timeVelocityDerivative u t x + spatialConvection u t x +
              spatialPressureGradient p t x =
            ν • spatialLaplacian u t x) ∧
        (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
        MatchesInitialVelocity u₀ u ∧
        uniformVorticityBoundUpTo u T B ∧
        ¬ boundedKineticEnergyUpTo u T) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x +
            spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity u₀ u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T := by
  rcases h with ⟨u, p, B, hu, hp, hmom, hdiv, hinit, hω, hE⟩
  have hBKM :
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
        integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) :=
    uniformVorticityBoundUpTo_implies_constantBKMEnvelope
      (u := u) (T := T) (B := B) hT hω
  exact ⟨u, p, B, hu, hp, hmom, hdiv, hinit, hBKM.1, hBKM.2, hE⟩

/-- A nonzero constant velocity field is an exact smooth incompressible
Navier--Stokes candidate on every nonnegative slab with the explicit zero BKM
envelope; the only missing finite-time witness slot is bounded kinetic energy
on `ℝ^3`. -/
theorem constantVelocityField_exhibits_BKMCandidate_except_boundedEnergy
    {ν T : ℝ} {c : NSSpace}
    (hc : c ≠ 0)
    (hT : 0 ≤ T) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (constantInitialVelocity c) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T := by
  exact
    exhibits_BKMCandidate_except_boundedEnergy_of_uniformCandidate
      (u₀ := constantInitialVelocity c) hT
      (constantVelocityField_exhibits_uniformCandidate_except_boundedEnergy
        (ν := ν) (T := T) (c := c) hc hT)

/-- The same nonzero constant-field BKM candidate remains valid after adding
any smooth slice-wise zero-spatial-gradient pressure gauge. The only missing
finite-time witness slot on `ℝ^3` is still bounded kinetic energy. -/
theorem constantVelocityField_exhibits_BKMCandidate_except_boundedEnergy_addPressureOfZeroSpatialGradient
    {ν T : ℝ} {c : NSSpace}
    (hc : c ≠ 0)
    (hT : 0 ≤ T)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (constantInitialVelocity c) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T := by
  exact
    exhibits_BKMCandidate_except_boundedEnergy_of_uniformCandidate
      (u₀ := constantInitialVelocity c) hT
      (constantVelocityField_exhibits_uniformCandidate_except_boundedEnergy_addPressureOfZeroSpatialGradient
        (ν := ν) (T := T) (c := c) hc hT q hq hq_zero)

/-- Constant initial data expose the same honest BKM-side gap as the shear
families: there is an explicit smooth incompressible candidate with an
integrable zero vorticity envelope, but the finite-time witness type is still
empty because bounded kinetic energy fails on `ℝ^3`. -/
theorem constantInitialVelocity_exhibits_BKMCandidate_without_finiteTimeWitness
    {ν T : ℝ} {c : NSSpace}
    (hc : c ≠ 0)
    (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (constantInitialVelocity c) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty (ExplicitFiniteTimeRegularityWitness ν (constantInitialVelocity c) T) := by
  refine ⟨?_, ?_⟩
  · exact constantVelocityField_exhibits_BKMCandidate_except_boundedEnergy
      (ν := ν) (T := T) hc hT
  · exact not_nonempty_ExplicitFiniteTimeRegularityWitness_constantInitialVelocity
      (ν := ν) (T := T) hc hT

/-- The same honest constant-data BKM gap persists after adding any smooth
zero-spatial-gradient pressure gauge to the explicit constant-field candidate.
-/
theorem constantInitialVelocity_exhibits_BKMCandidate_without_finiteTimeWitness_addPressureOfZeroSpatialGradient
    {ν T : ℝ} {c : NSSpace}
    (hc : c ≠ 0)
    (hT : 0 ≤ T)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (constantInitialVelocity c) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty (ExplicitFiniteTimeRegularityWitness ν (constantInitialVelocity c) T) := by
  refine ⟨?_, ?_⟩
  · exact
      constantVelocityField_exhibits_BKMCandidate_except_boundedEnergy_addPressureOfZeroSpatialGradient
        (ν := ν) (T := T) hc hT q hq hq_zero
  · exact not_nonempty_ExplicitFiniteTimeRegularityWitness_constantInitialVelocity
      (ν := ν) (T := T) hc hT

/-- The steady linear shear field is an exact smooth incompressible NS candidate
on every nonnegative slab with an explicit constant BKM envelope; the only
missing finite-time witness slot is bounded kinetic energy. -/
theorem linearShearVelocityField_exhibits_BKMCandidate_except_boundedEnergy
    {ν T a : ℝ} (ha : a ≠ 0) (hT : 0 ≤ T) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearInitialVelocity a) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T := by
  rcases linearShearVelocityField_exhibits_uniformCandidate_except_boundedEnergy
      (ν := ν) (T := T) (a := a) ha hT with
    ⟨u, p, B, hu, hp, hmom, hdiv, hinit, hω, hE⟩
  have hBKM :
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
        integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) :=
    uniformVorticityBoundUpTo_implies_constantBKMEnvelope
      (u := u) (T := T) (B := B) hT hω
  exact ⟨u, p, B, hu, hp, hmom, hdiv, hinit, hBKM.1, hBKM.2, hE⟩

/-- The steady field `u(t,x) = (a * x₁, 0, b)` is likewise an exact smooth
incompressible NS candidate on every nonnegative slab with the explicit
constant BKM envelope `Ω(t) = |a|`; bounded kinetic energy is again the only
missing witness slot. -/
theorem linearShearVerticalDriftVelocityField_exhibits_BKMCandidate_except_boundedEnergy
    {ν T a b : ℝ} (ha : a ≠ 0) (hT : 0 ≤ T) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearVerticalDriftInitialVelocity a b) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T := by
  rcases linearShearVerticalDriftVelocityField_exhibits_uniformCandidate_except_boundedEnergy
      (ν := ν) (T := T) (a := a) (b := b) ha hT with
    ⟨u, p, B, hu, hp, hmom, hdiv, hinit, hω, hE⟩
  have hBKM :
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
        integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) :=
    uniformVorticityBoundUpTo_implies_constantBKMEnvelope
      (u := u) (T := T) (B := B) hT hω
  exact ⟨u, p, B, hu, hp, hmom, hdiv, hinit, hBKM.1, hBKM.2, hE⟩

/-- Linear shear exposes the exact BKM-side gap in the current witness surface:
there is an explicit smooth incompressible candidate with a constant integrable
vorticity envelope, but the concrete finite-time witness type is still empty
because bounded kinetic energy fails on `ℝ^3`. -/
theorem linearShearInitialVelocity_exhibits_BKMCandidate_without_finiteTimeWitness
    {ν T a : ℝ} (ha : a ≠ 0) (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearInitialVelocity a) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty (ExplicitFiniteTimeRegularityWitness ν (linearShearInitialVelocity a) T) := by
  refine ⟨?_, ?_⟩
  · exact linearShearVelocityField_exhibits_BKMCandidate_except_boundedEnergy
      (ν := ν) (T := T) (a := a) ha hT
  · exact not_nonempty_ExplicitFiniteTimeRegularityWitness_linearShearInitialVelocity
      (ν := ν) (T := T) ha hT

/-- The same BKM-side gap persists for the affine shear datum
`x ↦ (a * x₁, 0, b)`: an explicit smooth incompressible candidate with constant
integrable vorticity envelope exists, but the finite-time witness type is still
empty because bounded kinetic energy fails on `ℝ^3`. -/
theorem linearShearVerticalDriftInitialVelocity_exhibits_BKMCandidate_without_finiteTimeWitness
    {ν T a b : ℝ} (ha : a ≠ 0) (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearVerticalDriftInitialVelocity a b) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness ν (linearShearVerticalDriftInitialVelocity a b) T) := by
  refine ⟨?_, ?_⟩
  · exact linearShearVerticalDriftVelocityField_exhibits_BKMCandidate_except_boundedEnergy
      (ν := ν) (T := T) (a := a) (b := b) ha hT
  · exact
      not_nonempty_ExplicitFiniteTimeRegularityWitness_linearShearVerticalDriftInitialVelocity
        (ν := ν) (T := T) (a := a) (b := b) ha hT

/-- The steady field `u(t,x) = (a * x₁, b, 0)` is likewise an exact smooth
incompressible NS candidate on every nonnegative slab with the explicit
constant BKM envelope `Ω(t) = |a|`; bounded kinetic energy is again the only
missing witness slot.  In this branch the affine pressure field is essential. -/
theorem linearShearHorizontalDriftVelocityField_exhibits_BKMCandidate_except_boundedEnergy
    {ν T a b : ℝ} (ha : a ≠ 0) (hT : 0 ≤ T) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearHorizontalDriftInitialVelocity a b) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T := by
  rcases linearShearHorizontalDriftVelocityField_exhibits_uniformCandidate_except_boundedEnergy
      (ν := ν) (T := T) (a := a) (b := b) ha hT with
    ⟨u, p, B, hu, hp, hmom, hdiv, hinit, hω, hE⟩
  have hBKM :
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
        integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) :=
    uniformVorticityBoundUpTo_implies_constantBKMEnvelope
      (u := u) (T := T) (B := B) hT hω
  exact ⟨u, p, B, hu, hp, hmom, hdiv, hinit, hBKM.1, hBKM.2, hE⟩

/-- The same horizontal affine-shear BKM candidate remains valid after adding
any smooth slice-wise zero-spatial-gradient pressure gauge.  The bounded-energy
slot on `ℝ^3` is still the only missing witness component. -/
theorem linearShearHorizontalDriftVelocityField_exhibits_BKMCandidate_except_boundedEnergy_addPressureOfZeroSpatialGradient
    {ν T a b : ℝ} (ha : a ≠ 0) (hT : 0 ≤ T)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearHorizontalDriftInitialVelocity a b) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T := by
  exact
    exhibits_BKMCandidate_except_boundedEnergy_of_uniformCandidate
      (u₀ := linearShearHorizontalDriftInitialVelocity a b) hT
      (linearShearHorizontalDriftVelocityField_exhibits_uniformCandidate_except_boundedEnergy_addPressureOfZeroSpatialGradient
        (ν := ν) (T := T) (a := a) (b := b) ha hT q hq hq_zero)

/-- Time-only special case of the horizontal affine-shear pressure-gauge
transport on the explicit BKM candidate surface. -/
theorem linearShearHorizontalDriftVelocityField_exhibits_BKMCandidate_except_boundedEnergy_addTimeOnlyPressure
    {ν T a b : ℝ} (ha : a ≠ 0) (hT : 0 ≤ T)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearHorizontalDriftInitialVelocity a b) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T := by
  exact
    linearShearHorizontalDriftVelocityField_exhibits_BKMCandidate_except_boundedEnergy_addPressureOfZeroSpatialGradient
      (ν := ν) (T := T) (a := a) (b := b) ha hT
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)

/-- The same BKM-side gap persists for the affine shear datum
`x ↦ (a * x₁, b, 0)`: an explicit smooth incompressible candidate with constant
integrable vorticity envelope exists, but the finite-time witness type is still
empty because bounded kinetic energy fails on `ℝ^3`. -/
theorem linearShearHorizontalDriftInitialVelocity_exhibits_BKMCandidate_without_finiteTimeWitness
    {ν T a b : ℝ} (ha : a ≠ 0) (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearHorizontalDriftInitialVelocity a b) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness ν (linearShearHorizontalDriftInitialVelocity a b) T) := by
  refine ⟨?_, ?_⟩
  · exact linearShearHorizontalDriftVelocityField_exhibits_BKMCandidate_except_boundedEnergy
      (ν := ν) (T := T) (a := a) (b := b) ha hT
  · exact
      not_nonempty_ExplicitFiniteTimeRegularityWitness_linearShearHorizontalDriftInitialVelocity
        (ν := ν) (T := T) (a := a) (b := b) ha hT

/-- The same horizontal affine-shear BKM gap persists after adding any smooth
slice-wise zero-spatial-gradient pressure gauge to the explicit slab
candidate. -/
theorem linearShearHorizontalDriftInitialVelocity_exhibits_BKMCandidate_without_finiteTimeWitness_addPressureOfZeroSpatialGradient
    {ν T a b : ℝ} (ha : a ≠ 0) (hT : 0 ≤ T)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearHorizontalDriftInitialVelocity a b) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness ν (linearShearHorizontalDriftInitialVelocity a b) T) := by
  refine ⟨?_, ?_⟩
  · exact
      linearShearHorizontalDriftVelocityField_exhibits_BKMCandidate_except_boundedEnergy_addPressureOfZeroSpatialGradient
        (ν := ν) (T := T) (a := a) (b := b) ha hT q hq hq_zero
  · exact
      not_nonempty_ExplicitFiniteTimeRegularityWitness_linearShearHorizontalDriftInitialVelocity
        (ν := ν) (T := T) (a := a) (b := b) ha hT

/-- Time-only special case of the horizontal affine-shear pressure-gauge gap on
the explicit BKM continuation surface. -/
theorem linearShearHorizontalDriftInitialVelocity_exhibits_BKMCandidate_without_finiteTimeWitness_addTimeOnlyPressure
    {ν T a b : ℝ} (ha : a ≠ 0) (hT : 0 ≤ T)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearHorizontalDriftInitialVelocity a b) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness ν (linearShearHorizontalDriftInitialVelocity a b) T) := by
  exact
    linearShearHorizontalDriftInitialVelocity_exhibits_BKMCandidate_without_finiteTimeWitness_addPressureOfZeroSpatialGradient
      (ν := ν) (T := T) (a := a) (b := b) ha hT
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)

/-- The steady field `u(t,x) = (a * x₁, b, c)` is likewise an exact smooth
incompressible NS candidate on every nonnegative slab with the explicit
constant BKM envelope `Ω(t) = |a|`; bounded kinetic energy is again the only
missing witness slot.  The same affine pressure as in the horizontal-drift
branch remains sufficient. -/
theorem linearShearFullDriftVelocityField_exhibits_BKMCandidate_except_boundedEnergy
    {ν T a b c : ℝ} (ha : a ≠ 0) (hT : 0 ≤ T) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearFullDriftInitialVelocity a b c) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T := by
  rcases linearShearFullDriftVelocityField_exhibits_uniformCandidate_except_boundedEnergy
      (ν := ν) (T := T) (a := a) (b := b) (c := c) ha hT with
    ⟨u, p, B, hu, hp, hmom, hdiv, hinit, hω, hE⟩
  have hBKM :
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
        integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) :=
    uniformVorticityBoundUpTo_implies_constantBKMEnvelope
      (u := u) (T := T) (B := B) hT hω
  exact ⟨u, p, B, hu, hp, hmom, hdiv, hinit, hBKM.1, hBKM.2, hE⟩

/-- The same BKM-side gap persists for the affine shear datum
`x ↦ (a * x₁, b, c)`: an explicit smooth incompressible candidate with constant
integrable vorticity envelope exists, but the finite-time witness type is still
empty because bounded kinetic energy fails on `ℝ^3`. -/
theorem linearShearFullDriftInitialVelocity_exhibits_BKMCandidate_without_finiteTimeWitness
    {ν T a b c : ℝ} (ha : a ≠ 0) (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearFullDriftInitialVelocity a b c) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness ν (linearShearFullDriftInitialVelocity a b c) T) := by
  refine ⟨?_, ?_⟩
  · exact linearShearFullDriftVelocityField_exhibits_BKMCandidate_except_boundedEnergy
      (ν := ν) (T := T) (a := a) (b := b) (c := c) ha hT
  · exact
      not_nonempty_ExplicitFiniteTimeRegularityWitness_linearShearFullDriftInitialVelocity
        (ν := ν) (T := T) (a := a) (b := b) (c := c) ha hT

/-- The damped sinusoidal heat-shear field is likewise an exact smooth
incompressible NS candidate on every nonnegative slab with the explicit
constant BKM envelope `Ω(t) = |a * k|`; bounded kinetic energy is still the
only missing witness slot. -/
theorem heatShearVelocityField_exhibits_BKMCandidate_except_boundedEnergy
    {ν T a k : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0)
    (hν : 0 ≤ ν) (hT : 0 ≤ T) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearInitialVelocity a k) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T := by
  rcases heatShearInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness
      (ν := ν) (T := T) (a := a) (k := k) ha hk hν hT with
    ⟨⟨u, p, B, hu, hp, hmom, hdiv, hinit, hω, hE⟩, _⟩
  have hBKM :
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
        integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) :=
    uniformVorticityBoundUpTo_implies_constantBKMEnvelope
      (u := u) (T := T) (B := B) hT hω
  exact ⟨u, p, B, hu, hp, hmom, hdiv, hinit, hBKM.1, hBKM.2, hE⟩

/-- Heat shear exposes the same exact BKM-side gap: there is an explicit smooth
incompressible candidate with an integrable constant vorticity envelope, but
the finite-time witness type is still empty because bounded kinetic energy
fails on `ℝ^3`. -/
theorem heatShearInitialVelocity_exhibits_BKMCandidate_without_finiteTimeWitness
    {ν T a k : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0)
    (hν : 0 ≤ ν) (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearInitialVelocity a k) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty (ExplicitFiniteTimeRegularityWitness ν (heatShearInitialVelocity a k) T) := by
  refine ⟨?_, ?_⟩
  · exact heatShearVelocityField_exhibits_BKMCandidate_except_boundedEnergy
      (ν := ν) (T := T) (a := a) (k := k) ha hk hν hT
  · exact not_nonempty_ExplicitFiniteTimeRegularityWitness_heatShearInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) ha hk hT

/-- Witness-level bridge from uniform linear-combination control on a large slab
to explicit BKM-envelope data on a shorter slab. -/
theorem ExplicitFiniteTimeRegularityWitness.uniformVorticityBound_linearCombination_implies_BKMEnvelope_restrict
    {ν ν' : ℝ} {u₀ u₀' : NSInitialVelocity} {T T' B B' : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (W' : ExplicitFiniteTimeRegularityWitness ν' u₀' T)
    (hω : uniformVorticityBoundUpTo W.velocity T B)
    (hω' : uniformVorticityBoundUpTo W'.velocity T B')
    (a b : ℝ)
    (hT : T' ≤ T) :
    ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
      vorticityEnvelopeOn
          (a • (W.restrict hT).velocity + b • (W'.restrict hT).velocity) T' Ω ∧
        integrableVorticityEnvelopeOn Ω T' Bint := by
  simpa [ExplicitFiniteTimeRegularityWitness.restrict] using
    (uniformVorticityBoundUpTo_linearCombination_implies_BKMEnvelope_restrict
      (u := W.velocity) (v := W'.velocity) (T := T) (T' := T')
      W.smooth_velocity W'.smooth_velocity hω hω' a b hT)

/-- Witness-level bridge from uniform linear-combination control on a large slab
to the explicit constant BKM envelope on a nonnegative shorter slab. -/
theorem ExplicitFiniteTimeRegularityWitness.uniformVorticityBound_linearCombination_implies_constantBKMEnvelope_restrict
    {ν ν' : ℝ} {u₀ u₀' : NSInitialVelocity} {T T' B B' : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (W' : ExplicitFiniteTimeRegularityWitness ν' u₀' T)
    (hT' : 0 ≤ T')
    (hω : uniformVorticityBoundUpTo W.velocity T B)
    (hω' : uniformVorticityBoundUpTo W'.velocity T B')
    (a b : ℝ)
    (hT : T' ≤ T) :
    vorticityEnvelopeOn
        (a • (W.restrict hT).velocity + b • (W'.restrict hT).velocity) T'
        (fun _ : NSTime => |a| * B + |b| * B') ∧
      integrableVorticityEnvelopeOn
        (fun _ : NSTime => |a| * B + |b| * B') T'
        (T' * (|a| * B + |b| * B')) := by
  simpa [ExplicitFiniteTimeRegularityWitness.restrict] using
    (uniformVorticityBoundUpTo_linearCombination_implies_constantBKMEnvelope_restrict
      (u := W.velocity) (v := W'.velocity) (T := T) (T' := T')
      hT' W.smooth_velocity W'.smooth_velocity hω hω' a b hT)

/-- BKM envelope data transport along witness restriction from `T` to `T' ≤ T`.
-/
theorem ExplicitFiniteTimeRegularityWitness.BKMEnvelope_restrict
    {ν : ℝ} {u₀ : NSInitialVelocity} {T T' : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hEnv :
      ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
        vorticityEnvelopeOn W.velocity T Ω ∧
          integrableVorticityEnvelopeOn Ω T B)
    (hT : T' ≤ T) :
    ∃ Ω : NSTime → ℝ, ∃ B' : ℝ,
      vorticityEnvelopeOn (W.restrict hT).velocity T' Ω ∧
        integrableVorticityEnvelopeOn Ω T' B' := by
  rcases hEnv with ⟨Ω, B, hV, hI⟩
  refine ⟨Ω, ∫ t in Set.Icc 0 T', Ω t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), ?_⟩
  refine ⟨?_, ?_⟩
  · simpa [ExplicitFiniteTimeRegularityWitness.restrict] using
      (vorticityEnvelopeOn_restrict (u := W.velocity) (T := T) (T' := T') (Ω := Ω) hV hT)
  · exact hV.integrable_restrict (hInt := hI) hT

/-- BKM envelope data are unchanged under adding any smooth pressure gauge with
zero spatial gradient on each slice, since the velocity field is unchanged. -/
theorem ExplicitFiniteTimeRegularityWitness.BKMEnvelope_addPressureOfZeroSpatialGradient
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hEnv :
      ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
        vorticityEnvelopeOn W.velocity T Ω ∧
          integrableVorticityEnvelopeOn Ω T B)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0) :
    ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
      vorticityEnvelopeOn (W.addPressureOfZeroSpatialGradient q hq hq_zero).velocity T Ω ∧
        integrableVorticityEnvelopeOn Ω T B := by
  simpa [ExplicitFiniteTimeRegularityWitness.addPressureOfZeroSpatialGradient] using hEnv

/-- BKM envelope data are unchanged under adding a smooth time-only pressure
gauge to the witness, since the velocity field is unchanged. -/
theorem ExplicitFiniteTimeRegularityWitness.BKMEnvelope_addTimeOnlyPressure
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hEnv :
      ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
        vorticityEnvelopeOn W.velocity T Ω ∧
          integrableVorticityEnvelopeOn Ω T B)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
      vorticityEnvelopeOn (W.addTimeOnlyPressure π hπ).velocity T Ω ∧
        integrableVorticityEnvelopeOn Ω T B := by
  exact
    W.BKMEnvelope_addPressureOfZeroSpatialGradient hEnv
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)

/-- BKM envelope data remain available after adding a smooth zero-spatial-gradient
pressure gauge and then restricting to a shorter slab. -/
theorem ExplicitFiniteTimeRegularityWitness.BKMEnvelope_addPressureOfZeroSpatialGradient_restrict
    {ν : ℝ} {u₀ : NSInitialVelocity} {T T' : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hEnv :
      ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
        vorticityEnvelopeOn W.velocity T Ω ∧
          integrableVorticityEnvelopeOn Ω T B)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0)
    (hT : T' ≤ T) :
    ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
      vorticityEnvelopeOn ((W.addPressureOfZeroSpatialGradient q hq hq_zero).restrict hT).velocity T' Ω ∧
        integrableVorticityEnvelopeOn Ω T' B := by
  exact
    (W.addPressureOfZeroSpatialGradient q hq hq_zero).BKMEnvelope_restrict
      (W.BKMEnvelope_addPressureOfZeroSpatialGradient hEnv q hq hq_zero) hT

/-- BKM envelope data remain available after adding a smooth time-only pressure
gauge and then restricting to a shorter slab. -/
theorem ExplicitFiniteTimeRegularityWitness.BKMEnvelope_addTimeOnlyPressure_restrict
    {ν : ℝ} {u₀ : NSInitialVelocity} {T T' : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hEnv :
      ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
        vorticityEnvelopeOn W.velocity T Ω ∧
          integrableVorticityEnvelopeOn Ω T B)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π)
    (hT : T' ≤ T) :
    ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
      vorticityEnvelopeOn ((W.addTimeOnlyPressure π hπ).restrict hT).velocity T' Ω ∧
        integrableVorticityEnvelopeOn Ω T' B := by
  exact
    W.BKMEnvelope_addPressureOfZeroSpatialGradient_restrict hEnv
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)
      hT

/-- Witness-level transport of BKM-envelope data under addition of velocities:
if two finite-time witnesses carry explicit BKM data on the same slab, then the
sum of their velocity fields carries explicit BKM data on that slab as well. -/
theorem ExplicitFiniteTimeRegularityWitness.BKMEnvelope_add
    {ν ν' : ℝ} {u₀ u₀' : NSInitialVelocity} {T : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (W' : ExplicitFiniteTimeRegularityWitness ν' u₀' T)
    (hEnv :
      ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
        vorticityEnvelopeOn W.velocity T Ω ∧
          integrableVorticityEnvelopeOn Ω T B)
    (hEnv' :
      ∃ Ω' : NSTime → ℝ, ∃ B' : ℝ,
        vorticityEnvelopeOn W'.velocity T Ω' ∧
          integrableVorticityEnvelopeOn Ω' T B') :
    ∃ Ω'' : NSTime → ℝ, ∃ B'' : ℝ,
      vorticityEnvelopeOn (W.velocity + W'.velocity) T Ω'' ∧
        integrableVorticityEnvelopeOn Ω'' T B'' := by
  rcases hEnv with ⟨Ω, B, hΩ, hInt⟩
  rcases hEnv' with ⟨Ω', B', hΩ', hInt'⟩
  refine ⟨fun t => Ω t + Ω' t, B + B', ?_⟩
  exact BKMEnvelopeData_add_of_smooth
    W.smooth_velocity W'.smooth_velocity hΩ hInt hΩ' hInt'

/-- Witness-level transport of BKM-envelope data under addition followed by
restriction to a shorter slab `0 ≤ t ≤ T'` with `T' ≤ T`. -/
theorem ExplicitFiniteTimeRegularityWitness.BKMEnvelope_add_restrict
    {ν ν' : ℝ} {u₀ u₀' : NSInitialVelocity} {T T' : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (W' : ExplicitFiniteTimeRegularityWitness ν' u₀' T)
    (hEnv :
      ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
        vorticityEnvelopeOn W.velocity T Ω ∧
          integrableVorticityEnvelopeOn Ω T B)
    (hEnv' :
      ∃ Ω' : NSTime → ℝ, ∃ B' : ℝ,
        vorticityEnvelopeOn W'.velocity T Ω' ∧
          integrableVorticityEnvelopeOn Ω' T B')
    (hT : T' ≤ T) :
    ∃ Ω'' : NSTime → ℝ, ∃ B'' : ℝ,
      vorticityEnvelopeOn (W.velocity + W'.velocity) T' Ω'' ∧
        integrableVorticityEnvelopeOn Ω'' T' B'' := by
  rcases W.BKMEnvelope_add W' hEnv hEnv' with ⟨Ω'', _B, hV, hI⟩
  refine ⟨Ω'', ∫ t in Set.Icc 0 T', Ω'' t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), ?_⟩
  exact BKMEnvelopeData_restrict hV hI hT

/-- Witness-level transport of BKM-envelope data under constant rescaling of
the velocity field. -/
theorem ExplicitFiniteTimeRegularityWitness.BKMEnvelope_const_smul
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hEnv :
      ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
        vorticityEnvelopeOn W.velocity T Ω ∧
          integrableVorticityEnvelopeOn Ω T B)
    (a : ℝ) :
    ∃ Ω' : NSTime → ℝ, ∃ B' : ℝ,
      vorticityEnvelopeOn (a • W.velocity) T Ω' ∧
        integrableVorticityEnvelopeOn Ω' T B' := by
  rcases hEnv with ⟨Ω, B, hΩ, hInt⟩
  refine ⟨fun t => |a| * Ω t, |a| * B, ?_⟩
  exact ⟨vorticityEnvelopeOn_const_smul (a := a) hΩ,
    integrableVorticityEnvelopeOn_abs_const_smul (a := a) hInt⟩

/-- Witness-level transport of BKM-envelope data under constant rescaling
followed by restriction to a shorter slab `0 ≤ t ≤ T'` with `T' ≤ T`. -/
theorem ExplicitFiniteTimeRegularityWitness.BKMEnvelope_const_smul_restrict
    {ν : ℝ} {u₀ : NSInitialVelocity} {T T' : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hEnv :
      ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
        vorticityEnvelopeOn W.velocity T Ω ∧
          integrableVorticityEnvelopeOn Ω T B)
    (a : ℝ)
    (hT : T' ≤ T) :
    ∃ Ω' : NSTime → ℝ, ∃ B' : ℝ,
      vorticityEnvelopeOn (a • W.velocity) T' Ω' ∧
        integrableVorticityEnvelopeOn Ω' T' B' := by
  rcases W.BKMEnvelope_const_smul hEnv a with ⟨Ω', _B, hV, hI⟩
  refine ⟨Ω', ∫ t in Set.Icc 0 T', Ω' t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), ?_⟩
  exact BKMEnvelopeData_restrict hV hI hT

/-- Witness-level transport of BKM-envelope data under sign flip of the
velocity field. -/
theorem ExplicitFiniteTimeRegularityWitness.BKMEnvelope_neg
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hEnv :
      ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
        vorticityEnvelopeOn W.velocity T Ω ∧
          integrableVorticityEnvelopeOn Ω T B) :
    ∃ Ω' : NSTime → ℝ, ∃ B' : ℝ,
        vorticityEnvelopeOn (-W.velocity) T Ω' ∧
        integrableVorticityEnvelopeOn Ω' T B' := by
  simpa using W.BKMEnvelope_const_smul hEnv (-1 : ℝ)

/-- Witness-level transport of BKM-envelope data under sign flip followed by
restriction to a shorter slab `0 ≤ t ≤ T'` with `T' ≤ T`. -/
theorem ExplicitFiniteTimeRegularityWitness.BKMEnvelope_neg_restrict
    {ν : ℝ} {u₀ : NSInitialVelocity} {T T' : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hEnv :
      ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
        vorticityEnvelopeOn W.velocity T Ω ∧
          integrableVorticityEnvelopeOn Ω T B)
    (hT : T' ≤ T) :
    ∃ Ω' : NSTime → ℝ, ∃ B' : ℝ,
      vorticityEnvelopeOn (-W.velocity) T' Ω' ∧
        integrableVorticityEnvelopeOn Ω' T' B' := by
  simpa using W.BKMEnvelope_const_smul_restrict hEnv (-1 : ℝ) hT

/-- Witness-level transport of BKM-envelope data under subtraction of
velocities: if two finite-time witnesses carry explicit BKM data on the same
slab, then the difference of their velocity fields carries explicit BKM data on
that slab as well. -/
theorem ExplicitFiniteTimeRegularityWitness.BKMEnvelope_sub
    {ν ν' : ℝ} {u₀ u₀' : NSInitialVelocity} {T : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (W' : ExplicitFiniteTimeRegularityWitness ν' u₀' T)
    (hEnv :
      ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
        vorticityEnvelopeOn W.velocity T Ω ∧
          integrableVorticityEnvelopeOn Ω T B)
    (hEnv' :
      ∃ Ω' : NSTime → ℝ, ∃ B' : ℝ,
        vorticityEnvelopeOn W'.velocity T Ω' ∧
          integrableVorticityEnvelopeOn Ω' T B') :
    ∃ Ω'' : NSTime → ℝ, ∃ B'' : ℝ,
      vorticityEnvelopeOn (W.velocity - W'.velocity) T Ω'' ∧
        integrableVorticityEnvelopeOn Ω'' T B'' := by
  rcases hEnv with ⟨Ω, B, hΩ, hInt⟩
  rcases hEnv' with ⟨Ω', B', hΩ', hInt'⟩
  refine ⟨fun t => Ω t + Ω' t, B + B', ?_⟩
  exact BKMEnvelopeData_sub_of_smooth
    W.smooth_velocity W'.smooth_velocity hΩ hInt hΩ' hInt'

/-- Witness-level transport of BKM-envelope data under subtraction followed by
restriction to a shorter slab `0 ≤ t ≤ T'` with `T' ≤ T`. -/
theorem ExplicitFiniteTimeRegularityWitness.BKMEnvelope_sub_restrict
    {ν ν' : ℝ} {u₀ u₀' : NSInitialVelocity} {T T' : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (W' : ExplicitFiniteTimeRegularityWitness ν' u₀' T)
    (hEnv :
      ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
        vorticityEnvelopeOn W.velocity T Ω ∧
          integrableVorticityEnvelopeOn Ω T B)
    (hEnv' :
      ∃ Ω' : NSTime → ℝ, ∃ B' : ℝ,
        vorticityEnvelopeOn W'.velocity T Ω' ∧
          integrableVorticityEnvelopeOn Ω' T B')
    (hT : T' ≤ T) :
    ∃ Ω'' : NSTime → ℝ, ∃ B'' : ℝ,
      vorticityEnvelopeOn (W.velocity - W'.velocity) T' Ω'' ∧
        integrableVorticityEnvelopeOn Ω'' T' B'' := by
  rcases W.BKMEnvelope_sub W' hEnv hEnv' with ⟨Ω'', _B, hV, hI⟩
  refine ⟨Ω'', ∫ t in Set.Icc 0 T', Ω'' t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), ?_⟩
  exact BKMEnvelopeData_restrict hV hI hT

/-- Witness-level BKM package for a linear combination on a smaller slab:
explicit BKM data for `W.velocity` and `W'.velocity` on `0 ≤ t ≤ T` induce
explicit BKM data for `a • W.velocity + b • W'.velocity` on every shorter slab
`0 ≤ t ≤ T' ≤ T`. -/
theorem ExplicitFiniteTimeRegularityWitness.BKMEnvelope_linearCombination_restrict
    {ν ν' : ℝ} {u₀ u₀' : NSInitialVelocity} {T T' : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (W' : ExplicitFiniteTimeRegularityWitness ν' u₀' T)
    (hEnv :
      ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
        vorticityEnvelopeOn W.velocity T Ω ∧
          integrableVorticityEnvelopeOn Ω T B)
    (hEnv' :
      ∃ Ω' : NSTime → ℝ, ∃ B' : ℝ,
        vorticityEnvelopeOn W'.velocity T Ω' ∧
          integrableVorticityEnvelopeOn Ω' T B')
    (a b : ℝ)
    (hT : T' ≤ T) :
    ∃ Ω'' : NSTime → ℝ, ∃ B'' : ℝ,
      vorticityEnvelopeOn (a • W.velocity + b • W'.velocity) T' Ω'' ∧
        integrableVorticityEnvelopeOn Ω'' T' B'' := by
  rcases hEnv with ⟨Ω, B, hΩ, hInt⟩
  rcases hEnv' with ⟨Ω', B', hΩ', hInt'⟩
  refine ⟨fun t => |a| * Ω t + |b| * Ω' t,
    ∫ t in Set.Icc 0 T', (|a| * Ω t + |b| * Ω' t)
      ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), ?_⟩
  exact BKMEnvelopeData_linearCombination_restrict_of_smooth
    W.smooth_velocity W'.smooth_velocity hΩ hInt hΩ' hInt' a b hT

/-- A BKM continuation clause at horizon `T'` can be applied to any larger-slab
witness by restricting the witness and its explicit BKM data from `0 ≤ t ≤ T`
down to `0 ≤ t ≤ T' ≤ T`. -/
theorem ExplicitBKMContinuationClause_apply_of_BKMEnvelope_restrict
    {ν : ℝ} {u₀ : NSInitialVelocity} {T T' : ℝ}
    (hClause : ExplicitBKMContinuationClause ν u₀ T')
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hEnv :
      ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
        vorticityEnvelopeOn W.velocity T Ω ∧
          integrableVorticityEnvelopeOn Ω T B)
    (hT : T' ≤ T) :
    ExplicitConcreteNavierStokesGlobalOutput ν u₀ := by
  exact hClause hν hsmooth hdiv (W.restrict hT) (W.BKMEnvelope_restrict hEnv hT)

/-- A BKM continuation clause can be applied equally well after changing the
witness by any smooth pressure gauge with zero spatial gradient, since the
explicit BKM data are pressure-invariant. -/
theorem ExplicitBKMContinuationClause_apply_of_BKMEnvelope_addPressureOfZeroSpatialGradient
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hClause : ExplicitBKMContinuationClause ν u₀ T)
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hEnv :
      ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
        vorticityEnvelopeOn W.velocity T Ω ∧
          integrableVorticityEnvelopeOn Ω T B)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0) :
    ExplicitConcreteNavierStokesGlobalOutput ν u₀ := by
  exact hClause hν hsmooth hdiv
    (W.addPressureOfZeroSpatialGradient q hq hq_zero)
    (W.BKMEnvelope_addPressureOfZeroSpatialGradient hEnv q hq hq_zero)

/-- A BKM continuation clause can be applied equally well after changing the
witness by a smooth time-only pressure gauge, since the explicit BKM data are
pressure-invariant. -/
theorem ExplicitBKMContinuationClause_apply_of_BKMEnvelope_addTimeOnlyPressure
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hClause : ExplicitBKMContinuationClause ν u₀ T)
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hEnv :
      ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
        vorticityEnvelopeOn W.velocity T Ω ∧
          integrableVorticityEnvelopeOn Ω T B)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    ExplicitConcreteNavierStokesGlobalOutput ν u₀ := by
  exact
    ExplicitBKMContinuationClause_apply_of_BKMEnvelope_addPressureOfZeroSpatialGradient
      (hClause := hClause) hν hsmooth hdiv W hEnv
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)

/-- A BKM continuation clause at horizon `T'` can also be applied after first
changing a larger-slab witness by a smooth zero-spatial-gradient pressure gauge
and then restricting to `0 ≤ t ≤ T' ≤ T`. -/
theorem ExplicitBKMContinuationClause_apply_of_BKMEnvelope_addPressureOfZeroSpatialGradient_restrict
    {ν : ℝ} {u₀ : NSInitialVelocity} {T T' : ℝ}
    (hClause : ExplicitBKMContinuationClause ν u₀ T')
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hEnv :
      ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
        vorticityEnvelopeOn W.velocity T Ω ∧
          integrableVorticityEnvelopeOn Ω T B)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0)
    (hT : T' ≤ T) :
    ExplicitConcreteNavierStokesGlobalOutput ν u₀ := by
  exact hClause hν hsmooth hdiv
    ((W.addPressureOfZeroSpatialGradient q hq hq_zero).restrict hT)
    (W.BKMEnvelope_addPressureOfZeroSpatialGradient_restrict hEnv q hq hq_zero hT)

/-- A BKM continuation clause at horizon `T'` can also be applied after first
changing a larger-slab witness by a smooth time-only pressure gauge and then
restricting to `0 ≤ t ≤ T' ≤ T`. -/
theorem ExplicitBKMContinuationClause_apply_of_BKMEnvelope_addTimeOnlyPressure_restrict
    {ν : ℝ} {u₀ : NSInitialVelocity} {T T' : ℝ}
    (hClause : ExplicitBKMContinuationClause ν u₀ T')
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hEnv :
      ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
        vorticityEnvelopeOn W.velocity T Ω ∧
          integrableVorticityEnvelopeOn Ω T B)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π)
    (hT : T' ≤ T) :
    ExplicitConcreteNavierStokesGlobalOutput ν u₀ := by
  exact
    ExplicitBKMContinuationClause_apply_of_BKMEnvelope_addPressureOfZeroSpatialGradient_restrict
      (hClause := hClause) hν hsmooth hdiv W hEnv
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)
      hT

/-- A BKM continuation clause at horizon `T'` can also be applied to a
larger-slab witness using only a uniform vorticity bound on the larger slab,
via the restricted uniform-to-BKM bridge. -/
theorem ExplicitBKMContinuationClause_apply_of_uniformVorticityBound_restrict
    {ν : ℝ} {u₀ : NSInitialVelocity} {T T' B : ℝ}
    (hClause : ExplicitBKMContinuationClause ν u₀ T')
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hω : uniformVorticityBoundUpTo W.velocity T B)
    (hT : T' ≤ T) :
    ExplicitConcreteNavierStokesGlobalOutput ν u₀ := by
  have hEnv :
      ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
        vorticityEnvelopeOn (W.restrict hT).velocity T' Ω ∧
          integrableVorticityEnvelopeOn Ω T' Bint := by
    simpa [ExplicitFiniteTimeRegularityWitness.restrict] using
      (uniformVorticityBoundUpTo_implies_BKMEnvelope_restrict
        (u := W.velocity) (T := T) (T' := T') (B := B) hω hT)
  exact hClause hν hsmooth hdiv (W.restrict hT) hEnv

/-- A BKM continuation clause can also be applied after changing a witness by
any smooth pressure gauge with zero spatial gradient, using only a uniform
vorticity bound on the same slab.  The pressure change leaves the velocity
unchanged, so the uniform bound still converts into explicit BKM data. -/
theorem ExplicitBKMContinuationClause_apply_of_uniformVorticityBound_addPressureOfZeroSpatialGradient
    {ν : ℝ} {u₀ : NSInitialVelocity} {T B : ℝ}
    (hClause : ExplicitBKMContinuationClause ν u₀ T)
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hω : uniformVorticityBoundUpTo W.velocity T B)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0) :
    ExplicitConcreteNavierStokesGlobalOutput ν u₀ := by
  have hEnv :
      ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
        vorticityEnvelopeOn (W.addPressureOfZeroSpatialGradient q hq hq_zero).velocity T Ω ∧
          integrableVorticityEnvelopeOn Ω T Bint := by
    exact
      uniformVorticityBoundUpTo_implies_BKMEnvelope
        (u := (W.addPressureOfZeroSpatialGradient q hq hq_zero).velocity) (T := T) (B := B)
        (W.uniformVorticityBound_addPressureOfZeroSpatialGradient hω q hq hq_zero)
  exact hClause hν hsmooth hdiv (W.addPressureOfZeroSpatialGradient q hq hq_zero) hEnv

/-- A BKM continuation clause can also be applied after changing a witness by a
smooth time-only pressure gauge, using only a uniform vorticity bound on the
same slab.  The pressure change leaves the velocity unchanged, so the uniform
bound still converts into explicit BKM data. -/
theorem ExplicitBKMContinuationClause_apply_of_uniformVorticityBound_addTimeOnlyPressure
    {ν : ℝ} {u₀ : NSInitialVelocity} {T B : ℝ}
    (hClause : ExplicitBKMContinuationClause ν u₀ T)
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hω : uniformVorticityBoundUpTo W.velocity T B)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    ExplicitConcreteNavierStokesGlobalOutput ν u₀ := by
  exact
    ExplicitBKMContinuationClause_apply_of_uniformVorticityBound_addPressureOfZeroSpatialGradient
      (hClause := hClause) hν hsmooth hdiv W hω
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)

/-- A BKM continuation clause at horizon `T'` can also be applied after first
changing a larger-slab witness by a smooth zero-spatial-gradient pressure gauge
and then using the resulting restricted uniform vorticity bound on
`0 ≤ t ≤ T' ≤ T`. -/
theorem ExplicitBKMContinuationClause_apply_of_uniformVorticityBound_addPressureOfZeroSpatialGradient_restrict
    {ν : ℝ} {u₀ : NSInitialVelocity} {T T' B : ℝ}
    (hClause : ExplicitBKMContinuationClause ν u₀ T')
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hω : uniformVorticityBoundUpTo W.velocity T B)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0)
    (hT : T' ≤ T) :
    ExplicitConcreteNavierStokesGlobalOutput ν u₀ := by
  simpa [ExplicitFiniteTimeRegularityWitness.restrict,
    ExplicitFiniteTimeRegularityWitness.addPressureOfZeroSpatialGradient] using
    (ExplicitBKMContinuationClause_apply_of_uniformVorticityBound_addPressureOfZeroSpatialGradient
      (hClause := hClause) hν hsmooth hdiv (W := W.restrict hT)
      (hω := W.uniformVorticityBound_restrict hω hT) q hq hq_zero)

/-- A BKM continuation clause at horizon `T'` can also be applied after first
changing a larger-slab witness by a smooth time-only pressure gauge and then
using the resulting restricted uniform vorticity bound on `0 ≤ t ≤ T' ≤ T`. -/
theorem ExplicitBKMContinuationClause_apply_of_uniformVorticityBound_addTimeOnlyPressure_restrict
    {ν : ℝ} {u₀ : NSInitialVelocity} {T T' B : ℝ}
    (hClause : ExplicitBKMContinuationClause ν u₀ T')
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hω : uniformVorticityBoundUpTo W.velocity T B)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π)
    (hT : T' ≤ T) :
    ExplicitConcreteNavierStokesGlobalOutput ν u₀ := by
  exact
    ExplicitBKMContinuationClause_apply_of_uniformVorticityBound_addPressureOfZeroSpatialGradient_restrict
      (hClause := hClause) hν hsmooth hdiv W hω
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)
      hT

/-- Horizon monotonicity for the BKM-style continuation clause:
if the clause is available on a smaller slab `0 ≤ t ≤ Tsmall`, then it is also
available on every larger slab `0 ≤ t ≤ Tlarge` with `Tsmall ≤ Tlarge`, by
restricting the witness and its envelope data. -/
theorem ExplicitBKMContinuationClause_mono_horizon
    {ν : ℝ} {u₀ : NSInitialVelocity} {Tsmall Tlarge : ℝ}
    (hClauseSmall : ExplicitBKMContinuationClause ν u₀ Tsmall)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitBKMContinuationClause ν u₀ Tlarge := by
  intro hν hsmooth hdiv W hEnv
  exact
    ExplicitBKMContinuationClause_apply_of_BKMEnvelope_restrict
      hClauseSmall hν hsmooth hdiv W hEnv hT

/-- A repaired BKM continuation clause at horizon `T'` can be applied to any
larger-slab witness by restricting the witness and its explicit BKM data from
`0 ≤ t ≤ T` down to `0 ≤ t ≤ T' ≤ T`. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_apply_of_BKMEnvelope_restrict
    {ν : ℝ} {u₀ : NSInitialVelocity} {T T' : ℝ}
    (hClause : ExplicitFiniteEnergyBKMContinuationClause ν u₀ T')
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (hfinite : finiteInitialKineticEnergy u₀)
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hEnv :
      ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
        vorticityEnvelopeOn W.velocity T Ω ∧
          integrableVorticityEnvelopeOn Ω T B)
    (hT : T' ≤ T) :
    ExplicitConcreteNavierStokesGlobalOutput ν u₀ := by
  exact hClause hν hsmooth hdiv hfinite (W.restrict hT) (W.BKMEnvelope_restrict hEnv hT)

/-- Horizon monotonicity for the repaired BKM continuation clause:
if the clause is available on a smaller slab `0 ≤ t ≤ Tsmall`, then it is also
available on every larger slab `0 ≤ t ≤ Tlarge` with `Tsmall ≤ Tlarge`, by
restricting the witness and its envelope data. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_mono_horizon
    {ν : ℝ} {u₀ : NSInitialVelocity} {Tsmall Tlarge : ℝ}
    (hClauseSmall : ExplicitFiniteEnergyBKMContinuationClause ν u₀ Tsmall)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitFiniteEnergyBKMContinuationClause ν u₀ Tlarge := by
  intro hν hsmooth hdiv hfinite W hEnv
  exact
    ExplicitFiniteEnergyBKMContinuationClause_apply_of_BKMEnvelope_restrict
      hClauseSmall hν hsmooth hdiv hfinite W hEnv hT

/-- The canonical zero slab witness carries a direct explicit BKM envelope:
`Ω(t) = 0`, with integral bound `B = 0`. -/
theorem zeroFiniteTimeRegularityWitness_has_BKMEnvelope
    (ν T : ℝ) :
    ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
      vorticityEnvelopeOn (zeroFiniteTimeRegularityWitness ν T).velocity T Ω ∧
        integrableVorticityEnvelopeOn Ω T B := by
  refine ⟨fun _ => 0, 0, ?_⟩
  refine ⟨?_, ?_⟩
  · simpa [zeroFiniteTimeRegularityWitness] using (vorticityEnvelopeOn_zero T)
  · simpa using (integrableVorticityEnvelopeOn_zero T)

/-- The zero witness gives an honest inhabited premise for the concrete BKM
continuation clause on every slab.  This is the basic nonvacuity baseline that
contrasts with the impossible nonzero constant-initial-data cases. -/
theorem zeroFiniteTimeRegularityWitness_exhibits_BKMContinuationPremise
    (ν T : ℝ) :
    ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
      ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
        vorticityEnvelopeOn W.velocity T Ω ∧
          integrableVorticityEnvelopeOn Ω T B := by
  refine ⟨zeroFiniteTimeRegularityWitness ν T, ?_⟩
  exact zeroFiniteTimeRegularityWitness_has_BKMEnvelope ν T

/-- Concrete finite-slab BKM gauge baseline: after adding any smooth time-only
pressure to the zero witness on a larger slab and restricting to a shorter one,
the resulting witness still carries the explicit zero BKM envelope. -/
theorem zeroFiniteTimeRegularityWitness_addPressureOfZeroSpatialGradient_restrict_has_BKMEnvelope
    (ν Tsmall Tlarge : ℝ)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0)
    (hT : Tsmall ≤ Tlarge) :
    ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
      vorticityEnvelopeOn
          (((zeroFiniteTimeRegularityWitness ν Tlarge).addPressureOfZeroSpatialGradient q hq hq_zero).restrict hT).velocity
          Tsmall Ω ∧
        integrableVorticityEnvelopeOn Ω Tsmall B := by
  exact
    (zeroFiniteTimeRegularityWitness ν Tlarge).BKMEnvelope_addPressureOfZeroSpatialGradient_restrict
      (zeroFiniteTimeRegularityWitness_has_BKMEnvelope ν Tlarge)
      q hq hq_zero hT

/-- Time-only special case of the zero-data zero-spatial-gradient BKM gauge
baseline on restricted slabs. -/
theorem zeroFiniteTimeRegularityWitness_addTimeOnlyPressure_restrict_has_BKMEnvelope
    (ν Tsmall Tlarge : ℝ)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π)
    (hT : Tsmall ≤ Tlarge) :
    ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
      vorticityEnvelopeOn
          (((zeroFiniteTimeRegularityWitness ν Tlarge).addTimeOnlyPressure π hπ).restrict hT).velocity
          Tsmall Ω ∧
        integrableVorticityEnvelopeOn Ω Tsmall B := by
  exact
    zeroFiniteTimeRegularityWitness_addPressureOfZeroSpatialGradient_restrict_has_BKMEnvelope
      ν Tsmall Tlarge
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)
      hT

/-- The fully explicit NS theorem target subsumes the BKM-style continuation
target.  This is only a one-way sanity theorem: the current proof reuses the
global theorem target directly and does not yet use the envelope/integrability
hypothesis analytically. -/
theorem ExplicitConcreteNavierStokesMillenniumTarget_implies_BKMContinuationTarget
    (h : ExplicitConcreteNavierStokesMillenniumTarget) :
    ExplicitBKMContinuationTarget := by
  intro ν u₀
  exact
    ExplicitConcreteNavierStokesRegularityClause_implies_ExplicitBKMContinuationClause_allHorizons
      (h ν u₀)

/-- The same unrepaired explicit theorem surface also exports the whole
fixed-datum family of BKM continuation clauses directly. -/
theorem ExplicitConcreteNavierStokesMillenniumTarget_implies_BKMContinuationClause_allHorizons
    (h : ExplicitConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ T : ℝ, ExplicitBKMContinuationClause ν u₀ T := by
  exact
    ExplicitConcreteNavierStokesRegularityClause_implies_ExplicitBKMContinuationClause_allHorizons
      (h ν u₀)

/-- The same unrepaired explicit theorem surface also gives the corresponding
fixed-horizon BKM continuation clause directly. -/
theorem ExplicitConcreteNavierStokesMillenniumTarget_implies_BKMContinuationClause
    (h : ExplicitConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitBKMContinuationClause ν u₀ T := by
  exact
    (ExplicitConcreteNavierStokesMillenniumTarget_implies_BKMContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀) h) T

/-- The original BKM continuation clause immediately implies the repaired
finite-energy version, since the extra input hypothesis only narrows the
admissible initial data. -/
theorem ExplicitBKMContinuationClause_implies_finiteEnergy
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hClause : ExplicitBKMContinuationClause ν u₀ T) :
    ExplicitFiniteEnergyBKMContinuationClause ν u₀ T := by
  intro hν hsmooth hdiv _hfinite W hBKM
  exact hClause hν hsmooth hdiv W hBKM

/-- The same lift also holds on the theorem surface: an unrepaired BKM target
immediately implies the repaired one, because the extra finite-energy input is
only an admissibility restriction. -/
theorem ExplicitBKMContinuationTarget_implies_finiteEnergyBKMContinuationTarget
    (hBKM : ExplicitBKMContinuationTarget) :
    ExplicitFiniteEnergyBKMContinuationTarget := by
  intro ν u₀ T
  exact ExplicitBKMContinuationClause_implies_finiteEnergy (hBKM ν u₀ T)

/-- The all-horizons repaired BKM target immediately yields the corrected
nonnegative-horizon repaired target. -/
theorem
    ExplicitFiniteEnergyBKMContinuationTarget_implies_finiteEnergyBKMContinuationTargetOnNonnegHorizons
    (hBKM : ExplicitFiniteEnergyBKMContinuationTarget) :
    ExplicitFiniteEnergyBKMContinuationTargetOnNonnegHorizons := by
  intro ν u₀ T _hT
  exact hBKM ν u₀ T

/-- On a nonnegative slab, the repaired and unrepaired BKM continuation clauses
coincide because any actual finite-time witness already carries finite initial
kinetic energy. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_iff_of_nonneg_horizon
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitFiniteEnergyBKMContinuationClause ν u₀ T ↔
      ExplicitBKMContinuationClause ν u₀ T := by
  constructor
  · intro hClause hν hsmooth hdiv W hBKM
    exact hClause hν hsmooth hdiv (W.finiteInitialKineticEnergy hT) W hBKM
  · intro hClause
    exact ExplicitBKMContinuationClause_implies_finiteEnergy hClause

/-- On a nonnegative slab, the repaired BKM clause can first be read as the
original unrepaired BKM clause, because any actual finite-time witness already
supplies the missing finite-energy hypothesis. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_implies_BKMContinuationClause_of_nonneg_horizon
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hClause : ExplicitFiniteEnergyBKMContinuationClause ν u₀ T)
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν u₀ T := by
  exact
    (ExplicitFiniteEnergyBKMContinuationClause_iff_of_nonneg_horizon hT).mp hClause

/-- Hence the repaired BKM target also forgets directly to the unrepaired BKM
clause at each fixed nonnegative horizon. -/
theorem ExplicitFiniteEnergyBKMContinuationTarget_implies_BKMContinuationClause_of_nonneg_horizon
    (hBKM : ExplicitFiniteEnergyBKMContinuationTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_implies_BKMContinuationClause_of_nonneg_horizon
      (hClause := hBKM ν u₀ T) hT

/-- The corrected nonnegative-horizon repaired BKM target forgets to the
unrepaired BKM clause at each fixed nonnegative horizon. -/
theorem
    ExplicitFiniteEnergyBKMContinuationTargetOnNonnegHorizons_implies_BKMContinuationClause_of_nonneg_horizon
    (hBKM : ExplicitFiniteEnergyBKMContinuationTargetOnNonnegHorizons)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_implies_BKMContinuationClause_of_nonneg_horizon
      (hClause := hBKM ν u₀ hT) hT

/-- The repaired BKM target also forgets to the unrepaired BKM clause family
on every nonnegative horizon. -/
theorem ExplicitFiniteEnergyBKMContinuationTarget_implies_BKMContinuationClause_allNonnegHorizons
    (hBKM : ExplicitFiniteEnergyBKMContinuationTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ ⦃T : ℝ⦄, 0 ≤ T → ExplicitBKMContinuationClause ν u₀ T := by
  intro T hT
  exact
    ExplicitFiniteEnergyBKMContinuationTarget_implies_BKMContinuationClause_of_nonneg_horizon
      (ν := ν) (u₀ := u₀) (T := T) hBKM hT

/-- The corrected nonnegative-horizon repaired BKM target forgets to the
unrepaired BKM clause family on every nonnegative horizon. -/
theorem
    ExplicitFiniteEnergyBKMContinuationTargetOnNonnegHorizons_implies_BKMContinuationClause_allNonnegHorizons
    (hBKM : ExplicitFiniteEnergyBKMContinuationTargetOnNonnegHorizons)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ ⦃T : ℝ⦄, 0 ≤ T → ExplicitBKMContinuationClause ν u₀ T := by
  intro T hT
  exact
    ExplicitFiniteEnergyBKMContinuationTargetOnNonnegHorizons_implies_BKMContinuationClause_of_nonneg_horizon
      (ν := ν) (u₀ := u₀) (T := T) hBKM hT

/-- The repaired explicit finite-energy theorem surface directly implies the
repaired BKM-style continuation target. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationTarget
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyBKMContinuationTarget := by
  intro ν u₀
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_implies_ExplicitFiniteEnergyBKMContinuationClause_allHorizons
      (h ν u₀)

/-- The repaired explicit finite-energy theorem surface also proves the
corrected nonnegative-horizon BKM continuation target. -/
theorem
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationTargetOnNonnegHorizons
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyBKMContinuationTargetOnNonnegHorizons := by
  exact
    ExplicitFiniteEnergyBKMContinuationTarget_implies_finiteEnergyBKMContinuationTargetOnNonnegHorizons
      (ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationTarget h)

/-- The repaired explicit finite-energy theorem surface also exports the whole
fixed-datum family of repaired BKM continuation clauses. -/
theorem
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationClause_allHorizons
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ T : ℝ, ExplicitFiniteEnergyBKMContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_implies_ExplicitFiniteEnergyBKMContinuationClause_allHorizons
      (h ν u₀)

/-- The repaired explicit finite-energy theorem surface also directly implies
the repaired BKM-style continuation clause at each fixed horizon. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationClause
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyBKMContinuationClause ν u₀ T := by
  exact
    (ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀) h) T

/-- Likewise for the structured repaired finite-energy theorem surface. -/
theorem FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationTarget
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyBKMContinuationTarget := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationTarget
      (FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget
        h)

/-- Likewise for the structured repaired finite-energy theorem surface as a
fixed-datum all-horizons family. -/
theorem FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationClause_allHorizons
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ T : ℝ, ExplicitFiniteEnergyBKMContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀)
      (FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget
        h)

/-- Likewise for the structured repaired finite-energy theorem surface at a
fixed horizon. -/
theorem FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationClause
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyBKMContinuationClause ν u₀ T := by
  exact
    (FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀) h) T

/-- Since the unrepaired explicit theorem surface subsumes the repaired
finite-energy theorem surface, it also directly subsumes the repaired
BKM-style continuation target. -/
theorem ExplicitConcreteNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationTarget
    (h : ExplicitConcreteNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyBKMContinuationTarget := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationTarget
      (ExplicitConcreteNavierStokesMillenniumTarget_implies_finiteEnergy h)

/-- The same unrepaired explicit theorem surface also exports the whole
fixed-datum family of repaired BKM continuation clauses. -/
theorem ExplicitConcreteNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationClause_allHorizons
    (h : ExplicitConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ T : ℝ, ExplicitFiniteEnergyBKMContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀)
      (ExplicitConcreteNavierStokesMillenniumTarget_implies_finiteEnergy h)

/-- Likewise, the unrepaired explicit theorem surface directly subsumes the
repaired BKM-style continuation clause at each fixed horizon. -/
theorem ExplicitConcreteNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationClause
    (h : ExplicitConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyBKMContinuationClause ν u₀ T := by
  exact
    (ExplicitConcreteNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀) h) T

/-- Likewise for the structured unrepaired whole-space theorem surface. -/
theorem ConcreteNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationTarget
    (h : ConcreteNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyBKMContinuationTarget := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationTarget
      (ConcreteNavierStokesMillenniumTarget_implies_ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget
        h)

/-- Likewise for the structured unrepaired whole-space theorem surface as a
fixed-datum all-horizons family of repaired BKM clauses. -/
theorem ConcreteNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationClause_allHorizons
    (h : ConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ T : ℝ, ExplicitFiniteEnergyBKMContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀)
      (ConcreteNavierStokesMillenniumTarget_implies_ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget
        h)

/-- Likewise for the structured unrepaired whole-space theorem surface at a
fixed horizon. -/
theorem ConcreteNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationClause
    (h : ConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyBKMContinuationClause ν u₀ T := by
  exact
    (ConcreteNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀) h) T

/-- The repaired explicit finite-energy theorem surface still implies the
BKM-style continuation clause on every nonnegative slab.  If the input datum is
not finite-energy, the finite-time witness type is already empty there. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_BKMContinuationClause_allNonnegHorizons
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ ⦃T : ℝ⦄, 0 ≤ T → ExplicitBKMContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyBKMContinuationTarget_implies_BKMContinuationClause_allNonnegHorizons
      (ν := ν) (u₀ := u₀)
      (ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationTarget
        h)

/-- The repaired explicit finite-energy theorem surface still implies the
BKM-style continuation clause on every nonnegative slab.  If the input datum is
not finite-energy, the finite-time witness type is already empty there. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_BKMContinuationClause_of_nonneg_horizon
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_BKMContinuationClause_allNonnegHorizons
      (ν := ν) (u₀ := u₀) h hT

/-- Likewise, the repaired structured finite-energy theorem surface implies the
same BKM continuation clause on every nonnegative slab. -/
theorem FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_BKMContinuationClause_allNonnegHorizons
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ ⦃T : ℝ⦄, 0 ≤ T → ExplicitBKMContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_BKMContinuationClause_allNonnegHorizons
      (ν := ν) (u₀ := u₀)
      (FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget
        h)

/-- Likewise, the repaired structured finite-energy theorem surface implies the
same BKM continuation clause on every nonnegative slab. -/
theorem FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_BKMContinuationClause_of_nonneg_horizon
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν u₀ T := by
  exact
    FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_BKMContinuationClause_allNonnegHorizons
      (ν := ν) (u₀ := u₀) h hT

/-- Therefore the structured fully concrete theorem target subsumes the same
BKM-style continuation target via the explicit-equivalence theorem.  Again,
this is only a subsumption theorem, not a BKM continuation proof. -/
theorem ConcreteNavierStokesMillenniumTarget_implies_BKMContinuationTarget
    (h : ConcreteNavierStokesMillenniumTarget) :
    ExplicitBKMContinuationTarget := by
  exact ExplicitConcreteNavierStokesMillenniumTarget_implies_BKMContinuationTarget
    (ConcreteNavierStokesMillenniumTarget_implies_ExplicitConcreteNavierStokesMillenniumTarget
      h)

/-- Likewise for the structured unrepaired whole-space theorem surface as a
fixed-datum all-horizons family of unrepaired BKM clauses. -/
theorem ConcreteNavierStokesMillenniumTarget_implies_BKMContinuationClause_allHorizons
    (h : ConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ T : ℝ, ExplicitBKMContinuationClause ν u₀ T := by
  exact
    ExplicitConcreteNavierStokesMillenniumTarget_implies_BKMContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀)
      (ConcreteNavierStokesMillenniumTarget_implies_ExplicitConcreteNavierStokesMillenniumTarget
        h)

/-- Likewise for the structured unrepaired whole-space theorem surface at a
fixed horizon. -/
theorem ConcreteNavierStokesMillenniumTarget_implies_BKMContinuationClause
    (h : ConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitBKMContinuationClause ν u₀ T := by
  exact
    (ConcreteNavierStokesMillenniumTarget_implies_BKMContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀) h) T

/-- Clause-level bridge: a BKM-style continuation clause at horizon `T` implies
the uniform-vorticity continuation clause at the same horizon. -/
theorem ExplicitBKMContinuationClause_implies_uniformVorticityContinuationClause
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hClause : ExplicitBKMContinuationClause ν u₀ T) :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  intro hν hsmooth hdiv W hω
  rcases hω with ⟨B, hbound⟩
  have hEnv :
      ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
        vorticityEnvelopeOn W.velocity T Ω ∧
          integrableVorticityEnvelopeOn Ω T Bint := by
    exact uniformVorticityBoundUpTo_implies_BKMEnvelope (u := W.velocity) (T := T) (B := B) hbound
  exact hClause hν hsmooth hdiv W hEnv

/-- Since the unrepaired uniform-vorticity clause already implies its repaired
finite-energy version, the unrepaired BKM clause also lands directly on the
repaired uniform surface at the same horizon. -/
theorem ExplicitBKMContinuationClause_implies_finiteEnergyUniformVorticityContinuationClause
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hClause : ExplicitBKMContinuationClause ν u₀ T) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitUniformVorticityContinuationClause_implies_finiteEnergy
      (ExplicitBKMContinuationClause_implies_uniformVorticityContinuationClause hClause)

/-- The unrepaired BKM clause on a smaller slab also yields the repaired
uniform clause on any larger slab: first pass to the repaired uniform clause on
the smaller slab, then restrict larger-slab witnesses back down. -/
theorem ExplicitBKMContinuationClause_implies_finiteEnergyUniformVorticityContinuationClause_mono_horizon
    {ν : ℝ} {u₀ : NSInitialVelocity} {Tsmall Tlarge : ℝ}
    (hClause : ExplicitBKMContinuationClause ν u₀ Tsmall)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ Tlarge := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_mono_horizon
      (ExplicitBKMContinuationClause_implies_finiteEnergyUniformVorticityContinuationClause
        hClause) hT

/-- The same bridge also holds on the repaired finite-energy continuation
surface.  No new analytic work is needed: the repaired BKM clause simply
forgets no information on actual witnesses, because a BKM envelope still
converts directly into a uniform-vorticity bound on the same slab. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_implies_finiteEnergyUniformVorticityContinuationClause
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hClause : ExplicitFiniteEnergyBKMContinuationClause ν u₀ T) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  intro hν hsmooth hdiv hfinite W hω
  rcases hω with ⟨B, hbound⟩
  have hEnv :
      ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
        vorticityEnvelopeOn W.velocity T Ω ∧
          integrableVorticityEnvelopeOn Ω T Bint := by
    exact uniformVorticityBoundUpTo_implies_BKMEnvelope (u := W.velocity) (T := T) (B := B) hbound
  exact hClause hν hsmooth hdiv hfinite W hEnv

/-- Likewise, a repaired BKM clause on a smaller slab yields the repaired
uniform clause on any larger slab via witness restriction. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_implies_finiteEnergyUniformVorticityContinuationClause_mono_horizon
    {ν : ℝ} {u₀ : NSInitialVelocity} {Tsmall Tlarge : ℝ}
    (hClause : ExplicitFiniteEnergyBKMContinuationClause ν u₀ Tsmall)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ Tlarge := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_mono_horizon
      (ExplicitFiniteEnergyBKMContinuationClause_implies_finiteEnergyUniformVorticityContinuationClause
        hClause) hT

/-- Therefore the unrepaired BKM target also implies the repaired
uniform-vorticity continuation target. -/
theorem ExplicitBKMContinuationTarget_implies_finiteEnergyUniformVorticityContinuationTarget
    (hBKM : ExplicitBKMContinuationTarget) :
    ExplicitFiniteEnergyUniformVorticityContinuationTarget := by
  intro ν u₀ T
  exact
    ExplicitFiniteEnergyBKMContinuationClause_implies_finiteEnergyUniformVorticityContinuationClause
      (ExplicitBKMContinuationTarget_implies_finiteEnergyBKMContinuationTarget hBKM ν u₀ T)

/-- The unrepaired BKM target also exports the whole fixed-datum family of
repaired uniform-vorticity continuation clauses. -/
theorem ExplicitBKMContinuationTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons
    (hBKM : ExplicitBKMContinuationTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ T : ℝ, ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  intro T
  exact
    ExplicitFiniteEnergyBKMContinuationClause_implies_finiteEnergyUniformVorticityContinuationClause
      (ExplicitBKMContinuationTarget_implies_finiteEnergyBKMContinuationTarget hBKM ν u₀ T)

/-- Hence the unrepaired BKM target also implies the repaired uniform clause at
each fixed horizon directly. -/
theorem ExplicitBKMContinuationTarget_implies_finiteEnergyUniformVorticityContinuationClause
    (hBKM : ExplicitBKMContinuationTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    (ExplicitBKMContinuationTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀) hBKM) T

/-- Therefore the repaired BKM target implies the repaired uniform-vorticity
target. -/
theorem ExplicitFiniteEnergyBKMContinuationTarget_implies_finiteEnergyUniformVorticityContinuationTarget
    (hBKM : ExplicitFiniteEnergyBKMContinuationTarget) :
    ExplicitFiniteEnergyUniformVorticityContinuationTarget := by
  intro ν u₀ T
  exact
    ExplicitFiniteEnergyBKMContinuationClause_implies_finiteEnergyUniformVorticityContinuationClause
      (hClause := hBKM ν u₀ T)

/-- The repaired BKM target also exports the whole fixed-datum family of
repaired uniform-vorticity continuation clauses. -/
theorem ExplicitFiniteEnergyBKMContinuationTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons
    (hBKM : ExplicitFiniteEnergyBKMContinuationTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ T : ℝ, ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  intro T
  exact
    ExplicitFiniteEnergyBKMContinuationClause_implies_finiteEnergyUniformVorticityContinuationClause
      (hClause := hBKM ν u₀ T)

/-- Hence the repaired BKM target implies the repaired uniform clause at each
fixed horizon directly. -/
theorem ExplicitFiniteEnergyBKMContinuationTarget_implies_finiteEnergyUniformVorticityContinuationClause
    (hBKM : ExplicitFiniteEnergyBKMContinuationTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    (ExplicitFiniteEnergyBKMContinuationTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀) hBKM) T

/-- On a nonnegative slab, the repaired BKM clause also implies the unrepaired
uniform-vorticity clause: once an actual witness exists, the repaired/unrepaired
uniform clauses coincide on that slab. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_implies_uniformVorticityContinuationClause_of_nonneg_horizon
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hClause : ExplicitFiniteEnergyBKMContinuationClause ν u₀ T)
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitBKMContinuationClause_implies_uniformVorticityContinuationClause
      (hClause :=
        ExplicitFiniteEnergyBKMContinuationClause_implies_BKMContinuationClause_of_nonneg_horizon
          hClause hT)

/-- Hence the repaired BKM target gives the unrepaired uniform-vorticity clause
on every fixed nonnegative horizon. -/
theorem ExplicitFiniteEnergyBKMContinuationTarget_implies_uniformVorticityContinuationClause_of_nonneg_horizon
    (hBKM : ExplicitFiniteEnergyBKMContinuationTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitBKMContinuationClause_implies_uniformVorticityContinuationClause
      (hClause :=
        ExplicitFiniteEnergyBKMContinuationTarget_implies_BKMContinuationClause_of_nonneg_horizon
          hBKM hT)

/-- The corrected nonnegative-horizon repaired BKM target gives the unrepaired
uniform-vorticity clause on every fixed nonnegative horizon. -/
theorem
    ExplicitFiniteEnergyBKMContinuationTargetOnNonnegHorizons_implies_uniformVorticityContinuationClause_of_nonneg_horizon
    (hBKM : ExplicitFiniteEnergyBKMContinuationTargetOnNonnegHorizons)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitBKMContinuationClause_implies_uniformVorticityContinuationClause
      (hClause :=
        ExplicitFiniteEnergyBKMContinuationTargetOnNonnegHorizons_implies_BKMContinuationClause_of_nonneg_horizon
          hBKM hT)

/-- The repaired BKM target also gives the unrepaired uniform clause family on
every nonnegative horizon. -/
theorem ExplicitFiniteEnergyBKMContinuationTarget_implies_uniformVorticityContinuationClause_allNonnegHorizons
    (hBKM : ExplicitFiniteEnergyBKMContinuationTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ ⦃T : ℝ⦄, 0 ≤ T → ExplicitUniformVorticityContinuationClause ν u₀ T := by
  intro T hT
  exact
    ExplicitFiniteEnergyBKMContinuationTarget_implies_uniformVorticityContinuationClause_of_nonneg_horizon
      (ν := ν) (u₀ := u₀) (T := T) hBKM hT

/-- The corrected nonnegative-horizon repaired BKM target gives the unrepaired
uniform-vorticity clause family on every nonnegative horizon. -/
theorem
    ExplicitFiniteEnergyBKMContinuationTargetOnNonnegHorizons_implies_uniformVorticityContinuationClause_allNonnegHorizons
    (hBKM : ExplicitFiniteEnergyBKMContinuationTargetOnNonnegHorizons)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ ⦃T : ℝ⦄, 0 ≤ T → ExplicitUniformVorticityContinuationClause ν u₀ T := by
  intro T hT
  exact
    ExplicitFiniteEnergyBKMContinuationTargetOnNonnegHorizons_implies_uniformVorticityContinuationClause_of_nonneg_horizon
      (ν := ν) (u₀ := u₀) (T := T) hBKM hT

/-- The BKM-style target implies the uniform-vorticity continuation target.
Unlike the global-theorem subsumption lemmas, this proof uses the continuation
hypothesis by converting a uniform slab bound into an explicit integrable
envelope. -/
theorem ExplicitBKMContinuationTarget_implies_uniformVorticityContinuationTarget
    (hBKM : ExplicitBKMContinuationTarget) :
    ExplicitUniformVorticityContinuationTarget := by
  intro ν u₀ T
  exact ExplicitBKMContinuationClause_implies_uniformVorticityContinuationClause
    (hClause := hBKM ν u₀ T)

/-- The unrepaired BKM target also exports the whole fixed-datum family of
unrepaired uniform-vorticity continuation clauses. -/
theorem ExplicitBKMContinuationTarget_implies_uniformVorticityContinuationClause_allHorizons
    (hBKM : ExplicitBKMContinuationTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ T : ℝ, ExplicitUniformVorticityContinuationClause ν u₀ T := by
  intro T
  exact ExplicitBKMContinuationClause_implies_uniformVorticityContinuationClause
    (hClause := hBKM ν u₀ T)

/-- Hence the unrepaired BKM target implies the unrepaired uniform clause at
each fixed horizon directly. -/
theorem ExplicitBKMContinuationTarget_implies_uniformVorticityContinuationClause
    (hBKM : ExplicitBKMContinuationTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    (ExplicitBKMContinuationTarget_implies_uniformVorticityContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀) hBKM) T

/-- The unrepaired explicit whole-space theorem surface therefore also implies
the unrepaired uniform-vorticity continuation target through the BKM route. -/
theorem ExplicitConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationTarget_via_BKM
    (h : ExplicitConcreteNavierStokesMillenniumTarget) :
    ExplicitUniformVorticityContinuationTarget := by
  exact
    ExplicitBKMContinuationTarget_implies_uniformVorticityContinuationTarget
      (ExplicitConcreteNavierStokesMillenniumTarget_implies_BKMContinuationTarget h)

/-- The same unrepaired explicit theorem surface also exports the whole
fixed-datum family of unrepaired uniform clauses explicitly through the BKM
route. -/
theorem ExplicitConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_allHorizons_via_BKM
    (h : ExplicitConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ T : ℝ, ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitBKMContinuationTarget_implies_uniformVorticityContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀)
      (ExplicitConcreteNavierStokesMillenniumTarget_implies_BKMContinuationTarget h)

/-- Hence the same theorem surface reaches each fixed unrepaired uniform clause
directly through the BKM route. -/
theorem ExplicitConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_via_BKM
    (h : ExplicitConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    (ExplicitConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_allHorizons_via_BKM
      (ν := ν) (u₀ := u₀) h) T

/-- The same unrepaired explicit theorem surface also reaches the repaired
uniform-vorticity continuation target through the repaired BKM route. -/
theorem ExplicitConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationTarget_via_BKM
    (h : ExplicitConcreteNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyUniformVorticityContinuationTarget := by
  exact
    ExplicitBKMContinuationTarget_implies_finiteEnergyUniformVorticityContinuationTarget
      (ExplicitConcreteNavierStokesMillenniumTarget_implies_BKMContinuationTarget h)

/-- The same unrepaired explicit theorem surface also exports the whole
fixed-datum family of repaired uniform clauses through the repaired BKM route. -/
theorem ExplicitConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons_via_BKM
    (h : ExplicitConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ T : ℝ, ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitBKMContinuationTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀)
      (ExplicitConcreteNavierStokesMillenniumTarget_implies_BKMContinuationTarget h)

/-- Hence the same theorem surface reaches each fixed repaired uniform clause
directly through the BKM route. -/
theorem ExplicitConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_via_BKM
    (h : ExplicitConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    (ExplicitConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons_via_BKM
      (ν := ν) (u₀ := u₀) h) T

/-- The repaired explicit finite-energy theorem surface reaches the repaired
uniform-vorticity continuation target through the repaired BKM target. -/
theorem
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationTarget_via_BKM
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyUniformVorticityContinuationTarget := by
  exact
    ExplicitFiniteEnergyBKMContinuationTarget_implies_finiteEnergyUniformVorticityContinuationTarget
      (ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationTarget
        h)

/-- The repaired explicit finite-energy theorem surface also exports the whole
fixed-datum family of repaired uniform clauses through the repaired BKM route. -/
theorem
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons_via_BKM
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ T : ℝ, ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyBKMContinuationTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀)
      (ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationTarget
        h)

/-- Hence the repaired explicit theorem surface reaches each fixed repaired
uniform clause directly through the same BKM route. -/
theorem
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_via_BKM
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    (ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons_via_BKM
      (ν := ν) (u₀ := u₀) h) T

/-- Likewise for the structured repaired finite-energy theorem surface. -/
theorem FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationTarget_via_BKM
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyUniformVorticityContinuationTarget := by
  exact
    ExplicitFiniteEnergyBKMContinuationTarget_implies_finiteEnergyUniformVorticityContinuationTarget
      (FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationTarget h)

/-- Likewise for the structured repaired theorem surface as a fixed-datum
all-horizons family of repaired uniform clauses through the BKM route. -/
theorem FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons_via_BKM
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ T : ℝ, ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyBKMContinuationTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀)
      (FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationTarget h)

/-- Likewise for the structured repaired theorem surface at each fixed horizon
through the BKM route. -/
theorem FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_via_BKM
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    (FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons_via_BKM
      (ν := ν) (u₀ := u₀) h) T

/-- Likewise for the structured unrepaired whole-space theorem surface on the
unrepaired uniform target. -/
theorem ConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationTarget_via_BKM
    (h : ConcreteNavierStokesMillenniumTarget) :
    ExplicitUniformVorticityContinuationTarget := by
  exact
    ExplicitBKMContinuationTarget_implies_uniformVorticityContinuationTarget
      (ConcreteNavierStokesMillenniumTarget_implies_BKMContinuationTarget h)

/-- Likewise for the structured unrepaired theorem surface as a fixed-datum
all-horizons family of unrepaired uniform clauses through the BKM route. -/
theorem ConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_allHorizons_via_BKM
    (h : ConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ T : ℝ, ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitBKMContinuationTarget_implies_uniformVorticityContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀)
      (ConcreteNavierStokesMillenniumTarget_implies_BKMContinuationTarget h)

/-- Likewise for the structured unrepaired theorem surface at each fixed
unrepaired uniform horizon through the BKM route. -/
theorem ConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_via_BKM
    (h : ConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    (ConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_allHorizons_via_BKM
      (ν := ν) (u₀ := u₀) h) T

/-- Likewise for the structured unrepaired whole-space theorem surface on the
repaired uniform target. -/
theorem ConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationTarget_via_BKM
    (h : ConcreteNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyUniformVorticityContinuationTarget := by
  exact
    ExplicitBKMContinuationTarget_implies_finiteEnergyUniformVorticityContinuationTarget
      (ConcreteNavierStokesMillenniumTarget_implies_BKMContinuationTarget h)

/-- Likewise for the structured unrepaired theorem surface as a fixed-datum
all-horizons family of repaired uniform clauses through the BKM route. -/
theorem ConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons_via_BKM
    (h : ConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ T : ℝ, ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitBKMContinuationTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀)
      (ConcreteNavierStokesMillenniumTarget_implies_BKMContinuationTarget h)

/-- Likewise for the structured unrepaired theorem surface at each fixed
repaired uniform horizon through the BKM route. -/
theorem ConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_via_BKM
    (h : ConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    (ConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons_via_BKM
      (ν := ν) (u₀ := u₀) h) T

/-- The repaired explicit finite-energy theorem surface also exports the
unrepaired uniform clause family on every nonnegative horizon through the
repaired BKM target. -/
theorem
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_allNonnegHorizons_via_BKM
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ ⦃T : ℝ⦄, 0 ≤ T → ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyBKMContinuationTarget_implies_uniformVorticityContinuationClause_allNonnegHorizons
      (ν := ν) (u₀ := u₀)
      (ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationTarget
        h)

/-- Hence the repaired explicit finite-energy theorem surface reaches the
unrepaired uniform clause at each fixed nonnegative horizon through the same
BKM route. -/
theorem
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_of_nonneg_horizon_via_BKM
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_allNonnegHorizons_via_BKM
      (ν := ν) (u₀ := u₀) h hT

/-- Likewise for the structured repaired finite-energy theorem surface. -/
theorem FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_allNonnegHorizons_via_BKM
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ∀ ⦃T : ℝ⦄, 0 ≤ T → ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyBKMContinuationTarget_implies_uniformVorticityContinuationClause_allNonnegHorizons
      (ν := ν) (u₀ := u₀)
      (FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationTarget h)

/-- Likewise for the structured repaired finite-energy theorem surface at each
fixed nonnegative horizon. -/
theorem FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_of_nonneg_horizon_via_BKM
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_allNonnegHorizons_via_BKM
      (ν := ν) (u₀ := u₀) h hT

/-- The unrepaired BKM continuation clause is directly inhabitable at zero
initial data: any finite-time witness with an integrable vorticity envelope may
be discarded in favor of the explicit global zero solution. -/
theorem ExplicitBKMContinuationClause_zero
    (ν T : ℝ) :
    ExplicitBKMContinuationClause ν (0 : NSInitialVelocity) T := by
  exact
    ExplicitConcreteNavierStokesRegularityClause_implies_ExplicitBKMContinuationClause
      (T := T) (ExplicitConcreteNavierStokesRegularityClause_zero ν)

/-- The repaired finite-energy BKM continuation clause is likewise directly
inhabitable at zero initial data. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_zero
    (ν T : ℝ) :
    ExplicitFiniteEnergyBKMContinuationClause ν (0 : NSInitialVelocity) T := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_implies_ExplicitFiniteEnergyBKMContinuationClause
      (T := T) (ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_zero ν)

/-- Clause-level operational consequence at zero initial data: applying a
BKM-style continuation clause to the canonical zero slab witness and its
explicit envelope data yields a global explicit output. -/
theorem ExplicitBKMContinuationClause_implies_zeroGlobalOutput
    {ν T : ℝ}
    (hClause : ExplicitBKMContinuationClause ν (0 : NSInitialVelocity) T)
    (hν : 0 < ν) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  have hdiv0 : ∀ x, initialSpatialDivergence (0 : NSInitialVelocity) x = 0 := by
    intro x
    simpa using (initialSpatialDivergence_zero x)
  rcases zeroFiniteTimeRegularityWitness_exhibits_BKMContinuationPremise ν T with
    ⟨W, hEnv⟩
  exact hClause hν smoothInitialVelocityData_zero hdiv0 W hEnv

/-- Nontrivial operational pressure-gauge sanity check: a smaller-slab BKM
continuation clause can be applied to a larger zero witness after adding any
smooth time-only pressure gauge and restricting back down. -/
theorem ExplicitBKMContinuationClause_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
    {ν Tsmall Tlarge : ℝ}
    (hClause : ExplicitBKMContinuationClause ν (0 : NSInitialVelocity) Tsmall)
    (hν : 0 < ν)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  have hdiv0 : ∀ x, initialSpatialDivergence (0 : NSInitialVelocity) x = 0 := by
    intro x
    simpa using (initialSpatialDivergence_zero x)
  have hEnv :
      ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
        vorticityEnvelopeOn
          (((zeroFiniteTimeRegularityWitness ν Tlarge).addPressureOfZeroSpatialGradient q hq hq_zero).restrict hT).velocity
          Tsmall Ω ∧
          integrableVorticityEnvelopeOn Ω Tsmall Bint :=
    zeroFiniteTimeRegularityWitness_addPressureOfZeroSpatialGradient_restrict_has_BKMEnvelope
      ν Tsmall Tlarge q hq hq_zero hT
  exact hClause hν smoothInitialVelocityData_zero hdiv0
    (((zeroFiniteTimeRegularityWitness ν Tlarge).addPressureOfZeroSpatialGradient q hq hq_zero).restrict hT) hEnv

/-- Time-only special case of the zero-data BKM clause-level
zero-spatial-gradient transport theorem. -/
theorem ExplicitBKMContinuationClause_implies_zeroGlobalOutput_timeOnlyPressure
    {ν Tsmall Tlarge : ℝ}
    (hClause : ExplicitBKMContinuationClause ν (0 : NSInitialVelocity) Tsmall)
    (hν : 0 < ν)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitBKMContinuationClause_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      hClause hν
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)
      hT

/-- Constant-pressure special case of the BKM clause-level pressure-gauge
sanity check at zero initial data. -/
theorem ExplicitBKMContinuationClause_implies_zeroGlobalOutput_constantPressure
    {ν T : ℝ}
    (hClause : ExplicitBKMContinuationClause ν (0 : NSInitialVelocity) T)
    (hν : 0 < ν)
    (c : ℝ) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitBKMContinuationClause_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      (Tsmall := T) (Tlarge := T) hClause hν
      (fun _ : NSTime => fun _ : NSSpace => c)
      (smoothSpaceTimePressure_const c)
      (fun t x => spatialPressureGradient_const c t x)
      le_rfl

/-- Operational consequence of the BKM-style target at zero initial data:
combining the BKM-to-uniform bridge with the zero-data uniform instantiation
gives an explicit global output for positive viscosity. -/
theorem ExplicitBKMContinuationTarget_implies_zeroGlobalOutput
    (hBKM : ExplicitBKMContinuationTarget)
    {ν T : ℝ} (hν : 0 < ν) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  have hClause : ExplicitBKMContinuationClause ν (0 : NSInitialVelocity) T :=
    hBKM ν (0 : NSInitialVelocity) T
  exact ExplicitBKMContinuationClause_implies_zeroGlobalOutput hClause hν

/-- Target-level operational pressure-gauge sanity check on the unrepaired BKM
layer: the target applies on any smaller zero slab after adding a smooth
time-only pressure gauge on a larger zero witness and restricting back down. -/
theorem ExplicitBKMContinuationTarget_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
    (hBKM : ExplicitBKMContinuationTarget)
    {ν Tsmall Tlarge : ℝ}
    (hν : 0 < ν)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  have hClause : ExplicitBKMContinuationClause ν (0 : NSInitialVelocity) Tsmall :=
    hBKM ν (0 : NSInitialVelocity) Tsmall
  exact
    ExplicitBKMContinuationClause_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      hClause hν q hq hq_zero hT

/-- Time-only special case of the zero-data BKM target-level
zero-spatial-gradient transport theorem. -/
theorem ExplicitBKMContinuationTarget_implies_zeroGlobalOutput_timeOnlyPressure
    (hBKM : ExplicitBKMContinuationTarget)
    {ν Tsmall Tlarge : ℝ}
    (hν : 0 < ν)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitBKMContinuationTarget_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      hBKM hν
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)
      hT

/-- Constant-pressure special case of the BKM target-level pressure-gauge
sanity check at zero initial data. -/
theorem ExplicitBKMContinuationTarget_implies_zeroGlobalOutput_constantPressure
    (hBKM : ExplicitBKMContinuationTarget)
    {ν T : ℝ}
    (hν : 0 < ν)
    (c : ℝ) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitBKMContinuationTarget_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      (Tsmall := T) (Tlarge := T) hBKM hν
      (fun _ : NSTime => fun _ : NSSpace => c)
      (smoothSpaceTimePressure_const c)
      (fun t x => spatialPressureGradient_const c t x)
      le_rfl

/-- The unrepaired BKM continuation target is false as stated. For a negative
horizon, nonzero linear shear admits a formal finite-time witness with a
vacuous BKM envelope on the empty slab, while the required global
bounded-energy output is already impossible on `ℝ^3`. -/
theorem not_ExplicitBKMContinuationTarget :
    ¬ ExplicitBKMContinuationTarget := by
  intro hBKM
  have hν : 0 < (1 : ℝ) := by positivity
  have hdiv :
      ∀ x, initialSpatialDivergence (linearShearInitialVelocity 1) x = 0 := by
    intro x
    simpa using initialSpatialDivergence_linearShearInitialVelocity 1 x
  let W : ExplicitFiniteTimeRegularityWitness 1 (linearShearInitialVelocity 1) (-1) :=
    explicitFiniteTimeRegularityWitness_linearShearInitialVelocity_of_lt_zero
      (ν := 1) (T := -1) (a := 1) (by norm_num)
  have hΩ : vorticityEnvelopeOn W.velocity (-1) (fun _ : NSTime => 0) := by
    refine ⟨?_, ?_⟩
    · intro t ht0 htT
      exfalso
      linarith
    · intro t x ht0 htT
      exfalso
      linarith
  have hEnv :
      ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
        vorticityEnvelopeOn W.velocity (-1) Ω ∧
          integrableVorticityEnvelopeOn Ω (-1) Bint := by
    exact ⟨(fun _ : NSTime => 0), 0, hΩ, integrableVorticityEnvelopeOn_zero (-1)⟩
  exact
    not_ExplicitConcreteNavierStokesGlobalOutput_linearShearInitialVelocity one_ne_zero
      (hBKM 1 (linearShearInitialVelocity 1) (-1)
        hν
        (smoothInitialVelocityData_linearShearInitialVelocity 1)
        hdiv W hEnv)

/-- Clause-level operational consequence for the repaired finite-energy BKM
layer: zero initial data satisfy the repaired input hypothesis directly, so a
repaired BKM clause instance can be applied to the canonical zero slab witness
and its explicit envelope data without vacuity. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_implies_zeroGlobalOutput
    {ν T : ℝ}
    (hClause : ExplicitFiniteEnergyBKMContinuationClause ν (0 : NSInitialVelocity) T)
    (hν : 0 < ν) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  have hdiv0 : ∀ x, initialSpatialDivergence (0 : NSInitialVelocity) x = 0 := by
    intro x
    simpa using (initialSpatialDivergence_zero x)
  rcases zeroFiniteTimeRegularityWitness_exhibits_BKMContinuationPremise ν T with
    ⟨W, hEnv⟩
  exact hClause hν smoothInitialVelocityData_zero hdiv0 finiteInitialKineticEnergy_zero W hEnv

/-- Nontrivial operational pressure-gauge sanity check on the repaired
finite-energy BKM layer: a smaller-slab repaired clause can be applied to a
larger zero witness after adding any smooth time-only pressure gauge and
restricting back down. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
    {ν Tsmall Tlarge : ℝ}
    (hClause : ExplicitFiniteEnergyBKMContinuationClause ν (0 : NSInitialVelocity) Tsmall)
    (hν : 0 < ν)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  have hdiv0 : ∀ x, initialSpatialDivergence (0 : NSInitialVelocity) x = 0 := by
    intro x
    simpa using (initialSpatialDivergence_zero x)
  have hEnv :
      ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
        vorticityEnvelopeOn
          (((zeroFiniteTimeRegularityWitness ν Tlarge).addPressureOfZeroSpatialGradient q hq hq_zero).restrict hT).velocity
          Tsmall Ω ∧
          integrableVorticityEnvelopeOn Ω Tsmall Bint :=
    zeroFiniteTimeRegularityWitness_addPressureOfZeroSpatialGradient_restrict_has_BKMEnvelope
      ν Tsmall Tlarge q hq hq_zero hT
  exact hClause hν smoothInitialVelocityData_zero hdiv0 finiteInitialKineticEnergy_zero
    (((zeroFiniteTimeRegularityWitness ν Tlarge).addPressureOfZeroSpatialGradient q hq hq_zero).restrict hT) hEnv

/-- Time-only special case of the repaired zero-data BKM clause-level
zero-spatial-gradient transport theorem. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_implies_zeroGlobalOutput_timeOnlyPressure
    {ν Tsmall Tlarge : ℝ}
    (hClause : ExplicitFiniteEnergyBKMContinuationClause ν (0 : NSInitialVelocity) Tsmall)
    (hν : 0 < ν)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      hClause hν
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)
      hT

/-- Constant-pressure special case of the repaired BKM clause-level
pressure-gauge sanity check at zero initial data. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_implies_zeroGlobalOutput_constantPressure
    {ν T : ℝ}
    (hClause : ExplicitFiniteEnergyBKMContinuationClause ν (0 : NSInitialVelocity) T)
    (hν : 0 < ν)
    (c : ℝ) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      (Tsmall := T) (Tlarge := T) hClause hν
      (fun _ : NSTime => fun _ : NSSpace => c)
      (smoothSpaceTimePressure_const c)
      (fun t x => spatialPressureGradient_const c t x)
      le_rfl

/-- The repaired finite-energy BKM target is likewise operational at zero
initial data: the zero datum satisfies the repaired input hypothesis directly,
so the target applies to the canonical zero slab witness with its explicit BKM
envelope. -/
theorem ExplicitFiniteEnergyBKMContinuationTarget_implies_zeroGlobalOutput
    (hBKM : ExplicitFiniteEnergyBKMContinuationTarget)
    {ν T : ℝ} (hν : 0 < ν) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  have hClause : ExplicitFiniteEnergyBKMContinuationClause ν (0 : NSInitialVelocity) T :=
    hBKM ν (0 : NSInitialVelocity) T
  exact ExplicitFiniteEnergyBKMContinuationClause_implies_zeroGlobalOutput hClause hν

/-- Target-level repaired time-gauge sanity check: the repaired finite-energy
BKM target applies on any smaller zero slab after adding a smooth time-only
pressure gauge on a larger zero witness and restricting back down. -/
theorem ExplicitFiniteEnergyBKMContinuationTarget_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
    (hBKM : ExplicitFiniteEnergyBKMContinuationTarget)
    {ν Tsmall Tlarge : ℝ}
    (hν : 0 < ν)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  have hClause : ExplicitFiniteEnergyBKMContinuationClause ν (0 : NSInitialVelocity) Tsmall :=
    hBKM ν (0 : NSInitialVelocity) Tsmall
  exact
    ExplicitFiniteEnergyBKMContinuationClause_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      hClause hν q hq hq_zero hT

/-- Time-only special case of the repaired zero-data BKM target-level
zero-spatial-gradient transport theorem. -/
theorem ExplicitFiniteEnergyBKMContinuationTarget_implies_zeroGlobalOutput_timeOnlyPressure
    (hBKM : ExplicitFiniteEnergyBKMContinuationTarget)
    {ν Tsmall Tlarge : ℝ}
    (hν : 0 < ν)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitFiniteEnergyBKMContinuationTarget_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      hBKM hν
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)
      hT

/-- Constant-pressure special case of the repaired BKM target-level
pressure-gauge sanity check at zero initial data. -/
theorem ExplicitFiniteEnergyBKMContinuationTarget_implies_zeroGlobalOutput_constantPressure
    (hBKM : ExplicitFiniteEnergyBKMContinuationTarget)
    {ν T : ℝ}
    (hν : 0 < ν)
    (c : ℝ) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitFiniteEnergyBKMContinuationTarget_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      (Tsmall := T) (Tlarge := T) hBKM hν
      (fun _ : NSTime => fun _ : NSSpace => c)
      (smoothSpaceTimePressure_const c)
      (fun t x => spatialPressureGradient_const c t x)
      le_rfl

/-- If the concrete finite-time witness type is empty on a slab, then the
BKM continuation clause is true there only vacuously. -/
theorem ExplicitBKMContinuationClause_of_not_nonempty_finiteTimeWitness
    {ν T : ℝ} {u₀ : NSInitialVelocity}
    (hEmpty : ¬ Nonempty (ExplicitFiniteTimeRegularityWitness ν u₀ T)) :
    ExplicitBKMContinuationClause ν u₀ T := by
  intro hν hsmooth hdiv W hEnv
  exfalso
  exact hEmpty ⟨W⟩

/-- On nonnegative slabs, the explicit BKM continuation clause is likewise
trivially satisfied for nonzero constant initial data because it quantifies over
the same finite-time witness type, which is already uninhabited there. -/
theorem ExplicitBKMContinuationClause_constantInitialVelocity
    {ν T : ℝ} {c : NSSpace}
    (hc : c ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν (constantInitialVelocity c) T := by
  exact
    ExplicitBKMContinuationClause_of_not_nonempty_finiteTimeWitness
      (u₀ := constantInitialVelocity c)
      (not_nonempty_ExplicitFiniteTimeRegularityWitness_constantInitialVelocity
        (ν := ν) (T := T) hc hT)

/-- The same vacuity caveat holds on the BKM surface: the clause can be true on
nonzero constant initial data while the concrete regularity clause remains
false. -/
theorem ExplicitBKMContinuationClause_constantInitialVelocity_without_regularity
    {ν T : ℝ} {c : NSSpace}
    (hν : 0 < ν)
    (hc : c ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν (constantInitialVelocity c) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν (constantInitialVelocity c) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitBKMContinuationClause_constantInitialVelocity
      (ν := ν) (T := T) hc hT
  · exact not_ExplicitConcreteNavierStokesRegularityClause_constantInitialVelocity hν hc

/-- The repaired BKM continuation clause is also vacuous on nonzero constant
initial data because the repaired finite-energy input hypothesis already fails.
No horizon sign condition is needed. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_constantInitialVelocity
    {ν T : ℝ} {c : NSSpace}
    (hc : c ≠ 0) :
    ExplicitFiniteEnergyBKMContinuationClause ν (constantInitialVelocity c) T := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_of_not_finiteInitialKineticEnergy
      (u₀ := constantInitialVelocity c)
      (not_finiteInitialKineticEnergy_constantInitialVelocity hc)

/-- The repaired BKM continuation clause can therefore also be true on nonzero
constant initial data while the concrete regularity clause is false there. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_constantInitialVelocity_without_regularity
    {ν T : ℝ} {c : NSSpace}
    (hν : 0 < ν)
    (hc : c ≠ 0) :
    ExplicitFiniteEnergyBKMContinuationClause ν (constantInitialVelocity c) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν (constantInitialVelocity c) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitFiniteEnergyBKMContinuationClause_constantInitialVelocity
      (ν := ν) (T := T) hc
  · exact not_ExplicitConcreteNavierStokesRegularityClause_constantInitialVelocity hν hc

/-- The same BKM-side vacuity caveat holds for nonzero linear shear initial
data: the clause is true on nonnegative slabs because the finite-time witness
type is already empty there. -/
theorem ExplicitBKMContinuationClause_linearShearInitialVelocity
    {ν T : ℝ} {a : ℝ}
    (ha : a ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν (linearShearInitialVelocity a) T := by
  exact
    ExplicitBKMContinuationClause_of_not_nonempty_finiteTimeWitness
      (u₀ := linearShearInitialVelocity a)
      (not_nonempty_ExplicitFiniteTimeRegularityWitness_linearShearInitialVelocity
        (ν := ν) (T := T) ha hT)

/-- The BKM continuation clause can therefore also be true on nonzero linear
shear initial data while the concrete regularity clause is false there. -/
theorem ExplicitBKMContinuationClause_linearShearInitialVelocity_without_regularity
    {ν T : ℝ} {a : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν (linearShearInitialVelocity a) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν (linearShearInitialVelocity a) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitBKMContinuationClause_linearShearInitialVelocity
      (ν := ν) (T := T) ha hT
  · exact not_ExplicitConcreteNavierStokesRegularityClause_linearShearInitialVelocity hν ha

/-- The repaired BKM continuation clause is also vacuous on nonzero linear
shear data because the repaired finite-energy input hypothesis already fails.
Again, no horizon sign condition is needed. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_linearShearInitialVelocity
    {ν T : ℝ} {a : ℝ}
    (ha : a ≠ 0) :
    ExplicitFiniteEnergyBKMContinuationClause ν (linearShearInitialVelocity a) T := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_of_not_finiteInitialKineticEnergy
      (u₀ := linearShearInitialVelocity a)
      (not_finiteInitialKineticEnergy_linearShearInitialVelocity ha)

/-- The repaired BKM continuation clause can therefore also be true on
nonzero linear shear data while the concrete regularity clause is false there.
-/
theorem ExplicitFiniteEnergyBKMContinuationClause_linearShearInitialVelocity_without_regularity
    {ν T : ℝ} {a : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) :
    ExplicitFiniteEnergyBKMContinuationClause ν (linearShearInitialVelocity a) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν (linearShearInitialVelocity a) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitFiniteEnergyBKMContinuationClause_linearShearInitialVelocity
      (ν := ν) (T := T) ha
  · exact not_ExplicitConcreteNavierStokesRegularityClause_linearShearInitialVelocity hν ha

/-- The same BKM-side vacuity caveat holds for nonzero affine shear initial
data `x ↦ (a * x₁, 0, b)`: on nonnegative slabs the clause is true because the
finite-time witness type is already empty there. -/
theorem ExplicitBKMContinuationClause_linearShearVerticalDriftInitialVelocity
    {ν T : ℝ} {a b : ℝ}
    (ha : a ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν (linearShearVerticalDriftInitialVelocity a b) T := by
  exact
    ExplicitBKMContinuationClause_of_not_nonempty_finiteTimeWitness
      (u₀ := linearShearVerticalDriftInitialVelocity a b)
      (not_nonempty_ExplicitFiniteTimeRegularityWitness_linearShearVerticalDriftInitialVelocity
        (ν := ν) (T := T) (a := a) (b := b) ha hT)

/-- The BKM continuation clause can therefore also be true on nonzero affine
shear data while the concrete regularity clause is false there. -/
theorem ExplicitBKMContinuationClause_linearShearVerticalDriftInitialVelocity_without_regularity
    {ν T : ℝ} {a b : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν (linearShearVerticalDriftInitialVelocity a b) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (linearShearVerticalDriftInitialVelocity a b) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitBKMContinuationClause_linearShearVerticalDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (b := b) ha hT
  · exact
      not_ExplicitConcreteNavierStokesRegularityClause_linearShearVerticalDriftInitialVelocity
        hν ha

/-- The repaired BKM continuation clause is also vacuous on nonzero affine
shear data because the repaired finite-energy input hypothesis already fails. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_linearShearVerticalDriftInitialVelocity
    {ν T : ℝ} {a b : ℝ}
    (ha : a ≠ 0) :
    ExplicitFiniteEnergyBKMContinuationClause ν
      (linearShearVerticalDriftInitialVelocity a b) T := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_of_not_finiteInitialKineticEnergy
      (u₀ := linearShearVerticalDriftInitialVelocity a b)
      (not_finiteInitialKineticEnergy_linearShearVerticalDriftInitialVelocity
        (a := a) (b := b) ha)

/-- The repaired BKM continuation clause can therefore also be true on nonzero
affine shear data while the concrete regularity clause is false there. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_linearShearVerticalDriftInitialVelocity_without_regularity
    {ν T : ℝ} {a b : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) :
    ExplicitFiniteEnergyBKMContinuationClause ν
        (linearShearVerticalDriftInitialVelocity a b) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (linearShearVerticalDriftInitialVelocity a b) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitFiniteEnergyBKMContinuationClause_linearShearVerticalDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (b := b) ha
  · exact
      not_ExplicitConcreteNavierStokesRegularityClause_linearShearVerticalDriftInitialVelocity
        hν ha

/-- The same BKM-side vacuity caveat holds for nonzero affine shear initial
data `x ↦ (a * x₁, b, 0)`: on nonnegative slabs the clause is true because the
finite-time witness type is already empty there. -/
theorem ExplicitBKMContinuationClause_linearShearHorizontalDriftInitialVelocity
    {ν T : ℝ} {a b : ℝ}
    (ha : a ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν (linearShearHorizontalDriftInitialVelocity a b) T := by
  exact
    ExplicitBKMContinuationClause_of_not_nonempty_finiteTimeWitness
      (u₀ := linearShearHorizontalDriftInitialVelocity a b)
      (not_nonempty_ExplicitFiniteTimeRegularityWitness_linearShearHorizontalDriftInitialVelocity
        (ν := ν) (T := T) (a := a) (b := b) ha hT)

/-- The BKM continuation clause can therefore also be true on nonzero affine
shear data `x ↦ (a * x₁, b, 0)` while the concrete regularity clause is false
there. -/
theorem ExplicitBKMContinuationClause_linearShearHorizontalDriftInitialVelocity_without_regularity
    {ν T : ℝ} {a b : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν (linearShearHorizontalDriftInitialVelocity a b) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (linearShearHorizontalDriftInitialVelocity a b) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitBKMContinuationClause_linearShearHorizontalDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (b := b) ha hT
  · exact
      not_ExplicitConcreteNavierStokesRegularityClause_linearShearHorizontalDriftInitialVelocity
        hν ha

/-- The repaired BKM continuation clause is also vacuous on nonzero affine
shear data `x ↦ (a * x₁, b, 0)` because the repaired finite-energy input
hypothesis already fails. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_linearShearHorizontalDriftInitialVelocity
    {ν T : ℝ} {a b : ℝ}
    (ha : a ≠ 0) :
    ExplicitFiniteEnergyBKMContinuationClause ν
      (linearShearHorizontalDriftInitialVelocity a b) T := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_of_not_finiteInitialKineticEnergy
      (u₀ := linearShearHorizontalDriftInitialVelocity a b)
      (not_finiteInitialKineticEnergy_linearShearHorizontalDriftInitialVelocity
        (a := a) (b := b) ha)

/-- The repaired BKM continuation clause can therefore also be true on nonzero
affine shear data `x ↦ (a * x₁, b, 0)` while the concrete regularity clause is
false there. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_linearShearHorizontalDriftInitialVelocity_without_regularity
    {ν T : ℝ} {a b : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) :
    ExplicitFiniteEnergyBKMContinuationClause ν
        (linearShearHorizontalDriftInitialVelocity a b) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (linearShearHorizontalDriftInitialVelocity a b) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitFiniteEnergyBKMContinuationClause_linearShearHorizontalDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (b := b) ha
  · exact
      not_ExplicitConcreteNavierStokesRegularityClause_linearShearHorizontalDriftInitialVelocity
        hν ha

/-- The same BKM-side vacuity caveat holds for nonzero affine shear initial
data `x ↦ (a * x₁, b, c)`: on nonnegative slabs the clause is true because the
finite-time witness type is already empty there. -/
theorem ExplicitBKMContinuationClause_linearShearFullDriftInitialVelocity
    {ν T : ℝ} {a b c : ℝ}
    (ha : a ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν (linearShearFullDriftInitialVelocity a b c) T := by
  exact
    ExplicitBKMContinuationClause_of_not_nonempty_finiteTimeWitness
      (u₀ := linearShearFullDriftInitialVelocity a b c)
      (not_nonempty_ExplicitFiniteTimeRegularityWitness_linearShearFullDriftInitialVelocity
        (ν := ν) (T := T) (a := a) (b := b) (c := c) ha hT)

/-- The BKM continuation clause can therefore also be true on nonzero affine
shear data `x ↦ (a * x₁, b, c)` while the concrete regularity clause is false
there. -/
theorem ExplicitBKMContinuationClause_linearShearFullDriftInitialVelocity_without_regularity
    {ν T : ℝ} {a b c : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν (linearShearFullDriftInitialVelocity a b c) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (linearShearFullDriftInitialVelocity a b c) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitBKMContinuationClause_linearShearFullDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (b := b) (c := c) ha hT
  · exact
      not_ExplicitConcreteNavierStokesRegularityClause_linearShearFullDriftInitialVelocity
        hν ha

/-- The repaired BKM continuation clause is also vacuous on nonzero affine
shear data `x ↦ (a * x₁, b, c)` because the repaired finite-energy input
hypothesis already fails. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_linearShearFullDriftInitialVelocity
    {ν T : ℝ} {a b c : ℝ}
    (ha : a ≠ 0) :
    ExplicitFiniteEnergyBKMContinuationClause ν
      (linearShearFullDriftInitialVelocity a b c) T := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_of_not_finiteInitialKineticEnergy
      (u₀ := linearShearFullDriftInitialVelocity a b c)
      (not_finiteInitialKineticEnergy_linearShearFullDriftInitialVelocity
        (a := a) (b := b) (c := c) ha)

/-- The repaired BKM continuation clause can therefore also be true on nonzero
affine shear data `x ↦ (a * x₁, b, c)` while the concrete regularity clause is
false there. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_linearShearFullDriftInitialVelocity_without_regularity
    {ν T : ℝ} {a b c : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) :
    ExplicitFiniteEnergyBKMContinuationClause ν
        (linearShearFullDriftInitialVelocity a b c) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (linearShearFullDriftInitialVelocity a b c) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitFiniteEnergyBKMContinuationClause_linearShearFullDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (b := b) (c := c) ha
  · exact
      not_ExplicitConcreteNavierStokesRegularityClause_linearShearFullDriftInitialVelocity
        hν ha

/-- The same BKM-side vacuity caveat holds for nontrivial heat-shear initial
data: on nonnegative slabs the clause is true because the finite-time witness
type is already empty there. -/
theorem ExplicitBKMContinuationClause_heatShearInitialVelocity
    {ν T : ℝ} {a k : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν (heatShearInitialVelocity a k) T := by
  exact
    ExplicitBKMContinuationClause_of_not_nonempty_finiteTimeWitness
      (u₀ := heatShearInitialVelocity a k)
      (not_nonempty_ExplicitFiniteTimeRegularityWitness_heatShearInitialVelocity
        (ν := ν) (T := T) (a := a) (k := k) ha hk hT)

/-- The BKM continuation clause can therefore also be true on nontrivial
heat-shear data while the concrete regularity clause is false there. -/
theorem ExplicitBKMContinuationClause_heatShearInitialVelocity_without_regularity
    {ν T : ℝ} {a k : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) (hk : k ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν (heatShearInitialVelocity a k) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν (heatShearInitialVelocity a k) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitBKMContinuationClause_heatShearInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) ha hk hT
  · exact not_ExplicitConcreteNavierStokesRegularityClause_heatShearInitialVelocity hν ha hk

/-- The repaired BKM continuation clause is also vacuous on nontrivial
heat-shear data because the repaired finite-energy hypothesis already fails. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_heatShearInitialVelocity
    {ν T : ℝ} {a k : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0) :
    ExplicitFiniteEnergyBKMContinuationClause ν (heatShearInitialVelocity a k) T := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearInitialVelocity a k)
      (not_finiteInitialKineticEnergy_heatShearInitialVelocity ha hk)

/-- The repaired BKM continuation clause can therefore also be true on
nontrivial heat-shear data while the concrete regularity clause is false
there. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_heatShearInitialVelocity_without_regularity
    {ν T : ℝ} {a k : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) (hk : k ≠ 0) :
    ExplicitFiniteEnergyBKMContinuationClause ν (heatShearInitialVelocity a k) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν (heatShearInitialVelocity a k) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitFiniteEnergyBKMContinuationClause_heatShearInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) ha hk
  · exact not_ExplicitConcreteNavierStokesRegularityClause_heatShearInitialVelocity hν ha hk

/-- The damped sinusoidal heat-shear field with constant streamwise drift is
likewise an exact smooth incompressible NS candidate on every nonnegative slab
with the explicit constant BKM envelope `Ω(t) = |a * k|`; bounded kinetic
energy is still the only missing witness slot. -/
theorem heatShearStreamwiseDriftVelocityField_exhibits_BKMCandidate_except_boundedEnergy
    {ν T a k d : ℝ}
    (hd : d ≠ 0)
    (hν : 0 ≤ ν) (hT : 0 ≤ T) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearStreamwiseDriftInitialVelocity a k d) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T := by
  rcases heatShearStreamwiseDriftInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness
      (ν := ν) (T := T) (a := a) (k := k) (d := d) hd hν hT with
    ⟨⟨u, p, B, hu, hp, hmom, hdiv, hinit, hω, hE⟩, _⟩
  have hBKM :
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
        integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) :=
    uniformVorticityBoundUpTo_implies_constantBKMEnvelope
      (u := u) (T := T) (B := B) hT hω
  exact ⟨u, p, B, hu, hp, hmom, hdiv, hinit, hBKM.1, hBKM.2, hE⟩

/-- Heat shear with constant streamwise drift exposes the same exact BKM-side
gap: there is an explicit smooth incompressible candidate with an integrable
constant vorticity envelope, but the finite-time witness type is still empty
because bounded kinetic energy fails on `ℝ^3`. -/
theorem heatShearStreamwiseDriftInitialVelocity_exhibits_BKMCandidate_without_finiteTimeWitness
    {ν T a k d : ℝ}
    (hd : d ≠ 0)
    (hν : 0 ≤ ν) (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearStreamwiseDriftInitialVelocity a k d) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness ν (heatShearStreamwiseDriftInitialVelocity a k d) T) := by
  refine ⟨?_, ?_⟩
  · exact heatShearStreamwiseDriftVelocityField_exhibits_BKMCandidate_except_boundedEnergy
      (ν := ν) (T := T) (a := a) (k := k) (d := d) hd hν hT
  · exact not_nonempty_ExplicitFiniteTimeRegularityWitness_heatShearStreamwiseDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) (d := d) hd hT

/-- The same BKM-side vacuity caveat holds for heat-shear initial data with
nonzero constant streamwise drift: on nonnegative slabs the clause is true
because the finite-time witness type is already empty there. -/
theorem ExplicitBKMContinuationClause_heatShearStreamwiseDriftInitialVelocity
    {ν T : ℝ} {a k d : ℝ}
    (hd : d ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν (heatShearStreamwiseDriftInitialVelocity a k d) T := by
  exact
    ExplicitBKMContinuationClause_of_not_nonempty_finiteTimeWitness
      (u₀ := heatShearStreamwiseDriftInitialVelocity a k d)
      (not_nonempty_ExplicitFiniteTimeRegularityWitness_heatShearStreamwiseDriftInitialVelocity
        (ν := ν) (T := T) (a := a) (k := k) (d := d) hd hT)

/-- The BKM continuation clause can therefore also be true on heat-shear data
with nonzero constant streamwise drift while the concrete regularity clause is
false there. -/
theorem ExplicitBKMContinuationClause_heatShearStreamwiseDriftInitialVelocity_without_regularity
    {ν T : ℝ} {a k d : ℝ}
    (hν : 0 < ν)
    (hd : d ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν (heatShearStreamwiseDriftInitialVelocity a k d) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (heatShearStreamwiseDriftInitialVelocity a k d) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitBKMContinuationClause_heatShearStreamwiseDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) (d := d) hd hT
  · exact not_ExplicitConcreteNavierStokesRegularityClause_heatShearStreamwiseDriftInitialVelocity
      hν hd

/-- The repaired BKM continuation clause is also vacuous on heat-shear data
with nonzero constant streamwise drift because the repaired finite-energy
hypothesis already fails. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_heatShearStreamwiseDriftInitialVelocity
    {ν T : ℝ} {a k d : ℝ}
    (hd : d ≠ 0) :
    ExplicitFiniteEnergyBKMContinuationClause
      ν (heatShearStreamwiseDriftInitialVelocity a k d) T := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearStreamwiseDriftInitialVelocity a k d)
      (not_finiteInitialKineticEnergy_heatShearStreamwiseDriftInitialVelocity hd)

/-- The repaired BKM continuation clause can therefore also be true on
heat-shear data with nonzero constant streamwise drift while the concrete
regularity clause is false there. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_heatShearStreamwiseDriftInitialVelocity_without_regularity
    {ν T : ℝ} {a k d : ℝ}
    (hν : 0 < ν)
    (hd : d ≠ 0) :
    ExplicitFiniteEnergyBKMContinuationClause
        ν (heatShearStreamwiseDriftInitialVelocity a k d) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (heatShearStreamwiseDriftInitialVelocity a k d) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitFiniteEnergyBKMContinuationClause_heatShearStreamwiseDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) (d := d) hd
  · exact not_ExplicitConcreteNavierStokesRegularityClause_heatShearStreamwiseDriftInitialVelocity
      hν hd

/-- The damped sinusoidal heat-shear field with constant vertical drift is
likewise an exact smooth incompressible NS candidate on every nonnegative slab
with the explicit constant BKM envelope `Ω(t) = |a * k|`; bounded kinetic
energy is still the only missing witness slot. -/
theorem heatShearVerticalDriftVelocityField_exhibits_BKMCandidate_except_boundedEnergy
    {ν T a k c : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0)
    (hν : 0 ≤ ν) (hT : 0 ≤ T) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearVerticalDriftInitialVelocity a k c) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T := by
  rcases heatShearVerticalDriftInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness
      (ν := ν) (T := T) (a := a) (k := k) (c := c) ha hk hν hT with
    ⟨⟨u, p, B, hu, hp, hmom, hdiv, hinit, hω, hE⟩, _⟩
  have hBKM :
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
        integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) :=
    uniformVorticityBoundUpTo_implies_constantBKMEnvelope
      (u := u) (T := T) (B := B) hT hω
  exact ⟨u, p, B, hu, hp, hmom, hdiv, hinit, hBKM.1, hBKM.2, hE⟩

/-- Heat shear with constant vertical drift exposes the same exact BKM-side
gap: there is an explicit smooth incompressible candidate with an integrable
constant vorticity envelope, but the finite-time witness type is still empty
because bounded kinetic energy fails on `ℝ^3`. -/
theorem heatShearVerticalDriftInitialVelocity_exhibits_BKMCandidate_without_finiteTimeWitness
    {ν T a k c : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0)
    (hν : 0 ≤ ν) (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearVerticalDriftInitialVelocity a k c) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness ν (heatShearVerticalDriftInitialVelocity a k c) T) := by
  refine ⟨?_, ?_⟩
  · exact heatShearVerticalDriftVelocityField_exhibits_BKMCandidate_except_boundedEnergy
      (ν := ν) (T := T) (a := a) (k := k) (c := c) ha hk hν hT
  · exact not_nonempty_ExplicitFiniteTimeRegularityWitness_heatShearVerticalDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) (c := c) ha hk hT

/-- The same BKM-side vacuity caveat holds for nontrivial heat-shear initial
data with vertical drift: on nonnegative slabs the clause is true because the
finite-time witness type is already empty there. -/
theorem ExplicitBKMContinuationClause_heatShearVerticalDriftInitialVelocity
    {ν T : ℝ} {a k c : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν (heatShearVerticalDriftInitialVelocity a k c) T := by
  exact
    ExplicitBKMContinuationClause_of_not_nonempty_finiteTimeWitness
      (u₀ := heatShearVerticalDriftInitialVelocity a k c)
      (not_nonempty_ExplicitFiniteTimeRegularityWitness_heatShearVerticalDriftInitialVelocity
        (ν := ν) (T := T) (a := a) (k := k) (c := c) ha hk hT)

/-- The BKM continuation clause can therefore also be true on nontrivial
heat-shear data with vertical drift while the concrete regularity clause is
false there. -/
theorem ExplicitBKMContinuationClause_heatShearVerticalDriftInitialVelocity_without_regularity
    {ν T : ℝ} {a k c : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) (hk : k ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν (heatShearVerticalDriftInitialVelocity a k c) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (heatShearVerticalDriftInitialVelocity a k c) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitBKMContinuationClause_heatShearVerticalDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) (c := c) ha hk hT
  · exact not_ExplicitConcreteNavierStokesRegularityClause_heatShearVerticalDriftInitialVelocity
      hν ha hk

/-- The repaired BKM continuation clause is also vacuous on nontrivial
heat-shear data with vertical drift because the repaired finite-energy
hypothesis already fails. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_heatShearVerticalDriftInitialVelocity
    {ν T : ℝ} {a k c : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0) :
    ExplicitFiniteEnergyBKMContinuationClause
      ν (heatShearVerticalDriftInitialVelocity a k c) T := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearVerticalDriftInitialVelocity a k c)
      (not_finiteInitialKineticEnergy_heatShearVerticalDriftInitialVelocity ha hk)

/-- The repaired BKM continuation clause can therefore also be true on
nontrivial heat-shear data with vertical drift while the concrete regularity
clause is false there. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_heatShearVerticalDriftInitialVelocity_without_regularity
    {ν T : ℝ} {a k c : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) (hk : k ≠ 0) :
    ExplicitFiniteEnergyBKMContinuationClause
        ν (heatShearVerticalDriftInitialVelocity a k c) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (heatShearVerticalDriftInitialVelocity a k c) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitFiniteEnergyBKMContinuationClause_heatShearVerticalDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) (c := c) ha hk
  · exact not_ExplicitConcreteNavierStokesRegularityClause_heatShearVerticalDriftInitialVelocity
      hν ha hk

/-- The damped sinusoidal heat-shear field with full constant drift is likewise
an exact smooth incompressible NS candidate on every nonnegative slab with the
explicit constant BKM envelope `Ω(t) = |a * k|`; bounded kinetic energy is
still the only missing witness slot. -/
theorem heatShearFullDriftVelocityField_exhibits_BKMCandidate_except_boundedEnergy
    {ν T a k d c : ℝ}
    (hd : d ≠ 0)
    (hν : 0 ≤ ν) (hT : 0 ≤ T) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearFullDriftInitialVelocity a k d c) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T := by
  rcases heatShearFullDriftInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness
      (ν := ν) (T := T) (a := a) (k := k) (d := d) (c := c) hd hν hT with
    ⟨⟨u, p, B, hu, hp, hmom, hdiv, hinit, hω, hE⟩, _⟩
  have hBKM :
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
        integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) :=
    uniformVorticityBoundUpTo_implies_constantBKMEnvelope
      (u := u) (T := T) (B := B) hT hω
  exact ⟨u, p, B, hu, hp, hmom, hdiv, hinit, hBKM.1, hBKM.2, hE⟩

/-- Heat shear with full constant drift exposes the same exact BKM-side gap:
there is an explicit smooth incompressible candidate with an integrable
constant vorticity envelope, but the finite-time witness type is still empty
because bounded kinetic energy fails on `ℝ^3`. -/
theorem heatShearFullDriftInitialVelocity_exhibits_BKMCandidate_without_finiteTimeWitness
    {ν T a k d c : ℝ}
    (hd : d ≠ 0)
    (hν : 0 ≤ ν) (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearFullDriftInitialVelocity a k d c) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness ν (heatShearFullDriftInitialVelocity a k d c) T) := by
  refine ⟨?_, ?_⟩
  · exact heatShearFullDriftVelocityField_exhibits_BKMCandidate_except_boundedEnergy
      (ν := ν) (T := T) (a := a) (k := k) (d := d) (c := c) hd hν hT
  · exact not_nonempty_ExplicitFiniteTimeRegularityWitness_heatShearFullDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) (d := d) (c := c) hd hT

/-- The same BKM-side vacuity caveat holds for full-drift heat-shear initial
data with nonzero streamwise drift: on nonnegative slabs the clause is true
because the finite-time witness type is already empty there. -/
theorem ExplicitBKMContinuationClause_heatShearFullDriftInitialVelocity
    {ν T : ℝ} {a k d c : ℝ}
    (hd : d ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν (heatShearFullDriftInitialVelocity a k d c) T := by
  exact
    ExplicitBKMContinuationClause_of_not_nonempty_finiteTimeWitness
      (u₀ := heatShearFullDriftInitialVelocity a k d c)
      (not_nonempty_ExplicitFiniteTimeRegularityWitness_heatShearFullDriftInitialVelocity
        (ν := ν) (T := T) (a := a) (k := k) (d := d) (c := c) hd hT)

/-- The BKM continuation clause can therefore also be true on full-drift
heat-shear data with nonzero streamwise drift while the concrete regularity
clause is false there. -/
theorem ExplicitBKMContinuationClause_heatShearFullDriftInitialVelocity_without_regularity
    {ν T : ℝ} {a k d c : ℝ}
    (hν : 0 < ν)
    (hd : d ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν (heatShearFullDriftInitialVelocity a k d c) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (heatShearFullDriftInitialVelocity a k d c) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitBKMContinuationClause_heatShearFullDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) (d := d) (c := c) hd hT
  · exact not_ExplicitConcreteNavierStokesRegularityClause_heatShearFullDriftInitialVelocity
      hν hd

/-- The repaired BKM continuation clause is also vacuous on full-drift
heat-shear data with nonzero streamwise drift because the repaired finite-energy
hypothesis already fails. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_heatShearFullDriftInitialVelocity
    {ν T : ℝ} {a k d c : ℝ}
    (hd : d ≠ 0) :
    ExplicitFiniteEnergyBKMContinuationClause
      ν (heatShearFullDriftInitialVelocity a k d c) T := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearFullDriftInitialVelocity a k d c)
      (not_finiteInitialKineticEnergy_heatShearFullDriftInitialVelocity hd)

/-- The repaired BKM continuation clause can therefore also be true on
full-drift heat-shear data with nonzero streamwise drift while the concrete
regularity clause is false there. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_heatShearFullDriftInitialVelocity_without_regularity
    {ν T : ℝ} {a k d c : ℝ}
    (hν : 0 < ν)
    (hd : d ≠ 0) :
    ExplicitFiniteEnergyBKMContinuationClause
        ν (heatShearFullDriftInitialVelocity a k d c) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (heatShearFullDriftInitialVelocity a k d c) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitFiniteEnergyBKMContinuationClause_heatShearFullDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) (d := d) (c := c) hd
  · exact not_ExplicitConcreteNavierStokesRegularityClause_heatShearFullDriftInitialVelocity
      hν hd

/-- The transported heat-shear field is likewise an exact smooth incompressible
NS candidate on every nonnegative slab with the explicit constant BKM envelope
`Ω(t) = |a * k|`; bounded kinetic energy is still the only missing witness
slot. -/
theorem heatShearTransportVelocityField_exhibits_BKMCandidate_except_boundedEnergy
    {ν T a k b : ℝ}
    (hb : b ≠ 0)
    (hν : 0 ≤ ν) (hT : 0 ≤ T) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearTransportInitialVelocity a k b) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T := by
  rcases heatShearTransportInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness
      (ν := ν) (T := T) (a := a) (k := k) (b := b) hb hν hT with
    ⟨⟨u, p, B, hu, hp, hmom, hdiv, hinit, hω, hE⟩, _⟩
  have hBKM :
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
        integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) :=
    uniformVorticityBoundUpTo_implies_constantBKMEnvelope
      (u := u) (T := T) (B := B) hT hω
  exact ⟨u, p, B, hu, hp, hmom, hdiv, hinit, hBKM.1, hBKM.2, hE⟩

/-- Transported heat shear exposes the same exact BKM-side gap: there is an
explicit smooth incompressible candidate with an integrable constant vorticity
envelope, but the finite-time witness type is still empty because bounded
kinetic energy fails on `ℝ^3`. -/
theorem heatShearTransportInitialVelocity_exhibits_BKMCandidate_without_finiteTimeWitness
    {ν T a k b : ℝ}
    (hb : b ≠ 0)
    (hν : 0 ≤ ν) (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearTransportInitialVelocity a k b) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness ν (heatShearTransportInitialVelocity a k b) T) := by
  refine ⟨?_, ?_⟩
  · exact heatShearTransportVelocityField_exhibits_BKMCandidate_except_boundedEnergy
      (ν := ν) (T := T) (a := a) (k := k) (b := b) hb hν hT
  · exact not_nonempty_ExplicitFiniteTimeRegularityWitness_heatShearTransportInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) (b := b) hb hT

/-- The same BKM-side vacuity caveat holds for transported heat-shear initial
data with nonzero transport speed: on nonnegative slabs the clause is true
because the finite-time witness type is already empty there. -/
theorem ExplicitBKMContinuationClause_heatShearTransportInitialVelocity
    {ν T : ℝ} {a k b : ℝ}
    (hb : b ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν (heatShearTransportInitialVelocity a k b) T := by
  exact
    ExplicitBKMContinuationClause_of_not_nonempty_finiteTimeWitness
      (u₀ := heatShearTransportInitialVelocity a k b)
      (not_nonempty_ExplicitFiniteTimeRegularityWitness_heatShearTransportInitialVelocity
        (ν := ν) (T := T) (a := a) (k := k) (b := b) hb hT)

/-- The BKM continuation clause can therefore also be true on transported
heat-shear data with nonzero transport speed while the concrete regularity
clause is false there. -/
theorem ExplicitBKMContinuationClause_heatShearTransportInitialVelocity_without_regularity
    {ν T : ℝ} {a k b : ℝ}
    (hν : 0 < ν)
    (hb : b ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν (heatShearTransportInitialVelocity a k b) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (heatShearTransportInitialVelocity a k b) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitBKMContinuationClause_heatShearTransportInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) (b := b) hb hT
  · exact not_ExplicitConcreteNavierStokesRegularityClause_heatShearTransportInitialVelocity
      hν hb

/-- The repaired BKM continuation clause is also vacuous on transported
heat-shear data with nonzero transport speed because the repaired finite-energy
hypothesis already fails. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_heatShearTransportInitialVelocity
    {ν T : ℝ} {a k b : ℝ}
    (hb : b ≠ 0) :
    ExplicitFiniteEnergyBKMContinuationClause
      ν (heatShearTransportInitialVelocity a k b) T := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearTransportInitialVelocity a k b)
      (not_finiteInitialKineticEnergy_heatShearTransportInitialVelocity hb)

/-- The repaired BKM continuation clause can therefore also be true on
transported heat-shear data with nonzero transport speed while the concrete
regularity clause is false there. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_heatShearTransportInitialVelocity_without_regularity
    {ν T : ℝ} {a k b : ℝ}
    (hν : 0 < ν)
    (hb : b ≠ 0) :
    ExplicitFiniteEnergyBKMContinuationClause
        ν (heatShearTransportInitialVelocity a k b) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (heatShearTransportInitialVelocity a k b) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitFiniteEnergyBKMContinuationClause_heatShearTransportInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) (b := b) hb
  · exact not_ExplicitConcreteNavierStokesRegularityClause_heatShearTransportInitialVelocity
      hν hb

/-- The transported full-drift heat-shear field is likewise an exact smooth
incompressible NS candidate on every nonnegative slab with the explicit
constant BKM envelope `Ω(t) = |a * k|`; bounded kinetic energy is still the
only missing witness slot. -/
theorem heatShearTransportFullDriftVelocityField_exhibits_BKMCandidate_except_boundedEnergy
    {ν T a k b d c : ℝ}
    (hb : b ≠ 0)
    (hν : 0 ≤ ν) (hT : 0 ≤ T) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearTransportFullDriftInitialVelocity a k b d c) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T := by
  rcases heatShearTransportFullDriftInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness
      (ν := ν) (T := T) (a := a) (k := k) (b := b) (d := d) (c := c) hb hν hT with
    ⟨⟨u, p, B, hu, hp, hmom, hdiv, hinit, hω, hE⟩, _⟩
  have hBKM :
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
        integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) :=
    uniformVorticityBoundUpTo_implies_constantBKMEnvelope
      (u := u) (T := T) (B := B) hT hω
  exact ⟨u, p, B, hu, hp, hmom, hdiv, hinit, hBKM.1, hBKM.2, hE⟩

/-- Transported full-drift heat shear exposes the same exact BKM-side gap:
there is an explicit smooth incompressible candidate with an integrable
constant vorticity envelope, but the finite-time witness type is still empty
because bounded kinetic energy fails on `ℝ^3`. -/
theorem heatShearTransportFullDriftInitialVelocity_exhibits_BKMCandidate_without_finiteTimeWitness
    {ν T a k b d c : ℝ}
    (hb : b ≠ 0)
    (hν : 0 ≤ ν) (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearTransportFullDriftInitialVelocity a k b d c) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness ν (heatShearTransportFullDriftInitialVelocity a k b d c) T) := by
  refine ⟨?_, ?_⟩
  · exact heatShearTransportFullDriftVelocityField_exhibits_BKMCandidate_except_boundedEnergy
      (ν := ν) (T := T) (a := a) (k := k) (b := b) (d := d) (c := c) hb hν hT
  · exact not_nonempty_ExplicitFiniteTimeRegularityWitness_heatShearTransportFullDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) (b := b) (d := d) (c := c) hb hT

/-- The same BKM-side vacuity caveat holds for transported full-drift
heat-shear initial data with nonzero transport speed: on nonnegative slabs the
clause is true because the finite-time witness type is already empty there. -/
theorem ExplicitBKMContinuationClause_heatShearTransportFullDriftInitialVelocity
    {ν T : ℝ} {a k b d c : ℝ}
    (hb : b ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν (heatShearTransportFullDriftInitialVelocity a k b d c) T := by
  exact
    ExplicitBKMContinuationClause_of_not_nonempty_finiteTimeWitness
      (u₀ := heatShearTransportFullDriftInitialVelocity a k b d c)
      (not_nonempty_ExplicitFiniteTimeRegularityWitness_heatShearTransportFullDriftInitialVelocity
        (ν := ν) (T := T) (a := a) (k := k) (b := b) (d := d) (c := c) hb hT)

/-- The BKM continuation clause can therefore also be true on transported
full-drift heat-shear data with nonzero transport speed while the concrete
regularity clause is false there. -/
theorem ExplicitBKMContinuationClause_heatShearTransportFullDriftInitialVelocity_without_regularity
    {ν T : ℝ} {a k b d c : ℝ}
    (hν : 0 < ν)
    (hb : b ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν (heatShearTransportFullDriftInitialVelocity a k b d c) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (heatShearTransportFullDriftInitialVelocity a k b d c) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitBKMContinuationClause_heatShearTransportFullDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) (b := b) (d := d) (c := c) hb hT
  · exact not_ExplicitConcreteNavierStokesRegularityClause_heatShearTransportFullDriftInitialVelocity
      hν hb

/-- The repaired BKM continuation clause is also vacuous on transported
full-drift heat-shear data with nonzero transport speed because the repaired
finite-energy hypothesis already fails. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_heatShearTransportFullDriftInitialVelocity
    {ν T : ℝ} {a k b d c : ℝ}
    (hb : b ≠ 0) :
    ExplicitFiniteEnergyBKMContinuationClause
      ν (heatShearTransportFullDriftInitialVelocity a k b d c) T := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearTransportFullDriftInitialVelocity a k b d c)
      (not_finiteInitialKineticEnergy_heatShearTransportFullDriftInitialVelocity hb)

/-- The repaired BKM continuation clause can therefore also be true on
transported full-drift heat-shear data with nonzero transport speed while the
concrete regularity clause is false there. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_heatShearTransportFullDriftInitialVelocity_without_regularity
    {ν T : ℝ} {a k b d c : ℝ}
    (hν : 0 < ν)
    (hb : b ≠ 0) :
    ExplicitFiniteEnergyBKMContinuationClause
        ν (heatShearTransportFullDriftInitialVelocity a k b d c) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (heatShearTransportFullDriftInitialVelocity a k b d c) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitFiniteEnergyBKMContinuationClause_heatShearTransportFullDriftInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) (b := b) (d := d) (c := c) hb
  · exact not_ExplicitConcreteNavierStokesRegularityClause_heatShearTransportFullDriftInitialVelocity
      hν hb

end BKMContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
