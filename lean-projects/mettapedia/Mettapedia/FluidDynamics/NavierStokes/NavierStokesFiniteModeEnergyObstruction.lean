import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeReconstruction
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityContinuationTarget

/-!
# Finite-Mode Energy Obstructions

This file connects the time-dependent finite-mode matrix construction to the
finite-time whole-space energy predicates.  The finite-mode reconstruction file
proves smooth global pointwise PDE identities for polynomial linear modes; here
we record the finite-energy boundary: an active nonzero matrix-linear mode is
not a finite-energy Navier--Stokes witness on `ℝ^3`.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open scoped ContDiff

/-- If a nonzero matrix-linear finite-mode velocity is active at some time in
the slab `0 ≤ t ≤ T`, it cannot satisfy the finite-time bounded-energy
predicate on that slab. -/
theorem not_boundedKineticEnergyUpTo_finiteModeLinearMatrixTimeVelocity
    {A : Fin 3 → Fin 3 → ℝ} {g : NSTime → ℝ} {T : ℝ}
    (hA : ∃ i j : Fin 3, A i j ≠ 0)
    (hactive : ∃ t : NSTime, 0 ≤ t ∧ t ≤ T ∧ g t ≠ 0) :
    ¬ boundedKineticEnergyUpTo (finiteModeLinearMatrixTimeVelocity A g) T := by
  intro hE
  rcases hE with ⟨C, hC, hbound⟩
  rcases hactive with ⟨t, ht0, htT, hgt⟩
  exact not_integrable_kineticEnergyDensity_finiteModeLinearMatrixTimeVelocity
    hA hgt ((hbound t ht0 htT).1)

/-- If the matrix-linear finite-mode initial slice is active at time zero, then
that initial datum is outside the finite-time witness domain on every
nonnegative slab. -/
theorem not_nonempty_ExplicitFiniteTimeRegularityWitness_finiteModeLinearMatrixTimeVelocity_initial
    {ν T : ℝ} {A : Fin 3 → Fin 3 → ℝ} {g : NSTime → ℝ}
    (hA : ∃ i j : Fin 3, A i j ≠ 0)
    (hg0 : g 0 ≠ 0)
    (hT : 0 ≤ T) :
    ¬ Nonempty
      (ExplicitFiniteTimeRegularityWitness ν
        (fun x : NSSpace => finiteModeLinearMatrixTimeVelocity A g 0 x) T) := by
  exact
    not_nonempty_ExplicitFiniteTimeRegularityWitness_of_not_finiteInitialKineticEnergy
      (u₀ := fun x : NSSpace => finiteModeLinearMatrixTimeVelocity A g 0 x)
      (not_finiteInitialKineticEnergy_finiteModeLinearMatrixTimeVelocity_initial
        hA hg0)
      hT

/-- The time-zero matrix-linear finite-mode slice has finite initial kinetic
energy exactly in the degenerate cases: either the matrix mode is zero, or the
scalar amplitude is inactive at time zero.  Thus no active linear-growth
matrix mode can be repaired into the finite-energy witness domain without
localizing the spatial profile. -/
theorem finiteInitialKineticEnergy_finiteModeLinearMatrixTimeVelocity_initial_iff
    (A : Fin 3 → Fin 3 → ℝ) (g : NSTime → ℝ) :
    finiteInitialKineticEnergy
        (fun x : NSSpace => finiteModeLinearMatrixTimeVelocity A g 0 x) ↔
      (∀ i j : Fin 3, A i j = 0) ∨ g 0 = 0 := by
  constructor
  · intro hE
    by_cases hAzero : ∀ i j : Fin 3, A i j = 0
    · exact Or.inl hAzero
    · by_cases hg0 : g 0 = 0
      · exact Or.inr hg0
      · have hAnz : ∃ i j : Fin 3, A i j ≠ 0 := by
          by_contra hnone
          apply hAzero
          intro i j
          by_contra hij
          exact hnone ⟨i, j, hij⟩
        exact
          False.elim
            ((not_finiteInitialKineticEnergy_finiteModeLinearMatrixTimeVelocity_initial
              hAnz hg0) hE)
  · intro hdegenerate
    rcases hdegenerate with hAzero | hg0
    · have hfield :
          (fun x : NSSpace => finiteModeLinearMatrixTimeVelocity A g 0 x) =
            (0 : NSInitialVelocity) := by
        funext x
        ext j
        rw [finiteModeLinearMatrixTimeVelocity_apply]
        simp [hAzero]
      simpa [hfield] using finiteInitialKineticEnergy_zero
    · have hfield :
          (fun x : NSSpace => finiteModeLinearMatrixTimeVelocity A g 0 x) =
            (0 : NSInitialVelocity) := by
        funext x
        ext j
        rw [finiteModeLinearMatrixTimeVelocity_apply]
        simp [hg0]
      simpa [hfield] using finiteInitialKineticEnergy_zero

/-- On nonnegative slabs, finite-time witness nonemptiness for a matrix-linear
initial slice is exact: the witness type is inhabited precisely when the
initial slice is the zero datum, i.e. either the matrix mode is zero or the
time-zero scalar amplitude vanishes. -/
theorem nonempty_ExplicitFiniteTimeRegularityWitness_finiteModeLinearMatrixTimeVelocity_initial_iff
    {ν T : ℝ} (hT : 0 ≤ T) (A : Fin 3 → Fin 3 → ℝ) (g : NSTime → ℝ) :
    Nonempty
        (ExplicitFiniteTimeRegularityWitness ν
          (fun x : NSSpace => finiteModeLinearMatrixTimeVelocity A g 0 x) T) ↔
      (∀ i j : Fin 3, A i j = 0) ∨ g 0 = 0 := by
  constructor
  · intro hW
    rcases hW with ⟨W⟩
    exact
      (finiteInitialKineticEnergy_finiteModeLinearMatrixTimeVelocity_initial_iff
        A g).mp (W.finiteInitialKineticEnergy hT)
  · intro hdegenerate
    have hfield :
        (fun x : NSSpace => finiteModeLinearMatrixTimeVelocity A g 0 x) =
          (0 : NSInitialVelocity) := by
      funext x
      ext j
      rw [finiteModeLinearMatrixTimeVelocity_apply]
      rcases hdegenerate with hAzero | hg0
      · simp [hAzero]
      · simp [hg0]
    simpa [hfield] using
      (Nonempty.intro (zeroFiniteTimeRegularityWitness ν T))

/-- Exact finite-time energy boundary for the matrix-linear finite-mode
velocity: on a slab `0 ≤ t ≤ T`, bounded kinetic energy holds precisely in the
degenerate cases where the matrix mode is zero, or the scalar amplitude
vanishes throughout the slab.  Any active nonzero linear-growth profile is
therefore excluded by the energy predicate itself. -/
theorem boundedKineticEnergyUpTo_finiteModeLinearMatrixTimeVelocity_iff
    (A : Fin 3 → Fin 3 → ℝ) (g : NSTime → ℝ) (T : ℝ) :
    boundedKineticEnergyUpTo (finiteModeLinearMatrixTimeVelocity A g) T ↔
      (∀ i j : Fin 3, A i j = 0) ∨
        ∀ t : NSTime, 0 ≤ t → t ≤ T → g t = 0 := by
  constructor
  · intro hE
    by_cases hAzero : ∀ i j : Fin 3, A i j = 0
    · exact Or.inl hAzero
    · right
      by_contra hzeroOn
      have hAnz : ∃ i j : Fin 3, A i j ≠ 0 := by
        by_contra hnone
        apply hAzero
        intro i j
        by_contra hij
        exact hnone ⟨i, j, hij⟩
      have hactive : ∃ t : NSTime, 0 ≤ t ∧ t ≤ T ∧ g t ≠ 0 := by
        by_contra hno
        apply hzeroOn
        intro t ht0 htT
        by_contra hgt
        exact hno ⟨t, ht0, htT, hgt⟩
      exact (not_boundedKineticEnergyUpTo_finiteModeLinearMatrixTimeVelocity
        hAnz hactive) hE
  · intro hdegenerate
    refine ⟨0, le_rfl, ?_⟩
    intro t ht0 htT
    have hfield :
        kineticEnergyDensity (finiteModeLinearMatrixTimeVelocity A g) t =
          fun _ : NSSpace => 0 := by
      funext x
      have hvelocity :
          finiteModeLinearMatrixTimeVelocity A g t x = (0 : NSSpace) := by
        ext j
        rw [finiteModeLinearMatrixTimeVelocity_apply]
        rcases hdegenerate with hAzero | hzeroOn
        · simp [hAzero]
        · simp [hzeroOn t ht0 htT]
      simp [kineticEnergyDensity, hvelocity]
    constructor
    · simp [hfield]
    · simp [kineticEnergyAt, hfield]

/-- Exact finite-time energy status of the smooth matrix-linear finite-mode
PDE package.  On a slab `0 ≤ t ≤ T`, symmetric trace-free matrix-linear
candidates can be closed by an explicit smooth affine-quadratic pressure and
satisfy the pointwise momentum equation and incompressibility on the slab, but
the finite-time bounded-energy slot is equivalent to genuine degeneracy on
that slab: either the matrix mode is zero, or the scalar amplitude vanishes
throughout the slab. -/
theorem finiteModeLinearMatrix_timeDependent_smooth_momentum_incompressible_boundedEnergyUpTo_iff_exists
    (ν T : ℝ) (A : Fin 3 → Fin 3 → ℝ) (g gdot : NSTime → ℝ)
    (hA : ∀ i j, A i j = A j i)
    (htrace : ∑ i : Fin 3, A i i = 0)
    (hg : ContDiff ℝ ∞ g) (hgdot : ContDiff ℝ ∞ gdot)
    (hderiv : ∀ t : NSTime, HasDerivAt g (gdot t) t) :
    ∃ b : ℝ → FiniteModeState FiniteModeAffineQuadraticPressureIndex,
      ∃ u : NSVelocityField, ∃ p : NSPressureField,
      b = finiteModeLinearMatrixTimePressureCoefficients A g gdot ∧
        u = finiteModeLinearMatrixTimeVelocity A g ∧
          p = finiteModeReconstructedPressure finiteModeAffineQuadraticPressureMode b ∧
            smoothSpaceTimeVelocity u ∧
              smoothSpaceTimePressure p ∧
                (∀ t x, 0 ≤ t → t ≤ T →
                  timeVelocityDerivative u t x +
                      spatialConvection u t x +
                        spatialPressureGradient p t x =
                    ν • spatialLaplacian u t x) ∧
                (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
                  (boundedKineticEnergyUpTo u T ↔
                    (∀ i j : Fin 3, A i j = 0) ∨
                      ∀ t : NSTime, 0 ≤ t → t ≤ T → g t = 0) := by
  refine
    ⟨finiteModeLinearMatrixTimePressureCoefficients A g gdot,
      finiteModeLinearMatrixTimeVelocity A g,
      finiteModeLinearMatrixTimePressure A g gdot,
      rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact finiteModeLinearMatrix_timeDependent_smoothSpaceTimeVelocity A g hg
  · simpa [finiteModeLinearMatrixTimePressure] using
      finiteModeLinearMatrix_timeDependent_smoothSpaceTimePressure
        A g gdot hg hgdot
  · intro t x _ht0 _htT
    simpa [finiteModeLinearMatrixTimePressure] using
      finiteModeLinearMatrix_timeDependent_pointwise_momentum_eq
        ν A g gdot hA hderiv t x
  · intro t x _ht0 _htT
    exact finiteModeLinearMatrix_timeDependent_spatialDivergence_zero_of_trace
      A g htrace t x
  · exact boundedKineticEnergyUpTo_finiteModeLinearMatrixTimeVelocity_iff A g T

/-- Exact global energy boundary for the matrix-linear finite-mode velocity:
globally bounded kinetic energy holds precisely when the matrix mode is zero,
or the scalar amplitude vanishes at every time.  This is the whole-time
counterpart of the slab classification. -/
theorem boundedKineticEnergy_finiteModeLinearMatrixTimeVelocity_iff
    (A : Fin 3 → Fin 3 → ℝ) (g : NSTime → ℝ) :
    boundedKineticEnergy (finiteModeLinearMatrixTimeVelocity A g) ↔
      (∀ i j : Fin 3, A i j = 0) ∨ ∀ t : NSTime, g t = 0 := by
  constructor
  · intro hE
    by_cases hAzero : ∀ i j : Fin 3, A i j = 0
    · exact Or.inl hAzero
    · right
      by_contra hzero
      have hAnz : ∃ i j : Fin 3, A i j ≠ 0 := by
        by_contra hnone
        apply hAzero
        intro i j
        by_contra hij
        exact hnone ⟨i, j, hij⟩
      have hgactive : ∃ t : NSTime, g t ≠ 0 := by
        by_contra hno
        apply hzero
        intro t
        by_contra hgt
        exact hno ⟨t, hgt⟩
      exact (not_boundedKineticEnergy_finiteModeLinearMatrixTimeVelocity
        hAnz hgactive) hE
  · intro hdegenerate
    refine ⟨0, le_rfl, ?_⟩
    intro t
    have hfield :
        kineticEnergyDensity (finiteModeLinearMatrixTimeVelocity A g) t =
          fun _ : NSSpace => 0 := by
      funext x
      have hvelocity :
          finiteModeLinearMatrixTimeVelocity A g t x = (0 : NSSpace) := by
        ext j
        rw [finiteModeLinearMatrixTimeVelocity_apply]
        rcases hdegenerate with hAzero | hzero
        · simp [hAzero]
        · simp [hzero t]
      simp [kineticEnergyDensity, hvelocity]
    constructor
    · simp [hfield]
    · simp [kineticEnergyAt, hfield]

/-- Exact global finite-energy status of the smooth matrix-linear finite-mode
PDE package.  Symmetric trace-free matrix-linear candidates can be closed by an
explicit smooth affine-quadratic pressure and satisfy the pointwise momentum
equation and incompressibility everywhere, but their global bounded-energy slot
is equivalent to genuine degeneracy of the velocity: either the matrix mode is
zero, or the scalar amplitude is identically zero. -/
theorem finiteModeLinearMatrix_timeDependent_global_smooth_momentum_incompressible_boundedEnergy_iff_exists
    (ν : ℝ) (A : Fin 3 → Fin 3 → ℝ) (g gdot : NSTime → ℝ)
    (hA : ∀ i j, A i j = A j i)
    (htrace : ∑ i : Fin 3, A i i = 0)
    (hg : ContDiff ℝ ∞ g) (hgdot : ContDiff ℝ ∞ gdot)
    (hderiv : ∀ t : NSTime, HasDerivAt g (gdot t) t) :
    ∃ b : ℝ → FiniteModeState FiniteModeAffineQuadraticPressureIndex,
      ∃ u : NSVelocityField, ∃ p : NSPressureField,
      b = finiteModeLinearMatrixTimePressureCoefficients A g gdot ∧
        u = finiteModeLinearMatrixTimeVelocity A g ∧
          p = finiteModeReconstructedPressure finiteModeAffineQuadraticPressureMode b ∧
            smoothSpaceTimeVelocity u ∧
              smoothSpaceTimePressure p ∧
                (∀ t x,
                  timeVelocityDerivative u t x +
                      spatialConvection u t x +
                        spatialPressureGradient p t x =
                    ν • spatialLaplacian u t x) ∧
                (∀ t x, spatialDivergence u t x = 0) ∧
                  (boundedKineticEnergy u ↔
                    (∀ i j : Fin 3, A i j = 0) ∨ ∀ t : NSTime, g t = 0) := by
  refine
    ⟨finiteModeLinearMatrixTimePressureCoefficients A g gdot,
      finiteModeLinearMatrixTimeVelocity A g,
      finiteModeLinearMatrixTimePressure A g gdot,
      rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact finiteModeLinearMatrix_timeDependent_smoothSpaceTimeVelocity A g hg
  · simpa [finiteModeLinearMatrixTimePressure] using
      finiteModeLinearMatrix_timeDependent_smoothSpaceTimePressure
        A g gdot hg hgdot
  · simpa [finiteModeLinearMatrixTimePressure] using
      finiteModeLinearMatrix_timeDependent_pointwise_momentum_eq
        ν A g gdot hA hderiv
  · exact finiteModeLinearMatrix_timeDependent_spatialDivergence_zero_of_trace
      A g htrace
  · exact boundedKineticEnergy_finiteModeLinearMatrixTimeVelocity_iff A g

/-- Smooth matrix-linear finite-mode candidates give the exact finite-time
status on an active slab: smooth velocity, smooth pressure, pointwise momentum,
and incompressibility are available on the slab, while finite-time bounded
kinetic energy is impossible on `ℝ^3`. -/
theorem finiteModeLinearMatrix_timeDependent_smooth_momentum_incompressible_without_boundedEnergyUpTo_exists
    (ν T : ℝ) (A : Fin 3 → Fin 3 → ℝ) (g gdot : NSTime → ℝ)
    (hA : ∀ i j, A i j = A j i)
    (htrace : ∑ i : Fin 3, A i i = 0)
    (hAnz : ∃ i j : Fin 3, A i j ≠ 0)
    (hactive : ∃ t : NSTime, 0 ≤ t ∧ t ≤ T ∧ g t ≠ 0)
    (hg : ContDiff ℝ ∞ g) (hgdot : ContDiff ℝ ∞ gdot)
    (hderiv : ∀ t : NSTime, HasDerivAt g (gdot t) t) :
    ∃ b : ℝ → FiniteModeState FiniteModeAffineQuadraticPressureIndex,
      ∃ u : NSVelocityField, ∃ p : NSPressureField,
      b = finiteModeLinearMatrixTimePressureCoefficients A g gdot ∧
        u = finiteModeLinearMatrixTimeVelocity A g ∧
          p = finiteModeReconstructedPressure finiteModeAffineQuadraticPressureMode b ∧
            smoothSpaceTimeVelocity u ∧
              smoothSpaceTimePressure p ∧
                (∀ t x, 0 ≤ t → t ≤ T →
                  timeVelocityDerivative u t x +
                      spatialConvection u t x +
                        spatialPressureGradient p t x =
                    ν • spatialLaplacian u t x) ∧
                (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
                  ¬ boundedKineticEnergyUpTo u T := by
  refine
    ⟨finiteModeLinearMatrixTimePressureCoefficients A g gdot,
      finiteModeLinearMatrixTimeVelocity A g,
      finiteModeLinearMatrixTimePressure A g gdot,
      rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact finiteModeLinearMatrix_timeDependent_smoothSpaceTimeVelocity A g hg
  · simpa [finiteModeLinearMatrixTimePressure] using
      finiteModeLinearMatrix_timeDependent_smoothSpaceTimePressure
        A g gdot hg hgdot
  · intro t x _ht0 _htT
    simpa [finiteModeLinearMatrixTimePressure] using
      finiteModeLinearMatrix_timeDependent_pointwise_momentum_eq
        ν A g gdot hA hderiv t x
  · intro t x _ht0 _htT
    exact finiteModeLinearMatrix_timeDependent_spatialDivergence_zero_of_trace
      A g htrace t x
  · exact not_boundedKineticEnergyUpTo_finiteModeLinearMatrixTimeVelocity
      hAnz hactive

/-- When the same active finite-mode candidate is already active at time zero,
the corresponding finite-time witness type is empty for every nonnegative
horizon. -/
theorem finiteModeLinearMatrix_timeDependent_initial_without_finiteTimeWitness
    {ν T : ℝ} {A : Fin 3 → Fin 3 → ℝ} {g : NSTime → ℝ}
    (hA : ∃ i j : Fin 3, A i j ≠ 0)
    (hg0 : g 0 ≠ 0)
    (hT : 0 ≤ T) :
    ¬ Nonempty
      (ExplicitFiniteTimeRegularityWitness ν
        (fun x : NSSpace => finiteModeLinearMatrixTimeVelocity A g 0 x) T) :=
  not_nonempty_ExplicitFiniteTimeRegularityWitness_finiteModeLinearMatrixTimeVelocity_initial
    hA hg0 hT

end NavierStokes
end FluidDynamics
end Mettapedia
