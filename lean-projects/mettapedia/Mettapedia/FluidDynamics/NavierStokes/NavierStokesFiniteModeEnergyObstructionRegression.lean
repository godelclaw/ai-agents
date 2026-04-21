import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeEnergyObstruction

/-!
# Regression Checks for Finite-Mode Energy Obstructions
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open scoped ContDiff

section FiniteModeEnergyObstructionRegression

/-- Active matrix-linear finite-mode velocities fail finite-time bounded energy
on any slab containing an active time. -/
theorem not_boundedKineticEnergyUpTo_finiteModeLinearMatrixTimeVelocity_regression
    {A : Fin 3 → Fin 3 → ℝ} {g : NSTime → ℝ} {T : ℝ}
    (hA : ∃ i j : Fin 3, A i j ≠ 0)
    (hactive : ∃ t : NSTime, 0 ≤ t ∧ t ≤ T ∧ g t ≠ 0) :
    ¬ boundedKineticEnergyUpTo (finiteModeLinearMatrixTimeVelocity A g) T :=
  not_boundedKineticEnergyUpTo_finiteModeLinearMatrixTimeVelocity hA hactive

/-- Active time-zero matrix-linear data have no finite-time witness on
nonnegative slabs. -/
theorem not_nonempty_ExplicitFiniteTimeRegularityWitness_finiteModeLinearMatrixTimeVelocity_initial_regression
    {ν T : ℝ} {A : Fin 3 → Fin 3 → ℝ} {g : NSTime → ℝ}
    (hA : ∃ i j : Fin 3, A i j ≠ 0)
    (hg0 : g 0 ≠ 0)
    (hT : 0 ≤ T) :
    ¬ Nonempty
      (ExplicitFiniteTimeRegularityWitness ν
        (fun x : NSSpace => finiteModeLinearMatrixTimeVelocity A g 0 x) T) :=
  not_nonempty_ExplicitFiniteTimeRegularityWitness_finiteModeLinearMatrixTimeVelocity_initial
    hA hg0 hT

/-- The time-zero finite-energy boundary for matrix-linear finite modes is
exact: finite-energy membership forces the matrix mode to vanish or the
time-zero scalar amplitude to vanish. -/
theorem finiteInitialKineticEnergy_finiteModeLinearMatrixTimeVelocity_initial_iff_regression
    (A : Fin 3 → Fin 3 → ℝ) (g : NSTime → ℝ) :
    finiteInitialKineticEnergy
        (fun x : NSSpace => finiteModeLinearMatrixTimeVelocity A g 0 x) ↔
      (∀ i j : Fin 3, A i j = 0) ∨ g 0 = 0 :=
  finiteInitialKineticEnergy_finiteModeLinearMatrixTimeVelocity_initial_iff A g

/-- The slab bounded-energy boundary for matrix-linear finite modes is exact:
bounded-energy membership forces the matrix mode to vanish or the scalar
amplitude to vanish throughout the slab. -/
theorem boundedKineticEnergyUpTo_finiteModeLinearMatrixTimeVelocity_iff_regression
    (A : Fin 3 → Fin 3 → ℝ) (g : NSTime → ℝ) (T : ℝ) :
    boundedKineticEnergyUpTo (finiteModeLinearMatrixTimeVelocity A g) T ↔
      (∀ i j : Fin 3, A i j = 0) ∨
        ∀ t : NSTime, 0 ≤ t → t ≤ T → g t = 0 :=
  boundedKineticEnergyUpTo_finiteModeLinearMatrixTimeVelocity_iff A g T

/-- The global bounded-energy boundary for matrix-linear finite modes is
exact: globally bounded-energy membership forces the matrix mode to vanish or
the scalar amplitude to vanish at every time. -/
theorem boundedKineticEnergy_finiteModeLinearMatrixTimeVelocity_iff_regression
    (A : Fin 3 → Fin 3 → ℝ) (g : NSTime → ℝ) :
    boundedKineticEnergy (finiteModeLinearMatrixTimeVelocity A g) ↔
      (∀ i j : Fin 3, A i j = 0) ∨ ∀ t : NSTime, g t = 0 :=
  boundedKineticEnergy_finiteModeLinearMatrixTimeVelocity_iff A g

/-- The global smooth matrix-linear PDE package has an exact bounded-energy
boundary: bounded energy is equivalent to a zero matrix mode or an identically
zero scalar amplitude. -/
theorem finiteModeLinearMatrix_timeDependent_global_smooth_momentum_incompressible_boundedEnergy_iff_exists_regression
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
                    (∀ i j : Fin 3, A i j = 0) ∨ ∀ t : NSTime, g t = 0) :=
  finiteModeLinearMatrix_timeDependent_global_smooth_momentum_incompressible_boundedEnergy_iff_exists
    ν A g gdot hA htrace hg hgdot hderiv

/-- The smooth active matrix-linear finite-mode package exposes the exact slab
energy obstruction. -/
theorem finiteModeLinearMatrix_timeDependent_smooth_momentum_incompressible_without_boundedEnergyUpTo_exists_regression
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
                  ¬ boundedKineticEnergyUpTo u T :=
  finiteModeLinearMatrix_timeDependent_smooth_momentum_incompressible_without_boundedEnergyUpTo_exists
    ν T A g gdot hA htrace hAnz hactive hg hgdot hderiv

/-- Time-zero activity of a matrix-linear finite-mode candidate rules out the
finite-time witness type for that initial datum. -/
theorem finiteModeLinearMatrix_timeDependent_initial_without_finiteTimeWitness_regression
    {ν T : ℝ} {A : Fin 3 → Fin 3 → ℝ} {g : NSTime → ℝ}
    (hA : ∃ i j : Fin 3, A i j ≠ 0)
    (hg0 : g 0 ≠ 0)
    (hT : 0 ≤ T) :
    ¬ Nonempty
      (ExplicitFiniteTimeRegularityWitness ν
        (fun x : NSSpace => finiteModeLinearMatrixTimeVelocity A g 0 x) T) :=
  finiteModeLinearMatrix_timeDependent_initial_without_finiteTimeWitness
    hA hg0 hT

end FiniteModeEnergyObstructionRegression

end NavierStokes
end FluidDynamics
end Mettapedia
