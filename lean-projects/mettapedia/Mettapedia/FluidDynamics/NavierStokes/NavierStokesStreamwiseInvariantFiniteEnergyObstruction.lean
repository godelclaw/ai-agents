import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSchwartzDirectionalRigidity
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Finite-Energy Obstruction for Streamwise-Invariant Data

This file records a bottom-up whole-space obstruction on `ℝ^3`:

if a smooth initial velocity profile is translation invariant in the streamwise
`x₀` direction and is not identically zero, then it cannot have finite initial
kinetic energy.

The proof does not depend on any special ansatz.  It uses a concrete
determinant-`2` scaling that stretches only the streamwise direction, leaving
the kinetic-energy density unchanged under the translation-invariance
hypothesis while rescaling Haar measure by `1 / 2`.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open MeasureTheory

abbrev coord0 : Fin 3 := 0
abbrev coord1 : Fin 3 := 1
abbrev coord2 : Fin 3 := 2

/-- The streamwise basis direction `e₀`. -/
def streamwiseDirection : NSSpace :=
  EuclideanSpace.single coord0 (1 : ℝ)

/-- The anisotropic scaling that doubles only the streamwise `x₀` direction. -/
def streamwiseScaling : NSSpace →ₗ[ℝ] NSSpace :=
  Matrix.toEuclideanLin (Matrix.diagonal ![(2 : ℝ), 1, 1])

/-- The streamwise scaling is exactly translation by `x₀ e₀`. -/
theorem streamwiseScaling_eq_add_coord0_smul_streamwiseDirection
    (x : NSSpace) :
    streamwiseScaling x = x + (x coord0) • streamwiseDirection := by
  ext i
  fin_cases i <;>
    simp [streamwiseScaling, streamwiseDirection, Matrix.toLpLin_apply,
      Matrix.mulVec, coord0, two_mul]

/-- Any streamwise-translation-invariant profile is fixed by the streamwise
scaling. -/
theorem comp_streamwiseScaling_eq_of_translationInvariantAlong_streamwise
    {α : Type*} {f : NSSpace → α}
    (hinv : TranslationInvariantAlong streamwiseDirection f) :
    (fun x => f (streamwiseScaling x)) = f := by
  funext x
  simpa [streamwiseScaling_eq_add_coord0_smul_streamwiseDirection] using
    hinv x (x coord0)

/-- The streamwise scaling has determinant `2`. -/
theorem det_streamwiseScaling :
    LinearMap.det streamwiseScaling = 2 := by
  rw [streamwiseScaling, Matrix.toEuclideanLin_eq_toLin_orthonormal]
  rw [LinearMap.det_toLin, Matrix.det_diagonal, Fin.prod_univ_three]
  have h0 : (![2, 1, 1] (0 : Fin 3) : ℝ) = 2 := by rfl
  have h1 : (![2, 1, 1] (1 : Fin 3) : ℝ) = 1 := by rfl
  have h2 : (![2, 1, 1] (2 : Fin 3) : ℝ) = 1 := by rfl
  rw [h0, h1, h2]
  norm_num

/-- A nonnegative continuous scalar field on `ℝ^3` that is invariant under
translation in the streamwise direction cannot be integrable unless it
vanishes everywhere.  The proof uses the determinant-`2` streamwise scaling.
-/
theorem not_integrable_of_continuous_nonneg_translationInvariantAlong_streamwise_of_exists_ne_zero_point
    {f : NSSpace → ℝ}
    (hcont : Continuous f)
    (hnonneg : ∀ x, 0 ≤ f x)
    (hinv : TranslationInvariantAlong streamwiseDirection f)
    (hpoint : ∃ x, f x ≠ 0) :
    ¬ Integrable f := by
  intro hInt
  rcases hpoint with ⟨x0, hx0⟩
  have hpos : 0 < ∫ x, f x := by
    exact MeasureTheory.integral_pos_of_integrable_nonneg_nonzero
      (x := x0) hcont hInt hnonneg hx0
  let I : ℝ := ∫ x, f x
  have hcomp :
      ∫ x, f (streamwiseScaling x) = I := by
    calc
      ∫ x, f (streamwiseScaling x)
          = ∫ x, f x := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with x
              exact congrArg (fun g : NSSpace → ℝ => g x)
                (comp_streamwiseScaling_eq_of_translationInvariantAlong_streamwise hinv)
      _ = I := by rfl
  have hdet : LinearMap.det streamwiseScaling ≠ 0 := by
    rw [det_streamwiseScaling]
    norm_num
  have hmap :
      MeasureTheory.Measure.map streamwiseScaling
          (MeasureTheory.volume : MeasureTheory.Measure NSSpace) =
        ENNReal.ofReal ((2 : ℝ)⁻¹) •
          (MeasureTheory.volume : MeasureTheory.Measure NSSpace) := by
    rw [MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar
      (μ := (MeasureTheory.volume : MeasureTheory.Measure NSSpace)) (f := streamwiseScaling)
      hdet]
    simp [det_streamwiseScaling]
  have hchange :
      ∫ x, f (streamwiseScaling x) = ((2 : ℝ)⁻¹) * I := by
    calc
      ∫ x : NSSpace, f (streamwiseScaling x)
          = ∫ y : NSSpace, f y ∂
              MeasureTheory.Measure.map streamwiseScaling
                (MeasureTheory.volume : MeasureTheory.Measure NSSpace) := by
              symm
              exact MeasureTheory.integral_map
                (μ := (MeasureTheory.volume : MeasureTheory.Measure NSSpace))
                (streamwiseScaling.continuous_of_finiteDimensional.aemeasurable)
                hcont.aestronglyMeasurable
      _ = ((2 : ℝ)⁻¹) * I := by
            rw [hmap, MeasureTheory.integral_smul_measure]
            simp [I]
  have hEq : I = ((2 : ℝ)⁻¹) * I := by
    simpa [hcomp] using hchange
  have hzero : I = 0 := by
    norm_num at hEq
    linarith
  have hposI : 0 < I := by
    simpa [I] using hpos
  nlinarith [hposI, hzero]

/-- Initial kinetic-energy density inherits streamwise translation invariance
from the underlying initial velocity profile. -/
theorem translationInvariantAlong_initialKineticEnergyDensity_of_translationInvariantAlong_streamwise
    {u₀ : NSInitialVelocity}
    (hinv : TranslationInvariantAlong streamwiseDirection u₀) :
    TranslationInvariantAlong streamwiseDirection (initialKineticEnergyDensity u₀) := by
  intro x s
  simp [initialKineticEnergyDensity, hinv x s]

/-- Smooth initial velocity data have continuous initial kinetic-energy
density. -/
theorem continuous_initialKineticEnergyDensity_of_smoothInitialVelocityData
    {u₀ : NSInitialVelocity}
    (hsmooth : smoothInitialVelocityData u₀) :
    Continuous (initialKineticEnergyDensity u₀) := by
  simpa [initialKineticEnergyDensity] using
    (continuous_norm.comp hsmooth.continuous).pow (2 : ℕ)

/-- Any nonzero smooth initial velocity profile that is invariant under
translation in the streamwise direction is not finite-energy admissible on
`ℝ^3`. -/
theorem not_finiteInitialKineticEnergy_of_translationInvariantAlong_streamwise_of_exists_ne_zero
    {u₀ : NSInitialVelocity}
    (hsmooth : smoothInitialVelocityData u₀)
    (hinv : TranslationInvariantAlong streamwiseDirection u₀)
    (hpoint : ∃ x, u₀ x ≠ 0) :
    ¬ finiteInitialKineticEnergy u₀ := by
  refine
    not_integrable_of_continuous_nonneg_translationInvariantAlong_streamwise_of_exists_ne_zero_point
      (f := initialKineticEnergyDensity u₀)
      (continuous_initialKineticEnergyDensity_of_smoothInitialVelocityData hsmooth)
      (fun x => by
        simpa [initialKineticEnergyDensity, pow_two] using sq_nonneg ‖u₀ x‖)
      (translationInvariantAlong_initialKineticEnergyDensity_of_translationInvariantAlong_streamwise
        hinv) ?_
  rcases hpoint with ⟨x0, hx0⟩
  refine ⟨x0, ?_⟩
  simp [initialKineticEnergyDensity, hx0]

/-- Streamwise-invariant smooth initial data are finite-energy admissible only
in the zero case. -/
theorem not_finiteInitialKineticEnergy_of_translationInvariantAlong_streamwise_of_ne_zero
    {u₀ : NSInitialVelocity}
    (hsmooth : smoothInitialVelocityData u₀)
    (hinv : TranslationInvariantAlong streamwiseDirection u₀)
    (hzero : u₀ ≠ 0) :
    ¬ finiteInitialKineticEnergy u₀ := by
  apply
    not_finiteInitialKineticEnergy_of_translationInvariantAlong_streamwise_of_exists_ne_zero
      hsmooth hinv
  by_contra hpoint
  push_neg at hpoint
  apply hzero
  funext x
  exact hpoint x

/-- Therefore the repaired finite-energy whole-space input domain contains no
problem datum whose initial velocity is a nonzero smooth streamwise-invariant
profile. -/
theorem not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_of_translationInvariantAlong_streamwise_of_ne_zero
    {u₀ : NSInitialVelocity}
    (hsmooth : smoothInitialVelocityData u₀)
    (hinv : TranslationInvariantAlong streamwiseDirection u₀)
    (hzero : u₀ ≠ 0) :
    ¬ Nonempty { P : FiniteEnergyAdmissibleNavierStokesProblemData //
        P.initialVelocity = u₀ } := by
  exact
    not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_of_not_finiteInitialKineticEnergy
      (u₀ := u₀)
      (not_finiteInitialKineticEnergy_of_translationInvariantAlong_streamwise_of_ne_zero
        hsmooth hinv hzero)

end NavierStokes
end FluidDynamics
end Mettapedia
