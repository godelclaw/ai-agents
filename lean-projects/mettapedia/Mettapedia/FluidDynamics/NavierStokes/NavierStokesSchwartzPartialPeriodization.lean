import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSchwartzDivergenceFreeData
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3

/-!
# Navier-Stokes Schwartz Partial Periodization

This file formalizes a finite bottom-up precursor to Appendix H.2/H.3 of the
manuscript.  Instead of the full infinite periodization series, we work with
finite lattice sums of translated Schwartz data.  This is enough to package the
exact local algebra that the later large-torus exhaustion argument needs:
translations preserve Schwartz regularity and divergence freeness, and finite
partial periodizations preserve smoothness and divergence freeness.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ContDiff SchwartzMap

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

/-- Integer lattice indices for `ℤ^3`. -/
abbrev NSLatticeIndex : Type := Fin 3 → ℤ

/-- The `2πL` lattice shift corresponding to an index `n ∈ ℤ^3`. -/
def periodizationShift (L : ℝ) (n : NSLatticeIndex) : NSSpace :=
  ∑ i : Fin 3, EuclideanSpace.single i ((2 * Real.pi * L) * (n i : ℝ))

/-- The zero lattice index induces the zero shift. -/
theorem periodizationShift_zero (L : ℝ) :
    periodizationShift L 0 = 0 := by
  ext i
  simp [periodizationShift]

/-- Translate initial data by a spatial vector. -/
def translateInitialVelocity (u₀ : NSInitialVelocity) (a : NSSpace) : NSInitialVelocity :=
  fun x => u₀ (x + a)

/-- Smoothness is preserved by spatial translation. -/
theorem smoothInitialVelocityData_translateInitialVelocity
    {u₀ : NSInitialVelocity}
    (hsmooth : smoothInitialVelocityData u₀)
    (a : NSSpace) :
    smoothInitialVelocityData (translateInitialVelocity u₀ a) := by
  unfold smoothInitialVelocityData translateInitialVelocity
  simpa using hsmooth.comp (contDiff_id.add contDiff_const)

/-- Initial divergence commutes with spatial translation on smooth data. -/
theorem initialSpatialDivergence_translateInitialVelocity
    {u₀ : NSInitialVelocity}
    (hsmooth : smoothInitialVelocityData u₀)
    (a x : NSSpace) :
    initialSpatialDivergence (translateInitialVelocity u₀ a) x =
      initialSpatialDivergence u₀ (x + a) := by
  unfold initialSpatialDivergence translateInitialVelocity
  have hu :
      HasFDerivAt u₀ (fderiv ℝ u₀ (x + a)) (x + a) :=
    ((hsmooth.differentiable (by simp)) (x + a)).hasFDerivAt
  have ha :
      HasFDerivAt (fun y : NSSpace => y + a) (ContinuousLinearMap.id ℝ NSSpace) x := by
    simpa using (hasFDerivAt_id x).add_const a
  have hfd :
      fderiv ℝ (fun y : NSSpace => u₀ (y + a)) x =
        fderiv ℝ u₀ (x + a) := by
    simpa using (hu.comp x ha).fderiv
  rw [hfd]

/-- Divergence freeness is preserved by spatial translation on smooth data. -/
theorem divergenceFreeInitialVelocityData_translateInitialVelocity
    {u₀ : NSInitialVelocity}
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (a : NSSpace) :
    ∀ x, initialSpatialDivergence (translateInitialVelocity u₀ a) x = 0 := by
  intro x
  rw [initialSpatialDivergence_translateInitialVelocity hsmooth a x]
  exact hdiv (x + a)

/-- Spatial translation is antilipschitz with constant `1`. -/
theorem antilipschitzWith_translateNSSpace
    (a : NSSpace) :
    AntilipschitzWith 1 (fun x : NSSpace => x + a) := by
  simpa using
    (IsometryClass.antilipschitz (IsometryEquiv.addRight a : NSSpace ≃ᵢ NSSpace))

/-- Finite sums of smooth initial data are smooth. -/
theorem smoothInitialVelocityData_finset_sum
    {ι : Type*} (s : Finset ι) {u : ι → NSInitialVelocity}
    (hsmooth : ∀ i ∈ s, smoothInitialVelocityData (u i)) :
    smoothInitialVelocityData ((s.sum u) : NSInitialVelocity) := by
  classical
  induction s using Finset.induction_on generalizing u with
  | empty =>
      simpa [smoothInitialVelocityData] using
        (contDiff_const : ContDiff ℝ ∞ (0 : NSInitialVelocity))
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact
        (hsmooth i (by simp)).add <|
          ih (fun j hj => hsmooth j (by simp [hj]))

/-- Initial divergence commutes with finite sums of smooth initial data. -/
theorem initialSpatialDivergence_finset_sum
    {ι : Type*} (s : Finset ι) {u : ι → NSInitialVelocity}
    (hsmooth : ∀ i ∈ s, smoothInitialVelocityData (u i))
    (x : NSSpace) :
    initialSpatialDivergence ((s.sum u) : NSInitialVelocity) x =
      s.sum (fun i => initialSpatialDivergence (u i) x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [initialSpatialDivergence_zero]
  | @insert i s hi ih =>
      have hiSmooth : smoothInitialVelocityData (u i) :=
        hsmooth i (by simp)
      have hsSmooth : ∀ j ∈ s, smoothInitialVelocityData (u j) := by
        intro j hj
        exact hsmooth j (by simp [hj])
      have hsumSmooth : smoothInitialVelocityData ((s.sum u) : NSInitialVelocity) :=
        smoothInitialVelocityData_finset_sum s hsSmooth
      rw [Finset.sum_insert hi]
      rw [initialSpatialDivergence_add
        (((hiSmooth.differentiable (by simp)) x))
        (((hsumSmooth.differentiable (by simp)) x))]
      simp [ih hsSmooth, hi]

/-- Translation preserves Schwartz initial data. -/
def translateSchwartzInitialVelocity
    (u₀ : NSSchwartzInitialVelocity) (a : NSSpace) :
    NSSchwartzInitialVelocity :=
  SchwartzMap.compCLMOfAntilipschitz ℝ
    (g := fun x : NSSpace => x + a)
    (by fun_prop)
    (antilipschitzWith_translateNSSpace a)
    u₀

/-- The translated Schwartz datum is the expected translated function. -/
@[simp] theorem translateSchwartzInitialVelocity_apply
    (u₀ : NSSchwartzInitialVelocity) (a x : NSSpace) :
    translateSchwartzInitialVelocity u₀ a x = u₀ (x + a) := by
  simp [translateSchwartzInitialVelocity]

/-- Finite partial periodization of initial data by lattice shifts. -/
def finitePartialPeriodizedInitialVelocity
    (s : Finset NSLatticeIndex) (L : ℝ) (u₀ : NSInitialVelocity) :
    NSInitialVelocity :=
  fun x => s.sum (fun n => u₀ (x + periodizationShift L n))

/-- The raw finite partial periodization is the same finite sum of translated
initial data. -/
theorem finitePartialPeriodizedInitialVelocity_eq_finset_sum_translate
    (s : Finset NSLatticeIndex) (L : ℝ) (u₀ : NSInitialVelocity) :
    finitePartialPeriodizedInitialVelocity s L u₀ =
      s.sum (fun n => translateInitialVelocity u₀ (periodizationShift L n)) := by
  ext x
  simp [finitePartialPeriodizedInitialVelocity, translateInitialVelocity, Finset.sum_apply]

/-- Finite partial periodizations of smooth data are smooth. -/
theorem smoothInitialVelocityData_finitePartialPeriodizedInitialVelocity
    (s : Finset NSLatticeIndex) (L : ℝ) {u₀ : NSInitialVelocity}
    (hsmooth : smoothInitialVelocityData u₀) :
    smoothInitialVelocityData (finitePartialPeriodizedInitialVelocity s L u₀) := by
  rw [finitePartialPeriodizedInitialVelocity_eq_finset_sum_translate]
  exact smoothInitialVelocityData_finset_sum s
      (u := fun n => translateInitialVelocity u₀ (periodizationShift L n))
      (fun _ _ => smoothInitialVelocityData_translateInitialVelocity hsmooth _)

/-- Finite partial periodizations preserve divergence freeness on smooth data. -/
theorem divergenceFreeInitialVelocityData_finitePartialPeriodizedInitialVelocity
    (s : Finset NSLatticeIndex) (L : ℝ) {u₀ : NSInitialVelocity}
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0) :
    ∀ x, initialSpatialDivergence (finitePartialPeriodizedInitialVelocity s L u₀) x = 0 := by
  intro x
  rw [finitePartialPeriodizedInitialVelocity_eq_finset_sum_translate]
  rw [initialSpatialDivergence_finset_sum
    (s := s) (u := fun n => translateInitialVelocity u₀ (periodizationShift L n))]
  · apply Finset.sum_eq_zero
    intro n hn
    exact divergenceFreeInitialVelocityData_translateInitialVelocity hsmooth hdiv _ x
  · intro n hn
    exact smoothInitialVelocityData_translateInitialVelocity hsmooth _

/-- Finite partial periodization preserves Schwartz regularity. -/
def finitePartialPeriodizationSchwartzInitialVelocity
    (s : Finset NSLatticeIndex) (L : ℝ) (u₀ : NSSchwartzInitialVelocity) :
    NSSchwartzInitialVelocity :=
  s.sum (fun n => translateSchwartzInitialVelocity u₀ (periodizationShift L n))

/-- The Schwartz partial periodization is the expected finite lattice sum. -/
@[simp] theorem finitePartialPeriodizationSchwartzInitialVelocity_apply
    (s : Finset NSLatticeIndex) (L : ℝ) (u₀ : NSSchwartzInitialVelocity) (x : NSSpace) :
    finitePartialPeriodizationSchwartzInitialVelocity s L u₀ x =
      s.sum (fun n => u₀ (x + periodizationShift L n)) := by
  simp [finitePartialPeriodizationSchwartzInitialVelocity]

/-- The Schwartz partial periodization agrees with the raw finite partial
periodization on the underlying function. -/
theorem finitePartialPeriodizationSchwartzInitialVelocity_coe_eq
    (s : Finset NSLatticeIndex) (L : ℝ) (u₀ : NSSchwartzInitialVelocity) :
    (finitePartialPeriodizationSchwartzInitialVelocity s L u₀ : NSSpace → NSSpace) =
      finitePartialPeriodizedInitialVelocity s L (u₀ : NSSpace → NSSpace) := by
  ext x
  simp [finitePartialPeriodizedInitialVelocity]

/-- Finite partial periodizations of divergence-free Schwartz data remain in the
manuscript's `Sσ(ℝ^3)` input class. -/
def finitePartialPeriodizationSchwartzDivergenceFreeInitialVelocity
    (s : Finset NSLatticeIndex) (L : ℝ)
    (u₀ : NSSchwartzDivergenceFreeInitialVelocity) :
    NSSchwartzDivergenceFreeInitialVelocity :=
  ⟨finitePartialPeriodizationSchwartzInitialVelocity s L u₀.1, by
    simpa [finitePartialPeriodizationSchwartzInitialVelocity_coe_eq]
      using
        divergenceFreeInitialVelocityData_finitePartialPeriodizedInitialVelocity
          s L
          (smoothInitialVelocityData_of_schwartzDivergenceFreeInitialVelocity u₀)
          (divergenceFreeInitialVelocityData_of_schwartzDivergenceFreeInitialVelocity u₀)⟩

end NavierStokes
end FluidDynamics
end Mettapedia
