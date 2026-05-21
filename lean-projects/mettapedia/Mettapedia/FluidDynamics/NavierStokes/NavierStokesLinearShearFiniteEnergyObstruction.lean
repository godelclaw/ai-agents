import Mettapedia.FluidDynamics.NavierStokes.NavierStokesStreamwiseInvariantFiniteEnergyObstruction
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSchwartzLinearShearObstruction

/-!
# Finite-Energy Obstruction for Affine Linear-Shear Seed Families

This file turns the generic streamwise-invariant finite-energy obstruction into
concrete blockers for the affine linear-shear families on `ℝ^3`.

As with the heat-shear file, the proof is structural rather than ansatz-
specific: these initial data depend only on the transverse coordinate `x₁`, so
their initial kinetic-energy density is translation invariant along the
streamwise `x₀` direction.  The determinant-`2` streamwise scaling from
`NavierStokesStreamwiseInvariantFiniteEnergyObstruction.lean` then forces any
nonzero such profile to have infinite initial kinetic energy.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

/-- The affine linear-shear streamwise direction agrees with the generic
streamwise direction used in the finite-energy obstruction. -/
theorem linearShearStreamwiseDirection_eq_streamwiseDirection :
    linearShearStreamwiseDirection = streamwiseDirection := by
  ext i
  fin_cases i <;>
    simp [linearShearStreamwiseDirection, streamwiseDirection, nsCoord0, coord0]

/-- Full-drift affine linear-shear data remain streamwise-translation-invariant. -/
theorem translationInvariantAlong_linearShearFullDriftInitialVelocity_streamwise_generic
    (a b c : ℝ) :
    TranslationInvariantAlong streamwiseDirection
      (linearShearFullDriftInitialVelocity a b c) := by
  simpa [linearShearStreamwiseDirection_eq_streamwiseDirection] using
    translationInvariantAlong_linearShearFullDriftInitialVelocity_streamwise a b c

/-- Any nontrivial affine linear-shear full-drift profile already lies outside
the repaired finite-energy whole-space input surface. -/
theorem not_finiteInitialKineticEnergy_linearShearFullDriftInitialVelocity_of_parameter_ne_zero
    {a b c : ℝ}
    (hparam : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) :
    ¬ finiteInitialKineticEnergy (linearShearFullDriftInitialVelocity a b c) := by
  refine
    not_finiteInitialKineticEnergy_of_translationInvariantAlong_streamwise_of_ne_zero ?_ ?_ ?_
  · simpa using smoothInitialVelocityData_linearShearFullDriftInitialVelocity a b c
  · exact translationInvariantAlong_linearShearFullDriftInitialVelocity_streamwise_generic a b c
  · intro hzero
    have hdeg :
        a = 0 ∧ b = 0 ∧ c = 0 :=
      (linearShearFullDriftInitialVelocity_eq_zero_iff (a := a) (b := b) (c := c)).mp hzero
    rcases hdeg with ⟨ha, hb, hc⟩
    rcases hparam with ha' | hb' | hc'
    · exact ha' ha
    · exact hb' hb
    · exact hc' hc

/-- Therefore the repaired finite-energy admissible-data type is empty on any
nontrivial affine linear-shear full-drift profile. -/
theorem not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_linearShearFullDriftInitialVelocity_of_parameter_ne_zero
    {a b c : ℝ}
    (hparam : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) :
    ¬ Nonempty { P : FiniteEnergyAdmissibleNavierStokesProblemData //
        P.initialVelocity = linearShearFullDriftInitialVelocity a b c } := by
  exact
    not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_of_not_finiteInitialKineticEnergy
      (u₀ := linearShearFullDriftInitialVelocity a b c)
      (not_finiteInitialKineticEnergy_linearShearFullDriftInitialVelocity_of_parameter_ne_zero
        hparam)

/-- Base affine linear shear is likewise excluded from the repaired finite-
energy input surface whenever the shear coefficient is nonzero. -/
theorem not_finiteInitialKineticEnergy_linearShearInitialVelocity_of_shear_ne_zero
    {a : ℝ} (ha : a ≠ 0) :
    ¬ finiteInitialKineticEnergy (linearShearInitialVelocity a) := by
  simpa [linearShearFullDriftInitialVelocity_zero_drifts] using
    (not_finiteInitialKineticEnergy_linearShearFullDriftInitialVelocity_of_parameter_ne_zero
      (a := a) (b := 0) (c := 0) (Or.inl ha))

/-- So the repaired finite-energy admissible-data type is empty on every
nontrivial base affine linear-shear seed. -/
theorem not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_linearShearInitialVelocity_of_shear_ne_zero
    {a : ℝ} (ha : a ≠ 0) :
    ¬ Nonempty { P : FiniteEnergyAdmissibleNavierStokesProblemData //
        P.initialVelocity = linearShearInitialVelocity a } := by
  simpa [linearShearFullDriftInitialVelocity_zero_drifts] using
    (not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_linearShearFullDriftInitialVelocity_of_parameter_ne_zero
      (a := a) (b := 0) (c := 0) (Or.inl ha))

/-- Vertical-drift affine linear shear is likewise excluded from the repaired
finite-energy input surface whenever either parameter is nonzero. -/
theorem not_finiteInitialKineticEnergy_linearShearVerticalDriftInitialVelocity_of_shear_ne_zero_or_verticalDrift_ne_zero
    {a c : ℝ} (hparam : a ≠ 0 ∨ c ≠ 0) :
    ¬ finiteInitialKineticEnergy (linearShearVerticalDriftInitialVelocity a c) := by
  simpa [linearShearFullDriftInitialVelocity_zero_horizontalDrift] using
    (not_finiteInitialKineticEnergy_linearShearFullDriftInitialVelocity_of_parameter_ne_zero
      (a := a) (b := 0) (c := c)
      (by
        rcases hparam with ha | hc
        · exact Or.inl ha
        · exact Or.inr <| Or.inr hc))

/-- So the repaired finite-energy admissible-data type is empty on every
nontrivial vertical-drift affine linear-shear seed. -/
theorem not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_linearShearVerticalDriftInitialVelocity_of_shear_ne_zero_or_verticalDrift_ne_zero
    {a c : ℝ} (hparam : a ≠ 0 ∨ c ≠ 0) :
    ¬ Nonempty { P : FiniteEnergyAdmissibleNavierStokesProblemData //
        P.initialVelocity = linearShearVerticalDriftInitialVelocity a c } := by
  simpa [linearShearFullDriftInitialVelocity_zero_horizontalDrift] using
    (not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_linearShearFullDriftInitialVelocity_of_parameter_ne_zero
      (a := a) (b := 0) (c := c)
      (by
        rcases hparam with ha | hc
        · exact Or.inl ha
        · exact Or.inr <| Or.inr hc))

/-- Horizontal-drift affine linear shear is likewise excluded from the repaired
finite-energy input surface whenever either parameter is nonzero. -/
theorem not_finiteInitialKineticEnergy_linearShearHorizontalDriftInitialVelocity_of_shear_ne_zero_or_horizontalDrift_ne_zero
    {a b : ℝ} (hparam : a ≠ 0 ∨ b ≠ 0) :
    ¬ finiteInitialKineticEnergy (linearShearHorizontalDriftInitialVelocity a b) := by
  simpa [linearShearFullDriftInitialVelocity_zero_verticalDrift] using
    (not_finiteInitialKineticEnergy_linearShearFullDriftInitialVelocity_of_parameter_ne_zero
      (a := a) (b := b) (c := 0)
      (by
        rcases hparam with ha | hb
        · exact Or.inl ha
        · exact Or.inr <| Or.inl hb))

/-- So the repaired finite-energy admissible-data type is empty on every
nontrivial horizontal-drift affine linear-shear seed. -/
theorem not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_linearShearHorizontalDriftInitialVelocity_of_shear_ne_zero_or_horizontalDrift_ne_zero
    {a b : ℝ} (hparam : a ≠ 0 ∨ b ≠ 0) :
    ¬ Nonempty { P : FiniteEnergyAdmissibleNavierStokesProblemData //
        P.initialVelocity = linearShearHorizontalDriftInitialVelocity a b } := by
  simpa [linearShearFullDriftInitialVelocity_zero_verticalDrift] using
    (not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_linearShearFullDriftInitialVelocity_of_parameter_ne_zero
      (a := a) (b := b) (c := 0)
      (by
        rcases hparam with ha | hb
        · exact Or.inl ha
        · exact Or.inr <| Or.inl hb))

end NavierStokes
end FluidDynamics
end Mettapedia
