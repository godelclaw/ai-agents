import Mettapedia.FluidDynamics.NavierStokes.NavierStokesStreamwiseInvariantFiniteEnergyObstruction
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSchwartzTransportedHeatShearObstruction

/-!
# Finite-Energy Obstruction for Heat-Shear Seed Families

This file turns the generic streamwise-invariant finite-energy obstruction into
concrete blockers for the manuscript-facing heat-shear families on `ℝ^3`.

The key point is structural rather than ansatz-specific: these velocity fields
depend only on the transverse coordinate `x₁`, so their initial kinetic-energy
density is translation invariant along the streamwise `x₀` direction.  The
determinant-`2` streamwise scaling from
`NavierStokesStreamwiseInvariantFiniteEnergyObstruction.lean` then forces any
nonzero such profile to have infinite initial kinetic energy.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

/-- The manuscript heat-shear streamwise direction agrees with the generic
streamwise direction used in the finite-energy obstruction. -/
theorem heatShearStreamwiseDirection_eq_streamwiseDirection :
    heatShearStreamwiseDirection = streamwiseDirection := by
  ext i
  fin_cases i <;>
    simp [heatShearStreamwiseDirection, streamwiseDirection, nsCoord0, coord0]

/-- Full-drift heat-shear data remain streamwise-translation-invariant. -/
theorem translationInvariantAlong_heatShearFullDriftInitialVelocity_streamwise
    (a k d c : ℝ) :
    TranslationInvariantAlong streamwiseDirection
      (heatShearFullDriftInitialVelocity a k d c) := by
  simpa [heatShearStreamwiseDirection_eq_streamwiseDirection,
    heatShearTransportFullDriftInitialVelocity_zero_transport] using
    translationInvariantAlong_heatShearTransportFullDriftInitialVelocity_streamwise a k 0 d c

/-- The full-drift heat-shear datum vanishes exactly in the degenerate case
`d = 0`, `c = 0`, and `a * k = 0`. -/
theorem heatShearFullDriftInitialVelocity_eq_zero_iff
    {a k d c : ℝ} :
    heatShearFullDriftInitialVelocity a k d c = (0 : NSInitialVelocity) ↔
      d = 0 ∧ c = 0 ∧ a * k = 0 := by
  simpa [heatShearTransportFullDriftInitialVelocity_zero_transport] using
    (heatShearTransportFullDriftInitialVelocity_eq_zero_iff
      (a := a) (k := k) (b := 0) (d := d) (c := c))

/-- Any nondegenerate full-drift heat-shear profile already lies outside the
repaired finite-energy whole-space input surface. -/
theorem not_finiteInitialKineticEnergy_heatShearFullDriftInitialVelocity_of_streamwiseDrift_ne_zero_or_verticalDrift_ne_zero_or_amplitude_mul_wavenumber_ne_zero
    {a k d c : ℝ}
    (hparam : d ≠ 0 ∨ c ≠ 0 ∨ a * k ≠ 0) :
    ¬ finiteInitialKineticEnergy (heatShearFullDriftInitialVelocity a k d c) := by
  refine
    not_finiteInitialKineticEnergy_of_translationInvariantAlong_streamwise_of_ne_zero ?_ ?_ ?_
  · simpa using smoothInitialVelocityData_heatShearFullDriftInitialVelocity a k d c
  · exact translationInvariantAlong_heatShearFullDriftInitialVelocity_streamwise a k d c
  · intro hzero
    have hdeg :
        d = 0 ∧ c = 0 ∧ a * k = 0 :=
      (heatShearFullDriftInitialVelocity_eq_zero_iff
        (a := a) (k := k) (d := d) (c := c)).mp hzero
    rcases hdeg with ⟨hd, hc, hak⟩
    rcases hparam with hdne | hcne | hakne
    · exact hdne hd
    · exact hcne hc
    · exact hakne hak

/-- Therefore the repaired finite-energy admissible-data type is empty on any
nondegenerate full-drift heat-shear profile. -/
theorem not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_heatShearFullDriftInitialVelocity_of_streamwiseDrift_ne_zero_or_verticalDrift_ne_zero_or_amplitude_mul_wavenumber_ne_zero
    {a k d c : ℝ}
    (hparam : d ≠ 0 ∨ c ≠ 0 ∨ a * k ≠ 0) :
    ¬ Nonempty { P : FiniteEnergyAdmissibleNavierStokesProblemData //
        P.initialVelocity = heatShearFullDriftInitialVelocity a k d c } := by
  exact
    not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearFullDriftInitialVelocity a k d c)
      (not_finiteInitialKineticEnergy_heatShearFullDriftInitialVelocity_of_streamwiseDrift_ne_zero_or_verticalDrift_ne_zero_or_amplitude_mul_wavenumber_ne_zero
        hparam)

/-- The base heat-shear seed is likewise excluded from the repaired
finite-energy input surface whenever its oscillatory part is nondegenerate. -/
theorem not_finiteInitialKineticEnergy_heatShearInitialVelocity_of_amplitude_mul_wavenumber_ne_zero
    {a k : ℝ} (hak : a * k ≠ 0) :
    ¬ finiteInitialKineticEnergy (heatShearInitialVelocity a k) := by
  simpa [heatShearFullDriftInitialVelocity_zero_drifts] using
    (not_finiteInitialKineticEnergy_heatShearFullDriftInitialVelocity_of_streamwiseDrift_ne_zero_or_verticalDrift_ne_zero_or_amplitude_mul_wavenumber_ne_zero
      (a := a) (k := k) (d := 0) (c := 0) (Or.inr <| Or.inr hak))

/-- So the repaired finite-energy admissible-data type is empty on every
nondegenerate base heat-shear seed. -/
theorem not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_heatShearInitialVelocity_of_amplitude_mul_wavenumber_ne_zero
    {a k : ℝ} (hak : a * k ≠ 0) :
    ¬ Nonempty { P : FiniteEnergyAdmissibleNavierStokesProblemData //
        P.initialVelocity = heatShearInitialVelocity a k } := by
  simpa [heatShearFullDriftInitialVelocity_zero_drifts] using
    (not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_heatShearFullDriftInitialVelocity_of_streamwiseDrift_ne_zero_or_verticalDrift_ne_zero_or_amplitude_mul_wavenumber_ne_zero
      (a := a) (k := k) (d := 0) (c := 0) (Or.inr <| Or.inr hak))

/-- Transported full-drift heat-shear data are also streamwise-translation
invariant in the generic sense used by the finite-energy obstruction. -/
theorem translationInvariantAlong_heatShearTransportFullDriftInitialVelocity_streamwise_generic
    (a k b d c : ℝ) :
    TranslationInvariantAlong streamwiseDirection
      (heatShearTransportFullDriftInitialVelocity a k b d c) := by
  simpa [heatShearStreamwiseDirection_eq_streamwiseDirection] using
    translationInvariantAlong_heatShearTransportFullDriftInitialVelocity_streamwise a k b d c

/-- Any nondegenerate transported full-drift heat-shear profile already lies
outside the repaired finite-energy whole-space input surface. -/
theorem not_finiteInitialKineticEnergy_heatShearTransportFullDriftInitialVelocity_of_transport_ne_zero_or_streamwiseDrift_ne_zero_or_verticalDrift_ne_zero_or_amplitude_mul_wavenumber_ne_zero
    {a k b d c : ℝ}
    (hparam : b ≠ 0 ∨ d ≠ 0 ∨ c ≠ 0 ∨ a * k ≠ 0) :
    ¬ finiteInitialKineticEnergy (heatShearTransportFullDriftInitialVelocity a k b d c) := by
  refine
    not_finiteInitialKineticEnergy_of_translationInvariantAlong_streamwise_of_ne_zero ?_ ?_ ?_
  · simpa using smoothInitialVelocityData_heatShearTransportFullDriftInitialVelocity a k b d c
  · exact translationInvariantAlong_heatShearTransportFullDriftInitialVelocity_streamwise_generic a k b d c
  · intro hzero
    have hdeg :
        b = 0 ∧ d = 0 ∧ c = 0 ∧ a * k = 0 :=
      (heatShearTransportFullDriftInitialVelocity_eq_zero_iff
        (a := a) (k := k) (b := b) (d := d) (c := c)).mp hzero
    rcases hdeg with ⟨hb, hd, hc, hak⟩
    rcases hparam with hbne | hdne | hcne | hakne
    · exact hbne hb
    · exact hdne hd
    · exact hcne hc
    · exact hakne hak

/-- Therefore the repaired finite-energy admissible-data type is empty on any
nondegenerate transported full-drift heat-shear profile. -/
theorem not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_heatShearTransportFullDriftInitialVelocity_of_transport_ne_zero_or_streamwiseDrift_ne_zero_or_verticalDrift_ne_zero_or_amplitude_mul_wavenumber_ne_zero
    {a k b d c : ℝ}
    (hparam : b ≠ 0 ∨ d ≠ 0 ∨ c ≠ 0 ∨ a * k ≠ 0) :
    ¬ Nonempty { P : FiniteEnergyAdmissibleNavierStokesProblemData //
        P.initialVelocity = heatShearTransportFullDriftInitialVelocity a k b d c } := by
  exact
    not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearTransportFullDriftInitialVelocity a k b d c)
      (not_finiteInitialKineticEnergy_heatShearTransportFullDriftInitialVelocity_of_transport_ne_zero_or_streamwiseDrift_ne_zero_or_verticalDrift_ne_zero_or_amplitude_mul_wavenumber_ne_zero
        hparam)

/-- The transported heat-shear subfamily is likewise excluded from the
repaired finite-energy input surface whenever either the transport is nonzero
or the oscillatory part is nondegenerate. -/
theorem not_finiteInitialKineticEnergy_heatShearTransportInitialVelocity_of_transport_ne_zero_or_amplitude_mul_wavenumber_ne_zero
    {a k b : ℝ}
    (hparam : b ≠ 0 ∨ a * k ≠ 0) :
    ¬ finiteInitialKineticEnergy (heatShearTransportInitialVelocity a k b) := by
  simpa [heatShearTransportFullDriftInitialVelocity_zero_drifts] using
    (not_finiteInitialKineticEnergy_heatShearTransportFullDriftInitialVelocity_of_transport_ne_zero_or_streamwiseDrift_ne_zero_or_verticalDrift_ne_zero_or_amplitude_mul_wavenumber_ne_zero
      (a := a) (k := k) (b := b) (d := 0) (c := 0)
      (by
        rcases hparam with hb | hak
        · exact Or.inl hb
        · exact Or.inr <| Or.inr <| Or.inr hak))

/-- So the repaired finite-energy admissible-data type is empty on every
nondegenerate transported heat-shear seed. -/
theorem not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_heatShearTransportInitialVelocity_of_transport_ne_zero_or_amplitude_mul_wavenumber_ne_zero
    {a k b : ℝ}
    (hparam : b ≠ 0 ∨ a * k ≠ 0) :
    ¬ Nonempty { P : FiniteEnergyAdmissibleNavierStokesProblemData //
        P.initialVelocity = heatShearTransportInitialVelocity a k b } := by
  simpa [heatShearTransportFullDriftInitialVelocity_zero_drifts] using
    (not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_heatShearTransportFullDriftInitialVelocity_of_transport_ne_zero_or_streamwiseDrift_ne_zero_or_verticalDrift_ne_zero_or_amplitude_mul_wavenumber_ne_zero
      (a := a) (k := k) (b := b) (d := 0) (c := 0)
      (by
        rcases hparam with hb | hak
        · exact Or.inl hb
        · exact Or.inr <| Or.inr <| Or.inr hak))

end NavierStokes
end FluidDynamics
end Mettapedia
