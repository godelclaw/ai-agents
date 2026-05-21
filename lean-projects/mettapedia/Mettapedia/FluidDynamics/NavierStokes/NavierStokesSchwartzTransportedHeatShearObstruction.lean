import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSchwartzHeatShearObstruction

/-!
# Schwartz Obstruction for Transported Heat-Shear Data

This file extends the concrete Schwartz-lane obstruction from the basic
heat-shear initial datum to the transported full-drift family

`x ↦ (d + a * sin (k * x₁), b, c)`.

These initial data are still translation invariant along the streamwise `x₀`
direction, so any Schwartz realization would have to vanish identically.
An explicit zero classification shows that vanishing occurs exactly in the
degenerate parameter case `b = d = c = 0` and `a * k = 0`.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

/-- Transported full-drift heat-shear initial data depend only on the
transverse coordinate `x₁`, so they are invariant under streamwise
translation. -/
theorem translationInvariantAlong_heatShearTransportFullDriftInitialVelocity_streamwise
    (a k b d c : ℝ) :
    TranslationInvariantAlong heatShearStreamwiseDirection
      (heatShearTransportFullDriftInitialVelocity a k b d c) := by
  intro x s
  rw [heatShearTransportFullDriftInitialVelocity_apply,
    heatShearTransportFullDriftInitialVelocity_apply]
  ext i
  fin_cases i <;>
    simp [heatShearStreamwiseDirection, nsCoord0, nsCoord1, nsCoord2,
      add_left_comm, add_comm]

/-- The transported full-drift heat-shear initial datum is zero exactly in the
degenerate case `b = d = c = 0` and `a * k = 0`. -/
theorem heatShearTransportFullDriftInitialVelocity_eq_zero_iff
    {a k b d c : ℝ} :
    heatShearTransportFullDriftInitialVelocity a k b d c = (0 : NSInitialVelocity) ↔
      b = 0 ∧ d = 0 ∧ c = 0 ∧ a * k = 0 := by
  constructor
  · intro hzero
    have h01 : nsCoord0 ≠ nsCoord1 := by decide
    have h02 : nsCoord0 ≠ nsCoord2 := by decide
    have h10 : nsCoord1 ≠ nsCoord0 := by simpa using h01.symm
    have h12 : nsCoord1 ≠ nsCoord2 := by decide
    have h20 : nsCoord2 ≠ nsCoord0 := by simpa using h02.symm
    have h21 : nsCoord2 ≠ nsCoord1 := by simpa using h12.symm
    have hzeroAt0 : heatShearTransportFullDriftInitialVelocity a k b d c 0 = 0 := by
      simpa using congrArg (fun u : NSInitialVelocity => u 0) hzero
    rw [heatShearTransportFullDriftInitialVelocity_apply] at hzeroAt0
    have hd : d = 0 := by
      have hcoord := congrArg (fun v : NSSpace => v nsCoord0) hzeroAt0
      simpa [h01, h02] using hcoord
    have hb : b = 0 := by
      have hcoord := congrArg (fun v : NSSpace => v nsCoord1) hzeroAt0
      simpa [h10, h12] using hcoord
    have hc : c = 0 := by
      have hcoord := congrArg (fun v : NSSpace => v nsCoord2) hzeroAt0
      simpa [h20, h21] using hcoord
    have hak : a * k = 0 := by
      by_cases hk : k = 0
      · simp [hk]
      · let x1 : NSSpace := EuclideanSpace.single nsCoord1 ((Real.pi / 2) / k)
        have hzeroAtx1 : heatShearTransportFullDriftInitialVelocity a k b d c x1 = 0 := by
          simpa using congrArg (fun u : NSInitialVelocity => u x1) hzero
        have hx1coord : x1 nsCoord1 = (Real.pi / 2) / k := by
          simp [x1, nsCoord1]
        have hkpi : k * ((Real.pi / 2) / k) = Real.pi / 2 := by
          field_simp [hk]
        have hcoord := congrArg (fun v : NSSpace => v nsCoord0) hzeroAtx1
        have ha : a = 0 := by
          simpa [heatShearTransportFullDriftInitialVelocity_apply, x1, hx1coord, hkpi,
            Real.sin_pi_div_two, hd, h01, h02] using hcoord
        simp [ha]
    exact ⟨hb, hd, hc, hak⟩
  · rintro ⟨rfl, rfl, rfl, hak⟩
    rcases mul_eq_zero.mp hak with ha | hk
    · simpa [heatShearTransportFullDriftInitialVelocity_zero_transport,
        heatShearFullDriftInitialVelocity_zero_drifts, ha] using
        heatShearInitialVelocity_zero_of_amplitude_zero k
    · simpa [heatShearTransportFullDriftInitialVelocity_zero_transport,
        heatShearFullDriftInitialVelocity_zero_drifts, hk] using
        heatShearInitialVelocity_zero_of_wavenumber_zero a

/-- The transported heat-shear subfamily is zero exactly when the transport
speed vanishes and the oscillatory slice is degenerate. -/
theorem heatShearTransportInitialVelocity_eq_zero_iff
    {a k b : ℝ} :
    heatShearTransportInitialVelocity a k b = (0 : NSInitialVelocity) ↔
      b = 0 ∧ a * k = 0 := by
  simpa [heatShearTransportFullDriftInitialVelocity_zero_drifts] using
    (heatShearTransportFullDriftInitialVelocity_eq_zero_iff
      (a := a) (k := k) (b := b) (d := 0) (c := 0))

/-- Any nonzero transported full-drift heat-shear datum is excluded from the
Schwartz initial-data lane by streamwise translation invariance. -/
theorem not_exists_schwartzInitialVelocity_eq_heatShearTransportFullDriftInitialVelocity_of_ne_zero
    {a k b d c : ℝ}
    (hnez : heatShearTransportFullDriftInitialVelocity a k b d c ≠ (0 : NSInitialVelocity)) :
    ¬ ∃ u₀ : NSSchwartzInitialVelocity,
        (u₀ : NSInitialVelocity) = heatShearTransportFullDriftInitialVelocity a k b d c := by
  intro h
  rcases h with ⟨u₀, hu₀⟩
  have hinv :
      TranslationInvariantAlong heatShearStreamwiseDirection
        (u₀ : NSInitialVelocity) := by
    simpa [hu₀] using
      translationInvariantAlong_heatShearTransportFullDriftInitialVelocity_streamwise a k b d c
  have huzero : (u₀ : NSInitialVelocity) = 0 := by
    exact
      schwartzInitialVelocity_eq_zero_of_translationInvariantAlong u₀
        heatShearStreamwiseDirection_ne_zero hinv
  have htransportzero :
      heatShearTransportFullDriftInitialVelocity a k b d c = (0 : NSInitialVelocity) := by
    simpa [hu₀] using huzero
  exact hnez htransportzero

/-- Therefore every transported full-drift heat-shear datum with either a
nonzero drift component or nondegenerate oscillatory part is excluded from the
Schwartz lane. -/
theorem not_exists_schwartzInitialVelocity_eq_heatShearTransportFullDriftInitialVelocity_of_nonzero_transport_or_streamwiseDrift_or_verticalDrift_or_amplitude_mul_wavenumber_ne_zero
    {a k b d c : ℝ}
    (hparam : b ≠ 0 ∨ d ≠ 0 ∨ c ≠ 0 ∨ a * k ≠ 0) :
    ¬ ∃ u₀ : NSSchwartzInitialVelocity,
        (u₀ : NSInitialVelocity) = heatShearTransportFullDriftInitialVelocity a k b d c := by
  apply not_exists_schwartzInitialVelocity_eq_heatShearTransportFullDriftInitialVelocity_of_ne_zero
  intro hzero
  have hdeg :
      b = 0 ∧ d = 0 ∧ c = 0 ∧ a * k = 0 :=
    (heatShearTransportFullDriftInitialVelocity_eq_zero_iff (a := a) (k := k)
      (b := b) (d := d) (c := c)).mp hzero
  rcases hdeg with ⟨hb, hd, hc, hak⟩
  rcases hparam with hbne | hdne | hcne | hakne
  · exact hbne hb
  · exact hdne hd
  · exact hcne hc
  · exact hakne hak

/-- The transported heat-shear subfamily is likewise excluded from the Schwartz
lane whenever either the transport speed is nonzero or the oscillatory profile
is nondegenerate. -/
theorem not_exists_schwartzInitialVelocity_eq_heatShearTransportInitialVelocity_of_transport_ne_zero_or_amplitude_mul_wavenumber_ne_zero
    {a k b : ℝ}
    (hparam : b ≠ 0 ∨ a * k ≠ 0) :
    ¬ ∃ u₀ : NSSchwartzInitialVelocity,
        (u₀ : NSInitialVelocity) = heatShearTransportInitialVelocity a k b := by
  intro h
  rcases h with ⟨u₀, hu₀⟩
  have hfull :
      ¬ ∃ v₀ : NSSchwartzInitialVelocity,
          (v₀ : NSInitialVelocity) = heatShearTransportFullDriftInitialVelocity a k b 0 0 := by
    exact
      not_exists_schwartzInitialVelocity_eq_heatShearTransportFullDriftInitialVelocity_of_nonzero_transport_or_streamwiseDrift_or_verticalDrift_or_amplitude_mul_wavenumber_ne_zero
        (a := a) (k := k) (b := b) (d := 0) (c := 0)
        (by
          rcases hparam with hb | hak
          · exact Or.inl hb
          · exact Or.inr <| Or.inr <| Or.inr hak)
  exact hfull ⟨u₀, by simpa [heatShearTransportFullDriftInitialVelocity_zero_drifts] using hu₀⟩

end NavierStokes
end FluidDynamics
end Mettapedia
