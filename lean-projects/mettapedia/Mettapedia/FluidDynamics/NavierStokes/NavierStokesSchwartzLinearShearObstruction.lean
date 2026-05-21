import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSchwartzDirectionalRigidity
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3

/-!
# Schwartz Obstruction for Affine Linear Shear Data

This file blocks the affine linear-shear family

`x ↦ (a * x₁, b, c)`

from the Schwartz initial-data lane on `ℝ^3`, except in the trivial zero-data
case.

As with the heat-shear files, the obstruction is completely concrete and
bottom-up: these initial data are translation invariant along the streamwise
`x₀` direction, so any Schwartz realization would have to vanish identically.
An explicit zero classification then isolates the exact degenerate parameter
case.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

/-- The streamwise basis direction `e₀` used for the linear-shear obstruction. -/
def linearShearStreamwiseDirection : NSSpace :=
  EuclideanSpace.single nsCoord0 (1 : ℝ)

theorem linearShearStreamwiseDirection_ne_zero :
    linearShearStreamwiseDirection ≠ 0 := by
  intro h
  have hcoord := congrArg (fun x : NSSpace => x nsCoord0) h
  simp [linearShearStreamwiseDirection, nsCoord0] at hcoord

/-- Affine linear-shear full-drift data depend only on `x₁`, so they are
invariant under translation in the streamwise `x₀` direction. -/
theorem translationInvariantAlong_linearShearFullDriftInitialVelocity_streamwise
    (a b c : ℝ) :
    TranslationInvariantAlong linearShearStreamwiseDirection
      (linearShearFullDriftInitialVelocity a b c) := by
  intro x s
  rw [linearShearFullDriftInitialVelocity_apply, linearShearFullDriftInitialVelocity_apply]
  ext i
  fin_cases i <;>
    simp [linearShearStreamwiseDirection, nsCoord0, nsCoord1, nsCoord2,
      add_left_comm, add_comm]

/-- The affine full-drift linear-shear datum is zero exactly when all three
parameters vanish. -/
theorem linearShearFullDriftInitialVelocity_eq_zero_iff
    {a b c : ℝ} :
    linearShearFullDriftInitialVelocity a b c = (0 : NSInitialVelocity) ↔
      a = 0 ∧ b = 0 ∧ c = 0 := by
  constructor
  · intro hzero
    have h01 : nsCoord0 ≠ nsCoord1 := by decide
    have h02 : nsCoord0 ≠ nsCoord2 := by decide
    have h10 : nsCoord1 ≠ nsCoord0 := by simpa using h01.symm
    have h12 : nsCoord1 ≠ nsCoord2 := by decide
    have h20 : nsCoord2 ≠ nsCoord0 := by simpa using h02.symm
    have h21 : nsCoord2 ≠ nsCoord1 := by simpa using h12.symm
    have hzeroAt0 : linearShearFullDriftInitialVelocity a b c 0 = 0 := by
      simpa using congrArg (fun u : NSInitialVelocity => u 0) hzero
    rw [linearShearFullDriftInitialVelocity_apply] at hzeroAt0
    have hb : b = 0 := by
      have hcoord := congrArg (fun v : NSSpace => v nsCoord1) hzeroAt0
      simpa [h10, h12] using hcoord
    have hc : c = 0 := by
      have hcoord := congrArg (fun v : NSSpace => v nsCoord2) hzeroAt0
      simpa [h20, h21] using hcoord
    let x1 : NSSpace := EuclideanSpace.single nsCoord1 (1 : ℝ)
    have hzeroAtx1 : linearShearFullDriftInitialVelocity a b c x1 = 0 := by
      simpa using congrArg (fun u : NSInitialVelocity => u x1) hzero
    have hx1coord : x1 nsCoord1 = 1 := by
      simp [x1, nsCoord1]
    have ha : a = 0 := by
      have hcoord := congrArg (fun v : NSSpace => v nsCoord0) hzeroAtx1
      simpa [linearShearFullDriftInitialVelocity_apply, x1, hx1coord, hb, h01, h02] using hcoord
    exact ⟨ha, hb, hc⟩
  · rintro ⟨rfl, rfl, rfl⟩
    funext x
    ext i
    fin_cases i <;>
      simp [linearShearFullDriftInitialVelocity_apply, nsCoord0, nsCoord1, nsCoord2]

/-- Base linear shear is zero exactly when its shear coefficient vanishes. -/
theorem linearShearInitialVelocity_eq_zero_iff
    {a : ℝ} :
    linearShearInitialVelocity a = (0 : NSInitialVelocity) ↔
      a = 0 := by
  simpa [linearShearFullDriftInitialVelocity_zero_drifts] using
    (linearShearFullDriftInitialVelocity_eq_zero_iff (a := a) (b := 0) (c := 0))

/-- Vertical-drift affine linear shear is zero exactly when both parameters
vanish. -/
theorem linearShearVerticalDriftInitialVelocity_eq_zero_iff
    {a c : ℝ} :
    linearShearVerticalDriftInitialVelocity a c = (0 : NSInitialVelocity) ↔
      a = 0 ∧ c = 0 := by
  simpa [linearShearFullDriftInitialVelocity_zero_horizontalDrift] using
    (linearShearFullDriftInitialVelocity_eq_zero_iff (a := a) (b := 0) (c := c))

/-- Horizontal-drift affine linear shear is zero exactly when both parameters
vanish. -/
theorem linearShearHorizontalDriftInitialVelocity_eq_zero_iff
    {a b : ℝ} :
    linearShearHorizontalDriftInitialVelocity a b = (0 : NSInitialVelocity) ↔
      a = 0 ∧ b = 0 := by
  simpa [linearShearFullDriftInitialVelocity_zero_verticalDrift] using
    (linearShearFullDriftInitialVelocity_eq_zero_iff (a := a) (b := b) (c := 0))

/-- Any nonzero affine full-drift linear-shear datum is excluded from the
Schwartz lane by streamwise translation invariance. -/
theorem not_exists_schwartzInitialVelocity_eq_linearShearFullDriftInitialVelocity_of_ne_zero
    {a b c : ℝ}
    (hnez : linearShearFullDriftInitialVelocity a b c ≠ (0 : NSInitialVelocity)) :
    ¬ ∃ u₀ : NSSchwartzInitialVelocity,
        (u₀ : NSInitialVelocity) = linearShearFullDriftInitialVelocity a b c := by
  intro h
  rcases h with ⟨u₀, hu₀⟩
  have hinv :
      TranslationInvariantAlong linearShearStreamwiseDirection
        (u₀ : NSInitialVelocity) := by
    simpa [hu₀] using
      translationInvariantAlong_linearShearFullDriftInitialVelocity_streamwise a b c
  have huzero : (u₀ : NSInitialVelocity) = 0 := by
    exact
      schwartzInitialVelocity_eq_zero_of_translationInvariantAlong u₀
        linearShearStreamwiseDirection_ne_zero hinv
  have hshearzero :
      linearShearFullDriftInitialVelocity a b c = (0 : NSInitialVelocity) := by
    simpa [hu₀] using huzero
  exact hnez hshearzero

/-- Therefore every nontrivial affine linear-shear full-drift datum is blocked
from the Schwartz initial-data lane. -/
theorem not_exists_schwartzInitialVelocity_eq_linearShearFullDriftInitialVelocity_of_parameter_ne_zero
    {a b c : ℝ}
    (hparam : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) :
    ¬ ∃ u₀ : NSSchwartzInitialVelocity,
        (u₀ : NSInitialVelocity) = linearShearFullDriftInitialVelocity a b c := by
  apply not_exists_schwartzInitialVelocity_eq_linearShearFullDriftInitialVelocity_of_ne_zero
  intro hzero
  have hdeg :
      a = 0 ∧ b = 0 ∧ c = 0 :=
    (linearShearFullDriftInitialVelocity_eq_zero_iff (a := a) (b := b) (c := c)).mp hzero
  rcases hdeg with ⟨ha, hb, hc⟩
  rcases hparam with ha' | hb' | hc'
  · exact ha' ha
  · exact hb' hb
  · exact hc' hc

/-- Base linear shear is excluded from the Schwartz lane whenever the shear
coefficient is nonzero. -/
theorem not_exists_schwartzInitialVelocity_eq_linearShearInitialVelocity_of_shear_ne_zero
    {a : ℝ} (ha : a ≠ 0) :
    ¬ ∃ u₀ : NSSchwartzInitialVelocity,
        (u₀ : NSInitialVelocity) = linearShearInitialVelocity a := by
  intro h
  rcases h with ⟨u₀, hu₀⟩
  have hfull :
      ¬ ∃ v₀ : NSSchwartzInitialVelocity,
          (v₀ : NSInitialVelocity) = linearShearFullDriftInitialVelocity a 0 0 := by
    exact
      not_exists_schwartzInitialVelocity_eq_linearShearFullDriftInitialVelocity_of_parameter_ne_zero
        (a := a) (b := 0) (c := 0) (Or.inl ha)
  exact hfull ⟨u₀, by simpa [linearShearFullDriftInitialVelocity_zero_drifts] using hu₀⟩

/-- Vertical-drift affine linear shear is excluded from the Schwartz lane
whenever either parameter is nonzero. -/
theorem not_exists_schwartzInitialVelocity_eq_linearShearVerticalDriftInitialVelocity_of_shear_ne_zero_or_verticalDrift_ne_zero
    {a c : ℝ} (hparam : a ≠ 0 ∨ c ≠ 0) :
    ¬ ∃ u₀ : NSSchwartzInitialVelocity,
        (u₀ : NSInitialVelocity) = linearShearVerticalDriftInitialVelocity a c := by
  intro h
  rcases h with ⟨u₀, hu₀⟩
  have hfull :
      ¬ ∃ v₀ : NSSchwartzInitialVelocity,
          (v₀ : NSInitialVelocity) = linearShearFullDriftInitialVelocity a 0 c := by
    exact
      not_exists_schwartzInitialVelocity_eq_linearShearFullDriftInitialVelocity_of_parameter_ne_zero
        (a := a) (b := 0) (c := c)
        (by
          rcases hparam with ha | hc
          · exact Or.inl ha
          · exact Or.inr <| Or.inr hc)
  exact hfull ⟨u₀, by simpa [linearShearFullDriftInitialVelocity_zero_horizontalDrift] using hu₀⟩

/-- Horizontal-drift affine linear shear is excluded from the Schwartz lane
whenever either parameter is nonzero. -/
theorem not_exists_schwartzInitialVelocity_eq_linearShearHorizontalDriftInitialVelocity_of_shear_ne_zero_or_horizontalDrift_ne_zero
    {a b : ℝ} (hparam : a ≠ 0 ∨ b ≠ 0) :
    ¬ ∃ u₀ : NSSchwartzInitialVelocity,
        (u₀ : NSInitialVelocity) = linearShearHorizontalDriftInitialVelocity a b := by
  intro h
  rcases h with ⟨u₀, hu₀⟩
  have hfull :
      ¬ ∃ v₀ : NSSchwartzInitialVelocity,
          (v₀ : NSInitialVelocity) = linearShearFullDriftInitialVelocity a b 0 := by
    exact
      not_exists_schwartzInitialVelocity_eq_linearShearFullDriftInitialVelocity_of_parameter_ne_zero
        (a := a) (b := b) (c := 0)
        (by
          rcases hparam with ha | hb
          · exact Or.inl ha
          · exact Or.inr <| Or.inl hb)
  exact hfull ⟨u₀, by simpa [linearShearFullDriftInitialVelocity_zero_verticalDrift] using hu₀⟩

end NavierStokes
end FluidDynamics
end Mettapedia
