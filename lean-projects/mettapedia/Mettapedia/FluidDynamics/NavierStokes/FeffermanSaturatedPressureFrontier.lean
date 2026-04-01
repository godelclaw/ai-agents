import Mettapedia.FluidDynamics.NavierStokes.FeffermanSeedBlendPressureFrontier

/-!
# Saturated Pressure-Seeded Frontier

This file introduces a nonlinear non-self candidate for the top-down NS ladder.
The candidate velocity is a saturated profile of the current tendril:

`u(t,x) = a * (ω(t,x) / (1 + |ω(t,x)|))`.

Pressure remains identically zero.  This keeps all target-side certificates
explicit while moving one step closer to a soft-cutoff style descendant route.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section SaturatedPressureFrontier

variable {Time X ι G : Type*}
variable [Fintype ι] [One Time] [Mul Time]
variable {radius statistic : G → ℝ}

/-- Initial slice of the saturated candidate at base time `1`. -/
def UniformVorticityTendril.saturatedInitialSlice
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (a : ℝ) : X → ℝ :=
  fun x => a * (T.vorticity 1 x / (1 + |T.vorticity 1 x|))

/-- A nonlinear non-self candidate: a saturated profile of the current
vorticity tendril, with zero pressure. -/
def UniformVorticityTendril.saturatedCandidate
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (a : ℝ) : VelocityPressureCandidate (Time := Time) (X := X) where
  velocity := fun t x => a * (T.vorticity t x / (1 + |T.vorticity t x|))
  pressure := fun _ _ => 0

theorem UniformVorticityTendril.saturatedCandidate_zeroPressure
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (a : ℝ) :
    ZeroPressure (T.saturatedCandidate a).pressure := by
  intro t x
  rfl

theorem UniformVorticityTendril.saturatedCandidate_matches_initialSlice
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (a : ℝ) :
    MatchesInitialSlice (T.saturatedInitialSlice a) (T.saturatedCandidate a).velocity := by
  intro x
  rfl

/-- Compatibility notion for the saturated descendant route. -/
def saturatedCompatibilityPred (a : ℝ) :
    VorticityCompatibilityPred (Time := Time) (X := X) :=
  fun T u => ∀ t x, u t x = a * (T.vorticity t x / (1 + |T.vorticity t x|))

theorem UniformVorticityTendril.saturatedCandidate_has_saturatedCompatibility
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (a : ℝ) :
    saturatedCompatibilityPred (Time := Time) (X := X) a T (T.saturatedCandidate a).velocity := by
  intro t x
  rfl

/-- The saturated profile is uniformly bounded by the original tendril
envelope. -/
theorem UniformVorticityTendril.saturated_abs_le
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (a : ℝ) (t : Time) (x : X) :
    |(T.saturatedCandidate a).velocity t x| ≤ |a| * T.envelope := by
  have hden_nonneg : 0 ≤ 1 + |T.vorticity t x| := by positivity
  have hfrac : |T.vorticity t x| / (1 + |T.vorticity t x|) ≤ |T.vorticity t x| := by
    have hone : 1 ≤ 1 + |T.vorticity t x| := by
      simpa using le_add_of_nonneg_right (abs_nonneg (T.vorticity t x))
    exact div_le_self (abs_nonneg _) hone
  calc
    |(T.saturatedCandidate a).velocity t x|
        = |a * (T.vorticity t x / (1 + |T.vorticity t x|))| := rfl
    _ = |a| * |T.vorticity t x / (1 + |T.vorticity t x|)| := by rw [abs_mul]
    _ = |a| * (|T.vorticity t x| / (1 + |T.vorticity t x|)) := by
      rw [abs_div, abs_of_nonneg hden_nonneg]
    _ ≤ |a| * |T.vorticity t x| := by
      gcongr
    _ ≤ |a| * T.envelope := by
      exact mul_le_mul_of_nonneg_left (T.abs_vorticity_le t x) (abs_nonneg a)

/-- Regularity for the saturated candidate is still controlled by the original
uniform envelope. -/
def UniformVorticityTendril.saturatedPressureSeededRegularityCertificate
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (a : ℝ) :
    RegularityCertificate
      (pressureSeededPredicateKit (Time := Time) (X := X) (T.saturatedInitialSlice a))
      (T.saturatedCandidate a) where
  smooth_velocity := by
    refine ⟨|a| * T.envelope, mul_nonneg (abs_nonneg a) T.envelope_nonneg, ?_⟩
    intro t x
    exact T.saturated_abs_le a t x
  smooth_pressure := T.saturatedCandidate_zeroPressure a

/-- The pressure and initial-slice dynamics slots remain explicit. -/
def UniformVorticityTendril.saturatedPressureSeededDynamicsCertificate
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (a : ℝ) :
    DynamicsCertificate
      (pressureSeededPredicateKit (Time := Time) (X := X) (T.saturatedInitialSlice a))
      (T.saturatedCandidate a) where
  momentum_equation := T.saturatedCandidate_zeroPressure a
  incompressible := trivial
  initial_condition := T.saturatedCandidate_matches_initialSlice a

/-- The energy-side bound is the same saturated envelope estimate. -/
def UniformVorticityTendril.saturatedPressureSeededEnergyCertificate
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (a : ℝ) :
    EnergyCertificate
      (pressureSeededPredicateKit (Time := Time) (X := X) (T.saturatedInitialSlice a))
      (T.saturatedCandidate a) where
  bounded_energy := by
    refine ⟨|a| * T.envelope, mul_nonneg (abs_nonneg a) T.envelope_nonneg, ?_⟩
    intro t x
    exact T.saturated_abs_le a t x

/-- The first nonlinear saturated almost-bridge. -/
def UniformVorticityTendril.toSaturatedPressureSeededAlmostBridge
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (a : ℝ) :
    AlmostFeffermanBridge
      (K := pressureSeededPredicateKit
        (Time := Time) (X := X) (T.saturatedInitialSlice a)) T where
  candidate := T.saturatedCandidate a
  regularity := T.saturatedPressureSeededRegularityCertificate a
  dynamics := T.saturatedPressureSeededDynamicsCertificate a
  energy := T.saturatedPressureSeededEnergyCertificate a

/-- Same-route version: all certificates are present and compatibility is the
remaining mouth. -/
theorem UniformVorticityTendril.realizes_pressure_seeded_clause_of_saturatedSelfCompatibility
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (a : ℝ)
    (hcompat : selfCompatibility (Time := Time) (X := X)
      T (T.saturatedCandidate a).velocity) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X)
      (pressureSeededPredicateKit (Time := Time) (X := X) (T.saturatedInitialSlice a)) :=
  (T.toSaturatedPressureSeededAlmostBridge a).realizes_clause_of_compatibility hcompat

/-- Descendant-route closure with the saturated compatibility notion. -/
def UniformVorticityTendril.toSaturatedPressureSeededBridge
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (a : ℝ) :
    TopDownFeffermanBridge
      (pressureSeededPredicateKit (Time := Time) (X := X) (T.saturatedInitialSlice a))
      (saturatedCompatibilityPred (Time := Time) (X := X) a) T :=
  (T.toSaturatedPressureSeededAlmostBridge a).toTopDownBridge
    (T.saturatedCandidate_has_saturatedCompatibility a)

theorem UniformVorticityTendril.realizes_saturated_pressure_seeded_clause
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (a : ℝ) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X)
      (pressureSeededPredicateKit (Time := Time) (X := X) (T.saturatedInitialSlice a)) :=
  (T.toSaturatedPressureSeededBridge a).realizes_clause

/-- Zero vorticity collapses the same-route mouth for any saturated scaling. -/
theorem UniformVorticityTendril.saturatedCandidate_has_selfCompatibility_of_zero
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (a : ℝ)
    (hzero : ∀ t x, T.vorticity t x = 0) :
    selfCompatibility (Time := Time) (X := X)
      T (T.saturatedCandidate a).velocity := by
  intro t x
  simp [UniformVorticityTendril.saturatedCandidate, hzero t x]

end SaturatedPressureFrontier

end NavierStokes
end FluidDynamics
end Mettapedia
