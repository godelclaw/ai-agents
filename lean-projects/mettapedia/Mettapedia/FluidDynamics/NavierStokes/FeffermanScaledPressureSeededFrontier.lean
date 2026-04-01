import Mettapedia.FluidDynamics.NavierStokes.FeffermanPressureSeededSelfModel

/-!
# Scaled Pressure-Seeded Frontier

This file introduces the first non-self candidate in the top-down NS ladder.
The candidate velocity is a scalar multiple of the current vorticity tendril,
with zero pressure.  This keeps all target-side certificates explicit while
making compatibility with the original vorticity non-tautological.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section ScaledPressureSeededFrontier

variable {Time X ι G : Type*}
variable [Fintype ι] [One Time] [Mul Time]
variable {radius statistic : G → ℝ}

/-- Initial slice of the scalar-rescaled candidate at base time `1`. -/
def UniformVorticityTendril.scaledInitialSlice
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (a : ℝ) : X → ℝ :=
  fun x => a * T.vorticity 1 x

/-- First non-self candidate: rescale the tendril vorticity by a fixed scalar
and keep pressure zero. -/
def UniformVorticityTendril.scaledCandidate
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (a : ℝ) : VelocityPressureCandidate (Time := Time) (X := X) where
  velocity := fun t x => a * T.vorticity t x
  pressure := fun _ _ => 0

omit [One Time] [Mul Time] in
theorem UniformVorticityTendril.scaledCandidate_zeroPressure
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (a : ℝ) :
    ZeroPressure (T.scaledCandidate a).pressure := by
  intro t x
  rfl

omit [Mul Time] in
theorem UniformVorticityTendril.scaledCandidate_matches_initialSlice
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (a : ℝ) :
    MatchesInitialSlice (T.scaledInitialSlice a) (T.scaledCandidate a).velocity := by
  intro x
  rfl

/-- Compatibility notion for the scalar-rescaled descendant route. -/
def scaledCompatibilityPred (a : ℝ) :
    VorticityCompatibilityPred (Time := Time) (X := X) :=
  fun T u => ∀ t x, u t x = a * T.vorticity t x

omit [One Time] [Mul Time] in
theorem UniformVorticityTendril.scaledCandidate_has_scaledCompatibility
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (a : ℝ) :
    scaledCompatibilityPred (Time := Time) (X := X) a T (T.scaledCandidate a).velocity := by
  intro t x
  rfl

/-- Regularity for the rescaled candidate is still controlled by the original
uniform envelope. -/
def UniformVorticityTendril.scaledPressureSeededRegularityCertificate
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (a : ℝ) :
    RegularityCertificate
      (pressureSeededPredicateKit (Time := Time) (X := X) (T.scaledInitialSlice a))
      (T.scaledCandidate a) where
  smooth_velocity := by
    refine ⟨|a| * T.envelope, mul_nonneg (abs_nonneg a) T.envelope_nonneg, ?_⟩
    intro t x
    calc
      |(T.scaledCandidate a).velocity t x|
          = |a * T.vorticity t x| := rfl
      _ = |a| * |T.vorticity t x| := by rw [abs_mul]
      _ ≤ |a| * T.envelope := by
        exact mul_le_mul_of_nonneg_left (T.abs_vorticity_le t x) (abs_nonneg a)
  smooth_pressure := T.scaledCandidate_zeroPressure a

/-- The rescaled candidate still satisfies the pressure and initial-slice
dynamics slots of the strengthened target. -/
def UniformVorticityTendril.scaledPressureSeededDynamicsCertificate
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (a : ℝ) :
    DynamicsCertificate
      (pressureSeededPredicateKit (Time := Time) (X := X) (T.scaledInitialSlice a))
      (T.scaledCandidate a) where
  momentum_equation := T.scaledCandidate_zeroPressure a
  incompressible := trivial
  initial_condition := T.scaledCandidate_matches_initialSlice a

/-- The energy-side bound is the same envelope estimate. -/
def UniformVorticityTendril.scaledPressureSeededEnergyCertificate
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (a : ℝ) :
    EnergyCertificate
      (pressureSeededPredicateKit (Time := Time) (X := X) (T.scaledInitialSlice a))
      (T.scaledCandidate a) where
  bounded_energy := by
    refine ⟨|a| * T.envelope, mul_nonneg (abs_nonneg a) T.envelope_nonneg, ?_⟩
    intro t x
    calc
      |(T.scaledCandidate a).velocity t x|
          = |a * T.vorticity t x| := rfl
      _ = |a| * |T.vorticity t x| := by rw [abs_mul]
      _ ≤ |a| * T.envelope := by
        exact mul_le_mul_of_nonneg_left (T.abs_vorticity_le t x) (abs_nonneg a)

/-- This gives an explicit non-self almost-bridge for the same strengthened
pressure-seeded target. -/
def UniformVorticityTendril.toScaledPressureSeededAlmostBridge
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (a : ℝ) :
    AlmostFeffermanBridge
      (K := pressureSeededPredicateKit
        (Time := Time) (X := X) (T.scaledInitialSlice a)) T where
  candidate := T.scaledCandidate a
  regularity := T.scaledPressureSeededRegularityCertificate a
  dynamics := T.scaledPressureSeededDynamicsCertificate a
  energy := T.scaledPressureSeededEnergyCertificate a

/-- The same-route version stops at the compatibility frontier. -/
theorem UniformVorticityTendril.realizes_pressure_seeded_clause_of_selfCompatibility
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (a : ℝ)
    (hcompat : selfCompatibility (Time := Time) (X := X)
      T (T.scaledCandidate a).velocity) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X)
      (pressureSeededPredicateKit (Time := Time) (X := X) (T.scaledInitialSlice a)) :=
  (T.toScaledPressureSeededAlmostBridge a).realizes_clause_of_compatibility hcompat

/-- The same-route compatibility mouth closes again when the scaling is
trivial. -/
theorem UniformVorticityTendril.scaledCandidate_has_selfCompatibility_of_one
    (T : UniformVorticityTendril (Time := Time) (X := X)) :
    selfCompatibility (Time := Time) (X := X)
      T (T.scaledCandidate (1 : ℝ)).velocity := by
  intro t x
  simp [UniformVorticityTendril.scaledCandidate]

/-- In that trivial-scaling regime the same-route clause closes again. -/
theorem UniformVorticityTendril.realizes_pressure_seeded_clause_of_one
    (T : UniformVorticityTendril (Time := Time) (X := X)) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X)
      (pressureSeededPredicateKit (Time := Time) (X := X)
        (T.scaledInitialSlice (1 : ℝ))) :=
  T.realizes_pressure_seeded_clause_of_selfCompatibility (a := 1)
    T.scaledCandidate_has_selfCompatibility_of_one

/-- The same-route compatibility also closes in the degenerate zero-vorticity
regime, for any scaling factor. -/
theorem UniformVorticityTendril.scaledCandidate_has_selfCompatibility_of_zero
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (a : ℝ)
    (hzero : ∀ t x, T.vorticity t x = 0) :
    selfCompatibility (Time := Time) (X := X)
      T (T.scaledCandidate a).velocity := by
  intro t x
  simp [UniformVorticityTendril.scaledCandidate, hzero t x]

/-- A nearby descendant route with rescaled compatibility closes immediately. -/
def UniformVorticityTendril.toScaledPressureSeededBridge
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (a : ℝ) :
    TopDownFeffermanBridge
      (pressureSeededPredicateKit (Time := Time) (X := X) (T.scaledInitialSlice a))
      (scaledCompatibilityPred (Time := Time) (X := X) a) T :=
  (T.toScaledPressureSeededAlmostBridge a).toTopDownBridge
    (T.scaledCandidate_has_scaledCompatibility a)

theorem UniformVorticityTendril.realizes_scaled_pressure_seeded_clause
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (a : ℝ) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X)
      (pressureSeededPredicateKit (Time := Time) (X := X) (T.scaledInitialSlice a)) :=
  (T.toScaledPressureSeededBridge a).realizes_clause

end ScaledPressureSeededFrontier

end NavierStokes
end FluidDynamics
end Mettapedia
