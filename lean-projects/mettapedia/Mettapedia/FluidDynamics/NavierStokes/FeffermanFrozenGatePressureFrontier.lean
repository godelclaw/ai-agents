import Mettapedia.FluidDynamics.NavierStokes.FeffermanSaturatedPressureFrontier

/-!
# Frozen-Gate Pressure-Seeded Frontier

This file adds a more manuscript-shaped non-self candidate.  The live tendril is
modulated by a gate computed from the frozen seed slice:

`u(t,x) = a * g(ω(1,x)) * ω(t,x)` with `g(s) = |s| / (1 + |s|)`.

Pressure remains identically zero.  This keeps all target-side certificates
explicit while making the descendant route depend on both live and seeded data.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section FrozenGatePressureFrontier

variable {Time X ι G : Type*}
variable [Fintype ι] [One Time] [Mul Time]
variable {radius statistic : G → ℝ}

/-- Frozen seed gate used to modulate the live tendril. -/
def UniformVorticityTendril.seedGate
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (x : X) : ℝ :=
  |T.vorticity 1 x| / (1 + |T.vorticity 1 x|)

/-- Initial slice of the frozen-gate candidate at base time `1`. -/
def UniformVorticityTendril.frozenGateInitialSlice
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (a : ℝ) : X → ℝ :=
  fun x => a * T.seedGate x * T.vorticity 1 x

/-- A seed-gated non-self candidate: the live tendril is multiplied by a gate
computed from the frozen seed slice. -/
def UniformVorticityTendril.frozenGateCandidate
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (a : ℝ) : VelocityPressureCandidate (Time := Time) (X := X) where
  velocity := fun t x => a * T.seedGate x * T.vorticity t x
  pressure := fun _ _ => 0

theorem UniformVorticityTendril.frozenGate_zeroPressure
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (a : ℝ) :
    ZeroPressure (T.frozenGateCandidate a).pressure := by
  intro t x
  rfl

theorem UniformVorticityTendril.frozenGate_matches_initialSlice
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (a : ℝ) :
    MatchesInitialSlice (T.frozenGateInitialSlice a) (T.frozenGateCandidate a).velocity := by
  intro x
  rfl

/-- Compatibility notion for the frozen-gate descendant route. -/
def frozenGateCompatibilityPred (a : ℝ) :
    VorticityCompatibilityPred (Time := Time) (X := X) :=
  fun T u => ∀ t x, u t x = a * T.seedGate x * T.vorticity t x

theorem UniformVorticityTendril.frozenGate_has_frozenGateCompatibility
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (a : ℝ) :
    frozenGateCompatibilityPred (Time := Time) (X := X) a T
      (T.frozenGateCandidate a).velocity := by
  intro t x
  rfl

theorem UniformVorticityTendril.seedGate_nonneg
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (x : X) : 0 ≤ T.seedGate x := by
  unfold UniformVorticityTendril.seedGate
  positivity

theorem UniformVorticityTendril.seedGate_le_one
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (x : X) : T.seedGate x ≤ 1 := by
  unfold UniformVorticityTendril.seedGate
  have hnum_le : |T.vorticity 1 x| ≤ 1 + |T.vorticity 1 x| := by linarith
  exact div_le_one_of_le₀ hnum_le (by positivity)

/-- The frozen-gate candidate is uniformly bounded by the original tendril
envelope. -/
theorem UniformVorticityTendril.frozenGate_abs_le
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (a : ℝ) (t : Time) (x : X) :
    |(T.frozenGateCandidate a).velocity t x| ≤ |a| * T.envelope := by
  have hgate_nonneg := T.seedGate_nonneg x
  have hgate_le_one := T.seedGate_le_one x
  have hgate_mul : T.seedGate x * |T.vorticity t x| ≤ 1 * T.envelope := by
    calc
      T.seedGate x * |T.vorticity t x| ≤ 1 * |T.vorticity t x| := by
        exact mul_le_mul_of_nonneg_right hgate_le_one (abs_nonneg _)
      _ ≤ 1 * T.envelope := by
        exact mul_le_mul_of_nonneg_left (T.abs_vorticity_le t x) zero_le_one
  calc
    |(T.frozenGateCandidate a).velocity t x|
        = |a * T.seedGate x * T.vorticity t x| := rfl
    _ = |a| * (T.seedGate x * |T.vorticity t x|) := by
      rw [mul_assoc, abs_mul, abs_mul, abs_of_nonneg hgate_nonneg]
    _ ≤ |a| * (1 * T.envelope) := by
      exact mul_le_mul_of_nonneg_left hgate_mul (abs_nonneg a)
    _ = |a| * T.envelope := by ring

/-- Regularity for the frozen-gate candidate is still controlled by the tendril
envelope. -/
def UniformVorticityTendril.frozenGateRegularityCertificate
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (a : ℝ) :
    RegularityCertificate
      (pressureSeededPredicateKit (Time := Time) (X := X) (T.frozenGateInitialSlice a))
      (T.frozenGateCandidate a) where
  smooth_velocity := by
    refine ⟨|a| * T.envelope, mul_nonneg (abs_nonneg a) T.envelope_nonneg, ?_⟩
    intro t x
    exact T.frozenGate_abs_le a t x
  smooth_pressure := T.frozenGate_zeroPressure a

/-- The pressure and initial-slice dynamics slots remain explicit. -/
def UniformVorticityTendril.frozenGateDynamicsCertificate
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (a : ℝ) :
    DynamicsCertificate
      (pressureSeededPredicateKit (Time := Time) (X := X) (T.frozenGateInitialSlice a))
      (T.frozenGateCandidate a) where
  momentum_equation := T.frozenGate_zeroPressure a
  incompressible := trivial
  initial_condition := T.frozenGate_matches_initialSlice a

/-- The energy-side bound is the same frozen-gate envelope estimate. -/
def UniformVorticityTendril.frozenGateEnergyCertificate
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (a : ℝ) :
    EnergyCertificate
      (pressureSeededPredicateKit (Time := Time) (X := X) (T.frozenGateInitialSlice a))
      (T.frozenGateCandidate a) where
  bounded_energy := by
    refine ⟨|a| * T.envelope, mul_nonneg (abs_nonneg a) T.envelope_nonneg, ?_⟩
    intro t x
    exact T.frozenGate_abs_le a t x

/-- The first frozen-seed-gated almost-bridge. -/
def UniformVorticityTendril.toFrozenGateAlmostBridge
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (a : ℝ) :
    AlmostFeffermanBridge
      (K := pressureSeededPredicateKit
        (Time := Time) (X := X) (T.frozenGateInitialSlice a)) T where
  candidate := T.frozenGateCandidate a
  regularity := T.frozenGateRegularityCertificate a
  dynamics := T.frozenGateDynamicsCertificate a
  energy := T.frozenGateEnergyCertificate a

/-- Same-route version: all certificates are present and compatibility is the
remaining mouth. -/
theorem UniformVorticityTendril.realizes_pressure_seeded_clause_of_frozenGateSelfCompatibility
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (a : ℝ)
    (hcompat : selfCompatibility (Time := Time) (X := X)
      T (T.frozenGateCandidate a).velocity) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X)
      (pressureSeededPredicateKit (Time := Time) (X := X) (T.frozenGateInitialSlice a)) :=
  (T.toFrozenGateAlmostBridge a).realizes_clause_of_compatibility hcompat

/-- Descendant-route closure with the frozen-gate compatibility notion. -/
def UniformVorticityTendril.toFrozenGateBridge
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (a : ℝ) :
    TopDownFeffermanBridge
      (pressureSeededPredicateKit (Time := Time) (X := X) (T.frozenGateInitialSlice a))
      (frozenGateCompatibilityPred (Time := Time) (X := X) a) T :=
  (T.toFrozenGateAlmostBridge a).toTopDownBridge
    (T.frozenGate_has_frozenGateCompatibility a)

theorem UniformVorticityTendril.realizes_frozenGate_pressure_seeded_clause
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (a : ℝ) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X)
      (pressureSeededPredicateKit (Time := Time) (X := X) (T.frozenGateInitialSlice a)) :=
  (T.toFrozenGateBridge a).realizes_clause

/-- Zero vorticity collapses the same-route mouth for any frozen-gate scaling. -/
theorem UniformVorticityTendril.frozenGate_has_selfCompatibility_of_zero
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (a : ℝ)
    (hzero : ∀ t x, T.vorticity t x = 0) :
    selfCompatibility (Time := Time) (X := X)
      T (T.frozenGateCandidate a).velocity := by
  intro t x
  simp [UniformVorticityTendril.frozenGateCandidate, UniformVorticityTendril.seedGate, hzero t x,
    hzero 1 x]

end FrozenGatePressureFrontier

end NavierStokes
end FluidDynamics
end Mettapedia
