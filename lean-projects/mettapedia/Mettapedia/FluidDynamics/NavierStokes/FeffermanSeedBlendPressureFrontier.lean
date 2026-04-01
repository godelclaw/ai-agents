import Mettapedia.FluidDynamics.NavierStokes.FeffermanScaledPressureSeededFrontier

/-!
# Seed-Blend Pressure-Seeded Frontier

This file pushes one step beyond pure scalar rescaling.  The candidate velocity
is an affine blend of the live tendril and its seeded slice:

* a time-varying part `a * ω(t,x)`;
* a frozen seeded part `b * ω(1,x)`.

Pressure remains identically zero.  This keeps the target-side certificates
explicit while moving the compatibility mouth closer to a manuscript-shaped
descendant route.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section SeedBlendPressureFrontier

variable {Time X ι G : Type*}
variable [Fintype ι] [One Time] [Mul Time]
variable {radius statistic : G → ℝ}

/-- Initial slice of the seed-blend candidate at base time `1`. -/
def UniformVorticityTendril.seedBlendInitialSlice
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (a b : ℝ) : X → ℝ :=
  fun x => (a + b) * T.vorticity 1 x

/-- A more manuscript-shaped non-self candidate: live tendril plus frozen seed
slice, with zero pressure. -/
def UniformVorticityTendril.seedBlendCandidate
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (a b : ℝ) : VelocityPressureCandidate (Time := Time) (X := X) where
  velocity := fun t x => a * T.vorticity t x + b * T.vorticity 1 x
  pressure := fun _ _ => 0

theorem UniformVorticityTendril.seedBlendCandidate_zeroPressure
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (a b : ℝ) :
    ZeroPressure (T.seedBlendCandidate a b).pressure := by
  intro t x
  rfl

theorem UniformVorticityTendril.seedBlendCandidate_matches_initialSlice
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (a b : ℝ) :
    MatchesInitialSlice (T.seedBlendInitialSlice a b) (T.seedBlendCandidate a b).velocity := by
  intro x
  change a * T.vorticity 1 x + b * T.vorticity 1 x = (a + b) * T.vorticity 1 x
  ring

/-- Compatibility notion for the affine seed-blend descendant route. -/
def seedBlendCompatibilityPred (a b : ℝ) :
    VorticityCompatibilityPred (Time := Time) (X := X) :=
  fun T u => ∀ t x, u t x = a * T.vorticity t x + b * T.vorticity 1 x

theorem UniformVorticityTendril.seedBlendCandidate_has_seedBlendCompatibility
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (a b : ℝ) :
    seedBlendCompatibilityPred (Time := Time) (X := X) a b T
      (T.seedBlendCandidate a b).velocity := by
  intro t x
  rfl

/-- Regularity for the blended candidate is still controlled by the tendril
envelope. -/
def UniformVorticityTendril.seedBlendPressureSeededRegularityCertificate
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (a b : ℝ) :
    RegularityCertificate
      (pressureSeededPredicateKit (Time := Time) (X := X) (T.seedBlendInitialSlice a b))
      (T.seedBlendCandidate a b) where
  smooth_velocity := by
    refine ⟨(|a| + |b|) * T.envelope, ?_, ?_⟩
    · exact mul_nonneg (add_nonneg (abs_nonneg a) (abs_nonneg b)) T.envelope_nonneg
    · intro t x
      calc
        |(T.seedBlendCandidate a b).velocity t x|
            = |a * T.vorticity t x + b * T.vorticity 1 x| := rfl
        _ ≤ |a * T.vorticity t x| + |b * T.vorticity 1 x| := abs_add_le _ _
        _ = |a| * |T.vorticity t x| + |b| * |T.vorticity 1 x| := by
          rw [abs_mul, abs_mul]
        _ ≤ |a| * T.envelope + |b| * T.envelope := by
          gcongr
          · exact T.abs_vorticity_le t x
          · exact T.abs_vorticity_le 1 x
        _ = (|a| + |b|) * T.envelope := by ring
  smooth_pressure := UniformVorticityTendril.seedBlendCandidate_zeroPressure T a b

/-- The pressure and initial-slice dynamics slots remain explicit. -/
def UniformVorticityTendril.seedBlendPressureSeededDynamicsCertificate
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (a b : ℝ) :
    DynamicsCertificate
      (pressureSeededPredicateKit (Time := Time) (X := X) (T.seedBlendInitialSlice a b))
      (T.seedBlendCandidate a b) where
  momentum_equation := UniformVorticityTendril.seedBlendCandidate_zeroPressure T a b
  incompressible := trivial
  initial_condition := T.seedBlendCandidate_matches_initialSlice a b

/-- The energy-side bound is the same envelope estimate. -/
def UniformVorticityTendril.seedBlendPressureSeededEnergyCertificate
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (a b : ℝ) :
    EnergyCertificate
      (pressureSeededPredicateKit (Time := Time) (X := X) (T.seedBlendInitialSlice a b))
      (T.seedBlendCandidate a b) where
  bounded_energy := by
    refine ⟨(|a| + |b|) * T.envelope, ?_, ?_⟩
    · exact mul_nonneg (add_nonneg (abs_nonneg a) (abs_nonneg b)) T.envelope_nonneg
    · intro t x
      calc
        |(T.seedBlendCandidate a b).velocity t x|
            = |a * T.vorticity t x + b * T.vorticity 1 x| := rfl
        _ ≤ |a * T.vorticity t x| + |b * T.vorticity 1 x| := abs_add_le _ _
        _ = |a| * |T.vorticity t x| + |b| * |T.vorticity 1 x| := by
          rw [abs_mul, abs_mul]
        _ ≤ |a| * T.envelope + |b| * T.envelope := by
          gcongr
          · exact T.abs_vorticity_le t x
          · exact T.abs_vorticity_le 1 x
        _ = (|a| + |b|) * T.envelope := by ring

/-- The first affine seed-blend almost-bridge. -/
def UniformVorticityTendril.toSeedBlendPressureSeededAlmostBridge
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (a b : ℝ) :
    AlmostFeffermanBridge
      (K := pressureSeededPredicateKit
        (Time := Time) (X := X) (T.seedBlendInitialSlice a b)) T where
  candidate := T.seedBlendCandidate a b
  regularity := T.seedBlendPressureSeededRegularityCertificate a b
  dynamics := T.seedBlendPressureSeededDynamicsCertificate a b
  energy := T.seedBlendPressureSeededEnergyCertificate a b

/-- Same-route version: all certificates are present and compatibility is the
remaining mouth. -/
theorem UniformVorticityTendril.realizes_pressure_seeded_clause_of_seedBlendSelfCompatibility
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (a b : ℝ)
    (hcompat : selfCompatibility (Time := Time) (X := X)
      T (T.seedBlendCandidate a b).velocity) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X)
      (pressureSeededPredicateKit (Time := Time) (X := X) (T.seedBlendInitialSlice a b)) :=
  (T.toSeedBlendPressureSeededAlmostBridge a b).realizes_clause_of_compatibility hcompat

/-- Descendant-route closure with the affine seed-blend compatibility notion. -/
def UniformVorticityTendril.toSeedBlendPressureSeededBridge
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (a b : ℝ) :
    TopDownFeffermanBridge
      (pressureSeededPredicateKit (Time := Time) (X := X) (T.seedBlendInitialSlice a b))
      (seedBlendCompatibilityPred (Time := Time) (X := X) a b) T :=
  (T.toSeedBlendPressureSeededAlmostBridge a b).toTopDownBridge
    (T.seedBlendCandidate_has_seedBlendCompatibility a b)

theorem UniformVorticityTendril.realizes_seedBlend_pressure_seeded_clause
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (a b : ℝ) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X)
      (pressureSeededPredicateKit (Time := Time) (X := X) (T.seedBlendInitialSlice a b)) :=
  (T.toSeedBlendPressureSeededBridge a b).realizes_clause

/-- Special closure: `(a,b)=(1,0)` recovers the same-route self candidate. -/
theorem UniformVorticityTendril.seedBlendCandidate_has_selfCompatibility_of_one_zero
    (T : UniformVorticityTendril (Time := Time) (X := X)) :
    selfCompatibility (Time := Time) (X := X)
      T (T.seedBlendCandidate (1 : ℝ) 0).velocity := by
  intro t x
  simp [UniformVorticityTendril.seedBlendCandidate]

/-- Special closure: zero vorticity makes the same-route mouth collapse for any
affine blend. -/
theorem UniformVorticityTendril.seedBlendCandidate_has_selfCompatibility_of_zero
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (a b : ℝ)
    (hzero : ∀ t x, T.vorticity t x = 0) :
    selfCompatibility (Time := Time) (X := X)
      T (T.seedBlendCandidate a b).velocity := by
  intro t x
  simp [UniformVorticityTendril.seedBlendCandidate, hzero t x, hzero 1 x]

end SeedBlendPressureFrontier

end NavierStokes
end FluidDynamics
end Mettapedia
