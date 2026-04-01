import Mettapedia.FluidDynamics.NavierStokes.FeffermanFrozenGatePressureFrontier

/-!
# Seed/Live Profile Pressure-Seeded Frontier

This file packages a reusable family of non-self top-down candidates.  A
profile `Φ(seed, live)` is allowed as soon as it satisfies a simple absolute
bound by `coeff * (|seed| + |live|)`.  That is enough to carry the whole
pressure-seeded target through to the compatibility frontier.

The existing scalar-rescaled, affine seed-blend, nonlinear saturated, and
frozen-seed-gated frontiers are then recovered as concrete instances of this
generic shell.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section SeedLiveProfileFrontier

variable {Time X ι G : Type*}
variable [Fintype ι] [One Time] [Mul Time]
variable {radius statistic : G → ℝ}

/-- Pointwise seed/live profile with a uniform absolute bound. -/
structure SeedLiveProfile where
  profile : ℝ → ℝ → ℝ
  coeff : ℝ
  coeff_nonneg : 0 ≤ coeff
  bound : ∀ seed live, |profile seed live| ≤ coeff * (|seed| + |live|)

/-- Initial slice induced by a seed/live profile. -/
def UniformVorticityTendril.seedLiveInitialSlice
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (P : SeedLiveProfile) : X → ℝ :=
  fun x => P.profile (T.vorticity 1 x) (T.vorticity 1 x)

/-- Candidate velocity/pressure fields induced by a seed/live profile. -/
def UniformVorticityTendril.seedLiveCandidate
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (P : SeedLiveProfile) :
    VelocityPressureCandidate (Time := Time) (X := X) where
  velocity := fun t x => P.profile (T.vorticity 1 x) (T.vorticity t x)
  pressure := fun _ _ => 0

/-- Exact compatibility notion for the generic seed/live descendant route. -/
def seedLiveCompatibilityPred (P : SeedLiveProfile) :
    VorticityCompatibilityPred (Time := Time) (X := X) :=
  fun T u => ∀ t x, u t x = P.profile (T.vorticity 1 x) (T.vorticity t x)

omit [Mul Time] in
theorem UniformVorticityTendril.seedLiveCandidate_zeroPressure
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (P : SeedLiveProfile) :
    ZeroPressure (T.seedLiveCandidate P).pressure := by
  intro t x
  rfl

omit [Mul Time] in
theorem UniformVorticityTendril.seedLiveCandidate_matches_initialSlice
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (P : SeedLiveProfile) :
    MatchesInitialSlice (T.seedLiveInitialSlice P) (T.seedLiveCandidate P).velocity := by
  intro x
  rfl

omit [Mul Time] in
theorem UniformVorticityTendril.seedLiveCandidate_has_seedLiveCompatibility
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (P : SeedLiveProfile) :
    seedLiveCompatibilityPred (Time := Time) (X := X) P T
      (T.seedLiveCandidate P).velocity := by
  intro t x
  rfl

/-- The profile bound pushes the whole seed/live candidate under the tendril
envelope. -/
theorem UniformVorticityTendril.seedLive_abs_le
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (P : SeedLiveProfile)
    (t : Time) (x : X) :
    |(T.seedLiveCandidate P).velocity t x| ≤ (2 * P.coeff) * T.envelope := by
  have hseed : |T.vorticity 1 x| ≤ T.envelope := T.abs_vorticity_le 1 x
  have hlive : |T.vorticity t x| ≤ T.envelope := T.abs_vorticity_le t x
  have hadd :
      |T.vorticity 1 x| + |T.vorticity t x| ≤ T.envelope + T.envelope :=
    add_le_add hseed hlive
  have hmul :
      P.coeff * (|T.vorticity 1 x| + |T.vorticity t x|) ≤
        P.coeff * (T.envelope + T.envelope) :=
    mul_le_mul_of_nonneg_left hadd P.coeff_nonneg
  calc
    |(T.seedLiveCandidate P).velocity t x|
        = |P.profile (T.vorticity 1 x) (T.vorticity t x)| := rfl
    _ ≤ P.coeff * (|T.vorticity 1 x| + |T.vorticity t x|) :=
      P.bound _ _
    _ ≤ P.coeff * (T.envelope + T.envelope) := hmul
    _ = (2 * P.coeff) * T.envelope := by ring

/-- Regularity for any bounded seed/live profile candidate. -/
def UniformVorticityTendril.seedLiveRegularityCertificate
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (P : SeedLiveProfile) :
    RegularityCertificate
      (pressureSeededPredicateKit (Time := Time) (X := X) (T.seedLiveInitialSlice P))
      (T.seedLiveCandidate P) where
  smooth_velocity := by
    have htwo : 0 ≤ 2 * P.coeff := by nlinarith [P.coeff_nonneg]
    refine ⟨(2 * P.coeff) * T.envelope, mul_nonneg htwo T.envelope_nonneg, ?_⟩
    intro t x
    exact T.seedLive_abs_le P t x
  smooth_pressure := T.seedLiveCandidate_zeroPressure P

/-- The pressure and initial-slice dynamics slots remain explicit. -/
def UniformVorticityTendril.seedLiveDynamicsCertificate
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (P : SeedLiveProfile) :
    DynamicsCertificate
      (pressureSeededPredicateKit (Time := Time) (X := X) (T.seedLiveInitialSlice P))
      (T.seedLiveCandidate P) where
  momentum_equation := T.seedLiveCandidate_zeroPressure P
  incompressible := trivial
  initial_condition := T.seedLiveCandidate_matches_initialSlice P

/-- The energy-side bound is the same envelope estimate. -/
def UniformVorticityTendril.seedLiveEnergyCertificate
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (P : SeedLiveProfile) :
    EnergyCertificate
      (pressureSeededPredicateKit (Time := Time) (X := X) (T.seedLiveInitialSlice P))
      (T.seedLiveCandidate P) where
  bounded_energy := by
    have htwo : 0 ≤ 2 * P.coeff := by nlinarith [P.coeff_nonneg]
    refine ⟨(2 * P.coeff) * T.envelope, mul_nonneg htwo T.envelope_nonneg, ?_⟩
    intro t x
    exact T.seedLive_abs_le P t x

/-- Generic almost-bridge for a bounded seed/live profile. -/
def UniformVorticityTendril.toSeedLiveAlmostBridge
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (P : SeedLiveProfile) :
    AlmostFeffermanBridge
      (K := pressureSeededPredicateKit
        (Time := Time) (X := X) (T.seedLiveInitialSlice P)) T where
  candidate := T.seedLiveCandidate P
  regularity := T.seedLiveRegularityCertificate P
  dynamics := T.seedLiveDynamicsCertificate P
  energy := T.seedLiveEnergyCertificate P

/-- Same-route version: all slots are filled and self-compatibility is the
remaining mouth. -/
theorem UniformVorticityTendril.realizes_pressure_seeded_clause_of_seedLiveSelfCompatibility
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (P : SeedLiveProfile)
    (hcompat : selfCompatibility (Time := Time) (X := X)
      T (T.seedLiveCandidate P).velocity) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X)
      (pressureSeededPredicateKit (Time := Time) (X := X) (T.seedLiveInitialSlice P)) :=
  (T.toSeedLiveAlmostBridge P).realizes_clause_of_compatibility hcompat

/-- Descendant-route closure for the exact seed/live profile compatibility. -/
def UniformVorticityTendril.toSeedLiveBridge
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (P : SeedLiveProfile) :
    TopDownFeffermanBridge
      (pressureSeededPredicateKit (Time := Time) (X := X) (T.seedLiveInitialSlice P))
      (seedLiveCompatibilityPred (Time := Time) (X := X) P) T :=
  (T.toSeedLiveAlmostBridge P).toTopDownBridge
    (T.seedLiveCandidate_has_seedLiveCompatibility P)

theorem UniformVorticityTendril.realizes_seedLive_pressure_seeded_clause
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (P : SeedLiveProfile) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X)
      (pressureSeededPredicateKit (Time := Time) (X := X) (T.seedLiveInitialSlice P)) :=
  (T.toSeedLiveBridge P).realizes_clause

/-- Scalar-rescaled live profile. -/
def linearSeedLiveProfile (a : ℝ) : SeedLiveProfile where
  profile := fun _ live => a * live
  coeff := |a|
  coeff_nonneg := abs_nonneg a
  bound := by
    intro seed live
    calc
      |a * live| = |a| * |live| := by rw [abs_mul]
      _ ≤ |a| * (|seed| + |live|) := by
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg a)
        linarith [abs_nonneg seed]

/-- Affine seed/live blend profile. -/
def seedBlendProfile (a b : ℝ) : SeedLiveProfile where
  profile := fun seed live => a * live + b * seed
  coeff := |a| + |b|
  coeff_nonneg := add_nonneg (abs_nonneg a) (abs_nonneg b)
  bound := by
    intro seed live
    have htri : |a * live + b * seed| ≤ |a| * |live| + |b| * |seed| := by
      calc
        |a * live + b * seed| ≤ |a * live| + |b * seed| := by
          simpa using abs_add_le (a * live) (b * seed)
        _ = |a| * |live| + |b| * |seed| := by rw [abs_mul, abs_mul]
    have ha : 0 ≤ |a| := abs_nonneg a
    have hb : 0 ≤ |b| := abs_nonneg b
    have hs : 0 ≤ |seed| := abs_nonneg seed
    have hl : 0 ≤ |live| := abs_nonneg live
    nlinarith

/-- Saturated live profile. -/
def saturatedSeedLiveProfile (a : ℝ) : SeedLiveProfile where
  profile := fun _ live => a * (live / (1 + |live|))
  coeff := |a|
  coeff_nonneg := abs_nonneg a
  bound := by
    intro seed live
    have hden : 0 < 1 + |live| := by positivity
    have hden_abs : abs (1 + |live|) = 1 + |live| := by
      exact abs_of_nonneg (by positivity)
    have habs_ratio : |live / (1 + |live|)| = |live| / (1 + |live|) := by
      simpa [hden_abs] using (abs_div live (1 + |live|))
    have hdiv : |live| / (1 + |live|) ≤ |live| := by
      refine (div_le_iff₀ hden).2 ?_
      nlinarith [abs_nonneg live]
    calc
      |a * (live / (1 + |live|))|
          = |a| * |live / (1 + |live|)| := by rw [abs_mul]
      _ = |a| * (|live| / (1 + |live|)) := by rw [habs_ratio]
      _ ≤ |a| * |live| := by
        exact mul_le_mul_of_nonneg_left hdiv (abs_nonneg a)
      _ ≤ |a| * (|seed| + |live|) := by
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg a)
        linarith [abs_nonneg seed]

/-- Frozen-seed-gated live profile. -/
def frozenGateSeedLiveProfile (a : ℝ) : SeedLiveProfile where
  profile := fun seed live => a * (|seed| / (1 + |seed|)) * live
  coeff := |a|
  coeff_nonneg := abs_nonneg a
  bound := by
    intro seed live
    have hgate_nonneg : 0 ≤ |seed| / (1 + |seed|) := by positivity
    have hgate_le_one : |seed| / (1 + |seed|) ≤ 1 := by
      have hnum_le : |seed| ≤ 1 + |seed| := by linarith
      exact div_le_one_of_le₀ hnum_le (by positivity)
    calc
      |a * (|seed| / (1 + |seed|)) * live|
          = |a| * ((|seed| / (1 + |seed|)) * |live|) := by
            rw [mul_assoc, abs_mul, abs_mul, abs_of_nonneg hgate_nonneg]
      _ ≤ |a| * (1 * |live|) := by
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg a)
        exact mul_le_mul_of_nonneg_right hgate_le_one (abs_nonneg live)
      _ = |a| * |live| := by ring
      _ ≤ |a| * (|seed| + |live|) := by
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg a)
        linarith [abs_nonneg seed]

omit [Mul Time] in
theorem UniformVorticityTendril.seedLiveCandidate_linear_eq_scaledCandidate
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (a : ℝ) :
    T.seedLiveCandidate (linearSeedLiveProfile a) = T.scaledCandidate a := by
  rfl

omit [Mul Time] in
theorem UniformVorticityTendril.seedLiveCandidate_seedBlend_eq_seedBlendCandidate
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (a b : ℝ) :
    T.seedLiveCandidate (seedBlendProfile a b) = T.seedBlendCandidate a b := by
  rfl

omit [Mul Time] in
theorem UniformVorticityTendril.seedLiveCandidate_saturated_eq_saturatedCandidate
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (a : ℝ) :
    T.seedLiveCandidate (saturatedSeedLiveProfile a) = T.saturatedCandidate a := by
  rfl

omit [Mul Time] in
theorem UniformVorticityTendril.seedLiveCandidate_frozenGate_eq_frozenGateCandidate
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (a : ℝ) :
    T.seedLiveCandidate (frozenGateSeedLiveProfile a) = T.frozenGateCandidate a := by
  rfl

end SeedLiveProfileFrontier

end NavierStokes
end FluidDynamics
end Mettapedia
