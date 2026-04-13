import Mettapedia.FluidDynamics.NavierStokes.FeffermanSeedLiveProfileFrontier

/-!
# Seed/Live Operator Pressure-Seeded Frontier

This file pushes the non-self NS frontier one step beyond pointwise profiles.
An operator may now depend on the full seeded/live slices as functions, as long
as it obeys a uniform bound in terms of seeded/live sup envelopes.

The pointwise `SeedLiveProfile` shell embeds into this operator shell, and a
simple anchored non-pointwise blend is provided as a concrete instance.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section SeedLiveOperatorFrontier

variable {Time X ι G : Type*}
variable [Fintype ι] [One Time] [Mul Time]
variable {radius statistic : G → ℝ}

/-- Non-pointwise operator shell: the output at `x` may depend on the full
seeded/live slices, but must admit a uniform envelope bound. -/
structure SeedLiveOperator (X : Type*) where
  operator : (X → ℝ) → (X → ℝ) → X → ℝ
  coeff : ℝ
  coeff_nonneg : 0 ≤ coeff
  bound :
    ∀ seed live Bseed Blive,
      0 ≤ Bseed →
      0 ≤ Blive →
      (∀ x, |seed x| ≤ Bseed) →
      (∀ x, |live x| ≤ Blive) →
      ∀ x, |operator seed live x| ≤ coeff * (Bseed + Blive)

/-- Initial slice induced by a seed/live operator. -/
def UniformVorticityTendril.seedLiveOperatorInitialSlice
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (O : SeedLiveOperator X) : X → ℝ :=
  fun x => O.operator (fun y => T.vorticity 1 y) (fun y => T.vorticity 1 y) x

/-- Candidate fields induced by a seed/live operator. -/
def UniformVorticityTendril.seedLiveOperatorCandidate
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (O : SeedLiveOperator X) :
    VelocityPressureCandidate (Time := Time) (X := X) where
  velocity := fun t x => O.operator (fun y => T.vorticity 1 y) (fun y => T.vorticity t y) x
  pressure := fun _ _ => 0

/-- Exact compatibility notion for the seed/live operator descendant route. -/
def seedLiveOperatorCompatibilityPred (O : SeedLiveOperator X) :
    VorticityCompatibilityPred (Time := Time) (X := X) :=
  fun T u => ∀ t x,
    u t x = O.operator (fun y => T.vorticity 1 y) (fun y => T.vorticity t y) x

omit [Mul Time] in
theorem UniformVorticityTendril.seedLiveOperatorCandidate_zeroPressure
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (O : SeedLiveOperator X) :
    ZeroPressure (T.seedLiveOperatorCandidate O).pressure := by
  intro t x
  rfl

omit [Mul Time] in
theorem UniformVorticityTendril.seedLiveOperatorCandidate_matches_initialSlice
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (O : SeedLiveOperator X) :
    MatchesInitialSlice (T.seedLiveOperatorInitialSlice O) (T.seedLiveOperatorCandidate O).velocity := by
  intro x
  rfl

omit [Mul Time] in
theorem UniformVorticityTendril.seedLiveOperatorCandidate_has_seedLiveOperatorCompatibility
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (O : SeedLiveOperator X) :
    seedLiveOperatorCompatibilityPred (Time := Time) (X := X) O T
      (T.seedLiveOperatorCandidate O).velocity := by
  intro t x
  rfl

/- Any admissible seed/live operator is uniformly bounded by the tendril
envelope. -/
omit [Mul Time] in
theorem UniformVorticityTendril.seedLiveOperator_abs_le
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (O : SeedLiveOperator X)
    (t : Time) (x : X) :
    |(T.seedLiveOperatorCandidate O).velocity t x| ≤ (2 * O.coeff) * T.envelope := by
  have hseed : ∀ y, |T.vorticity 1 y| ≤ T.envelope := fun y => T.abs_vorticity_le 1 y
  have hlive : ∀ y, |T.vorticity t y| ≤ T.envelope := fun y => T.abs_vorticity_le t y
  have hbound :=
    O.bound (fun y => T.vorticity 1 y) (fun y => T.vorticity t y)
      T.envelope T.envelope T.envelope_nonneg T.envelope_nonneg hseed hlive x
  calc
    |(T.seedLiveOperatorCandidate O).velocity t x|
        = |O.operator (fun y => T.vorticity 1 y) (fun y => T.vorticity t y) x| := rfl
    _ ≤ O.coeff * (T.envelope + T.envelope) := hbound
    _ = (2 * O.coeff) * T.envelope := by ring

/-- Regularity for any bounded seed/live operator candidate. -/
def UniformVorticityTendril.seedLiveOperatorRegularityCertificate
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (O : SeedLiveOperator X) :
    RegularityCertificate
      (pressureSeededPredicateKit (Time := Time) (X := X) (T.seedLiveOperatorInitialSlice O))
      (T.seedLiveOperatorCandidate O) where
  smooth_velocity := by
    have htwo : 0 ≤ 2 * O.coeff := by nlinarith [O.coeff_nonneg]
    refine ⟨(2 * O.coeff) * T.envelope, mul_nonneg htwo T.envelope_nonneg, ?_⟩
    intro t x
    exact T.seedLiveOperator_abs_le O t x
  smooth_pressure := T.seedLiveOperatorCandidate_zeroPressure O

/-- Pressure and initial-slice slots remain explicit. -/
def UniformVorticityTendril.seedLiveOperatorDynamicsCertificate
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (O : SeedLiveOperator X) :
    DynamicsCertificate
      (pressureSeededPredicateKit (Time := Time) (X := X) (T.seedLiveOperatorInitialSlice O))
      (T.seedLiveOperatorCandidate O) where
  momentum_equation := T.seedLiveOperatorCandidate_zeroPressure O
  incompressible := trivial
  initial_condition := T.seedLiveOperatorCandidate_matches_initialSlice O

/-- Energy-side bound for any admissible seed/live operator. -/
def UniformVorticityTendril.seedLiveOperatorEnergyCertificate
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (O : SeedLiveOperator X) :
    EnergyCertificate
      (pressureSeededPredicateKit (Time := Time) (X := X) (T.seedLiveOperatorInitialSlice O))
      (T.seedLiveOperatorCandidate O) where
  bounded_energy := by
    have htwo : 0 ≤ 2 * O.coeff := by nlinarith [O.coeff_nonneg]
    refine ⟨(2 * O.coeff) * T.envelope, mul_nonneg htwo T.envelope_nonneg, ?_⟩
    intro t x
    exact T.seedLiveOperator_abs_le O t x

/-- Generic almost-bridge for a seed/live operator. -/
def UniformVorticityTendril.toSeedLiveOperatorAlmostBridge
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (O : SeedLiveOperator X) :
    AlmostFeffermanBridge
      (K := pressureSeededPredicateKit
        (Time := Time) (X := X) (T.seedLiveOperatorInitialSlice O)) T where
  candidate := T.seedLiveOperatorCandidate O
  regularity := T.seedLiveOperatorRegularityCertificate O
  dynamics := T.seedLiveOperatorDynamicsCertificate O
  energy := T.seedLiveOperatorEnergyCertificate O

/- Same-route version: self-compatibility is the only remaining mouth. -/
omit [Mul Time] in
theorem UniformVorticityTendril.realizes_pressure_seeded_clause_of_seedLiveOperatorSelfCompatibility
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (O : SeedLiveOperator X)
    (hcompat : selfCompatibility (Time := Time) (X := X)
      T (T.seedLiveOperatorCandidate O).velocity) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X)
      (pressureSeededPredicateKit (Time := Time) (X := X) (T.seedLiveOperatorInitialSlice O)) :=
  (T.toSeedLiveOperatorAlmostBridge O).realizes_clause_of_compatibility hcompat
omit [Mul Time] in
theorem UniformVorticityTendril.realizes_seedLiveOperator_pressure_seeded_clause_of_selfCompatibility
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (O : SeedLiveOperator X)
    (hcompat : selfCompatibility (Time := Time) (X := X)
      T (T.seedLiveOperatorCandidate O).velocity) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X)
      (pressureSeededPredicateKit (Time := Time) (X := X)
        (T.seedLiveOperatorInitialSlice O)) :=
  T.realizes_pressure_seeded_clause_of_seedLiveOperatorSelfCompatibility O hcompat

omit [Mul Time] in
theorem UniformVorticityTendril.seedLiveOperatorCandidate_has_selfCompatibility_of_operator_eq_live
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (O : SeedLiveOperator X)
    (hO : ∀ seed live x, O.operator seed live x = live x) :
    selfCompatibility (Time := Time) (X := X)
      T (T.seedLiveOperatorCandidate O).velocity := by
  intro t x
  simpa [UniformVorticityTendril.seedLiveOperatorCandidate] using
    hO (fun y => T.vorticity 1 y) (fun y => T.vorticity t y) x
omit [Mul Time] in
theorem UniformVorticityTendril.realizes_seedLiveOperator_pressure_seeded_clause_of_operator_eq_live
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (O : SeedLiveOperator X)
    (hO : ∀ seed live x, O.operator seed live x = live x) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X)
      (pressureSeededPredicateKit (Time := Time) (X := X)
        (T.seedLiveOperatorInitialSlice O)) :=
  T.realizes_seedLiveOperator_pressure_seeded_clause_of_selfCompatibility O
    (T.seedLiveOperatorCandidate_has_selfCompatibility_of_operator_eq_live O hO)

omit [Mul Time] in
theorem UniformVorticityTendril.seedLiveOperatorCandidate_has_selfCompatibility_of_operator_eq_seed_of_stationary
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (O : SeedLiveOperator X)
    (hO : ∀ seed live x, O.operator seed live x = seed x)
    (hstat : ∀ t x, T.vorticity 1 x = T.vorticity t x) :
    selfCompatibility (Time := Time) (X := X)
      T (T.seedLiveOperatorCandidate O).velocity := by
  intro t x
  calc
    (T.seedLiveOperatorCandidate O).velocity t x
        = O.operator (fun y => T.vorticity 1 y) (fun y => T.vorticity t y) x := rfl
    _ = T.vorticity 1 x := hO (fun y => T.vorticity 1 y) (fun y => T.vorticity t y) x
    _ = T.vorticity t x := hstat t x
omit [Mul Time] in
theorem UniformVorticityTendril.realizes_seedLiveOperator_pressure_seeded_clause_of_operator_eq_seed_of_stationary
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (O : SeedLiveOperator X)
    (hO : ∀ seed live x, O.operator seed live x = seed x)
    (hstat : ∀ t x, T.vorticity 1 x = T.vorticity t x) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X)
      (pressureSeededPredicateKit (Time := Time) (X := X)
        (T.seedLiveOperatorInitialSlice O)) :=
  T.realizes_seedLiveOperator_pressure_seeded_clause_of_selfCompatibility O
    (T.seedLiveOperatorCandidate_has_selfCompatibility_of_operator_eq_seed_of_stationary
      O hO hstat)

omit [Mul Time] in
theorem UniformVorticityTendril.seedLiveOperatorCandidate_has_selfCompatibility_of_zero_vorticity
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (O : SeedLiveOperator X)
    (hO0 : ∀ x, O.operator (fun _ => 0) (fun _ => 0) x = 0)
    (hzero : ∀ t x, T.vorticity t x = 0) :
    selfCompatibility (Time := Time) (X := X)
      T (T.seedLiveOperatorCandidate O).velocity := by
  intro t x
  have hseed0 : (fun y => T.vorticity 1 y) = (fun _ => (0 : ℝ)) := by
    funext y
    exact hzero 1 y
  have hlive0 : (fun y => T.vorticity t y) = (fun _ => (0 : ℝ)) := by
    funext y
    exact hzero t y
  calc
    (T.seedLiveOperatorCandidate O).velocity t x
        = O.operator (fun y => T.vorticity 1 y) (fun y => T.vorticity t y) x := rfl
    _ = O.operator (fun _ => 0) (fun _ => 0) x := by rw [hseed0, hlive0]
    _ = 0 := hO0 x
    _ = T.vorticity t x := by
      symm
      exact hzero t x

/-- Descendant-route closure for the exact seed/live operator compatibility. -/
def UniformVorticityTendril.toSeedLiveOperatorBridge
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (O : SeedLiveOperator X) :
    TopDownFeffermanBridge
      (pressureSeededPredicateKit (Time := Time) (X := X) (T.seedLiveOperatorInitialSlice O))
      (seedLiveOperatorCompatibilityPred (Time := Time) (X := X) O) T :=
  (T.toSeedLiveOperatorAlmostBridge O).toTopDownBridge
    (T.seedLiveOperatorCandidate_has_seedLiveOperatorCompatibility O)
omit [Mul Time] in
theorem UniformVorticityTendril.realizes_seedLiveOperator_pressure_seeded_clause
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (O : SeedLiveOperator X) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X)
      (pressureSeededPredicateKit (Time := Time) (X := X) (T.seedLiveOperatorInitialSlice O)) :=
  (T.toSeedLiveOperatorBridge O).realizes_clause
omit [Mul Time] in
theorem UniformVorticityTendril.realizes_seedLiveOperator_pressure_seeded_clause_of_zero_vorticity
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (O : SeedLiveOperator X)
    (hO0 : ∀ x, O.operator (fun _ => 0) (fun _ => 0) x = 0)
    (hzero : ∀ t x, T.vorticity t x = 0) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X)
      (pressureSeededPredicateKit (Time := Time) (X := X)
        (T.seedLiveOperatorInitialSlice O)) :=
  T.realizes_seedLiveOperator_pressure_seeded_clause_of_selfCompatibility O
    (T.seedLiveOperatorCandidate_has_selfCompatibility_of_zero_vorticity O hO0 hzero)
omit [Mul Time] in
theorem UniformVorticityTendril.toSeedLiveOperatorBridge_retains_uniform_vorticity
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (O : SeedLiveOperator X) :
    ∀ t x, |T.vorticity t x| ≤ T.envelope :=
  (T.toSeedLiveOperatorBridge O).retains_uniform_vorticity

/-- Every pointwise seed/live profile yields a seed/live operator. -/
def SeedLiveProfile.toSeedLiveOperator
    (P : SeedLiveProfile) : SeedLiveOperator X where
  operator := fun seed live x => P.profile (seed x) (live x)
  coeff := P.coeff
  coeff_nonneg := P.coeff_nonneg
  bound := by
    intro seed live Bseed Blive hBseed hBlive hseed hlive x
    have hpoint := P.bound (seed x) (live x)
    have hsum : |seed x| + |live x| ≤ Bseed + Blive := add_le_add (hseed x) (hlive x)
    calc
      |P.profile (seed x) (live x)| ≤ P.coeff * (|seed x| + |live x|) := hpoint
      _ ≤ P.coeff * (Bseed + Blive) := mul_le_mul_of_nonneg_left hsum P.coeff_nonneg

omit [Mul Time] in
theorem UniformVorticityTendril.seedLiveOperatorCandidate_profile_eq_seedLiveCandidate
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (P : SeedLiveProfile) :
    T.seedLiveOperatorCandidate P.toSeedLiveOperator = T.seedLiveCandidate P := by
  rfl

/-- A concrete non-pointwise operator: the live value at `x` is blended with
seeded and live values sampled at `anchor x`. -/
def anchoredSeedLiveBlendOperator
    (anchor : X → X) (a b c : ℝ) : SeedLiveOperator X where
  operator := fun seed live x => a * live x + b * seed (anchor x) + c * live (anchor x)
  coeff := |a| + |b| + |c|
  coeff_nonneg := by positivity
  bound := by
    intro seed live Bseed Blive hBseed hBlive hseed hlive x
    have htri : |a * live x + b * seed (anchor x) + c * live (anchor x)|
        ≤ |a * live x| + |b * seed (anchor x)| + |c * live (anchor x)| := by
      calc
        |a * live x + b * seed (anchor x) + c * live (anchor x)|
            ≤ |a * live x + b * seed (anchor x)| + |c * live (anchor x)| := by
              simpa using abs_add_le (a * live x + b * seed (anchor x)) (c * live (anchor x))
        _ ≤ (|a * live x| + |b * seed (anchor x)|) + |c * live (anchor x)| := by
          gcongr
          simpa using abs_add_le (a * live x) (b * seed (anchor x))
        _ = |a * live x| + |b * seed (anchor x)| + |c * live (anchor x)| := by ring
    have ha : |a * live x| ≤ |a| * Blive := by
      calc
        |a * live x| = |a| * |live x| := by rw [abs_mul]
        _ ≤ |a| * Blive := mul_le_mul_of_nonneg_left (hlive x) (abs_nonneg a)
    have hb : |b * seed (anchor x)| ≤ |b| * Bseed := by
      calc
        |b * seed (anchor x)| = |b| * |seed (anchor x)| := by rw [abs_mul]
        _ ≤ |b| * Bseed := mul_le_mul_of_nonneg_left (hseed (anchor x)) (abs_nonneg b)
    have hc : |c * live (anchor x)| ≤ |c| * Blive := by
      calc
        |c * live (anchor x)| = |c| * |live (anchor x)| := by rw [abs_mul]
        _ ≤ |c| * Blive := mul_le_mul_of_nonneg_left (hlive (anchor x)) (abs_nonneg c)
    calc
      |a * live x + b * seed (anchor x) + c * live (anchor x)|
          ≤ |a * live x| + |b * seed (anchor x)| + |c * live (anchor x)| := htri
      _ ≤ |a| * Blive + |b| * Bseed + |c| * Blive := add_le_add (add_le_add ha hb) hc
      _ ≤ (|a| + |b| + |c|) * (Bseed + Blive) := by
        have ha' : 0 ≤ |a| := abs_nonneg a
        have hb' : 0 ≤ |b| := abs_nonneg b
        have hc' : 0 ≤ |c| := abs_nonneg c
        nlinarith

end SeedLiveOperatorFrontier

end NavierStokes
end FluidDynamics
end Mettapedia
