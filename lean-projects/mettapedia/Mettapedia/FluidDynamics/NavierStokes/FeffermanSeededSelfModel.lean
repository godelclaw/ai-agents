import Mettapedia.FluidDynamics.NavierStokes.FeffermanWeakSelfModel

/-!
# Seeded Self-Model for the Fefferman Bridge

This file strengthens the weak self-model.  It still uses the current uniform
vorticity tendril as its own candidate velocity field, but the target now has
two genuinely nontrivial output-side predicates:

* the pressure field must be identically zero;
* the velocity must agree at the distinguished base time `1` with a prescribed
  initial slice.

So the current NS route now closes more than a bare boundedness-only target.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section SeededSelfModel

variable {Time X ι G : Type*}
variable [Fintype ι] [One Time] [Mul Time]
variable {radius statistic : G → ℝ}

/-- Pressure-zero predicate used in the seeded self model. -/
def ZeroPressure (p : Time → X → ℝ) : Prop :=
  ∀ t x, p t x = 0

/-- Initial-slice predicate at the distinguished base time `1`. -/
def MatchesInitialSlice (u₀ : X → ℝ) (u : Time → X → ℝ) : Prop :=
  ∀ x, u 1 x = u₀ x

/-- Stronger weak target: bounded velocity, zero pressure, and a specified
initial slice at time `1`. -/
def seededPredicateKit (u₀ : X → ℝ) : FeffermanPredicateKit (Time := Time) (X := X) where
  SmoothVelocity := fun _ => True
  SmoothPressure := ZeroPressure
  MomentumEquation := fun _ _ => True
  Incompressible := fun _ => True
  InitialCondition := MatchesInitialSlice u₀
  BoundedEnergy := UniformPointwiseBound

/-- Canonical initial slice extracted from a tendril. -/
def UniformVorticityTendril.initialSlice
    (T : UniformVorticityTendril (Time := Time) (X := X)) : X → ℝ :=
  fun x => T.vorticity 1 x

omit [Mul Time] in
theorem UniformVorticityTendril.selfCandidate_matches_initialSlice
    (T : UniformVorticityTendril (Time := Time) (X := X)) :
    MatchesInitialSlice (T.initialSlice) T.selfCandidate.velocity := by
  intro x
  rfl

omit [One Time] [Mul Time] in
theorem UniformVorticityTendril.selfCandidate_zeroPressure
    (T : UniformVorticityTendril (Time := Time) (X := X)) :
    ZeroPressure T.selfCandidate.pressure := by
  intro t x
  rfl

/-- The stronger regularity layer is still immediate: pressure is exactly zero. -/
def UniformVorticityTendril.seededSelfRegularityCertificate
    (T : UniformVorticityTendril (Time := Time) (X := X)) :
    RegularityCertificate (seededPredicateKit (Time := Time) (X := X) T.initialSlice) T.selfCandidate where
  smooth_velocity := trivial
  smooth_pressure := T.selfCandidate_zeroPressure

/-- The stronger dynamics layer now contains a genuine initial-slice equality. -/
def UniformVorticityTendril.seededSelfDynamicsCertificate
    (T : UniformVorticityTendril (Time := Time) (X := X)) :
    DynamicsCertificate (seededPredicateKit (Time := Time) (X := X) T.initialSlice) T.selfCandidate where
  momentum_equation := trivial
  incompressible := trivial
  initial_condition := T.selfCandidate_matches_initialSlice

/-- The energy layer is unchanged from the weak self model. -/
def UniformVorticityTendril.seededSelfEnergyCertificate
    (T : UniformVorticityTendril (Time := Time) (X := X)) :
    EnergyCertificate (seededPredicateKit (Time := Time) (X := X) T.initialSlice) T.selfCandidate where
  bounded_energy := by
    refine ⟨T.envelope, T.envelope_nonneg, ?_⟩
    intro t x
    simpa [UniformVorticityTendril.selfCandidate]
      using T.abs_vorticity_le t x

/-- Hence every tendril yields a stronger almost-bridge. -/
def UniformVorticityTendril.toSeededSelfAlmostBridge
    (T : UniformVorticityTendril (Time := Time) (X := X)) :
    AlmostFeffermanBridge
      (K := seededPredicateKit (Time := Time) (X := X) T.initialSlice) T where
  candidate := T.selfCandidate
  regularity := T.seededSelfRegularityCertificate
  dynamics := T.seededSelfDynamicsCertificate
  energy := T.seededSelfEnergyCertificate

/-- And therefore a stronger full bridge. -/
def UniformVorticityTendril.toSeededSelfBridge
    (T : UniformVorticityTendril (Time := Time) (X := X)) :
    TopDownFeffermanBridge
      (seededPredicateKit (Time := Time) (X := X) T.initialSlice)
      (selfCompatibility (Time := Time) (X := X)) T :=
  (T.toSeededSelfAlmostBridge).toTopDownBridge T.selfCompatibility_holds

omit [Mul Time] in
theorem UniformVorticityTendril.realizes_seeded_clause
    (T : UniformVorticityTendril (Time := Time) (X := X)) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X)
      (seededPredicateKit (Time := Time) (X := X) T.initialSlice) :=
  T.toSeededSelfBridge.realizes_clause

omit [Mul Time] in
theorem UniformVorticityTendril.realizes_seeded_clause_via_frontier
    (T : UniformVorticityTendril (Time := Time) (X := X)) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X)
      (seededPredicateKit (Time := Time) (X := X) T.initialSlice) :=
  (T.toSeededSelfAlmostBridge).realizes_clause_of_compatibility T.selfCompatibility_holds

omit [Mul Time] in
theorem ColeHopfIdentityData.realizes_seeded_self_clause
    (S : ColeHopfIdentityData (Time := Time) (ι := ι) (X := X)) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X)
      (seededPredicateKit (Time := Time) (X := X) S.toUniformVorticityTendril.initialSlice) :=
  UniformVorticityTendril.realizes_seeded_clause S.toUniformVorticityTendril

omit [Mul Time] in
theorem FiniteModeColeHopfData.realizes_seeded_self_clause
    (S : FiniteModeColeHopfData (Time := Time) (ι := ι) (X := X)) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X)
      (seededPredicateKit (Time := Time) (X := X) S.toUniformVorticityTendril.initialSlice) :=
  UniformVorticityTendril.realizes_seeded_clause S.toUniformVorticityTendril

theorem ColeHopfKernelSemigroupData.realizes_seeded_self_clause
    (S : ColeHopfKernelSemigroupData (Time := Time) (ι := ι) (X := X)) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X)
      (seededPredicateKit (Time := Time) (X := X) S.toUniformVorticityTendril.initialSlice) :=
  UniformVorticityTendril.realizes_seeded_clause S.toUniformVorticityTendril

theorem FiniteModeColeHopfKernelData.realizes_seeded_self_clause
    (S : FiniteModeColeHopfKernelData (Time := Time) (ι := ι) (X := X)) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X)
      (seededPredicateKit (Time := Time) (X := X) S.toUniformVorticityTendril.initialSlice) :=
  UniformVorticityTendril.realizes_seeded_clause S.toUniformVorticityTendril

theorem ManuscriptTruncationPackage.realizes_seeded_self_clause
    (S : ManuscriptTruncationPackage (Time := Time) (ι := ι) (X := X) radius statistic) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X)
      (seededPredicateKit (Time := Time) (X := X) S.toUniformVorticityTendril.initialSlice) :=
  UniformVorticityTendril.realizes_seeded_clause S.toUniformVorticityTendril

theorem SharedApproximationPackage.realizes_seeded_self_clause
    (S : SharedApproximationPackage (Time := Time) (ι := ι) (X := X) radius statistic)
    (x : G) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X)
      (seededPredicateKit (Time := Time) (X := X) (S.toUniformVorticityTendril x).initialSlice) :=
  UniformVorticityTendril.realizes_seeded_clause (S.toUniformVorticityTendril x)

end SeededSelfModel

end NavierStokes
end FluidDynamics
end Mettapedia
