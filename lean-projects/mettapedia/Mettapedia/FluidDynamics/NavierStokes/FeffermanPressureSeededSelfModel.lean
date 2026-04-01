import Mettapedia.FluidDynamics.NavierStokes.FeffermanBoundedSeededSelfModel

/-!
# Pressure-Seeded Self-Model for the Fefferman Bridge

This file strengthens the bounded seeded self-model one step further.  It keeps
the same canonical self candidate, but now the dynamics-side momentum slot is
also nontrivial: it requires the pressure field to vanish.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section PressureSeededSelfModel

variable {Time X ι G : Type*}
variable [Fintype ι] [One Time] [Mul Time]
variable {radius statistic : G → ℝ}

/-- Stronger seeded target: velocity is uniformly bounded, pressure must vanish
in both the regularity and momentum slots, the initial slice is prescribed, and
the same bound is kept as the energy-side target. -/
def pressureSeededPredicateKit (u₀ : X → ℝ) :
    FeffermanPredicateKit (Time := Time) (X := X) where
  SmoothVelocity := UniformPointwiseBound
  SmoothPressure := ZeroPressure
  MomentumEquation := fun _ p => ZeroPressure p
  Incompressible := fun _ => True
  InitialCondition := MatchesInitialSlice u₀
  BoundedEnergy := UniformPointwiseBound

/-- The stronger regularity layer is unchanged from the bounded seeded model. -/
def UniformVorticityTendril.pressureSeededRegularityCertificate
    (T : UniformVorticityTendril (Time := Time) (X := X)) :
    RegularityCertificate
      (pressureSeededPredicateKit (Time := Time) (X := X) T.initialSlice)
      T.selfCandidate where
  smooth_velocity := by
    refine ⟨T.envelope, T.envelope_nonneg, ?_⟩
    intro t x
    simpa [UniformVorticityTendril.selfCandidate]
      using T.abs_vorticity_le t x
  smooth_pressure := T.selfCandidate_zeroPressure

/-- The momentum slot is now nontrivial too: it is witnessed by the same zero
pressure proof. -/
def UniformVorticityTendril.pressureSeededDynamicsCertificate
    (T : UniformVorticityTendril (Time := Time) (X := X)) :
    DynamicsCertificate
      (pressureSeededPredicateKit (Time := Time) (X := X) T.initialSlice)
      T.selfCandidate where
  momentum_equation := T.selfCandidate_zeroPressure
  incompressible := trivial
  initial_condition := T.selfCandidate_matches_initialSlice

/-- The energy layer stays the same pointwise envelope bound. -/
def UniformVorticityTendril.pressureSeededEnergyCertificate
    (T : UniformVorticityTendril (Time := Time) (X := X)) :
    EnergyCertificate
      (pressureSeededPredicateKit (Time := Time) (X := X) T.initialSlice)
      T.selfCandidate where
  bounded_energy := by
    refine ⟨T.envelope, T.envelope_nonneg, ?_⟩
    intro t x
    simpa [UniformVorticityTendril.selfCandidate]
      using T.abs_vorticity_le t x

/-- Every tendril therefore yields a still stronger almost-bridge. -/
def UniformVorticityTendril.toPressureSeededSelfAlmostBridge
    (T : UniformVorticityTendril (Time := Time) (X := X)) :
    AlmostFeffermanBridge
      (K := pressureSeededPredicateKit (Time := Time) (X := X) T.initialSlice) T where
  candidate := T.selfCandidate
  regularity := T.pressureSeededRegularityCertificate
  dynamics := T.pressureSeededDynamicsCertificate
  energy := T.pressureSeededEnergyCertificate

/-- And hence a still stronger full bridge. -/
def UniformVorticityTendril.toPressureSeededSelfBridge
    (T : UniformVorticityTendril (Time := Time) (X := X)) :
    TopDownFeffermanBridge
      (pressureSeededPredicateKit (Time := Time) (X := X) T.initialSlice)
      (selfCompatibility (Time := Time) (X := X)) T :=
  (T.toPressureSeededSelfAlmostBridge).toTopDownBridge T.selfCompatibility_holds

omit [Mul Time] in
theorem UniformVorticityTendril.realizes_pressure_seeded_clause
    (T : UniformVorticityTendril (Time := Time) (X := X)) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X)
      (pressureSeededPredicateKit (Time := Time) (X := X) T.initialSlice) :=
  T.toPressureSeededSelfBridge.realizes_clause

omit [Mul Time] in
theorem UniformVorticityTendril.realizes_pressure_seeded_clause_via_frontier
    (T : UniformVorticityTendril (Time := Time) (X := X)) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X)
      (pressureSeededPredicateKit (Time := Time) (X := X) T.initialSlice) :=
  (T.toPressureSeededSelfAlmostBridge).realizes_clause_of_compatibility
    T.selfCompatibility_holds

omit [Mul Time] in
theorem ColeHopfIdentityData.realizes_pressure_seeded_self_clause
    (S : ColeHopfIdentityData (Time := Time) (ι := ι) (X := X)) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X)
      (pressureSeededPredicateKit
        (Time := Time) (X := X) S.toUniformVorticityTendril.initialSlice) :=
  UniformVorticityTendril.realizes_pressure_seeded_clause S.toUniformVorticityTendril

omit [Mul Time] in
theorem FiniteModeColeHopfData.realizes_pressure_seeded_self_clause
    (S : FiniteModeColeHopfData (Time := Time) (ι := ι) (X := X)) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X)
      (pressureSeededPredicateKit
        (Time := Time) (X := X) S.toUniformVorticityTendril.initialSlice) :=
  UniformVorticityTendril.realizes_pressure_seeded_clause S.toUniformVorticityTendril

theorem ColeHopfKernelSemigroupData.realizes_pressure_seeded_self_clause
    (S : ColeHopfKernelSemigroupData (Time := Time) (ι := ι) (X := X)) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X)
      (pressureSeededPredicateKit
        (Time := Time) (X := X) S.toUniformVorticityTendril.initialSlice) :=
  UniformVorticityTendril.realizes_pressure_seeded_clause S.toUniformVorticityTendril

theorem FiniteModeColeHopfKernelData.realizes_pressure_seeded_self_clause
    (S : FiniteModeColeHopfKernelData (Time := Time) (ι := ι) (X := X)) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X)
      (pressureSeededPredicateKit
        (Time := Time) (X := X) S.toUniformVorticityTendril.initialSlice) :=
  UniformVorticityTendril.realizes_pressure_seeded_clause S.toUniformVorticityTendril

theorem ManuscriptTruncationPackage.realizes_pressure_seeded_self_clause
    (S : ManuscriptTruncationPackage
      (Time := Time) (ι := ι) (X := X) radius statistic) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X)
      (pressureSeededPredicateKit
        (Time := Time) (X := X) S.toUniformVorticityTendril.initialSlice) :=
  UniformVorticityTendril.realizes_pressure_seeded_clause S.toUniformVorticityTendril

theorem SharedApproximationPackage.realizes_pressure_seeded_self_clause
    (S : SharedApproximationPackage
      (Time := Time) (ι := ι) (X := X) radius statistic)
    (x : G) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X)
      (pressureSeededPredicateKit
        (Time := Time) (X := X) (S.toUniformVorticityTendril x).initialSlice) :=
  UniformVorticityTendril.realizes_pressure_seeded_clause
    (S.toUniformVorticityTendril x)

end PressureSeededSelfModel

end NavierStokes
end FluidDynamics
end Mettapedia
