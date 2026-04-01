import Mettapedia.FluidDynamics.NavierStokes.FeffermanSeededSelfModel

/-!
# Bounded Seeded Self-Model for the Fefferman Bridge

This file strengthens the seeded self-model one step further.  The canonical
self candidate still uses the tendril vorticity as velocity and zero pressure,
but now the target-side regularity slot for velocity is also nontrivial: it
requires the same uniform pointwise bound already carried by the tendril
envelope.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section BoundedSeededSelfModel

variable {Time X ι G : Type*}
variable [Fintype ι] [One Time] [Mul Time]
variable {radius statistic : G → ℝ}

/-- Stronger seeded target: velocity is uniformly pointwise bounded, pressure is
identically zero, the initial slice is prescribed, and the same bound is kept
as the energy-side target. -/
def boundedSeededPredicateKit (u₀ : X → ℝ) :
    FeffermanPredicateKit (Time := Time) (X := X) where
  SmoothVelocity := UniformPointwiseBound
  SmoothPressure := ZeroPressure
  MomentumEquation := fun _ _ => True
  Incompressible := fun _ => True
  InitialCondition := MatchesInitialSlice u₀
  BoundedEnergy := UniformPointwiseBound

/-- The current tendril envelope already furnishes the stronger regularity-side
velocity bound. -/
def UniformVorticityTendril.boundedSeededRegularityCertificate
    (T : UniformVorticityTendril (Time := Time) (X := X)) :
    RegularityCertificate
      (boundedSeededPredicateKit (Time := Time) (X := X) T.initialSlice)
      T.selfCandidate where
  smooth_velocity := by
    refine ⟨T.envelope, T.envelope_nonneg, ?_⟩
    intro t x
    simpa [UniformVorticityTendril.selfCandidate]
      using T.abs_vorticity_le t x
  smooth_pressure := T.selfCandidate_zeroPressure

/-- The stronger dynamics layer is unchanged from the seeded self model. -/
def UniformVorticityTendril.boundedSeededDynamicsCertificate
    (T : UniformVorticityTendril (Time := Time) (X := X)) :
    DynamicsCertificate
      (boundedSeededPredicateKit (Time := Time) (X := X) T.initialSlice)
      T.selfCandidate where
  momentum_equation := trivial
  incompressible := trivial
  initial_condition := T.selfCandidate_matches_initialSlice

/-- The energy layer stays the same pointwise envelope bound. -/
def UniformVorticityTendril.boundedSeededEnergyCertificate
    (T : UniformVorticityTendril (Time := Time) (X := X)) :
    EnergyCertificate
      (boundedSeededPredicateKit (Time := Time) (X := X) T.initialSlice)
      T.selfCandidate where
  bounded_energy := by
    refine ⟨T.envelope, T.envelope_nonneg, ?_⟩
    intro t x
    simpa [UniformVorticityTendril.selfCandidate]
      using T.abs_vorticity_le t x

/-- Every tendril therefore yields a stronger almost-bridge. -/
def UniformVorticityTendril.toBoundedSeededSelfAlmostBridge
    (T : UniformVorticityTendril (Time := Time) (X := X)) :
    AlmostFeffermanBridge
      (K := boundedSeededPredicateKit (Time := Time) (X := X) T.initialSlice) T where
  candidate := T.selfCandidate
  regularity := T.boundedSeededRegularityCertificate
  dynamics := T.boundedSeededDynamicsCertificate
  energy := T.boundedSeededEnergyCertificate

/-- And hence a stronger full bridge. -/
def UniformVorticityTendril.toBoundedSeededSelfBridge
    (T : UniformVorticityTendril (Time := Time) (X := X)) :
    TopDownFeffermanBridge
      (boundedSeededPredicateKit (Time := Time) (X := X) T.initialSlice)
      (selfCompatibility (Time := Time) (X := X)) T :=
  (T.toBoundedSeededSelfAlmostBridge).toTopDownBridge T.selfCompatibility_holds

omit [Mul Time] in
theorem UniformVorticityTendril.realizes_bounded_seeded_clause
    (T : UniformVorticityTendril (Time := Time) (X := X)) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X)
      (boundedSeededPredicateKit (Time := Time) (X := X) T.initialSlice) :=
  T.toBoundedSeededSelfBridge.realizes_clause

omit [Mul Time] in
theorem UniformVorticityTendril.realizes_bounded_seeded_clause_via_frontier
    (T : UniformVorticityTendril (Time := Time) (X := X)) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X)
      (boundedSeededPredicateKit (Time := Time) (X := X) T.initialSlice) :=
  (T.toBoundedSeededSelfAlmostBridge).realizes_clause_of_compatibility
    T.selfCompatibility_holds

omit [Mul Time] in
theorem ColeHopfIdentityData.realizes_bounded_seeded_self_clause
    (S : ColeHopfIdentityData (Time := Time) (ι := ι) (X := X)) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X)
      (boundedSeededPredicateKit
        (Time := Time) (X := X) S.toUniformVorticityTendril.initialSlice) :=
  UniformVorticityTendril.realizes_bounded_seeded_clause S.toUniformVorticityTendril

omit [Mul Time] in
theorem FiniteModeColeHopfData.realizes_bounded_seeded_self_clause
    (S : FiniteModeColeHopfData (Time := Time) (ι := ι) (X := X)) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X)
      (boundedSeededPredicateKit
        (Time := Time) (X := X) S.toUniformVorticityTendril.initialSlice) :=
  UniformVorticityTendril.realizes_bounded_seeded_clause S.toUniformVorticityTendril

theorem ColeHopfKernelSemigroupData.realizes_bounded_seeded_self_clause
    (S : ColeHopfKernelSemigroupData (Time := Time) (ι := ι) (X := X)) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X)
      (boundedSeededPredicateKit
        (Time := Time) (X := X) S.toUniformVorticityTendril.initialSlice) :=
  UniformVorticityTendril.realizes_bounded_seeded_clause S.toUniformVorticityTendril

theorem FiniteModeColeHopfKernelData.realizes_bounded_seeded_self_clause
    (S : FiniteModeColeHopfKernelData (Time := Time) (ι := ι) (X := X)) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X)
      (boundedSeededPredicateKit
        (Time := Time) (X := X) S.toUniformVorticityTendril.initialSlice) :=
  UniformVorticityTendril.realizes_bounded_seeded_clause S.toUniformVorticityTendril

theorem ManuscriptTruncationPackage.realizes_bounded_seeded_self_clause
    (S : ManuscriptTruncationPackage
      (Time := Time) (ι := ι) (X := X) radius statistic) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X)
      (boundedSeededPredicateKit
        (Time := Time) (X := X) S.toUniformVorticityTendril.initialSlice) :=
  UniformVorticityTendril.realizes_bounded_seeded_clause S.toUniformVorticityTendril

theorem SharedApproximationPackage.realizes_bounded_seeded_self_clause
    (S : SharedApproximationPackage
      (Time := Time) (ι := ι) (X := X) radius statistic)
    (x : G) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X)
      (boundedSeededPredicateKit
        (Time := Time) (X := X) (S.toUniformVorticityTendril x).initialSlice) :=
  UniformVorticityTendril.realizes_bounded_seeded_clause
    (S.toUniformVorticityTendril x)

end BoundedSeededSelfModel

end NavierStokes
end FluidDynamics
end Mettapedia
