import Mettapedia.FluidDynamics.NavierStokes.FeffermanSeedLiveSampleKernelFrontier

/-!
# Seed/Live Shift-Kernel Pressure-Seeded Frontier

This file specializes the finite sampled-kernel shell to translation-style
kernels on an additive state space.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section SeedLiveShiftKernelFrontier

variable {Time X ι G κ : Type*}
variable [Fintype ι] [One Time] [Mul Time] [Fintype κ] [AddMonoid X]
variable {radius statistic : G → ℝ}

/-- Finite translation-style kernel mixing seeded and live slices. -/
structure SeedLiveShiftKernel (κ X : Type*) [Fintype κ] [AddMonoid X] where
  seedShift : κ → X
  liveShift : κ → X
  seedCoeff : κ → ℝ
  liveCoeff : κ → ℝ

/-- Every shift kernel induces a finite sampled kernel via translation anchors. -/
def SeedLiveShiftKernel.toSampleKernel (K : SeedLiveShiftKernel κ X) :
    SeedLiveSampleKernel κ X where
  seedAnchor := fun j x => x + K.seedShift j
  liveAnchor := fun j x => x + K.liveShift j
  seedCoeff := K.seedCoeff
  liveCoeff := K.liveCoeff

/-- Exact shift-kernel compatibility predicate. -/
def shiftKernelCompatibilityPred (K : SeedLiveShiftKernel κ X) :
    VorticityCompatibilityPred (Time := Time) (X := X) :=
  sampleKernelCompatibilityPred (Time := Time) (X := X) K.toSampleKernel

/-- Every shift kernel reaches the same sampled-kernel frontier. -/
def UniformVorticityTendril.toShiftKernelAlmostBridge
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (K : SeedLiveShiftKernel κ X) :
    AlmostFeffermanBridge
      (K := pressureSeededPredicateKit
        (Time := Time) (X := X) (T.seedLiveOperatorInitialSlice K.toSampleKernel.toSeedLiveOperator)) T :=
  T.toSampleKernelAlmostBridge K.toSampleKernel

/- Same-route version: self-compatibility is still the remaining mouth. -/
omit [Mul Time] in
theorem UniformVorticityTendril.realizes_pressure_seeded_clause_of_shiftKernelSelfCompatibility
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (K : SeedLiveShiftKernel κ X)
    (hcompat : selfCompatibility (Time := Time) (X := X)
      T (T.seedLiveOperatorCandidate K.toSampleKernel.toSeedLiveOperator).velocity) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X)
      (pressureSeededPredicateKit
        (Time := Time) (X := X) (T.seedLiveOperatorInitialSlice K.toSampleKernel.toSeedLiveOperator)) :=
  T.realizes_pressure_seeded_clause_of_sampleKernelSelfCompatibility K.toSampleKernel hcompat

omit [Mul Time] in
theorem UniformVorticityTendril.shiftKernelCandidate_has_selfCompatibility_of_zero_vorticity
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (K : SeedLiveShiftKernel κ X)
    (hzero : ∀ t x, T.vorticity t x = 0) :
    selfCompatibility (Time := Time) (X := X)
      T (T.seedLiveOperatorCandidate K.toSampleKernel.toSeedLiveOperator).velocity :=
  T.sampleKernelCandidate_has_selfCompatibility_of_zero_vorticity K.toSampleKernel hzero

/-- Descendant-route closure for exact shift-kernel compatibility. -/
def UniformVorticityTendril.toShiftKernelBridge
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (K : SeedLiveShiftKernel κ X) :
    TopDownFeffermanBridge
      (pressureSeededPredicateKit
        (Time := Time) (X := X) (T.seedLiveOperatorInitialSlice K.toSampleKernel.toSeedLiveOperator))
      (shiftKernelCompatibilityPred (Time := Time) (X := X) K) T :=
  T.toSampleKernelBridge K.toSampleKernel
omit [Mul Time] in
theorem UniformVorticityTendril.realizes_shiftKernel_pressure_seeded_clause
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (K : SeedLiveShiftKernel κ X) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X)
      (pressureSeededPredicateKit
        (Time := Time) (X := X) (T.seedLiveOperatorInitialSlice K.toSampleKernel.toSeedLiveOperator)) :=
  T.realizes_sampleKernel_pressure_seeded_clause K.toSampleKernel
omit [Mul Time] in
theorem UniformVorticityTendril.realizes_shiftKernel_pressure_seeded_clause_of_selfCompatibility
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (K : SeedLiveShiftKernel κ X)
    (hcompat : selfCompatibility (Time := Time) (X := X)
      T (T.seedLiveOperatorCandidate K.toSampleKernel.toSeedLiveOperator).velocity) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X)
      (pressureSeededPredicateKit
        (Time := Time) (X := X) (T.seedLiveOperatorInitialSlice K.toSampleKernel.toSeedLiveOperator)) :=
  T.realizes_pressure_seeded_clause_of_shiftKernelSelfCompatibility K hcompat

omit [Mul Time] in
theorem UniformVorticityTendril.shiftKernelCandidate_has_selfCompatibility_of_operator_eq_live
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (K : SeedLiveShiftKernel κ X)
    (hK : ∀ seed live x, K.toSampleKernel.toSeedLiveOperator.operator seed live x = live x) :
    selfCompatibility (Time := Time) (X := X)
      T (T.seedLiveOperatorCandidate K.toSampleKernel.toSeedLiveOperator).velocity :=
  T.sampleKernelCandidate_has_selfCompatibility_of_operator_eq_live
    K.toSampleKernel hK
omit [Mul Time] in
theorem UniformVorticityTendril.realizes_shiftKernel_pressure_seeded_clause_of_operator_eq_live
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (K : SeedLiveShiftKernel κ X)
    (hK : ∀ seed live x, K.toSampleKernel.toSeedLiveOperator.operator seed live x = live x) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X)
      (pressureSeededPredicateKit
        (Time := Time) (X := X) (T.seedLiveOperatorInitialSlice K.toSampleKernel.toSeedLiveOperator)) :=
  T.realizes_shiftKernel_pressure_seeded_clause_of_selfCompatibility K
    (T.shiftKernelCandidate_has_selfCompatibility_of_operator_eq_live K hK)

omit [Mul Time] in
theorem UniformVorticityTendril.shiftKernelCandidate_has_selfCompatibility_of_operator_eq_seed_of_stationary
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (K : SeedLiveShiftKernel κ X)
    (hK : ∀ seed live x, K.toSampleKernel.toSeedLiveOperator.operator seed live x = seed x)
    (hstat : ∀ t x, T.vorticity 1 x = T.vorticity t x) :
    selfCompatibility (Time := Time) (X := X)
      T (T.seedLiveOperatorCandidate K.toSampleKernel.toSeedLiveOperator).velocity :=
  T.sampleKernelCandidate_has_selfCompatibility_of_operator_eq_seed_of_stationary
    K.toSampleKernel hK hstat
omit [Mul Time] in
theorem UniformVorticityTendril.realizes_shiftKernel_pressure_seeded_clause_of_operator_eq_seed_of_stationary
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (K : SeedLiveShiftKernel κ X)
    (hK : ∀ seed live x, K.toSampleKernel.toSeedLiveOperator.operator seed live x = seed x)
    (hstat : ∀ t x, T.vorticity 1 x = T.vorticity t x) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X)
      (pressureSeededPredicateKit
        (Time := Time) (X := X) (T.seedLiveOperatorInitialSlice K.toSampleKernel.toSeedLiveOperator)) :=
  T.realizes_shiftKernel_pressure_seeded_clause_of_selfCompatibility K
    (T.shiftKernelCandidate_has_selfCompatibility_of_operator_eq_seed_of_stationary
      K hK hstat)
omit [Mul Time] in
theorem UniformVorticityTendril.realizes_shiftKernel_pressure_seeded_clause_of_zero_vorticity
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (K : SeedLiveShiftKernel κ X)
    (hzero : ∀ t x, T.vorticity t x = 0) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X)
      (pressureSeededPredicateKit
        (Time := Time) (X := X) (T.seedLiveOperatorInitialSlice K.toSampleKernel.toSeedLiveOperator)) :=
  T.realizes_shiftKernel_pressure_seeded_clause_of_selfCompatibility K
    (T.shiftKernelCandidate_has_selfCompatibility_of_zero_vorticity K hzero)
omit [Mul Time] in
theorem UniformVorticityTendril.toShiftKernelBridge_retains_uniform_vorticity
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (K : SeedLiveShiftKernel κ X) :
    ∀ t x, |T.vorticity t x| ≤ T.envelope :=
  (T.toShiftKernelBridge K).retains_uniform_vorticity

/-- A concrete same-shift live/seed blend kernel. -/
def diagonalShiftKernel (s : X) (a b : ℝ) : SeedLiveShiftKernel Unit X where
  seedShift := fun _ => s
  liveShift := fun _ => s
  seedCoeff := fun _ => a
  liveCoeff := fun _ => b

section Anchored

/-- A three-term translation kernel recovering the anchored blend
`a * live x + b * seed (x + s) + c * live (x + s)`. -/
def anchoredTranslationShiftKernel (s : X) (a b c : ℝ) :
    SeedLiveShiftKernel (Fin 3) X where
  seedShift
    | 0 => 0
    | 1 => s
    | 2 => 0
  liveShift
    | 0 => 0
    | 1 => 0
    | 2 => s
  seedCoeff
    | 0 => 0
    | 1 => b
    | 2 => 0
  liveCoeff
    | 0 => a
    | 1 => 0
    | 2 => c

omit [Mul Time] in
theorem UniformVorticityTendril.seedLiveOperatorInitialSlice_anchoredTranslationShiftKernel_eq_anchoredSeedLiveBlend
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (s : X) (a b c : ℝ) :
    T.seedLiveOperatorInitialSlice
        ((anchoredTranslationShiftKernel (X := X) s a b c).toSampleKernel.toSeedLiveOperator) =
      T.seedLiveOperatorInitialSlice (anchoredSeedLiveBlendOperator (X := X) (fun x => x + s) a b c) := by
  funext x
  simp [UniformVorticityTendril.seedLiveOperatorInitialSlice,
    SeedLiveShiftKernel.toSampleKernel, SeedLiveSampleKernel.toSeedLiveOperator,
    anchoredTranslationShiftKernel, anchoredSeedLiveBlendOperator, Fin.sum_univ_three,
    add_zero, add_assoc, add_left_comm, add_comm,
    mul_comm]

omit [Mul Time] in
theorem UniformVorticityTendril.seedLiveOperatorCandidate_anchoredTranslationShiftKernel_eq_anchoredSeedLiveBlend
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (s : X) (a b c : ℝ) :
    T.seedLiveOperatorCandidate
        ((anchoredTranslationShiftKernel (X := X) s a b c).toSampleKernel.toSeedLiveOperator) =
      T.seedLiveOperatorCandidate (anchoredSeedLiveBlendOperator (X := X) (fun x => x + s) a b c) := by
  unfold UniformVorticityTendril.seedLiveOperatorCandidate
  congr
  funext t x
  simp [SeedLiveShiftKernel.toSampleKernel, SeedLiveSampleKernel.toSeedLiveOperator,
    anchoredTranslationShiftKernel, anchoredSeedLiveBlendOperator, Fin.sum_univ_three,
    add_zero, add_assoc, add_left_comm, add_comm,
    mul_comm]

end Anchored

end SeedLiveShiftKernelFrontier

end NavierStokes
end FluidDynamics
end Mettapedia
