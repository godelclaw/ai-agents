import Mettapedia.FluidDynamics.NavierStokes.FeffermanSeedLiveOperatorFrontier

/-!
# Seed/Live Sample-Kernel Pressure-Seeded Frontier

This file specializes the non-pointwise operator shell to a finite sampled
kernel family.  The candidate at `x` is a finite linear combination of seeded
and live samples taken at anchor maps.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section SeedLiveSampleKernelFrontier

variable {Time X ι G κ : Type*}
variable [Fintype ι] [One Time] [Mul Time] [Fintype κ]
variable {radius statistic : G → ℝ}

/-- Finite sampled kernel mixing seeded and live samples via anchor maps. -/
structure SeedLiveSampleKernel (κ X : Type*) [Fintype κ] where
  seedAnchor : κ → X → X
  liveAnchor : κ → X → X
  seedCoeff : κ → ℝ
  liveCoeff : κ → ℝ

/-- Total absolute kernel mass controlling the uniform envelope bound. -/
def SeedLiveSampleKernel.mass (K : SeedLiveSampleKernel κ X) : ℝ :=
  ∑ i, (|K.seedCoeff i| + |K.liveCoeff i|)

theorem SeedLiveSampleKernel.mass_nonneg (K : SeedLiveSampleKernel κ X) : 0 ≤ K.mass := by
  refine Finset.sum_nonneg ?_
  intro i hi
  exact add_nonneg (abs_nonneg _) (abs_nonneg _)

/-- Every sampled kernel induces a seed/live operator. -/
def SeedLiveSampleKernel.toSeedLiveOperator (K : SeedLiveSampleKernel κ X) :
    SeedLiveOperator X where
  operator := fun seed live x =>
    ∑ i, (K.seedCoeff i * seed (K.seedAnchor i x) + K.liveCoeff i * live (K.liveAnchor i x))
  coeff := K.mass
  coeff_nonneg := K.mass_nonneg
  bound := by
    intro seed live Bseed Blive hBseed hBlive hseed hlive x
    calc
      |∑ i, (K.seedCoeff i * seed (K.seedAnchor i x) + K.liveCoeff i * live (K.liveAnchor i x))|
          ≤ ∑ i, |K.seedCoeff i * seed (K.seedAnchor i x) + K.liveCoeff i * live (K.liveAnchor i x)| := by
            simpa using (Finset.abs_sum_le_sum_abs
              (s := Finset.univ)
              (f := fun i : κ =>
                K.seedCoeff i * seed (K.seedAnchor i x) +
                  K.liveCoeff i * live (K.liveAnchor i x)))
      _ ≤ ∑ i, (|K.seedCoeff i| * Bseed + |K.liveCoeff i| * Blive) := by
            refine Finset.sum_le_sum ?_
            intro i hi
            have hseedi :
                |K.seedCoeff i * seed (K.seedAnchor i x)| ≤ |K.seedCoeff i| * Bseed := by
              calc
                |K.seedCoeff i * seed (K.seedAnchor i x)|
                    = |K.seedCoeff i| * |seed (K.seedAnchor i x)| := by rw [abs_mul]
                _ ≤ |K.seedCoeff i| * Bseed := by
                  exact mul_le_mul_of_nonneg_left (hseed (K.seedAnchor i x)) (abs_nonneg _)
            have hlivei :
                |K.liveCoeff i * live (K.liveAnchor i x)| ≤ |K.liveCoeff i| * Blive := by
              calc
                |K.liveCoeff i * live (K.liveAnchor i x)|
                    = |K.liveCoeff i| * |live (K.liveAnchor i x)| := by rw [abs_mul]
                _ ≤ |K.liveCoeff i| * Blive := by
                  exact mul_le_mul_of_nonneg_left (hlive (K.liveAnchor i x)) (abs_nonneg _)
            calc
              |K.seedCoeff i * seed (K.seedAnchor i x) + K.liveCoeff i * live (K.liveAnchor i x)|
                  ≤ |K.seedCoeff i * seed (K.seedAnchor i x)|
                    + |K.liveCoeff i * live (K.liveAnchor i x)| := by
                      simpa using abs_add_le
                        (K.seedCoeff i * seed (K.seedAnchor i x))
                        (K.liveCoeff i * live (K.liveAnchor i x))
              _ ≤ |K.seedCoeff i| * Bseed + |K.liveCoeff i| * Blive := add_le_add hseedi hlivei
      _ ≤ ∑ i, (|K.seedCoeff i| + |K.liveCoeff i|) * (Bseed + Blive) := by
            refine Finset.sum_le_sum ?_
            intro i hi
            have ha : 0 ≤ |K.seedCoeff i| := abs_nonneg _
            have hb : 0 ≤ |K.liveCoeff i| := abs_nonneg _
            nlinarith [hBseed, hBlive]
      _ = K.mass * (Bseed + Blive) := by
            simpa [SeedLiveSampleKernel.mass] using
              (Finset.sum_mul
                (s := Finset.univ)
                (f := fun i : κ => |K.seedCoeff i| + |K.liveCoeff i|)
                (a := Bseed + Blive)).symm

/-- Exact sampled-kernel compatibility predicate. -/
def sampleKernelCompatibilityPred (K : SeedLiveSampleKernel κ X) :
    VorticityCompatibilityPred (Time := Time) (X := X) :=
  seedLiveOperatorCompatibilityPred (Time := Time) (X := X) K.toSeedLiveOperator

/-- Every sampled kernel therefore reaches the same operator frontier. -/
def UniformVorticityTendril.toSampleKernelAlmostBridge
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (K : SeedLiveSampleKernel κ X) :
    AlmostFeffermanBridge
      (K := pressureSeededPredicateKit
        (Time := Time) (X := X) (T.seedLiveOperatorInitialSlice K.toSeedLiveOperator)) T :=
  T.toSeedLiveOperatorAlmostBridge K.toSeedLiveOperator

/- Same-route version: self-compatibility is still the only remaining mouth. -/
omit [Mul Time] in
theorem UniformVorticityTendril.realizes_pressure_seeded_clause_of_sampleKernelSelfCompatibility
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (K : SeedLiveSampleKernel κ X)
    (hcompat : selfCompatibility (Time := Time) (X := X)
      T (T.seedLiveOperatorCandidate K.toSeedLiveOperator).velocity) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X)
      (pressureSeededPredicateKit
        (Time := Time) (X := X) (T.seedLiveOperatorInitialSlice K.toSeedLiveOperator)) :=
  T.realizes_pressure_seeded_clause_of_seedLiveOperatorSelfCompatibility K.toSeedLiveOperator hcompat

omit [Mul Time] in
theorem UniformVorticityTendril.sampleKernelCandidate_has_selfCompatibility_of_zero_vorticity
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (K : SeedLiveSampleKernel κ X)
    (hzero : ∀ t x, T.vorticity t x = 0) :
    selfCompatibility (Time := Time) (X := X)
      T (T.seedLiveOperatorCandidate K.toSeedLiveOperator).velocity :=
  T.seedLiveOperatorCandidate_has_selfCompatibility_of_zero_vorticity K.toSeedLiveOperator
    (by
      intro x
      simp [SeedLiveSampleKernel.toSeedLiveOperator])
    hzero

/-- Descendant-route closure for the exact sampled-kernel compatibility. -/
def UniformVorticityTendril.toSampleKernelBridge
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (K : SeedLiveSampleKernel κ X) :
    TopDownFeffermanBridge
      (pressureSeededPredicateKit
        (Time := Time) (X := X) (T.seedLiveOperatorInitialSlice K.toSeedLiveOperator))
      (sampleKernelCompatibilityPred (Time := Time) (X := X) K) T :=
  T.toSeedLiveOperatorBridge K.toSeedLiveOperator
omit [Mul Time] in
theorem UniformVorticityTendril.realizes_sampleKernel_pressure_seeded_clause
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (K : SeedLiveSampleKernel κ X) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X)
      (pressureSeededPredicateKit
        (Time := Time) (X := X) (T.seedLiveOperatorInitialSlice K.toSeedLiveOperator)) :=
  T.realizes_seedLiveOperator_pressure_seeded_clause K.toSeedLiveOperator
omit [Mul Time] in
theorem UniformVorticityTendril.realizes_sampleKernel_pressure_seeded_clause_of_selfCompatibility
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (K : SeedLiveSampleKernel κ X)
    (hcompat : selfCompatibility (Time := Time) (X := X)
      T (T.seedLiveOperatorCandidate K.toSeedLiveOperator).velocity) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X)
      (pressureSeededPredicateKit
        (Time := Time) (X := X) (T.seedLiveOperatorInitialSlice K.toSeedLiveOperator)) :=
  T.realizes_pressure_seeded_clause_of_sampleKernelSelfCompatibility K hcompat

omit [Mul Time] in
theorem UniformVorticityTendril.sampleKernelCandidate_has_selfCompatibility_of_operator_eq_live
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (K : SeedLiveSampleKernel κ X)
    (hK : ∀ seed live x, K.toSeedLiveOperator.operator seed live x = live x) :
    selfCompatibility (Time := Time) (X := X)
      T (T.seedLiveOperatorCandidate K.toSeedLiveOperator).velocity :=
  T.seedLiveOperatorCandidate_has_selfCompatibility_of_operator_eq_live
    K.toSeedLiveOperator hK
omit [Mul Time] in
theorem UniformVorticityTendril.realizes_sampleKernel_pressure_seeded_clause_of_operator_eq_live
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (K : SeedLiveSampleKernel κ X)
    (hK : ∀ seed live x, K.toSeedLiveOperator.operator seed live x = live x) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X)
      (pressureSeededPredicateKit
        (Time := Time) (X := X) (T.seedLiveOperatorInitialSlice K.toSeedLiveOperator)) :=
  T.realizes_sampleKernel_pressure_seeded_clause_of_selfCompatibility K
    (T.sampleKernelCandidate_has_selfCompatibility_of_operator_eq_live K hK)

omit [Mul Time] in
theorem UniformVorticityTendril.sampleKernelCandidate_has_selfCompatibility_of_operator_eq_seed_of_stationary
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (K : SeedLiveSampleKernel κ X)
    (hK : ∀ seed live x, K.toSeedLiveOperator.operator seed live x = seed x)
    (hstat : ∀ t x, T.vorticity 1 x = T.vorticity t x) :
    selfCompatibility (Time := Time) (X := X)
      T (T.seedLiveOperatorCandidate K.toSeedLiveOperator).velocity :=
  T.seedLiveOperatorCandidate_has_selfCompatibility_of_operator_eq_seed_of_stationary
    K.toSeedLiveOperator hK hstat
omit [Mul Time] in
theorem UniformVorticityTendril.realizes_sampleKernel_pressure_seeded_clause_of_operator_eq_seed_of_stationary
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (K : SeedLiveSampleKernel κ X)
    (hK : ∀ seed live x, K.toSeedLiveOperator.operator seed live x = seed x)
    (hstat : ∀ t x, T.vorticity 1 x = T.vorticity t x) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X)
      (pressureSeededPredicateKit
        (Time := Time) (X := X) (T.seedLiveOperatorInitialSlice K.toSeedLiveOperator)) :=
  T.realizes_sampleKernel_pressure_seeded_clause_of_selfCompatibility K
    (T.sampleKernelCandidate_has_selfCompatibility_of_operator_eq_seed_of_stationary
      K hK hstat)
omit [Mul Time] in
theorem UniformVorticityTendril.realizes_sampleKernel_pressure_seeded_clause_of_zero_vorticity
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (K : SeedLiveSampleKernel κ X)
    (hzero : ∀ t x, T.vorticity t x = 0) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X)
      (pressureSeededPredicateKit
        (Time := Time) (X := X) (T.seedLiveOperatorInitialSlice K.toSeedLiveOperator)) :=
  T.realizes_sampleKernel_pressure_seeded_clause_of_selfCompatibility K
    (T.sampleKernelCandidate_has_selfCompatibility_of_zero_vorticity K hzero)
omit [Mul Time] in
theorem UniformVorticityTendril.toSampleKernelBridge_retains_uniform_vorticity
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (K : SeedLiveSampleKernel κ X) :
    ∀ t x, |T.vorticity t x| ≤ T.envelope :=
  (T.toSampleKernelBridge K).retains_uniform_vorticity

/-- Single-sample kernel recovering the affine seed/live blend. -/
def diagonalSampleKernel (a b : ℝ) : SeedLiveSampleKernel Unit X where
  seedAnchor := fun _ x => x
  liveAnchor := fun _ x => x
  seedCoeff := fun _ => b
  liveCoeff := fun _ => a

omit [Mul Time] in
theorem UniformVorticityTendril.seedLiveOperatorInitialSlice_diagonalSampleKernel_eq_seedBlendInitialSlice
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (a b : ℝ) :
    T.seedLiveOperatorInitialSlice (diagonalSampleKernel (X := X) a b).toSeedLiveOperator =
      T.seedBlendInitialSlice a b := by
  funext x
  simp [UniformVorticityTendril.seedLiveOperatorInitialSlice,
    UniformVorticityTendril.seedBlendInitialSlice, SeedLiveSampleKernel.toSeedLiveOperator,
    diagonalSampleKernel]
  ring

omit [Mul Time] in
theorem UniformVorticityTendril.seedLiveOperatorCandidate_diagonalSampleKernel_eq_seedBlendCandidate
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (a b : ℝ) :
    T.seedLiveOperatorCandidate (diagonalSampleKernel (X := X) a b).toSeedLiveOperator =
      T.seedBlendCandidate a b := by
  unfold UniformVorticityTendril.seedLiveOperatorCandidate UniformVorticityTendril.seedBlendCandidate
  congr
  funext t x
  simp [SeedLiveSampleKernel.toSeedLiveOperator, diagonalSampleKernel]
  ring

omit [Mul Time] in
theorem diagonalSampleKernelCompatibilityPred_iff_seedBlendCompatibilityPred
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (u : Time → X → ℝ)
    (a b : ℝ) :
    sampleKernelCompatibilityPred (Time := Time) (X := X)
        (diagonalSampleKernel (X := X) a b) T u
      ↔
    seedBlendCompatibilityPred (Time := Time) (X := X) a b T u := by
  constructor <;> intro h t x
  · specialize h t x
    simpa [sampleKernelCompatibilityPred, seedLiveOperatorCompatibilityPred,
      diagonalSampleKernel, SeedLiveSampleKernel.toSeedLiveOperator,
      seedBlendCompatibilityPred, add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc] using h
  · specialize h t x
    simpa [sampleKernelCompatibilityPred, seedLiveOperatorCompatibilityPred,
      diagonalSampleKernel, SeedLiveSampleKernel.toSeedLiveOperator,
      seedBlendCompatibilityPred, add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc] using h
omit [Mul Time] in
theorem UniformVorticityTendril.toSampleKernelBridge_diagonalSampleKernel_realizes_seedBlend_clause
    (T : UniformVorticityTendril (Time := Time) (X := X))
    (a b : ℝ) :
    FeffermanGlobalRegularityClause
      (Time := Time) (X := X)
      (pressureSeededPredicateKit (Time := Time) (X := X) (T.seedBlendInitialSlice a b)) := by
  simpa [UniformVorticityTendril.seedLiveOperatorInitialSlice_diagonalSampleKernel_eq_seedBlendInitialSlice
      (T := T) (a := a) (b := b)]
    using
      (T.realizes_sampleKernel_pressure_seeded_clause
        (K := diagonalSampleKernel (X := X) a b))

end SeedLiveSampleKernelFrontier

end NavierStokes
end FluidDynamics
end Mettapedia
