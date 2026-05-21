import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMContinuationTarget
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatScaledSeededFrontier
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatScaledPressureSeededFrontier
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSeedLiveProfileFrontier
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSeedLiveOperatorFrontier
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSampleKernelFrontier
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatIdentitySampleKernelObstruction
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatShiftKernelFrontier
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSaturatedShiftKernelConstantMagnitudeFrontier
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSaturatedShiftKernelInvariantFrontier
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSaturatedShiftKernelInvariantObstruction
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSaturatedAnchoredShiftInvariantFrontier
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSaturatedAnchoredShiftInvariantObstruction
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSaturatedMaskedShiftKernelFrontier
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSaturatedIdentitySampleKernelFrontier
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSaturatedDiagonalSampleKernelFrontier

/-!
# Navier-Stokes Continuation Regression

Small theorem-level checks for the repaired and unrepaired continuation exports.

Positive examples:
- zero initial data satisfy the repaired regularity surface;
- explicit and structured whole-space theorem targets transport directly to
  fixed-horizon unrepaired and repaired continuation clauses.

Negative examples:
- the original whole-space theorem targets are false as stated;
- the repaired explicit regularity clause is vacuous on non-finite-energy
  constant and linear-shear data while the unrepaired concrete clause is false;
- nonzero constant and linear-shear data are not finite-energy and therefore
  still vacuously satisfy the repaired continuation clauses, while the
  unrepaired clauses remain vacuous on nonnegative slabs because no finite-time
  witness exists there.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace ContinuationRegression

section WindowedColeHopfHeatScaledSeeded

variable {ι X : Type*}
variable [Fintype ι]

theorem windowed_heat_scaled_seeded_compatibility_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState) :
    windowedScaledCompatibilityPred (X := X) a
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
      (L.windowedColeHopfHeatScaledCandidate
        (ι := ι) (X := X)
        selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity := by
  exact
    L.windowedColeHopfHeatScaledCandidate_has_scaledCompatibility
      (ι := ι) (X := X)
      selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x

theorem windowed_heat_scaled_seeded_clause_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState) :
    FeffermanGlobalRegularityClause
      (L.windowedColeHopfHeatScaledSeededPredicateKit
        (ι := ι) (X := X)
        selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x) := by
  exact
    L.windowedColeHopfHeat_realizes_scaled_seeded_clause
      (ι := ι) (X := X)
      selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x

theorem windowed_heat_scaled_seeded_bridge_retains_uniform_vorticity_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState) :
    ∀ t y,
      |(L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y| ≤
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).envelope := by
  exact
    L.toWindowedColeHopfHeatScaledSeededBridge_retains_uniform_vorticity
      (ι := ι) (X := X)
      selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x

end WindowedColeHopfHeatScaledSeeded

section WindowedColeHopfHeatScaledPressureSeeded

variable {ι X : Type*}
variable [Fintype ι]

theorem windowed_heat_scaled_pressure_seeded_selfCompatibility_of_one_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState) :
    selfCompatibility (Time := NNReal) (X := X)
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
      (L.windowedColeHopfHeatScaledPressureSeededCandidate
        (ι := ι) (X := X)
        selector (1 : ℝ) c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity := by
  exact
    L.windowedColeHopfHeatScaledPressureSeededCandidate_has_selfCompatibility_of_one
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x

theorem windowed_heat_scaled_pressure_seeded_clause_of_one_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatScaledPressureSeededInitialSlice
          (ι := ι) (X := X)
          selector (1 : ℝ) c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) := by
  exact
    L.windowedColeHopfHeat_realizes_scaled_pressure_seeded_clause_of_one
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x

theorem windowed_heat_scaled_pressure_seeded_clause_of_zero_vorticity_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hzero :
      ∀ t y,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y = 0) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatScaledPressureSeededInitialSlice
          (ι := ι) (X := X)
          selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) := by
  exact
    L.windowedColeHopfHeat_realizes_scaled_pressure_seeded_clause_of_zero_vorticity
      (ι := ι) (X := X)
      selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hzero

end WindowedColeHopfHeatScaledPressureSeeded

section WindowedColeHopfHeatSeedLiveProfile

variable {ι X : Type*}
variable [Fintype ι]

theorem windowed_heat_seedLive_profile_eq_live_clause_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (P : SeedLiveProfile)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hP : ∀ seed live, P.profile seed live = live) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatSeedLiveInitialSlice
          (ι := ι) (X := X)
          selector P c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) := by
  exact
    L.windowedColeHopfHeat_realizes_seedLive_pressure_seeded_clause_of_profile_eq_live
      (ι := ι) (X := X)
      selector P c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hP

theorem windowed_heat_seedLive_profile_eq_seed_stationary_clause_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (P : SeedLiveProfile)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hP : ∀ seed live, P.profile seed live = seed)
    (hstat :
      ∀ t y,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatSeedLiveInitialSlice
          (ι := ι) (X := X)
          selector P c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) := by
  exact
    L.windowedColeHopfHeat_realizes_seedLive_pressure_seeded_clause_of_profile_eq_seed_of_stationary
      (ι := ι) (X := X)
      selector P c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hP hstat

theorem windowed_heat_seedLive_zero_vorticity_clause_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (P : SeedLiveProfile)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hP0 : P.profile 0 0 = 0)
    (hzero :
      ∀ t y,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y = 0) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatSeedLiveInitialSlice
          (ι := ι) (X := X)
          selector P c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) := by
  exact
    L.windowedColeHopfHeat_realizes_seedLive_pressure_seeded_clause_of_zero_vorticity
      (ι := ι) (X := X)
      selector P c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hP0 hzero

theorem windowed_heat_seedLive_bridge_retains_uniform_vorticity_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (P : SeedLiveProfile)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState) :
    ∀ t y,
      |(L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y| ≤
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).envelope := by
  exact
    L.toWindowedColeHopfHeatSeedLiveBridge_retains_uniform_vorticity
      (ι := ι) (X := X)
      selector P c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x

end WindowedColeHopfHeatSeedLiveProfile

section WindowedColeHopfHeatSeedLiveOperator

variable {ι X : Type*}
variable [Fintype ι] [AddMonoid X]

omit [AddMonoid X] in
theorem windowed_heat_seedLiveOperator_operator_eq_live_clause_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (O : SeedLiveOperator X)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hO : ∀ seed live y, O.operator seed live y = live y) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatSeedLiveOperatorInitialSlice
          (ι := ι) (X := X)
          selector O c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) := by
  exact
    L.windowedColeHopfHeat_realizes_seedLiveOperator_pressure_seeded_clause_of_operator_eq_live
      (ι := ι) (X := X)
      selector O c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hO

omit [AddMonoid X] in
theorem windowed_heat_seedLiveOperator_zero_vorticity_clause_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (O : SeedLiveOperator X)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hO0 : ∀ y, O.operator (fun _ => 0) (fun _ => 0) y = 0)
    (hzero :
      ∀ t y,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y = 0) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatSeedLiveOperatorInitialSlice
          (ι := ι) (X := X)
          selector O c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) := by
  exact
    L.windowedColeHopfHeat_realizes_seedLiveOperator_pressure_seeded_clause_of_zero_vorticity
      (ι := ι) (X := X)
      selector O c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hO0 hzero

omit [AddMonoid X] in
theorem windowed_heat_seedLiveOperator_operator_eq_seed_stationary_clause_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (O : SeedLiveOperator X)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hO : ∀ seed live y, O.operator seed live y = seed y)
    (hstat :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatSeedLiveOperatorInitialSlice
          (ι := ι) (X := X)
          selector O c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) := by
  exact
    L.windowedColeHopfHeat_realizes_seedLiveOperator_pressure_seeded_clause_of_operator_eq_seed_of_stationary
      (ι := ι) (X := X)
      selector O c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
      hO hstat

omit [AddMonoid X] in
theorem windowed_heat_seedLiveOperator_bridge_retains_uniform_vorticity_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (O : SeedLiveOperator X)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState) :
    ∀ t y,
      |(L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y| ≤
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).envelope := by
  exact
    L.toWindowedColeHopfHeatSeedLiveOperatorBridge_retains_uniform_vorticity
      (ι := ι) (X := X)
      selector O c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x

end WindowedColeHopfHeatSeedLiveOperator

section WindowedColeHopfHeatSampleKernel

variable {ι X κ : Type*}
variable [Fintype ι] [Fintype κ]

theorem windowed_heat_sampleKernel_live_clause_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveSampleKernel κ X)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hK : ∀ seed live y, K.toSeedLiveOperator.operator seed live y = live y) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatSampleKernelInitialSlice
          (ι := ι) (X := X)
          selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) := by
  exact
    L.windowedColeHopfHeat_realizes_sampleKernel_pressure_seeded_clause_of_operator_eq_live
      (ι := ι) (X := X)
      selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hK

theorem windowed_heat_sampleKernel_zero_vorticity_clause_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveSampleKernel κ X)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hzero :
      ∀ t y,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y = 0) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatSampleKernelInitialSlice
          (ι := ι) (X := X)
          selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) := by
  exact
    L.windowedColeHopfHeat_realizes_sampleKernel_pressure_seeded_clause_of_zero_vorticity
      (ι := ι) (X := X)
      selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hzero

theorem windowed_heat_sampleKernel_seed_stationary_clause_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveSampleKernel κ X)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hK : ∀ seed live y, K.toSeedLiveOperator.operator seed live y = seed y)
    (hstat :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatSampleKernelInitialSlice
          (ι := ι) (X := X)
          selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) := by
  exact
    L.windowedColeHopfHeat_realizes_sampleKernel_pressure_seeded_clause_of_operator_eq_seed_of_stationary
      (ι := ι) (X := X)
      selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
      hK hstat

theorem windowed_heat_sampleKernel_bridge_retains_uniform_vorticity_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveSampleKernel κ X)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState) :
    ∀ t y,
      |(L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y| ≤
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).envelope := by
  exact
    L.toWindowedColeHopfHeatSampleKernelBridge_retains_uniform_vorticity
      (ι := ι) (X := X)
      selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x

theorem windowed_heat_diagonal_sampleKernel_initialSlice_eq_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a b c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState) :
    L.windowedColeHopfHeatSampleKernelInitialSlice
      (ι := ι) (X := X)
      selector (diagonalSampleKernel (X := X) a b) c ν hc hν
      curlFrame curlBound curlBound_nonneg hcurl x =
    L.windowedColeHopfHeatSeedBlendInitialSlice
      (ι := ι) (X := X)
      selector a b c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  exact
    L.windowedColeHopfHeatDiagonalSampleKernelInitialSlice_eq_seedBlendInitialSlice
      (ι := ι) (X := X)
      selector a b c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x

theorem windowed_heat_diagonal_sampleKernel_candidate_eq_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a b c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState) :
    L.windowedColeHopfHeatSampleKernelCandidate
      (ι := ι) (X := X)
      selector (diagonalSampleKernel (X := X) a b) c ν hc hν
      curlFrame curlBound curlBound_nonneg hcurl x =
    L.windowedColeHopfHeatSeedBlendCandidate
      (ι := ι) (X := X)
      selector a b c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  exact
    L.windowedColeHopfHeatDiagonalSampleKernelCandidate_eq_seedBlendCandidate
      (ι := ι) (X := X)
      selector a b c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x

theorem windowed_heat_diagonal_sampleKernel_seedBlend_clause_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatSeedBlendInitialSlice
          (ι := ι) (X := X)
          selector (1 : ℝ) 0 c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) := by
  exact
    L.windowedColeHopfHeat_realizes_diagonalSampleKernel_pressure_seeded_clause_of_seedBlendSelfCompatibility
      (ι := ι) (X := X)
      selector (1 : ℝ) 0 c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
      (L.windowedColeHopfHeatSeedBlendCandidate_has_selfCompatibility_of_one_zero
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)

theorem windowed_heat_diagonal_sampleKernel_live_endpoint_clause_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatSeedBlendInitialSlice
          (ι := ι) (X := X)
          selector (1 : ℝ) 0 c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) := by
  exact
    L.windowedColeHopfHeat_realizes_diagonalSampleKernel_pressure_seeded_clause_of_live_endpoint
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x

theorem windowed_heat_diagonal_sampleKernel_zero_vorticity_clause_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a b c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hzero :
      ∀ t y,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y = 0) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatSeedBlendInitialSlice
          (ι := ι) (X := X)
          selector a b c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) := by
  exact
    L.windowedColeHopfHeat_realizes_diagonalSampleKernel_pressure_seeded_clause_of_zero_vorticity
      (ι := ι) (X := X)
      selector a b c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hzero

theorem windowed_heat_diagonal_sampleKernel_seed_stationary_clause_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hstat :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatSeedBlendInitialSlice
          (ι := ι) (X := X)
          selector (0 : ℝ) (1 : ℝ) c ν hc hν
          curlFrame curlBound curlBound_nonneg hcurl x)) := by
  exact
    L.windowedColeHopfHeat_realizes_diagonalSampleKernel_pressure_seeded_clause_of_seed_stationary
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hstat

theorem windowed_heat_identitySampleKernel_liveCoeffSum_blocker_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveSampleKernel κ X)
    (c ν : ℝ)
    (hlive : K.liveCoeffSum ≠ 1)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hK : K.IdentityAnchors)
    (hwitness :
      ∃ t y,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y ≠ 0) :
    ¬ ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := X)
            (L.windowedColeHopfHeatSampleKernelInitialSlice
              (ι := ι) (X := X)
              selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
          (windowedSelfCompatibility (X := X))
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatSampleKernelCandidate
            (ι := ι) (X := X)
            selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  exact
    L.not_exists_windowedColeHopfHeatIdentitySampleKernelTopDownBridge_of_liveCoeffSum_ne_one_of_zero_initial_nonzero_live
      (ι := ι) (X := X)
      selector K c ν hlive hc hν curlFrame curlBound curlBound_nonneg hcurl x hK hwitness

theorem windowed_heat_identitySampleKernel_seedCoeffSum_blocker_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveSampleKernel κ X)
    (c ν : ℝ)
    (hseed : K.seedCoeffSum ≠ 0)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hK : K.IdentityAnchors)
    (hwitness :
      ∃ t y,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y = 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y ≠ 0) :
    ¬ ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := X)
            (L.windowedColeHopfHeatSampleKernelInitialSlice
              (ι := ι) (X := X)
              selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
          (windowedSelfCompatibility (X := X))
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatSampleKernelCandidate
            (ι := ι) (X := X)
            selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  exact
    L.not_exists_windowedColeHopfHeatIdentitySampleKernelTopDownBridge_of_seedCoeffSum_ne_zero_of_zero_live_nonzero_initial
      (ι := ι) (X := X)
      selector K c ν hseed hc hν curlFrame curlBound curlBound_nonneg hcurl x hK hwitness

end WindowedColeHopfHeatSampleKernel

section WindowedColeHopfHeatShiftKernel

variable {ι X κ : Type*}
variable [Fintype ι] [Fintype κ] [AddMonoid X]

theorem windowed_heat_shiftKernel_live_clause_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hK : ∀ seed live y, K.toSampleKernel.toSeedLiveOperator.operator seed live y = live y) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatShiftKernelInitialSlice
          (ι := ι) (X := X)
          selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) := by
  exact
    L.windowedColeHopfHeat_realizes_shiftKernel_pressure_seeded_clause_of_operator_eq_live
      (ι := ι) (X := X)
      selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hK

theorem windowed_heat_shiftKernel_zero_vorticity_clause_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hzero :
      ∀ t y,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y = 0) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatShiftKernelInitialSlice
          (ι := ι) (X := X)
          selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) := by
  exact
    L.windowedColeHopfHeat_realizes_shiftKernel_pressure_seeded_clause_of_zero_vorticity
      (ι := ι) (X := X)
      selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hzero

theorem windowed_heat_shiftKernel_seed_stationary_clause_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hK : ∀ seed live y, K.toSampleKernel.toSeedLiveOperator.operator seed live y = seed y)
    (hstat :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatShiftKernelInitialSlice
          (ι := ι) (X := X)
          selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) := by
  exact
    L.windowedColeHopfHeat_realizes_shiftKernel_pressure_seeded_clause_of_operator_eq_seed_of_stationary
      (ι := ι) (X := X)
      selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
      hK hstat

theorem windowed_heat_shiftKernel_bridge_retains_uniform_vorticity_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState) :
    ∀ t y,
      |(L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y| ≤
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).envelope := by
  exact
    L.toWindowedColeHopfHeatShiftKernelBridge_retains_uniform_vorticity
      (ι := ι) (X := X)
      selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x

theorem windowed_heat_anchoredTranslation_shiftKernel_initialSlice_eq_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (a b d c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState) :
    L.windowedColeHopfHeatShiftKernelInitialSlice
      (ι := ι) (X := X)
      selector (anchoredTranslationShiftKernel (X := X) s a b d) c ν hc hν
      curlFrame curlBound curlBound_nonneg hcurl x =
    L.windowedColeHopfHeatAnchoredShiftInitialSlice
      (ι := ι) (X := X)
      selector s a b d c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  exact
    L.windowedColeHopfHeatAnchoredTranslationShiftKernelInitialSlice_eq_anchoredShiftInitialSlice
      (ι := ι) (X := X)
      selector s a b d c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x

theorem windowed_heat_anchoredTranslation_shiftKernel_candidate_eq_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (a b d c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState) :
    L.windowedColeHopfHeatShiftKernelCandidate
      (ι := ι) (X := X)
      selector (anchoredTranslationShiftKernel (X := X) s a b d) c ν hc hν
      curlFrame curlBound curlBound_nonneg hcurl x =
    L.windowedColeHopfHeatAnchoredShiftCandidate
      (ι := ι) (X := X)
      selector s a b d c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  exact
    L.windowedColeHopfHeatAnchoredTranslationShiftKernelCandidate_eq_anchoredShiftCandidate
      (ι := ι) (X := X)
      selector s a b d c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x

theorem windowed_heat_anchoredTranslation_shiftKernel_clause_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (a b d c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatAnchoredShiftInitialSlice
          (ι := ι) (X := X)
          selector s a b d c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) := by
  exact
    L.windowedColeHopfHeat_realizes_anchoredTranslationShiftKernel_pressure_seeded_clause
      (ι := ι) (X := X)
      selector s a b d c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x

theorem windowed_heat_anchoredTranslation_shiftKernel_bridge_retains_uniform_vorticity_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (a b d c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState) :
    ∀ t y,
      |(L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y| ≤
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).envelope := by
  exact
    L.toWindowedColeHopfHeatShiftKernelBridge_retains_uniform_vorticity
      (ι := ι) (X := X)
      selector (anchoredTranslationShiftKernel (X := X) s a b d)
      c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x

theorem windowed_heat_anchoredTranslation_shiftKernel_selfCompatibility_clause_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (a b d c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hself :
      selfCompatibility (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
        (L.windowedColeHopfHeatAnchoredShiftCandidate
          (ι := ι) (X := X)
          selector s a b d c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatAnchoredShiftInitialSlice
          (ι := ι) (X := X)
          selector s a b d c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) := by
  exact
    L.windowedColeHopfHeat_realizes_anchoredTranslationShiftKernel_pressure_seeded_clause_of_anchoredShiftSelfCompatibility
      (ι := ι) (X := X)
      selector s a b d c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hself

theorem windowed_heat_anchoredTranslation_shiftKernel_zero_vorticity_clause_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (a b d c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hzero :
      ∀ t y,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y = 0) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatAnchoredShiftInitialSlice
          (ι := ι) (X := X)
          selector s a b d c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) := by
  exact
    L.windowedColeHopfHeat_realizes_anchoredTranslationShiftKernel_pressure_seeded_clause_of_zero_vorticity
      (ι := ι) (X := X)
      selector s a b d c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hzero

theorem windowed_heat_anchoredTranslation_shiftKernel_live_clause_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (a b d c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hK :
      ∀ seed live y,
        ((anchoredTranslationShiftKernel (X := X) s a b d).toSampleKernel.toSeedLiveOperator).operator
          seed live y = live y) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatAnchoredShiftInitialSlice
          (ι := ι) (X := X)
          selector s a b d c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) := by
  exact
    L.windowedColeHopfHeat_realizes_anchoredTranslationShiftKernel_pressure_seeded_clause_of_operator_eq_live
      (ι := ι) (X := X)
      selector s a b d c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hK

theorem windowed_heat_anchoredTranslation_shiftKernel_seed_stationary_clause_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (a b d c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hK :
      ∀ seed live y,
        ((anchoredTranslationShiftKernel (X := X) s a b d).toSampleKernel.toSeedLiveOperator).operator
          seed live y = seed y)
    (hstat :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatAnchoredShiftInitialSlice
          (ι := ι) (X := X)
          selector s a b d c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) := by
  exact
    L.windowedColeHopfHeat_realizes_anchoredTranslationShiftKernel_pressure_seeded_clause_of_operator_eq_seed_of_stationary
      (ι := ι) (X := X)
      selector s a b d c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
      hK hstat

end WindowedColeHopfHeatShiftKernel

section WindowedColeHopfHeatSaturatedShiftKernelConstantMagnitude

variable {ι X : Type*}
variable [Fintype ι] [AddMonoid X]

theorem windowed_heat_saturated_constantMagnitude_shiftKernel_initialSlice_eq_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (habs :
      ∀ y,
        |(L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y| = r) :
    L.windowedColeHopfHeatShiftKernelInitialSlice
      (ι := ι) (X := X)
      selector (saturatedConstantMagnitudeShiftKernel X a r) c ν hc hν
      curlFrame curlBound curlBound_nonneg hcurl x =
    (L.windowedColeHopfHeatUniformVorticityTendril
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).saturatedInitialSlice a := by
  exact
    L.windowedColeHopfHeatSaturatedConstantMagnitudeShiftKernelInitialSlice_eq_saturatedInitialSlice
      (ι := ι) (X := X)
      selector a r c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x habs

theorem windowed_heat_saturated_constantMagnitude_shiftKernel_candidate_eq_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (habs :
      ∀ t y,
        |(L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y| = r) :
    L.windowedColeHopfHeatShiftKernelCandidate
      (ι := ι) (X := X)
      selector (saturatedConstantMagnitudeShiftKernel X a r) c ν hc hν
      curlFrame curlBound curlBound_nonneg hcurl x =
    L.windowedColeHopfHeatSaturatedCandidate
      (ι := ι) (X := X)
      selector a c ν hc hν
      curlFrame curlBound curlBound_nonneg hcurl x := by
  exact
    L.windowedColeHopfHeatSaturatedConstantMagnitudeShiftKernelCandidate_eq_saturatedCandidate
      (ι := ι) (X := X)
      selector a r c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x habs

theorem windowed_heat_saturated_constantMagnitude_shiftKernel_clause_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (habs :
      ∀ t y,
        |(L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y| = r) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatSaturatedInitialSlice
          (ι := ι) (X := X)
          selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) := by
  exact
    L.windowedColeHopfHeat_realizes_saturated_pressure_seeded_clause_via_constantMagnitudeShiftKernel
      (ι := ι) (X := X)
      selector a r c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x habs

theorem windowed_heat_saturated_constantMagnitude_shiftKernel_bridge_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (habs :
      ∀ t y,
        |(L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y| = r) :
    ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := X)
            (L.windowedColeHopfHeatShiftKernelInitialSlice
              (ι := ι) (X := X)
              selector (saturatedConstantMagnitudeShiftKernel X a r) c ν hc hν
              curlFrame curlBound curlBound_nonneg hcurl x))
          (shiftKernelCompatibilityPred
            (Time := NNReal) (X := X) (saturatedConstantMagnitudeShiftKernel X a r))
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatSaturatedCandidate
            (ι := ι) (X := X)
            selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  exact
    L.exists_windowedColeHopfHeatSaturatedConstantMagnitudeShiftKernelBridge
      (ι := ι) (X := X)
      selector a r c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x habs

end WindowedColeHopfHeatSaturatedShiftKernelConstantMagnitude

section WindowedColeHopfHeatSaturatedShiftKernelInvariant

variable {ι X κ : Type*}
variable [Fintype ι] [Fintype κ] [AddMonoid X]

theorem windowed_heat_saturated_shiftKernel_invariant_initialSlice_eq_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (a r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hcoeff : SeedLiveShiftKernel.totalCoeffSum K = a / (1 + r))
    (hseedInv :
      ∀ i : κ, ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y + K.seedShift i) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hliveInv :
      ∀ i : κ, ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y + K.liveShift i) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (habs :
      ∀ t : NNReal, ∀ y : X,
        |(L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y| = r) :
    L.windowedColeHopfHeatShiftKernelInitialSlice
      (ι := ι) (X := X)
      selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x =
    (L.windowedColeHopfHeatUniformVorticityTendril
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).saturatedInitialSlice a := by
  exact
    L.windowedColeHopfHeatSaturatedShiftKernelInitialSlice_eq_saturatedInitialSlice_of_shiftInvariant_constantMagnitude
      (ι := ι) (X := X)
      selector K a r c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
      hcoeff hseedInv hliveInv habs

theorem windowed_heat_saturated_shiftKernel_invariant_candidate_eq_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (a r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hcoeff : SeedLiveShiftKernel.totalCoeffSum K = a / (1 + r))
    (hseedInv :
      ∀ i : κ, ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y + K.seedShift i) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hliveInv :
      ∀ i : κ, ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y + K.liveShift i) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hstat :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (habs :
      ∀ t : NNReal, ∀ y : X,
        |(L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y| = r) :
    L.windowedColeHopfHeatShiftKernelCandidate
      (ι := ι) (X := X)
      selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x =
    L.windowedColeHopfHeatSaturatedCandidate
      (ι := ι) (X := X)
      selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  exact
    L.windowedColeHopfHeatSaturatedShiftKernelCandidate_eq_saturatedCandidate_of_stationary_shiftInvariant_constantMagnitude
      (ι := ι) (X := X)
      selector K a r c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
      hcoeff hseedInv hliveInv hstat habs

theorem windowed_heat_saturated_shiftKernel_invariant_clause_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (a r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hcoeff : SeedLiveShiftKernel.totalCoeffSum K = a / (1 + r))
    (hseedInv :
      ∀ i : κ, ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y + K.seedShift i) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hliveInv :
      ∀ i : κ, ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y + K.liveShift i) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (habs :
      ∀ t : NNReal, ∀ y : X,
        |(L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y| = r) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatSaturatedInitialSlice
          (ι := ι) (X := X)
          selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) := by
  exact
    L.windowedColeHopfHeat_realizes_saturated_pressure_seeded_clause_via_shiftKernel_of_shiftInvariant_constantMagnitude
      (ι := ι) (X := X)
      selector K a r c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
      hcoeff hseedInv hliveInv habs

theorem windowed_heat_saturated_shiftKernel_invariant_candidate_zeroSum_or_abs_eq_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (a c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hseedInv :
      ∀ i : κ, ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y + K.seedShift i) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hliveInv :
      ∀ i : κ, ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y + K.liveShift i) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hstat :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hCand :
      L.windowedColeHopfHeatShiftKernelCandidate
        (ι := ι) (X := X)
        selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x =
      L.windowedColeHopfHeatSaturatedCandidate
        (ι := ι) (X := X)
        selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
    {t₁ t₂ : NNReal} {y₁ y₂ : X}
    (hnz₁ :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₁ y₁ ≠ 0)
    (hnz₂ :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₂ y₂ ≠ 0) :
    SeedLiveShiftKernel.totalCoeffSum K = 0 ∨
      |(L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₁ y₁| =
        |(L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₂ y₂| := by
  exact
    L.windowedColeHopfHeatShiftKernel_totalCoeffSum_zero_or_abs_eq_abs_of_candidate_eq_saturatedCandidate_of_stationary_shiftInvariant
      (ι := ι) (X := X)
      selector K a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
      hseedInv hliveInv hstat hCand hnz₁ hnz₂

theorem windowed_heat_saturated_shiftKernel_invariant_candidate_coeff_formula_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (a c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hseedInv :
      ∀ i : κ, ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y + K.seedShift i) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hliveInv :
      ∀ i : κ, ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y + K.liveShift i) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hstat :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hCand :
      L.windowedColeHopfHeatShiftKernelCandidate
        (ι := ι) (X := X)
        selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x =
      L.windowedColeHopfHeatSaturatedCandidate
        (ι := ι) (X := X)
        selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
    {t : NNReal} {y : X}
    (hnz :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y ≠ 0) :
    SeedLiveShiftKernel.totalCoeffSum K *
        (1 + |(L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y|) =
      a := by
  exact
    L.windowedColeHopfHeatShiftKernel_totalCoeffSum_mul_one_add_abs_eq_saturatedCoeff_of_candidate_eq_saturatedCandidate_of_stationary_shiftInvariant
      (ι := ι) (X := X)
      selector K a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
      hseedInv hliveInv hstat hCand hnz

theorem windowed_heat_saturated_shiftKernel_invariant_candidate_zeroSum_of_abs_ne_abs_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (a c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hseedInv :
      ∀ i : κ, ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y + K.seedShift i) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hliveInv :
      ∀ i : κ, ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y + K.liveShift i) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hstat :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hCand :
      L.windowedColeHopfHeatShiftKernelCandidate
        (ι := ι) (X := X)
        selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x =
      L.windowedColeHopfHeatSaturatedCandidate
        (ι := ι) (X := X)
        selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
    (hwitness :
      ∃ t₁ t₂ y₁ y₂,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₁ y₁ ≠ 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₂ y₂ ≠ 0 ∧
        |(L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₁ y₁| ≠
          |(L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₂ y₂|) :
    SeedLiveShiftKernel.totalCoeffSum K = 0 := by
  exact
    L.windowedColeHopfHeatShiftKernel_totalCoeffSum_zero_of_candidate_eq_saturatedCandidate_of_abs_ne_abs_of_stationary_shiftInvariant
      (ι := ι) (X := X)
      selector K a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
      hseedInv hliveInv hstat hCand hwitness

theorem windowed_heat_saturated_shiftKernel_invariant_no_candidate_of_zeroSum_nonzero_saturatedCoeff_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (a c ν : ℝ)
    (hsum0 : SeedLiveShiftKernel.totalCoeffSum K = 0)
    (ha : a ≠ 0)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hseedInv :
      ∀ i : κ, ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y + K.seedShift i) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hliveInv :
      ∀ i : κ, ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y + K.liveShift i) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hstat :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    {t : NNReal} {y : X}
    (hnz :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y ≠ 0) :
    L.windowedColeHopfHeatShiftKernelCandidate
      (ι := ι) (X := X)
      selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x ≠
    L.windowedColeHopfHeatSaturatedCandidate
      (ι := ι) (X := X)
      selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  exact
    L.not_windowedColeHopfHeatShiftKernelCandidate_eq_saturatedCandidate_of_totalCoeffSum_zero_of_saturatedCoeff_ne_zero_of_stationary_shiftInvariant
      (ι := ι) (X := X)
      selector K a c ν hsum0 ha hc hν curlFrame curlBound curlBound_nonneg hcurl x
      hseedInv hliveInv hstat hnz

theorem windowed_heat_saturated_shiftKernel_invariant_no_candidate_of_nonpos_sum_pos_saturatedCoeff_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (a c ν : ℝ)
    (hsum_nonpos : SeedLiveShiftKernel.totalCoeffSum K ≤ 0)
    (ha : 0 < a)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hseedInv :
      ∀ i : κ, ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y + K.seedShift i) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hliveInv :
      ∀ i : κ, ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y + K.liveShift i) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hstat :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    {t : NNReal} {y : X}
    (hnz :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y ≠ 0) :
    L.windowedColeHopfHeatShiftKernelCandidate
      (ι := ι) (X := X)
      selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x ≠
    L.windowedColeHopfHeatSaturatedCandidate
      (ι := ι) (X := X)
      selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  exact
    L.not_windowedColeHopfHeatShiftKernelCandidate_eq_saturatedCandidate_of_totalCoeffSum_nonpos_of_saturatedCoeff_pos_of_stationary_shiftInvariant
      (ι := ι) (X := X)
      selector K a c ν hsum_nonpos ha hc hν curlFrame curlBound curlBound_nonneg hcurl x
      hseedInv hliveInv hstat hnz

theorem windowed_heat_saturated_shiftKernel_invariant_no_candidate_of_nonneg_sum_neg_saturatedCoeff_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (a c ν : ℝ)
    (hsum_nonneg : 0 ≤ SeedLiveShiftKernel.totalCoeffSum K)
    (ha : a < 0)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hseedInv :
      ∀ i : κ, ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y + K.seedShift i) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hliveInv :
      ∀ i : κ, ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y + K.liveShift i) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hstat :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    {t : NNReal} {y : X}
    (hnz :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y ≠ 0) :
    L.windowedColeHopfHeatShiftKernelCandidate
      (ι := ι) (X := X)
      selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x ≠
    L.windowedColeHopfHeatSaturatedCandidate
      (ι := ι) (X := X)
      selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  exact
    L.not_windowedColeHopfHeatShiftKernelCandidate_eq_saturatedCandidate_of_totalCoeffSum_nonneg_of_saturatedCoeff_neg_of_stationary_shiftInvariant
      (ι := ι) (X := X)
      selector K a c ν hsum_nonneg ha hc hν curlFrame curlBound curlBound_nonneg hcurl x
      hseedInv hliveInv hstat hnz

theorem windowed_heat_saturated_shiftKernel_invariant_candidate_abs_sum_le_abs_saturatedCoeff_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (a c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hseedInv :
      ∀ i : κ, ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y + K.seedShift i) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hliveInv :
      ∀ i : κ, ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y + K.liveShift i) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hstat :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hCand :
      L.windowedColeHopfHeatShiftKernelCandidate
        (ι := ι) (X := X)
        selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x =
      L.windowedColeHopfHeatSaturatedCandidate
        (ι := ι) (X := X)
        selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
    {t : NNReal} {y : X}
    (hnz :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y ≠ 0) :
    |SeedLiveShiftKernel.totalCoeffSum K| ≤ |a| := by
  exact
    L.windowedColeHopfHeatShiftKernel_abs_totalCoeffSum_le_abs_saturatedCoeff_of_candidate_eq_saturatedCandidate_of_stationary_shiftInvariant
      (ι := ι) (X := X)
      selector K a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
      hseedInv hliveInv hstat hCand hnz

theorem windowed_heat_saturated_shiftKernel_invariant_candidate_abs_sum_lt_abs_saturatedCoeff_of_nonzero_sum_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (a c ν : ℝ)
    (hsum : SeedLiveShiftKernel.totalCoeffSum K ≠ 0)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hseedInv :
      ∀ i : κ, ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y + K.seedShift i) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hliveInv :
      ∀ i : κ, ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y + K.liveShift i) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hstat :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hCand :
      L.windowedColeHopfHeatShiftKernelCandidate
        (ι := ι) (X := X)
        selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x =
      L.windowedColeHopfHeatSaturatedCandidate
        (ι := ι) (X := X)
        selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
    {t : NNReal} {y : X}
    (hnz :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y ≠ 0) :
    |SeedLiveShiftKernel.totalCoeffSum K| < |a| := by
  exact
    L.windowedColeHopfHeatShiftKernel_abs_totalCoeffSum_lt_abs_saturatedCoeff_of_candidate_eq_saturatedCandidate_of_totalCoeffSum_ne_zero_of_stationary_shiftInvariant
      (ι := ι) (X := X)
      selector K a c ν hsum hc hν curlFrame curlBound curlBound_nonneg hcurl x
      hseedInv hliveInv hstat hCand hnz

theorem windowed_heat_saturated_shiftKernel_invariant_no_candidate_of_abs_saturatedCoeff_lt_abs_sum_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (a c ν : ℝ)
    (hlarge : |a| < |SeedLiveShiftKernel.totalCoeffSum K|)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hseedInv :
      ∀ i : κ, ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y + K.seedShift i) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hliveInv :
      ∀ i : κ, ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y + K.liveShift i) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hstat :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    {t : NNReal} {y : X}
    (hnz :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y ≠ 0) :
    L.windowedColeHopfHeatShiftKernelCandidate
      (ι := ι) (X := X)
      selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x ≠
    L.windowedColeHopfHeatSaturatedCandidate
      (ι := ι) (X := X)
      selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  exact
    L.not_windowedColeHopfHeatShiftKernelCandidate_eq_saturatedCandidate_of_abs_saturatedCoeff_lt_abs_totalCoeffSum_of_stationary_shiftInvariant
      (ι := ι) (X := X)
      selector K a c ν hlarge hc hν curlFrame curlBound curlBound_nonneg hcurl x
      hseedInv hliveInv hstat hnz

theorem windowed_heat_saturated_shiftKernel_invariant_no_candidate_of_abs_saturatedCoeff_le_abs_sum_nonzero_sum_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (a c ν : ℝ)
    (hlarge : |a| ≤ |SeedLiveShiftKernel.totalCoeffSum K|)
    (hsum : SeedLiveShiftKernel.totalCoeffSum K ≠ 0)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hseedInv :
      ∀ i : κ, ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y + K.seedShift i) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hliveInv :
      ∀ i : κ, ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y + K.liveShift i) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hstat :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    {t : NNReal} {y : X}
    (hnz :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y ≠ 0) :
    L.windowedColeHopfHeatShiftKernelCandidate
      (ι := ι) (X := X)
      selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x ≠
    L.windowedColeHopfHeatSaturatedCandidate
      (ι := ι) (X := X)
      selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  exact
    L.not_windowedColeHopfHeatShiftKernelCandidate_eq_saturatedCandidate_of_abs_saturatedCoeff_le_abs_totalCoeffSum_of_totalCoeffSum_ne_zero_of_stationary_shiftInvariant
      (ι := ι) (X := X)
      selector K a c ν hlarge hsum hc hν curlFrame curlBound curlBound_nonneg hcurl x
      hseedInv hliveInv hstat hnz

theorem windowed_heat_saturated_shiftKernel_invariant_bridge_abs_eq_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (a c ν : ℝ)
    (hsum : SeedLiveShiftKernel.totalCoeffSum K ≠ 0)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hseedInv :
      ∀ i : κ, ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y + K.seedShift i) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hliveInv :
      ∀ i : κ, ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y + K.liveShift i) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hstat :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (B :
      TopDownFeffermanBridge
        (pressureSeededPredicateKit
          (Time := NNReal) (X := X)
          (L.windowedColeHopfHeatShiftKernelInitialSlice
            (ι := ι) (X := X)
            selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
        (shiftKernelCompatibilityPred (Time := NNReal) (X := X) K)
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatSaturatedCandidate
          (ι := ι) (X := X)
          selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
    {t₁ t₂ : NNReal} {y₁ y₂ : X}
    (hnz₁ :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₁ y₁ ≠ 0)
    (hnz₂ :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₂ y₂ ≠ 0) :
    |(L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₁ y₁| =
    |(L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₂ y₂| := by
  exact
    L.windowedColeHopfHeatShiftKernel_abs_eq_abs_of_topDownBridge_eq_saturatedCandidate_of_stationary_shiftInvariant
      (ι := ι) (X := X)
      selector K a c ν hsum hc hν curlFrame curlBound curlBound_nonneg hcurl x
      hseedInv hliveInv hstat B hCand hnz₁ hnz₂

theorem windowed_heat_saturated_shiftKernel_invariant_bridge_coeff_formula_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (a c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hseedInv :
      ∀ i : κ, ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y + K.seedShift i) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hliveInv :
      ∀ i : κ, ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y + K.liveShift i) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hstat :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (B :
      TopDownFeffermanBridge
        (pressureSeededPredicateKit
          (Time := NNReal) (X := X)
          (L.windowedColeHopfHeatShiftKernelInitialSlice
            (ι := ι) (X := X)
            selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
        (shiftKernelCompatibilityPred (Time := NNReal) (X := X) K)
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatSaturatedCandidate
          (ι := ι) (X := X)
          selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
    {t : NNReal} {y : X}
    (hnz :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y ≠ 0) :
    SeedLiveShiftKernel.totalCoeffSum K *
        (1 + |(L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y|) =
      a := by
  exact
    L.windowedColeHopfHeatShiftKernel_totalCoeffSum_mul_one_add_abs_eq_saturatedCoeff_of_topDownBridge_eq_saturatedCandidate_of_stationary_shiftInvariant
      (ι := ι) (X := X)
      selector K a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
      hseedInv hliveInv hstat B hCand hnz

theorem windowed_heat_saturated_shiftKernel_invariant_bridge_zeroSum_or_abs_eq_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (a c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hseedInv :
      ∀ i : κ, ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y + K.seedShift i) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hliveInv :
      ∀ i : κ, ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y + K.liveShift i) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hstat :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (B :
      TopDownFeffermanBridge
        (pressureSeededPredicateKit
          (Time := NNReal) (X := X)
          (L.windowedColeHopfHeatShiftKernelInitialSlice
            (ι := ι) (X := X)
            selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
        (shiftKernelCompatibilityPred (Time := NNReal) (X := X) K)
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatSaturatedCandidate
          (ι := ι) (X := X)
          selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
    {t₁ t₂ : NNReal} {y₁ y₂ : X}
    (hnz₁ :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₁ y₁ ≠ 0)
    (hnz₂ :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₂ y₂ ≠ 0) :
    SeedLiveShiftKernel.totalCoeffSum K = 0 ∨
      |(L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₁ y₁| =
        |(L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₂ y₂| := by
  exact
    L.windowedColeHopfHeatShiftKernel_totalCoeffSum_zero_or_abs_eq_abs_of_topDownBridge_eq_saturatedCandidate_of_stationary_shiftInvariant
      (ι := ι) (X := X)
      selector K a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
      hseedInv hliveInv hstat B hCand hnz₁ hnz₂

theorem windowed_heat_saturated_shiftKernel_invariant_bridge_zeroSum_of_abs_ne_abs_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (a c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hseedInv :
      ∀ i : κ, ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y + K.seedShift i) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hliveInv :
      ∀ i : κ, ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y + K.liveShift i) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hstat :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (B :
      TopDownFeffermanBridge
        (pressureSeededPredicateKit
          (Time := NNReal) (X := X)
          (L.windowedColeHopfHeatShiftKernelInitialSlice
            (ι := ι) (X := X)
            selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
        (shiftKernelCompatibilityPred (Time := NNReal) (X := X) K)
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatSaturatedCandidate
          (ι := ι) (X := X)
          selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
    (hwitness :
      ∃ t₁ t₂ y₁ y₂,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₁ y₁ ≠ 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₂ y₂ ≠ 0 ∧
        |(L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₁ y₁| ≠
          |(L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₂ y₂|) :
    SeedLiveShiftKernel.totalCoeffSum K = 0 := by
  exact
    L.windowedColeHopfHeatShiftKernel_totalCoeffSum_zero_of_topDownBridge_eq_saturatedCandidate_of_abs_ne_abs_of_stationary_shiftInvariant
      (ι := ι) (X := X)
      selector K a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
      hseedInv hliveInv hstat B hCand hwitness

theorem windowed_heat_saturated_shiftKernel_invariant_no_bridge_of_zeroSum_nonzero_saturatedCoeff_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (a c ν : ℝ)
    (hsum0 : SeedLiveShiftKernel.totalCoeffSum K = 0)
    (ha : a ≠ 0)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hseedInv :
      ∀ i : κ, ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y + K.seedShift i) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hliveInv :
      ∀ i : κ, ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y + K.liveShift i) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hstat :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    {t : NNReal} {y : X}
    (hnz :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y ≠ 0) :
    ¬ ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := X)
            (L.windowedColeHopfHeatShiftKernelInitialSlice
              (ι := ι) (X := X)
              selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
          (shiftKernelCompatibilityPred (Time := NNReal) (X := X) K)
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatSaturatedCandidate
            (ι := ι) (X := X)
            selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  exact
    L.not_exists_windowedColeHopfHeatShiftKernelTopDownBridge_eq_saturatedCandidate_of_totalCoeffSum_zero_of_saturatedCoeff_ne_zero_of_stationary_shiftInvariant
      (ι := ι) (X := X)
      selector K a c ν hsum0 ha hc hν curlFrame curlBound curlBound_nonneg hcurl x
      hseedInv hliveInv hstat hnz

theorem windowed_heat_saturated_shiftKernel_invariant_no_bridge_of_nonpos_sum_pos_saturatedCoeff_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (a c ν : ℝ)
    (hsum_nonpos : SeedLiveShiftKernel.totalCoeffSum K ≤ 0)
    (ha : 0 < a)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hseedInv :
      ∀ i : κ, ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y + K.seedShift i) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hliveInv :
      ∀ i : κ, ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y + K.liveShift i) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hstat :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    {t : NNReal} {y : X}
    (hnz :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y ≠ 0) :
    ¬ ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := X)
            (L.windowedColeHopfHeatShiftKernelInitialSlice
              (ι := ι) (X := X)
              selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
          (shiftKernelCompatibilityPred (Time := NNReal) (X := X) K)
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatSaturatedCandidate
            (ι := ι) (X := X)
            selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  exact
    L.not_exists_windowedColeHopfHeatShiftKernelTopDownBridge_eq_saturatedCandidate_of_totalCoeffSum_nonpos_of_saturatedCoeff_pos_of_stationary_shiftInvariant
      (ι := ι) (X := X)
      selector K a c ν hsum_nonpos ha hc hν curlFrame curlBound curlBound_nonneg hcurl x
      hseedInv hliveInv hstat hnz

theorem windowed_heat_saturated_shiftKernel_invariant_no_bridge_of_nonneg_sum_neg_saturatedCoeff_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (a c ν : ℝ)
    (hsum_nonneg : 0 ≤ SeedLiveShiftKernel.totalCoeffSum K)
    (ha : a < 0)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hseedInv :
      ∀ i : κ, ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y + K.seedShift i) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hliveInv :
      ∀ i : κ, ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y + K.liveShift i) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hstat :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    {t : NNReal} {y : X}
    (hnz :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y ≠ 0) :
    ¬ ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := X)
            (L.windowedColeHopfHeatShiftKernelInitialSlice
              (ι := ι) (X := X)
              selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
          (shiftKernelCompatibilityPred (Time := NNReal) (X := X) K)
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatSaturatedCandidate
            (ι := ι) (X := X)
            selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  exact
    L.not_exists_windowedColeHopfHeatShiftKernelTopDownBridge_eq_saturatedCandidate_of_totalCoeffSum_nonneg_of_saturatedCoeff_neg_of_stationary_shiftInvariant
      (ι := ι) (X := X)
      selector K a c ν hsum_nonneg ha hc hν curlFrame curlBound curlBound_nonneg hcurl x
      hseedInv hliveInv hstat hnz

theorem windowed_heat_saturated_shiftKernel_invariant_bridge_abs_sum_le_abs_saturatedCoeff_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (a c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hseedInv :
      ∀ i : κ, ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y + K.seedShift i) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hliveInv :
      ∀ i : κ, ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y + K.liveShift i) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hstat :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (B :
      TopDownFeffermanBridge
        (pressureSeededPredicateKit
          (Time := NNReal) (X := X)
          (L.windowedColeHopfHeatShiftKernelInitialSlice
            (ι := ι) (X := X)
            selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
        (shiftKernelCompatibilityPred (Time := NNReal) (X := X) K)
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatSaturatedCandidate
          (ι := ι) (X := X)
          selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
    {t : NNReal} {y : X}
    (hnz :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y ≠ 0) :
    |SeedLiveShiftKernel.totalCoeffSum K| ≤ |a| := by
  exact
    L.windowedColeHopfHeatShiftKernel_abs_totalCoeffSum_le_abs_saturatedCoeff_of_topDownBridge_eq_saturatedCandidate_of_stationary_shiftInvariant
      (ι := ι) (X := X)
      selector K a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
      hseedInv hliveInv hstat B hCand hnz

theorem windowed_heat_saturated_shiftKernel_invariant_bridge_abs_sum_lt_abs_saturatedCoeff_of_nonzero_sum_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (a c ν : ℝ)
    (hsum : SeedLiveShiftKernel.totalCoeffSum K ≠ 0)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hseedInv :
      ∀ i : κ, ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y + K.seedShift i) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hliveInv :
      ∀ i : κ, ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y + K.liveShift i) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hstat :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (B :
      TopDownFeffermanBridge
        (pressureSeededPredicateKit
          (Time := NNReal) (X := X)
          (L.windowedColeHopfHeatShiftKernelInitialSlice
            (ι := ι) (X := X)
            selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
        (shiftKernelCompatibilityPred (Time := NNReal) (X := X) K)
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatSaturatedCandidate
          (ι := ι) (X := X)
          selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
    {t : NNReal} {y : X}
    (hnz :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y ≠ 0) :
    |SeedLiveShiftKernel.totalCoeffSum K| < |a| := by
  exact
    L.windowedColeHopfHeatShiftKernel_abs_totalCoeffSum_lt_abs_saturatedCoeff_of_topDownBridge_eq_saturatedCandidate_of_totalCoeffSum_ne_zero_of_stationary_shiftInvariant
      (ι := ι) (X := X)
      selector K a c ν hsum hc hν curlFrame curlBound curlBound_nonneg hcurl x
      hseedInv hliveInv hstat B hCand hnz

theorem windowed_heat_saturated_shiftKernel_invariant_no_bridge_of_abs_saturatedCoeff_lt_abs_sum_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (a c ν : ℝ)
    (hlarge : |a| < |SeedLiveShiftKernel.totalCoeffSum K|)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hseedInv :
      ∀ i : κ, ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y + K.seedShift i) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hliveInv :
      ∀ i : κ, ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y + K.liveShift i) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hstat :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    {t : NNReal} {y : X}
    (hnz :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y ≠ 0) :
    ¬ ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := X)
            (L.windowedColeHopfHeatShiftKernelInitialSlice
              (ι := ι) (X := X)
              selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
          (shiftKernelCompatibilityPred (Time := NNReal) (X := X) K)
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatSaturatedCandidate
            (ι := ι) (X := X)
            selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  exact
    L.not_exists_windowedColeHopfHeatShiftKernelTopDownBridge_eq_saturatedCandidate_of_abs_saturatedCoeff_lt_abs_totalCoeffSum_of_stationary_shiftInvariant
      (ι := ι) (X := X)
      selector K a c ν hlarge hc hν curlFrame curlBound curlBound_nonneg hcurl x
      hseedInv hliveInv hstat hnz

theorem windowed_heat_saturated_shiftKernel_invariant_no_bridge_of_abs_saturatedCoeff_le_abs_sum_nonzero_sum_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (a c ν : ℝ)
    (hlarge : |a| ≤ |SeedLiveShiftKernel.totalCoeffSum K|)
    (hsum : SeedLiveShiftKernel.totalCoeffSum K ≠ 0)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hseedInv :
      ∀ i : κ, ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y + K.seedShift i) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hliveInv :
      ∀ i : κ, ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y + K.liveShift i) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hstat :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    {t : NNReal} {y : X}
    (hnz :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y ≠ 0) :
    ¬ ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := X)
            (L.windowedColeHopfHeatShiftKernelInitialSlice
              (ι := ι) (X := X)
              selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
          (shiftKernelCompatibilityPred (Time := NNReal) (X := X) K)
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatSaturatedCandidate
            (ι := ι) (X := X)
            selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  exact
    L.not_exists_windowedColeHopfHeatShiftKernelTopDownBridge_eq_saturatedCandidate_of_abs_saturatedCoeff_le_abs_totalCoeffSum_of_totalCoeffSum_ne_zero_of_stationary_shiftInvariant
      (ι := ι) (X := X)
      selector K a c ν hlarge hsum hc hν curlFrame curlBound curlBound_nonneg hcurl x
      hseedInv hliveInv hstat hnz

theorem windowed_heat_saturated_shiftKernel_invariant_no_bridge_of_abs_ne_abs_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (a c ν : ℝ)
    (hsum : SeedLiveShiftKernel.totalCoeffSum K ≠ 0)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hseedInv :
      ∀ i : κ, ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y + K.seedShift i) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hliveInv :
      ∀ i : κ, ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t
          (y + K.liveShift i) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hstat :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hwitness :
      ∃ t₁ t₂ y₁ y₂,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₁ y₁ ≠ 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₂ y₂ ≠ 0 ∧
        |(L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₁ y₁| ≠
          |(L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₂ y₂|) :
    ¬ ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := X)
            (L.windowedColeHopfHeatShiftKernelInitialSlice
              (ι := ι) (X := X)
              selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
          (shiftKernelCompatibilityPred (Time := NNReal) (X := X) K)
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatSaturatedCandidate
            (ι := ι) (X := X)
            selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  exact
    L.not_exists_windowedColeHopfHeatShiftKernelTopDownBridge_eq_saturatedCandidate_of_abs_ne_abs_of_stationary_shiftInvariant
      (ι := ι) (X := X)
      selector K a c ν hsum hc hν curlFrame curlBound curlBound_nonneg hcurl x
      hseedInv hliveInv hstat hwitness

end WindowedColeHopfHeatSaturatedShiftKernelInvariant

section WindowedColeHopfHeatSaturatedAnchoredShiftInvariant

variable {ι X : Type*}
variable [Fintype ι] [AddMonoid X]

theorem windowed_heat_saturated_anchored_shiftInvariant_candidate_eq_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (baseCoeff seedCoeff shiftCoeff satCoeff r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hcoeff : baseCoeff + seedCoeff + shiftCoeff = satCoeff / (1 + r))
    (hshiftInv :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t (y + s) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hstat :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (habs :
      ∀ t : NNReal, ∀ y : X,
        |(L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y| = r) :
    L.windowedColeHopfHeatAnchoredShiftCandidate
      (ι := ι) (X := X)
      selector s baseCoeff seedCoeff shiftCoeff c ν hc hν
      curlFrame curlBound curlBound_nonneg hcurl x =
    L.windowedColeHopfHeatSaturatedCandidate
      (ι := ι) (X := X)
      selector satCoeff c ν hc hν
      curlFrame curlBound curlBound_nonneg hcurl x := by
  exact
    L.windowedColeHopfHeatAnchoredShiftCandidate_eq_saturatedCandidate_of_stationary_shiftInvariant_constantMagnitude
      (ι := ι) (X := X)
      selector s baseCoeff seedCoeff shiftCoeff satCoeff r c ν hc hν
      curlFrame curlBound curlBound_nonneg hcurl x
      hcoeff hshiftInv hstat habs

theorem windowed_heat_saturated_anchored_shiftInvariant_candidate_abs_coeffSum_lt_abs_saturatedCoeff_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (baseCoeff seedCoeff shiftCoeff satCoeff c ν : ℝ)
    (hsum : baseCoeff + seedCoeff + shiftCoeff ≠ 0)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hshiftInv :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t (y + s) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hstat :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hCand :
      L.windowedColeHopfHeatAnchoredShiftCandidate
        (ι := ι) (X := X)
        selector s baseCoeff seedCoeff shiftCoeff c ν hc hν
        curlFrame curlBound curlBound_nonneg hcurl x =
      L.windowedColeHopfHeatSaturatedCandidate
        (ι := ι) (X := X)
        selector satCoeff c ν hc hν
        curlFrame curlBound curlBound_nonneg hcurl x)
    {t : NNReal} {y : X}
    (hnz :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y ≠ 0) :
    |baseCoeff + seedCoeff + shiftCoeff| < |satCoeff| := by
  exact
    L.windowedColeHopfHeatAnchoredShift_abs_coeffSum_lt_abs_saturatedCoeff_of_candidate_eq_saturatedCandidate_of_stationary_shiftInvariant
      (ι := ι) (X := X)
      selector s baseCoeff seedCoeff shiftCoeff satCoeff c ν hsum hc hν
      curlFrame curlBound curlBound_nonneg hcurl x hshiftInv hstat hCand hnz

theorem windowed_heat_saturated_anchored_shiftInvariant_no_candidate_of_abs_saturatedCoeff_le_abs_coeffSum_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (baseCoeff seedCoeff shiftCoeff satCoeff c ν : ℝ)
    (hlarge : |satCoeff| ≤ |baseCoeff + seedCoeff + shiftCoeff|)
    (hsum : baseCoeff + seedCoeff + shiftCoeff ≠ 0)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hshiftInv :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t (y + s) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hstat :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    {t : NNReal} {y : X}
    (hnz :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y ≠ 0) :
    L.windowedColeHopfHeatAnchoredShiftCandidate
      (ι := ι) (X := X)
      selector s baseCoeff seedCoeff shiftCoeff c ν hc hν
      curlFrame curlBound curlBound_nonneg hcurl x ≠
    L.windowedColeHopfHeatSaturatedCandidate
      (ι := ι) (X := X)
      selector satCoeff c ν hc hν
      curlFrame curlBound curlBound_nonneg hcurl x := by
  exact
    L.not_windowedColeHopfHeatAnchoredShiftCandidate_eq_saturatedCandidate_of_abs_saturatedCoeff_le_abs_coeffSum_of_stationary_shiftInvariant
      (ι := ι) (X := X)
      selector s baseCoeff seedCoeff shiftCoeff satCoeff c ν hlarge hsum hc hν
      curlFrame curlBound curlBound_nonneg hcurl x hshiftInv hstat hnz

theorem windowed_heat_saturated_anchored_shiftInvariant_clause_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (baseCoeff seedCoeff shiftCoeff satCoeff r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hcoeff : baseCoeff + seedCoeff + shiftCoeff = satCoeff / (1 + r))
    (hshiftInv :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t (y + s) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (habs :
      ∀ t : NNReal, ∀ y : X,
        |(L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y| = r) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatSaturatedInitialSlice
          (ι := ι) (X := X)
          selector satCoeff c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) := by
  exact
    L.windowedColeHopfHeat_realizes_saturated_pressure_seeded_clause_via_anchoredShift_of_shiftInvariant_constantMagnitude
      (ι := ι) (X := X)
      selector s baseCoeff seedCoeff shiftCoeff satCoeff r c ν hc hν
      curlFrame curlBound curlBound_nonneg hcurl x hcoeff hshiftInv habs

theorem windowed_heat_saturated_anchored_shiftInvariant_bridge_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (baseCoeff seedCoeff shiftCoeff satCoeff r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hcoeff : baseCoeff + seedCoeff + shiftCoeff = satCoeff / (1 + r))
    (hshiftInv :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t (y + s) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hstat :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (habs :
      ∀ t : NNReal, ∀ y : X,
        |(L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y| = r) :
    ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := X)
            (L.windowedColeHopfHeatShiftKernelInitialSlice
              (ι := ι) (X := X)
              selector (anchoredTranslationShiftKernel (X := X) s baseCoeff seedCoeff shiftCoeff)
              c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
          (shiftKernelCompatibilityPred
            (Time := NNReal) (X := X)
            (anchoredTranslationShiftKernel (X := X) s baseCoeff seedCoeff shiftCoeff))
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatSaturatedCandidate
            (ι := ι) (X := X)
            selector satCoeff c ν hc hν
            curlFrame curlBound curlBound_nonneg hcurl x := by
  exact
    L.exists_windowedColeHopfHeatSaturatedAnchoredShiftKernelBridge_of_stationary_shiftInvariant_constantMagnitude
      (ι := ι) (X := X)
      selector s baseCoeff seedCoeff shiftCoeff satCoeff r c ν hc hν
      curlFrame curlBound curlBound_nonneg hcurl x
      hcoeff hshiftInv hstat habs

theorem windowed_heat_saturated_anchored_shiftInvariant_bridge_abs_eq_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (baseCoeff seedCoeff shiftCoeff satCoeff c ν : ℝ)
    (hsum : baseCoeff + seedCoeff + shiftCoeff ≠ 0)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hshiftInv :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t (y + s) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hstat :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (B :
      TopDownFeffermanBridge
        (pressureSeededPredicateKit
          (Time := NNReal) (X := X)
          (L.windowedColeHopfHeatShiftKernelInitialSlice
            (ι := ι) (X := X)
            selector (anchoredTranslationShiftKernel (X := X) s baseCoeff seedCoeff shiftCoeff)
            c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
        (shiftKernelCompatibilityPred
          (Time := NNReal) (X := X)
          (anchoredTranslationShiftKernel (X := X) s baseCoeff seedCoeff shiftCoeff))
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatSaturatedCandidate
          (ι := ι) (X := X)
          selector satCoeff c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
    {t₁ t₂ : NNReal} {y₁ y₂ : X}
    (hnz₁ :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₁ y₁ ≠ 0)
    (hnz₂ :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₂ y₂ ≠ 0) :
    |(L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₁ y₁| =
    |(L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₂ y₂| := by
  exact
    L.windowedColeHopfHeatAnchoredShift_abs_eq_abs_of_topDownBridge_eq_saturatedCandidate_of_stationary_shiftInvariant
      (ι := ι) (X := X)
      selector s baseCoeff seedCoeff shiftCoeff satCoeff c ν hsum hc hν
      curlFrame curlBound curlBound_nonneg hcurl x hshiftInv hstat B hCand hnz₁ hnz₂

theorem windowed_heat_saturated_anchored_shiftInvariant_bridge_abs_coeffSum_lt_abs_saturatedCoeff_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (baseCoeff seedCoeff shiftCoeff satCoeff c ν : ℝ)
    (hsum : baseCoeff + seedCoeff + shiftCoeff ≠ 0)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hshiftInv :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t (y + s) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hstat :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (B :
      TopDownFeffermanBridge
        (pressureSeededPredicateKit
          (Time := NNReal) (X := X)
          (L.windowedColeHopfHeatShiftKernelInitialSlice
            (ι := ι) (X := X)
            selector (anchoredTranslationShiftKernel (X := X) s baseCoeff seedCoeff shiftCoeff)
            c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
        (shiftKernelCompatibilityPred
          (Time := NNReal) (X := X)
          (anchoredTranslationShiftKernel (X := X) s baseCoeff seedCoeff shiftCoeff))
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatSaturatedCandidate
          (ι := ι) (X := X)
          selector satCoeff c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
    {t : NNReal} {y : X}
    (hnz :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y ≠ 0) :
    |baseCoeff + seedCoeff + shiftCoeff| < |satCoeff| := by
  exact
    L.windowedColeHopfHeatAnchoredShift_abs_coeffSum_lt_abs_saturatedCoeff_of_topDownBridge_eq_saturatedCandidate_of_stationary_shiftInvariant
      (ι := ι) (X := X)
      selector s baseCoeff seedCoeff shiftCoeff satCoeff c ν hsum hc hν
      curlFrame curlBound curlBound_nonneg hcurl x hshiftInv hstat B hCand hnz

theorem windowed_heat_saturated_anchored_shiftInvariant_no_bridge_of_abs_saturatedCoeff_le_abs_coeffSum_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (baseCoeff seedCoeff shiftCoeff satCoeff c ν : ℝ)
    (hlarge : |satCoeff| ≤ |baseCoeff + seedCoeff + shiftCoeff|)
    (hsum : baseCoeff + seedCoeff + shiftCoeff ≠ 0)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hshiftInv :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t (y + s) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hstat :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    {t : NNReal} {y : X}
    (hnz :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y ≠ 0) :
    ¬ ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := X)
            (L.windowedColeHopfHeatShiftKernelInitialSlice
              (ι := ι) (X := X)
              selector (anchoredTranslationShiftKernel (X := X) s baseCoeff seedCoeff shiftCoeff)
              c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
          (shiftKernelCompatibilityPred
            (Time := NNReal) (X := X)
            (anchoredTranslationShiftKernel (X := X) s baseCoeff seedCoeff shiftCoeff))
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatSaturatedCandidate
            (ι := ι) (X := X)
            selector satCoeff c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  exact
    L.not_exists_windowedColeHopfHeatAnchoredShiftTopDownBridge_eq_saturatedCandidate_of_abs_saturatedCoeff_le_abs_coeffSum_of_stationary_shiftInvariant
      (ι := ι) (X := X)
      selector s baseCoeff seedCoeff shiftCoeff satCoeff c ν hlarge hsum hc hν
      curlFrame curlBound curlBound_nonneg hcurl x hshiftInv hstat hnz

theorem windowed_heat_saturated_anchored_shiftInvariant_no_bridge_of_abs_ne_abs_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (baseCoeff seedCoeff shiftCoeff satCoeff c ν : ℝ)
    (hsum : baseCoeff + seedCoeff + shiftCoeff ≠ 0)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hshiftInv :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t (y + s) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hstat :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hwitness :
      ∃ t₁ t₂ y₁ y₂,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₁ y₁ ≠ 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₂ y₂ ≠ 0 ∧
        |(L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₁ y₁| ≠
          |(L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₂ y₂|) :
    ¬ ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := X)
            (L.windowedColeHopfHeatShiftKernelInitialSlice
              (ι := ι) (X := X)
              selector (anchoredTranslationShiftKernel (X := X) s baseCoeff seedCoeff shiftCoeff)
              c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
          (shiftKernelCompatibilityPred
            (Time := NNReal) (X := X)
            (anchoredTranslationShiftKernel (X := X) s baseCoeff seedCoeff shiftCoeff))
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatSaturatedCandidate
            (ι := ι) (X := X)
            selector satCoeff c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  exact
    L.not_exists_windowedColeHopfHeatAnchoredShiftTopDownBridge_eq_saturatedCandidate_of_abs_ne_abs_of_stationary_shiftInvariant
      (ι := ι) (X := X)
      selector s baseCoeff seedCoeff shiftCoeff satCoeff c ν hsum hc hν
      curlFrame curlBound curlBound_nonneg hcurl x hshiftInv hstat hwitness

end WindowedColeHopfHeatSaturatedAnchoredShiftInvariant

section WindowedColeHopfHeatSaturatedMaskedShiftKernel

variable {ι X κ : Type*}
variable [Fintype ι] [Fintype κ] [AddMonoid X]

theorem windowed_heat_saturated_masked_shiftKernel_candidate_eq_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (mask : κ → Bool)
    (s : X)
    (seedCoeff liveCoeff : κ → ℝ)
    (a r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hcoeff :
      SeedLiveShiftKernel.totalCoeffSum
        (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
          (X := X) mask s seedCoeff liveCoeff) = a / (1 + r))
    (hshiftInv :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t (y + s) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hstat :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (habs :
      ∀ t : NNReal, ∀ y : X,
        |(L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y| = r) :
    L.windowedColeHopfHeatShiftKernelCandidate
      (ι := ι) (X := X)
      selector
      (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
        (X := X) mask s seedCoeff liveCoeff)
      c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x =
    L.windowedColeHopfHeatSaturatedCandidate
      (ι := ι) (X := X)
      selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  exact
    L.windowedColeHopfHeatMaskedShiftKernelCandidate_eq_saturatedCandidate_of_stationary_shiftInvariant_constantMagnitude
      (ι := ι) (X := X)
      selector mask s seedCoeff liveCoeff a r c ν hc hν
      curlFrame curlBound curlBound_nonneg hcurl x
      hcoeff hshiftInv hstat habs

theorem windowed_heat_saturated_masked_shiftKernel_clause_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (mask : κ → Bool)
    (s : X)
    (seedCoeff liveCoeff : κ → ℝ)
    (a r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hcoeff :
      SeedLiveShiftKernel.totalCoeffSum
        (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
          (X := X) mask s seedCoeff liveCoeff) = a / (1 + r))
    (hshiftInv :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t (y + s) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (habs :
      ∀ t : NNReal, ∀ y : X,
        |(L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y| = r) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatSaturatedInitialSlice
          (ι := ι) (X := X)
          selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) := by
  exact
    L.windowedColeHopfHeat_realizes_saturated_pressure_seeded_clause_via_maskedShiftKernel_of_shiftInvariant_constantMagnitude
      (ι := ι) (X := X)
      selector mask s seedCoeff liveCoeff a r c ν hc hν
      curlFrame curlBound curlBound_nonneg hcurl x
      hcoeff hshiftInv habs

theorem windowed_heat_saturated_masked_shiftKernel_bridge_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (mask : κ → Bool)
    (s : X)
    (seedCoeff liveCoeff : κ → ℝ)
    (a r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hcoeff :
      SeedLiveShiftKernel.totalCoeffSum
        (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
          (X := X) mask s seedCoeff liveCoeff) = a / (1 + r))
    (hshiftInv :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t (y + s) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hstat :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (habs :
      ∀ t : NNReal, ∀ y : X,
        |(L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y| = r) :
    ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := X)
            (L.windowedColeHopfHeatShiftKernelInitialSlice
              (ι := ι) (X := X)
              selector
              (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
                (X := X) mask s seedCoeff liveCoeff)
              c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
          (shiftKernelCompatibilityPred (Time := NNReal) (X := X)
            (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
              (X := X) mask s seedCoeff liveCoeff))
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatSaturatedCandidate
            (ι := ι) (X := X)
            selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  exact
    L.exists_windowedColeHopfHeatSaturatedMaskedShiftKernelBridge_of_stationary_shiftInvariant_constantMagnitude
      (ι := ι) (X := X)
      selector mask s seedCoeff liveCoeff a r c ν hc hν
      curlFrame curlBound curlBound_nonneg hcurl x
      hcoeff hshiftInv hstat habs

end WindowedColeHopfHeatSaturatedMaskedShiftKernel

section WindowedColeHopfHeatSaturatedIdentitySampleKernel

variable {ι X κ : Type*}
variable [Fintype ι] [Fintype κ] [AddMonoid X]

theorem windowed_heat_saturated_identitySampleKernel_initialSlice_eq_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveSampleKernel κ X)
    (a r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hK : K.IdentityAnchors)
    (hcoeff : K.liveCoeffSum + K.seedCoeffSum = a / (1 + r))
    (habs :
      ∀ t : NNReal, ∀ y : X,
        |(L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y| = r) :
    L.windowedColeHopfHeatSampleKernelInitialSlice
      (ι := ι) (X := X)
      selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x =
    L.windowedColeHopfHeatSaturatedInitialSlice
      (ι := ι) (X := X)
      selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  exact
    L.windowedColeHopfHeatIdentitySampleKernelInitialSlice_eq_saturatedInitialSlice_of_constantMagnitude
      (ι := ι) (X := X)
      selector K a r c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
      hK hcoeff habs

theorem windowed_heat_saturated_identitySampleKernel_candidate_eq_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveSampleKernel κ X)
    (a r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hK : K.IdentityAnchors)
    (hcoeff : K.liveCoeffSum + K.seedCoeffSum = a / (1 + r))
    (hstat :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (habs :
      ∀ t : NNReal, ∀ y : X,
        |(L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y| = r) :
    L.windowedColeHopfHeatSampleKernelCandidate
      (ι := ι) (X := X)
      selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x =
    L.windowedColeHopfHeatSaturatedCandidate
      (ι := ι) (X := X)
      selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  exact
    L.windowedColeHopfHeatIdentitySampleKernelCandidate_eq_saturatedCandidate_of_stationary_constantMagnitude
      (ι := ι) (X := X)
      selector K a r c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
      hK hcoeff hstat habs

theorem windowed_heat_saturated_identitySampleKernel_clause_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveSampleKernel κ X)
    (a r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hK : K.IdentityAnchors)
    (hcoeff : K.liveCoeffSum + K.seedCoeffSum = a / (1 + r))
    (habs :
      ∀ t : NNReal, ∀ y : X,
        |(L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y| = r) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatSaturatedInitialSlice
          (ι := ι) (X := X)
          selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) := by
  exact
    L.windowedColeHopfHeat_realizes_saturated_pressure_seeded_clause_via_identitySampleKernel_of_constantMagnitude
      (ι := ι) (X := X)
      selector K a r c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
      hK hcoeff habs

theorem windowed_heat_saturated_identitySampleKernel_bridge_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveSampleKernel κ X)
    (a r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hK : K.IdentityAnchors)
    (hcoeff : K.liveCoeffSum + K.seedCoeffSum = a / (1 + r))
    (hstat :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (habs :
      ∀ t : NNReal, ∀ y : X,
        |(L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y| = r) :
    ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := X)
            (L.windowedColeHopfHeatSampleKernelInitialSlice
              (ι := ι) (X := X)
              selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
          (sampleKernelCompatibilityPred (Time := NNReal) (X := X) K)
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatSaturatedCandidate
            (ι := ι) (X := X)
            selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  exact
    L.exists_windowedColeHopfHeatSaturatedIdentitySampleKernelBridge_of_stationary_constantMagnitude
      (ι := ι) (X := X)
      selector K a r c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
      hK hcoeff hstat habs

end WindowedColeHopfHeatSaturatedIdentitySampleKernel

section WindowedColeHopfHeatSaturatedDiagonalSampleKernel

variable {ι X : Type*}
variable [Fintype ι] [AddMonoid X]

theorem windowed_heat_saturated_diagonalSampleKernel_initialSlice_eq_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (p q a r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hcoeff : p + q = a / (1 + r))
    (habs :
      ∀ t : NNReal, ∀ y : X,
        |(L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y| = r) :
    L.windowedColeHopfHeatSampleKernelInitialSlice
      (ι := ι) (X := X)
      selector (diagonalSampleKernel (X := X) p q) c ν hc hν
      curlFrame curlBound curlBound_nonneg hcurl x =
    L.windowedColeHopfHeatSaturatedInitialSlice
      (ι := ι) (X := X)
      selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  exact
    L.windowedColeHopfHeatDiagonalSampleKernelInitialSlice_eq_saturatedInitialSlice_of_constantMagnitude
      (ι := ι) (X := X)
      selector p q a r c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
      hcoeff habs

theorem windowed_heat_saturated_diagonalSampleKernel_candidate_eq_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (p q a r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hcoeff : p + q = a / (1 + r))
    (hstat :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (habs :
      ∀ t : NNReal, ∀ y : X,
        |(L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y| = r) :
    L.windowedColeHopfHeatSampleKernelCandidate
      (ι := ι) (X := X)
      selector (diagonalSampleKernel (X := X) p q) c ν hc hν
      curlFrame curlBound curlBound_nonneg hcurl x =
    L.windowedColeHopfHeatSaturatedCandidate
      (ι := ι) (X := X)
      selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  exact
    L.windowedColeHopfHeatDiagonalSampleKernelCandidate_eq_saturatedCandidate_of_stationary_constantMagnitude
      (ι := ι) (X := X)
      selector p q a r c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
      hcoeff hstat habs

theorem windowed_heat_saturated_diagonalSampleKernel_clause_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (p q a r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hcoeff : p + q = a / (1 + r))
    (habs :
      ∀ t : NNReal, ∀ y : X,
        |(L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y| = r) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatSaturatedInitialSlice
          (ι := ι) (X := X)
          selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) := by
  exact
    L.windowedColeHopfHeat_realizes_saturated_pressure_seeded_clause_via_diagonalSampleKernel_of_constantMagnitude
      (ι := ι) (X := X)
      selector p q a r c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
      hcoeff habs

theorem windowed_heat_saturated_diagonalSampleKernel_bridge_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (p q a r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hcoeff : p + q = a / (1 + r))
    (hstat :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (habs :
      ∀ t : NNReal, ∀ y : X,
        |(L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y| = r) :
    ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := X)
            (L.windowedColeHopfHeatSampleKernelInitialSlice
              (ι := ι) (X := X)
              selector (diagonalSampleKernel (X := X) p q) c ν hc hν
              curlFrame curlBound curlBound_nonneg hcurl x))
          (sampleKernelCompatibilityPred
            (Time := NNReal) (X := X)
            (diagonalSampleKernel (X := X) p q))
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatSaturatedCandidate
            (ι := ι) (X := X)
            selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  exact
    L.exists_windowedColeHopfHeatSaturatedDiagonalSampleKernelBridge_of_stationary_constantMagnitude
      (ι := ι) (X := X)
      selector p q a r c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
      hcoeff hstat habs

end WindowedColeHopfHeatSaturatedDiagonalSampleKernel

theorem zero_data_finiteInitialKineticEnergy_regression :
    finiteInitialKineticEnergy (0 : NSInitialVelocity) := by
  exact finiteInitialKineticEnergy_zero

theorem zero_data_repaired_regularity_regression
    {ν : ℝ} :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause ν (0 : NSInitialVelocity) := by
  exact ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_zero ν

theorem zero_data_unrepaired_regularity_constantPressure_regression
    {ν : ℝ} (c : ℝ) :
    ExplicitConcreteNavierStokesRegularityClause ν (0 : NSInitialVelocity) := by
  exact ExplicitConcreteNavierStokesRegularityClause_zero_constantPressure (ν := ν) c

theorem zero_data_unrepaired_regularity_timeOnlyPressure_regression
    {ν : ℝ} (π : NSTime → ℝ) (hπ : ContDiff ℝ ∞ π) :
    ExplicitConcreteNavierStokesRegularityClause ν (0 : NSInitialVelocity) := by
  exact ExplicitConcreteNavierStokesRegularityClause_zero_timeOnlyPressure (ν := ν) π hπ

theorem zero_data_repaired_regularity_constantPressure_regression
    {ν : ℝ} (c : ℝ) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause ν (0 : NSInitialVelocity) := by
  exact ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_zero_constantPressure (ν := ν) c

theorem zero_data_repaired_regularity_timeOnlyPressure_regression
    {ν : ℝ} (π : NSTime → ℝ) (hπ : ContDiff ℝ ∞ π) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause ν (0 : NSInitialVelocity) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_zero_timeOnlyPressure
      (ν := ν) π hπ

theorem concrete_clause_zero_regression
    {ν : ℝ} (hν : 0 < ν) :
    NavierStokesGlobalRegularityClause
      mkFullyConcreteNavierStokesSurface
      { viscosity := ν
        viscosity_pos := hν
        initialVelocity := (0 : NSInitialVelocity)
        smooth_initial := smoothInitialVelocityData_zero
        divergence_free_initial := by
          intro x
          simpa using (initialSpatialDivergence_zero x) } := by
  exact concreteNavierStokesGlobalRegularityClause_zero hν

theorem repaired_concrete_clause_zero_regression
    {ν : ℝ} (hν : 0 < ν) :
    NavierStokesGlobalRegularityClause
      mkFullyConcreteNavierStokesSurface
      ({ viscosity := ν
         viscosity_pos := hν
         initialVelocity := (0 : NSInitialVelocity)
         smooth_initial := smoothInitialVelocityData_zero
         divergence_free_initial := by
           intro x
           simpa using (initialSpatialDivergence_zero x)
         finite_initial_energy := finiteInitialKineticEnergy_zero } :
        FiniteEnergyAdmissibleNavierStokesProblemData).toNavierStokesProblemData := by
  exact finiteEnergyConcreteNavierStokesGlobalRegularityClause_zero hν

theorem concrete_clause_zero_add_zeroGradient_affinePressure_regression
    {ν : ℝ} (hν : 0 < ν)
    (a b c : ℝ)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    NavierStokesGlobalRegularityClause
      mkFullyConcreteNavierStokesSurface
      { viscosity := ν
        viscosity_pos := hν
        initialVelocity := (0 : NSInitialVelocity)
        smooth_initial := smoothInitialVelocityData_zero
        divergence_free_initial := by
          intro x
          simpa using (initialSpatialDivergence_zero x) } := by
  have hq_zero :
      ∀ t x,
        spatialPressureGradient
          (a • (fun _ : NSTime => fun _ : NSSpace => c) +
            b • (fun s : NSTime => fun _ : NSSpace => π s)) t x = 0 := by
    intro t x
    have hc :
        DifferentiableAt ℝ (fun y : NSSpace => (fun _ : NSTime => fun _ : NSSpace => c) t y) x :=
      smoothSpaceTimePressure_differentiableAt_spatialSlice
        (smoothSpaceTimePressure_const c) t x
    have hπx :
        DifferentiableAt ℝ (fun y : NSSpace => (fun s : NSTime => fun _ : NSSpace => π s) t y) x :=
      smoothSpaceTimePressure_differentiableAt_spatialSlice
        (smoothSpaceTimePressure_timeOnly hπ) t x
    rw [spatialPressureGradient_linearCombination
      (p := fun _ : NSTime => fun _ : NSSpace => c)
      (q := fun s : NSTime => fun _ : NSSpace => π s) a b hc hπx]
    rw [spatialPressureGradient_const, spatialPressureGradient_timeOnly]
    simp
  exact
    concreteNavierStokesGlobalRegularityClause_zero_addPressureOfZeroSpatialGradient
      hν
      (a • (fun _ : NSTime => fun _ : NSSpace => c) +
        b • (fun t : NSTime => fun _ : NSSpace => π t))
      (smoothSpaceTimePressure_linearCombination a b
        (smoothSpaceTimePressure_const c)
        (smoothSpaceTimePressure_timeOnly hπ))
      hq_zero

theorem repaired_concrete_clause_zero_add_zeroGradient_affinePressure_regression
    {ν : ℝ} (hν : 0 < ν)
    (a b c : ℝ)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    NavierStokesGlobalRegularityClause
      mkFullyConcreteNavierStokesSurface
      ({ viscosity := ν
         viscosity_pos := hν
         initialVelocity := (0 : NSInitialVelocity)
         smooth_initial := smoothInitialVelocityData_zero
         divergence_free_initial := by
           intro x
           simpa using (initialSpatialDivergence_zero x)
         finite_initial_energy := finiteInitialKineticEnergy_zero } :
        FiniteEnergyAdmissibleNavierStokesProblemData).toNavierStokesProblemData := by
  have hq_zero :
      ∀ t x,
        spatialPressureGradient
          (a • (fun _ : NSTime => fun _ : NSSpace => c) +
            b • (fun s : NSTime => fun _ : NSSpace => π s)) t x = 0 := by
    intro t x
    have hc :
        DifferentiableAt ℝ (fun y : NSSpace => (fun _ : NSTime => fun _ : NSSpace => c) t y) x :=
      smoothSpaceTimePressure_differentiableAt_spatialSlice
        (smoothSpaceTimePressure_const c) t x
    have hπx :
        DifferentiableAt ℝ (fun y : NSSpace => (fun s : NSTime => fun _ : NSSpace => π s) t y) x :=
      smoothSpaceTimePressure_differentiableAt_spatialSlice
        (smoothSpaceTimePressure_timeOnly hπ) t x
    rw [spatialPressureGradient_linearCombination
      (p := fun _ : NSTime => fun _ : NSSpace => c)
      (q := fun s : NSTime => fun _ : NSSpace => π s) a b hc hπx]
    rw [spatialPressureGradient_const, spatialPressureGradient_timeOnly]
    simp
  exact
    finiteEnergyConcreteNavierStokesGlobalRegularityClause_zero_addPressureOfZeroSpatialGradient
      hν
      (a • (fun _ : NSTime => fun _ : NSSpace => c) +
        b • (fun t : NSTime => fun _ : NSSpace => π t))
      (smoothSpaceTimePressure_linearCombination a b
        (smoothSpaceTimePressure_const c)
        (smoothSpaceTimePressure_timeOnly hπ))
      hq_zero

theorem zero_data_uniform_clause_regression
    {ν T : ℝ} :
    ExplicitUniformVorticityContinuationClause ν (0 : NSInitialVelocity) T := by
  exact ExplicitUniformVorticityContinuationClause_zero ν T

theorem zero_data_uniform_clause_from_explicit_regularity_regression
    {ν T : ℝ} :
    ExplicitUniformVorticityContinuationClause ν (0 : NSInitialVelocity) T := by
  exact
    ExplicitConcreteNavierStokesRegularityClause_implies_ExplicitUniformVorticityContinuationClause
      (T := T) (ExplicitConcreteNavierStokesRegularityClause_zero ν)

theorem zero_data_uniform_allHorizons_from_explicit_regularity_regression
    {ν T : ℝ} :
    ExplicitUniformVorticityContinuationClause ν (0 : NSInitialVelocity) T := by
  exact
    (ExplicitConcreteNavierStokesRegularityClause_implies_ExplicitUniformVorticityContinuationClause_allHorizons
      (ExplicitConcreteNavierStokesRegularityClause_zero ν)) T

theorem zero_data_repaired_uniform_clause_regression
    {ν T : ℝ} :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν (0 : NSInitialVelocity) T := by
  exact ExplicitFiniteEnergyUniformVorticityContinuationClause_zero ν T

theorem zero_data_repaired_uniform_clause_from_explicit_regularity_regression
    {ν T : ℝ} :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν (0 : NSInitialVelocity) T := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_implies_ExplicitFiniteEnergyUniformVorticityContinuationClause
      (T := T) (ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_zero ν)

theorem zero_data_repaired_uniform_allHorizons_from_explicit_regularity_regression
    {ν T : ℝ} :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν (0 : NSInitialVelocity) T := by
  exact
    (ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_implies_ExplicitFiniteEnergyUniformVorticityContinuationClause_allHorizons
      (ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_zero ν)) T

theorem zero_data_BKM_clause_regression
    {ν T : ℝ} :
    ExplicitBKMContinuationClause ν (0 : NSInitialVelocity) T := by
  exact ExplicitBKMContinuationClause_zero ν T

theorem zero_data_BKM_clause_from_explicit_regularity_regression
    {ν T : ℝ} :
    ExplicitBKMContinuationClause ν (0 : NSInitialVelocity) T := by
  exact
    ExplicitConcreteNavierStokesRegularityClause_implies_ExplicitBKMContinuationClause
      (T := T) (ExplicitConcreteNavierStokesRegularityClause_zero ν)

theorem zero_data_BKM_allHorizons_from_explicit_regularity_regression
    {ν T : ℝ} :
    ExplicitBKMContinuationClause ν (0 : NSInitialVelocity) T := by
  exact
    (ExplicitConcreteNavierStokesRegularityClause_implies_ExplicitBKMContinuationClause_allHorizons
      (ExplicitConcreteNavierStokesRegularityClause_zero ν)) T

theorem zero_data_repaired_BKM_clause_regression
    {ν T : ℝ} :
    ExplicitFiniteEnergyBKMContinuationClause ν (0 : NSInitialVelocity) T := by
  exact ExplicitFiniteEnergyBKMContinuationClause_zero ν T

theorem zero_data_repaired_BKM_clause_from_explicit_regularity_regression
    {ν T : ℝ} :
    ExplicitFiniteEnergyBKMContinuationClause ν (0 : NSInitialVelocity) T := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_implies_ExplicitFiniteEnergyBKMContinuationClause
      (T := T) (ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_zero ν)

theorem zero_data_repaired_BKM_allHorizons_from_explicit_regularity_regression
    {ν T : ℝ} :
    ExplicitFiniteEnergyBKMContinuationClause ν (0 : NSInitialVelocity) T := by
  exact
    (ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_implies_ExplicitFiniteEnergyBKMContinuationClause_allHorizons
      (ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_zero ν)) T

theorem smooth_velocity_linearCombination_regression
    (a b c : ℝ) :
    smoothSpaceTimeVelocity
      (a • constantVelocityField (EuclideanSpace.single nsCoord0 c) +
        b • linearShearVelocityField 1) := by
  exact
    smoothSpaceTimeVelocity_linearCombination a b
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord0 c))
      (smoothSpaceTimeVelocity_linearShearVelocityField 1)

theorem zero_globalOutput_add_zeroGradient_affinePressure_regression
    (ν a b c : ℝ)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  let q : NSPressureField :=
    a • (fun _ : NSTime => fun _ : NSSpace => c) +
      b • (fun t : NSTime => fun _ : NSSpace => π t)
  have hq : smoothSpaceTimePressure q := by
    dsimp [q]
    exact
      smoothSpaceTimePressure_linearCombination a b
        (smoothSpaceTimePressure_const c)
        (smoothSpaceTimePressure_timeOnly hπ)
  have hq_zero : ∀ t x, spatialPressureGradient q t x = 0 := by
    intro t x
    dsimp [q]
    exact spatialPressureGradient_affineConstantTimeOnly a b c π t x
  exact
    (ExplicitConcreteNavierStokesGlobalOutput_zero ν).addPressureOfZeroSpatialGradient
      q hq hq_zero

theorem zero_witness_uniformBound_add_zeroGradient_affinePressure_regression
    (ν T a b c : ℝ)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    ∃ B : ℝ,
      uniformVorticityBoundUpTo
        ((zeroFiniteTimeRegularityWitness ν T).addPressureOfZeroSpatialGradient
          (a • (fun _ : NSTime => fun _ : NSSpace => c) +
            b • (fun t : NSTime => fun _ : NSSpace => π t))
          (smoothSpaceTimePressure_linearCombination a b
            (smoothSpaceTimePressure_const c)
            (smoothSpaceTimePressure_timeOnly hπ))
          (spatialPressureGradient_affineConstantTimeOnly a b c π)).velocity
        T B := by
  refine ⟨0, ?_⟩
  have hω :
      uniformVorticityBoundUpTo (zeroFiniteTimeRegularityWitness ν T).velocity T 0 := by
    simpa [zeroFiniteTimeRegularityWitness] using uniformVorticityBoundUpTo_zero T
  exact
    (zeroFiniteTimeRegularityWitness ν T).uniformVorticityBound_addPressureOfZeroSpatialGradient
      hω
      (a • (fun _ : NSTime => fun _ : NSSpace => c) +
        b • (fun t : NSTime => fun _ : NSSpace => π t))
      (smoothSpaceTimePressure_linearCombination a b
        (smoothSpaceTimePressure_const c)
        (smoothSpaceTimePressure_timeOnly hπ))
      (spatialPressureGradient_affineConstantTimeOnly a b c π)

theorem zero_witness_BKMEnvelope_add_zeroGradient_affinePressure_regression
    (ν T a b c : ℝ)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
      vorticityEnvelopeOn
        ((zeroFiniteTimeRegularityWitness ν T).addPressureOfZeroSpatialGradient
          (a • (fun _ : NSTime => fun _ : NSSpace => c) +
            b • (fun t : NSTime => fun _ : NSSpace => π t))
          (smoothSpaceTimePressure_linearCombination a b
            (smoothSpaceTimePressure_const c)
            (smoothSpaceTimePressure_timeOnly hπ))
          (spatialPressureGradient_affineConstantTimeOnly a b c π)).velocity
        T Ω ∧
      integrableVorticityEnvelopeOn Ω T B := by
  exact
    (zeroFiniteTimeRegularityWitness ν T).BKMEnvelope_addPressureOfZeroSpatialGradient
      (zeroFiniteTimeRegularityWitness_has_BKMEnvelope ν T)
      (a • (fun _ : NSTime => fun _ : NSSpace => c) +
        b • (fun t : NSTime => fun _ : NSSpace => π t))
      (smoothSpaceTimePressure_linearCombination a b
        (smoothSpaceTimePressure_const c)
        (smoothSpaceTimePressure_timeOnly hπ))
      (spatialPressureGradient_affineConstantTimeOnly a b c π)

theorem zero_uniform_clause_add_zeroGradient_affinePressure_regression
    (ν Tsmall Tlarge a b c : ℝ)
    (hν : 0 < ν)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  let q : NSPressureField :=
    a • (fun _ : NSTime => fun _ : NSSpace => c) +
      b • (fun t : NSTime => fun _ : NSSpace => π t)
  have hq : smoothSpaceTimePressure q := by
    dsimp [q]
    exact
      smoothSpaceTimePressure_linearCombination a b
        (smoothSpaceTimePressure_const c)
        (smoothSpaceTimePressure_timeOnly hπ)
  have hq_zero : ∀ t x, spatialPressureGradient q t x = 0 := by
    intro t x
    dsimp [q]
    exact spatialPressureGradient_affineConstantTimeOnly a b c π t x
  exact
    ExplicitUniformVorticityContinuationClause_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      (hClause := ExplicitUniformVorticityContinuationClause_zero ν Tsmall)
      hν q hq hq_zero hT

theorem zero_repaired_BKM_clause_add_zeroGradient_affinePressure_regression
    (ν Tsmall Tlarge a b c : ℝ)
    (hν : 0 < ν)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  let q : NSPressureField :=
    a • (fun _ : NSTime => fun _ : NSSpace => c) +
      b • (fun t : NSTime => fun _ : NSSpace => π t)
  have hq : smoothSpaceTimePressure q := by
    dsimp [q]
    exact
      smoothSpaceTimePressure_linearCombination a b
        (smoothSpaceTimePressure_const c)
        (smoothSpaceTimePressure_timeOnly hπ)
  have hq_zero : ∀ t x, spatialPressureGradient q t x = 0 := by
    intro t x
    dsimp [q]
    exact spatialPressureGradient_affineConstantTimeOnly a b c π t x
  exact
    ExplicitFiniteEnergyBKMContinuationClause_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      (hClause := ExplicitFiniteEnergyBKMContinuationClause_zero ν Tsmall)
      hν q hq hq_zero hT

theorem explicit_target_zero_add_zeroGradient_affinePressure_regression
    (h : ExplicitConcreteNavierStokesMillenniumTarget)
    (ν a b c : ℝ)
    (hν : 0 < ν)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  let q : NSPressureField :=
    a • (fun _ : NSTime => fun _ : NSSpace => c) +
      b • (fun t : NSTime => fun _ : NSSpace => π t)
  have hq : smoothSpaceTimePressure q := by
    dsimp [q]
    exact
      smoothSpaceTimePressure_linearCombination a b
        (smoothSpaceTimePressure_const c)
        (smoothSpaceTimePressure_timeOnly hπ)
  have hq_zero : ∀ t x, spatialPressureGradient q t x = 0 := by
    intro t x
    dsimp [q]
    exact spatialPressureGradient_affineConstantTimeOnly a b c π t x
  exact
    ExplicitConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      h hν q hq hq_zero

theorem repaired_target_zero_add_zeroGradient_affinePressure_regression
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    (ν a b c : ℝ)
    (hν : 0 < ν)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  let q : NSPressureField :=
    a • (fun _ : NSTime => fun _ : NSSpace => c) +
      b • (fun t : NSTime => fun _ : NSSpace => π t)
  have hq : smoothSpaceTimePressure q := by
    dsimp [q]
    exact
      smoothSpaceTimePressure_linearCombination a b
        (smoothSpaceTimePressure_const c)
        (smoothSpaceTimePressure_timeOnly hπ)
  have hq_zero : ∀ t x, spatialPressureGradient q t x = 0 := by
    intro t x
    dsimp [q]
    exact spatialPressureGradient_affineConstantTimeOnly a b c π t x
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      h hν q hq hq_zero

theorem zero_unrepaired_regularity_add_zeroGradient_affinePressure_regression
    (ν a b c : ℝ)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    ExplicitConcreteNavierStokesRegularityClause ν (0 : NSInitialVelocity) := by
  let q : NSPressureField :=
    a • (fun _ : NSTime => fun _ : NSSpace => c) +
      b • (fun t : NSTime => fun _ : NSSpace => π t)
  have hq : smoothSpaceTimePressure q := by
    dsimp [q]
    exact
      smoothSpaceTimePressure_linearCombination a b
        (smoothSpaceTimePressure_const c)
        (smoothSpaceTimePressure_timeOnly hπ)
  have hq_zero : ∀ t x, spatialPressureGradient q t x = 0 := by
    intro t x
    dsimp [q]
    exact spatialPressureGradient_affineConstantTimeOnly a b c π t x
  exact
    ExplicitConcreteNavierStokesRegularityClause_zero_addPressureOfZeroSpatialGradient
      ν q hq hq_zero

theorem zero_repaired_regularity_add_zeroGradient_affinePressure_regression
    (ν a b c : ℝ)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause ν (0 : NSInitialVelocity) := by
  let q : NSPressureField :=
    a • (fun _ : NSTime => fun _ : NSSpace => c) +
      b • (fun t : NSTime => fun _ : NSSpace => π t)
  have hq : smoothSpaceTimePressure q := by
    dsimp [q]
    exact
      smoothSpaceTimePressure_linearCombination a b
        (smoothSpaceTimePressure_const c)
        (smoothSpaceTimePressure_timeOnly hπ)
  have hq_zero : ∀ t x, spatialPressureGradient q t x = 0 := by
    intro t x
    dsimp [q]
    exact spatialPressureGradient_affineConstantTimeOnly a b c π t x
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_zero_addPressureOfZeroSpatialGradient
      ν q hq hq_zero

theorem explicit_regularity_implies_finiteEnergy_regression
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (h : ExplicitConcreteNavierStokesRegularityClause ν u₀) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause ν u₀ := by
  exact ExplicitConcreteNavierStokesRegularityClause_implies_finiteEnergy h

theorem repaired_regularity_iff_of_finiteInitialKineticEnergy_regression
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (hfinite : finiteInitialKineticEnergy u₀) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause ν u₀ ↔
      ExplicitConcreteNavierStokesRegularityClause ν u₀ := by
  exact ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_iff_of_finiteInitialKineticEnergy hfinite

theorem repaired_regularity_implies_unrepaired_of_finiteInitialKineticEnergy_regression
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause ν u₀)
    (hfinite : finiteInitialKineticEnergy u₀) :
    ExplicitConcreteNavierStokesRegularityClause ν u₀ := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_implies_ExplicitConcreteNavierStokesRegularityClause_of_finiteInitialKineticEnergy
      h hfinite

theorem repaired_concrete_clause_iff_regression
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (hfinite : finiteInitialKineticEnergy u₀) :
    NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        ({ viscosity := ν
           viscosity_pos := hν
           initialVelocity := u₀
           smooth_initial := hsmooth
           divergence_free_initial := hdiv
           finite_initial_energy := hfinite } :
          FiniteEnergyAdmissibleNavierStokesProblemData).toNavierStokesProblemData
      ↔
        ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause ν u₀ := by
  exact finiteEnergyConcreteNavierStokesGlobalRegularityClause_iff hν hsmooth hdiv hfinite

theorem repaired_unrepaired_concrete_clause_iff_of_finiteInitialKineticEnergy_regression
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (hfinite : finiteInitialKineticEnergy u₀) :
    NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        ({ viscosity := ν
           viscosity_pos := hν
           initialVelocity := u₀
           smooth_initial := hsmooth
           divergence_free_initial := hdiv
           finite_initial_energy := hfinite } :
          FiniteEnergyAdmissibleNavierStokesProblemData).toNavierStokesProblemData
      ↔
        NavierStokesGlobalRegularityClause
          mkFullyConcreteNavierStokesSurface
          { viscosity := ν
            viscosity_pos := hν
            initialVelocity := u₀
            smooth_initial := hsmooth
            divergence_free_initial := hdiv } := by
  exact
    finiteEnergyConcreteNavierStokesGlobalRegularityClause_iff_of_finiteInitialKineticEnergy
      hν hsmooth hdiv hfinite

theorem repaired_concrete_clause_implies_unrepaired_of_finiteInitialKineticEnergy_regression
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (hfinite : finiteInitialKineticEnergy u₀)
    (h :
      NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        ({ viscosity := ν
           viscosity_pos := hν
           initialVelocity := u₀
           smooth_initial := hsmooth
           divergence_free_initial := hdiv
           finite_initial_energy := hfinite } :
          FiniteEnergyAdmissibleNavierStokesProblemData).toNavierStokesProblemData) :
    NavierStokesGlobalRegularityClause
      mkFullyConcreteNavierStokesSurface
      { viscosity := ν
        viscosity_pos := hν
        initialVelocity := u₀
        smooth_initial := hsmooth
        divergence_free_initial := hdiv } := by
  exact
    finiteEnergyConcreteNavierStokesGlobalRegularityClause_implies_concreteNavierStokesGlobalRegularityClause_of_finiteInitialKineticEnergy
      hν hsmooth hdiv hfinite h

theorem unrepaired_concrete_clause_implies_repaired_of_finiteInitialKineticEnergy_regression
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (hfinite : finiteInitialKineticEnergy u₀)
    (h :
      NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := u₀
          smooth_initial := hsmooth
          divergence_free_initial := hdiv }) :
    NavierStokesGlobalRegularityClause
      mkFullyConcreteNavierStokesSurface
      ({ viscosity := ν
         viscosity_pos := hν
         initialVelocity := u₀
         smooth_initial := hsmooth
         divergence_free_initial := hdiv
         finite_initial_energy := hfinite } :
        FiniteEnergyAdmissibleNavierStokesProblemData).toNavierStokesProblemData := by
  exact
    concreteNavierStokesGlobalRegularityClause_implies_finiteEnergyConcreteNavierStokesGlobalRegularityClause_of_finiteInitialKineticEnergy
      hν hsmooth hdiv hfinite h

theorem explicit_target_implies_finiteEnergy_regression
    (h : ExplicitConcreteNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget := by
  exact ExplicitConcreteNavierStokesMillenniumTarget_implies_finiteEnergy h

theorem concrete_target_iff_explicit_regression :
    ConcreteNavierStokesMillenniumTarget ↔ ExplicitConcreteNavierStokesMillenniumTarget := by
  exact ConcreteNavierStokesMillenniumTarget_iff_explicit

theorem repaired_concrete_target_iff_explicit_regression :
    FiniteEnergyConcreteNavierStokesMillenniumTarget ↔
      ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget := by
  exact FiniteEnergyConcreteNavierStokesMillenniumTarget_iff_explicit

theorem concrete_target_implies_explicit_regression
    (h : ConcreteNavierStokesMillenniumTarget) :
    ExplicitConcreteNavierStokesMillenniumTarget := by
  exact
    ConcreteNavierStokesMillenniumTarget_implies_ExplicitConcreteNavierStokesMillenniumTarget
      h

theorem repaired_concrete_target_implies_explicit_regression
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget := by
  exact
    FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget
      h

theorem concrete_target_implies_repaired_explicit_regression
    (h : ConcreteNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget := by
  exact
    ConcreteNavierStokesMillenniumTarget_implies_ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget
      h

theorem concrete_target_implies_finiteEnergy_regression
    (h : ConcreteNavierStokesMillenniumTarget) :
    FiniteEnergyConcreteNavierStokesMillenniumTarget := by
  exact ConcreteNavierStokesMillenniumTarget_implies_finiteEnergy h

theorem witness_component_shadow_regression
    {D : NavierStokesDifferentialKit} {P : NavierStokesProblemData D}
    (W : NavierStokesGlobalRegularityWitness D P)
    (i : Fin 3) :
    Nonempty (FeffermanGlobalRegularityOutput (D.toComponentPredicateKit P i)) := by
  exact ⟨W.toComponentFeffermanOutput i⟩

theorem clause_component_shadow_regression
    {D : NavierStokesDifferentialKit} {P : NavierStokesProblemData D}
    (h : NavierStokesGlobalRegularityClause D P)
    (i : Fin 3) :
    FeffermanGlobalRegularityClause (D.toComponentPredicateKit P i) := by
  exact NavierStokesGlobalRegularityClause.implies_componentFeffermanClause h i

theorem target_component_shadow_regression
    {D : NavierStokesDifferentialKit}
    (h : NavierStokesMillenniumTarget D)
    (i : Fin 3) :
    ∀ P : NavierStokesProblemData D,
      FeffermanGlobalRegularityClause (D.toComponentPredicateKit P i) := by
  exact NavierStokesMillenniumTarget.implies_componentFeffermanTarget h i

theorem explicit_target_uniform_clause_regression
    (h : ExplicitConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact ExplicitConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause h

theorem explicit_target_BKM_clause_regression
    (h : ExplicitConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitBKMContinuationClause ν u₀ T := by
  exact ExplicitConcreteNavierStokesMillenniumTarget_implies_BKMContinuationClause h

theorem explicit_target_repaired_uniform_clause_regression
    (h : ExplicitConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause
      h

theorem explicit_target_repaired_BKM_clause_regression
    (h : ExplicitConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyBKMContinuationClause ν u₀ T := by
  exact ExplicitConcreteNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationClause h

theorem concrete_target_uniform_clause_regression
    (h : ConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact ConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause h

theorem concrete_target_BKM_clause_regression
    (h : ConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitBKMContinuationClause ν u₀ T := by
  exact ConcreteNavierStokesMillenniumTarget_implies_BKMContinuationClause h

theorem concrete_target_repaired_uniform_clause_regression
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause
      h

theorem concrete_target_repaired_BKM_clause_regression
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyBKMContinuationClause ν u₀ T := by
  exact FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationClause h

theorem uniform_clause_implies_finiteEnergy_regression
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (h : ExplicitUniformVorticityContinuationClause ν u₀ T) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact ExplicitUniformVorticityContinuationClause_implies_finiteEnergy h

theorem uniform_target_implies_finiteEnergy_regression
    (h : ExplicitUniformVorticityContinuationTarget) :
    ExplicitFiniteEnergyUniformVorticityContinuationTarget := by
  exact
    ExplicitUniformVorticityContinuationTarget_implies_finiteEnergyUniformVorticityContinuationTarget
      h

theorem BKM_clause_implies_finiteEnergy_regression
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (h : ExplicitBKMContinuationClause ν u₀ T) :
    ExplicitFiniteEnergyBKMContinuationClause ν u₀ T := by
  exact ExplicitBKMContinuationClause_implies_finiteEnergy h

theorem BKM_target_implies_finiteEnergy_regression
    (h : ExplicitBKMContinuationTarget) :
    ExplicitFiniteEnergyBKMContinuationTarget := by
  exact ExplicitBKMContinuationTarget_implies_finiteEnergyBKMContinuationTarget h

theorem BKM_clause_uniform_clause_regression
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (h : ExplicitBKMContinuationClause ν u₀ T) :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact ExplicitBKMContinuationClause_implies_uniformVorticityContinuationClause h

theorem repaired_BKM_clause_repaired_uniform_clause_regression
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (h : ExplicitFiniteEnergyBKMContinuationClause ν u₀ T) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact ExplicitFiniteEnergyBKMContinuationClause_implies_finiteEnergyUniformVorticityContinuationClause h

theorem explicit_target_to_uniform_target_regression
    (h : ExplicitConcreteNavierStokesMillenniumTarget) :
    ExplicitUniformVorticityContinuationTarget := by
  exact ExplicitConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationTarget h

theorem explicit_target_to_uniform_allHorizons_regression
    (h : ExplicitConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    (ExplicitConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀) h) T

theorem explicit_target_to_BKM_target_regression
    (h : ExplicitConcreteNavierStokesMillenniumTarget) :
    ExplicitBKMContinuationTarget := by
  exact ExplicitConcreteNavierStokesMillenniumTarget_implies_BKMContinuationTarget h

theorem explicit_target_to_BKM_allHorizons_regression
    (h : ExplicitConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitBKMContinuationClause ν u₀ T := by
  exact
    (ExplicitConcreteNavierStokesMillenniumTarget_implies_BKMContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀) h) T

theorem explicit_target_to_repaired_uniform_target_regression
    (h : ExplicitConcreteNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyUniformVorticityContinuationTarget := by
  exact
    ExplicitConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationTarget
      h

theorem explicit_target_to_repaired_uniform_allHorizons_regression
    (h : ExplicitConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    (ExplicitConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀) h) T

theorem explicit_repaired_target_to_repaired_uniform_allHorizons_regression
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    (ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀) h) T

theorem explicit_target_to_repaired_BKM_target_regression
    (h : ExplicitConcreteNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyBKMContinuationTarget := by
  exact ExplicitConcreteNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationTarget h

theorem explicit_target_to_repaired_BKM_allHorizons_regression
    (h : ExplicitConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyBKMContinuationClause ν u₀ T := by
  exact
    (ExplicitConcreteNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀) h) T

theorem explicit_repaired_target_to_repaired_BKM_allHorizons_regression
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyBKMContinuationClause ν u₀ T := by
  exact
    (ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀) h) T

theorem concrete_target_to_uniform_target_regression
    (h : ConcreteNavierStokesMillenniumTarget) :
    ExplicitUniformVorticityContinuationTarget := by
  exact ConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationTarget h

theorem concrete_target_to_uniform_allHorizons_regression
    (h : ConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    (ConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀) h) T

theorem concrete_target_to_BKM_target_regression
    (h : ConcreteNavierStokesMillenniumTarget) :
    ExplicitBKMContinuationTarget := by
  exact ConcreteNavierStokesMillenniumTarget_implies_BKMContinuationTarget h

theorem concrete_target_to_BKM_allHorizons_regression
    (h : ConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitBKMContinuationClause ν u₀ T := by
  exact
    (ConcreteNavierStokesMillenniumTarget_implies_BKMContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀) h) T

theorem concrete_target_to_repaired_uniform_target_regression
    (h : ConcreteNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyUniformVorticityContinuationTarget := by
  exact ConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationTarget h

theorem concrete_target_to_repaired_uniform_allHorizons_regression
    (h : ConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    (ConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀) h) T

theorem concrete_target_to_repaired_BKM_target_regression
    (h : ConcreteNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyBKMContinuationTarget := by
  exact ConcreteNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationTarget h

theorem concrete_target_to_repaired_BKM_allHorizons_regression
    (h : ConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyBKMContinuationClause ν u₀ T := by
  exact
    (ConcreteNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀) h) T

theorem explicit_repaired_target_to_repaired_uniform_target_regression
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyUniformVorticityContinuationTarget := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationTarget
      h

theorem explicit_repaired_target_to_repaired_BKM_target_regression
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyBKMContinuationTarget := by
  exact ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationTarget h

theorem concrete_repaired_target_to_repaired_uniform_target_regression
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyUniformVorticityContinuationTarget := by
  exact
    FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationTarget
      h

theorem concrete_repaired_target_to_repaired_uniform_allHorizons_regression
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    (FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀) h) T

theorem concrete_repaired_target_to_repaired_BKM_target_regression
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyBKMContinuationTarget := by
  exact FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationTarget h

theorem concrete_repaired_target_to_repaired_BKM_allHorizons_regression
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyBKMContinuationClause ν u₀ T := by
  exact
    (FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_finiteEnergyBKMContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀) h) T

theorem explicit_target_zero_output_regression
    (h : ExplicitConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} (hν : 0 < ν) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact ExplicitConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput h hν

theorem explicit_target_zero_output_timeOnlyPressure_regression
    (h : ExplicitConcreteNavierStokesMillenniumTarget)
    {ν : ℝ}
    (hν : 0 < ν)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput_timeOnlyPressure
      h hν π hπ

theorem explicit_target_zero_output_constantPressure_regression
    (h : ExplicitConcreteNavierStokesMillenniumTarget)
    {ν : ℝ}
    (hν : 0 < ν)
    (c : ℝ) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput_constantPressure
      h hν c

theorem concrete_target_zero_output_regression
    (h : ConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} (hν : 0 < ν) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact ConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput h hν

theorem concrete_target_zero_output_timeOnlyPressure_regression
    (h : ConcreteNavierStokesMillenniumTarget)
    {ν : ℝ}
    (hν : 0 < ν)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact ConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput_timeOnlyPressure h hν π hπ

theorem concrete_target_zero_output_constantPressure_regression
    (h : ConcreteNavierStokesMillenniumTarget)
    {ν : ℝ}
    (hν : 0 < ν)
    (c : ℝ) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact ConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput_constantPressure h hν c

theorem explicit_repaired_target_zero_output_regression
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    {ν : ℝ} (hν : 0 < ν) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_zeroGlobalOutput h hν

theorem explicit_repaired_target_zero_output_timeOnlyPressure_regression
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    {ν : ℝ}
    (hν : 0 < ν)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_zeroGlobalOutput_timeOnlyPressure
      h hν π hπ

theorem explicit_repaired_target_zero_output_constantPressure_regression
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    {ν : ℝ}
    (hν : 0 < ν)
    (c : ℝ) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_zeroGlobalOutput_constantPressure
      h hν c

theorem concrete_repaired_target_zero_output_regression
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} (hν : 0 < ν) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput h hν

theorem concrete_repaired_target_zero_output_timeOnlyPressure_regression
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ}
    (hν : 0 < ν)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput_timeOnlyPressure
      h hν π hπ

theorem concrete_repaired_target_zero_output_constantPressure_regression
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ}
    (hν : 0 < ν)
    (c : ℝ) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput_constantPressure h hν c

theorem repaired_uniform_clause_iff_unrepaired_of_nonneg_horizon_regression
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T ↔
      ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact ExplicitFiniteEnergyUniformVorticityContinuationClause_iff_of_nonneg_horizon hT

theorem repaired_uniform_clause_unrepaired_uniform_clause_of_nonneg_horizon_regression
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (h : ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T)
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_implies_uniformVorticityContinuationClause_of_nonneg_horizon
      h hT

theorem repaired_uniform_target_unrepaired_uniform_clause_of_nonneg_horizon_regression
    (h : ExplicitFiniteEnergyUniformVorticityContinuationTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationTarget_implies_uniformVorticityContinuationClause_of_nonneg_horizon
      h hT

theorem repaired_uniform_target_unrepaired_uniform_allNonnegHorizons_regression
    (h : ExplicitFiniteEnergyUniformVorticityContinuationTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationTarget_implies_uniformVorticityContinuationClause_allNonnegHorizons
      (ν := ν) (u₀ := u₀) h hT

theorem repaired_uniform_clause_mono_horizon_regression
    {ν : ℝ} {u₀ : NSInitialVelocity} {Tsmall Tlarge : ℝ}
    (h : ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ Tsmall)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ Tlarge := by
  exact ExplicitFiniteEnergyUniformVorticityContinuationClause_mono_horizon h hT

theorem repaired_BKM_clause_iff_unrepaired_of_nonneg_horizon_regression
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitFiniteEnergyBKMContinuationClause ν u₀ T ↔
      ExplicitBKMContinuationClause ν u₀ T := by
  exact ExplicitFiniteEnergyBKMContinuationClause_iff_of_nonneg_horizon hT

theorem repaired_BKM_clause_mono_horizon_regression
    {ν : ℝ} {u₀ : NSInitialVelocity} {Tsmall Tlarge : ℝ}
    (h : ExplicitFiniteEnergyBKMContinuationClause ν u₀ Tsmall)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitFiniteEnergyBKMContinuationClause ν u₀ Tlarge := by
  exact ExplicitFiniteEnergyBKMContinuationClause_mono_horizon h hT

theorem BKM_clause_repaired_uniform_clause_regression
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (h : ExplicitBKMContinuationClause ν u₀ T) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitBKMContinuationClause_implies_finiteEnergyUniformVorticityContinuationClause h

theorem BKM_clause_repaired_uniform_clause_mono_horizon_regression
    {ν : ℝ} {u₀ : NSInitialVelocity} {Tsmall Tlarge : ℝ}
    (h : ExplicitBKMContinuationClause ν u₀ Tsmall)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ Tlarge := by
  exact
    ExplicitBKMContinuationClause_implies_finiteEnergyUniformVorticityContinuationClause_mono_horizon
      h hT

theorem repaired_BKM_clause_repaired_uniform_clause_mono_horizon_regression
    {ν : ℝ} {u₀ : NSInitialVelocity} {Tsmall Tlarge : ℝ}
    (h : ExplicitFiniteEnergyBKMContinuationClause ν u₀ Tsmall)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ Tlarge := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_implies_finiteEnergyUniformVorticityContinuationClause_mono_horizon
      h hT

theorem BKM_target_uniform_target_regression
    (h : ExplicitBKMContinuationTarget) :
    ExplicitUniformVorticityContinuationTarget := by
  exact ExplicitBKMContinuationTarget_implies_uniformVorticityContinuationTarget h

theorem BKM_target_uniform_allHorizons_regression
    (h : ExplicitBKMContinuationTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    (ExplicitBKMContinuationTarget_implies_uniformVorticityContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀) h) T

theorem BKM_target_repaired_uniform_target_regression
    (h : ExplicitBKMContinuationTarget) :
    ExplicitFiniteEnergyUniformVorticityContinuationTarget := by
  exact ExplicitBKMContinuationTarget_implies_finiteEnergyUniformVorticityContinuationTarget h

theorem BKM_target_repaired_uniform_allHorizons_regression
    (h : ExplicitBKMContinuationTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    (ExplicitBKMContinuationTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀) h) T

theorem repaired_BKM_target_uniform_target_regression
    (h : ExplicitFiniteEnergyBKMContinuationTarget) :
    ExplicitFiniteEnergyUniformVorticityContinuationTarget := by
  exact ExplicitFiniteEnergyBKMContinuationTarget_implies_finiteEnergyUniformVorticityContinuationTarget h

theorem repaired_BKM_target_repaired_uniform_allHorizons_regression
    (h : ExplicitFiniteEnergyBKMContinuationTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    (ExplicitFiniteEnergyBKMContinuationTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons
      (ν := ν) (u₀ := u₀) h) T

theorem explicit_target_uniform_target_via_BKM_regression
    (h : ExplicitConcreteNavierStokesMillenniumTarget) :
    ExplicitUniformVorticityContinuationTarget := by
  exact
    ExplicitConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationTarget_via_BKM
      h

theorem explicit_target_repaired_uniform_target_via_BKM_regression
    (h : ExplicitConcreteNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyUniformVorticityContinuationTarget := by
  exact
    ExplicitConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationTarget_via_BKM
      h

theorem explicit_repaired_target_repaired_uniform_target_via_BKM_regression
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyUniformVorticityContinuationTarget := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationTarget_via_BKM
      h

theorem concrete_repaired_target_repaired_uniform_target_via_BKM_regression
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyUniformVorticityContinuationTarget := by
  exact
    FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationTarget_via_BKM
      h

theorem concrete_target_uniform_target_via_BKM_regression
    (h : ConcreteNavierStokesMillenniumTarget) :
    ExplicitUniformVorticityContinuationTarget := by
  exact
    ConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationTarget_via_BKM
      h

theorem concrete_target_repaired_uniform_target_via_BKM_regression
    (h : ConcreteNavierStokesMillenniumTarget) :
    ExplicitFiniteEnergyUniformVorticityContinuationTarget := by
  exact
    ConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationTarget_via_BKM
      h

theorem explicit_target_uniform_allHorizons_via_BKM_regression
    (h : ExplicitConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    (ExplicitConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_allHorizons_via_BKM
      (ν := ν) (u₀ := u₀) h) T

theorem explicit_target_repaired_uniform_allHorizons_via_BKM_regression
    (h : ExplicitConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    (ExplicitConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons_via_BKM
      (ν := ν) (u₀ := u₀) h) T

theorem explicit_repaired_target_repaired_uniform_allHorizons_via_BKM_regression
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    (ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons_via_BKM
      (ν := ν) (u₀ := u₀) h) T

theorem concrete_repaired_target_repaired_uniform_allHorizons_via_BKM_regression
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    (FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons_via_BKM
      (ν := ν) (u₀ := u₀) h) T

theorem concrete_target_uniform_allHorizons_via_BKM_regression
    (h : ConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    (ConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_allHorizons_via_BKM
      (ν := ν) (u₀ := u₀) h) T

theorem concrete_target_repaired_uniform_allHorizons_via_BKM_regression
    (h : ConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ} :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  exact
    (ConcreteNavierStokesMillenniumTarget_implies_finiteEnergyUniformVorticityContinuationClause_allHorizons_via_BKM
      (ν := ν) (u₀ := u₀) h) T

theorem repaired_BKM_clause_unrepaired_BKM_clause_of_nonneg_horizon_regression
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (h : ExplicitFiniteEnergyBKMContinuationClause ν u₀ T)
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_implies_BKMContinuationClause_of_nonneg_horizon
      h hT

theorem repaired_BKM_target_unrepaired_BKM_clause_of_nonneg_horizon_regression
    (h : ExplicitFiniteEnergyBKMContinuationTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyBKMContinuationTarget_implies_BKMContinuationClause_of_nonneg_horizon
      h hT

theorem repaired_BKM_target_unrepaired_BKM_allNonnegHorizons_regression
    (h : ExplicitFiniteEnergyBKMContinuationTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyBKMContinuationTarget_implies_BKMContinuationClause_allNonnegHorizons
      (ν := ν) (u₀ := u₀) h hT

theorem repaired_BKM_clause_uniform_clause_of_nonneg_horizon_regression
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (h : ExplicitFiniteEnergyBKMContinuationClause ν u₀ T)
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_implies_uniformVorticityContinuationClause_of_nonneg_horizon
      h hT

theorem repaired_BKM_target_uniform_clause_of_nonneg_horizon_regression
    (h : ExplicitFiniteEnergyBKMContinuationTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyBKMContinuationTarget_implies_uniformVorticityContinuationClause_of_nonneg_horizon
      h hT

theorem repaired_BKM_target_uniform_allNonnegHorizons_regression
    (h : ExplicitFiniteEnergyBKMContinuationTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyBKMContinuationTarget_implies_uniformVorticityContinuationClause_allNonnegHorizons
      (ν := ν) (u₀ := u₀) h hT

theorem explicit_repaired_target_uniform_clause_of_nonneg_horizon_regression
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_of_nonneg_horizon
      h hT

theorem explicit_repaired_target_uniform_allNonnegHorizons_regression
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_allNonnegHorizons
      (ν := ν) (u₀ := u₀) h hT

theorem concrete_repaired_target_uniform_clause_of_nonneg_horizon_regression
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_of_nonneg_horizon
      h hT

theorem concrete_repaired_target_uniform_allNonnegHorizons_regression
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_allNonnegHorizons
      (ν := ν) (u₀ := u₀) h hT

theorem explicit_repaired_target_uniform_clause_of_nonneg_horizon_via_BKM_regression
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_of_nonneg_horizon_via_BKM
      (ν := ν) (u₀ := u₀) h hT

theorem explicit_repaired_target_uniform_allNonnegHorizons_via_BKM_regression
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_allNonnegHorizons_via_BKM
      (ν := ν) (u₀ := u₀) h hT

theorem concrete_repaired_target_uniform_clause_of_nonneg_horizon_via_BKM_regression
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_of_nonneg_horizon_via_BKM
      (ν := ν) (u₀ := u₀) h hT

theorem concrete_repaired_target_uniform_allNonnegHorizons_via_BKM_regression
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  exact
    FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_uniformVorticityContinuationClause_allNonnegHorizons_via_BKM
      (ν := ν) (u₀ := u₀) h hT

theorem explicit_repaired_target_BKM_clause_of_nonneg_horizon_regression
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_BKMContinuationClause_of_nonneg_horizon
      h hT

theorem explicit_repaired_target_BKM_allNonnegHorizons_regression
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν u₀ T := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_BKMContinuationClause_allNonnegHorizons
      (ν := ν) (u₀ := u₀) h hT

theorem concrete_repaired_target_BKM_clause_of_nonneg_horizon_regression
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν u₀ T := by
  exact
    FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_BKMContinuationClause_of_nonneg_horizon
      h hT

theorem concrete_repaired_target_BKM_allNonnegHorizons_regression
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν u₀ T := by
  exact
    FiniteEnergyConcreteNavierStokesMillenniumTarget_implies_BKMContinuationClause_allNonnegHorizons
      (ν := ν) (u₀ := u₀) h hT

theorem uniform_clause_zero_output_regression
    {ν T : ℝ}
    (h : ExplicitUniformVorticityContinuationClause ν (0 : NSInitialVelocity) T)
    (hν : 0 < ν) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact ExplicitUniformVorticityContinuationClause_implies_zeroGlobalOutput h hν

theorem uniform_clause_zero_output_timeOnlyPressure_regression
    {ν Tsmall Tlarge : ℝ}
    (h : ExplicitUniformVorticityContinuationClause ν (0 : NSInitialVelocity) Tsmall)
    (hν : 0 < ν)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact ExplicitUniformVorticityContinuationClause_implies_zeroGlobalOutput_timeOnlyPressure
    (Tsmall := Tsmall) (Tlarge := Tlarge) h hν π hπ hT

theorem uniform_clause_zero_output_constantPressure_regression
    {ν T : ℝ}
    (h : ExplicitUniformVorticityContinuationClause ν (0 : NSInitialVelocity) T)
    (hν : 0 < ν)
    (c : ℝ) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact ExplicitUniformVorticityContinuationClause_implies_zeroGlobalOutput_constantPressure
    (T := T) h hν c

theorem repaired_uniform_clause_zero_output_regression
    {ν T : ℝ}
    (h : ExplicitFiniteEnergyUniformVorticityContinuationClause ν (0 : NSInitialVelocity) T)
    (hν : 0 < ν) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact ExplicitFiniteEnergyUniformVorticityContinuationClause_implies_zeroGlobalOutput h hν

theorem repaired_uniform_clause_zero_output_timeOnlyPressure_regression
    {ν Tsmall Tlarge : ℝ}
    (h : ExplicitFiniteEnergyUniformVorticityContinuationClause ν (0 : NSInitialVelocity) Tsmall)
    (hν : 0 < ν)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_implies_zeroGlobalOutput_timeOnlyPressure
      (Tsmall := Tsmall) (Tlarge := Tlarge) h hν π hπ hT

theorem repaired_uniform_clause_zero_output_constantPressure_regression
    {ν T : ℝ}
    (h : ExplicitFiniteEnergyUniformVorticityContinuationClause ν (0 : NSInitialVelocity) T)
    (hν : 0 < ν)
    (c : ℝ) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact ExplicitFiniteEnergyUniformVorticityContinuationClause_implies_zeroGlobalOutput_constantPressure
    (T := T) h hν c

theorem BKM_clause_zero_output_regression
    {ν T : ℝ}
    (h : ExplicitBKMContinuationClause ν (0 : NSInitialVelocity) T)
    (hν : 0 < ν) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact ExplicitBKMContinuationClause_implies_zeroGlobalOutput h hν

theorem BKM_clause_zero_output_timeOnlyPressure_regression
    {ν Tsmall Tlarge : ℝ}
    (h : ExplicitBKMContinuationClause ν (0 : NSInitialVelocity) Tsmall)
    (hν : 0 < ν)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact ExplicitBKMContinuationClause_implies_zeroGlobalOutput_timeOnlyPressure
    (Tsmall := Tsmall) (Tlarge := Tlarge) h hν π hπ hT

theorem BKM_clause_zero_output_constantPressure_regression
    {ν T : ℝ}
    (h : ExplicitBKMContinuationClause ν (0 : NSInitialVelocity) T)
    (hν : 0 < ν)
    (c : ℝ) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact ExplicitBKMContinuationClause_implies_zeroGlobalOutput_constantPressure
    (T := T) h hν c

theorem repaired_BKM_clause_zero_output_regression
    {ν T : ℝ}
    (h : ExplicitFiniteEnergyBKMContinuationClause ν (0 : NSInitialVelocity) T)
    (hν : 0 < ν) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact ExplicitFiniteEnergyBKMContinuationClause_implies_zeroGlobalOutput h hν

theorem repaired_BKM_clause_zero_output_timeOnlyPressure_regression
    {ν Tsmall Tlarge : ℝ}
    (h : ExplicitFiniteEnergyBKMContinuationClause ν (0 : NSInitialVelocity) Tsmall)
    (hν : 0 < ν)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact ExplicitFiniteEnergyBKMContinuationClause_implies_zeroGlobalOutput_timeOnlyPressure
    (Tsmall := Tsmall) (Tlarge := Tlarge) h hν π hπ hT

theorem repaired_BKM_clause_zero_output_constantPressure_regression
    {ν T : ℝ}
    (h : ExplicitFiniteEnergyBKMContinuationClause ν (0 : NSInitialVelocity) T)
    (hν : 0 < ν)
    (c : ℝ) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact ExplicitFiniteEnergyBKMContinuationClause_implies_zeroGlobalOutput_constantPressure
    (T := T) h hν c

theorem uniform_target_zero_output_regression
    (h : ExplicitUniformVorticityContinuationTarget)
    {ν T : ℝ} (hν : 0 < ν) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact ExplicitUniformVorticityContinuationTarget_implies_zeroGlobalOutput
    (T := T) h hν

theorem uniform_target_zero_output_timeOnlyPressure_regression
    (h : ExplicitUniformVorticityContinuationTarget)
    {ν Tsmall Tlarge : ℝ}
    (hν : 0 < ν)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitUniformVorticityContinuationTarget_implies_zeroGlobalOutput_timeOnlyPressure
      (Tsmall := Tsmall) (Tlarge := Tlarge) h hν π hπ hT

theorem uniform_target_zero_output_constantPressure_regression
    (h : ExplicitUniformVorticityContinuationTarget)
    {ν T : ℝ} (hν : 0 < ν) (c : ℝ) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact ExplicitUniformVorticityContinuationTarget_implies_zeroGlobalOutput_constantPressure
    (T := T) h hν c

theorem repaired_uniform_target_zero_output_regression
    (h : ExplicitFiniteEnergyUniformVorticityContinuationTarget)
    {ν T : ℝ} (hν : 0 < ν) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact ExplicitFiniteEnergyUniformVorticityContinuationTarget_implies_zeroGlobalOutput
    (T := T) h hν

theorem repaired_uniform_target_zero_output_constantPressure_regression
    (h : ExplicitFiniteEnergyUniformVorticityContinuationTarget)
    {ν T : ℝ} (hν : 0 < ν) (c : ℝ) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationTarget_implies_zeroGlobalOutput_constantPressure
      (T := T) h hν c

theorem repaired_uniform_target_zero_output_timeOnlyPressure_regression
    (h : ExplicitFiniteEnergyUniformVorticityContinuationTarget)
    {ν Tsmall Tlarge : ℝ}
    (hν : 0 < ν)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationTarget_implies_zeroGlobalOutput_timeOnlyPressure
      (Tsmall := Tsmall) (Tlarge := Tlarge) h hν π hπ hT

theorem BKM_target_zero_output_timeOnlyPressure_regression
    (h : ExplicitBKMContinuationTarget)
    {ν Tsmall Tlarge : ℝ}
    (hν : 0 < ν)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitBKMContinuationTarget_implies_zeroGlobalOutput_timeOnlyPressure
      (Tsmall := Tsmall) (Tlarge := Tlarge) h hν π hπ hT

theorem BKM_target_zero_output_regression
    (h : ExplicitBKMContinuationTarget)
    {ν T : ℝ} (hν : 0 < ν) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact ExplicitBKMContinuationTarget_implies_zeroGlobalOutput
    (T := T) h hν

theorem BKM_target_zero_output_constantPressure_regression
    (h : ExplicitBKMContinuationTarget)
    {ν T : ℝ} (hν : 0 < ν) (c : ℝ) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact ExplicitBKMContinuationTarget_implies_zeroGlobalOutput_constantPressure
    (T := T) h hν c

theorem repaired_BKM_target_zero_output_constantPressure_regression
    (h : ExplicitFiniteEnergyBKMContinuationTarget)
    {ν T : ℝ} (hν : 0 < ν) (c : ℝ) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact ExplicitFiniteEnergyBKMContinuationTarget_implies_zeroGlobalOutput_constantPressure
    (T := T) h hν c

theorem repaired_BKM_target_zero_output_regression
    (h : ExplicitFiniteEnergyBKMContinuationTarget)
    {ν T : ℝ} (hν : 0 < ν) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact ExplicitFiniteEnergyBKMContinuationTarget_implies_zeroGlobalOutput
    (T := T) h hν

theorem repaired_BKM_target_zero_output_timeOnlyPressure_regression
    (h : ExplicitFiniteEnergyBKMContinuationTarget)
    {ν Tsmall Tlarge : ℝ}
    (hν : 0 < ν)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitFiniteEnergyBKMContinuationTarget_implies_zeroGlobalOutput_timeOnlyPressure
      (Tsmall := Tsmall) (Tlarge := Tlarge) h hν π hπ hT

theorem old_explicit_target_false_regression :
    ¬ ExplicitConcreteNavierStokesMillenniumTarget := by
  exact not_ExplicitConcreteNavierStokesMillenniumTarget

theorem old_concrete_target_false_regression :
    ¬ ConcreteNavierStokesMillenniumTarget := by
  exact not_ConcreteNavierStokesMillenniumTarget

def nonzeroConstantVelocity : NSSpace :=
  EuclideanSpace.single nsCoord0 (1 : ℝ)

theorem nonzeroConstantVelocity_ne_zero :
    nonzeroConstantVelocity ≠ 0 := by
  intro h
  simp [nonzeroConstantVelocity, EuclideanSpace.single_eq_zero_iff] at h

theorem constant_velocity_not_finiteInitialKineticEnergy_regression :
    ¬ finiteInitialKineticEnergy (constantInitialVelocity nonzeroConstantVelocity) := by
  exact not_finiteInitialKineticEnergy_constantInitialVelocity nonzeroConstantVelocity_ne_zero

theorem linear_shear_not_finiteInitialKineticEnergy_regression :
    ¬ finiteInitialKineticEnergy (linearShearInitialVelocity 1) := by
  exact
    not_finiteInitialKineticEnergy_linearShearInitialVelocity
      (a := 1) (by simp)

theorem repaired_structured_domain_exclusion_of_not_finiteInitialKineticEnergy_regression
    {u₀ : NSInitialVelocity}
    (hfinite : ¬ finiteInitialKineticEnergy u₀) :
    ¬ Nonempty { P : FiniteEnergyAdmissibleNavierStokesProblemData //
        P.initialVelocity = u₀ } := by
  exact
    not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_of_not_finiteInitialKineticEnergy
      hfinite

theorem repaired_structured_domain_nonempty_iff_finiteInitialKineticEnergy_regression
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0) :
    Nonempty { P : FiniteEnergyAdmissibleNavierStokesProblemData //
        P.viscosity = ν ∧ P.initialVelocity = u₀ } ↔
      finiteInitialKineticEnergy u₀ := by
  exact
    nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_iff hν hsmooth hdiv

theorem zero_data_repaired_structured_domain_regression
    {ν : ℝ} (hν : 0 < ν) :
    Nonempty { P : FiniteEnergyAdmissibleNavierStokesProblemData //
        P.viscosity = ν ∧ P.initialVelocity = (0 : NSInitialVelocity) } := by
  exact
    (nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_iff
      (ν := ν) (u₀ := (0 : NSInitialVelocity))
      hν smoothInitialVelocityData_zero (by
        intro x
        simpa using (initialSpatialDivergence_zero x))).2
      finiteInitialKineticEnergy_zero

theorem constant_velocity_not_in_repaired_structured_domain_regression :
    ¬ Nonempty { P : FiniteEnergyAdmissibleNavierStokesProblemData //
        P.initialVelocity = constantInitialVelocity nonzeroConstantVelocity } := by
  exact
    not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_constantInitialVelocity
      nonzeroConstantVelocity_ne_zero

theorem linear_shear_not_in_repaired_structured_domain_regression :
    ¬ Nonempty { P : FiniteEnergyAdmissibleNavierStokesProblemData //
        P.initialVelocity = linearShearInitialVelocity 1 } := by
  exact
    not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_linearShearInitialVelocity
      (by simp)

theorem constant_velocity_repaired_regularity_without_regularity_regression
    {ν : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
        ν (constantInitialVelocity nonzeroConstantVelocity) ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (constantInitialVelocity nonzeroConstantVelocity) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_constantInitialVelocity_without_regularity
      (ν := ν) hν nonzeroConstantVelocity_ne_zero

theorem constant_velocity_time_only_pressure_candidate_without_finiteTimeWitness_regression :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ 1 →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          (1 : ℝ) • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ 1 → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (constantInitialVelocity nonzeroConstantVelocity) u ∧
      uniformVorticityBoundUpTo u 1 B ∧
      ¬ boundedKineticEnergyUpTo u 1) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness 1 (constantInitialVelocity nonzeroConstantVelocity) 1) := by
  exact
    constantInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness_addPressureOfZeroSpatialGradient
      (ν := 1) (T := 1)
      nonzeroConstantVelocity_ne_zero
      (by norm_num)
      (fun t : NSTime => fun _ : NSSpace => t + 1)
      (smoothSpaceTimePressure_timeOnly (by simpa using
        (contDiff_id.add contDiff_const : ContDiff ℝ ∞ (fun s : NSTime => s + 1))))
      (fun t x => spatialPressureGradient_timeOnly (fun s : NSTime => s + 1) t x)

theorem linear_shear_repaired_regularity_without_regularity_regression
    {ν : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
        ν (linearShearInitialVelocity 1) ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν (linearShearInitialVelocity 1) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_linearShearInitialVelocity_without_regularity
      (ν := ν) hν (by simp)

theorem affine_shear_repaired_regularity_without_regularity_regression
    {ν : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
        ν (linearShearVerticalDriftInitialVelocity 1 1) ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (linearShearVerticalDriftInitialVelocity 1 1) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_linearShearVerticalDriftInitialVelocity_without_regularity
      (ν := ν) (a := 1) (b := 1) hν (by simp)

theorem horizontal_affine_shear_repaired_regularity_without_regularity_regression
    {ν : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
        ν (linearShearHorizontalDriftInitialVelocity 1 1) ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (linearShearHorizontalDriftInitialVelocity 1 1) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_linearShearHorizontalDriftInitialVelocity_without_regularity
      (ν := ν) (a := 1) (b := 1) hν (by simp)

theorem constant_velocity_structured_clause_false_regression
    {ν : ℝ} (hν : 0 < ν) :
    ¬ NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := constantInitialVelocity nonzeroConstantVelocity
          smooth_initial := smoothInitialVelocityData_constantInitialVelocity
            nonzeroConstantVelocity
          divergence_free_initial := by
            intro x
            simpa using
              initialSpatialDivergence_constantInitialVelocity
                nonzeroConstantVelocity x } := by
  exact
    not_concreteNavierStokesGlobalRegularityClause_constantInitialVelocity
      (ν := ν) hν nonzeroConstantVelocity_ne_zero

theorem linear_shear_structured_clause_false_regression
    {ν : ℝ} (hν : 0 < ν) :
    ¬ NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := linearShearInitialVelocity 1
          smooth_initial := smoothInitialVelocityData_linearShearInitialVelocity 1
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_linearShearInitialVelocity 1 x } := by
  exact
    not_concreteNavierStokesGlobalRegularityClause_linearShearInitialVelocity
      (ν := ν) hν (by simp)

theorem affine_shear_structured_clause_false_regression
    {ν : ℝ} (hν : 0 < ν) :
    ¬ NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := linearShearVerticalDriftInitialVelocity 1 1
          smooth_initial := smoothInitialVelocityData_linearShearVerticalDriftInitialVelocity 1 1
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_linearShearVerticalDriftInitialVelocity 1 1 x } := by
  exact
    not_concreteNavierStokesGlobalRegularityClause_linearShearVerticalDriftInitialVelocity
      (ν := ν) hν (by simp)

theorem horizontal_affine_shear_structured_clause_false_regression
    {ν : ℝ} (hν : 0 < ν) :
    ¬ NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := linearShearHorizontalDriftInitialVelocity 1 1
          smooth_initial := smoothInitialVelocityData_linearShearHorizontalDriftInitialVelocity 1 1
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_linearShearHorizontalDriftInitialVelocity 1 1 x } := by
  exact
    not_concreteNavierStokesGlobalRegularityClause_linearShearHorizontalDriftInitialVelocity
      (ν := ν) hν (by simp)

theorem constant_velocity_uniform_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause
        ν (constantInitialVelocity nonzeroConstantVelocity) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (constantInitialVelocity nonzeroConstantVelocity) := by
  exact
    ExplicitUniformVorticityContinuationClause_constantInitialVelocity_without_regularity
      (ν := ν) (T := T) hν nonzeroConstantVelocity_ne_zero hT

theorem constant_velocity_uniform_candidate_gap_regression
    {ν T : ℝ} (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (constantInitialVelocity nonzeroConstantVelocity) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness ν
          (constantInitialVelocity nonzeroConstantVelocity) T) := by
  exact
    constantInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness
      (ν := ν) (T := T) nonzeroConstantVelocity_ne_zero hT

theorem constant_velocity_BKM_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν (constantInitialVelocity nonzeroConstantVelocity) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (constantInitialVelocity nonzeroConstantVelocity) := by
  exact
    ExplicitBKMContinuationClause_constantInitialVelocity_without_regularity
      (ν := ν) (T := T) hν nonzeroConstantVelocity_ne_zero hT

theorem constant_velocity_BKM_candidate_gap_regression
    {ν T : ℝ} (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (constantInitialVelocity nonzeroConstantVelocity) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness ν
          (constantInitialVelocity nonzeroConstantVelocity) T) := by
  exact
    constantInitialVelocity_exhibits_BKMCandidate_without_finiteTimeWitness
      (ν := ν) (T := T) nonzeroConstantVelocity_ne_zero hT

theorem constant_velocity_time_only_pressure_BKM_candidate_gap_regression :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ 1 →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          (1 : ℝ) • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ 1 → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (constantInitialVelocity nonzeroConstantVelocity) u ∧
      vorticityEnvelopeOn u 1 (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) 1 (1 * B) ∧
      ¬ boundedKineticEnergyUpTo u 1) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness 1 (constantInitialVelocity nonzeroConstantVelocity) 1) := by
  exact
    constantInitialVelocity_exhibits_BKMCandidate_without_finiteTimeWitness_addPressureOfZeroSpatialGradient
      (ν := 1) (T := 1)
      nonzeroConstantVelocity_ne_zero
      (by norm_num)
      (fun t : NSTime => fun _ : NSSpace => t + 1)
      (smoothSpaceTimePressure_timeOnly (by simpa using
        (contDiff_id.add contDiff_const : ContDiff ℝ ∞ (fun s : NSTime => s + 1))))
      (fun t x => spatialPressureGradient_timeOnly (fun s : NSTime => s + 1) t x)

theorem linear_shear_uniform_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν (linearShearInitialVelocity 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν (linearShearInitialVelocity 1) := by
  exact
    ExplicitUniformVorticityContinuationClause_linearShearInitialVelocity_without_regularity
      (ν := ν) (T := T) hν (by simp) hT

theorem linear_shear_uniform_candidate_gap_regression
    {ν T : ℝ} (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearInitialVelocity 1) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty (ExplicitFiniteTimeRegularityWitness ν (linearShearInitialVelocity 1) T) := by
  exact
    linearShearInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness
      (ν := ν) (T := T) (a := 1) (by simp) hT

theorem linear_shear_BKM_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν (linearShearInitialVelocity 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν (linearShearInitialVelocity 1) := by
  exact
    ExplicitBKMContinuationClause_linearShearInitialVelocity_without_regularity
      (ν := ν) (T := T) hν (by simp) hT

theorem linear_shear_BKM_candidate_gap_regression
    {ν T : ℝ} (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearInitialVelocity 1) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty (ExplicitFiniteTimeRegularityWitness ν (linearShearInitialVelocity 1) T) := by
  exact
    linearShearInitialVelocity_exhibits_BKMCandidate_without_finiteTimeWitness
      (ν := ν) (T := T) (a := 1) (by simp) hT

theorem affine_shear_uniform_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause
        ν (linearShearVerticalDriftInitialVelocity 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (linearShearVerticalDriftInitialVelocity 1 1) := by
  exact
    ExplicitUniformVorticityContinuationClause_linearShearVerticalDriftInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (b := 1) hν (by simp) hT

theorem affine_shear_uniform_candidate_gap_regression
    {ν T : ℝ} (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearVerticalDriftInitialVelocity 1 1) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness ν (linearShearVerticalDriftInitialVelocity 1 1) T) := by
  exact
    linearShearVerticalDriftInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness
      (ν := ν) (T := T) (a := 1) (b := 1) (by simp) hT

theorem affine_shear_BKM_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν (linearShearVerticalDriftInitialVelocity 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (linearShearVerticalDriftInitialVelocity 1 1) := by
  exact
    ExplicitBKMContinuationClause_linearShearVerticalDriftInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (b := 1) hν (by simp) hT

theorem affine_shear_BKM_candidate_gap_regression
    {ν T : ℝ} (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearVerticalDriftInitialVelocity 1 1) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness ν (linearShearVerticalDriftInitialVelocity 1 1) T) := by
  exact
    linearShearVerticalDriftInitialVelocity_exhibits_BKMCandidate_without_finiteTimeWitness
      (ν := ν) (T := T) (a := 1) (b := 1) (by simp) hT

theorem horizontal_affine_shear_uniform_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause
        ν (linearShearHorizontalDriftInitialVelocity 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (linearShearHorizontalDriftInitialVelocity 1 1) := by
  exact
    ExplicitUniformVorticityContinuationClause_linearShearHorizontalDriftInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (b := 1) hν (by simp) hT

theorem horizontal_affine_shear_uniform_candidate_gap_regression
    {ν T : ℝ} (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearHorizontalDriftInitialVelocity 1 1) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness ν (linearShearHorizontalDriftInitialVelocity 1 1) T) := by
  exact
    linearShearHorizontalDriftInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness
      (ν := ν) (T := T) (a := 1) (b := 1) (by simp) hT

theorem horizontal_affine_shear_BKM_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν (linearShearHorizontalDriftInitialVelocity 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (linearShearHorizontalDriftInitialVelocity 1 1) := by
  exact
    ExplicitBKMContinuationClause_linearShearHorizontalDriftInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (b := 1) hν (by simp) hT

theorem horizontal_affine_shear_BKM_candidate_gap_regression
    {ν T : ℝ} (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearHorizontalDriftInitialVelocity 1 1) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness ν (linearShearHorizontalDriftInitialVelocity 1 1) T) := by
  exact
    linearShearHorizontalDriftInitialVelocity_exhibits_BKMCandidate_without_finiteTimeWitness
      (ν := ν) (T := T) (a := 1) (b := 1) (by simp) hT

theorem horizontal_affine_shear_time_only_pressure_uniform_candidate_gap_regression :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ 1 →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          (1 : ℝ) • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ 1 → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearHorizontalDriftInitialVelocity 1 1) u ∧
      uniformVorticityBoundUpTo u 1 B ∧
      ¬ boundedKineticEnergyUpTo u 1) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness 1 (linearShearHorizontalDriftInitialVelocity 1 1) 1) := by
  exact
    linearShearHorizontalDriftInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness_addTimeOnlyPressure
      (ν := 1) (T := 1) (a := 1) (b := 1) (by simp) (by norm_num)
      (fun s : NSTime => s + 1)
      (by simpa using
        (contDiff_id.add contDiff_const : ContDiff ℝ ∞ (fun s : NSTime => s + 1)))

theorem horizontal_affine_shear_time_only_pressure_BKM_candidate_gap_regression :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ 1 →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          (1 : ℝ) • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ 1 → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearHorizontalDriftInitialVelocity 1 1) u ∧
      vorticityEnvelopeOn u 1 (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) 1 (1 * B) ∧
      ¬ boundedKineticEnergyUpTo u 1) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness 1 (linearShearHorizontalDriftInitialVelocity 1 1) 1) := by
  exact
    linearShearHorizontalDriftInitialVelocity_exhibits_BKMCandidate_without_finiteTimeWitness_addTimeOnlyPressure
      (ν := 1) (T := 1) (a := 1) (b := 1) (by simp) (by norm_num)
      (fun s : NSTime => s + 1)
      (by simpa using
        (contDiff_id.add contDiff_const : ContDiff ℝ ∞ (fun s : NSTime => s + 1)))

theorem constant_velocity_repaired_uniform_clause_regression
    {ν T : ℝ} :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
      ν (constantInitialVelocity nonzeroConstantVelocity) T := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_constantInitialVelocity
      (ν := ν) (T := T) nonzeroConstantVelocity_ne_zero

theorem constant_velocity_repaired_BKM_clause_regression
    {ν T : ℝ} :
    ExplicitFiniteEnergyBKMContinuationClause
      ν (constantInitialVelocity nonzeroConstantVelocity) T := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_constantInitialVelocity
      (ν := ν) (T := T) nonzeroConstantVelocity_ne_zero

theorem linear_shear_repaired_uniform_clause_regression
    {ν T : ℝ} :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
      ν (linearShearInitialVelocity 1) T := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_linearShearInitialVelocity
      (ν := ν) (T := T) (by simp)

theorem linear_shear_repaired_BKM_clause_regression
    {ν T : ℝ} :
    ExplicitFiniteEnergyBKMContinuationClause ν (linearShearInitialVelocity 1) T := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_linearShearInitialVelocity
      (ν := ν) (T := T) (by simp)

theorem constant_velocity_repaired_uniform_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
        ν (constantInitialVelocity nonzeroConstantVelocity) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (constantInitialVelocity nonzeroConstantVelocity) := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_constantInitialVelocity_without_regularity
      (ν := ν) (T := T) hν nonzeroConstantVelocity_ne_zero

theorem constant_velocity_repaired_BKM_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyBKMContinuationClause
        ν (constantInitialVelocity nonzeroConstantVelocity) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (constantInitialVelocity nonzeroConstantVelocity) := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_constantInitialVelocity_without_regularity
      (ν := ν) (T := T) hν nonzeroConstantVelocity_ne_zero

theorem linear_shear_repaired_uniform_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
        ν (linearShearInitialVelocity 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (linearShearInitialVelocity 1) := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_linearShearInitialVelocity_without_regularity
      (ν := ν) (T := T) hν (by simp)

theorem linear_shear_repaired_BKM_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyBKMContinuationClause
        ν (linearShearInitialVelocity 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (linearShearInitialVelocity 1) := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_linearShearInitialVelocity_without_regularity
      (ν := ν) (T := T) hν (by simp)

theorem affine_shear_repaired_uniform_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
        ν (linearShearVerticalDriftInitialVelocity 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (linearShearVerticalDriftInitialVelocity 1 1) := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_linearShearVerticalDriftInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (b := 1) hν (by simp)

theorem affine_shear_repaired_BKM_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyBKMContinuationClause
        ν (linearShearVerticalDriftInitialVelocity 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (linearShearVerticalDriftInitialVelocity 1 1) := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_linearShearVerticalDriftInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (b := 1) hν (by simp)

theorem horizontal_affine_shear_repaired_uniform_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
        ν (linearShearHorizontalDriftInitialVelocity 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (linearShearHorizontalDriftInitialVelocity 1 1) := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_linearShearHorizontalDriftInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (b := 1) hν (by simp)

theorem horizontal_affine_shear_repaired_BKM_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyBKMContinuationClause
        ν (linearShearHorizontalDriftInitialVelocity 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (linearShearHorizontalDriftInitialVelocity 1 1) := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_linearShearHorizontalDriftInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (b := 1) hν (by simp)

theorem full_drift_affine_shear_repaired_regularity_without_regularity_regression
    {ν : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
        ν (linearShearFullDriftInitialVelocity 1 1 1) ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (linearShearFullDriftInitialVelocity 1 1 1) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_linearShearFullDriftInitialVelocity_without_regularity
      (ν := ν) (a := 1) (b := 1) (c := 1) hν (by simp)

theorem full_drift_affine_shear_structured_clause_false_regression
    {ν : ℝ} (hν : 0 < ν) :
    ¬ NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := linearShearFullDriftInitialVelocity 1 1 1
          smooth_initial := smoothInitialVelocityData_linearShearFullDriftInitialVelocity 1 1 1
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_linearShearFullDriftInitialVelocity 1 1 1 x } := by
  exact
    not_concreteNavierStokesGlobalRegularityClause_linearShearFullDriftInitialVelocity
      (ν := ν) hν (by simp)

theorem full_drift_affine_shear_uniform_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause
        ν (linearShearFullDriftInitialVelocity 1 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (linearShearFullDriftInitialVelocity 1 1 1) := by
  exact
    ExplicitUniformVorticityContinuationClause_linearShearFullDriftInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (b := 1) (c := 1) hν (by simp) hT

theorem full_drift_affine_shear_uniform_candidate_gap_regression
    {ν T : ℝ} (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearFullDriftInitialVelocity 1 1 1) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness ν (linearShearFullDriftInitialVelocity 1 1 1) T) := by
  exact
    linearShearFullDriftInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness
      (ν := ν) (T := T) (a := 1) (b := 1) (c := 1) (by simp) hT

theorem full_drift_affine_shear_BKM_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν (linearShearFullDriftInitialVelocity 1 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (linearShearFullDriftInitialVelocity 1 1 1) := by
  exact
    ExplicitBKMContinuationClause_linearShearFullDriftInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (b := 1) (c := 1) hν (by simp) hT

theorem full_drift_affine_shear_BKM_candidate_gap_regression
    {ν T : ℝ} (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearFullDriftInitialVelocity 1 1 1) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness ν (linearShearFullDriftInitialVelocity 1 1 1) T) := by
  exact
    linearShearFullDriftInitialVelocity_exhibits_BKMCandidate_without_finiteTimeWitness
      (ν := ν) (T := T) (a := 1) (b := 1) (c := 1) (by simp) hT

theorem full_drift_affine_shear_repaired_uniform_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
        ν (linearShearFullDriftInitialVelocity 1 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (linearShearFullDriftInitialVelocity 1 1 1) := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_linearShearFullDriftInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (b := 1) (c := 1) hν (by simp)

theorem full_drift_affine_shear_repaired_BKM_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyBKMContinuationClause
        ν (linearShearFullDriftInitialVelocity 1 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (linearShearFullDriftInitialVelocity 1 1 1) := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_linearShearFullDriftInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (b := 1) (c := 1) hν (by simp)

theorem linear_shear_zero_pressure_momentum_regression
    (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (linearShearVelocityField 1) t x +
        spatialConvection (linearShearVelocityField 1) t x +
        spatialPressureGradient (0 : NSPressureField) t x =
      spatialLaplacian (linearShearVelocityField 1) t x := by
  simpa using momentumEquation_linearShearVelocityField_zeroPressure 1 1 t x

theorem linear_shear_uniform_bound_regression
    (T : ℝ) :
    uniformVorticityBoundUpTo (linearShearVelocityField 1) T 1 := by
  simpa using uniformVorticityBoundUpTo_linearShearVelocityField 1 T

theorem linear_shear_BKM_envelope_regression
    {T : ℝ} (hT : 0 ≤ T) :
    vorticityEnvelopeOn (linearShearVelocityField 1) T (fun _ : NSTime => 1) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => 1) T T := by
  simpa using linearShearVelocityField_has_constantBKMEnvelope 1 T hT

theorem affine_shear_zero_pressure_momentum_regression
    (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (linearShearVerticalDriftVelocityField 1 1) t x +
        spatialConvection (linearShearVerticalDriftVelocityField 1 1) t x +
        spatialPressureGradient (0 : NSPressureField) t x =
      spatialLaplacian (linearShearVerticalDriftVelocityField 1 1) t x := by
  simpa using momentumEquation_linearShearVerticalDriftVelocityField_zeroPressure 1 1 1 t x

theorem affine_shear_uniform_bound_regression
    (T : ℝ) :
    uniformVorticityBoundUpTo (linearShearVerticalDriftVelocityField 1 1) T 1 := by
  simpa using uniformVorticityBoundUpTo_linearShearVerticalDriftVelocityField 1 1 T

theorem affine_shear_BKM_envelope_regression
    {T : ℝ} (hT : 0 ≤ T) :
    vorticityEnvelopeOn (linearShearVerticalDriftVelocityField 1 1) T
        (fun _ : NSTime => 1) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => 1) T T := by
  simpa using linearShearVerticalDriftVelocityField_has_constantBKMEnvelope 1 1 T hT

theorem horizontal_affine_shear_momentum_regression
    (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (linearShearHorizontalDriftVelocityField 1 1) t x +
        spatialConvection (linearShearHorizontalDriftVelocityField 1 1) t x +
        spatialPressureGradient (linearShearHorizontalDriftPressureField 1 1) t x =
      spatialLaplacian (linearShearHorizontalDriftVelocityField 1 1) t x := by
  simpa using momentumEquation_linearShearHorizontalDriftVelocityField 1 1 1 t x

theorem horizontal_affine_shear_uniform_bound_regression
    (T : ℝ) :
    uniformVorticityBoundUpTo (linearShearHorizontalDriftVelocityField 1 1) T 1 := by
  simpa using uniformVorticityBoundUpTo_linearShearHorizontalDriftVelocityField 1 1 T

theorem horizontal_affine_shear_BKM_envelope_regression
    {T : ℝ} (hT : 0 ≤ T) :
    vorticityEnvelopeOn (linearShearHorizontalDriftVelocityField 1 1) T
        (fun _ : NSTime => 1) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => 1) T T := by
  simpa using linearShearHorizontalDriftVelocityField_has_constantBKMEnvelope 1 1 T hT

theorem full_drift_affine_shear_momentum_regression
    (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (linearShearFullDriftVelocityField 1 1 1) t x +
        spatialConvection (linearShearFullDriftVelocityField 1 1 1) t x +
        spatialPressureGradient (linearShearHorizontalDriftPressureField 1 1) t x =
      spatialLaplacian (linearShearFullDriftVelocityField 1 1 1) t x := by
  simpa using momentumEquation_linearShearFullDriftVelocityField 1 1 1 1 t x

theorem full_drift_affine_shear_uniform_bound_regression
    (T : ℝ) :
    uniformVorticityBoundUpTo (linearShearFullDriftVelocityField 1 1 1) T 1 := by
  simpa using uniformVorticityBoundUpTo_linearShearFullDriftVelocityField 1 1 1 T

theorem full_drift_affine_shear_BKM_envelope_regression
    {T : ℝ} (hT : 0 ≤ T) :
    vorticityEnvelopeOn (linearShearFullDriftVelocityField 1 1 1) T
        (fun _ : NSTime => 1) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => 1) T T := by
  simpa using linearShearFullDriftVelocityField_has_constantBKMEnvelope 1 1 1 T hT

theorem heat_shear_zero_pressure_momentum_regression
    (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (heatShearVelocityField 1 1 1) t x +
        spatialConvection (heatShearVelocityField 1 1 1) t x +
        spatialPressureGradient (0 : NSPressureField) t x =
      spatialLaplacian (heatShearVelocityField 1 1 1) t x := by
  simpa using momentumEquation_heatShearVelocityField_zeroPressure 1 1 1 t x

theorem heat_shear_uniform_bound_regression
    (T : ℝ) :
    uniformVorticityBoundUpTo (heatShearVelocityField 1 1 1) T 1 := by
  simpa using uniformVorticityBoundUpTo_heatShearVelocityField 1 1 1 T (by positivity)

theorem heat_shear_BKM_envelope_regression
    {T : ℝ} (hT : 0 ≤ T) :
    vorticityEnvelopeOn (heatShearVelocityField 1 1 1) T (fun _ : NSTime => 1) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => 1) T T := by
  simpa using heatShearVelocityField_has_constantBKMEnvelope 1 1 1 T (by positivity) hT

theorem heat_shear_vertical_drift_zero_pressure_momentum_regression
    (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (heatShearVerticalDriftVelocityField 1 1 1 1) t x +
        spatialConvection (heatShearVerticalDriftVelocityField 1 1 1 1) t x +
        spatialPressureGradient (0 : NSPressureField) t x =
      spatialLaplacian (heatShearVerticalDriftVelocityField 1 1 1 1) t x := by
  simpa using momentumEquation_heatShearVerticalDriftVelocityField_zeroPressure 1 1 1 1 t x

theorem heat_shear_vertical_drift_uniform_bound_regression
    (T : ℝ) :
    uniformVorticityBoundUpTo (heatShearVerticalDriftVelocityField 1 1 1 1) T 1 := by
  simpa using
    uniformVorticityBoundUpTo_heatShearVerticalDriftVelocityField 1 1 1 1 T (by positivity)

theorem heat_shear_vertical_drift_BKM_envelope_regression
    {T : ℝ} (hT : 0 ≤ T) :
    vorticityEnvelopeOn (heatShearVerticalDriftVelocityField 1 1 1 1) T
        (fun _ : NSTime => 1) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => 1) T T := by
  simpa using
    heatShearVerticalDriftVelocityField_has_constantBKMEnvelope 1 1 1 1 T
      (by positivity) hT

theorem heat_shear_full_drift_zero_pressure_momentum_regression
    (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (heatShearFullDriftVelocityField 1 1 1 1 1) t x +
        spatialConvection (heatShearFullDriftVelocityField 1 1 1 1 1) t x +
        spatialPressureGradient (0 : NSPressureField) t x =
      spatialLaplacian (heatShearFullDriftVelocityField 1 1 1 1 1) t x := by
  simpa using momentumEquation_heatShearFullDriftVelocityField_zeroPressure 1 1 1 1 1 t x

theorem heat_shear_full_drift_uniform_bound_regression
    (T : ℝ) :
    uniformVorticityBoundUpTo (heatShearFullDriftVelocityField 1 1 1 1 1) T 1 := by
  simpa using
    uniformVorticityBoundUpTo_heatShearFullDriftVelocityField 1 1 1 1 1 T (by positivity)

theorem heat_shear_full_drift_BKM_envelope_regression
    {T : ℝ} (hT : 0 ≤ T) :
    vorticityEnvelopeOn (heatShearFullDriftVelocityField 1 1 1 1 1) T
        (fun _ : NSTime => 1) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => 1) T T := by
  simpa using
    heatShearFullDriftVelocityField_has_constantBKMEnvelope 1 1 1 1 1 T
      (by positivity) hT

theorem heat_shear_transport_zero_pressure_momentum_regression
    (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (heatShearTransportVelocityField 1 1 1 1) t x +
        spatialConvection (heatShearTransportVelocityField 1 1 1 1) t x +
        spatialPressureGradient (0 : NSPressureField) t x =
      spatialLaplacian (heatShearTransportVelocityField 1 1 1 1) t x := by
  simpa using momentumEquation_heatShearTransportVelocityField_zeroPressure 1 1 1 1 t x

theorem heat_shear_transport_uniform_bound_regression
    (T : ℝ) :
    uniformVorticityBoundUpTo (heatShearTransportVelocityField 1 1 1 1) T 1 := by
  simpa using
    uniformVorticityBoundUpTo_heatShearTransportVelocityField 1 1 1 1 T (by positivity)

theorem heat_shear_transport_BKM_envelope_regression
    {T : ℝ} (hT : 0 ≤ T) :
    vorticityEnvelopeOn (heatShearTransportVelocityField 1 1 1 1) T
        (fun _ : NSTime => 1) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => 1) T T := by
  simpa using
    heatShearTransportVelocityField_has_constantBKMEnvelope 1 1 1 1 T
      (by positivity) hT

theorem heat_shear_transport_full_drift_zero_pressure_momentum_regression
    (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (heatShearTransportFullDriftVelocityField 1 1 1 1 1 1) t x +
        spatialConvection (heatShearTransportFullDriftVelocityField 1 1 1 1 1 1) t x +
        spatialPressureGradient (0 : NSPressureField) t x =
      spatialLaplacian (heatShearTransportFullDriftVelocityField 1 1 1 1 1 1) t x := by
  simpa using
    momentumEquation_heatShearTransportFullDriftVelocityField_zeroPressure 1 1 1 1 1 1 t x

theorem heat_shear_transport_full_drift_uniform_bound_regression
    (T : ℝ) :
    uniformVorticityBoundUpTo (heatShearTransportFullDriftVelocityField 1 1 1 1 1 1) T 1 := by
  simpa using
    uniformVorticityBoundUpTo_heatShearTransportFullDriftVelocityField 1 1 1 1 1 1 T
      (by positivity)

theorem heat_shear_transport_full_drift_BKM_envelope_regression
    {T : ℝ} (hT : 0 ≤ T) :
    vorticityEnvelopeOn (heatShearTransportFullDriftVelocityField 1 1 1 1 1 1) T
        (fun _ : NSTime => 1) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => 1) T T := by
  simpa using
    heatShearTransportFullDriftVelocityField_has_constantBKMEnvelope 1 1 1 1 1 1 T
      (by positivity) hT

theorem heat_shear_not_finite_initial_energy_regression :
    ¬ finiteInitialKineticEnergy (heatShearInitialVelocity 1 1) := by
  exact not_finiteInitialKineticEnergy_heatShearInitialVelocity (a := 1) (k := 1) (by simp) (by simp)

theorem heat_shear_direct_unbounded_energy_regression :
    ¬ boundedKineticEnergy (heatShearVelocityField 1 1 1) := by
  exact
    not_boundedKineticEnergy_heatShearVelocityField
      (ν := 1) (a := 1) (k := 1) (by simp) (by simp)

theorem heat_shear_direct_unbounded_energy_up_to_regression
    {T : ℝ} (hT : 0 ≤ T) :
    ¬ boundedKineticEnergyUpTo (heatShearVelocityField 1 1 1) T := by
  exact
    not_boundedKineticEnergyUpTo_heatShearVelocityField
      (ν := 1) (a := 1) (k := 1) (by simp) (by simp) hT

theorem heat_shear_not_in_repaired_structured_domain_regression :
    ¬ Nonempty { P : FiniteEnergyAdmissibleNavierStokesProblemData //
        P.initialVelocity = heatShearInitialVelocity 1 1 } := by
  exact
    not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_heatShearInitialVelocity
      (a := 1) (k := 1) (by simp) (by simp)

theorem heat_shear_concrete_candidate_without_global_output_regression :
    (∃ u : NSVelocityField, ∃ p : NSPressureField,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x,
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          spatialLaplacian u t x) ∧
      (∀ t x, spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearInitialVelocity 1 1) u ∧
      ¬ boundedKineticEnergy u) ∧
      ¬ ExplicitConcreteNavierStokesGlobalOutput 1 (heatShearInitialVelocity 1 1) := by
  simpa using
    heatShearInitialVelocity_exhibits_concreteCandidate_without_globalOutput
      (ν := 1) (a := 1) (k := 1) (by simp) (by simp)

theorem heat_shear_uniform_candidate_gap_regression
    {T : ℝ} (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearInitialVelocity 1 1) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty (ExplicitFiniteTimeRegularityWitness 1 (heatShearInitialVelocity 1 1) T) := by
  simpa using
    heatShearInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness
      (ν := 1) (T := T) (a := 1) (k := 1) (by simp) (by simp) (by positivity) hT

theorem heat_shear_uniform_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν (heatShearInitialVelocity 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν (heatShearInitialVelocity 1 1) := by
  exact
    ExplicitUniformVorticityContinuationClause_heatShearInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (k := 1) hν (by simp) (by simp) hT

theorem heat_shear_repaired_uniform_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν (heatShearInitialVelocity 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν (heatShearInitialVelocity 1 1) := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_heatShearInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (k := 1) hν (by simp) (by simp)

theorem heat_shear_repaired_regularity_without_regularity_regression
    {ν : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
        ν (heatShearInitialVelocity 1 1) ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν (heatShearInitialVelocity 1 1) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearInitialVelocity_without_regularity
      (ν := ν) (a := 1) (k := 1) hν (by simp) (by simp)

theorem heat_shear_structured_clause_false_regression
    {ν : ℝ} (hν : 0 < ν) :
    ¬ NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := heatShearInitialVelocity 1 1
          smooth_initial := smoothInitialVelocityData_heatShearInitialVelocity 1 1
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_heatShearInitialVelocity 1 1 x } := by
  exact
    not_concreteNavierStokesGlobalRegularityClause_heatShearInitialVelocity
      (ν := ν) (a := 1) (k := 1) hν (by simp) (by simp)

theorem heat_shear_BKM_candidate_gap_regression
    {T : ℝ} (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearInitialVelocity 1 1) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty (ExplicitFiniteTimeRegularityWitness 1 (heatShearInitialVelocity 1 1) T) := by
  simpa using
    heatShearInitialVelocity_exhibits_BKMCandidate_without_finiteTimeWitness
      (ν := 1) (T := T) (a := 1) (k := 1) (by simp) (by simp) (by positivity) hT

theorem heat_shear_BKM_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν (heatShearInitialVelocity 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν (heatShearInitialVelocity 1 1) := by
  exact
    ExplicitBKMContinuationClause_heatShearInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (k := 1) hν (by simp) (by simp) hT

theorem heat_shear_repaired_BKM_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyBKMContinuationClause ν (heatShearInitialVelocity 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν (heatShearInitialVelocity 1 1) := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_heatShearInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (k := 1) hν (by simp) (by simp)

theorem heat_shear_streamwise_drift_not_finite_initial_energy_regression :
    ¬ finiteInitialKineticEnergy (heatShearStreamwiseDriftInitialVelocity 1 1 1) := by
  exact
    not_finiteInitialKineticEnergy_heatShearStreamwiseDriftInitialVelocity
      (a := 1) (k := 1) (d := 1) (by simp)

theorem heat_shear_streamwise_drift_direct_unbounded_energy_regression :
    ¬ boundedKineticEnergy (heatShearStreamwiseDriftVelocityField 1 1 1 1) := by
  exact
    not_boundedKineticEnergy_heatShearStreamwiseDriftVelocityField
      (ν := 1) (a := 1) (k := 1) (d := 1) (by simp)

theorem heat_shear_streamwise_drift_direct_unbounded_energy_up_to_regression
    {T : ℝ} (hT : 0 ≤ T) :
    ¬ boundedKineticEnergyUpTo (heatShearStreamwiseDriftVelocityField 1 1 1 1) T := by
  exact
    not_boundedKineticEnergyUpTo_heatShearStreamwiseDriftVelocityField
      (ν := 1) (a := 1) (k := 1) (d := 1) (by simp) hT

theorem heat_shear_streamwise_drift_concrete_candidate_without_global_output_regression :
    (∃ u : NSVelocityField, ∃ p : NSPressureField,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x,
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          spatialLaplacian u t x) ∧
      (∀ t x, spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearStreamwiseDriftInitialVelocity 1 1 1) u ∧
      ¬ boundedKineticEnergy u) ∧
      ¬ ExplicitConcreteNavierStokesGlobalOutput 1
        (heatShearStreamwiseDriftInitialVelocity 1 1 1) := by
  simpa using
    heatShearStreamwiseDriftInitialVelocity_exhibits_concreteCandidate_without_globalOutput
      (ν := 1) (a := 1) (k := 1) (d := 1) (by simp)

theorem heat_shear_streamwise_drift_uniform_candidate_gap_regression
    {T : ℝ} (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearStreamwiseDriftInitialVelocity 1 1 1) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty (ExplicitFiniteTimeRegularityWitness 1
        (heatShearStreamwiseDriftInitialVelocity 1 1 1) T) := by
  simpa using
    heatShearStreamwiseDriftInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness
      (ν := 1) (T := T) (a := 1) (k := 1) (d := 1) (by simp) (by positivity) hT

theorem heat_shear_streamwise_drift_uniform_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν
        (heatShearStreamwiseDriftInitialVelocity 1 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearStreamwiseDriftInitialVelocity 1 1 1) := by
  exact
    ExplicitUniformVorticityContinuationClause_heatShearStreamwiseDriftInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (k := 1) (d := 1) hν (by simp) hT

theorem heat_shear_streamwise_drift_repaired_uniform_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
        ν (heatShearStreamwiseDriftInitialVelocity 1 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearStreamwiseDriftInitialVelocity 1 1 1) := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_heatShearStreamwiseDriftInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (k := 1) (d := 1) hν (by simp)

theorem heat_shear_streamwise_drift_repaired_regularity_without_regularity_regression
    {ν : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
        ν (heatShearStreamwiseDriftInitialVelocity 1 1 1) ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearStreamwiseDriftInitialVelocity 1 1 1) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearStreamwiseDriftInitialVelocity_without_regularity
      (ν := ν) (a := 1) (k := 1) (d := 1) hν (by simp)

theorem heat_shear_streamwise_drift_structured_clause_false_regression
    {ν : ℝ} (hν : 0 < ν) :
    ¬ NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := heatShearStreamwiseDriftInitialVelocity 1 1 1
          smooth_initial := smoothInitialVelocityData_heatShearStreamwiseDriftInitialVelocity 1 1 1
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_heatShearStreamwiseDriftInitialVelocity 1 1 1 x } := by
  exact
    not_concreteNavierStokesGlobalRegularityClause_heatShearStreamwiseDriftInitialVelocity
      (ν := ν) (a := 1) (k := 1) (d := 1) hν (by simp)

theorem heat_shear_streamwise_drift_BKM_candidate_gap_regression
    {T : ℝ} (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearStreamwiseDriftInitialVelocity 1 1 1) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty (ExplicitFiniteTimeRegularityWitness 1
        (heatShearStreamwiseDriftInitialVelocity 1 1 1) T) := by
  simpa using
    heatShearStreamwiseDriftInitialVelocity_exhibits_BKMCandidate_without_finiteTimeWitness
      (ν := 1) (T := T) (a := 1) (k := 1) (d := 1) (by simp) (by positivity) hT

theorem heat_shear_streamwise_drift_BKM_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν
        (heatShearStreamwiseDriftInitialVelocity 1 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearStreamwiseDriftInitialVelocity 1 1 1) := by
  exact
    ExplicitBKMContinuationClause_heatShearStreamwiseDriftInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (k := 1) (d := 1) hν (by simp) hT

theorem heat_shear_streamwise_drift_repaired_BKM_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyBKMContinuationClause
        ν (heatShearStreamwiseDriftInitialVelocity 1 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearStreamwiseDriftInitialVelocity 1 1 1) := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_heatShearStreamwiseDriftInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (k := 1) (d := 1) hν (by simp)

theorem heat_shear_vertical_drift_not_finite_initial_energy_regression :
    ¬ finiteInitialKineticEnergy (heatShearVerticalDriftInitialVelocity 1 1 1) := by
  exact
    not_finiteInitialKineticEnergy_heatShearVerticalDriftInitialVelocity
      (a := 1) (k := 1) (c := 1) (by simp) (by simp)

theorem heat_shear_vertical_drift_direct_unbounded_energy_regression :
    ¬ boundedKineticEnergy (heatShearVerticalDriftVelocityField 1 1 1 1) := by
  exact
    not_boundedKineticEnergy_heatShearVerticalDriftVelocityField
      (ν := 1) (a := 1) (k := 1) (c := 1) (by simp) (by simp)

theorem heat_shear_vertical_drift_direct_unbounded_energy_up_to_regression
    {T : ℝ} (hT : 0 ≤ T) :
    ¬ boundedKineticEnergyUpTo (heatShearVerticalDriftVelocityField 1 1 1 1) T := by
  exact
    not_boundedKineticEnergyUpTo_heatShearVerticalDriftVelocityField
      (ν := 1) (a := 1) (k := 1) (c := 1) (by simp) (by simp) hT

theorem heat_shear_vertical_drift_concrete_candidate_without_global_output_regression :
    (∃ u : NSVelocityField, ∃ p : NSPressureField,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x,
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          spatialLaplacian u t x) ∧
      (∀ t x, spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearVerticalDriftInitialVelocity 1 1 1) u ∧
      ¬ boundedKineticEnergy u) ∧
      ¬ ExplicitConcreteNavierStokesGlobalOutput 1
        (heatShearVerticalDriftInitialVelocity 1 1 1) := by
  simpa using
    heatShearVerticalDriftInitialVelocity_exhibits_concreteCandidate_without_globalOutput
      (ν := 1) (a := 1) (k := 1) (c := 1) (by simp) (by simp)

theorem heat_shear_vertical_drift_uniform_candidate_gap_regression
    {T : ℝ} (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearVerticalDriftInitialVelocity 1 1 1) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty (ExplicitFiniteTimeRegularityWitness 1 (heatShearVerticalDriftInitialVelocity 1 1 1) T) := by
  simpa using
    heatShearVerticalDriftInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness
      (ν := 1) (T := T) (a := 1) (k := 1) (c := 1) (by simp) (by simp) (by positivity) hT

theorem heat_shear_vertical_drift_uniform_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν (heatShearVerticalDriftInitialVelocity 1 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearVerticalDriftInitialVelocity 1 1 1) := by
  exact
    ExplicitUniformVorticityContinuationClause_heatShearVerticalDriftInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (k := 1) (c := 1) hν (by simp) (by simp) hT

theorem heat_shear_vertical_drift_repaired_uniform_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
        ν (heatShearVerticalDriftInitialVelocity 1 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearVerticalDriftInitialVelocity 1 1 1) := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_heatShearVerticalDriftInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (k := 1) (c := 1) hν (by simp) (by simp)

theorem heat_shear_vertical_drift_repaired_regularity_without_regularity_regression
    {ν : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
        ν (heatShearVerticalDriftInitialVelocity 1 1 1) ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearVerticalDriftInitialVelocity 1 1 1) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearVerticalDriftInitialVelocity_without_regularity
      (ν := ν) (a := 1) (k := 1) (c := 1) hν (by simp) (by simp)

theorem heat_shear_vertical_drift_structured_clause_false_regression
    {ν : ℝ} (hν : 0 < ν) :
    ¬ NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := heatShearVerticalDriftInitialVelocity 1 1 1
          smooth_initial := smoothInitialVelocityData_heatShearVerticalDriftInitialVelocity 1 1 1
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_heatShearVerticalDriftInitialVelocity 1 1 1 x } := by
  exact
    not_concreteNavierStokesGlobalRegularityClause_heatShearVerticalDriftInitialVelocity
      (ν := ν) (a := 1) (k := 1) (c := 1) hν (by simp) (by simp)

theorem heat_shear_vertical_drift_BKM_candidate_gap_regression
    {T : ℝ} (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearVerticalDriftInitialVelocity 1 1 1) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty (ExplicitFiniteTimeRegularityWitness 1 (heatShearVerticalDriftInitialVelocity 1 1 1) T) := by
  simpa using
    heatShearVerticalDriftInitialVelocity_exhibits_BKMCandidate_without_finiteTimeWitness
      (ν := 1) (T := T) (a := 1) (k := 1) (c := 1) (by simp) (by simp) (by positivity) hT

theorem heat_shear_vertical_drift_BKM_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν (heatShearVerticalDriftInitialVelocity 1 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearVerticalDriftInitialVelocity 1 1 1) := by
  exact
    ExplicitBKMContinuationClause_heatShearVerticalDriftInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (k := 1) (c := 1) hν (by simp) (by simp) hT

theorem heat_shear_vertical_drift_repaired_BKM_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyBKMContinuationClause
        ν (heatShearVerticalDriftInitialVelocity 1 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearVerticalDriftInitialVelocity 1 1 1) := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_heatShearVerticalDriftInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (k := 1) (c := 1) hν (by simp) (by simp)

theorem heat_shear_full_drift_not_finite_initial_energy_regression :
    ¬ finiteInitialKineticEnergy (heatShearFullDriftInitialVelocity 1 1 1 1) := by
  exact
    not_finiteInitialKineticEnergy_heatShearFullDriftInitialVelocity
      (a := 1) (k := 1) (d := 1) (c := 1) (by simp)

theorem heat_shear_full_drift_direct_unbounded_energy_regression :
    ¬ boundedKineticEnergy (heatShearFullDriftVelocityField 1 1 1 1 1) := by
  exact
    not_boundedKineticEnergy_heatShearFullDriftVelocityField
      (ν := 1) (a := 1) (k := 1) (d := 1) (c := 1) (by simp)

theorem heat_shear_full_drift_direct_unbounded_energy_up_to_regression
    {T : ℝ} (hT : 0 ≤ T) :
    ¬ boundedKineticEnergyUpTo (heatShearFullDriftVelocityField 1 1 1 1 1) T := by
  exact
    not_boundedKineticEnergyUpTo_heatShearFullDriftVelocityField
      (ν := 1) (a := 1) (k := 1) (d := 1) (c := 1) (by simp) hT

theorem heat_shear_full_drift_concrete_candidate_without_global_output_regression :
    (∃ u : NSVelocityField, ∃ p : NSPressureField,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x,
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          spatialLaplacian u t x) ∧
      (∀ t x, spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearFullDriftInitialVelocity 1 1 1 1) u ∧
      ¬ boundedKineticEnergy u) ∧
      ¬ ExplicitConcreteNavierStokesGlobalOutput 1
        (heatShearFullDriftInitialVelocity 1 1 1 1) := by
  simpa using
    heatShearFullDriftInitialVelocity_exhibits_concreteCandidate_without_globalOutput
      (ν := 1) (a := 1) (k := 1) (d := 1) (c := 1) (by simp)

theorem heat_shear_full_drift_uniform_candidate_gap_regression
    {T : ℝ} (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearFullDriftInitialVelocity 1 1 1 1) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty (ExplicitFiniteTimeRegularityWitness 1
        (heatShearFullDriftInitialVelocity 1 1 1 1) T) := by
  simpa using
    heatShearFullDriftInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness
      (ν := 1) (T := T) (a := 1) (k := 1) (d := 1) (c := 1) (by simp) (by positivity) hT

theorem heat_shear_full_drift_uniform_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν
        (heatShearFullDriftInitialVelocity 1 1 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearFullDriftInitialVelocity 1 1 1 1) := by
  exact
    ExplicitUniformVorticityContinuationClause_heatShearFullDriftInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (k := 1) (d := 1) (c := 1) hν (by simp) hT

theorem heat_shear_full_drift_repaired_uniform_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
        ν (heatShearFullDriftInitialVelocity 1 1 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearFullDriftInitialVelocity 1 1 1 1) := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_heatShearFullDriftInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (k := 1) (d := 1) (c := 1) hν (by simp)

theorem heat_shear_full_drift_repaired_regularity_without_regularity_regression
    {ν : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
        ν (heatShearFullDriftInitialVelocity 1 1 1 1) ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearFullDriftInitialVelocity 1 1 1 1) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearFullDriftInitialVelocity_without_regularity
      (ν := ν) (a := 1) (k := 1) (d := 1) (c := 1) hν (by simp)

theorem heat_shear_full_drift_structured_clause_false_regression
    {ν : ℝ} (hν : 0 < ν) :
    ¬ NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := heatShearFullDriftInitialVelocity 1 1 1 1
          smooth_initial := smoothInitialVelocityData_heatShearFullDriftInitialVelocity 1 1 1 1
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_heatShearFullDriftInitialVelocity 1 1 1 1 x } := by
  exact
    not_concreteNavierStokesGlobalRegularityClause_heatShearFullDriftInitialVelocity
      (ν := ν) (a := 1) (k := 1) (d := 1) (c := 1) hν (by simp)

theorem heat_shear_full_drift_BKM_candidate_gap_regression
    {T : ℝ} (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearFullDriftInitialVelocity 1 1 1 1) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty (ExplicitFiniteTimeRegularityWitness 1
        (heatShearFullDriftInitialVelocity 1 1 1 1) T) := by
  simpa using
    heatShearFullDriftInitialVelocity_exhibits_BKMCandidate_without_finiteTimeWitness
      (ν := 1) (T := T) (a := 1) (k := 1) (d := 1) (c := 1) (by simp) (by positivity) hT

theorem heat_shear_full_drift_BKM_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν
        (heatShearFullDriftInitialVelocity 1 1 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearFullDriftInitialVelocity 1 1 1 1) := by
  exact
    ExplicitBKMContinuationClause_heatShearFullDriftInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (k := 1) (d := 1) (c := 1) hν (by simp) hT

theorem heat_shear_full_drift_repaired_BKM_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyBKMContinuationClause
        ν (heatShearFullDriftInitialVelocity 1 1 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearFullDriftInitialVelocity 1 1 1 1) := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_heatShearFullDriftInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (k := 1) (d := 1) (c := 1) hν (by simp)

theorem heat_shear_transport_not_finite_initial_energy_regression :
    ¬ finiteInitialKineticEnergy (heatShearTransportInitialVelocity 1 1 1) := by
  exact
    not_finiteInitialKineticEnergy_heatShearTransportInitialVelocity
      (a := 1) (k := 1) (b := 1) (by simp)

theorem heat_shear_transport_direct_unbounded_energy_regression :
    ¬ boundedKineticEnergy (heatShearTransportVelocityField 1 1 1 1) := by
  exact
    not_boundedKineticEnergy_heatShearTransportVelocityField
      (ν := 1) (a := 1) (k := 1) (b := 1) (by simp)

theorem heat_shear_transport_direct_unbounded_energy_up_to_regression
    {T : ℝ} (hT : 0 ≤ T) :
    ¬ boundedKineticEnergyUpTo (heatShearTransportVelocityField 1 1 1 1) T := by
  exact
    not_boundedKineticEnergyUpTo_heatShearTransportVelocityField
      (ν := 1) (a := 1) (k := 1) (b := 1) (by simp) hT

theorem heat_shear_transport_concrete_candidate_without_global_output_regression :
    (∃ u : NSVelocityField, ∃ p : NSPressureField,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x,
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          spatialLaplacian u t x) ∧
      (∀ t x, spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearTransportInitialVelocity 1 1 1) u ∧
      ¬ boundedKineticEnergy u) ∧
      ¬ ExplicitConcreteNavierStokesGlobalOutput 1
        (heatShearTransportInitialVelocity 1 1 1) := by
  simpa using
    heatShearTransportInitialVelocity_exhibits_concreteCandidate_without_globalOutput
      (ν := 1) (a := 1) (k := 1) (b := 1) (by simp)

theorem heat_shear_transport_uniform_candidate_gap_regression
    {T : ℝ} (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearTransportInitialVelocity 1 1 1) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty (ExplicitFiniteTimeRegularityWitness 1
        (heatShearTransportInitialVelocity 1 1 1) T) := by
  simpa using
    heatShearTransportInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness
      (ν := 1) (T := T) (a := 1) (k := 1) (b := 1) (by simp) (by positivity) hT

theorem heat_shear_transport_uniform_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν
        (heatShearTransportInitialVelocity 1 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearTransportInitialVelocity 1 1 1) := by
  exact
    ExplicitUniformVorticityContinuationClause_heatShearTransportInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (k := 1) (b := 1) hν (by simp) hT

theorem heat_shear_transport_repaired_uniform_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
        ν (heatShearTransportInitialVelocity 1 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearTransportInitialVelocity 1 1 1) := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_heatShearTransportInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (k := 1) (b := 1) hν (by simp)

theorem heat_shear_transport_repaired_regularity_without_regularity_regression
    {ν : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
        ν (heatShearTransportInitialVelocity 1 1 1) ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearTransportInitialVelocity 1 1 1) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearTransportInitialVelocity_without_regularity
      (ν := ν) (a := 1) (k := 1) (b := 1) hν (by simp)

theorem heat_shear_transport_structured_clause_false_regression
    {ν : ℝ} (hν : 0 < ν) :
    ¬ NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := heatShearTransportInitialVelocity 1 1 1
          smooth_initial := smoothInitialVelocityData_heatShearTransportInitialVelocity 1 1 1
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_heatShearTransportInitialVelocity 1 1 1 x } := by
  exact
    not_concreteNavierStokesGlobalRegularityClause_heatShearTransportInitialVelocity
      (ν := ν) (a := 1) (k := 1) (b := 1) hν (by simp)

theorem heat_shear_transport_BKM_candidate_gap_regression
    {T : ℝ} (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearTransportInitialVelocity 1 1 1) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty (ExplicitFiniteTimeRegularityWitness 1
        (heatShearTransportInitialVelocity 1 1 1) T) := by
  simpa using
    heatShearTransportInitialVelocity_exhibits_BKMCandidate_without_finiteTimeWitness
      (ν := 1) (T := T) (a := 1) (k := 1) (b := 1) (by simp) (by positivity) hT

theorem heat_shear_transport_BKM_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν
        (heatShearTransportInitialVelocity 1 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearTransportInitialVelocity 1 1 1) := by
  exact
    ExplicitBKMContinuationClause_heatShearTransportInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (k := 1) (b := 1) hν (by simp) hT

theorem heat_shear_transport_repaired_BKM_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyBKMContinuationClause
        ν (heatShearTransportInitialVelocity 1 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearTransportInitialVelocity 1 1 1) := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_heatShearTransportInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (k := 1) (b := 1) hν (by simp)

theorem heat_shear_transport_full_drift_not_finite_initial_energy_regression :
    ¬ finiteInitialKineticEnergy (heatShearTransportFullDriftInitialVelocity 1 1 1 1 1) := by
  exact
    not_finiteInitialKineticEnergy_heatShearTransportFullDriftInitialVelocity
      (a := 1) (k := 1) (b := 1) (d := 1) (c := 1) (by simp)

theorem heat_shear_transport_full_drift_direct_unbounded_energy_regression :
    ¬ boundedKineticEnergy (heatShearTransportFullDriftVelocityField 1 1 1 1 1 1) := by
  exact
    not_boundedKineticEnergy_heatShearTransportFullDriftVelocityField
      (ν := 1) (a := 1) (k := 1) (b := 1) (d := 1) (c := 1) (by simp)

theorem heat_shear_transport_full_drift_direct_unbounded_energy_up_to_regression
    {T : ℝ} (hT : 0 ≤ T) :
    ¬ boundedKineticEnergyUpTo (heatShearTransportFullDriftVelocityField 1 1 1 1 1 1) T := by
  exact
    not_boundedKineticEnergyUpTo_heatShearTransportFullDriftVelocityField
      (ν := 1) (a := 1) (k := 1) (b := 1) (d := 1) (c := 1) (by simp) hT

theorem heat_shear_transport_full_drift_concrete_candidate_without_global_output_regression :
    (∃ u : NSVelocityField, ∃ p : NSPressureField,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x,
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          spatialLaplacian u t x) ∧
      (∀ t x, spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearTransportFullDriftInitialVelocity 1 1 1 1 1) u ∧
      ¬ boundedKineticEnergy u) ∧
      ¬ ExplicitConcreteNavierStokesGlobalOutput 1
        (heatShearTransportFullDriftInitialVelocity 1 1 1 1 1) := by
  simpa using
    heatShearTransportFullDriftInitialVelocity_exhibits_concreteCandidate_without_globalOutput
      (ν := 1) (a := 1) (k := 1) (b := 1) (d := 1) (c := 1) (by simp)

theorem heat_shear_transport_full_drift_uniform_candidate_gap_regression
    {T : ℝ} (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearTransportFullDriftInitialVelocity 1 1 1 1 1) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty (ExplicitFiniteTimeRegularityWitness 1
        (heatShearTransportFullDriftInitialVelocity 1 1 1 1 1) T) := by
  simpa using
    heatShearTransportFullDriftInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness
      (ν := 1) (T := T) (a := 1) (k := 1) (b := 1) (d := 1) (c := 1)
      (by simp) (by positivity) hT

theorem heat_shear_transport_full_drift_uniform_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν
        (heatShearTransportFullDriftInitialVelocity 1 1 1 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearTransportFullDriftInitialVelocity 1 1 1 1 1) := by
  exact
    ExplicitUniformVorticityContinuationClause_heatShearTransportFullDriftInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (k := 1) (b := 1) (d := 1) (c := 1) hν (by simp) hT

theorem heat_shear_transport_full_drift_repaired_uniform_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
        ν (heatShearTransportFullDriftInitialVelocity 1 1 1 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearTransportFullDriftInitialVelocity 1 1 1 1 1) := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_heatShearTransportFullDriftInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (k := 1) (b := 1) (d := 1) (c := 1) hν (by simp)

theorem heat_shear_transport_full_drift_repaired_regularity_without_regularity_regression
    {ν : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
        ν (heatShearTransportFullDriftInitialVelocity 1 1 1 1 1) ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearTransportFullDriftInitialVelocity 1 1 1 1 1) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearTransportFullDriftInitialVelocity_without_regularity
      (ν := ν) (a := 1) (k := 1) (b := 1) (d := 1) (c := 1) hν (by simp)

theorem heat_shear_transport_full_drift_structured_clause_false_regression
    {ν : ℝ} (hν : 0 < ν) :
    ¬ NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := heatShearTransportFullDriftInitialVelocity 1 1 1 1 1
          smooth_initial := smoothInitialVelocityData_heatShearTransportFullDriftInitialVelocity 1 1 1 1 1
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_heatShearTransportFullDriftInitialVelocity 1 1 1 1 1 x } := by
  exact
    not_concreteNavierStokesGlobalRegularityClause_heatShearTransportFullDriftInitialVelocity
      (ν := ν) (a := 1) (k := 1) (b := 1) (d := 1) (c := 1) hν (by simp)

theorem heat_shear_transport_full_drift_BKM_candidate_gap_regression
    {T : ℝ} (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearTransportFullDriftInitialVelocity 1 1 1 1 1) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty (ExplicitFiniteTimeRegularityWitness 1
        (heatShearTransportFullDriftInitialVelocity 1 1 1 1 1) T) := by
  simpa using
    heatShearTransportFullDriftInitialVelocity_exhibits_BKMCandidate_without_finiteTimeWitness
      (ν := 1) (T := T) (a := 1) (k := 1) (b := 1) (d := 1) (c := 1)
      (by simp) (by positivity) hT

theorem heat_shear_transport_full_drift_BKM_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν
        (heatShearTransportFullDriftInitialVelocity 1 1 1 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearTransportFullDriftInitialVelocity 1 1 1 1 1) := by
  exact
    ExplicitBKMContinuationClause_heatShearTransportFullDriftInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (k := 1) (b := 1) (d := 1) (c := 1) hν (by simp) hT

theorem heat_shear_transport_full_drift_repaired_BKM_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyBKMContinuationClause
        ν (heatShearTransportFullDriftInitialVelocity 1 1 1 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearTransportFullDriftInitialVelocity 1 1 1 1 1) := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_heatShearTransportFullDriftInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (k := 1) (b := 1) (d := 1) (c := 1) hν (by simp)

end ContinuationRegression
end NavierStokes
end FluidDynamics
end Mettapedia
