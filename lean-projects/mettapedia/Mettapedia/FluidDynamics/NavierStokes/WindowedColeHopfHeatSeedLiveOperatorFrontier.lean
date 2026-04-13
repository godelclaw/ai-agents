import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatPackage
import Mettapedia.FluidDynamics.NavierStokes.FeffermanSeedLiveOperatorFrontier
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSeedLiveProfileFrontier
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSampleKernelFrontier
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatShiftKernelFrontier

/-!
# Seed/Live Operator Frontier on the Windowed Cole-Hopf Heat Route

This file instantiates the generic non-pointwise seed/live operator shell on the
concrete windowed heat route.

It also records that the pointwise seed/live-profile shell, the finite
sampled-kernel shell, and the finite shift-kernel shell are all exact
specializations of this one concrete operator frontier.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section WindowedColeHopfHeatSeedLiveOperatorFrontier

variable {ι X κ : Type*}
variable [Fintype ι] [Fintype κ]
variable {κs : Type*}
variable [Fintype κs] [AddMonoid X]

abbrev WeightedObservable.windowedColeHopfHeatSeedLiveOperatorInitialSlice
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
    (x : ModeState) : X → ℝ :=
  (L.windowedColeHopfHeatUniformVorticityTendril
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).seedLiveOperatorInitialSlice O

abbrev WeightedObservable.windowedColeHopfHeatSeedLiveOperatorCandidate
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
    VelocityPressureCandidate (Time := NNReal) (X := X) :=
  (L.windowedColeHopfHeatUniformVorticityTendril
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).seedLiveOperatorCandidate O

omit [AddMonoid X] in
theorem WeightedObservable.windowedColeHopfHeatSeedLiveOperatorCandidate_has_seedLiveOperatorCompatibility
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
    seedLiveOperatorCompatibilityPred (Time := NNReal) (X := X) O
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
      (L.windowedColeHopfHeatSeedLiveOperatorCandidate
        (ι := ι) (X := X)
        selector O c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity :=
  (L.windowedColeHopfHeatUniformVorticityTendril
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).seedLiveOperatorCandidate_has_seedLiveOperatorCompatibility O

omit [AddMonoid X] in
theorem WeightedObservable.windowedColeHopfHeatSeedLiveOperatorCandidate_has_selfCompatibility_of_operator_eq_live
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
    selfCompatibility (Time := NNReal) (X := X)
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
      (L.windowedColeHopfHeatSeedLiveOperatorCandidate
        (ι := ι) (X := X)
        selector O c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity :=
  (L.windowedColeHopfHeatUniformVorticityTendril
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).seedLiveOperatorCandidate_has_selfCompatibility_of_operator_eq_live O hO

omit [AddMonoid X] in
theorem WeightedObservable.windowedColeHopfHeatSeedLiveOperatorCandidate_has_selfCompatibility_of_zero_vorticity
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
    selfCompatibility (Time := NNReal) (X := X)
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
      (L.windowedColeHopfHeatSeedLiveOperatorCandidate
        (ι := ι) (X := X)
        selector O c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity :=
  (L.windowedColeHopfHeatUniformVorticityTendril
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).seedLiveOperatorCandidate_has_selfCompatibility_of_zero_vorticity
      O hO0 hzero

def WeightedObservable.toWindowedColeHopfHeatSeedLiveOperatorAlmostBridge
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
    AlmostFeffermanBridge
      (K := pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatSeedLiveOperatorInitialSlice
          (ι := ι) (X := X)
          selector O c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x) :=
  (L.windowedColeHopfHeatUniformVorticityTendril
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).toSeedLiveOperatorAlmostBridge O

def WeightedObservable.toWindowedColeHopfHeatSeedLiveOperatorBridge
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
    TopDownFeffermanBridge
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatSeedLiveOperatorInitialSlice
          (ι := ι) (X := X)
          selector O c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
      (seedLiveOperatorCompatibilityPred (Time := NNReal) (X := X) O)
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x) :=
  (L.windowedColeHopfHeatUniformVorticityTendril
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).toSeedLiveOperatorBridge O

omit [AddMonoid X] in
theorem WeightedObservable.windowedColeHopfHeat_realizes_seedLiveOperator_pressure_seeded_clause
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
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatSeedLiveOperatorInitialSlice
          (ι := ι) (X := X)
          selector O c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) :=
  (L.toWindowedColeHopfHeatSeedLiveOperatorBridge
    (ι := ι) (X := X)
    selector O c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).realizes_clause

omit [AddMonoid X] in
theorem WeightedObservable.windowedColeHopfHeat_realizes_seedLiveOperator_pressure_seeded_clause_of_selfCompatibility
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
    (hcompat :
      selfCompatibility (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
        (L.windowedColeHopfHeatSeedLiveOperatorCandidate
          (ι := ι) (X := X)
          selector O c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatSeedLiveOperatorInitialSlice
          (ι := ι) (X := X)
          selector O c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) :=
  (L.windowedColeHopfHeatUniformVorticityTendril
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).realizes_seedLiveOperator_pressure_seeded_clause_of_selfCompatibility
      O hcompat

omit [AddMonoid X] in
theorem WeightedObservable.windowedColeHopfHeat_realizes_seedLiveOperator_pressure_seeded_clause_of_operator_eq_live
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
          selector O c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) :=
  L.windowedColeHopfHeat_realizes_seedLiveOperator_pressure_seeded_clause_of_selfCompatibility
    (ι := ι) (X := X)
    selector O c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
    (L.windowedColeHopfHeatSeedLiveOperatorCandidate_has_selfCompatibility_of_operator_eq_live
      (ι := ι) (X := X)
      selector O c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hO)

omit [AddMonoid X] in
theorem WeightedObservable.windowedColeHopfHeatSeedLiveOperatorCandidate_has_selfCompatibility_of_operator_eq_seed_of_stationary
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
    selfCompatibility (Time := NNReal) (X := X)
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
      (L.windowedColeHopfHeatSeedLiveOperatorCandidate
        (ι := ι) (X := X)
        selector O c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity :=
  (L.windowedColeHopfHeatUniformVorticityTendril
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).seedLiveOperatorCandidate_has_selfCompatibility_of_operator_eq_seed_of_stationary
      O hO hstat

omit [AddMonoid X] in
theorem WeightedObservable.windowedColeHopfHeat_realizes_seedLiveOperator_pressure_seeded_clause_of_operator_eq_seed_of_stationary
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
          selector O c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) :=
  L.windowedColeHopfHeat_realizes_seedLiveOperator_pressure_seeded_clause_of_selfCompatibility
    (ι := ι) (X := X)
    selector O c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
    (L.windowedColeHopfHeatSeedLiveOperatorCandidate_has_selfCompatibility_of_operator_eq_seed_of_stationary
      (ι := ι) (X := X)
      selector O c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hO hstat)

omit [AddMonoid X] in
theorem WeightedObservable.windowedColeHopfHeat_realizes_seedLiveOperator_pressure_seeded_clause_of_zero_vorticity
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
          selector O c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) :=
  L.windowedColeHopfHeat_realizes_seedLiveOperator_pressure_seeded_clause_of_selfCompatibility
    (ι := ι) (X := X)
    selector O c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
    (L.windowedColeHopfHeatSeedLiveOperatorCandidate_has_selfCompatibility_of_zero_vorticity
      (ι := ι) (X := X)
      selector O c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hO0 hzero)

omit [AddMonoid X] in
theorem WeightedObservable.toWindowedColeHopfHeatSeedLiveOperatorBridge_retains_uniform_vorticity
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
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).envelope :=
  (L.toWindowedColeHopfHeatSeedLiveOperatorBridge
    (ι := ι) (X := X)
    selector O c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).retains_uniform_vorticity

omit [AddMonoid X] in
theorem WeightedObservable.windowedColeHopfHeatSeedLiveOperatorInitialSlice_profile_eq_seedLiveInitialSlice
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
    L.windowedColeHopfHeatSeedLiveOperatorInitialSlice
        (ι := ι) (X := X)
        selector P.toSeedLiveOperator c ν hc hν
        curlFrame curlBound curlBound_nonneg hcurl x =
      L.windowedColeHopfHeatSeedLiveInitialSlice
        (ι := ι) (X := X)
        selector P c ν hc hν
        curlFrame curlBound curlBound_nonneg hcurl x := by
  rfl

omit [AddMonoid X] in
theorem WeightedObservable.windowedColeHopfHeatSeedLiveOperatorCandidate_profile_eq_seedLiveCandidate
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
    L.windowedColeHopfHeatSeedLiveOperatorCandidate
        (ι := ι) (X := X)
        selector P.toSeedLiveOperator c ν hc hν
        curlFrame curlBound curlBound_nonneg hcurl x =
      L.windowedColeHopfHeatSeedLiveCandidate
        (ι := ι) (X := X)
        selector P c ν hc hν
        curlFrame curlBound curlBound_nonneg hcurl x := by
  rfl

omit [AddMonoid X] in
theorem WeightedObservable.windowedColeHopfHeatSeedLiveOperatorInitialSlice_sampleKernel_eq_sampleKernelInitialSlice
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
    L.windowedColeHopfHeatSeedLiveOperatorInitialSlice
        (ι := ι) (X := X)
        selector K.toSeedLiveOperator c ν hc hν
        curlFrame curlBound curlBound_nonneg hcurl x =
      L.windowedColeHopfHeatSampleKernelInitialSlice
        (ι := ι) (X := X)
        selector K c ν hc hν
        curlFrame curlBound curlBound_nonneg hcurl x := by
  rfl

omit [AddMonoid X] in
theorem WeightedObservable.windowedColeHopfHeatSeedLiveOperatorCandidate_sampleKernel_eq_sampleKernelCandidate
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
    L.windowedColeHopfHeatSeedLiveOperatorCandidate
        (ι := ι) (X := X)
        selector K.toSeedLiveOperator c ν hc hν
        curlFrame curlBound curlBound_nonneg hcurl x =
      L.windowedColeHopfHeatSampleKernelCandidate
        (ι := ι) (X := X)
        selector K c ν hc hν
        curlFrame curlBound curlBound_nonneg hcurl x := by
  rfl

theorem WeightedObservable.windowedColeHopfHeatSeedLiveOperatorInitialSlice_shiftKernel_eq_shiftKernelInitialSlice
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κs X)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState) :
    L.windowedColeHopfHeatSeedLiveOperatorInitialSlice
        (ι := ι) (X := X)
        selector K.toSampleKernel.toSeedLiveOperator c ν hc hν
        curlFrame curlBound curlBound_nonneg hcurl x =
      L.windowedColeHopfHeatShiftKernelInitialSlice
        (ι := ι) (κ := κs) (X := X)
        selector K c ν hc hν
        curlFrame curlBound curlBound_nonneg hcurl x := by
  rfl

theorem WeightedObservable.windowedColeHopfHeatSeedLiveOperatorCandidate_shiftKernel_eq_shiftKernelCandidate
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κs X)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState) :
    L.windowedColeHopfHeatSeedLiveOperatorCandidate
        (ι := ι) (X := X)
        selector K.toSampleKernel.toSeedLiveOperator c ν hc hν
        curlFrame curlBound curlBound_nonneg hcurl x =
      L.windowedColeHopfHeatShiftKernelCandidate
        (ι := ι) (κ := κs) (X := X)
        selector K c ν hc hν
        curlFrame curlBound curlBound_nonneg hcurl x := by
  rfl

end WindowedColeHopfHeatSeedLiveOperatorFrontier

end NavierStokes
end FluidDynamics
end Mettapedia
