import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatPackage
import Mettapedia.FluidDynamics.NavierStokes.FeffermanSeedLiveProfileFrontier
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatScaledSeededFrontier
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSeedBlendFrontier
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSaturatedFrontier
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatFrozenGateFrontier

/-!
# Seed/Live Profile Frontier on the Windowed Cole-Hopf Heat Route

This file instantiates the generic pointwise seed/live profile shell on the
concrete windowed heat route.

It exposes one concrete descendant family

`u(t,x) = P(ω(1,x), ω(t,x))`

on the current windowed vorticity tendril, and records that the previously
studied scaled, affine seed-blend, saturated, and frozen-gate descendants are
all exact special cases of this same pointwise shell.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section WindowedColeHopfHeatSeedLiveProfileFrontier

variable {ι X : Type*}
variable [Fintype ι]

abbrev WeightedObservable.windowedColeHopfHeatSeedLiveInitialSlice
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
    (x : ModeState) : X → ℝ :=
  (L.windowedColeHopfHeatUniformVorticityTendril
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).seedLiveInitialSlice P

abbrev WeightedObservable.windowedColeHopfHeatSeedLiveCandidate
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
    VelocityPressureCandidate (Time := NNReal) (X := X) :=
  (L.windowedColeHopfHeatUniformVorticityTendril
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).seedLiveCandidate P

theorem WeightedObservable.windowedColeHopfHeatSeedLiveCandidate_has_seedLiveCompatibility
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
    seedLiveCompatibilityPred (Time := NNReal) (X := X) P
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
      (L.windowedColeHopfHeatSeedLiveCandidate
        (ι := ι) (X := X)
        selector P c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity :=
  (L.windowedColeHopfHeatUniformVorticityTendril
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).seedLiveCandidate_has_seedLiveCompatibility P

theorem WeightedObservable.windowedColeHopfHeatSeedLiveCandidate_has_selfCompatibility_of_profile_eq_live
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
    selfCompatibility (Time := NNReal) (X := X)
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
      (L.windowedColeHopfHeatSeedLiveCandidate
        (ι := ι) (X := X)
        selector P c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity := by
  intro t y
  simpa [selfCompatibility, WeightedObservable.windowedColeHopfHeatSeedLiveCandidate] using
    hP
      ((L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y)
      ((L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)

theorem WeightedObservable.windowedColeHopfHeatSeedLiveCandidate_has_selfCompatibility_of_profile_eq_seed_of_stationary
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
    selfCompatibility (Time := NNReal) (X := X)
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
      (L.windowedColeHopfHeatSeedLiveCandidate
        (ι := ι) (X := X)
        selector P c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity :=
  (L.windowedColeHopfHeatUniformVorticityTendril
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).seedLiveCandidate_has_selfCompatibility_of_profile_eq_seed_of_stationary
      P hP hstat

theorem WeightedObservable.windowedColeHopfHeatSeedLiveCandidate_has_selfCompatibility_of_zero_vorticity
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
    selfCompatibility (Time := NNReal) (X := X)
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
      (L.windowedColeHopfHeatSeedLiveCandidate
        (ι := ι) (X := X)
        selector P c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity := by
  intro t y
  calc
    (L.windowedColeHopfHeatSeedLiveCandidate
        (ι := ι) (X := X)
        selector P c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity t y
        =
          P.profile
            ((L.windowedColeHopfHeatUniformVorticityTendril
              (ι := ι) (X := X)
              selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity 1 y)
            ((L.windowedColeHopfHeatUniformVorticityTendril
              (ι := ι) (X := X)
              selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y) := rfl
    _ = P.profile 0 0 := by rw [hzero 1 y, hzero t y]
    _ = 0 := hP0
    _ =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y := by
            symm
            exact hzero t y

def WeightedObservable.toWindowedColeHopfHeatSeedLiveAlmostBridge
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
    AlmostFeffermanBridge
      (K := pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatSeedLiveInitialSlice
          (ι := ι) (X := X)
          selector P c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x) :=
  (L.windowedColeHopfHeatUniformVorticityTendril
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).toSeedLiveAlmostBridge P

def WeightedObservable.toWindowedColeHopfHeatSeedLiveBridge
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
    TopDownFeffermanBridge
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatSeedLiveInitialSlice
          (ι := ι) (X := X)
          selector P c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
      (seedLiveCompatibilityPred (Time := NNReal) (X := X) P)
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x) :=
  (L.windowedColeHopfHeatUniformVorticityTendril
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).toSeedLiveBridge P

theorem WeightedObservable.windowedColeHopfHeat_realizes_seedLive_pressure_seeded_clause
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
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatSeedLiveInitialSlice
          (ι := ι) (X := X)
          selector P c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) :=
  (L.toWindowedColeHopfHeatSeedLiveBridge
    (ι := ι) (X := X)
    selector P c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).realizes_clause

theorem WeightedObservable.windowedColeHopfHeat_realizes_seedLive_pressure_seeded_clause_of_selfCompatibility
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
    (hcompat :
      selfCompatibility (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
        (L.windowedColeHopfHeatSeedLiveCandidate
          (ι := ι) (X := X)
          selector P c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatSeedLiveInitialSlice
          (ι := ι) (X := X)
          selector P c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) :=
  (L.windowedColeHopfHeatUniformVorticityTendril
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).realizes_pressure_seeded_clause_of_seedLiveSelfCompatibility
      P hcompat

theorem WeightedObservable.windowedColeHopfHeat_realizes_seedLive_pressure_seeded_clause_of_profile_eq_live
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
          selector P c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) :=
  L.windowedColeHopfHeat_realizes_seedLive_pressure_seeded_clause_of_selfCompatibility
    (ι := ι) (X := X)
    selector P c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
    (L.windowedColeHopfHeatSeedLiveCandidate_has_selfCompatibility_of_profile_eq_live
      (ι := ι) (X := X)
      selector P c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hP)

theorem WeightedObservable.windowedColeHopfHeat_realizes_seedLive_pressure_seeded_clause_of_profile_eq_seed_of_stationary
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
          selector P c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) :=
  L.windowedColeHopfHeat_realizes_seedLive_pressure_seeded_clause_of_selfCompatibility
    (ι := ι) (X := X)
    selector P c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
    (L.windowedColeHopfHeatSeedLiveCandidate_has_selfCompatibility_of_profile_eq_seed_of_stationary
      (ι := ι) (X := X)
      selector P c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hP hstat)

theorem WeightedObservable.windowedColeHopfHeat_realizes_seedLive_pressure_seeded_clause_of_zero_vorticity
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
          selector P c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) :=
  L.windowedColeHopfHeat_realizes_seedLive_pressure_seeded_clause_of_selfCompatibility
    (ι := ι) (X := X)
    selector P c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
    (L.windowedColeHopfHeatSeedLiveCandidate_has_selfCompatibility_of_zero_vorticity
      (ι := ι) (X := X)
      selector P c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hP0 hzero)

theorem WeightedObservable.toWindowedColeHopfHeatSeedLiveBridge_retains_uniform_vorticity
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
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).envelope :=
  (L.toWindowedColeHopfHeatSeedLiveBridge
    (ι := ι) (X := X)
    selector P c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).retains_uniform_vorticity

theorem WeightedObservable.windowedColeHopfHeatSeedLiveCandidate_linear_eq_scaledCandidate
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
    L.windowedColeHopfHeatSeedLiveCandidate
        (ι := ι) (X := X)
        selector (linearSeedLiveProfile a) c ν hc hν
        curlFrame curlBound curlBound_nonneg hcurl x =
      L.windowedColeHopfHeatScaledCandidate
        (ι := ι) (X := X)
        selector a c ν hc hν
        curlFrame curlBound curlBound_nonneg hcurl x := by
  rfl

theorem WeightedObservable.windowedColeHopfHeatSeedLiveCandidate_seedBlend_eq_seedBlendCandidate
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
    L.windowedColeHopfHeatSeedLiveCandidate
        (ι := ι) (X := X)
        selector (seedBlendProfile a b) c ν hc hν
        curlFrame curlBound curlBound_nonneg hcurl x =
      L.windowedColeHopfHeatSeedBlendCandidate
        (ι := ι) (X := X)
        selector a b c ν hc hν
        curlFrame curlBound curlBound_nonneg hcurl x := by
  rfl

theorem WeightedObservable.windowedColeHopfHeatSeedLiveCandidate_saturated_eq_saturatedCandidate
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
    L.windowedColeHopfHeatSeedLiveCandidate
        (ι := ι) (X := X)
        selector (saturatedSeedLiveProfile a) c ν hc hν
        curlFrame curlBound curlBound_nonneg hcurl x =
      L.windowedColeHopfHeatSaturatedCandidate
        (ι := ι) (X := X)
        selector a c ν hc hν
        curlFrame curlBound curlBound_nonneg hcurl x := by
  rfl

theorem WeightedObservable.windowedColeHopfHeatSeedLiveCandidate_frozenGate_eq_frozenGateCandidate
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
    L.windowedColeHopfHeatSeedLiveCandidate
        (ι := ι) (X := X)
        selector (frozenGateSeedLiveProfile a) c ν hc hν
        curlFrame curlBound curlBound_nonneg hcurl x =
      L.windowedColeHopfHeatFrozenGateCandidate
        (ι := ι) (X := X)
        selector a c ν hc hν
        curlFrame curlBound curlBound_nonneg hcurl x := by
  rfl

end WindowedColeHopfHeatSeedLiveProfileFrontier

end NavierStokes
end FluidDynamics
end Mettapedia
