import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSeededModel

/-!
# Scaled Seeded Frontier for the Windowed Cole-Hopf Heat Route

This file is the first genuinely non-self compatibility upgrade on the concrete
windowed heat NS route.  The candidate velocity is a scalar multiple of the
current windowed heat vorticity field, while pressure remains zero.

The result is still local and still does not claim the real NS PDE.  But it
does make the compatibility mouth nontrivial on the actual current route.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section WindowedColeHopfHeatScaledSeededFrontier

variable {ι X : Type*}
variable [Fintype ι]

/-- Initial slice of the scalar-rescaled windowed candidate at time `1`. -/
def WeightedObservable.windowedColeHopfHeatScaledInitialSlice
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (a c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState) : X → ℝ :=
  fun y =>
    a *
      (L.windowedColeHopfHeatCandidate
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity 1 y

/-- First non-self candidate on the concrete windowed heat route: scale the
velocity by a constant and keep pressure zero. -/
def WeightedObservable.windowedColeHopfHeatScaledCandidate
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
    VelocityPressureCandidate (Time := NNReal) (X := X) where
  velocity := fun t y =>
    a *
      (L.windowedColeHopfHeatCandidate
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity t y
  pressure := fun _ _ => 0

/-- Compatibility notion for the scalar-rescaled descendant route. -/
def windowedScaledCompatibilityPred (a : ℝ) :
    VorticityCompatibilityPred (Time := NNReal) (X := X) :=
  fun T u => ∀ t x, u t x = a * T.vorticity t x

/-- Stronger seeded target on the concrete route:
velocity is uniformly bounded, pressure vanishes in both pressure slots, the
initial slice is prescribed, and the same bound is used on the energy side. -/
def WeightedObservable.windowedColeHopfHeatScaledSeededPredicateKit
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
    FeffermanPredicateKit (Time := NNReal) (X := X) where
  SmoothVelocity := SeededUniformPointwiseBound
  SmoothPressure := SeededZeroPressure
  MomentumEquation := fun _ p => SeededZeroPressure p
  Incompressible := fun _ => True
  InitialCondition :=
    SeededMatchesInitialSlice
      (L.windowedColeHopfHeatScaledInitialSlice
        (ι := ι) (X := X)
        selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
  BoundedEnergy := SeededUniformPointwiseBound

theorem WeightedObservable.windowedColeHopfHeatScaledCandidate_zeroPressure
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
    SeededZeroPressure
      (X := X)
      (L.windowedColeHopfHeatScaledCandidate
        (ι := ι) (X := X)
        selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).pressure := by
  intro t y
  rfl

theorem WeightedObservable.windowedColeHopfHeatScaledCandidate_matchesInitialSlice
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
    SeededMatchesInitialSlice
      (X := X)
      (L.windowedColeHopfHeatScaledInitialSlice
        (ι := ι) (X := X)
        selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
      (L.windowedColeHopfHeatScaledCandidate
        (ι := ι) (X := X)
        selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity := by
  intro y
  rfl

theorem WeightedObservable.windowedColeHopfHeatScaledCandidate_bounded
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
    SeededUniformPointwiseBound
      (X := X)
      (L.windowedColeHopfHeatScaledCandidate
        (ι := ι) (X := X)
        selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity := by
  refine ⟨|a| *
    (L.windowedColeHopfHeatUniformVorticityTendril
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).envelope, ?_, ?_⟩
  · exact mul_nonneg (abs_nonneg a)
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).envelope_nonneg
  · intro t y
    calc
      |(L.windowedColeHopfHeatScaledCandidate
          (ι := ι) (X := X)
          selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity t y|
          = |a * (L.windowedColeHopfHeatCandidate
              (ι := ι) (X := X)
              selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity t y| := rfl
      _ = |a| * |(L.windowedColeHopfHeatCandidate
              (ι := ι) (X := X)
              selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity t y| := by
            rw [abs_mul]
      _ ≤ |a| *
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).envelope := by
            exact mul_le_mul_of_nonneg_left
              (L.windowedColeHopfHeatCandidate_abs_velocity_le_envelope
                (ι := ι) (X := X)
                selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x t y)
              (abs_nonneg a)

theorem WeightedObservable.windowedColeHopfHeatScaledCandidate_has_scaledCompatibility
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
  intro t y
  rfl

/-- Strong concrete non-self almost-bridge on the windowed heat route. -/
def WeightedObservable.toWindowedColeHopfHeatScaledSeededAlmostBridge
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
    AlmostFeffermanBridge
      (K :=
        L.windowedColeHopfHeatScaledSeededPredicateKit
          (ι := ι) (X := X)
          selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x) where
  candidate :=
    L.windowedColeHopfHeatScaledCandidate
      (ι := ι) (X := X)
      selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
  regularity :=
    { smooth_velocity := L.windowedColeHopfHeatScaledCandidate_bounded
        (ι := ι) (X := X)
        selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
      smooth_pressure := L.windowedColeHopfHeatScaledCandidate_zeroPressure
        (ι := ι) (X := X)
        selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x }
  dynamics :=
    { momentum_equation := L.windowedColeHopfHeatScaledCandidate_zeroPressure
        (ι := ι) (X := X)
        selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
      incompressible := trivial
      initial_condition := L.windowedColeHopfHeatScaledCandidate_matchesInitialSlice
        (ι := ι) (X := X)
        selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x }
  energy :=
    { bounded_energy := L.windowedColeHopfHeatScaledCandidate_bounded
        (ι := ι) (X := X)
        selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x }

theorem WeightedObservable.windowedColeHopfHeat_realizes_scaled_seeded_clause
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
        selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x) :=
  (L.toWindowedColeHopfHeatScaledSeededAlmostBridge
    (ι := ι) (X := X)
    selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).realizes_clause_of_compatibility
      (L.windowedColeHopfHeatScaledCandidate_has_scaledCompatibility
        (ι := ι) (X := X)
        selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)

/-- The scaled seeded frontier also upgrades to a full top-down bridge on the
windowed heat route. -/
def WeightedObservable.toWindowedColeHopfHeatScaledSeededBridge
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
    TopDownFeffermanBridge
      (L.windowedColeHopfHeatScaledSeededPredicateKit
        (ι := ι) (X := X)
        selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
      (windowedScaledCompatibilityPred (X := X) a)
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x) :=
  (L.toWindowedColeHopfHeatScaledSeededAlmostBridge
    (ι := ι) (X := X)
    selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).toTopDownBridge
      (L.windowedColeHopfHeatScaledCandidate_has_scaledCompatibility
        (ι := ι) (X := X)
        selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)

theorem WeightedObservable.toWindowedColeHopfHeatScaledSeededBridge_retains_uniform_vorticity
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
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).envelope :=
  (L.toWindowedColeHopfHeatScaledSeededBridge
    (ι := ι) (X := X)
    selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).retains_uniform_vorticity

end WindowedColeHopfHeatScaledSeededFrontier

end NavierStokes
end FluidDynamics
end Mettapedia
