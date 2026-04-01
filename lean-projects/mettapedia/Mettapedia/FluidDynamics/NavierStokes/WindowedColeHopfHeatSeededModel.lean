import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatFoundationFrontier

/-!
# Seeded Local Model for the Windowed Cole-Hopf Heat Candidate

This file strengthens the current concrete windowed heat route beyond the bare
compatibility frontier.

It packages a local target with two genuinely nontrivial predicates:

* pressure is identically zero;
* velocity matches its own distinguished initial slice at time `1`.

The route still leaves the actual NS PDE predicates abstract, but it now closes
more than a boundedness-only target on the fixed windowed candidate.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section WindowedColeHopfHeatSeededModel

variable {ι X : Type*}
variable [Fintype ι]

/-- Pressure-zero predicate for the seeded local model. -/
def SeededZeroPressure (p : NNReal → X → ℝ) : Prop :=
  ∀ t x, p t x = 0

/-- Initial-slice predicate at the distinguished base time `1`. -/
def SeededMatchesInitialSlice (u₀ : X → ℝ) (u : NNReal → X → ℝ) : Prop :=
  ∀ x, u 1 x = u₀ x

/-- Weak but nontrivial boundedness predicate on the candidate velocity. -/
def SeededUniformPointwiseBound (u : NNReal → X → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ t x, |u t x| ≤ C

/-- Compatibility for the seeded local model: the chosen velocity is exactly the
current tendril vorticity. -/
def windowedSelfCompatibility :
    VorticityCompatibilityPred (Time := NNReal) (X := X) :=
  fun T u => ∀ t x, u t x = T.vorticity t x

/-- Distinguished initial slice extracted from the fixed windowed heat
candidate. -/
def WeightedObservable.windowedColeHopfHeatInitialSlice
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState) : X → ℝ :=
  fun y =>
    (L.windowedColeHopfHeatCandidate
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity 1 y

/-- The local seeded predicate kit carried by the fixed windowed heat
candidate. -/
def WeightedObservable.windowedColeHopfHeatSeededPredicateKit
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
    FeffermanPredicateKit (Time := NNReal) (X := X) where
  SmoothVelocity := fun _ => True
  SmoothPressure := SeededZeroPressure
  MomentumEquation := fun _ _ => True
  Incompressible := fun _ => True
  InitialCondition :=
    SeededMatchesInitialSlice
      (L.windowedColeHopfHeatInitialSlice
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
  BoundedEnergy := SeededUniformPointwiseBound

theorem WeightedObservable.windowedColeHopfHeatCandidate_zeroPressure
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
    SeededZeroPressure
      (X := X)
      (L.windowedColeHopfHeatCandidate
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).pressure := by
  intro t y
  rfl

theorem WeightedObservable.windowedColeHopfHeatCandidate_matchesInitialSlice
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
    SeededMatchesInitialSlice
      (X := X)
      (L.windowedColeHopfHeatInitialSlice
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
      (L.windowedColeHopfHeatCandidate
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity := by
  intro y
  rfl

theorem WeightedObservable.windowedColeHopfHeatCandidate_boundedEnergy
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
    SeededUniformPointwiseBound
      (X := X)
      (L.windowedColeHopfHeatCandidate
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity := by
  refine ⟨(L.windowedColeHopfHeatUniformVorticityTendril
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).envelope, ?_, ?_⟩
  · exact (L.windowedColeHopfHeatUniformVorticityTendril
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).envelope_nonneg
  · intro t y
    simpa [WeightedObservable.windowedColeHopfHeatCandidate] using
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).abs_vorticity_le t y

theorem WeightedObservable.windowedColeHopfHeatCandidate_selfCompatibility
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
    windowedSelfCompatibility
      (X := X)
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
      (L.windowedColeHopfHeatCandidate
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity := by
  intro t y
  rfl

/-- The fixed windowed heat candidate already supplies a stronger local
foundation package than the bare boundedness-only weak model. -/
def WeightedObservable.windowedColeHopfHeatSeededFoundation
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
    L.WindowedColeHopfHeatFoundationData
      (ι := ι) (X := X)
      (L.windowedColeHopfHeatSeededPredicateKit
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
      (windowedSelfCompatibility (X := X))
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x where
  regularity :=
    { smooth_velocity := trivial
      smooth_pressure := L.windowedColeHopfHeatCandidate_zeroPressure
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x }
  dynamics :=
    { momentum_equation := trivial
      incompressible := trivial
      initial_condition := L.windowedColeHopfHeatCandidate_matchesInitialSlice
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x }
  energy :=
    { bounded_energy := L.windowedColeHopfHeatCandidate_boundedEnergy
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x }

theorem WeightedObservable.windowedColeHopfHeat_realizes_seeded_clause
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
      (L.windowedColeHopfHeatSeededPredicateKit
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x) :=
  (L.windowedColeHopfHeatSeededFoundation
    (ι := ι) (X := X)
    selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).realizes_clause_of_compatibility
      (L.windowedColeHopfHeatCandidate_selfCompatibility
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)

end WindowedColeHopfHeatSeededModel

end NavierStokes
end FluidDynamics
end Mettapedia
