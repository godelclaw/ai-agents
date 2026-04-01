import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatPackage
import Mettapedia.FluidDynamics.NavierStokes.FeffermanCompatibilityFrontier

/-!
# Foundation Frontier for the Windowed Cole-Hopf Heat Route

This file fixes the actual candidate fields carried by the current concrete
windowed heat package and packages the strongest local foundations currently
available before the remaining compatibility theorem.

Concretely:

* velocity is fixed to the package's vorticity field;
* pressure is fixed to zero;
* pointwise envelope control for that velocity is proved;
* regularity, dynamics, and target-side energy certificates are packaged on
  that fixed candidate, yielding an `AlmostFeffermanBridge`.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section WindowedColeHopfHeatFoundationFrontier

variable {ι X : Type*}
variable [Fintype ι]

/-- The concrete candidate fields currently supplied by the windowed heat
package: velocity is the package vorticity, pressure is zero. -/
def WeightedObservable.windowedColeHopfHeatCandidate
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
    VelocityPressureCandidate (Time := NNReal) (X := X) where
  velocity :=
    (L.windowedColeHopfHeatUniformVorticityTendril
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity
  pressure := fun _ _ => 0

theorem WeightedObservable.windowedColeHopfHeatCandidate_velocity
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
    (L.windowedColeHopfHeatCandidate
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity =
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity :=
  rfl

theorem WeightedObservable.windowedColeHopfHeatCandidate_pressure
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
    (L.windowedColeHopfHeatCandidate
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).pressure =
      fun _ _ => (0 : ℝ) :=
  rfl

theorem WeightedObservable.windowedColeHopfHeatCandidate_abs_velocity_le_envelope
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
    ∀ t y,
      |(L.windowedColeHopfHeatCandidate
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity t y| ≤
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).envelope := by
  simpa [WeightedObservable.windowedColeHopfHeatCandidate] using
    L.windowedColeHopfHeat_abs_vorticity_le_uniform
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x

/-- Foundations through the regularity/dynamics/energy layers for the fixed
windowed heat candidate. Compatibility is intentionally left for later. -/
structure WeightedObservable.WindowedColeHopfHeatFoundationData
    (K : FeffermanPredicateKit (Time := NNReal) (X := X))
    (Compat : VorticityCompatibilityPred (Time := NNReal) (X := X))
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState) where
  regularity :
    RegularityCertificate K
      (L.windowedColeHopfHeatCandidate
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
  dynamics :
    DynamicsCertificate K
      (L.windowedColeHopfHeatCandidate
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
  energy :
    EnergyCertificate K
      (L.windowedColeHopfHeatCandidate
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)

def WeightedObservable.WindowedColeHopfHeatFoundationData.toAlmostBridge
    {K : FeffermanPredicateKit (Time := NNReal) (X := X)}
    {Compat : VorticityCompatibilityPred (Time := NNReal) (X := X)}
    {L : WeightedObservable}
    {selector : ι → ℕ}
    {c ν : ℝ}
    {hc : 0 < c}
    {hν : 0 < ν}
    {curlFrame : ι → X → ℝ}
    {curlBound : ℝ}
    {curlBound_nonneg : 0 ≤ curlBound}
    {hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound}
    {x : ModeState}
    (B : L.WindowedColeHopfHeatFoundationData
      (ι := ι) (X := X) K Compat
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x) :
    AlmostFeffermanBridge
      (K := K)
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x) where
  candidate :=
    L.windowedColeHopfHeatCandidate
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
  regularity := B.regularity
  dynamics := B.dynamics
  energy := B.energy

theorem WeightedObservable.WindowedColeHopfHeatFoundationData.realizes_clause_of_compatibility
    {K : FeffermanPredicateKit (Time := NNReal) (X := X)}
    {Compat : VorticityCompatibilityPred (Time := NNReal) (X := X)}
    {L : WeightedObservable}
    {selector : ι → ℕ}
    {c ν : ℝ}
    {hc : 0 < c}
    {hν : 0 < ν}
    {curlFrame : ι → X → ℝ}
    {curlBound : ℝ}
    {curlBound_nonneg : 0 ≤ curlBound}
    {hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound}
    {x : ModeState}
    (B : L.WindowedColeHopfHeatFoundationData
      (ι := ι) (X := X) K Compat
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
    (hcompat :
      Compat
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
        (L.windowedColeHopfHeatCandidate
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity) :
    FeffermanGlobalRegularityClause K :=
  B.toAlmostBridge.realizes_clause_of_compatibility hcompat

end WindowedColeHopfHeatFoundationFrontier

end NavierStokes
end FluidDynamics
end Mettapedia
