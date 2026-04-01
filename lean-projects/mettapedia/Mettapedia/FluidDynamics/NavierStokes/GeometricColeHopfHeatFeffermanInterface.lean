import Mettapedia.FluidDynamics.NavierStokes.FeffermanGrassrootsInterface
import Mettapedia.FluidDynamics.NavierStokes.GeometricColeHopfHeatApproximation
import Mettapedia.FluidDynamics.NavierStokes.GeometricColeHopfPackage

/-!
# Fefferman Lift Interface for the Geometric Cole-Hopf Heat Package

This file pins the generic grassroots lift interface to the current most
concrete positive NS package: the geometric Cole-Hopf shared approximation with
heat-decayed coefficient data.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section GeometricColeHopfHeatFefferman

variable {ι X : Type*}
variable [Fintype ι]
variable (K : FeffermanPredicateKit (Time := NNReal) (X := X))
variable (Compat : VorticityCompatibilityPred (Time := NNReal) (X := X))

/-- The concrete shared approximation package used by the current heat-decayed
Cole-Hopf route. -/
abbrev WeightedObservable.geometricColeHopfHeatSharedPackage
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (ν B : ℝ)
    (hν : 0 < ν)
    (hB : 0 ≤ B)
    (cutoff : ℝ → ℝ)
    (hcutoff_cont : Continuous cutoff)
    (hcutoff : ∀ r, |cutoff r| ≤ B)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound) :
    SharedApproximationPackage (Time := NNReal) (ι := ι) (X := X)
      radiusSq (matchingObservable L) :=
  L.geometricColeHopfHeatApproximation
    selector ν B hν hB cutoff hcutoff_cont hcutoff
    curlFrame curlBound curlBound_nonneg hcurl

/-- The concrete vorticity tendril delivered by the current heat-decayed
Cole-Hopf package at a base state `x`. -/
def WeightedObservable.geometricColeHopfHeatUniformVorticityTendril
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (ν B : ℝ)
    (hν : 0 < ν)
    (hB : 0 ≤ B)
    (cutoff : ℝ → ℝ)
    (hcutoff_cont : Continuous cutoff)
    (hcutoff : ∀ r, |cutoff r| ≤ B)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState) :
    UniformVorticityTendril (Time := NNReal) (X := X) :=
  (L.geometricColeHopfHeatSharedPackage
    (ι := ι) (X := X)
    selector ν B hν hB cutoff hcutoff_cont hcutoff
    curlFrame curlBound curlBound_nonneg hcurl).toUniformVorticityTendril x

/-- Explicit envelope formula carried by the current heat-decayed Cole-Hopf
package. -/
def WeightedObservable.geometricColeHopfHeatEnvelope
    (L : WeightedObservable)
    (ν B curlBound : ℝ) : ℝ :=
  coleHopfVorticityEnvelope ν
    (L.geometricColeHopfLowerBound ν B)
    (L.geometricColeHopfEnergyBound (ι := ι) ν B)
    curlBound

theorem WeightedObservable.geometricColeHopfHeat_abs_vorticity_le_uniform
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (ν B : ℝ)
    (hν : 0 < ν)
    (hB : 0 ≤ B)
    (cutoff : ℝ → ℝ)
    (hcutoff_cont : Continuous cutoff)
    (hcutoff : ∀ r, |cutoff r| ≤ B)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState) :
    ∀ t y,
      |(L.geometricColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector ν B hν hB cutoff hcutoff_cont hcutoff
        curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y| ≤
        L.geometricColeHopfHeatEnvelope (ι := ι) ν B curlBound := by
  let S :=
    L.geometricColeHopfHeatUniformVorticityTendril
      (ι := ι) (X := X)
      selector ν B hν hB cutoff hcutoff_cont hcutoff
      curlFrame curlBound curlBound_nonneg hcurl x
  have h := S.abs_vorticity_le_uniform
  simpa [WeightedObservable.geometricColeHopfHeatEnvelope,
    WeightedObservable.geometricColeHopfHeatUniformVorticityTendril, S] using h

/-- The current concrete positive route only needs the generic shared-package
lift data on top of its heat-decayed package. -/
abbrev WeightedObservable.GeometricColeHopfHeatLiftData
    (L : WeightedObservable)
    (K : FeffermanPredicateKit (Time := NNReal) (X := X))
    (Compat : VorticityCompatibilityPred (Time := NNReal) (X := X))
    (selector : ι → ℕ)
    (ν B : ℝ)
    (hν : 0 < ν)
    (hB : 0 ≤ B)
    (cutoff : ℝ → ℝ)
    (hcutoff_cont : Continuous cutoff)
    (hcutoff : ∀ r, |cutoff r| ≤ B)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState) :=
  SharedApproximationLiftData K Compat
    (S := L.geometricColeHopfHeatSharedPackage
      (ι := ι) (X := X)
      selector ν B hν hB cutoff hcutoff_cont hcutoff
      curlFrame curlBound curlBound_nonneg hcurl)
    x

theorem WeightedObservable.geometricColeHopfHeatLiftData_realizes_clause
    {L : WeightedObservable}
    {K : FeffermanPredicateKit (Time := NNReal) (X := X)}
    {Compat : VorticityCompatibilityPred (Time := NNReal) (X := X)}
    {selector : ι → ℕ}
    {ν B : ℝ}
    {hν : 0 < ν}
    {hB : 0 ≤ B}
    {cutoff : ℝ → ℝ}
    {hcutoff_cont : Continuous cutoff}
    {hcutoff : ∀ r, |cutoff r| ≤ B}
    {curlFrame : ι → X → ℝ}
    {curlBound : ℝ}
    {curlBound_nonneg : 0 ≤ curlBound}
    {hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound}
    {x : ModeState}
    (Bdata : L.GeometricColeHopfHeatLiftData
      (ι := ι) (X := X) K Compat
      selector ν B hν hB cutoff hcutoff_cont hcutoff
      curlFrame curlBound curlBound_nonneg hcurl x) :
    FeffermanGlobalRegularityClause K := by
  exact Bdata.realizes_clause

theorem WeightedObservable.geometricColeHopfHeatLiftData_retains_uniform_vorticity
    {L : WeightedObservable}
    {K : FeffermanPredicateKit (Time := NNReal) (X := X)}
    {Compat : VorticityCompatibilityPred (Time := NNReal) (X := X)}
    {selector : ι → ℕ}
    {ν B : ℝ}
    {hν : 0 < ν}
    {hB : 0 ≤ B}
    {cutoff : ℝ → ℝ}
    {hcutoff_cont : Continuous cutoff}
    {hcutoff : ∀ r, |cutoff r| ≤ B}
    {curlFrame : ι → X → ℝ}
    {curlBound : ℝ}
    {curlBound_nonneg : 0 ≤ curlBound}
    {hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound}
    {x : ModeState}
    (Bdata : L.GeometricColeHopfHeatLiftData
      (ι := ι) (X := X) K Compat
      selector ν B hν hB cutoff hcutoff_cont hcutoff
      curlFrame curlBound curlBound_nonneg hcurl x) :
    ∀ t y,
      |(L.geometricColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector ν B hν hB cutoff hcutoff_cont hcutoff
        curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y| ≤
      (L.geometricColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector ν B hν hB cutoff hcutoff_cont hcutoff
        curlFrame curlBound curlBound_nonneg hcurl x).envelope := by
  simpa [WeightedObservable.geometricColeHopfHeatUniformVorticityTendril,
    WeightedObservable.geometricColeHopfHeatSharedPackage] using
    Bdata.retains_uniform_vorticity

end GeometricColeHopfHeatFefferman

end NavierStokes
end FluidDynamics
end Mettapedia
