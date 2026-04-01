import Mettapedia.FluidDynamics.NavierStokes.ManuscriptChartPackage
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Windowed Cutoff Through the NS Approximation Shell

This file records a positive fact about the current grassroots NS route:
a genuine smooth window cutoff still passes through the existing approximation
interfaces, because those interfaces only require cutoff continuity.

So leaving the stricter `EnergyProfile` shell does not, by itself, block the
chart-side truncation and Cole-Hopf convergence story.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open Filter

section WindowedCutoffApproximation

variable {Time ι X : Type*}
variable [One Time] [Mul Time] [Fintype ι]

/-- A smooth window cutoff: it turns on and later turns off. -/
def smoothWindowCutoff (c : ℝ) : ℝ → ℝ :=
  fun u => u * (Real.smoothTransition (c * u + 1) - Real.smoothTransition (c * u))

theorem continuous_smoothWindowCutoff (c : ℝ) :
    Continuous (smoothWindowCutoff c) := by
  unfold smoothWindowCutoff
  refine continuous_id.mul ?_
  exact
    (Real.smoothTransition.continuous.comp
      ((continuous_const.mul continuous_id).add continuous_const)).sub
    (Real.smoothTransition.continuous.comp (continuous_const.mul continuous_id))

theorem modeApproximation_windowed_cutoffPotential_tendsto
    (c : ℝ) (x : ModeState) :
    Tendsto
      (fun N => cutoffPotential (smoothWindowCutoff c) modeRadius modeStatistic
        (modeApproximationData.approx N x))
      Filter.atTop
      (nhds (cutoffPotential (smoothWindowCutoff c) modeRadius modeStatistic x)) := by
  exact modeApproximationData.cutoffPotential_tendsto
    (continuous_smoothWindowCutoff c) x

theorem modeApproximation_windowed_coleHopfPhi_tendsto
    (c ν : ℝ) (x : ModeState) :
    Tendsto
      (fun N =>
        coleHopfPhi ν
          (cutoffPotential (smoothWindowCutoff c) modeRadius modeStatistic)
          (modeApproximationData.approx N x))
      Filter.atTop
      (nhds (coleHopfPhi ν
        (cutoffPotential (smoothWindowCutoff c) modeRadius modeStatistic) x)) := by
  exact modeApproximationData.coleHopfPhi_tendsto
    (continuous_smoothWindowCutoff c) x

theorem manuscript_windowedW0_tendsto
    (L : WeightedObservable) (c : ℝ) (x : ModeState) :
    Tendsto
      (fun N => manuscriptW0 (smoothWindowCutoff c) L (truncateModes N x))
      Filter.atTop
      (nhds (manuscriptW0 (smoothWindowCutoff c) L x)) := by
  exact manuscriptW0_tendsto L (continuous_smoothWindowCutoff c) x

theorem manuscript_windowedPhi_tendsto
    (L : WeightedObservable) (c ν : ℝ) (x : ModeState) :
    Tendsto
      (fun N => manuscriptPhi ν (smoothWindowCutoff c) L (truncateModes N x))
      Filter.atTop
      (nhds (manuscriptPhi ν (smoothWindowCutoff c) L x)) := by
  exact manuscriptPhi_tendsto L (continuous_smoothWindowCutoff c) x

theorem WeightedObservable.package_windowed_cutoffPotential_tendsto
    (L : WeightedObservable)
    (S : FiniteModeColeHopfKernelData (Time := Time) (ι := ι) (X := X))
    (c : ℝ) (x : ModeState) :
    Tendsto
      (fun N =>
        cutoffPotential (smoothWindowCutoff c) radiusSq (matchingObservable L)
          (truncateModes N x))
      Filter.atTop
      (nhds (cutoffPotential (smoothWindowCutoff c) radiusSq (matchingObservable L) x)) := by
  exact L.package_cutoffPotential_tendsto S (continuous_smoothWindowCutoff c) x

theorem WeightedObservable.package_windowed_coleHopfPhi_tendsto
    (L : WeightedObservable)
    (S : FiniteModeColeHopfKernelData (Time := Time) (ι := ι) (X := X))
    (c : ℝ) (x : ModeState) :
    Tendsto
      (fun N =>
        coleHopfPhi S.ν
          (cutoffPotential (smoothWindowCutoff c) radiusSq (matchingObservable L))
          (truncateModes N x))
      Filter.atTop
      (nhds (coleHopfPhi S.ν
        (cutoffPotential (smoothWindowCutoff c) radiusSq (matchingObservable L)) x)) := by
  exact L.package_coleHopfPhi_tendsto S (continuous_smoothWindowCutoff c) x

end WindowedCutoffApproximation

end NavierStokes
end FluidDynamics
end Mettapedia
