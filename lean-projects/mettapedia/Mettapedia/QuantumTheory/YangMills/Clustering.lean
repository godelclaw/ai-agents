import Mettapedia.QuantumTheory.YangMills.MassGap
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Yang-Mills Exponential Clustering Audit

The Clay Yang-Mills statement records exponential clustering as a consequence
of a mass gap.  This file does not attempt the analytic proof of clustering.
It isolates the rate-level obligation in a small, reusable form: if a proposed
Hamiltonian gap is routed through a spectral-gap-to-clustering bridge, then a
single persistent clustering violation at a rate `0 < C < Δ` rules out that
proposed gap.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills

/-- A real-valued spatial two-point correlation kernel.  In later Yang-Mills
work this should be instantiated by a centered vacuum expectation such as
`⟨Ω, O(x)O(y)Ω⟩`. -/
abbrev SpatialCorrelation := Space → Space → ℝ

/-- Exponential clustering at one fixed decay rate `C`: beyond some radius,
the absolute two-point correlation is bounded by `exp (-C * dist x y)`. -/
def HasExponentialClusteringAtRate (corr : SpatialCorrelation) (C : ℝ) : Prop :=
  ∃ R : ℝ, 0 ≤ R ∧
    ∀ x y : Space, R ≤ dist x y →
      |corr x y| ≤ Real.exp (-C * dist x y)

/-- Exponential clustering for every rate strictly below the proposed gap. -/
def HasExponentialClusteringUpTo (corr : SpatialCorrelation) (Δ : ℝ) : Prop :=
  ∀ C : ℝ, 0 < C → C < Δ → HasExponentialClusteringAtRate corr C

/-- A concrete rate-level obstruction: no matter how far out one looks, there
is a pair of points violating the exponential clustering bound at rate `C`. -/
def HasArbitrarilyLargeClusteringViolation
    (corr : SpatialCorrelation) (C : ℝ) : Prop :=
  ∀ R : ℝ, 0 ≤ R →
    ∃ x y : Space,
      R ≤ dist x y ∧ Real.exp (-C * dist x y) < |corr x y|

/-- A persistent positive long-range lower bound for a spatial correlation:
beyond every radius there are two points whose absolute correlation remains at
least `ε`. -/
def HasPositiveLongRangeLowerBound
    (corr : SpatialCorrelation) (ε : ℝ) : Prop :=
  0 < ε ∧
    ∀ R : ℝ, 0 ≤ R →
      ∃ x y : Space, R ≤ dist x y ∧ ε ≤ |corr x y|

/-- Abstract bridge used for auditing proposed Yang-Mills mass-gap routes:
every spectral mass gap for `A` implies clustering of the supplied correlation
kernel up to that gap. -/
def SpectralGapClusteringBridge
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (A : LinearOperator H) (corr : SpatialCorrelation) : Prop :=
  ∀ Δ : ℝ, HasSpectralMassGap A Δ → HasExponentialClusteringUpTo corr Δ

theorem HasExponentialClusteringUpTo.at_rate
    {corr : SpatialCorrelation} {Δ C : ℝ}
    (hcluster : HasExponentialClusteringUpTo corr Δ)
    (hCpos : 0 < C) (hCΔ : C < Δ) :
    HasExponentialClusteringAtRate corr C :=
  hcluster C hCpos hCΔ

/-- If clustering holds for all rates below `Δ`, it holds for all rates below
any smaller endpoint `δ`. -/
theorem HasExponentialClusteringUpTo.mono
    {corr : SpatialCorrelation} {δ Δ : ℝ}
    (hcluster : HasExponentialClusteringUpTo corr Δ)
    (hδΔ : δ ≤ Δ) :
    HasExponentialClusteringUpTo corr δ := by
  intro C hCpos hCδ
  exact hcluster.at_rate hCpos (lt_of_lt_of_le hCδ hδΔ)

/-- Persistent rate-level violations refute clustering at that rate. -/
theorem not_hasExponentialClusteringAtRate_of_arbitrarilyLarge_violation
    {corr : SpatialCorrelation} {C : ℝ}
    (hfail : HasArbitrarilyLargeClusteringViolation corr C) :
    ¬ HasExponentialClusteringAtRate corr C := by
  intro hcluster
  rcases hcluster with ⟨R, hRnonneg, hbound⟩
  rcases hfail R hRnonneg with ⟨x, y, hRxy, hlt⟩
  exact (not_lt_of_ge (hbound x y hRxy)) hlt

/-- Failure of clustering at a single admissible rate refutes the
all-rates-below-`Δ` clustering claim. -/
theorem not_hasExponentialClusteringUpTo_of_rate_failure
    {corr : SpatialCorrelation} {Δ C : ℝ}
    (hCpos : 0 < C) (hCΔ : C < Δ)
    (hfail : ¬ HasExponentialClusteringAtRate corr C) :
    ¬ HasExponentialClusteringUpTo corr Δ := by
  intro hcluster
  exact hfail (hcluster.at_rate hCpos hCΔ)

/-- Persistent violations at one rate below `Δ` refute clustering up to `Δ`. -/
theorem not_hasExponentialClusteringUpTo_of_arbitrarilyLarge_violation
    {corr : SpatialCorrelation} {Δ C : ℝ}
    (hCpos : 0 < C) (hCΔ : C < Δ)
    (hfail : HasArbitrarilyLargeClusteringViolation corr C) :
    ¬ HasExponentialClusteringUpTo corr Δ := by
  exact not_hasExponentialClusteringUpTo_of_rate_failure hCpos hCΔ
    (not_hasExponentialClusteringAtRate_of_arbitrarilyLarge_violation hfail)

theorem SpectralGapClusteringBridge.clusteringUpTo_of_gap
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {corr : SpatialCorrelation} {Δ : ℝ}
    (hbridge : SpectralGapClusteringBridge A corr)
    (hgap : HasSpectralMassGap A Δ) :
    HasExponentialClusteringUpTo corr Δ :=
  hbridge Δ hgap

theorem SpectralGapClusteringBridge.clusteringAtRate_of_gap
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {corr : SpatialCorrelation} {Δ C : ℝ}
    (hbridge : SpectralGapClusteringBridge A corr)
    (hgap : HasSpectralMassGap A Δ)
    (hCpos : 0 < C) (hCΔ : C < Δ) :
    HasExponentialClusteringAtRate corr C :=
  (hbridge.clusteringUpTo_of_gap hgap).at_rate hCpos hCΔ

/-- Crux audit: under a spectral-gap-to-clustering bridge, failure of
clustering at any rate below `Δ` rules out `Δ` as a spectral mass gap. -/
theorem not_hasSpectralMassGap_of_clustering_rate_failure
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {corr : SpatialCorrelation} {Δ C : ℝ}
    (hbridge : SpectralGapClusteringBridge A corr)
    (hCpos : 0 < C) (hCΔ : C < Δ)
    (hfail : ¬ HasExponentialClusteringAtRate corr C) :
    ¬ HasSpectralMassGap A Δ := by
  intro hgap
  exact hfail (hbridge.clusteringAtRate_of_gap hgap hCpos hCΔ)

/-- Concrete witness form of the clustering crux audit. -/
theorem not_hasSpectralMassGap_of_arbitrarilyLarge_clustering_violation
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {corr : SpatialCorrelation} {Δ C : ℝ}
    (hbridge : SpectralGapClusteringBridge A corr)
    (hCpos : 0 < C) (hCΔ : C < Δ)
    (hfail : HasArbitrarilyLargeClusteringViolation corr C) :
    ¬ HasSpectralMassGap A Δ := by
  exact not_hasSpectralMassGap_of_clustering_rate_failure hbridge hCpos hCΔ
    (not_hasExponentialClusteringAtRate_of_arbitrarilyLarge_violation hfail)

/-- Quantitative contrapositive: if clustering fails at a positive rate `C`,
then every spectral gap routed through the bridge is at most `C`. -/
theorem spectralGap_le_of_clustering_rate_failure
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {corr : SpatialCorrelation} {Δ C : ℝ}
    (hbridge : SpectralGapClusteringBridge A corr)
    (hCpos : 0 < C)
    (hfail : ¬ HasExponentialClusteringAtRate corr C)
    (hgap : HasSpectralMassGap A Δ) :
    Δ ≤ C := by
  by_contra hnot
  exact hfail
    (hbridge.clusteringAtRate_of_gap hgap hCpos (lt_of_not_ge hnot))

/-- Persistent concrete violations at rate `C` upper-bound every bridged
spectral gap by `C`. -/
theorem spectralGap_le_of_arbitrarilyLarge_clustering_violation
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {corr : SpatialCorrelation} {Δ C : ℝ}
    (hbridge : SpectralGapClusteringBridge A corr)
    (hCpos : 0 < C)
    (hfail : HasArbitrarilyLargeClusteringViolation corr C)
    (hgap : HasSpectralMassGap A Δ) :
    Δ ≤ C :=
  spectralGap_le_of_clustering_rate_failure hbridge hCpos
    (not_hasExponentialClusteringAtRate_of_arbitrarilyLarge_violation hfail)
    hgap

/-- Supremum audit form: one failed clustering rate bounds the supremum of all
admitted gaps, provided at least one gap is admitted. -/
theorem spectralGapSup_le_of_clustering_rate_failure_of_gap
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {corr : SpatialCorrelation} {Δ₀ C : ℝ}
    (hbridge : SpectralGapClusteringBridge A corr)
    (hgap₀ : HasSpectralMassGap A Δ₀)
    (hCpos : 0 < C)
    (hfail : ¬ HasExponentialClusteringAtRate corr C) :
    SpectralGapSup A ≤ C :=
  spectralGapSup_le_of_gap_bound hgap₀ (by
    intro Δ hgap
    exact spectralGap_le_of_clustering_rate_failure hbridge hCpos hfail hgap)

/-- If a bridged correlation fails to cluster at every positive rate, then no
positive spectral gap can exist for that route. -/
theorem not_exists_hasSpectralMassGap_of_all_positive_clustering_rate_failure
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {corr : SpatialCorrelation}
    (hbridge : SpectralGapClusteringBridge A corr)
    (hfail : ∀ C : ℝ, 0 < C → ¬ HasExponentialClusteringAtRate corr C) :
    ¬ ∃ Δ : ℝ, HasSpectralMassGap A Δ := by
  rintro ⟨Δ, hgap⟩
  have hCpos : 0 < Δ / 2 := by linarith [hgap.positive]
  have hCΔ : Δ / 2 < Δ := by linarith [hgap.positive]
  exact hfail (Δ / 2) hCpos
    (hbridge.clusteringAtRate_of_gap hgap hCpos hCΔ)

/-- Concrete persistent-violation form of the no-gap criterion at all positive
rates. -/
theorem not_exists_hasSpectralMassGap_of_all_positive_arbitrarilyLarge_clustering_violation
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {corr : SpatialCorrelation}
    (hbridge : SpectralGapClusteringBridge A corr)
    (hfail : ∀ C : ℝ, 0 < C → HasArbitrarilyLargeClusteringViolation corr C) :
    ¬ ∃ Δ : ℝ, HasSpectralMassGap A Δ := by
  exact not_exists_hasSpectralMassGap_of_all_positive_clustering_rate_failure
    hbridge (by
      intro C hCpos
      exact not_hasExponentialClusteringAtRate_of_arbitrarilyLarge_violation
        (hfail C hCpos))

/-- A positive long-range lower bound beats every positive exponential decay
rate, producing persistent clustering violations at that rate. -/
theorem HasPositiveLongRangeLowerBound.arbitrarilyLargeClusteringViolation
    {corr : SpatialCorrelation} {ε C : ℝ}
    (hlower : HasPositiveLongRangeLowerBound corr ε)
    (hCpos : 0 < C) :
    HasArbitrarilyLargeClusteringViolation corr C := by
  intro R hR
  let R' : ℝ := max R ((1 - Real.log ε) / C)
  have hRR' : R ≤ R' := le_max_left _ _
  have hthresholdR' : (1 - Real.log ε) / C ≤ R' := le_max_right _ _
  have hR'nonneg : 0 ≤ R' := le_trans hR hRR'
  rcases hlower.2 R' hR'nonneg with ⟨x, y, hR'dist, hεle⟩
  refine ⟨x, y, le_trans hRR' hR'dist, lt_of_lt_of_le ?_ hεle⟩
  have hthreshold : (1 - Real.log ε) / C ≤ dist x y :=
    le_trans hthresholdR' hR'dist
  have hmul : 1 - Real.log ε ≤ C * dist x y := by
    simpa [mul_comm] using (div_le_iff₀ hCpos).mp hthreshold
  have hlog_lt : -C * dist x y < Real.log ε := by
    nlinarith
  rw [← Real.exp_log hlower.1]
  exact Real.exp_lt_exp.mpr hlog_lt

/-- A positive long-range lower bound rules out every positive spectral gap
under a spectral-gap-to-clustering bridge. -/
theorem not_exists_hasSpectralMassGap_of_positiveLongRangeLowerBound
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {corr : SpatialCorrelation} {ε : ℝ}
    (hbridge : SpectralGapClusteringBridge A corr)
    (hlower : HasPositiveLongRangeLowerBound corr ε) :
    ¬ ∃ Δ : ℝ, HasSpectralMassGap A Δ := by
  exact
    not_exists_hasSpectralMassGap_of_all_positive_arbitrarilyLarge_clustering_violation
      hbridge (by
        intro C hCpos
        exact hlower.arbitrarilyLargeClusteringViolation hCpos)

end YangMills
end QuantumTheory
end Mettapedia
