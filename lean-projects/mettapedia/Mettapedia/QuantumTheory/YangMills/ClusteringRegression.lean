import Mettapedia.QuantumTheory.YangMills.Clustering

/-!
# Yang-Mills Exponential Clustering Regression

Theorem-level checks for the abstract clustering bridge and its rate-level
obstruction form.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace ClusteringRegression

theorem clustering_up_to_rate_regression
    {corr : SpatialCorrelation} {Δ C : ℝ}
    (hcluster : HasExponentialClusteringUpTo corr Δ)
    (hCpos : 0 < C) (hCΔ : C < Δ) :
    HasExponentialClusteringAtRate corr C := by
  exact hcluster.at_rate hCpos hCΔ

theorem clustering_up_to_mono_regression
    {corr : SpatialCorrelation} {δ Δ : ℝ}
    (hcluster : HasExponentialClusteringUpTo corr Δ)
    (hδΔ : δ ≤ Δ) :
    HasExponentialClusteringUpTo corr δ := by
  exact hcluster.mono hδΔ

theorem rate_violation_blocks_rate_clustering_regression
    {corr : SpatialCorrelation} {C : ℝ}
    (hfail : HasArbitrarilyLargeClusteringViolation corr C) :
    ¬ HasExponentialClusteringAtRate corr C := by
  exact not_hasExponentialClusteringAtRate_of_arbitrarilyLarge_violation hfail

theorem rate_failure_blocks_clustering_up_to_regression
    {corr : SpatialCorrelation} {Δ C : ℝ}
    (hCpos : 0 < C) (hCΔ : C < Δ)
    (hfail : ¬ HasExponentialClusteringAtRate corr C) :
    ¬ HasExponentialClusteringUpTo corr Δ := by
  exact not_hasExponentialClusteringUpTo_of_rate_failure hCpos hCΔ hfail

theorem rate_violation_blocks_clustering_up_to_regression
    {corr : SpatialCorrelation} {Δ C : ℝ}
    (hCpos : 0 < C) (hCΔ : C < Δ)
    (hfail : HasArbitrarilyLargeClusteringViolation corr C) :
    ¬ HasExponentialClusteringUpTo corr Δ := by
  exact not_hasExponentialClusteringUpTo_of_arbitrarilyLarge_violation
    hCpos hCΔ hfail

theorem bridge_gap_gives_clustering_up_to_regression
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {corr : SpatialCorrelation} {Δ : ℝ}
    (hbridge : SpectralGapClusteringBridge A corr)
    (hgap : HasSpectralMassGap A Δ) :
    HasExponentialClusteringUpTo corr Δ := by
  exact hbridge.clusteringUpTo_of_gap hgap

theorem bridge_gap_gives_clustering_at_rate_regression
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {corr : SpatialCorrelation} {Δ C : ℝ}
    (hbridge : SpectralGapClusteringBridge A corr)
    (hgap : HasSpectralMassGap A Δ)
    (hCpos : 0 < C) (hCΔ : C < Δ) :
    HasExponentialClusteringAtRate corr C := by
  exact hbridge.clusteringAtRate_of_gap hgap hCpos hCΔ

theorem bridge_rate_failure_blocks_spectral_gap_regression
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {corr : SpatialCorrelation} {Δ C : ℝ}
    (hbridge : SpectralGapClusteringBridge A corr)
    (hCpos : 0 < C) (hCΔ : C < Δ)
    (hfail : ¬ HasExponentialClusteringAtRate corr C) :
    ¬ HasSpectralMassGap A Δ := by
  exact not_hasSpectralMassGap_of_clustering_rate_failure
    hbridge hCpos hCΔ hfail

theorem bridge_rate_violation_blocks_spectral_gap_regression
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {corr : SpatialCorrelation} {Δ C : ℝ}
    (hbridge : SpectralGapClusteringBridge A corr)
    (hCpos : 0 < C) (hCΔ : C < Δ)
    (hfail : HasArbitrarilyLargeClusteringViolation corr C) :
    ¬ HasSpectralMassGap A Δ := by
  exact not_hasSpectralMassGap_of_arbitrarilyLarge_clustering_violation
    hbridge hCpos hCΔ hfail

theorem bridge_rate_failure_bounds_spectral_gap_regression
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {corr : SpatialCorrelation} {Δ C : ℝ}
    (hbridge : SpectralGapClusteringBridge A corr)
    (hCpos : 0 < C)
    (hfail : ¬ HasExponentialClusteringAtRate corr C)
    (hgap : HasSpectralMassGap A Δ) :
    Δ ≤ C := by
  exact spectralGap_le_of_clustering_rate_failure
    hbridge hCpos hfail hgap

theorem bridge_rate_violation_bounds_spectral_gap_regression
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {corr : SpatialCorrelation} {Δ C : ℝ}
    (hbridge : SpectralGapClusteringBridge A corr)
    (hCpos : 0 < C)
    (hfail : HasArbitrarilyLargeClusteringViolation corr C)
    (hgap : HasSpectralMassGap A Δ) :
    Δ ≤ C := by
  exact spectralGap_le_of_arbitrarilyLarge_clustering_violation
    hbridge hCpos hfail hgap

theorem bridge_rate_failure_bounds_gap_sup_regression
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {corr : SpatialCorrelation} {Δ₀ C : ℝ}
    (hbridge : SpectralGapClusteringBridge A corr)
    (hgap₀ : HasSpectralMassGap A Δ₀)
    (hCpos : 0 < C)
    (hfail : ¬ HasExponentialClusteringAtRate corr C) :
    SpectralGapSup A ≤ C := by
  exact spectralGapSup_le_of_clustering_rate_failure_of_gap
    hbridge hgap₀ hCpos hfail

theorem all_positive_rate_failures_block_all_spectral_gaps_regression
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {corr : SpatialCorrelation}
    (hbridge : SpectralGapClusteringBridge A corr)
    (hfail : ∀ C : ℝ, 0 < C → ¬ HasExponentialClusteringAtRate corr C) :
    ¬ ∃ Δ : ℝ, HasSpectralMassGap A Δ := by
  exact not_exists_hasSpectralMassGap_of_all_positive_clustering_rate_failure
    hbridge hfail

theorem all_positive_rate_violations_block_all_spectral_gaps_regression
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {corr : SpatialCorrelation}
    (hbridge : SpectralGapClusteringBridge A corr)
    (hfail : ∀ C : ℝ, 0 < C → HasArbitrarilyLargeClusteringViolation corr C) :
    ¬ ∃ Δ : ℝ, HasSpectralMassGap A Δ := by
  exact
    not_exists_hasSpectralMassGap_of_all_positive_arbitrarilyLarge_clustering_violation
      hbridge hfail

theorem positive_long_range_lower_bound_gives_rate_violation_regression
    {corr : SpatialCorrelation} {ε C : ℝ}
    (hlower : HasPositiveLongRangeLowerBound corr ε)
    (hCpos : 0 < C) :
    HasArbitrarilyLargeClusteringViolation corr C := by
  exact hlower.arbitrarilyLargeClusteringViolation hCpos

theorem positive_long_range_lower_bound_blocks_all_spectral_gaps_regression
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {corr : SpatialCorrelation} {ε : ℝ}
    (hbridge : SpectralGapClusteringBridge A corr)
    (hlower : HasPositiveLongRangeLowerBound corr ε) :
    ¬ ∃ Δ : ℝ, HasSpectralMassGap A Δ := by
  exact not_exists_hasSpectralMassGap_of_positiveLongRangeLowerBound
    hbridge hlower

end ClusteringRegression
end YangMills
end QuantumTheory
end Mettapedia
