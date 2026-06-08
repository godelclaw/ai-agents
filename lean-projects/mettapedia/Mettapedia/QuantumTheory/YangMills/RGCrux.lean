import Mettapedia.QuantumTheory.YangMills.Clustering
import Mettapedia.QuantumTheory.YangMills.RGBootstrap

/-!
# Yang-Mills RG Route Crux

This file switches the Yang-Mills lane from reusable infrastructure to a
route-level obstruction.  It does not assert that Yang-Mills lacks a mass gap.
It says that a manuscript-style route certificate using the advertised
same-constant recombination bound `2224`, block factor `2`, and any extraction
depth `dmax ≤ 14` cannot exist: the required RG contraction is arithmetically
false before the OS/clustering layer is reached.

The raw natural-number arithmetic is deliberately kept separate from the
manuscript-shape even-depth audit: `dmax = 15` contracts numerically, but it is
not one of the even canonical-dimension cutoffs `4, 6, ..., dmax` used by the
manuscript.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills

/-- Same-constant lower-extraction RG certificate: a proposed repair keeps the
manuscript's advertised recombination bound `2224` and block factor `2`, but
tries to close the RG contraction with extraction depth at most `14`. -/
def SameConstantLowerExtractionRGCertificate (dmax : ℕ) : Prop :=
  dmax ≤ 14 ∧ HasExtendedExtractionContraction 2224 2 dmax

/-- Same-constant lower-extraction certificate in the manuscript's even
canonical-dimension shape: the cutoff is strictly below `16`, is even, and uses
the same advertised recombination bound `2224`. -/
def SameConstantEvenBelowSixteenRGCertificate (dmax : ℕ) : Prop :=
  dmax < 16 ∧ Even dmax ∧ HasExtendedExtractionContraction 2224 2 dmax

/-- Threshold lower-extraction certificate in the manuscript's even
canonical-dimension shape: the cutoff is strictly below `16`, is even, and the
recombination constant is no smaller than `2048`.  Any surviving repair on this
surface would therefore need a genuinely sharper constant. -/
def AtLeast2048EvenBelowSixteenRGCertificate (C : ℝ) (dmax : ℕ) : Prop :=
  dmax < 16 ∧ Even dmax ∧ 2048 ≤ C ∧ HasExtendedExtractionContraction C 2 dmax

/-- A same-constant lower-extraction route certificate for a candidate
Hamiltonian gap.  The spectral gap and clustering bridge components record the
surrounding Yang-Mills route, while the RG certificate records the specific
lower-extraction repair attempt being audited. -/
def SameConstantLowerExtractionGapRouteCertificate
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (A : LinearOperator H) (corr : SpatialCorrelation) (Δ : ℝ) : Prop :=
  HasSpectralMassGap A Δ ∧
    SpectralGapClusteringBridge A corr ∧
      ∃ dmax : ℕ, SameConstantLowerExtractionRGCertificate dmax

/-- Same as `SameConstantLowerExtractionGapRouteCertificate`, but with the
manuscript-shape even cutoff made explicit. -/
def SameConstantEvenBelowSixteenGapRouteCertificate
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (A : LinearOperator H) (corr : SpatialCorrelation) (Δ : ℝ) : Prop :=
  HasSpectralMassGap A Δ ∧
    SpectralGapClusteringBridge A corr ∧
      ∃ dmax : ℕ, SameConstantEvenBelowSixteenRGCertificate dmax

/-- Same surrounding route surface as
`SameConstantEvenBelowSixteenGapRouteCertificate`, but the RG component is only
required to use some recombination constant at least `2048`. -/
def AtLeast2048EvenBelowSixteenGapRouteCertificate
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (A : LinearOperator H) (corr : SpatialCorrelation) (Δ : ℝ) (C : ℝ) : Prop :=
  HasSpectralMassGap A Δ ∧
    SpectralGapClusteringBridge A corr ∧
      ∃ dmax : ℕ, AtLeast2048EvenBelowSixteenRGCertificate C dmax

/-- An even natural extraction depth strictly below `16` is at most `14`.
This tiny arithmetic lemma keeps the route crux honest: the obstruction below
does not pretend that raw `dmax = 15` is impossible. -/
theorem even_lt_sixteen_le_fourteen
    {dmax : ℕ} (hlt : dmax < 16) (heven : Even dmax) :
    dmax ≤ 14 := by
  rcases heven with ⟨k, hk⟩
  omega

/-- No same-constant RG certificate exists at extraction depth `dmax ≤ 14`. -/
theorem not_sameConstantLowerExtractionRGCertificate
    {dmax : ℕ} :
    ¬ SameConstantLowerExtractionRGCertificate dmax := by
  intro hcert
  exact (not_rgContraction_2224_two_of_dmax_le_fourteen hcert.1) hcert.2

/-- No same-constant RG certificate exists for an even manuscript-shape cutoff
strictly below `16`. -/
theorem not_sameConstantEvenBelowSixteenRGCertificate
    {dmax : ℕ} :
    ¬ SameConstantEvenBelowSixteenRGCertificate dmax := by
  intro hcert
  have hdmax : dmax ≤ 14 :=
    even_lt_sixteen_le_fourteen hcert.1 hcert.2.1
  exact (not_rgContraction_2224_two_of_dmax_le_fourteen hdmax) hcert.2.2

/-- No even manuscript-shape lower-extraction RG certificate exists once the
recombination constant is at least `2048`. -/
theorem not_atLeast2048EvenBelowSixteenRGCertificate
    {C : ℝ} {dmax : ℕ} :
    ¬ AtLeast2048EvenBelowSixteenRGCertificate C dmax := by
  intro hcert
  have hdmax : dmax ≤ 14 :=
    even_lt_sixteen_le_fourteen hcert.1 hcert.2.1
  exact
    (not_rgContraction_two_of_ge_2048_of_dmax_le_fourteen hcert.2.2.1 hdmax)
      hcert.2.2.2

/-- There is no lower-extraction same-constant RG certificate at any depth
`dmax ≤ 14`. -/
theorem not_exists_sameConstantLowerExtractionRGCertificate :
    ¬ ∃ dmax : ℕ, SameConstantLowerExtractionRGCertificate dmax := by
  intro hcert
  rcases hcert with ⟨dmax, hdmax⟩
  exact not_sameConstantLowerExtractionRGCertificate hdmax

/-- There is no even manuscript-shape same-constant RG certificate below
`dmax = 16`. -/
theorem not_exists_sameConstantEvenBelowSixteenRGCertificate :
    ¬ ∃ dmax : ℕ, SameConstantEvenBelowSixteenRGCertificate dmax := by
  intro hcert
  rcases hcert with ⟨dmax, hdmax⟩
  exact not_sameConstantEvenBelowSixteenRGCertificate hdmax

/-- There is no even manuscript-shape lower-extraction RG certificate below
`dmax = 16` for any recombination constant at least `2048`. -/
theorem not_exists_atLeast2048EvenBelowSixteenRGCertificate
    {C : ℝ} :
    ¬ ∃ dmax : ℕ, AtLeast2048EvenBelowSixteenRGCertificate C dmax := by
  intro hcert
  rcases hcert with ⟨dmax, hdmax⟩
  exact not_atLeast2048EvenBelowSixteenRGCertificate hdmax

/-- Crux-out route statement: a proposed Yang-Mills mass-gap route cannot keep
the advertised constant `2224`, lower the extraction depth to at most `14`, and
still claim the same RG contraction certificate. -/
theorem not_sameConstantLowerExtractionGapRouteCertificate
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {corr : SpatialCorrelation} {Δ : ℝ} :
    ¬ SameConstantLowerExtractionGapRouteCertificate A corr Δ := by
  intro hroute
  exact not_exists_sameConstantLowerExtractionRGCertificate hroute.2.2

/-- Manuscript-shape crux-out route statement: a proposed Yang-Mills mass-gap
route cannot keep the advertised constant `2224`, use an even extraction depth
strictly below `16`, and still claim the same RG contraction certificate. -/
theorem not_sameConstantEvenBelowSixteenGapRouteCertificate
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {corr : SpatialCorrelation} {Δ : ℝ} :
    ¬ SameConstantEvenBelowSixteenGapRouteCertificate A corr Δ := by
  intro hroute
  exact not_exists_sameConstantEvenBelowSixteenRGCertificate hroute.2.2

/-- Strengthened manuscript-shape crux-out route statement: a proposed
Yang-Mills mass-gap route cannot use any block-factor-`2` lower-even extraction
certificate below `dmax = 16` whose recombination constant is at least
`2048`. -/
theorem not_atLeast2048EvenBelowSixteenGapRouteCertificate
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {corr : SpatialCorrelation} {Δ : ℝ} {C : ℝ} :
    ¬ AtLeast2048EvenBelowSixteenGapRouteCertificate A corr Δ C := by
  intro hroute
  exact not_exists_atLeast2048EvenBelowSixteenRGCertificate hroute.2.2

/-- Pointed version for the nearest even depth below the manuscript's
`dmax = 16`: the route would need an RG constant below `2048`, so the
advertised same-bound constant `2224` cannot certify the contraction. -/
theorem not_sameConstantFourteenExtractionGapRouteCertificate
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {corr : SpatialCorrelation} {Δ : ℝ} :
    ¬ (HasSpectralMassGap A Δ ∧
        SpectralGapClusteringBridge A corr ∧
          HasExtendedExtractionContraction 2224 2 14) := by
  intro hroute
  exact not_rgContraction_2224_two_fourteen hroute.2.2

end YangMills
end QuantumTheory
end Mettapedia
