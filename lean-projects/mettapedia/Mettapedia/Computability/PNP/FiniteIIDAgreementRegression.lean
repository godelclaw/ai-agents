import Mettapedia.Computability.PNP.FiniteIIDAgreement

namespace Mettapedia.Computability.PNP.FiniteIIDAgreementRegression

open Mettapedia.Computability.PNP
open scoped BigOperators

universe u v

theorem finite_region_agreement_mass_lower_bound_regression
    {Input : Type u} {Output : Type v}
    [Fintype Input] [DecidableEq Output]
    {μ : PMF Input} {target predict : Input → Output}
    (region : Finset Input)
    (hagree : ∀ x, x ∈ region → predict x = target x) :
    region.sum (fun x => μ x) ≤ agreementMass μ target predict := by
  exact finset_mass_le_agreementMass_of_agrees_on region hagree

theorem finite_region_consistent_sample_mass_lower_bound_regression
    {Input : Type u} {Output : Type v}
    [Fintype Input] [DecidableEq Output]
    {μ : PMF Input} {target predict : Input → Output}
    (region : Finset Input)
    (hagree : ∀ x, x ∈ region → predict x = target x)
    (m : ℕ) :
    region.sum (fun x => μ x) ^ m ≤ consistentSampleMass μ target predict m := by
  exact regionMass_pow_le_consistentSampleMass_of_agrees_on region hagree m

theorem agreement_mass_one_forces_support_agreement_regression
    {Input : Type u} {Output : Type v}
    [Fintype Input] [DecidableEq Output]
    {μ : PMF Input} {target predict : Input → Output}
    (hone : agreementMass μ target predict = 1)
    (x : Input) (hxμ : μ x ≠ 0) :
    predict x = target x := by
  exact agrees_on_support_of_agreementMass_eq_one hone x hxμ

theorem positive_mass_disagreement_blocks_perfect_agreement_regression
    {Input : Type u} {Output : Type v}
    [Fintype Input] [DecidableEq Output]
    {μ : PMF Input} {target predict : Input → Output} {x : Input}
    (hxμ : μ x ≠ 0)
    (hdisagree : predict x ≠ target x) :
    agreementMass μ target predict < 1 := by
  exact agreementMass_lt_one_of_pos_mass_disagreement hxμ hdisagree

theorem pure_atom_disagreement_blocks_perfect_agreement_regression
    {Input : Type u} {Output : Type v}
    [Fintype Input] [DecidableEq Output]
    {target predict : Input → Output} {x : Input}
    (hdisagree : predict x ≠ target x) :
    agreementMass (PMF.pure x) target predict < 1 := by
  have hxμ : PMF.pure x x ≠ 0 := by simp
  exact agreementMass_lt_one_of_pos_mass_disagreement
    (μ := PMF.pure x) (target := target) (predict := predict) hxμ hdisagree

end Mettapedia.Computability.PNP.FiniteIIDAgreementRegression
