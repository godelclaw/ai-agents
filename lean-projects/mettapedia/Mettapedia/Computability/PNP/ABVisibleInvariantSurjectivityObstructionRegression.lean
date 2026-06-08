import Mettapedia.Computability.PNP.ABVisibleInvariantSurjectivityObstruction

namespace Mettapedia.Computability.PNP.ABVisibleInvariantSurjectivityObstructionRegression

open Mettapedia.Computability.PNP

def constantFalseCode : SharedAffineDecisionListCode (1 + 1) :=
  ((fun _ => false), false)

def boolConstantCodes : Unit → SharedAffineDecisionListCode (1 + 1) :=
  fun _ => constantFalseCode

theorem canonicalABCodeFamily_ignores_z_regression :
    (canonicalABCodeFamily (Z := Bool) (k := 1) boolConstantCodes).predict ()
        ⟨false, default, default⟩ =
      (canonicalABCodeFamily (Z := Bool) (k := 1) boolConstantCodes).predict ()
        ⟨true, default, default⟩ := by
  rfl

def zProjectionRule (u : ExactVisiblePostSwitchSurface Bool 1) : Bool := u.z

theorem canonicalABCodeFamily_not_zProjectionRule_regression :
    (canonicalABCodeFamily (Z := Bool) (k := 1) boolConstantCodes).predict () ≠
      zProjectionRule := by
  intro h
  have hfalse := congrFun h ⟨false, default, default⟩
  have htrue := congrFun h ⟨true, default, default⟩
  simp [canonicalABCodeFamily, boolConstantCodes, constantFalseCode, zProjectionRule] at hfalse htrue
  exact Bool.false_ne_true (hfalse.symm.trans htrue)

theorem canonicalABCodeFamily_not_surjective_of_nontrivial_regression :
    ¬ Function.Surjective
        (canonicalABCodeFamily (Z := Bool) (k := 1) boolConstantCodes).predict := by
  exact
    canonicalABCodeFamily_not_surjective_of_nontrivial
      (Z := Bool) (k := 1) (Index := Unit) boolConstantCodes

theorem boolZProjectionRule_separates_ab_fiber_regression :
    ABFiberSeparatingRule (Z := Bool) (k := 1) (boolZProjectionRule (k := 1)) := by
  exact boolZProjectionRule_abFiberSeparatingRule (k := 1)

theorem ab_visible_invariant_family_not_realize_zProjectionRule_regression
    {Index : Type*} {G : ExactVisibleSwitchedFamily Bool 1 Index}
    (hinv : ABVisibleInvariant (Z := Bool) (k := 1) G) :
    ¬ ∃ i, G.predict i = boolZProjectionRule (k := 1) := by
  exact not_exists_predict_eq_boolZProjectionRule_of_abVisibleInvariant
    (k := 1) hinv

theorem canonicalABCodeFamily_not_exists_predict_eq_boolZProjectionRule_regression :
    ¬ ∃ i,
        (canonicalABCodeFamily (Z := Bool) (k := 1) boolConstantCodes).predict i =
          boolZProjectionRule (k := 1) := by
  exact
    canonicalABCodeFamily_not_exists_predict_eq_boolZProjectionRule
      (k := 1) (Index := Unit) boolConstantCodes

theorem canonicalABDecisionListCandidateData_not_surjective_of_nontrivial_regression :
    ¬ Function.Surjective
        (canonicalABCodeFamily (Z := Bool) (k := 1) boolConstantCodes).predict := by
  exact
    CanonicalABDecisionListCandidateData.not_surjective_predict_of_nontrivial
      (Z := Bool) (k := 1) (Index := Unit)
      (canonicalABDecisionListCandidateData_of_codes
        (Z := Bool) (k := 1) (Index := Unit) boolConstantCodes)

theorem canonicalABDecisionListCandidateData_not_exists_predict_eq_boolZProjectionRule_regression :
    ¬ ∃ i,
        (canonicalABCodeFamily (Z := Bool) (k := 1) boolConstantCodes).predict i =
          boolZProjectionRule (k := 1) := by
  exact
    CanonicalABDecisionListCandidateData.not_exists_predict_eq_boolZProjectionRule
      (k := 1) (Index := Unit)
      (canonicalABDecisionListCandidateData_of_codes
        (Z := Bool) (k := 1) (Index := Unit) boolConstantCodes)

theorem ab_visible_invariant_predict_disagrees_on_separating_support_regression
    {Index : Type*} {G : ExactVisibleSwitchedFamily Bool 1 Index}
    (hinv : ABVisibleInvariant (Z := Bool) (k := 1) G)
    {μ : PMF (ExactVisiblePostSwitchSurface Bool 1)}
    (i : Index)
    (hfalse : μ ⟨false, default, default⟩ ≠ 0)
    (htrue : μ ⟨true, default, default⟩ ≠ 0) :
    ∃ x, μ x ≠ 0 ∧ G.predict i x ≠ boolZProjectionRule (k := 1) x := by
  exact
    exists_pos_mass_disagreement_of_abVisibleInvariant_predict_boolZProjectionRule
      (k := 1) hinv (μ := μ) i hfalse htrue

theorem canonicalABCodeFamily_disagrees_with_zProjection_on_two_point_support_regression
    {μ : PMF (ExactVisiblePostSwitchSurface Bool 1)}
    (hfalse : μ ⟨false, default, default⟩ ≠ 0)
    (htrue : μ ⟨true, default, default⟩ ≠ 0) :
    ∃ x, μ x ≠ 0 ∧
      (canonicalABCodeFamily (Z := Bool) (k := 1) boolConstantCodes).predict () x ≠
        boolZProjectionRule (k := 1) x := by
  exact
    canonicalABCodeFamily_exists_pos_mass_disagreement_boolZProjectionRule
      (k := 1) (Index := Unit) boolConstantCodes (μ := μ) () hfalse htrue

theorem canonicalABDecisionListCandidateData_disagrees_with_zProjection_on_two_point_support_regression
    {μ : PMF (ExactVisiblePostSwitchSurface Bool 1)}
    (hfalse : μ ⟨false, default, default⟩ ≠ 0)
    (htrue : μ ⟨true, default, default⟩ ≠ 0) :
    ∃ x, μ x ≠ 0 ∧
      (canonicalABCodeFamily (Z := Bool) (k := 1) boolConstantCodes).predict () x ≠
        boolZProjectionRule (k := 1) x := by
  exact
    CanonicalABDecisionListCandidateData.exists_pos_mass_disagreement_boolZProjectionRule
      (k := 1) (Index := Unit)
      (canonicalABDecisionListCandidateData_of_codes
        (Z := Bool) (k := 1) (Index := Unit) boolConstantCodes)
      (μ := μ) () hfalse htrue

theorem ab_visible_invariant_predict_has_subunit_agreement_on_two_point_support_regression
    {Index : Type*} {G : ExactVisibleSwitchedFamily Bool 1 Index}
    (hinv : ABVisibleInvariant (Z := Bool) (k := 1) G)
    {μ : PMF (ExactVisiblePostSwitchSurface Bool 1)}
    (i : Index)
    (hfalse : μ ⟨false, default, default⟩ ≠ 0)
    (htrue : μ ⟨true, default, default⟩ ≠ 0) :
    agreementMass μ (boolZProjectionRule (k := 1)) (G.predict i) < 1 := by
  exact
    agreementMass_lt_one_of_abVisibleInvariant_predict_boolZProjectionRule
      (k := 1) hinv (μ := μ) i hfalse htrue

theorem canonicalABCodeFamily_subunit_agreement_with_zProjection_on_two_point_support_regression
    {μ : PMF (ExactVisiblePostSwitchSurface Bool 1)}
    (hfalse : μ ⟨false, default, default⟩ ≠ 0)
    (htrue : μ ⟨true, default, default⟩ ≠ 0) :
    agreementMass μ (boolZProjectionRule (k := 1))
      ((canonicalABCodeFamily (Z := Bool) (k := 1) boolConstantCodes).predict ()) < 1 := by
  exact
    canonicalABCodeFamily_agreementMass_lt_one_boolZProjectionRule
      (k := 1) (Index := Unit) boolConstantCodes (μ := μ) () hfalse htrue

theorem canonicalABDecisionListCandidateData_subunit_agreement_with_zProjection_on_two_point_support_regression
    {μ : PMF (ExactVisiblePostSwitchSurface Bool 1)}
    (hfalse : μ ⟨false, default, default⟩ ≠ 0)
    (htrue : μ ⟨true, default, default⟩ ≠ 0) :
    agreementMass μ (boolZProjectionRule (k := 1))
      ((canonicalABCodeFamily (Z := Bool) (k := 1) boolConstantCodes).predict ()) < 1 := by
  exact
    CanonicalABDecisionListCandidateData.agreementMass_lt_one_boolZProjectionRule
      (k := 1) (Index := Unit)
      (canonicalABDecisionListCandidateData_of_codes
        (Z := Bool) (k := 1) (Index := Unit) boolConstantCodes)
      (μ := μ) () hfalse htrue

theorem ab_visible_invariant_family_has_no_perfect_agreement_on_two_point_support_regression
    {Index : Type*} {G : ExactVisibleSwitchedFamily Bool 1 Index}
    (hinv : ABVisibleInvariant (Z := Bool) (k := 1) G)
    {μ : PMF (ExactVisiblePostSwitchSurface Bool 1)}
    (hfalse : μ ⟨false, default, default⟩ ≠ 0)
    (htrue : μ ⟨true, default, default⟩ ≠ 0) :
    ¬ ∃ i, agreementMass μ (boolZProjectionRule (k := 1)) (G.predict i) = 1 := by
  exact
    not_exists_agreementMass_eq_one_boolZProjectionRule_of_abVisibleInvariant
      (k := 1) hinv (μ := μ) hfalse htrue

theorem canonicalABCodeFamily_has_no_perfect_agreement_with_zProjection_on_two_point_support_regression
    {μ : PMF (ExactVisiblePostSwitchSurface Bool 1)}
    (hfalse : μ ⟨false, default, default⟩ ≠ 0)
    (htrue : μ ⟨true, default, default⟩ ≠ 0) :
    ¬ ∃ i, agreementMass μ (boolZProjectionRule (k := 1))
      ((canonicalABCodeFamily (Z := Bool) (k := 1) boolConstantCodes).predict i) = 1 := by
  exact
    canonicalABCodeFamily_not_exists_agreementMass_eq_one_boolZProjectionRule
      (k := 1) (Index := Unit) boolConstantCodes (μ := μ) hfalse htrue

theorem canonicalABDecisionListCandidateData_has_no_perfect_agreement_with_zProjection_regression
    {μ : PMF (ExactVisiblePostSwitchSurface Bool 1)}
    (hfalse : μ ⟨false, default, default⟩ ≠ 0)
    (htrue : μ ⟨true, default, default⟩ ≠ 0) :
    ¬ ∃ i, agreementMass μ (boolZProjectionRule (k := 1))
      ((canonicalABCodeFamily (Z := Bool) (k := 1) boolConstantCodes).predict i) = 1 := by
  exact
    CanonicalABDecisionListCandidateData.not_exists_agreementMass_eq_one_boolZProjectionRule
      (k := 1) (Index := Unit)
      (canonicalABDecisionListCandidateData_of_codes
        (Z := Bool) (k := 1) (Index := Unit) boolConstantCodes)
      (μ := μ) hfalse htrue

end Mettapedia.Computability.PNP.ABVisibleInvariantSurjectivityObstructionRegression
