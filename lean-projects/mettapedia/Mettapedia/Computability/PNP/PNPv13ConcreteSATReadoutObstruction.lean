import Mettapedia.Computability.PNP.PNPv13CruxLedger

/-!
# PNP v13: concrete CNF readout ambiguity

`PNPv13CruxLedger` isolates the abstract SAT-search obligation: if a decoder
must work for any satisfying witness returned by SAT search, all satisfying
witnesses must have the same message readout.  This file instantiates that
obligation on a concrete one-variable CNF tautology.  The point is deliberately
small: even ordinary CNF satisfiability permits multiple satisfying assignments
with different readouts, so a manuscript route must prove a genuine readout
constancy theorem rather than relying on SAT satisfiability alone.
-/

namespace Mettapedia.Computability.PNP

universe u v

namespace ConcreteCNF

/-- Boolean CNF assignments over a variable type. -/
abbrev Assignment (Var : Type u) :=
  Var → Bool

/-- A signed CNF literal. -/
inductive Literal (Var : Type u) where
  | pos : Var → Literal Var
  | neg : Var → Literal Var
  deriving DecidableEq

namespace Literal

/-- Evaluate a signed literal under a Boolean assignment. -/
def eval {Var : Type u} : Literal Var → Assignment Var → Bool
  | pos v, σ => σ v
  | neg v, σ => !σ v

end Literal

/-- A CNF clause is a finite disjunction of literals. -/
abbrev Clause (Var : Type u) :=
  List (Literal Var)

/-- A CNF formula is a finite conjunction of clauses. -/
abbrev Formula (Var : Type u) :=
  List (Clause Var)

/-- Propositional satisfaction of a clause. -/
def IsSatClause {Var : Type u} (clause : Clause Var) (σ : Assignment Var) : Prop :=
  ∃ lit ∈ clause, Literal.eval lit σ = true

/-- Propositional satisfaction of a CNF formula. -/
def IsSatFormula {Var : Type u} (formula : Formula Var) (σ : Assignment Var) : Prop :=
  ∀ clause ∈ formula, IsSatClause clause σ

end ConcreteCNF

/-- The one-variable CNF formula consisting of the tautological clause
`x ∨ ¬x`. -/
def oneVarTautologyCNF : ConcreteCNF.Formula (Fin 1) :=
  [[ConcreteCNF.Literal.pos (0 : Fin 1), ConcreteCNF.Literal.neg (0 : Fin 1)]]

/-- The all-false assignment for the one-variable CNF. -/
def oneVarFalseAssignment : ConcreteCNF.Assignment (Fin 1) :=
  fun _ => false

/-- The all-true assignment for the one-variable CNF. -/
def oneVarTrueAssignment : ConcreteCNF.Assignment (Fin 1) :=
  fun _ => true

/-- The hidden-message readout used by the concrete SAT countermodel: read the
truth value of the single variable. -/
def oneVarReadout (σ : ConcreteCNF.Assignment (Fin 1)) : Bool :=
  σ 0

/-- The false assignment satisfies the tautological one-variable CNF. -/
theorem oneVarTautologyCNF_satisfied_false :
    ConcreteCNF.IsSatFormula oneVarTautologyCNF oneVarFalseAssignment := by
  intro clause hclause
  rw [oneVarTautologyCNF] at hclause
  simp only [List.mem_singleton] at hclause
  rw [hclause]
  exact
    ⟨ConcreteCNF.Literal.neg (0 : Fin 1), by simp,
      by simp [ConcreteCNF.Literal.eval, oneVarFalseAssignment]⟩

/-- The true assignment satisfies the tautological one-variable CNF. -/
theorem oneVarTautologyCNF_satisfied_true :
    ConcreteCNF.IsSatFormula oneVarTautologyCNF oneVarTrueAssignment := by
  intro clause hclause
  rw [oneVarTautologyCNF] at hclause
  simp only [List.mem_singleton] at hclause
  rw [hclause]
  exact
    ⟨ConcreteCNF.Literal.pos (0 : Fin 1), by simp,
      by simp [ConcreteCNF.Literal.eval, oneVarTrueAssignment]⟩

/-- The two satisfying assignments have different message readouts. -/
theorem oneVarReadout_false_ne_true :
    oneVarReadout oneVarFalseAssignment ≠ oneVarReadout oneVarTrueAssignment := by
  intro h
  cases h

/-- The concrete CNF has two satisfying assignments with different readouts. -/
theorem oneVarTautologyCNF_has_distinct_satisfying_readouts :
    ∃ σ₁ σ₂ : ConcreteCNF.Assignment (Fin 1),
      ConcreteCNF.IsSatFormula oneVarTautologyCNF σ₁ ∧
      ConcreteCNF.IsSatFormula oneVarTautologyCNF σ₂ ∧
      oneVarReadout σ₁ ≠ oneVarReadout σ₂ := by
  exact
    ⟨oneVarFalseAssignment, oneVarTrueAssignment,
      oneVarTautologyCNF_satisfied_false,
      oneVarTautologyCNF_satisfied_true,
      oneVarReadout_false_ne_true⟩

/-- At the concrete CNF layer, any message correct for all valid SAT-search
outputs forces single-message readout constancy across all satisfying
assignments. -/
theorem cnf_singleMessageReadout_of_exists_correctForAllSatSearchOutputs
    {Var : Type u} {Message : Type v}
    {formula : ConcreteCNF.Formula Var}
    {readout : ConcreteCNF.Assignment Var → Message}
    (h :
      ∃ msg : Message,
        CorrectForAllSatSearchOutputs
          (ConcreteCNF.IsSatFormula formula) readout msg) :
    SingleMessageReadout (ConcreteCNF.IsSatFormula formula) readout := by
  rcases h with ⟨_msg, hmsg⟩
  exact singleMessageReadout_of_correctForAllSatSearchOutputs hmsg

/-- Conversely, for a satisfiable concrete CNF, readout constancy is sufficient
to produce a message correct for all valid SAT-search outputs.  This is the
minimal positive repair theorem the manuscript must instantiate for its actual
CNF realization. -/
theorem cnf_exists_correctForAllSatSearchOutputs_of_singleMessageReadout
    {Var : Type u} {Message : Type v}
    {formula : ConcreteCNF.Formula Var}
    {readout : ConcreteCNF.Assignment Var → Message}
    {σ₀ : ConcreteCNF.Assignment Var}
    (hσ₀ : ConcreteCNF.IsSatFormula formula σ₀)
    (hconst : SingleMessageReadout
      (ConcreteCNF.IsSatFormula formula) readout) :
    ∃ msg : Message,
      CorrectForAllSatSearchOutputs
        (ConcreteCNF.IsSatFormula formula) readout msg := by
  exact
    (exists_correctForAllSatSearchOutputs_iff_singleMessageReadout_of_witness
      (sat := ConcreteCNF.IsSatFormula formula) (readout := readout)
      (w₀ := σ₀) hσ₀).mpr hconst

/-- For satisfiable concrete CNFs, the arbitrary-output SAT-search repair
exists exactly when all satisfying assignments have the same readout. -/
theorem cnf_exists_correctForAllSatSearchOutputs_iff_singleMessageReadout_of_satisfying_assignment
    {Var : Type u} {Message : Type v}
    {formula : ConcreteCNF.Formula Var}
    {readout : ConcreteCNF.Assignment Var → Message}
    {σ₀ : ConcreteCNF.Assignment Var}
    (hσ₀ : ConcreteCNF.IsSatFormula formula σ₀) :
    (∃ msg : Message,
      CorrectForAllSatSearchOutputs
        (ConcreteCNF.IsSatFormula formula) readout msg) ↔
      SingleMessageReadout (ConcreteCNF.IsSatFormula formula) readout := by
  exact
    exists_correctForAllSatSearchOutputs_iff_singleMessageReadout_of_witness
      (sat := ConcreteCNF.IsSatFormula formula) (readout := readout)
      (w₀ := σ₀) hσ₀

/-- Concrete CNF satisfiability alone does not force single-message readout
constancy. -/
theorem oneVarTautologyCNF_not_singleMessageReadout :
    ¬ SingleMessageReadout
      (ConcreteCNF.IsSatFormula oneVarTautologyCNF) oneVarReadout := by
  exact
    not_singleMessageReadout_of_distinct_satisfying_readouts
      (sat := ConcreteCNF.IsSatFormula oneVarTautologyCNF)
      (readout := oneVarReadout)
      (w₁ := oneVarFalseAssignment) (w₂ := oneVarTrueAssignment)
      oneVarTautologyCNF_satisfied_false
      oneVarTautologyCNF_satisfied_true
      oneVarReadout_false_ne_true

/-- No fixed message is correct for all satisfying assignments of the concrete
one-variable CNF under the readout that exposes the free variable. -/
theorem oneVarTautologyCNF_not_exists_fixedMessageReadout :
    ¬ ∃ msg : Bool,
      FixedMessageReadout
        (ConcreteCNF.IsSatFormula oneVarTautologyCNF) oneVarReadout msg := by
  exact
    not_exists_fixedMessageReadout_of_distinct_satisfying_readouts
      (sat := ConcreteCNF.IsSatFormula oneVarTautologyCNF)
      (readout := oneVarReadout)
      (w₁ := oneVarFalseAssignment) (w₂ := oneVarTrueAssignment)
      oneVarTautologyCNF_satisfied_false
      oneVarTautologyCNF_satisfied_true
      oneVarReadout_false_ne_true

/-- Therefore no decoder message is correct for all valid SAT-search outputs
on the concrete one-variable CNF. -/
theorem oneVarTautologyCNF_not_exists_correctForAllSatSearchOutputs :
    ¬ ∃ msg : Bool,
      CorrectForAllSatSearchOutputs
        (ConcreteCNF.IsSatFormula oneVarTautologyCNF) oneVarReadout msg := by
  exact
    not_exists_correctForAllSatSearchOutputs_of_distinct_satisfying_readouts
      (sat := ConcreteCNF.IsSatFormula oneVarTautologyCNF)
      (readout := oneVarReadout)
      (w₁ := oneVarFalseAssignment) (w₂ := oneVarTrueAssignment)
      oneVarTautologyCNF_satisfied_false
      oneVarTautologyCNF_satisfied_true
      oneVarReadout_false_ne_true

/-- A favorable selected SAT witness can still certify either message.  This is
the concrete CNF version of the gap between selected-output and arbitrary-output
SAT-search contracts. -/
theorem oneVarTautologyCNF_correctForSomeSatSearchOutput_false_and_true :
    CorrectForSomeSatSearchOutput
        (ConcreteCNF.IsSatFormula oneVarTautologyCNF) oneVarReadout false ∧
      CorrectForSomeSatSearchOutput
        (ConcreteCNF.IsSatFormula oneVarTautologyCNF) oneVarReadout true := by
  exact
    ⟨⟨⟨oneVarFalseAssignment, oneVarTautologyCNF_satisfied_false⟩, rfl⟩,
      ⟨⟨oneVarTrueAssignment, oneVarTautologyCNF_satisfied_true⟩, rfl⟩⟩

/-- The concrete CNF has selected-output correctness but no arbitrary-output
correctness. -/
theorem oneVarTautologyCNF_correctForSomeSatSearchOutput_not_correctForAll :
    (∃ msg : Bool,
      CorrectForSomeSatSearchOutput
        (ConcreteCNF.IsSatFormula oneVarTautologyCNF) oneVarReadout msg) ∧
      ¬ ∃ msg : Bool,
        CorrectForAllSatSearchOutputs
          (ConcreteCNF.IsSatFormula oneVarTautologyCNF) oneVarReadout msg := by
  exact
    exists_correctForSomeSatSearchOutput_and_not_exists_correctForAll_of_distinct_satisfying_readouts
      (sat := ConcreteCNF.IsSatFormula oneVarTautologyCNF)
      (readout := oneVarReadout)
      (w₁ := oneVarFalseAssignment) (w₂ := oneVarTrueAssignment)
      oneVarTautologyCNF_satisfied_false
      oneVarTautologyCNF_satisfied_true
      oneVarReadout_false_ne_true

end Mettapedia.Computability.PNP
