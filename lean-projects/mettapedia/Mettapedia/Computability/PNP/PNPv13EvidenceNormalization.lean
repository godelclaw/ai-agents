import Mettapedia.Computability.PNP.PNPv13CruxLedger

/-!
# PNP v13 evidence-normalization boundary

The v13 crux ledger names a CD evidence-normalization obligation: every
target-relevant non-neutral trace leaf must be absorbed by either a safe buffer
or a hidden gauge.  This file isolates the exact finite logical boundary of
that obligation.  A normalization theorem is equivalent to the absence of a
residual target-relevant non-neutral atom, and the positive-score variant
pinpoints the remaining theorem needed if the manuscript tries to ignore
zero-score residuals.
-/

namespace Mettapedia.Computability.PNP

universe u

/-- Abstract surface for the v13 evidence-normalization audit.  The predicates
are intentionally semantic: an atom is either target-relevant, neutral, absorbed
by a safe buffer, absorbed by a hidden gauge, or residual. -/
structure V13EvidenceNormalizationSurface (Atom : Type u) where
  targetRelevant : Atom → Prop
  neutral : Atom → Prop
  safeBuffer : Atom → Prop
  hiddenGauge : Atom → Prop

namespace V13EvidenceNormalizationSurface

/-- The manuscript-shaped normalization obligation: every target-relevant
non-neutral atom is accounted for by a safe-buffer or hidden-gauge class. -/
def NormalizesNonNeutral (S : V13EvidenceNormalizationSurface Atom) : Prop :=
  ∀ a, S.targetRelevant a → ¬ S.neutral a → S.safeBuffer a ∨ S.hiddenGauge a

/-- A residual atom is exactly a target-relevant non-neutral atom not absorbed
by either named normalization class. -/
def ResidualAtom (S : V13EvidenceNormalizationSurface Atom) (a : Atom) : Prop :=
  S.targetRelevant a ∧ ¬ S.neutral a ∧ ¬ S.safeBuffer a ∧ ¬ S.hiddenGauge a

/-- The existence form of the residual obstruction. -/
def HasResidualAtom (S : V13EvidenceNormalizationSurface Atom) : Prop :=
  ∃ a, S.ResidualAtom a

/-- One residual atom refutes the normalization theorem. -/
theorem not_normalizesNonNeutral_of_residualAtom
    {S : V13EvidenceNormalizationSurface Atom} {a : Atom}
    (h : S.ResidualAtom a) :
    ¬ S.NormalizesNonNeutral := by
  intro hnorm
  rcases h with ⟨htarget, hnonneutral, hsafe, hgauge⟩
  rcases hnorm a htarget hnonneutral with hsafe' | hgauge'
  · exact hsafe hsafe'
  · exact hgauge hgauge'

/-- A successful normalization theorem rules out every residual atom. -/
theorem not_hasResidualAtom_of_normalizesNonNeutral
    {S : V13EvidenceNormalizationSurface Atom}
    (hnorm : S.NormalizesNonNeutral) :
    ¬ S.HasResidualAtom := by
  intro hres
  rcases hres with ⟨a, ha⟩
  exact not_normalizesNonNeutral_of_residualAtom ha hnorm

/-- Failure of normalization exposes a residual atom. -/
theorem exists_residualAtom_of_not_normalizesNonNeutral
    {S : V13EvidenceNormalizationSurface Atom}
    (hfail : ¬ S.NormalizesNonNeutral) :
    S.HasResidualAtom := by
  classical
  by_cases hres : S.HasResidualAtom
  · exact hres
  · exfalso
    apply hfail
    intro a htarget hnonneutral
    by_cases hcover : S.safeBuffer a ∨ S.hiddenGauge a
    · exact hcover
    · exfalso
      exact hres ⟨a, htarget, hnonneutral, hcover ∘ Or.inl, hcover ∘ Or.inr⟩

/-- Evidence normalization is exactly absence of residual atoms. -/
theorem normalizesNonNeutral_iff_not_hasResidualAtom
    (S : V13EvidenceNormalizationSurface Atom) :
    S.NormalizesNonNeutral ↔ ¬ S.HasResidualAtom := by
  constructor
  · exact not_hasResidualAtom_of_normalizesNonNeutral
  · intro hno a htarget hnonneutral
    classical
    by_cases hcover : S.safeBuffer a ∨ S.hiddenGauge a
    · exact hcover
    · exfalso
      exact hno ⟨a, htarget, hnonneutral, hcover ∘ Or.inl, hcover ∘ Or.inr⟩

/-- The contrapositive residual obstruction form. -/
theorem not_normalizesNonNeutral_iff_hasResidualAtom
    (S : V13EvidenceNormalizationSurface Atom) :
    ¬ S.NormalizesNonNeutral ↔ S.HasResidualAtom := by
  constructor
  · exact exists_residualAtom_of_not_normalizesNonNeutral
  · intro hres hnorm
    exact not_hasResidualAtom_of_normalizesNonNeutral hnorm hres

/-- Positive-score normalization only asks the safe/gauge cover on residual
atoms that could carry positive message advantage. -/
def PositiveAtomsCovered (S : V13EvidenceNormalizationSurface Atom)
    (score : Atom → Nat) : Prop :=
  ∀ a, S.targetRelevant a → ¬ S.neutral a → 0 < score a →
    S.safeBuffer a ∨ S.hiddenGauge a

/-- Positive residual score is the exact obstruction to positive-score
normalization. -/
def PositiveResidualScore (S : V13EvidenceNormalizationSurface Atom)
    (score : Atom → Nat) : Prop :=
  ∃ a, S.ResidualAtom a ∧ 0 < score a

/-- Positive-score normalization is equivalent to absence of positive residual
score. -/
theorem positiveAtomsCovered_iff_not_positiveResidualScore
    (S : V13EvidenceNormalizationSurface Atom) (score : Atom → Nat) :
    S.PositiveAtomsCovered score ↔ ¬ S.PositiveResidualScore score := by
  constructor
  · intro hcover hres
    rcases hres with ⟨a, hresidual, hpos⟩
    rcases hresidual with ⟨htarget, hnonneutral, hsafe, hgauge⟩
    rcases hcover a htarget hnonneutral hpos with hsafe' | hgauge'
    · exact hsafe hsafe'
    · exact hgauge hgauge'
  · intro hno a htarget hnonneutral hpos
    classical
    by_cases hcover : S.safeBuffer a ∨ S.hiddenGauge a
    · exact hcover
    · exfalso
      exact hno ⟨a, ⟨htarget, hnonneutral, hcover ∘ Or.inl, hcover ∘ Or.inr⟩, hpos⟩

/-- A positive residual score refutes positive-score normalization. -/
theorem not_positiveAtomsCovered_of_positiveResidualScore
    {S : V13EvidenceNormalizationSurface Atom} {score : Atom → Nat}
    (hres : S.PositiveResidualScore score) :
    ¬ S.PositiveAtomsCovered score := by
  intro hcover
  exact (positiveAtomsCovered_iff_not_positiveResidualScore S score).1 hcover hres

/-- Failure of positive-score normalization exposes a positive residual atom. -/
theorem positiveResidualScore_of_not_positiveAtomsCovered
    {S : V13EvidenceNormalizationSurface Atom} {score : Atom → Nat}
    (hfail : ¬ S.PositiveAtomsCovered score) :
    S.PositiveResidualScore score := by
  classical
  by_cases hres : S.PositiveResidualScore score
  · exact hres
  · exfalso
    exact hfail ((positiveAtomsCovered_iff_not_positiveResidualScore S score).2 hres)

/-- Full non-neutral normalization implies the positive-score version for any
score. -/
theorem positiveAtomsCovered_of_normalizesNonNeutral
    {S : V13EvidenceNormalizationSurface Atom} {score : Atom → Nat}
    (hnorm : S.NormalizesNonNeutral) :
    S.PositiveAtomsCovered score := by
  intro a htarget hnonneutral _hpos
  exact hnorm a htarget hnonneutral

end V13EvidenceNormalizationSurface

/-- Three-atom model separating safe buffers, hidden gauges, and a genuine
residual class. -/
inductive V13ToyEvidenceAtom where
  | safe
  | gauge
  | residual
  deriving DecidableEq, Repr

/-- A toy evidence surface with one residual target-relevant non-neutral atom. -/
def v13ToyEvidenceSurface :
    V13EvidenceNormalizationSurface V13ToyEvidenceAtom where
  targetRelevant := fun _ => True
  neutral := fun _ => False
  safeBuffer
    | .safe => True
    | _ => False
  hiddenGauge
    | .gauge => True
    | _ => False

/-- Only the residual atom carries positive score in the toy surface. -/
def v13ToyEvidenceScore : V13ToyEvidenceAtom → Nat
  | .residual => 1
  | _ => 0

/-- The toy residual atom is target-relevant, non-neutral, and uncovered. -/
theorem v13ToyEvidenceSurface_residualAtom :
    v13ToyEvidenceSurface.ResidualAtom .residual := by
  simp [V13EvidenceNormalizationSurface.ResidualAtom, v13ToyEvidenceSurface]

/-- The toy residual atom refutes full evidence normalization. -/
theorem v13ToyEvidenceSurface_not_normalizesNonNeutral :
    ¬ v13ToyEvidenceSurface.NormalizesNonNeutral := by
  exact
    V13EvidenceNormalizationSurface.not_normalizesNonNeutral_of_residualAtom
      v13ToyEvidenceSurface_residualAtom

/-- The toy residual atom has positive score. -/
theorem v13ToyEvidenceSurface_positiveResidualScore :
    v13ToyEvidenceSurface.PositiveResidualScore v13ToyEvidenceScore := by
  exact
    ⟨.residual, v13ToyEvidenceSurface_residualAtom, Nat.zero_lt_succ 0⟩

/-- Positive-score normalization fails in the toy surface. -/
theorem v13ToyEvidenceSurface_not_positiveAtomsCovered :
    ¬ v13ToyEvidenceSurface.PositiveAtomsCovered v13ToyEvidenceScore := by
  exact
    V13EvidenceNormalizationSurface.not_positiveAtomsCovered_of_positiveResidualScore
      v13ToyEvidenceSurface_positiveResidualScore

end Mettapedia.Computability.PNP
