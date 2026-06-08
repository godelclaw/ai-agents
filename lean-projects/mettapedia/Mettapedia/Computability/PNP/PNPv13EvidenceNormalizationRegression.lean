import Mettapedia.Computability.PNP.PNPv13EvidenceNormalization

/-!
# Regression checks for the PNP v13 evidence-normalization boundary
-/

namespace Mettapedia.Computability.PNP.PNPv13EvidenceNormalizationRegression

open Mettapedia.Computability.PNP

universe u

theorem normalization_iff_no_residual_regression
    {Atom : Type u} (S : V13EvidenceNormalizationSurface Atom) :
    S.NormalizesNonNeutral ↔ ¬ S.HasResidualAtom := by
  exact V13EvidenceNormalizationSurface.normalizesNonNeutral_iff_not_hasResidualAtom S

theorem no_normalization_iff_residual_regression
    {Atom : Type u} (S : V13EvidenceNormalizationSurface Atom) :
    ¬ S.NormalizesNonNeutral ↔ S.HasResidualAtom := by
  exact V13EvidenceNormalizationSurface.not_normalizesNonNeutral_iff_hasResidualAtom S

theorem positive_cover_iff_no_positive_residual_regression
    {Atom : Type u} (S : V13EvidenceNormalizationSurface Atom)
    (score : Atom → Nat) :
    S.PositiveAtomsCovered score ↔ ¬ S.PositiveResidualScore score := by
  exact V13EvidenceNormalizationSurface.positiveAtomsCovered_iff_not_positiveResidualScore
    S score

theorem full_normalization_implies_positive_cover_regression
    {Atom : Type u} {S : V13EvidenceNormalizationSurface Atom}
    {score : Atom → Nat}
    (hnorm : S.NormalizesNonNeutral) :
    S.PositiveAtomsCovered score := by
  exact V13EvidenceNormalizationSurface.positiveAtomsCovered_of_normalizesNonNeutral
    hnorm

theorem toy_evidence_surface_has_residual_atom_regression :
    v13ToyEvidenceSurface.ResidualAtom .residual := by
  exact v13ToyEvidenceSurface_residualAtom

theorem toy_evidence_surface_not_normalized_regression :
    ¬ v13ToyEvidenceSurface.NormalizesNonNeutral := by
  exact v13ToyEvidenceSurface_not_normalizesNonNeutral

theorem toy_evidence_surface_positive_residual_score_regression :
    v13ToyEvidenceSurface.PositiveResidualScore v13ToyEvidenceScore := by
  exact v13ToyEvidenceSurface_positiveResidualScore

theorem toy_evidence_surface_not_positive_atoms_covered_regression :
    ¬ v13ToyEvidenceSurface.PositiveAtomsCovered v13ToyEvidenceScore := by
  exact v13ToyEvidenceSurface_not_positiveAtomsCovered

end Mettapedia.Computability.PNP.PNPv13EvidenceNormalizationRegression
