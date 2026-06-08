import Mettapedia.Computability.PNP.PNPv13AppendixDPublicSyntaxDiscipline

/-!
# Regression tests for Appendix D public syntax discipline

These checks pin down the strengthened blocker: adding D.29--D.31 neutral
public syntax normalization to the bounded-local locked core still does not
imply Appendix D.8.
-/

namespace Mettapedia.Computability.PNP

theorem public_syntax_template_neutral_regression :
    ∃ n : Unit,
      ambiguousPublicSyntaxDisciplinedLocalCore.publicSyntax.normalize
        (AppendixDPublicPrimitive.template ()) = n :=
  ambiguousPublicSyntaxDisciplined_template_neutral

theorem public_syntax_surface_neutral_regression :
    ∃ n : Unit,
      ambiguousPublicSyntaxDisciplinedLocalCore.publicSyntax.normalize
        (AppendixDPublicPrimitive.surface ()) = n :=
  ambiguousPublicSyntaxDisciplined_surface_neutral

theorem public_syntax_countermodel_satisfies_D7_regression :
    ambiguousPublicSyntaxDisciplinedLocalCore.toAppendixDLockedCore.LockSatisfiable :=
  ambiguousPublicSyntaxDisciplined_lockSatisfiable

theorem public_syntax_countermodel_read_deterministic_regression :
    ambiguousPublicSyntaxDisciplinedLocalCore.toAppendixDLockedCore.ReadDeterministic :=
  ambiguousPublicSyntaxDisciplined_readDeterministic

theorem public_syntax_countermodel_not_D8_regression :
    ¬ AppendixDLockedCore.LockedMessageRigidity
        ambiguousPublicSyntaxDisciplinedLocalCore.toAppendixDLockedCore :=
  ambiguousPublicSyntaxDisciplined_not_lockedMessageRigidity

end Mettapedia.Computability.PNP
