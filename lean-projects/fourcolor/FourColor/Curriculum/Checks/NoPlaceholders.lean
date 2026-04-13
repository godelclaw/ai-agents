/-!
# Curriculum Placeholder Policy

This module records the policy for the production curriculum path:

- `FourColor/Curriculum/Actual`
- `FourColor/Curriculum/Checks`

These paths must not contain unresolved placeholder keywords.
The policy is enforced by:

`scripts/check-curriculum-no-placeholders.sh`
-/

namespace FourColor.Curriculum.Checks

/-- Marker definition documenting that placeholder-free checks are active. -/
def placeholderGuardActive : Prop := True

theorem placeholderGuardActive_true : placeholderGuardActive := trivial

end FourColor.Curriculum.Checks
