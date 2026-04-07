import FourColor.GoertzelV23.Section7BoundedInteractionTarget

namespace FourColor.GoertzelV23

/--
The Section 7.3 theorem-back target for Ben Goertzel's `v23` route.

This isolates Lemma 7.6: once an anchored Kempe cycle genuinely escapes the
radius-1 collar, a minimal long gate reduces to a three-cell patch.
-/
structure Section7GateReductionTarget where
  interaction : Section7BoundedInteractionTarget
  EscapingAnchoredCycle : interaction.Face → Prop
  MinimalGate : interaction.Face → interaction.Boundary → Prop
  lemma_7_6 :
    ∀ {f : interaction.Face} {Γ : interaction.Boundary},
      EscapingAnchoredCycle f →
      MinimalGate f Γ →
      interaction.LongGate Γ →
      ∃ P : interaction.Patch,
        interaction.ThreeCellPatch P ∧ interaction.GatePatch f Γ P

/-- Every escaping anchored cycle still sits on a canonical zig-zag gate. -/
theorem Section7GateReductionTarget.escaping_cycle_has_zig_zag_gate
    (S : Section7GateReductionTarget) :
    ∀ {f : S.interaction.Face},
      S.EscapingAnchoredCycle f →
      ∃ Γ : S.interaction.Boundary, S.interaction.ZigZagBoundary f Γ := by
  intro f _
  exact S.interaction.zig_zag_boundary_exists f

/--
Lemma 7.6 in extracted form: a minimal long gate on an escaping anchored cycle
reduces to a concrete three-cell patch.
-/
theorem Section7GateReductionTarget.minimal_gate_reduces_to_three_cell
    (S : Section7GateReductionTarget) :
    ∀ {f : S.interaction.Face} {Γ : S.interaction.Boundary},
      S.EscapingAnchoredCycle f →
      S.MinimalGate f Γ →
      S.interaction.LongGate Γ →
      ∃ P : S.interaction.Patch, S.interaction.ThreeCellPatch P := by
  intro f Γ hescape hminimal hlong
  rcases S.lemma_7_6 hescape hminimal hlong with ⟨P, hpatch, _⟩
  exact ⟨P, hpatch⟩

end FourColor.GoertzelV23
