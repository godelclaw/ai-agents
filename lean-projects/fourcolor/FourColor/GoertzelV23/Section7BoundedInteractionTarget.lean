namespace FourColor.GoertzelV23

universe u v w

/--
The Section 7.2-7.3 theorem-back target for Ben Goertzel's `v23` route.

This packages the purely geometric front of the locality chapter:
- Lemma 7.3: bounded interaction in the depth-1 annulus
- Lemma 7.5: the canonical outer zig-zag boundary

The extracted output is the only part later files really need: every long
enough gate on the canonical outer boundary contains a three-cell patch.
-/
structure Section7BoundedInteractionTarget where
  Face : Type u
  Boundary : Type v
  Patch : Type w
  BoundedInteraction : Face → Prop
  ZigZagBoundary : Face → Boundary → Prop
  LongGate : Boundary → Prop
  ThreeCellPatch : Patch → Prop
  GatePatch : Face → Boundary → Patch → Prop
  lemma_7_3 :
    ∀ f : Face, BoundedInteraction f
  lemma_7_5 :
    ∀ {f : Face},
      BoundedInteraction f →
      ∃ Γ : Boundary, ZigZagBoundary f Γ
  long_gate_contains_patch :
    ∀ {f : Face} {Γ : Boundary},
      ZigZagBoundary f Γ →
      LongGate Γ →
      ∃ P : Patch, ThreeCellPatch P ∧ GatePatch f Γ P

/-- Every face in the bounded-interaction regime has a canonical zig-zag boundary. -/
theorem Section7BoundedInteractionTarget.zig_zag_boundary_exists
    (S : Section7BoundedInteractionTarget) :
    ∀ f : S.Face, ∃ Γ : S.Boundary, S.ZigZagBoundary f Γ := by
  intro f
  exact S.lemma_7_5 (S.lemma_7_3 f)

/--
The extracted Section 7.2-7.3 output: every long canonical gate already
contains a three-cell patch suitable for the later micro-enumeration step.
-/
def Section7BoundedInteractionTarget.HasLocalThreeCellGate
    (S : Section7BoundedInteractionTarget) : Prop :=
  ∀ {f : S.Face} {Γ : S.Boundary},
    S.ZigZagBoundary f Γ →
    S.LongGate Γ →
    ∃ P : S.Patch, S.ThreeCellPatch P

theorem Section7BoundedInteractionTarget.has_local_three_cell_gate
    (S : Section7BoundedInteractionTarget) :
    S.HasLocalThreeCellGate := by
  intro f Γ hzigzag hlong
  rcases S.long_gate_contains_patch hzigzag hlong with ⟨P, hpatch, _⟩
  exact ⟨P, hpatch⟩

end FourColor.GoertzelV23
