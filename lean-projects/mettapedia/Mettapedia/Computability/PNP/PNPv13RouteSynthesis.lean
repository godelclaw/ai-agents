import Mettapedia.Computability.PNP.PNPv13SwitchingInstantiation

/-!
# PNP v13 switching route synthesis

This file packages the current fixed-field switching obstruction as a decision
surface.  It deliberately does not assert that the manuscript construction
falls into any particular case.  Instead it names the exact hypotheses under
which the route is blocked and the exact repair obligations left if those
hypotheses are not supplied.
-/

namespace Mettapedia.Computability.PNP

universe u

/-- A switched list contains a repeated positive-mass pivot when, after some
prefix, it repeats the same switched step and the first occurrence leaves a
nonempty accumulated success history.  This is the abstract atom-ledger
assumption under which the repeated-event obstruction applies. -/
def V13RepeatedPositivePivotFrom {Ω : Type u} [Fintype Ω]
    (hist : List (FiniteEvent Ω)) (steps : List (V13SwitchedStep Ω)) : Prop :=
  ∃ pre step suffix,
    steps = pre ++ step :: step :: suffix ∧
      0 < finiteHistoryCount Ω
        ((hist ++ v13SuccessEvents pre) ++ [step.successEvent])

/-- The complement of the repeated-positive-pivot audit target.  A repair that
does not fall under the repeated-event blocker must prove this proposition for
the actual switched list. -/
def V13NoRepeatedPositivePivotFrom {Ω : Type u} [Fintype Ω]
    (hist : List (FiniteEvent Ω)) (steps : List (V13SwitchedStep Ω)) : Prop :=
  ¬ V13RepeatedPositivePivotFrom hist steps

/-- If a positive-mass repeated switched pivot occurs after an explicit prefix,
the v13 abstract atom-ledger instantiation is blocked at the second copy. -/
theorem not_v13SwitchingInstantiatedFrom_repeatedPositivePivot_at
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)}
    {pre : List (V13SwitchedStep Ω)} {step : V13SwitchedStep Ω}
    {suffix : List (V13SwitchedStep Ω)}
    (hpos :
      0 < finiteHistoryCount Ω
        ((hist ++ v13SuccessEvents pre) ++ [step.successEvent])) :
    ¬ V13SwitchingInstantiatedFrom hist (pre ++ step :: step :: suffix) := by
  induction pre generalizing hist with
  | nil =>
      have hpos' :
          0 < finiteHistoryCount Ω (hist ++ [step.successEvent]) := by
        simpa [v13SuccessEvents] using hpos
      have hfail :
          ¬ PrefixHalfStep (hist ++ [step.successEvent])
            step.successEvent :=
        not_prefixHalfStep_repeated_of_positive hpos'
      intro h
      exact not_v13PrefixInstantiated_of_not_prefixHalfStep hfail h.2.1
  | cons head tail ih =>
      intro h
      have hpos' :
          0 < finiteHistoryCount Ω
            (((hist ++ [head.successEvent]) ++ v13SuccessEvents tail) ++
              [step.successEvent]) := by
        simpa [v13SuccessEvents, List.append_assoc] using hpos
      exact ih (hist := hist ++ [head.successEvent]) hpos' h.2

/-- Route-class blocker: any abstract v13 switching list with a repeated
positive-mass pivot cannot be instantiated. -/
theorem not_v13SwitchingInstantiatedFrom_of_repeatedPositivePivot
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {steps : List (V13SwitchedStep Ω)}
    (hrep : V13RepeatedPositivePivotFrom hist steps) :
    ¬ V13SwitchingInstantiatedFrom hist steps := by
  rcases hrep with ⟨pre, step, suffix, hsteps, hpos⟩
  rw [hsteps]
  exact not_v13SwitchingInstantiatedFrom_repeatedPositivePivot_at
    (hist := hist) (pre := pre) (step := step) (suffix := suffix) hpos

/-- Therefore any successful abstract v13 atom-ledger instantiation must prove
that the repeated-positive-pivot audit target is absent. -/
theorem v13NoRepeatedPositivePivotFrom_of_v13SwitchingInstantiatedFrom
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {steps : List (V13SwitchedStep Ω)}
    (h : V13SwitchingInstantiatedFrom hist steps) :
    V13NoRepeatedPositivePivotFrom hist steps := by
  intro hrep
  exact not_v13SwitchingInstantiatedFrom_of_repeatedPositivePivot hrep h

/-- A fixed-field switched list contains a repeated positive-mass pivot when it
reuses the same fielded step after the first copy has left positive accumulated
success mass.  This is the fixed-field/repeated-event route-class assumption. -/
def V13RepeatedPositiveFieldedPivotFrom {Ω : Type u} [Fintype Ω]
    (hist : List (FiniteEvent Ω)) (items : List (V13FieldedStep Ω)) : Prop :=
  ∃ pre item suffix,
    items = pre ++ item :: item :: suffix ∧
      0 < finiteHistoryCount Ω
        ((hist ++ v13FieldedSuccessEvents pre) ++ [item.step.successEvent])

/-- The complement of the fixed-field repeated-positive-pivot audit target.
This is the first repair theorem needed if the manuscript construction claims
to avoid literal repeated positive-mass fielded pivots. -/
def V13NoRepeatedPositiveFieldedPivotFrom {Ω : Type u} [Fintype Ω]
    (hist : List (FiniteEvent Ω)) (items : List (V13FieldedStep Ω)) : Prop :=
  ¬ V13RepeatedPositiveFieldedPivotFrom hist items

/-- If a positive-mass repeated fielded pivot occurs after an explicit prefix,
no fixed-field certificate can instantiate the whole list. -/
theorem not_v13FieldSwitchingInstantiatedFrom_repeatedPositiveFieldedPivot_at
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)}
    {pre : List (V13FieldedStep Ω)} {item : V13FieldedStep Ω}
    {suffix : List (V13FieldedStep Ω)}
    (hpos :
      0 < finiteHistoryCount Ω
        ((hist ++ v13FieldedSuccessEvents pre) ++ [item.step.successEvent])) :
    ¬ V13FieldSwitchingInstantiatedFrom hist
      (pre ++ item :: item :: suffix) := by
  induction pre generalizing hist with
  | nil =>
      have hpos' :
          0 < finiteHistoryCount Ω (hist ++ [item.step.successEvent]) := by
        simpa [v13FieldedSuccessEvents] using hpos
      have hfailHalf :
          ¬ PrefixHalfStep (hist ++ [item.step.successEvent])
            item.step.successEvent :=
        not_prefixHalfStep_repeated_of_positive hpos'
      have hfailCert :
          ¬ V13FieldPrefixInstantiation item.field
            (hist ++ [item.step.successEvent]) item.step := by
        intro cert
        exact hfailHalf (prefixHalfStep_of_v13FieldPrefixInstantiation cert)
      intro h
      exact hfailCert h.2.1
  | cons head tail ih =>
      intro h
      have hpos' :
          0 < finiteHistoryCount Ω
            (((hist ++ [head.step.successEvent]) ++
                v13FieldedSuccessEvents tail) ++ [item.step.successEvent]) := by
        simpa [v13FieldedSuccessEvents, List.append_assoc] using hpos
      exact ih (hist := hist ++ [head.step.successEvent]) hpos' h.2

/-- Route-class blocker: any fixed-field v13 switching list with a repeated
positive-mass fielded pivot cannot be instantiated. -/
theorem not_v13FieldSwitchingInstantiatedFrom_of_repeatedPositiveFieldedPivot
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hrep : V13RepeatedPositiveFieldedPivotFrom hist items) :
    ¬ V13FieldSwitchingInstantiatedFrom hist items := by
  rcases hrep with ⟨pre, item, suffix, hitems, hpos⟩
  rw [hitems]
  exact
    not_v13FieldSwitchingInstantiatedFrom_repeatedPositiveFieldedPivot_at
      (hist := hist) (pre := pre) (item := item) (suffix := suffix) hpos

/-- The same repeated-positive-pivot blocker rules out the operational
same-cell matching formulation. -/
theorem not_v13FieldSwitchingFailureMatchingFrom_of_repeatedPositiveFieldedPivot
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hrep : V13RepeatedPositiveFieldedPivotFrom hist items) :
    ¬ V13FieldSwitchingFailureMatchingFrom hist items := by
  intro hmatch
  exact
    not_v13FieldSwitchingInstantiatedFrom_of_repeatedPositiveFieldedPivot hrep
      (v13FieldSwitchingInstantiatedFrom_iff_failureMatchingFrom.mpr hmatch)

/-- Synthesis form: a repeated positive-mass fielded pivot blocks both the
fixed-field certificate route and the equivalent same-cell matching route. -/
theorem v13RepeatedPositiveFieldedPivot_blocks_fixedFieldRoute
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hrep : V13RepeatedPositiveFieldedPivotFrom hist items) :
    (¬ V13FieldSwitchingInstantiatedFrom hist items) ∧
      ¬ V13FieldSwitchingFailureMatchingFrom hist items := by
  exact
    ⟨not_v13FieldSwitchingInstantiatedFrom_of_repeatedPositiveFieldedPivot hrep,
      not_v13FieldSwitchingFailureMatchingFrom_of_repeatedPositiveFieldedPivot
        hrep⟩

/-- Therefore any successful fixed-field instantiation must prove that the
repeated-positive-pivot audit target is absent. -/
theorem v13NoRepeatedPositiveFieldedPivotFrom_of_v13FieldSwitchingInstantiatedFrom
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (h : V13FieldSwitchingInstantiatedFrom hist items) :
    V13NoRepeatedPositiveFieldedPivotFrom hist items := by
  intro hrep
  exact not_v13FieldSwitchingInstantiatedFrom_of_repeatedPositiveFieldedPivot
    hrep h

/-- The same no-repeated-pivot obligation follows from a proof of the
equivalent recursive same-cell matching theorem. -/
theorem v13NoRepeatedPositiveFieldedPivotFrom_of_failureMatchingFrom
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hmatch : V13FieldSwitchingFailureMatchingFrom hist items) :
    V13NoRepeatedPositiveFieldedPivotFrom hist items := by
  exact
    v13NoRepeatedPositiveFieldedPivotFrom_of_v13FieldSwitchingInstantiatedFrom
      (v13FieldSwitchingInstantiatedFrom_iff_failureMatchingFrom.mpr hmatch)

/-- A concrete bad supplied cell at a fielded position: after the preceding
fielded prefix has been imposed, one cell has strictly fewer next-failure
points than next-success points.  This is the bad-cell localization audit
target for the fixed-field route. -/
def V13FieldedBadCellFrom {Ω : Type u} [Fintype Ω]
    (hist : List (FiniteEvent Ω)) (items : List (V13FieldedStep Ω)) : Prop :=
  ∃ pre item suffix,
    items = pre ++ item :: suffix ∧
      ∃ cell : item.field.Cell,
        v13ConcreteFailureCount (Ω := Ω)
            (hist ++ v13FieldedSuccessEvents pre)
            item.step item.field.cellOf cell <
          v13ConcreteSuccessCount (Ω := Ω)
            (hist ++ v13FieldedSuccessEvents pre)
            item.step item.field.cellOf cell

/-- The complement of the bad-cell audit target.  A fixed-field repair must
prove this by proving the stronger recursive same-cell matching theorem. -/
def V13NoFieldedBadCellFrom {Ω : Type u} [Fintype Ω]
    (hist : List (FiniteEvent Ω)) (items : List (V13FieldedStep Ω)) : Prop :=
  ¬ V13FieldedBadCellFrom hist items

/-- A concrete bad supplied cell blocks the whole fixed-field instantiation. -/
theorem not_v13FieldSwitchingInstantiatedFrom_of_fieldedBadCell
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hbad : V13FieldedBadCellFrom hist items) :
    ¬ V13FieldSwitchingInstantiatedFrom hist items := by
  rcases hbad with ⟨pre, item, suffix, hitems, cell, hcell⟩
  rw [hitems]
  exact
    not_v13FieldSwitchingInstantiatedFrom_append_cons_of_not_fieldPrefixInstantiation
      (hist := hist) (pre := pre) (item := item) (suffix := suffix)
      (not_v13FieldPrefixInstantiation_of_success_gt_failure cell hcell)

/-- A concrete bad supplied cell also blocks the equivalent operational
same-cell matching formulation. -/
theorem not_v13FieldSwitchingFailureMatchingFrom_of_fieldedBadCell
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hbad : V13FieldedBadCellFrom hist items) :
    ¬ V13FieldSwitchingFailureMatchingFrom hist items := by
  intro hmatch
  exact not_v13FieldSwitchingInstantiatedFrom_of_fieldedBadCell hbad
    (v13FieldSwitchingInstantiatedFrom_iff_failureMatchingFrom.mpr hmatch)

/-- Any successful fixed-field instantiation must avoid every localized bad
cell. -/
theorem v13NoFieldedBadCellFrom_of_v13FieldSwitchingInstantiatedFrom
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (h : V13FieldSwitchingInstantiatedFrom hist items) :
    V13NoFieldedBadCellFrom hist items := by
  intro hbad
  exact not_v13FieldSwitchingInstantiatedFrom_of_fieldedBadCell hbad h

/-- A proof of recursive same-cell matching is precisely the repair theorem
that rules out localized bad cells. -/
theorem v13NoFieldedBadCellFrom_of_failureMatchingFrom
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hmatch : V13FieldSwitchingFailureMatchingFrom hist items) :
    V13NoFieldedBadCellFrom hist items := by
  exact
    v13NoFieldedBadCellFrom_of_v13FieldSwitchingInstantiatedFrom
      (v13FieldSwitchingInstantiatedFrom_iff_failureMatchingFrom.mpr hmatch)

/-- Product-bound failure for a fixed-field list localizes to the bad-cell
audit target. -/
theorem v13FieldedBadCellFrom_of_product_bound_violation
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hbad :
      ¬ 2 ^ items.length *
          finiteHistoryCount Ω (hist ++ v13FieldedSuccessEvents items) ≤
        finiteHistoryCount Ω hist) :
    V13FieldedBadCellFrom hist items := by
  exact exists_bad_cell_at_append_cons_of_product_bound_violation hbad

/-- Full synthesis for the fixed-field product route: a product-bound
violation produces a concrete bad cell and therefore blocks both fixed-field
certificate and same-cell matching formulations. -/
theorem v13FieldedProductViolation_yields_badCell_and_blocks
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hbad :
      ¬ 2 ^ items.length *
          finiteHistoryCount Ω (hist ++ v13FieldedSuccessEvents items) ≤
        finiteHistoryCount Ω hist) :
    V13FieldedBadCellFrom hist items ∧
      (¬ V13FieldSwitchingInstantiatedFrom hist items) ∧
        ¬ V13FieldSwitchingFailureMatchingFrom hist items := by
  have hcell := v13FieldedBadCellFrom_of_product_bound_violation
    (hist := hist) (items := items) hbad
  exact
    ⟨hcell,
      not_v13FieldSwitchingInstantiatedFrom_of_fieldedBadCell hcell,
      not_v13FieldSwitchingFailureMatchingFrom_of_fieldedBadCell hcell⟩

/-- The positive repair obligations forced by a fixed-field proof: the actual
list must have no repeated positive-mass fielded pivot, no localized bad cell,
and it must satisfy the finite tower product bound. -/
theorem v13FieldedRouteObligations_of_v13FieldSwitchingInstantiatedFrom
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (h : V13FieldSwitchingInstantiatedFrom hist items) :
    V13NoRepeatedPositiveFieldedPivotFrom hist items ∧
      V13NoFieldedBadCellFrom hist items ∧
        2 ^ items.length *
            finiteHistoryCount Ω (hist ++ v13FieldedSuccessEvents items) ≤
          finiteHistoryCount Ω hist := by
  exact
    ⟨v13NoRepeatedPositiveFieldedPivotFrom_of_v13FieldSwitchingInstantiatedFrom h,
      v13NoFieldedBadCellFrom_of_v13FieldSwitchingInstantiatedFrom h,
      v13_product_bound_of_fieldInstantiatedFrom hist items h⟩

end Mettapedia.Computability.PNP
