import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mettapedia.Computability.PNP.FiniteSwitchingAdmissibility

/-!
# PNP v13 switching instantiation interface

The generic finite switching theorem proves a tower product bound once a list
of success events is sequentially half-admissible.  The v13 manuscript needs a
stronger, concrete instantiation: for each switched coordinate, the full
history field before that coordinate must decompose into finite atoms, and the
next success event must occupy at most half of every such atom.

This file records exactly that finite certificate.  It does not assert that
the manuscript's actual SAT ensemble supplies the certificate; it proves what
Lean can conclude once the certificate is supplied.
-/

namespace Mettapedia.Computability.PNP

open scoped BigOperators

universe u

/-- One switched coordinate in the v13 product-success argument.  The event
used by the tower product is exact success of the observer's output bit on the
hidden target bit for this coordinate. -/
structure V13SwitchedStep (Ω : Type u) where
  coordinate : Nat
  observerBit : Ω → Bool
  targetBit : Ω → Bool

namespace V13SwitchedStep

/-- The exact-success event `A_j = B_j` for one switched coordinate. -/
def successEvent {Ω : Type u} (step : V13SwitchedStep Ω) : FiniteEvent Ω where
  pred := fun ω => step.observerBit ω = step.targetBit ω
  decidablePred := fun _ => inferInstance

end V13SwitchedStep

/-- The success-event history induced by an ordered list of v13 switched
coordinates. -/
def v13SuccessEvents {Ω : Type u} :
    List (V13SwitchedStep Ω) → List (FiniteEvent Ω)
  | [] => []
  | step :: rest => step.successEvent :: v13SuccessEvents rest

@[simp] theorem v13SuccessEvents_length {Ω : Type u}
    (steps : List (V13SwitchedStep Ω)) :
    (v13SuccessEvents steps).length = steps.length := by
  induction steps with
  | nil =>
      rfl
  | cons step rest ih =>
      simp [v13SuccessEvents, ih]

/-- A finite atom ledger for one v13 prefix.  The `Cell` type represents the
atoms of the full switched history field before the next coordinate.  The two
decomposition equalities say that these atoms exactly account for the current
success prefix and for the prefix plus the next success event.  The cellwise
half bound is the finite form of v13 admissibility on every positive or empty
history atom. -/
structure V13PrefixInstantiation {Ω : Type u} [Fintype Ω]
    (hist : List (FiniteEvent Ω)) (step : V13SwitchedStep Ω) where
  Cell : Type u
  [fintypeCell : Fintype Cell]
  prefixCount : Cell → Nat
  successCount : Cell → Nat
  prefix_decomp :
    finiteHistoryCount Ω hist = Finset.univ.sum prefixCount
  success_decomp :
    finiteHistoryCount Ω (hist ++ [step.successEvent]) =
      Finset.univ.sum successCount
  cell_half : ∀ cell, 2 * successCount cell ≤ prefixCount cell

attribute [instance] V13PrefixInstantiation.fintypeCell

/-- Supplying a v13 atom ledger for one prefix implies the generic prefix
half-step required by the tower theorem. -/
theorem prefixHalfStep_of_v13PrefixInstantiation
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (cert : V13PrefixInstantiation hist step) :
    PrefixHalfStep hist step.successEvent := by
  rw [PrefixHalfStep, cert.success_decomp, cert.prefix_decomp]
  calc
    2 * Finset.univ.sum cert.successCount =
        Finset.univ.sum (fun cell => 2 * cert.successCount cell) := by
        rw [Finset.mul_sum]
    _ ≤ Finset.univ.sum cert.prefixCount := by
        exact Finset.sum_le_sum (fun cell _ => cert.cell_half cell)

/-- The summary ledger above is exactly as strong as the generic prefix
half-step: when the prefix half-step holds, the whole history can be represented
as one abstract cell.  This is useful as a guardrail: a real v13 instantiation
must add semantic content about the cells, not merely supply this summary
ledger. -/
def v13PrefixInstantiation_of_prefixHalfStep
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (h : PrefixHalfStep hist step.successEvent) :
    V13PrefixInstantiation hist step := by
  refine
    { Cell := PUnit.{u+1}
      prefixCount := fun _ => finiteHistoryCount Ω hist
      successCount := fun _ => finiteHistoryCount Ω (hist ++ [step.successEvent])
      prefix_decomp := ?_
      success_decomp := ?_
      cell_half := ?_ }
  · simp
  · simp
  · intro cell
    simpa [PrefixHalfStep] using h

/-- The proposition that the v13 atom-ledger obligation has been instantiated
for a particular prefix and next switched coordinate. -/
def V13PrefixInstantiated {Ω : Type u} [Fintype Ω]
    (hist : List (FiniteEvent Ω)) (step : V13SwitchedStep Ω) : Prop :=
  Nonempty (V13PrefixInstantiation hist step)

theorem prefixHalfStep_of_v13PrefixInstantiated
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (h : V13PrefixInstantiated hist step) :
    PrefixHalfStep hist step.successEvent := by
  rcases h with ⟨cert⟩
  exact prefixHalfStep_of_v13PrefixInstantiation cert

/-- The abstract v13 summary-ledger proposition is equivalent to the generic
prefix half-step.  The later concrete-cell interface is the non-vacuous
instantiation target. -/
theorem v13PrefixInstantiated_iff_prefixHalfStep
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω} :
    V13PrefixInstantiated hist step ↔
      PrefixHalfStep hist step.successEvent := by
  constructor
  · exact prefixHalfStep_of_v13PrefixInstantiated
  · intro h
    exact ⟨v13PrefixInstantiation_of_prefixHalfStep h⟩

/-- Failure of the generic prefix half-step rules out any v13 atom-ledger
instantiation for that prefix. -/
theorem not_v13PrefixInstantiated_of_not_prefixHalfStep
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (hfail : ¬ PrefixHalfStep hist step.successEvent) :
    ¬ V13PrefixInstantiated hist step := by
  intro h
  exact hfail (prefixHalfStep_of_v13PrefixInstantiated h)

/-- Finite event counts respect pointwise logical equivalence. -/
theorem finiteEventCount_congr {Ω : Type u} [Fintype Ω]
    {E F : Ω → Prop} [DecidablePred E] [DecidablePred F]
    (h : ∀ ω, E ω ↔ F ω) :
    finiteEventCount Ω E = finiteEventCount Ω F := by
  apply le_antisymm
  · exact finiteEventCount_le_of_imp (fun ω hE => (h ω).1 hE)
  · exact finiteEventCount_le_of_imp (fun ω hF => (h ω).2 hF)

/-- Split a finite event by a decidable subevent. -/
def finiteEventSplitEquiv {Ω : Type u} {E F : Ω → Prop} [DecidablePred F] :
    {ω : Ω // E ω} ≃
      ({ω : Ω // E ω ∧ F ω} ⊕ {ω : Ω // E ω ∧ ¬ F ω}) where
  toFun := fun ω =>
    if hF : F ω.1 then Sum.inl ⟨ω.1, ω.2, hF⟩
    else Sum.inr ⟨ω.1, ω.2, hF⟩
  invFun := fun s =>
    match s with
    | Sum.inl ω => ⟨ω.1, ω.2.1⟩
    | Sum.inr ω => ⟨ω.1, ω.2.1⟩
  left_inv := by
    intro ω
    by_cases hF : F ω.1 <;> simp [hF]
  right_inv := by
    intro s
    cases s with
    | inl ω => simp [ω.2.2]
    | inr ω => simp [ω.2.2]

/-- A finite event count splits into the part satisfying a decidable subevent
and the complementary part. -/
theorem finiteEventCount_split {Ω : Type u} [Fintype Ω]
    {E F : Ω → Prop} [DecidablePred E] [DecidablePred F] :
    finiteEventCount Ω E =
      finiteEventCount Ω (fun ω => E ω ∧ F ω) +
        finiteEventCount Ω (fun ω => E ω ∧ ¬ F ω) := by
  change Fintype.card {ω : Ω // E ω} =
    Fintype.card {ω : Ω // E ω ∧ F ω} +
      Fintype.card {ω : Ω // E ω ∧ ¬ F ω}
  rw [Fintype.card_congr (finiteEventSplitEquiv (E := E) (F := F))]
  exact Fintype.card_sum

/-- A singleton extension of a history is the intersection of the history with
the final event. -/
theorem allEvents_append_singleton_iff {Ω : Type u}
    (hist : List (FiniteEvent Ω)) (E : FiniteEvent Ω) (ω : Ω) :
    allEvents (hist ++ [E]) ω ↔ allEvents hist ω ∧ E.pred ω := by
  induction hist with
  | nil =>
      simp [allEvents]
  | cons F rest ih =>
      simp [allEvents, ih, and_assoc]

/-- Counting a history extended by one event is the same as counting the
intersection of the old history and that event. -/
theorem finiteHistoryCount_append_singleton {Ω : Type u} [Fintype Ω]
    (hist : List (FiniteEvent Ω)) (E : FiniteEvent Ω) :
    finiteHistoryCount Ω (hist ++ [E]) =
      finiteEventCount Ω (fun ω => allEvents hist ω ∧ E.pred ω) := by
  simpa [finiteHistoryCount] using
    finiteEventCount_congr (Ω := Ω)
      (E := allEvents (hist ++ [E]))
      (F := fun ω => allEvents hist ω ∧ E.pred ω)
      (allEvents_append_singleton_iff hist E)

/-- Partition a finite event by an arbitrary finite cell map.  This is the
generic counting fact behind the concrete v13 atom ledger: once a finite
`cellOf` map is supplied, the decomposition equations are ordinary finite
partition identities. -/
def finiteEventCellPartitionEquiv {Ω Cell : Type u} {E : Ω → Prop}
    (cellOf : Ω → Cell) :
    {ω : Ω // E ω} ≃
      Sigma (fun cell : Cell => {ω : Ω // E ω ∧ cellOf ω = cell}) where
  toFun := fun ω => ⟨cellOf ω.1, ⟨ω.1, ω.2, rfl⟩⟩
  invFun := fun cellω => ⟨cellω.2.1, cellω.2.2.1⟩
  left_inv := by
    intro ω
    rfl
  right_inv := by
    rintro ⟨cell, ω, hE, hcell⟩
    cases hcell
    rfl

/-- Finite event counts split as the sum of their finite cell fibers. -/
theorem finiteEventCount_cell_partition {Ω Cell : Type u}
    [Fintype Ω] [Fintype Cell] [DecidableEq Cell]
    {E : Ω → Prop} [DecidablePred E] (cellOf : Ω → Cell) :
    finiteEventCount Ω E =
      Finset.univ.sum (fun cell =>
        finiteEventCount Ω (fun ω => E ω ∧ cellOf ω = cell)) := by
  change Fintype.card {ω : Ω // E ω} =
    Finset.univ.sum (fun cell : Cell =>
      Fintype.card {ω : Ω // E ω ∧ cellOf ω = cell})
  rw [Fintype.card_congr (finiteEventCellPartitionEquiv cellOf)]
  rw [Fintype.card_sigma]

/-- The count of a concrete history atom selected by a cell map. -/
def v13ConcretePrefixCount {Ω Cell : Type u} [Fintype Ω]
    [DecidableEq Cell] (hist : List (FiniteEvent Ω))
    (cellOf : Ω → Cell) (cell : Cell) : Nat :=
  finiteEventCount Ω (fun ω => allEvents hist ω ∧ cellOf ω = cell)

/-- The count of points in a concrete history atom that also satisfy the next
exact-success event. -/
def v13ConcreteSuccessCount {Ω Cell : Type u} [Fintype Ω]
    [DecidableEq Cell] (hist : List (FiniteEvent Ω))
    (step : V13SwitchedStep Ω) (cellOf : Ω → Cell) (cell : Cell) : Nat :=
  finiteEventCount Ω
    (fun ω => allEvents hist ω ∧ cellOf ω = cell ∧ step.successEvent.pred ω)

/-- The count of points in a concrete history atom that fail the next
exact-success event. -/
def v13ConcreteFailureCount {Ω Cell : Type u} [Fintype Ω]
    [DecidableEq Cell] (hist : List (FiniteEvent Ω))
    (step : V13SwitchedStep Ω) (cellOf : Ω → Cell) (cell : Cell) : Nat :=
  finiteEventCount Ω
    (fun ω => allEvents hist ω ∧ cellOf ω = cell ∧ ¬ step.successEvent.pred ω)

/-- A concrete history atom splits exactly into its next-success and
next-failure parts. -/
theorem v13ConcretePrefixCount_eq_success_add_failure {Ω Cell : Type u}
    [Fintype Ω] [DecidableEq Cell]
    (hist : List (FiniteEvent Ω)) (step : V13SwitchedStep Ω)
    (cellOf : Ω → Cell) (cell : Cell) :
    v13ConcretePrefixCount (Ω := Ω) hist cellOf cell =
      v13ConcreteSuccessCount (Ω := Ω) hist step cellOf cell +
        v13ConcreteFailureCount (Ω := Ω) hist step cellOf cell := by
  have hsplit := finiteEventCount_split (Ω := Ω)
    (E := fun ω => allEvents hist ω ∧ cellOf ω = cell)
    (F := step.successEvent.pred)
  rw [v13ConcretePrefixCount, v13ConcreteSuccessCount,
    v13ConcreteFailureCount]
  rw [hsplit]
  congr 1
  · exact finiteEventCount_congr (Ω := Ω)
      (E := fun ω =>
        (allEvents hist ω ∧ cellOf ω = cell) ∧ step.successEvent.pred ω)
      (F := fun ω =>
        allEvents hist ω ∧ cellOf ω = cell ∧ step.successEvent.pred ω)
      (by
        intro ω
        constructor
        · intro h
          exact ⟨h.1.1, h.1.2, h.2⟩
        · intro h
          exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩)
  · exact finiteEventCount_congr (Ω := Ω)
      (E := fun ω =>
        (allEvents hist ω ∧ cellOf ω = cell) ∧ ¬ step.successEvent.pred ω)
      (F := fun ω =>
        allEvents hist ω ∧ cellOf ω = cell ∧ ¬ step.successEvent.pred ω)
      (by
        intro ω
        constructor
        · intro h
          exact ⟨h.1.1, h.1.2, h.2⟩
        · intro h
          exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩)

/-- The fixed-cell half-success inequality is exactly a success-versus-failure
balance condition inside that cell. -/
theorem v13ConcreteCellHalf_iff_success_le_failure {Ω Cell : Type u}
    [Fintype Ω] [DecidableEq Cell]
    (hist : List (FiniteEvent Ω)) (step : V13SwitchedStep Ω)
    (cellOf : Ω → Cell) (cell : Cell) :
    (2 * v13ConcreteSuccessCount (Ω := Ω) hist step cellOf cell ≤
        v13ConcretePrefixCount (Ω := Ω) hist cellOf cell) ↔
      v13ConcreteSuccessCount (Ω := Ω) hist step cellOf cell ≤
        v13ConcreteFailureCount (Ω := Ω) hist step cellOf cell := by
  have hsplit := v13ConcretePrefixCount_eq_success_add_failure
    (Ω := Ω) hist step cellOf cell
  constructor
  · intro h
    omega
  · intro h
    omega

/-- Any finite cell map automatically decomposes the current v13 success
prefix into its concrete cell fibers. -/
theorem v13ConcretePrefixCount_decomp {Ω Cell : Type u}
    [Fintype Ω] [Fintype Cell] [DecidableEq Cell]
    (hist : List (FiniteEvent Ω)) (cellOf : Ω → Cell) :
    finiteHistoryCount Ω hist =
      Finset.univ.sum (v13ConcretePrefixCount (Ω := Ω) hist cellOf) := by
  simpa [finiteHistoryCount, v13ConcretePrefixCount] using
    finiteEventCount_cell_partition (Ω := Ω) (Cell := Cell)
      (E := allEvents hist) cellOf

/-- Any finite cell map automatically decomposes the next-success prefix into
its concrete cell fibers. -/
theorem v13ConcreteSuccessCount_decomp {Ω Cell : Type u}
    [Fintype Ω] [Fintype Cell] [DecidableEq Cell]
    (hist : List (FiniteEvent Ω)) (step : V13SwitchedStep Ω)
    (cellOf : Ω → Cell) :
    finiteHistoryCount Ω (hist ++ [step.successEvent]) =
      Finset.univ.sum (v13ConcreteSuccessCount (Ω := Ω) hist step cellOf) := by
  have hpartition :
      finiteEventCount Ω (fun ω => allEvents hist ω ∧ step.successEvent.pred ω) =
        Finset.univ.sum (fun cell =>
          finiteEventCount Ω
            (fun ω =>
              (allEvents hist ω ∧ step.successEvent.pred ω) ∧
                cellOf ω = cell)) :=
    finiteEventCount_cell_partition (Ω := Ω) (Cell := Cell)
      (E := fun ω => allEvents hist ω ∧ step.successEvent.pred ω) cellOf
  have hsum :
      Finset.univ.sum (fun cell =>
          finiteEventCount Ω
            (fun ω =>
              (allEvents hist ω ∧ step.successEvent.pred ω) ∧
                cellOf ω = cell)) =
        Finset.univ.sum (v13ConcreteSuccessCount (Ω := Ω) hist step cellOf) := by
    apply Finset.sum_congr rfl
    intro cell hcell
    exact finiteEventCount_congr (Ω := Ω)
      (E := fun ω =>
        (allEvents hist ω ∧ step.successEvent.pred ω) ∧ cellOf ω = cell)
      (F := fun ω =>
        allEvents hist ω ∧ cellOf ω = cell ∧ step.successEvent.pred ω)
      (by
        intro ω
        constructor
        · intro h
          exact ⟨h.1.1, h.2, h.1.2⟩
        · intro h
          exact ⟨⟨h.1, h.2.2⟩, h.2.1⟩)
  rw [finiteHistoryCount_append_singleton (Ω := Ω) hist step.successEvent,
    hpartition, hsum]

/-- A semantic v13 prefix certificate.  Unlike `V13PrefixInstantiation`, this
contains an actual finite cell map on sample points.  The decomposition fields
are retained in the record for auditability, but the lemmas above show that
they are automatic for every finite `cellOf` map; the nontrivial burden is the
cellwise half-success inequality. -/
structure V13ConcretePrefixInstantiation {Ω : Type u} [Fintype Ω]
    (hist : List (FiniteEvent Ω)) (step : V13SwitchedStep Ω) where
  Cell : Type u
  [fintypeCell : Fintype Cell]
  [decidableEqCell : DecidableEq Cell]
  cellOf : Ω → Cell
  prefix_decomp :
    finiteHistoryCount Ω hist =
      Finset.univ.sum (v13ConcretePrefixCount (Ω := Ω) hist cellOf)
  success_decomp :
    finiteHistoryCount Ω (hist ++ [step.successEvent]) =
      Finset.univ.sum (v13ConcreteSuccessCount (Ω := Ω) hist step cellOf)
  cell_half : ∀ cell,
    2 * v13ConcreteSuccessCount (Ω := Ω) hist step cellOf cell ≤
      v13ConcretePrefixCount (Ω := Ω) hist cellOf cell

attribute [instance] V13ConcretePrefixInstantiation.fintypeCell
attribute [instance] V13ConcretePrefixInstantiation.decidableEqCell

/-- Build a semantic concrete-cell certificate from a finite cell map plus the
cellwise half-success inequalities.  The decomposition fields are supplied by
finite partition identities. -/
def v13ConcretePrefixInstantiation_of_cellHalf
    {Ω Cell : Type u} [Fintype Ω] [Fintype Cell] [DecidableEq Cell]
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (cellOf : Ω → Cell)
    (hhalf : ∀ cell,
      2 * v13ConcreteSuccessCount (Ω := Ω) hist step cellOf cell ≤
        v13ConcretePrefixCount (Ω := Ω) hist cellOf cell) :
    V13ConcretePrefixInstantiation hist step where
  Cell := Cell
  cellOf := cellOf
  prefix_decomp := v13ConcretePrefixCount_decomp hist cellOf
  success_decomp := v13ConcreteSuccessCount_decomp hist step cellOf
  cell_half := hhalf

/-- A concrete cell-map certificate induces the abstract summary ledger. -/
def v13PrefixInstantiation_of_concretePrefixInstantiation
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (cert : V13ConcretePrefixInstantiation hist step) :
    V13PrefixInstantiation hist step := by
  letI : Fintype cert.Cell := cert.fintypeCell
  letI : DecidableEq cert.Cell := cert.decidableEqCell
  exact
    { Cell := cert.Cell
      prefixCount := v13ConcretePrefixCount (Ω := Ω) hist cert.cellOf
      successCount := v13ConcreteSuccessCount (Ω := Ω) hist step cert.cellOf
      prefix_decomp := cert.prefix_decomp
      success_decomp := cert.success_decomp
      cell_half := cert.cell_half }

/-- A concrete cell-map certificate is sufficient for the generic prefix
half-step. -/
theorem prefixHalfStep_of_v13ConcretePrefixInstantiation
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (cert : V13ConcretePrefixInstantiation hist step) :
    PrefixHalfStep hist step.successEvent := by
  exact prefixHalfStep_of_v13PrefixInstantiation
    (v13PrefixInstantiation_of_concretePrefixInstantiation cert)

/-- The proposition that a semantic v13 cell-map certificate has been supplied
for one prefix. -/
def V13ConcretePrefixInstantiated {Ω : Type u} [Fintype Ω]
    (hist : List (FiniteEvent Ω)) (step : V13SwitchedStep Ω) : Prop :=
  Nonempty (V13ConcretePrefixInstantiation hist step)

theorem v13PrefixInstantiated_of_v13ConcretePrefixInstantiated
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (h : V13ConcretePrefixInstantiated hist step) :
    V13PrefixInstantiated hist step := by
  rcases h with ⟨cert⟩
  exact ⟨v13PrefixInstantiation_of_concretePrefixInstantiation cert⟩

theorem prefixHalfStep_of_v13ConcretePrefixInstantiated
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (h : V13ConcretePrefixInstantiated hist step) :
    PrefixHalfStep hist step.successEvent := by
  exact prefixHalfStep_of_v13PrefixInstantiated
    (v13PrefixInstantiated_of_v13ConcretePrefixInstantiated h)

/-- Even the existential concrete-cell certificate is equivalent to the generic
prefix half-step: the constant cell map witnesses it whenever the half-step
already holds.  A non-vacuous v13 instantiation therefore has to fix the
history field externally. -/
def v13ConcretePrefixInstantiation_of_prefixHalfStep
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (h : PrefixHalfStep hist step.successEvent) :
    V13ConcretePrefixInstantiation hist step := by
  let cellOf : Ω → PUnit.{u+1} := fun _ => PUnit.unit
  refine
    { Cell := PUnit.{u+1}
      cellOf := cellOf
      prefix_decomp := ?_
      success_decomp := ?_
      cell_half := ?_ }
  · have hcount :
        finiteHistoryCount Ω hist =
          finiteEventCount Ω
            (fun ω => allEvents hist ω ∧ cellOf ω = PUnit.unit) := by
      simp [finiteHistoryCount, cellOf]
    simpa [v13ConcretePrefixCount, cellOf] using hcount
  · have hcount :
        finiteHistoryCount Ω (hist ++ [step.successEvent]) =
          finiteEventCount Ω
            (fun ω =>
              allEvents hist ω ∧ cellOf ω = PUnit.unit ∧
                step.successEvent.pred ω) := by
      have hhist :
          finiteHistoryCount Ω (hist ++ [step.successEvent]) =
            finiteEventCount Ω
              (fun ω => allEvents hist ω ∧ step.successEvent.pred ω) :=
        finiteHistoryCount_append_singleton (Ω := Ω) hist step.successEvent
      have hcell :
          finiteEventCount Ω
              (fun ω => allEvents hist ω ∧ step.successEvent.pred ω) =
            finiteEventCount Ω
              (fun ω =>
                allEvents hist ω ∧ cellOf ω = PUnit.unit ∧
                  step.successEvent.pred ω) := by
        exact finiteEventCount_congr (Ω := Ω)
          (E := fun ω => allEvents hist ω ∧ step.successEvent.pred ω)
          (F := fun ω =>
            allEvents hist ω ∧ cellOf ω = PUnit.unit ∧
              step.successEvent.pred ω)
          (by intro ω; simp [cellOf])
      exact hhist.trans hcell
    simpa [v13ConcreteSuccessCount, cellOf] using hcount
  · intro cell
    cases cell
    have hprefix :
        finiteHistoryCount Ω hist =
          v13ConcretePrefixCount (Ω := Ω) hist cellOf PUnit.unit := by
      have hcount :
          finiteHistoryCount Ω hist =
            finiteEventCount Ω
              (fun ω => allEvents hist ω ∧ cellOf ω = PUnit.unit) := by
        simp [finiteHistoryCount, cellOf]
      simpa [v13ConcretePrefixCount, cellOf] using hcount
    have hsuccess :
        finiteHistoryCount Ω (hist ++ [step.successEvent]) =
          v13ConcreteSuccessCount (Ω := Ω) hist step cellOf PUnit.unit := by
      have hcount :
          finiteHistoryCount Ω (hist ++ [step.successEvent]) =
            finiteEventCount Ω
              (fun ω =>
                allEvents hist ω ∧ cellOf ω = PUnit.unit ∧
                  step.successEvent.pred ω) := by
        have hhist :
            finiteHistoryCount Ω (hist ++ [step.successEvent]) =
              finiteEventCount Ω
                (fun ω => allEvents hist ω ∧ step.successEvent.pred ω) :=
          finiteHistoryCount_append_singleton (Ω := Ω) hist step.successEvent
        have hcell :
            finiteEventCount Ω
                (fun ω => allEvents hist ω ∧ step.successEvent.pred ω) =
              finiteEventCount Ω
                (fun ω =>
                  allEvents hist ω ∧ cellOf ω = PUnit.unit ∧
                    step.successEvent.pred ω) := by
          exact finiteEventCount_congr (Ω := Ω)
            (E := fun ω => allEvents hist ω ∧ step.successEvent.pred ω)
            (F := fun ω =>
              allEvents hist ω ∧ cellOf ω = PUnit.unit ∧
                step.successEvent.pred ω)
            (by intro ω; simp [cellOf])
        exact hhist.trans hcell
      simpa [v13ConcreteSuccessCount, cellOf] using hcount
    rw [← hprefix, ← hsuccess]
    exact h

/-- The existential concrete-cell proposition is still exactly the generic
prefix half-step. -/
theorem v13ConcretePrefixInstantiated_iff_prefixHalfStep
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω} :
    V13ConcretePrefixInstantiated hist step ↔
      PrefixHalfStep hist step.successEvent := by
  constructor
  · exact prefixHalfStep_of_v13ConcretePrefixInstantiated
  · intro h
    exact ⟨v13ConcretePrefixInstantiation_of_prefixHalfStep h⟩

/-- A fixed history field for a v13 prefix.  Unlike
`V13ConcretePrefixInstantiation`, this is meant to be supplied by the
manuscript's actual switched-history construction, not existentially chosen
after the fact. -/
structure V13HistoryField (Ω : Type u) where
  Cell : Type u
  [fintypeCell : Fintype Cell]
  [decidableEqCell : DecidableEq Cell]
  cellOf : Ω → Cell

attribute [instance] V13HistoryField.fintypeCell
attribute [instance] V13HistoryField.decidableEqCell

/-- A fixed history field determines the next success event when every field
cell is success-homogeneous: once one point in a cell is successful for the
next switched coordinate, every point in that same cell is also successful. -/
def V13HistoryFieldDeterminesSuccess {Ω : Type u}
    (field : V13HistoryField Ω) (step : V13SwitchedStep Ω) : Prop :=
  ∀ ⦃ω ω' : Ω⦄,
    field.cellOf ω = field.cellOf ω' →
      step.successEvent.pred ω → step.successEvent.pred ω'

/-- Prefix-relative success determination.  This is the relevant obstruction
for conditioned switching histories: a field may reveal the next success event
on the current history support even if it does not reveal it globally. -/
def V13HistoryFieldDeterminesSuccessOn {Ω : Type u}
    (field : V13HistoryField Ω) (hist : List (FiniteEvent Ω))
    (step : V13SwitchedStep Ω) : Prop :=
  ∀ ⦃ω ω' : Ω⦄,
    allEvents hist ω →
      allEvents hist ω' →
        field.cellOf ω = field.cellOf ω' →
          step.successEvent.pred ω → step.successEvent.pred ω'

/-- Global success determination implies prefix-relative success determination
on every current history support. -/
theorem v13HistoryFieldDeterminesSuccessOn_of_determinesSuccess {Ω : Type u}
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω}
    (hdet : V13HistoryFieldDeterminesSuccess field step) :
    V13HistoryFieldDeterminesSuccessOn field hist step := by
  intro ω ω' _ _ hcell hsucc
  exact hdet hcell hsucc

/-- The fixed field that reveals exactly whether the next v13 switched step is
successful.  A genuine v13 history field cannot behave this way on a
positive-mass prefix while also satisfying the cellwise half-success
certificate below. -/
def v13SuccessHistoryField {Ω : Type u} (step : V13SwitchedStep Ω) :
    V13HistoryField Ω where
  Cell := ULift.{u} Bool
  cellOf := fun ω => ULift.up (decide (step.successEvent.pred ω))

/-- The success-revealing history field determines the next success event. -/
theorem v13SuccessHistoryField_determinesSuccess {Ω : Type u}
    (step : V13SwitchedStep Ω) :
    V13HistoryFieldDeterminesSuccess (v13SuccessHistoryField step) step := by
  intro ω ω' hcell hsucc
  have hbool :
      decide (step.successEvent.pred ω) =
        decide (step.successEvent.pred ω') := congrArg ULift.down hcell
  rw [decide_eq_true hsucc] at hbool
  exact of_decide_eq_true hbool.symm

/-- In the success-revealing field, the `true` cell is exactly the next success
event. -/
theorem v13SuccessHistoryField_prefix_true_count
    {Ω : Type u} [Fintype Ω]
    (hist : List (FiniteEvent Ω)) (step : V13SwitchedStep Ω) :
    v13ConcretePrefixCount (Ω := Ω) hist
        (v13SuccessHistoryField step).cellOf (ULift.up true) =
      finiteHistoryCount Ω (hist ++ [step.successEvent]) := by
  rw [v13ConcretePrefixCount,
    finiteHistoryCount_append_singleton (Ω := Ω) hist step.successEvent]
  exact finiteEventCount_congr (Ω := Ω)
    (E := fun ω =>
      allEvents hist ω ∧ (v13SuccessHistoryField step).cellOf ω = ULift.up true)
    (F := fun ω => allEvents hist ω ∧ step.successEvent.pred ω)
    (by
      intro ω
      simp [v13SuccessHistoryField])

/-- Once the fixed field has already selected the next-success cell, intersecting
that cell with the next success event does not reduce it. -/
theorem v13SuccessHistoryField_success_true_count_eq_prefix_true_count
    {Ω : Type u} [Fintype Ω]
    (hist : List (FiniteEvent Ω)) (step : V13SwitchedStep Ω) :
    v13ConcreteSuccessCount (Ω := Ω) hist step
        (v13SuccessHistoryField step).cellOf (ULift.up true) =
      v13ConcretePrefixCount (Ω := Ω) hist
        (v13SuccessHistoryField step).cellOf (ULift.up true) := by
  rw [v13ConcreteSuccessCount, v13ConcretePrefixCount]
  exact finiteEventCount_congr (Ω := Ω)
    (E := fun ω =>
      allEvents hist ω ∧
        (v13SuccessHistoryField step).cellOf ω = ULift.up true ∧
          step.successEvent.pred ω)
    (F := fun ω =>
      allEvents hist ω ∧ (v13SuccessHistoryField step).cellOf ω = ULift.up true)
    (by
      intro ω
      simp [v13SuccessHistoryField])

/-- Cellwise half-success certificate for a fixed externally supplied history
field.  This is the non-vacuous v13 instantiation target: the field is a
parameter, not part of an existential certificate. -/
structure V13FieldPrefixInstantiation {Ω : Type u} [Fintype Ω]
    (field : V13HistoryField Ω) (hist : List (FiniteEvent Ω))
    (step : V13SwitchedStep Ω) where
  prefix_decomp :
    finiteHistoryCount Ω hist =
      Finset.univ.sum (v13ConcretePrefixCount (Ω := Ω) hist field.cellOf)
  success_decomp :
    finiteHistoryCount Ω (hist ++ [step.successEvent]) =
      Finset.univ.sum (v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf)
  cell_half : ∀ cell,
    2 * v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell ≤
      v13ConcretePrefixCount (Ω := Ω) hist field.cellOf cell

/-- Build a fixed-field prefix certificate from the cellwise half-success
inequality.  The decomposition obligations are automatic finite partition
identities for the supplied field. -/
def v13FieldPrefixInstantiation_of_cellHalf
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω}
    (hhalf : ∀ cell,
      2 * v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell ≤
        v13ConcretePrefixCount (Ω := Ω) hist field.cellOf cell) :
    V13FieldPrefixInstantiation field hist step where
  prefix_decomp := v13ConcretePrefixCount_decomp hist field.cellOf
  success_decomp := v13ConcreteSuccessCount_decomp hist step field.cellOf
  cell_half := hhalf

/-- For a fixed supplied history field, the v13 prefix certificate is exactly
the cellwise half-success inequality.  The decomposition fields in the record
are audit data, not additional mathematical obligations. -/
theorem v13FieldPrefixInstantiation_iff_cellHalf
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω} :
    V13FieldPrefixInstantiation field hist step ↔
      ∀ cell,
        2 * v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell ≤
          v13ConcretePrefixCount (Ω := Ω) hist field.cellOf cell := by
  constructor
  · intro cert
    exact cert.cell_half
  · intro hhalf
    exact v13FieldPrefixInstantiation_of_cellHalf hhalf

/-- Equivalently, the exact missing fixed-field theorem is a per-cell balance:
every successful prefix point in a supplied history atom must be matched by at
least one unsuccessful prefix point in the same atom. -/
theorem v13FieldPrefixInstantiation_iff_success_le_failure
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω} :
    V13FieldPrefixInstantiation field hist step ↔
      ∀ cell,
        v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell ≤
          v13ConcreteFailureCount (Ω := Ω) hist step field.cellOf cell := by
  rw [v13FieldPrefixInstantiation_iff_cellHalf]
  constructor
  · intro h cell
    exact (v13ConcreteCellHalf_iff_success_le_failure
      (Ω := Ω) hist step field.cellOf cell).mp (h cell)
  · intro h cell
    exact (v13ConcreteCellHalf_iff_success_le_failure
      (Ω := Ω) hist step field.cellOf cell).mpr (h cell)

/-- The successful points in a supplied history cell for the next v13 switched
coordinate. -/
def V13CellSuccessFiber {Ω : Type u} [Fintype Ω]
    (field : V13HistoryField Ω) (hist : List (FiniteEvent Ω))
    (step : V13SwitchedStep Ω) (cell : field.Cell) : Type u :=
  {ω : Ω // allEvents hist ω ∧ field.cellOf ω = cell ∧ step.successEvent.pred ω}

/-- The unsuccessful points in a supplied history cell for the next v13
switched coordinate. -/
def V13CellFailureFiber {Ω : Type u} [Fintype Ω]
    (field : V13HistoryField Ω) (hist : List (FiniteEvent Ω))
    (step : V13SwitchedStep Ω) (cell : field.Cell) : Type u :=
  {ω : Ω // allEvents hist ω ∧ field.cellOf ω = cell ∧ ¬ step.successEvent.pred ω}

instance v13CellSuccessFiber_fintype {Ω : Type u} [Fintype Ω]
    (field : V13HistoryField Ω) (hist : List (FiniteEvent Ω))
    (step : V13SwitchedStep Ω) (cell : field.Cell) :
    Fintype (V13CellSuccessFiber field hist step cell) := by
  unfold V13CellSuccessFiber
  infer_instance

instance v13CellFailureFiber_fintype {Ω : Type u} [Fintype Ω]
    (field : V13HistoryField Ω) (hist : List (FiniteEvent Ω))
    (step : V13SwitchedStep Ω) (cell : field.Cell) :
    Fintype (V13CellFailureFiber field hist step cell) := by
  unfold V13CellFailureFiber
  infer_instance

/-- The operational fixed-field obligation: in every supplied history cell,
successful prefix points can be injectively matched to unsuccessful prefix
points in the same cell. -/
def V13FieldFailureMatching {Ω : Type u} [Fintype Ω]
    (field : V13HistoryField Ω) (hist : List (FiniteEvent Ω))
    (step : V13SwitchedStep Ω) : Prop :=
  ∀ cell, Nonempty
    (V13CellSuccessFiber field hist step cell ↪
      V13CellFailureFiber field hist step cell)

/-- A same-cell failure matching gives an explicit failed prefix point in the
same supplied field cell for every successful prefix point. -/
theorem exists_sameCell_failure_of_fieldFailureMatching_success
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω}
    (hmatch : V13FieldFailureMatching field hist step)
    {ω : Ω} (hhist : allEvents hist ω)
    (hsucc : step.successEvent.pred ω) :
    ∃ ω' : Ω,
      allEvents hist ω' ∧
        field.cellOf ω' = field.cellOf ω ∧
          ¬ step.successEvent.pred ω' := by
  rcases hmatch (field.cellOf ω) with ⟨emb⟩
  rcases emb ⟨ω, hhist, rfl, hsucc⟩ with ⟨ω', hω'⟩
  exact ⟨ω', hω'.1, hω'.2.1, hω'.2.2⟩

/-- If one successful prefix point has no failed prefix point in its supplied
field cell, the same-cell failure matching obligation is impossible. -/
theorem not_v13FieldFailureMatching_of_success_without_sameCell_failure
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω} {ω : Ω}
    (hhist : allEvents hist ω)
    (hsucc : step.successEvent.pred ω)
    (hnoFailure :
      ∀ ⦃ω' : Ω⦄,
        allEvents hist ω' →
          field.cellOf ω' = field.cellOf ω →
            step.successEvent.pred ω') :
    ¬ V13FieldFailureMatching field hist step := by
  intro hmatch
  rcases exists_sameCell_failure_of_fieldFailureMatching_success
      hmatch hhist hsucc with
    ⟨ω', hhist', hcell', hfail'⟩
  exact hfail' (hnoFailure hhist' hcell')

/-- The same-cell failure matching interface is exactly the per-cell
success-versus-failure count balance. -/
theorem v13FieldFailureMatching_iff_success_le_failure
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω} :
    V13FieldFailureMatching field hist step ↔
      ∀ cell,
        v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell ≤
          v13ConcreteFailureCount (Ω := Ω) hist step field.cellOf cell := by
  constructor
  · intro hmatch cell
    rcases hmatch cell with ⟨emb⟩
    have hcard := Fintype.card_le_of_embedding emb
    simpa [V13CellSuccessFiber, V13CellFailureFiber,
      v13ConcreteSuccessCount, v13ConcreteFailureCount, finiteEventCount]
      using hcard
  · intro hbalance cell
    rw [Function.Embedding.nonempty_iff_card_le]
    simpa [V13CellSuccessFiber, V13CellFailureFiber,
      v13ConcreteSuccessCount, v13ConcreteFailureCount, finiteEventCount]
      using hbalance cell

/-- A fixed-field v13 prefix certificate is equivalent to an explicit
same-cell injection from successful prefix points to unsuccessful prefix
points.  This is the constructive interface a proof of v13 sequential
admissibility must supply after the field is fixed. -/
theorem v13FieldPrefixInstantiation_iff_failureMatching
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω} :
    V13FieldPrefixInstantiation field hist step ↔
      V13FieldFailureMatching field hist step := by
  constructor
  · intro cert
    exact v13FieldFailureMatching_iff_success_le_failure.mpr
      (v13FieldPrefixInstantiation_iff_success_le_failure.mp cert)
  · intro hmatch
    exact v13FieldPrefixInstantiation_iff_success_le_failure.mpr
      (v13FieldFailureMatching_iff_success_le_failure.mp hmatch)

/-- An explicit same-cell success-to-failure matching is sufficient to build
the fixed-field prefix certificate. -/
def v13FieldPrefixInstantiation_of_failureMatching
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω}
    (hmatch : V13FieldFailureMatching field hist step) :
    V13FieldPrefixInstantiation field hist step :=
  v13FieldPrefixInstantiation_iff_failureMatching.mpr hmatch

/-- A fixed-field prefix certificate gives an explicit failed prefix point in
the same supplied field cell for every successful prefix point. -/
theorem exists_sameCell_failure_of_fieldPrefixInstantiation_success
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω}
    (cert : V13FieldPrefixInstantiation field hist step)
    {ω : Ω} (hhist : allEvents hist ω)
    (hsucc : step.successEvent.pred ω) :
    ∃ ω' : Ω,
      allEvents hist ω' ∧
        field.cellOf ω' = field.cellOf ω ∧
          ¬ step.successEvent.pred ω' := by
  exact
    exists_sameCell_failure_of_fieldFailureMatching_success
      (v13FieldPrefixInstantiation_iff_failureMatching.mp cert) hhist hsucc

/-- Failure of the same-cell matching obligation blocks the fixed-field prefix
certificate. -/
theorem not_v13FieldPrefixInstantiation_of_not_failureMatching
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω}
    (hfail : ¬ V13FieldFailureMatching field hist step) :
    ¬ V13FieldPrefixInstantiation field hist step := by
  intro cert
  exact hfail (v13FieldPrefixInstantiation_iff_failureMatching.mp cert)

/-- If one successful prefix point has no failed prefix point in its supplied
field cell, the fixed-field prefix certificate is impossible. -/
theorem not_v13FieldPrefixInstantiation_of_success_without_sameCell_failure
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω} {ω : Ω}
    (hhist : allEvents hist ω)
    (hsucc : step.successEvent.pred ω)
    (hnoFailure :
      ∀ ⦃ω' : Ω⦄,
        allEvents hist ω' →
          field.cellOf ω' = field.cellOf ω →
            step.successEvent.pred ω') :
    ¬ V13FieldPrefixInstantiation field hist step := by
  exact not_v13FieldPrefixInstantiation_of_not_failureMatching
    (not_v13FieldFailureMatching_of_success_without_sameCell_failure
      hhist hsucc hnoFailure)

/-- If a field cell has more next-success points than next-failure points, the
fixed-field prefix certificate is impossible. -/
theorem not_v13FieldPrefixInstantiation_of_success_gt_failure
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω} (cell : field.Cell)
    (hbad :
      v13ConcreteFailureCount (Ω := Ω) hist step field.cellOf cell <
        v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell) :
    ¬ V13FieldPrefixInstantiation field hist step := by
  intro cert
  have hbalance :=
    (v13FieldPrefixInstantiation_iff_success_le_failure.mp cert) cell
  exact (not_le_of_gt hbad) hbalance

/-- In a prefix-relative success-homogeneous field cell, positive success mass
forces the next-failure count in that same cell to be zero. -/
theorem v13ConcreteFailureCount_eq_zero_of_fieldDeterminesSuccessOn_of_success_pos
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω}
    (hdet : V13HistoryFieldDeterminesSuccessOn field hist step)
    (cell : field.Cell)
    (hpos : 0 < v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell) :
    v13ConcreteFailureCount (Ω := Ω) hist step field.cellOf cell = 0 := by
  have hnonempty :
      Nonempty {ω : Ω //
        allEvents hist ω ∧ field.cellOf ω = cell ∧ step.successEvent.pred ω} := by
    exact Fintype.card_pos_iff.mp (by
      simpa [v13ConcreteSuccessCount, finiteEventCount] using hpos)
  rcases hnonempty with ⟨⟨ω₀, hhist₀, hcell₀, hsuccess₀⟩⟩
  apply Nat.eq_zero_of_le_zero
  have hle :
      finiteEventCount Ω
          (fun ω =>
            allEvents hist ω ∧ field.cellOf ω = cell ∧
              ¬ step.successEvent.pred ω) ≤
        finiteEventCount Ω (fun _ : Ω => False) := by
    exact finiteEventCount_le_of_imp (Ω := Ω)
      (E := fun ω =>
        allEvents hist ω ∧ field.cellOf ω = cell ∧
          ¬ step.successEvent.pred ω)
      (F := fun _ : Ω => False)
      (by
        intro ω hω
        exact hω.2.2
          (hdet hhist₀ hω.1 (hcell₀.trans hω.2.1.symm) hsuccess₀))
  simpa [v13ConcreteFailureCount, finiteEventCount] using hle

/-- In a globally success-homogeneous field cell, positive success mass forces
the next-failure count in that same cell to be zero. -/
theorem v13ConcreteFailureCount_eq_zero_of_fieldDeterminesSuccess_of_success_pos
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω}
    (hdet : V13HistoryFieldDeterminesSuccess field step)
    (cell : field.Cell)
    (hpos : 0 < v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell) :
    v13ConcreteFailureCount (Ω := Ω) hist step field.cellOf cell = 0 := by
  exact
    v13ConcreteFailureCount_eq_zero_of_fieldDeterminesSuccessOn_of_success_pos
      (v13HistoryFieldDeterminesSuccessOn_of_determinesSuccess hdet) cell hpos

/-- If a supplied field determines the next success event on the current
history support, any cell with positive next-success mass blocks the fixed-field
prefix certificate. -/
theorem not_v13FieldPrefixInstantiation_of_fieldDeterminesSuccessOn_cell_success
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω}
    (hdet : V13HistoryFieldDeterminesSuccessOn field hist step)
    (cell : field.Cell)
    (hpos : 0 < v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell) :
    ¬ V13FieldPrefixInstantiation field hist step := by
  have hfailure_zero :=
    v13ConcreteFailureCount_eq_zero_of_fieldDeterminesSuccessOn_of_success_pos
      (Ω := Ω) (field := field) (hist := hist) (step := step)
      hdet cell hpos
  exact not_v13FieldPrefixInstantiation_of_success_gt_failure cell (by
    rw [hfailure_zero]
    exact hpos)

/-- If a supplied field determines the next success event, any cell with
positive next-success mass blocks the fixed-field prefix certificate. -/
theorem not_v13FieldPrefixInstantiation_of_fieldDeterminesSuccess_cell_success
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω}
    (hdet : V13HistoryFieldDeterminesSuccess field step)
    (cell : field.Cell)
    (hpos : 0 < v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell) :
    ¬ V13FieldPrefixInstantiation field hist step := by
  exact
    not_v13FieldPrefixInstantiation_of_fieldDeterminesSuccessOn_cell_success
      (v13HistoryFieldDeterminesSuccessOn_of_determinesSuccess hdet) cell hpos

/-- A prefix-relative success-determining field can satisfy the fixed-field
prefix certificate only when the next-success prefix has zero mass. -/
theorem not_v13FieldPrefixInstantiation_of_fieldDeterminesSuccessOn_positive_success
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω}
    (hdet : V13HistoryFieldDeterminesSuccessOn field hist step)
    (hpos : 0 < finiteHistoryCount Ω (hist ++ [step.successEvent])) :
    ¬ V13FieldPrefixInstantiation field hist step := by
  have hnonempty :
      Nonempty {ω : Ω // allEvents (hist ++ [step.successEvent]) ω} := by
    exact Fintype.card_pos_iff.mp (by
      simpa [finiteHistoryCount, finiteEventCount] using hpos)
  rcases hnonempty with ⟨⟨ω, hω⟩⟩
  have hboth := (allEvents_append_singleton_iff hist step.successEvent ω).mp hω
  let cell : field.Cell := field.cellOf ω
  have hcellpos :
      0 < v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell := by
    rw [v13ConcreteSuccessCount]
    exact Fintype.card_pos_iff.mpr ⟨⟨ω, hboth.1, rfl, hboth.2⟩⟩
  exact not_v13FieldPrefixInstantiation_of_fieldDeterminesSuccessOn_cell_success
    hdet cell hcellpos

/-- A success-determining field can satisfy the fixed-field prefix certificate
only when the next-success prefix has zero mass. -/
theorem not_v13FieldPrefixInstantiation_of_fieldDeterminesSuccess_positive_success
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω}
    (hdet : V13HistoryFieldDeterminesSuccess field step)
    (hpos : 0 < finiteHistoryCount Ω (hist ++ [step.successEvent])) :
    ¬ V13FieldPrefixInstantiation field hist step := by
  exact
    not_v13FieldPrefixInstantiation_of_fieldDeterminesSuccessOn_positive_success
      (v13HistoryFieldDeterminesSuccessOn_of_determinesSuccess hdet) hpos

/-- A prefix-relative success-determining field with positive next-success mass
cannot satisfy the operational same-cell failure-matching obligation. -/
theorem not_v13FieldFailureMatching_of_fieldDeterminesSuccessOn_positive_success
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω}
    (hdet : V13HistoryFieldDeterminesSuccessOn field hist step)
    (hpos : 0 < finiteHistoryCount Ω (hist ++ [step.successEvent])) :
    ¬ V13FieldFailureMatching field hist step := by
  intro hmatch
  exact not_v13FieldPrefixInstantiation_of_fieldDeterminesSuccessOn_positive_success
    hdet hpos (v13FieldPrefixInstantiation_of_failureMatching hmatch)

/-- A success-determining field with positive next-success mass cannot satisfy
the operational same-cell failure-matching obligation. -/
theorem not_v13FieldFailureMatching_of_fieldDeterminesSuccess_positive_success
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω}
    (hdet : V13HistoryFieldDeterminesSuccess field step)
    (hpos : 0 < finiteHistoryCount Ω (hist ++ [step.successEvent])) :
    ¬ V13FieldFailureMatching field hist step := by
  exact
    not_v13FieldFailureMatching_of_fieldDeterminesSuccessOn_positive_success
      (v13HistoryFieldDeterminesSuccessOn_of_determinesSuccess hdet) hpos

/-- Conversely, a valid same-cell failure matching on a positive next-success
prefix proves that the supplied field does not determine the next success bit
on the current history support. -/
theorem not_v13HistoryFieldDeterminesSuccessOn_of_failureMatching_positive_success
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω}
    (hmatch : V13FieldFailureMatching field hist step)
    (hpos : 0 < finiteHistoryCount Ω (hist ++ [step.successEvent])) :
    ¬ V13HistoryFieldDeterminesSuccessOn field hist step := by
  intro hdet
  exact
    not_v13FieldFailureMatching_of_fieldDeterminesSuccessOn_positive_success
      hdet hpos hmatch

/-- Conversely, a valid same-cell failure matching on a positive next-success
prefix proves that the supplied field does not globally determine the next
success bit. -/
theorem not_v13HistoryFieldDeterminesSuccess_of_failureMatching_positive_success
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω}
    (hmatch : V13FieldFailureMatching field hist step)
    (hpos : 0 < finiteHistoryCount Ω (hist ++ [step.successEvent])) :
    ¬ V13HistoryFieldDeterminesSuccess field step := by
  intro hdet
  exact
    not_v13HistoryFieldDeterminesSuccessOn_of_failureMatching_positive_success
      hmatch hpos
      (v13HistoryFieldDeterminesSuccessOn_of_determinesSuccess hdet)

/-- A fixed-field certificate induces the existential concrete-cell certificate. -/
def v13ConcretePrefixInstantiation_of_fieldPrefixInstantiation
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω}
    (cert : V13FieldPrefixInstantiation field hist step) :
    V13ConcretePrefixInstantiation hist step := by
  letI : Fintype field.Cell := field.fintypeCell
  letI : DecidableEq field.Cell := field.decidableEqCell
  exact
    { Cell := field.Cell
      cellOf := field.cellOf
      prefix_decomp := cert.prefix_decomp
      success_decomp := cert.success_decomp
      cell_half := cert.cell_half }

/-- A fixed-field v13 certificate is sufficient for the generic prefix
half-step. -/
theorem prefixHalfStep_of_v13FieldPrefixInstantiation
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω}
    (cert : V13FieldPrefixInstantiation field hist step) :
    PrefixHalfStep hist step.successEvent := by
  exact prefixHalfStep_of_v13ConcretePrefixInstantiation
    (v13ConcretePrefixInstantiation_of_fieldPrefixInstantiation cert)

/-- A fixed-field prefix certificate is blocked by one cell whose conditional
success count exceeds half of the cell's prefix count. -/
theorem not_v13FieldPrefixInstantiation_of_cell_half_violation
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω} (cell : field.Cell)
    (hbad :
      ¬ 2 * v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell ≤
        v13ConcretePrefixCount (Ω := Ω) hist field.cellOf cell) :
    ¬ V13FieldPrefixInstantiation field hist step := by
  intro cert
  exact hbad (cert.cell_half cell)

/-- In any fixed-field prefix certificate, every cell containing a successful
point must also contain at least one unsuccessful prefix point. -/
theorem v13FieldPrefixInstantiation_successCount_lt_prefixCount_of_success_pos
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω}
    (cert : V13FieldPrefixInstantiation field hist step)
    (cell : field.Cell)
    (hpos :
      0 < v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell) :
    v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell <
      v13ConcretePrefixCount (Ω := Ω) hist field.cellOf cell := by
  have hlt :
      1 * v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell <
        2 * v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell :=
    Nat.mul_lt_mul_of_pos_right (by decide) hpos
  exact lt_of_lt_of_le (by simpa using hlt) (cert.cell_half cell)

/-- A one-success cell in a fixed-field prefix certificate must contain at
least two prefix points.  Thus singleton successful cells are forbidden. -/
theorem v13FieldPrefixInstantiation_two_le_prefixCount_of_successCount_eq_one
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω}
    (cert : V13FieldPrefixInstantiation field hist step)
    (cell : field.Cell)
    (hsucc :
      v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell = 1) :
    2 ≤ v13ConcretePrefixCount (Ω := Ω) hist field.cellOf cell := by
  simpa [hsucc] using cert.cell_half cell

/-- A fixed-field prefix certificate is impossible when some positive-mass cell
is entirely successful for the next switched coordinate. -/
theorem not_v13FieldPrefixInstantiation_of_cell_success_eq_prefix
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω} (cell : field.Cell)
    (hpos :
      0 < v13ConcretePrefixCount (Ω := Ω) hist field.cellOf cell)
    (hall :
      v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell =
        v13ConcretePrefixCount (Ω := Ω) hist field.cellOf cell) :
    ¬ V13FieldPrefixInstantiation field hist step := by
  exact not_v13FieldPrefixInstantiation_of_cell_half_violation cell (by
    rw [hall]
    exact not_le_of_gt (by
      have hlt :
          1 * v13ConcretePrefixCount (Ω := Ω) hist field.cellOf cell <
            2 * v13ConcretePrefixCount (Ω := Ω) hist field.cellOf cell :=
        Nat.mul_lt_mul_of_pos_right (by decide) hpos
      simpa using hlt))

/-- A fixed-field prefix certificate is impossible when a cell has positive
success mass and that success mass exhausts the cell. -/
theorem not_v13FieldPrefixInstantiation_of_positive_success_eq_prefix
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω} (cell : field.Cell)
    (hpos :
      0 < v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell)
    (hall :
      v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell =
        v13ConcretePrefixCount (Ω := Ω) hist field.cellOf cell) :
    ¬ V13FieldPrefixInstantiation field hist step := by
  exact not_v13FieldPrefixInstantiation_of_cell_success_eq_prefix cell
    (by
      rw [← hall]
      exact hpos)
    hall

/-- A singleton cell that is successful for the next switched coordinate
cannot satisfy the fixed-field half-success certificate. -/
theorem not_v13FieldPrefixInstantiation_of_singleton_success_cell
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω} (cell : field.Cell)
    (hprefix :
      v13ConcretePrefixCount (Ω := Ω) hist field.cellOf cell = 1)
    (hsuccess :
      v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell = 1) :
    ¬ V13FieldPrefixInstantiation field hist step := by
  exact not_v13FieldPrefixInstantiation_of_positive_success_eq_prefix cell
    (by
      rw [hsuccess]
      decide)
    (by
      rw [hsuccess, hprefix])

/-- If the supplied fixed history field reveals the next success event, then a
positive-mass next-success prefix blocks the v13 cellwise half-success
certificate. -/
theorem not_v13FieldPrefixInstantiation_successHistoryField_of_positive_success
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (hpos : 0 < finiteHistoryCount Ω (hist ++ [step.successEvent])) :
    ¬ V13FieldPrefixInstantiation (v13SuccessHistoryField step) hist step := by
  exact not_v13FieldPrefixInstantiation_of_cell_success_eq_prefix (ULift.up true)
    (by
      rw [v13SuccessHistoryField_prefix_true_count]
      exact hpos)
    (v13SuccessHistoryField_success_true_count_eq_prefix_true_count hist step)

/-- A switched coordinate together with the fixed history field relative to
which its cellwise half-success obligation is to be checked. -/
structure V13FieldedStep (Ω : Type u) where
  field : V13HistoryField Ω
  step : V13SwitchedStep Ω

/-- A switched coordinate paired with the forbidden success-revealing fixed
field.  This is a reusable negative test case for v13 instantiation attempts:
on any positive-mass success prefix, the fielded certificate must fail. -/
def v13SuccessFieldedStep {Ω : Type u} (step : V13SwitchedStep Ω) :
    V13FieldedStep Ω where
  field := v13SuccessHistoryField step
  step := step

/-- The success-event history induced by an ordered list of fixed-field
switched coordinates. -/
def v13FieldedSuccessEvents {Ω : Type u} :
    List (V13FieldedStep Ω) → List (FiniteEvent Ω)
  | [] => []
  | item :: rest => item.step.successEvent :: v13FieldedSuccessEvents rest

@[simp] theorem v13FieldedSuccessEvents_length {Ω : Type u}
    (items : List (V13FieldedStep Ω)) :
    (v13FieldedSuccessEvents items).length = items.length := by
  induction items with
  | nil =>
      rfl
  | cons item rest ih =>
      simp [v13FieldedSuccessEvents, ih]

/-- Recursive fixed-field v13 instantiation from an existing success history:
every next coordinate has a cellwise half-success certificate for its externally
specified history field. -/
def V13FieldSwitchingInstantiatedFrom {Ω : Type u} [Fintype Ω]
    (hist : List (FiniteEvent Ω)) : List (V13FieldedStep Ω) → Prop
  | [] => True
  | item :: rest =>
      V13FieldPrefixInstantiation item.field hist item.step ∧
        V13FieldSwitchingInstantiatedFrom (hist ++ [item.step.successEvent]) rest

/-- Recursive fixed-field v13 instantiation from the empty success history. -/
def V13FieldSwitchingInstantiated {Ω : Type u} [Fintype Ω]
    (items : List (V13FieldedStep Ω)) : Prop :=
  V13FieldSwitchingInstantiatedFrom ([] : List (FiniteEvent Ω)) items

/-- The residual fixed-field obligation after decomposition automaticity: for
each ordered fielded step, every cell of the supplied field must satisfy the
cellwise half-success inequality relative to the current success prefix. -/
def V13FieldSwitchingCellHalfFrom {Ω : Type u} [Fintype Ω]
    (hist : List (FiniteEvent Ω)) : List (V13FieldedStep Ω) → Prop
  | [] => True
  | item :: rest =>
      (∀ cell,
        2 * v13ConcreteSuccessCount (Ω := Ω) hist item.step item.field.cellOf cell ≤
          v13ConcretePrefixCount (Ω := Ω) hist item.field.cellOf cell) ∧
        V13FieldSwitchingCellHalfFrom (hist ++ [item.step.successEvent]) rest

/-- Empty-history form of the residual fixed-field cell-half obligation. -/
def V13FieldSwitchingCellHalf {Ω : Type u} [Fintype Ω]
    (items : List (V13FieldedStep Ω)) : Prop :=
  V13FieldSwitchingCellHalfFrom ([] : List (FiniteEvent Ω)) items

/-- After the fields are fixed externally, v13 fielded switching is exactly the
recursive list of cellwise half-success inequalities. -/
theorem v13FieldSwitchingInstantiatedFrom_iff_cellHalfFrom
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)} :
    V13FieldSwitchingInstantiatedFrom hist items ↔
      V13FieldSwitchingCellHalfFrom hist items := by
  induction items generalizing hist with
  | nil =>
      constructor <;> intro h <;> trivial
  | cons item rest ih =>
      constructor
      · intro h
        rcases h with ⟨hitem, hrest⟩
        exact ⟨(v13FieldPrefixInstantiation_iff_cellHalf.mp hitem),
          (ih.mp hrest)⟩
      · intro h
        rcases h with ⟨hitem, hrest⟩
        exact ⟨(v13FieldPrefixInstantiation_iff_cellHalf.mpr hitem),
          (ih.mpr hrest)⟩

/-- Empty-history form: fixed-field v13 switching is exactly the residual
recursive cell-half obligation. -/
theorem v13FieldSwitchingInstantiated_iff_cellHalf
    {Ω : Type u} [Fintype Ω] {items : List (V13FieldedStep Ω)} :
    V13FieldSwitchingInstantiated items ↔
      V13FieldSwitchingCellHalf items := by
  exact v13FieldSwitchingInstantiatedFrom_iff_cellHalfFrom

/-- Recursive operational matching obligation: at each fielded step, every
successful point in each current history cell must be injectively matchable to
an unsuccessful point in the same cell. -/
def V13FieldSwitchingFailureMatchingFrom {Ω : Type u} [Fintype Ω]
    (hist : List (FiniteEvent Ω)) : List (V13FieldedStep Ω) → Prop
  | [] => True
  | item :: rest =>
      V13FieldFailureMatching item.field hist item.step ∧
        V13FieldSwitchingFailureMatchingFrom
          (hist ++ [item.step.successEvent]) rest

/-- Empty-history form of the recursive same-cell success-to-failure matching
obligation. -/
def V13FieldSwitchingFailureMatching {Ω : Type u} [Fintype Ω]
    (items : List (V13FieldedStep Ω)) : Prop :=
  V13FieldSwitchingFailureMatchingFrom ([] : List (FiniteEvent Ω)) items

/-- The whole fixed-field v13 switching interface is exactly the recursive
same-cell success-to-failure matching obligation. -/
theorem v13FieldSwitchingInstantiatedFrom_iff_failureMatchingFrom
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)} :
    V13FieldSwitchingInstantiatedFrom hist items ↔
      V13FieldSwitchingFailureMatchingFrom hist items := by
  induction items generalizing hist with
  | nil =>
      constructor <;> intro h <;> trivial
  | cons item rest ih =>
      constructor
      · intro h
        rcases h with ⟨hitem, hrest⟩
        exact ⟨v13FieldPrefixInstantiation_iff_failureMatching.mp hitem,
          (ih.mp hrest)⟩
      · intro h
        rcases h with ⟨hitem, hrest⟩
        exact ⟨v13FieldPrefixInstantiation_iff_failureMatching.mpr hitem,
          (ih.mpr hrest)⟩

/-- Empty-history form: fixed-field v13 switching is exactly recursive
same-cell success-to-failure matching. -/
theorem v13FieldSwitchingInstantiated_iff_failureMatching
    {Ω : Type u} [Fintype Ω] {items : List (V13FieldedStep Ω)} :
    V13FieldSwitchingInstantiated items ↔
      V13FieldSwitchingFailureMatching items := by
  exact v13FieldSwitchingInstantiatedFrom_iff_failureMatchingFrom

/-- Failure of the recursive same-cell matching obligation blocks fixed-field
v13 switching. -/
theorem not_v13FieldSwitchingInstantiatedFrom_of_not_failureMatchingFrom
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hfail : ¬ V13FieldSwitchingFailureMatchingFrom hist items) :
    ¬ V13FieldSwitchingInstantiatedFrom hist items := by
  intro h
  exact hfail (v13FieldSwitchingInstantiatedFrom_iff_failureMatchingFrom.mp h)

/-- Empty-history blocker from failure of recursive same-cell matching. -/
theorem not_v13FieldSwitchingInstantiated_of_not_failureMatching
    {Ω : Type u} [Fintype Ω] {items : List (V13FieldedStep Ω)}
    (hfail : ¬ V13FieldSwitchingFailureMatching items) :
    ¬ V13FieldSwitchingInstantiated items := by
  exact not_v13FieldSwitchingInstantiatedFrom_of_not_failureMatchingFrom hfail

/-- Extract the same-cell matching obligation for any later fielded step from
the recursive fielded matching proof. -/
theorem v13FieldFailureMatching_at_append_cons_of_failureMatchingFrom
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)}
    {pre : List (V13FieldedStep Ω)} {item : V13FieldedStep Ω}
    {suffix : List (V13FieldedStep Ω)}
    (h : V13FieldSwitchingFailureMatchingFrom hist (pre ++ item :: suffix)) :
    V13FieldFailureMatching item.field
      (hist ++ v13FieldedSuccessEvents pre) item.step := by
  induction pre generalizing hist with
  | nil =>
      simpa [v13FieldedSuccessEvents] using h.1
  | cons head tail ih =>
      have htail :
          V13FieldSwitchingFailureMatchingFrom
            (hist ++ [head.step.successEvent]) (tail ++ item :: suffix) := h.2
      have hitem := ih (hist := hist ++ [head.step.successEvent]) htail
      simpa [v13FieldedSuccessEvents, List.append_assoc] using hitem

/-- At any later fielded position, recursive same-cell matching supplies an
explicit failed prefix point in the same field cell for every successful prefix
point. -/
theorem exists_sameCell_failure_at_append_cons_of_failureMatchingFrom_success
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)}
    {pre : List (V13FieldedStep Ω)} {item : V13FieldedStep Ω}
    {suffix : List (V13FieldedStep Ω)}
    (hmatch :
      V13FieldSwitchingFailureMatchingFrom hist (pre ++ item :: suffix))
    {ω : Ω}
    (hhist : allEvents (hist ++ v13FieldedSuccessEvents pre) ω)
    (hsucc : item.step.successEvent.pred ω) :
    ∃ ω' : Ω,
      allEvents (hist ++ v13FieldedSuccessEvents pre) ω' ∧
        item.field.cellOf ω' = item.field.cellOf ω ∧
          ¬ item.step.successEvent.pred ω' := by
  exact
    exists_sameCell_failure_of_fieldFailureMatching_success
      (v13FieldFailureMatching_at_append_cons_of_failureMatchingFrom
        (hist := hist) (pre := pre) (item := item) (suffix := suffix) hmatch)
      hhist hsucc

/-- A single successful point whose accumulated-history field cell contains no
failed point blocks the recursive same-cell matching obligation. -/
theorem not_v13FieldSwitchingFailureMatchingFrom_append_cons_of_success_without_sameCell_failure
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)}
    {pre : List (V13FieldedStep Ω)} {item : V13FieldedStep Ω}
    {suffix : List (V13FieldedStep Ω)} {ω : Ω}
    (hhist : allEvents (hist ++ v13FieldedSuccessEvents pre) ω)
    (hsucc : item.step.successEvent.pred ω)
    (hnoFailure :
      ∀ ⦃ω' : Ω⦄,
        allEvents (hist ++ v13FieldedSuccessEvents pre) ω' →
          item.field.cellOf ω' = item.field.cellOf ω →
            item.step.successEvent.pred ω') :
    ¬ V13FieldSwitchingFailureMatchingFrom hist (pre ++ item :: suffix) := by
  intro hmatch
  rcases exists_sameCell_failure_at_append_cons_of_failureMatchingFrom_success
      hmatch hhist hsucc with
    ⟨ω', hhist', hcell', hfail'⟩
  exact hfail' (hnoFailure hhist' hcell')

/-- At any later fielded position, a recursive matching proof on a positive
next-success prefix rules out a supplied field that determines the next success
bit on the accumulated history support. -/
theorem not_v13HistoryFieldDeterminesSuccessOn_at_append_cons_of_failureMatchingFrom_positive_success
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)}
    {pre : List (V13FieldedStep Ω)} {item : V13FieldedStep Ω}
    {suffix : List (V13FieldedStep Ω)}
    (hmatch :
      V13FieldSwitchingFailureMatchingFrom hist (pre ++ item :: suffix))
    (hpos :
      0 < finiteHistoryCount Ω
        ((hist ++ v13FieldedSuccessEvents pre) ++ [item.step.successEvent])) :
    ¬ V13HistoryFieldDeterminesSuccessOn item.field
      (hist ++ v13FieldedSuccessEvents pre) item.step := by
  exact
    not_v13HistoryFieldDeterminesSuccessOn_of_failureMatching_positive_success
      (v13FieldFailureMatching_at_append_cons_of_failureMatchingFrom
        (hist := hist) (pre := pre) (item := item) (suffix := suffix) hmatch)
      hpos

/-- At any later fielded position, a recursive matching proof on a positive
next-success prefix rules out a supplied field that globally determines the
next success bit. -/
theorem not_v13HistoryFieldDeterminesSuccess_at_append_cons_of_failureMatchingFrom_positive_success
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)}
    {pre : List (V13FieldedStep Ω)} {item : V13FieldedStep Ω}
    {suffix : List (V13FieldedStep Ω)}
    (hmatch :
      V13FieldSwitchingFailureMatchingFrom hist (pre ++ item :: suffix))
    (hpos :
      0 < finiteHistoryCount Ω
        ((hist ++ v13FieldedSuccessEvents pre) ++ [item.step.successEvent])) :
    ¬ V13HistoryFieldDeterminesSuccess item.field item.step := by
  intro hdet
  exact
    not_v13HistoryFieldDeterminesSuccessOn_at_append_cons_of_failureMatchingFrom_positive_success
      hmatch hpos
      (v13HistoryFieldDeterminesSuccessOn_of_determinesSuccess hdet)

/-- A prefix-relative success-determining later field with positive
next-success mass blocks the recursive same-cell matching obligation itself. -/
theorem not_v13FieldSwitchingFailureMatchingFrom_append_cons_of_fieldDeterminesSuccessOn_positive_success
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)}
    {pre : List (V13FieldedStep Ω)} {item : V13FieldedStep Ω}
    {suffix : List (V13FieldedStep Ω)}
    (hdet :
      V13HistoryFieldDeterminesSuccessOn item.field
        (hist ++ v13FieldedSuccessEvents pre) item.step)
    (hpos :
      0 < finiteHistoryCount Ω
        ((hist ++ v13FieldedSuccessEvents pre) ++ [item.step.successEvent])) :
    ¬ V13FieldSwitchingFailureMatchingFrom hist (pre ++ item :: suffix) := by
  intro hmatch
  exact
    not_v13HistoryFieldDeterminesSuccessOn_at_append_cons_of_failureMatchingFrom_positive_success
      hmatch hpos hdet

/-- A globally success-determining later field with positive next-success mass
blocks the recursive same-cell matching obligation itself. -/
theorem not_v13FieldSwitchingFailureMatchingFrom_append_cons_of_fieldDeterminesSuccess_positive_success
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)}
    {pre : List (V13FieldedStep Ω)} {item : V13FieldedStep Ω}
    {suffix : List (V13FieldedStep Ω)}
    (hdet : V13HistoryFieldDeterminesSuccess item.field item.step)
    (hpos :
      0 < finiteHistoryCount Ω
        ((hist ++ v13FieldedSuccessEvents pre) ++ [item.step.successEvent])) :
    ¬ V13FieldSwitchingFailureMatchingFrom hist (pre ++ item :: suffix) := by
  exact
    not_v13FieldSwitchingFailureMatchingFrom_append_cons_of_fieldDeterminesSuccessOn_positive_success
      (hdet :=
        v13HistoryFieldDeterminesSuccessOn_of_determinesSuccess
          (hist := hist ++ v13FieldedSuccessEvents pre) hdet)
      hpos

/-- Fixed-field v13 certificates instantiate the generic sequential
half-admissibility interface. -/
theorem sequentialHalfAdmissibleFrom_of_v13FieldSwitchingInstantiatedFrom
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (h : V13FieldSwitchingInstantiatedFrom hist items) :
    SequentialHalfAdmissibleFrom hist (v13FieldedSuccessEvents items) := by
  induction items generalizing hist with
  | nil =>
      trivial
  | cons item rest ih =>
      rcases h with ⟨hitem, hrest⟩
      exact ⟨by
        simpa [PrefixHalfStep] using
          prefixHalfStep_of_v13FieldPrefixInstantiation hitem, ih hrest⟩

/-- Fixed-field v13 certificates imply the finite tower product bound from an
arbitrary existing success history. -/
theorem v13_product_bound_of_fieldInstantiatedFrom
    {Ω : Type u} [Fintype Ω]
    (hist : List (FiniteEvent Ω)) (items : List (V13FieldedStep Ω))
    (h : V13FieldSwitchingInstantiatedFrom hist items) :
    2 ^ items.length * finiteHistoryCount Ω (hist ++ v13FieldedSuccessEvents items) ≤
      finiteHistoryCount Ω hist := by
  have hadm :
      SequentialHalfAdmissibleFrom hist (v13FieldedSuccessEvents items) :=
    sequentialHalfAdmissibleFrom_of_v13FieldSwitchingInstantiatedFrom h
  simpa [v13FieldedSuccessEvents_length] using
    finiteHistory_product_bound_of_sequentialHalfFrom hist
      (v13FieldedSuccessEvents items) hadm

/-- Fixed-field v13 certificates imply the finite tower product bound from the
empty success history. -/
theorem v13_product_bound_of_fieldInstantiated
    {Ω : Type u} [Fintype Ω]
    (items : List (V13FieldedStep Ω))
    (h : V13FieldSwitchingInstantiated items) :
    2 ^ items.length * finiteHistoryCount Ω (v13FieldedSuccessEvents items) ≤
      finiteHistoryCount Ω ([] : List (FiniteEvent Ω)) := by
  simpa [V13FieldSwitchingInstantiated] using
    v13_product_bound_of_fieldInstantiatedFrom
      ([] : List (FiniteEvent Ω)) items h

/-- Recursive same-cell matchings imply the finite tower product bound. -/
theorem v13_product_bound_of_fieldFailureMatchingFrom
    {Ω : Type u} [Fintype Ω]
    (hist : List (FiniteEvent Ω)) (items : List (V13FieldedStep Ω))
    (h : V13FieldSwitchingFailureMatchingFrom hist items) :
    2 ^ items.length * finiteHistoryCount Ω (hist ++ v13FieldedSuccessEvents items) ≤
      finiteHistoryCount Ω hist := by
  exact v13_product_bound_of_fieldInstantiatedFrom hist items
    (v13FieldSwitchingInstantiatedFrom_iff_failureMatchingFrom.mpr h)

/-- Empty-history tower product bound from recursive same-cell matchings. -/
theorem v13_product_bound_of_fieldFailureMatching
    {Ω : Type u} [Fintype Ω]
    (items : List (V13FieldedStep Ω))
    (h : V13FieldSwitchingFailureMatching items) :
    2 ^ items.length * finiteHistoryCount Ω (v13FieldedSuccessEvents items) ≤
      finiteHistoryCount Ω ([] : List (FiniteEvent Ω)) := by
  simpa [V13FieldSwitchingFailureMatching] using
    v13_product_bound_of_fieldFailureMatchingFrom
      ([] : List (FiniteEvent Ω)) items h

/-- A global tower-product violation blocks any fixed-field v13 instantiation,
regardless of the individual cells. -/
theorem not_v13FieldSwitchingInstantiatedFrom_of_product_bound_violation
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hbad :
      ¬ 2 ^ items.length *
          finiteHistoryCount Ω (hist ++ v13FieldedSuccessEvents items) ≤
        finiteHistoryCount Ω hist) :
    ¬ V13FieldSwitchingInstantiatedFrom hist items := by
  intro h
  exact hbad (v13_product_bound_of_fieldInstantiatedFrom hist items h)

/-- Empty-history fixed-field v13 blocker from failure of the global
tower-product inequality. -/
theorem not_v13FieldSwitchingInstantiated_of_product_bound_violation
    {Ω : Type u} [Fintype Ω]
    {items : List (V13FieldedStep Ω)}
    (hbad :
      ¬ 2 ^ items.length * finiteHistoryCount Ω (v13FieldedSuccessEvents items) ≤
        finiteHistoryCount Ω ([] : List (FiniteEvent Ω))) :
    ¬ V13FieldSwitchingInstantiated items := by
  intro h
  exact hbad (v13_product_bound_of_fieldInstantiated items h)

/-- A global tower-product violation also blocks the operational recursive
same-cell matching obligation directly. -/
theorem not_v13FieldSwitchingFailureMatchingFrom_of_product_bound_violation
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hbad :
      ¬ 2 ^ items.length *
          finiteHistoryCount Ω (hist ++ v13FieldedSuccessEvents items) ≤
        finiteHistoryCount Ω hist) :
    ¬ V13FieldSwitchingFailureMatchingFrom hist items := by
  intro hmatch
  exact hbad (v13_product_bound_of_fieldFailureMatchingFrom hist items hmatch)

/-- Empty-history tower-product blocker for the operational recursive same-cell
matching obligation. -/
theorem not_v13FieldSwitchingFailureMatching_of_product_bound_violation
    {Ω : Type u} [Fintype Ω]
    {items : List (V13FieldedStep Ω)}
    (hbad :
      ¬ 2 ^ items.length * finiteHistoryCount Ω (v13FieldedSuccessEvents items) ≤
        finiteHistoryCount Ω ([] : List (FiniteEvent Ω))) :
    ¬ V13FieldSwitchingFailureMatching items := by
  intro hmatch
  exact hbad (v13_product_bound_of_fieldFailureMatching items hmatch)

/-- One failed fixed-field prefix certificate blocks the corresponding
fixed-field switching suffix. -/
theorem not_v13FieldSwitchingInstantiatedFrom_cons_of_not_fieldPrefixInstantiation
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)}
    {item : V13FieldedStep Ω} {rest : List (V13FieldedStep Ω)}
    (hfail : ¬ V13FieldPrefixInstantiation item.field hist item.step) :
    ¬ V13FieldSwitchingInstantiatedFrom hist (item :: rest) := by
  intro h
  exact hfail h.1

/-- If the supplied first field in a fielded suffix determines the next success
event on the current history support and that next-success prefix has positive
mass, the whole fielded suffix is blocked. -/
theorem not_v13FieldSwitchingInstantiatedFrom_cons_of_fieldDeterminesSuccessOn_positive_success
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {item : V13FieldedStep Ω}
    {rest : List (V13FieldedStep Ω)}
    (hdet : V13HistoryFieldDeterminesSuccessOn item.field hist item.step)
    (hpos : 0 < finiteHistoryCount Ω (hist ++ [item.step.successEvent])) :
    ¬ V13FieldSwitchingInstantiatedFrom hist (item :: rest) := by
  exact not_v13FieldSwitchingInstantiatedFrom_cons_of_not_fieldPrefixInstantiation
    (not_v13FieldPrefixInstantiation_of_fieldDeterminesSuccessOn_positive_success
      hdet hpos)

/-- If the supplied first field in a fielded suffix globally determines the next
success event and that next-success prefix has positive mass, the whole fielded
suffix is blocked. -/
theorem not_v13FieldSwitchingInstantiatedFrom_cons_of_fieldDeterminesSuccess_positive_success
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {item : V13FieldedStep Ω}
    {rest : List (V13FieldedStep Ω)}
    (hdet : V13HistoryFieldDeterminesSuccess item.field item.step)
    (hpos : 0 < finiteHistoryCount Ω (hist ++ [item.step.successEvent])) :
    ¬ V13FieldSwitchingInstantiatedFrom hist (item :: rest) := by
  exact
    not_v13FieldSwitchingInstantiatedFrom_cons_of_fieldDeterminesSuccessOn_positive_success
      (v13HistoryFieldDeterminesSuccessOn_of_determinesSuccess hdet) hpos

/-- A failed fixed-field prefix certificate at any later position blocks the
whole fielded switching list.  The history at the failed item is exactly the
incoming history extended by the success events of the preceding fielded
prefix. -/
theorem not_v13FieldSwitchingInstantiatedFrom_append_cons_of_not_fieldPrefixInstantiation
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)}
    {pre : List (V13FieldedStep Ω)} {item : V13FieldedStep Ω}
    {suffix : List (V13FieldedStep Ω)}
    (hfail :
      ¬ V13FieldPrefixInstantiation item.field
          (hist ++ v13FieldedSuccessEvents pre) item.step) :
    ¬ V13FieldSwitchingInstantiatedFrom hist (pre ++ item :: suffix) := by
  induction pre generalizing hist with
  | nil =>
      have hfail' :
          ¬ V13FieldPrefixInstantiation item.field hist item.step := by
        simpa [v13FieldedSuccessEvents] using hfail
      simpa using
        (not_v13FieldSwitchingInstantiatedFrom_cons_of_not_fieldPrefixInstantiation
          (hist := hist) (item := item) (rest := suffix) hfail')
  | cons head tail ih =>
      intro h
      have hfail' :
          ¬ V13FieldPrefixInstantiation item.field
              ((hist ++ [head.step.successEvent]) ++
                v13FieldedSuccessEvents tail) item.step := by
        simpa [v13FieldedSuccessEvents, List.append_assoc] using hfail
      exact ih (hist := hist ++ [head.step.successEvent]) hfail' h.2

/-- A single successful point whose accumulated-history field cell contains no
failed point blocks the whole fixed-field switching instantiation. -/
theorem not_v13FieldSwitchingInstantiatedFrom_append_cons_of_success_without_sameCell_failure
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)}
    {pre : List (V13FieldedStep Ω)} {item : V13FieldedStep Ω}
    {suffix : List (V13FieldedStep Ω)} {ω : Ω}
    (hhist : allEvents (hist ++ v13FieldedSuccessEvents pre) ω)
    (hsucc : item.step.successEvent.pred ω)
    (hnoFailure :
      ∀ ⦃ω' : Ω⦄,
        allEvents (hist ++ v13FieldedSuccessEvents pre) ω' →
          item.field.cellOf ω' = item.field.cellOf ω →
            item.step.successEvent.pred ω') :
    ¬ V13FieldSwitchingInstantiatedFrom hist (pre ++ item :: suffix) := by
  exact
    not_v13FieldSwitchingInstantiatedFrom_append_cons_of_not_fieldPrefixInstantiation
      (hist := hist) (pre := pre) (item := item) (suffix := suffix)
      (not_v13FieldPrefixInstantiation_of_success_without_sameCell_failure
        (field := item.field) (hist := hist ++ v13FieldedSuccessEvents pre)
        (step := item.step) hhist hsucc hnoFailure)

/-- If any later supplied field determines its next success event on the
accumulated history support and the corresponding next-success prefix has
positive mass, the whole fielded switching list is blocked. -/
theorem not_v13FieldSwitchingInstantiatedFrom_append_cons_of_fieldDeterminesSuccessOn_positive_success
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)}
    {pre : List (V13FieldedStep Ω)} {item : V13FieldedStep Ω}
    {suffix : List (V13FieldedStep Ω)}
    (hdet :
      V13HistoryFieldDeterminesSuccessOn item.field
        (hist ++ v13FieldedSuccessEvents pre) item.step)
    (hpos :
      0 < finiteHistoryCount Ω
        ((hist ++ v13FieldedSuccessEvents pre) ++ [item.step.successEvent])) :
    ¬ V13FieldSwitchingInstantiatedFrom hist (pre ++ item :: suffix) := by
  exact
    not_v13FieldSwitchingInstantiatedFrom_append_cons_of_not_fieldPrefixInstantiation
      (hist := hist) (pre := pre) (item := item) (suffix := suffix)
      (not_v13FieldPrefixInstantiation_of_fieldDeterminesSuccessOn_positive_success
        (Ω := Ω) (field := item.field)
        (hist := hist ++ v13FieldedSuccessEvents pre) (step := item.step)
        hdet hpos)

/-- If any later supplied field globally determines its next success event and
the corresponding next-success prefix has positive mass, the whole fielded
switching list is blocked. -/
theorem not_v13FieldSwitchingInstantiatedFrom_append_cons_of_fieldDeterminesSuccess_positive_success
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)}
    {pre : List (V13FieldedStep Ω)} {item : V13FieldedStep Ω}
    {suffix : List (V13FieldedStep Ω)}
    (hdet : V13HistoryFieldDeterminesSuccess item.field item.step)
    (hpos :
      0 < finiteHistoryCount Ω
        ((hist ++ v13FieldedSuccessEvents pre) ++ [item.step.successEvent])) :
    ¬ V13FieldSwitchingInstantiatedFrom hist (pre ++ item :: suffix) := by
  exact
    not_v13FieldSwitchingInstantiatedFrom_append_cons_of_fieldDeterminesSuccessOn_positive_success
      (hdet :=
        v13HistoryFieldDeterminesSuccessOn_of_determinesSuccess
          (hist := hist ++ v13FieldedSuccessEvents pre) hdet)
      hpos

/-- A success-revealing fielded step with positive next-success mass blocks the
entire fixed-field switching suffix. -/
theorem not_v13FieldSwitchingInstantiatedFrom_successField_cons_of_positive_success
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω} {rest : List (V13FieldedStep Ω)}
    (hpos : 0 < finiteHistoryCount Ω (hist ++ [step.successEvent])) :
    ¬ V13FieldSwitchingInstantiatedFrom hist
      (v13SuccessFieldedStep step :: rest) := by
  exact
    not_v13FieldSwitchingInstantiatedFrom_cons_of_not_fieldPrefixInstantiation
      (not_v13FieldPrefixInstantiation_successHistoryField_of_positive_success hpos)

/-- Recursive v13 instantiation from an existing success history: every next
coordinate has an atom-ledger certificate relative to the current success
prefix. -/
def V13SwitchingInstantiatedFrom {Ω : Type u} [Fintype Ω]
    (hist : List (FiniteEvent Ω)) : List (V13SwitchedStep Ω) → Prop
  | [] => True
  | step :: rest =>
      V13PrefixInstantiated hist step ∧
        V13SwitchingInstantiatedFrom (hist ++ [step.successEvent]) rest

/-- Recursive v13 instantiation from the empty success history. -/
def V13SwitchingInstantiated {Ω : Type u} [Fintype Ω]
    (steps : List (V13SwitchedStep Ω)) : Prop :=
  V13SwitchingInstantiatedFrom ([] : List (FiniteEvent Ω)) steps

/-- Recursive semantic v13 instantiation from an existing success history:
every next coordinate has a concrete cell-map certificate relative to the
current success prefix. -/
def V13ConcreteSwitchingInstantiatedFrom {Ω : Type u} [Fintype Ω]
    (hist : List (FiniteEvent Ω)) : List (V13SwitchedStep Ω) → Prop
  | [] => True
  | step :: rest =>
      V13ConcretePrefixInstantiated hist step ∧
        V13ConcreteSwitchingInstantiatedFrom (hist ++ [step.successEvent]) rest

/-- Recursive semantic v13 instantiation from the empty success history. -/
def V13ConcreteSwitchingInstantiated {Ω : Type u} [Fintype Ω]
    (steps : List (V13SwitchedStep Ω)) : Prop :=
  V13ConcreteSwitchingInstantiatedFrom ([] : List (FiniteEvent Ω)) steps

/-- Concrete semantic v13 certificates supply the abstract v13 summary
certificates. -/
theorem v13SwitchingInstantiatedFrom_of_concreteSwitchingInstantiatedFrom
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {steps : List (V13SwitchedStep Ω)}
    (h : V13ConcreteSwitchingInstantiatedFrom hist steps) :
    V13SwitchingInstantiatedFrom hist steps := by
  induction steps generalizing hist with
  | nil =>
      trivial
  | cons step rest ih =>
      rcases h with ⟨hstep, hrest⟩
      exact ⟨v13PrefixInstantiated_of_v13ConcretePrefixInstantiated hstep,
        ih hrest⟩

/-- V13 atom-ledger certificates instantiate the generic sequential
half-admissibility interface. -/
theorem sequentialHalfAdmissibleFrom_of_v13SwitchingInstantiatedFrom
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {steps : List (V13SwitchedStep Ω)}
    (h : V13SwitchingInstantiatedFrom hist steps) :
    SequentialHalfAdmissibleFrom hist (v13SuccessEvents steps) := by
  induction steps generalizing hist with
  | nil =>
      trivial
  | cons step rest ih =>
      rcases h with ⟨hstep, hrest⟩
      exact ⟨by
        simpa [PrefixHalfStep] using
          prefixHalfStep_of_v13PrefixInstantiated hstep, ih hrest⟩

/-- Conversely, generic sequential half-admissibility is enough to build the
abstract v13 atom-ledger instantiation, because every prefix half-step can be
represented by a one-cell ledger.  This pins the abstract v13 interface as no
stronger than the generic sequential condition. -/
theorem v13SwitchingInstantiatedFrom_of_sequentialHalfAdmissibleFrom
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {steps : List (V13SwitchedStep Ω)}
    (h : SequentialHalfAdmissibleFrom hist (v13SuccessEvents steps)) :
    V13SwitchingInstantiatedFrom hist steps := by
  induction steps generalizing hist with
  | nil =>
      trivial
  | cons step rest ih =>
      rcases h with ⟨hstep, hrest⟩
      have hprefix : PrefixHalfStep hist step.successEvent := by
        simpa [PrefixHalfStep] using hstep
      exact ⟨⟨v13PrefixInstantiation_of_prefixHalfStep hprefix⟩, ih hrest⟩

/-- The whole abstract v13 atom-ledger switching interface is exactly generic
sequential half-admissibility of the induced success events. -/
theorem v13SwitchingInstantiatedFrom_iff_sequentialHalfAdmissibleFrom
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {steps : List (V13SwitchedStep Ω)} :
    V13SwitchingInstantiatedFrom hist steps ↔
      SequentialHalfAdmissibleFrom hist (v13SuccessEvents steps) := by
  constructor
  · exact sequentialHalfAdmissibleFrom_of_v13SwitchingInstantiatedFrom
  · exact v13SwitchingInstantiatedFrom_of_sequentialHalfAdmissibleFrom

/-- Empty-history form: abstract v13 atom-ledger switching is equivalent to
generic sequential half-admissibility of the success-event list. -/
theorem v13SwitchingInstantiated_iff_sequentialHalfAdmissible
    {Ω : Type u} [Fintype Ω] {steps : List (V13SwitchedStep Ω)} :
    V13SwitchingInstantiated steps ↔
      SequentialHalfAdmissible (v13SuccessEvents steps) := by
  exact v13SwitchingInstantiatedFrom_iff_sequentialHalfAdmissibleFrom

/-- Generic sequential half-admissibility is also enough to build the
existential concrete-cell v13 instantiation, by choosing the constant cell map
at every prefix. -/
theorem v13ConcreteSwitchingInstantiatedFrom_of_sequentialHalfAdmissibleFrom
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {steps : List (V13SwitchedStep Ω)}
    (h : SequentialHalfAdmissibleFrom hist (v13SuccessEvents steps)) :
    V13ConcreteSwitchingInstantiatedFrom hist steps := by
  induction steps generalizing hist with
  | nil =>
      trivial
  | cons step rest ih =>
      rcases h with ⟨hstep, hrest⟩
      have hprefix : PrefixHalfStep hist step.successEvent := by
        simpa [PrefixHalfStep] using hstep
      exact ⟨⟨v13ConcretePrefixInstantiation_of_prefixHalfStep hprefix⟩, ih hrest⟩

/-- The existential concrete-cell v13 switching interface is exactly generic
sequential half-admissibility of the induced success events.  Semantic force
only appears once the history fields are externally fixed. -/
theorem v13ConcreteSwitchingInstantiatedFrom_iff_sequentialHalfAdmissibleFrom
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {steps : List (V13SwitchedStep Ω)} :
    V13ConcreteSwitchingInstantiatedFrom hist steps ↔
      SequentialHalfAdmissibleFrom hist (v13SuccessEvents steps) := by
  constructor
  · intro h
    exact sequentialHalfAdmissibleFrom_of_v13SwitchingInstantiatedFrom
      (v13SwitchingInstantiatedFrom_of_concreteSwitchingInstantiatedFrom h)
  · exact v13ConcreteSwitchingInstantiatedFrom_of_sequentialHalfAdmissibleFrom

/-- Empty-history form: existential concrete-cell v13 switching is equivalent
to generic sequential half-admissibility of the success-event list. -/
theorem v13ConcreteSwitchingInstantiated_iff_sequentialHalfAdmissible
    {Ω : Type u} [Fintype Ω] {steps : List (V13SwitchedStep Ω)} :
    V13ConcreteSwitchingInstantiated steps ↔
      SequentialHalfAdmissible (v13SuccessEvents steps) := by
  exact v13ConcreteSwitchingInstantiatedFrom_iff_sequentialHalfAdmissibleFrom

/-- V13 atom-ledger certificates imply the finite tower product bound from an
arbitrary existing success history. -/
theorem v13_product_bound_of_instantiatedFrom
    {Ω : Type u} [Fintype Ω]
    (hist : List (FiniteEvent Ω)) (steps : List (V13SwitchedStep Ω))
    (h : V13SwitchingInstantiatedFrom hist steps) :
    2 ^ steps.length * finiteHistoryCount Ω (hist ++ v13SuccessEvents steps) ≤
      finiteHistoryCount Ω hist := by
  have hadm :
      SequentialHalfAdmissibleFrom hist (v13SuccessEvents steps) :=
    sequentialHalfAdmissibleFrom_of_v13SwitchingInstantiatedFrom h
  simpa [v13SuccessEvents_length] using
    finiteHistory_product_bound_of_sequentialHalfFrom hist
      (v13SuccessEvents steps) hadm

/-- V13 atom-ledger certificates imply the finite tower product bound from the
empty success history. -/
theorem v13_product_bound_of_instantiated
    {Ω : Type u} [Fintype Ω]
    (steps : List (V13SwitchedStep Ω))
    (h : V13SwitchingInstantiated steps) :
    2 ^ steps.length * finiteHistoryCount Ω (v13SuccessEvents steps) ≤
      finiteHistoryCount Ω ([] : List (FiniteEvent Ω)) := by
  simpa [V13SwitchingInstantiated] using
    v13_product_bound_of_instantiatedFrom
      ([] : List (FiniteEvent Ω)) steps h

/-- Semantic v13 cell-map certificates imply the finite tower product bound
from an arbitrary existing success history. -/
theorem v13_product_bound_of_concreteInstantiatedFrom
    {Ω : Type u} [Fintype Ω]
    (hist : List (FiniteEvent Ω)) (steps : List (V13SwitchedStep Ω))
    (h : V13ConcreteSwitchingInstantiatedFrom hist steps) :
    2 ^ steps.length * finiteHistoryCount Ω (hist ++ v13SuccessEvents steps) ≤
      finiteHistoryCount Ω hist := by
  exact v13_product_bound_of_instantiatedFrom hist steps
    (v13SwitchingInstantiatedFrom_of_concreteSwitchingInstantiatedFrom h)

/-- Semantic v13 cell-map certificates imply the finite tower product bound
from the empty success history. -/
theorem v13_product_bound_of_concreteInstantiated
    {Ω : Type u} [Fintype Ω]
    (steps : List (V13SwitchedStep Ω))
    (h : V13ConcreteSwitchingInstantiated steps) :
    2 ^ steps.length * finiteHistoryCount Ω (v13SuccessEvents steps) ≤
      finiteHistoryCount Ω ([] : List (FiniteEvent Ω)) := by
  simpa [V13ConcreteSwitchingInstantiated] using
    v13_product_bound_of_concreteInstantiatedFrom
      ([] : List (FiniteEvent Ω)) steps h

/-- A global tower-product violation blocks any v13 abstract atom-ledger
instantiation. -/
theorem not_v13SwitchingInstantiatedFrom_of_product_bound_violation
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {steps : List (V13SwitchedStep Ω)}
    (hbad :
      ¬ 2 ^ steps.length *
          finiteHistoryCount Ω (hist ++ v13SuccessEvents steps) ≤
        finiteHistoryCount Ω hist) :
    ¬ V13SwitchingInstantiatedFrom hist steps := by
  intro h
  exact hbad (v13_product_bound_of_instantiatedFrom hist steps h)

/-- Empty-history v13 abstract atom-ledger blocker from failure of the global
tower-product inequality. -/
theorem not_v13SwitchingInstantiated_of_product_bound_violation
    {Ω : Type u} [Fintype Ω]
    {steps : List (V13SwitchedStep Ω)}
    (hbad :
      ¬ 2 ^ steps.length * finiteHistoryCount Ω (v13SuccessEvents steps) ≤
        finiteHistoryCount Ω ([] : List (FiniteEvent Ω))) :
    ¬ V13SwitchingInstantiated steps := by
  intro h
  exact hbad (v13_product_bound_of_instantiated steps h)

/-- A global tower-product violation blocks any semantic concrete-cell v13
instantiation. -/
theorem not_v13ConcreteSwitchingInstantiatedFrom_of_product_bound_violation
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {steps : List (V13SwitchedStep Ω)}
    (hbad :
      ¬ 2 ^ steps.length *
          finiteHistoryCount Ω (hist ++ v13SuccessEvents steps) ≤
        finiteHistoryCount Ω hist) :
    ¬ V13ConcreteSwitchingInstantiatedFrom hist steps := by
  intro h
  exact hbad (v13_product_bound_of_concreteInstantiatedFrom hist steps h)

/-- Empty-history concrete-cell v13 blocker from failure of the global
tower-product inequality. -/
theorem not_v13ConcreteSwitchingInstantiated_of_product_bound_violation
    {Ω : Type u} [Fintype Ω]
    {steps : List (V13SwitchedStep Ω)}
    (hbad :
      ¬ 2 ^ steps.length * finiteHistoryCount Ω (v13SuccessEvents steps) ≤
        finiteHistoryCount Ω ([] : List (FiniteEvent Ω))) :
    ¬ V13ConcreteSwitchingInstantiated steps := by
  intro h
  exact hbad (v13_product_bound_of_concreteInstantiated steps h)

/-- One failed prefix half-step blocks the corresponding v13 atom-ledger
instantiation for the whole remaining switched suffix. -/
theorem not_v13SwitchingInstantiatedFrom_cons_of_not_prefixHalfStep
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω} {rest : List (V13SwitchedStep Ω)}
    (hfail : ¬ PrefixHalfStep hist step.successEvent) :
    ¬ V13SwitchingInstantiatedFrom hist (step :: rest) := by
  intro h
  exact not_v13PrefixInstantiated_of_not_prefixHalfStep hfail h.1

section BoolPairRepeatedStep

/-- A concrete repeated-coordinate switched step on the Boolean square.  Exact
success is the first-coordinate event. -/
def v13BoolPairRepeatedStep : V13SwitchedStep (Bool × Bool) where
  coordinate := 0
  observerBit := fun ω => ω.1
  targetBit := fun _ => true

/-- The fixed field that reveals the same first coordinate used by the success
event. -/
def v13BoolPairFirstCoordinateField : V13HistoryField (Bool × Bool) where
  Cell := Bool
  cellOf := fun ω => ω.1

/-- A fixed field that reveals the second coordinate.  It does not globally
determine first-coordinate success, but it does after conditioning on the
diagonal history event below. -/
def v13BoolPairSecondCoordinateField : V13HistoryField (Bool × Bool) where
  Cell := Bool
  cellOf := fun ω => ω.2

/-- The diagonal history event `first = second` on the Boolean square. -/
def v13BoolPairDiagonalEvent : FiniteEvent (Bool × Bool) where
  pred := fun ω => ω.1 = ω.2
  decidablePred := fun _ => inferInstance

/-- The first-coordinate field determines exact success for the repeated
first-coordinate switched step. -/
theorem v13BoolPairFirstCoordinateField_determinesSuccess :
    V13HistoryFieldDeterminesSuccess v13BoolPairFirstCoordinateField
      v13BoolPairRepeatedStep := by
  intro ω ω' hcell hsucc
  cases ω with
  | mk a b =>
      cases ω' with
      | mk a' b' =>
          cases a <;> cases a' <;> cases b <;> cases b' <;>
            simp [v13BoolPairFirstCoordinateField, v13BoolPairRepeatedStep,
              V13SwitchedStep.successEvent] at hcell hsucc ⊢

/-- The second-coordinate field does not globally determine first-coordinate
success: outside the diagonal, points with the same second coordinate can have
different first-coordinate success values. -/
theorem not_v13BoolPairSecondCoordinateField_determinesSuccess :
    ¬ V13HistoryFieldDeterminesSuccess v13BoolPairSecondCoordinateField
      v13BoolPairRepeatedStep := by
  intro hdet
  have htarget :
      v13BoolPairRepeatedStep.successEvent.pred (false, true) :=
    hdet (ω := (true, true)) (ω' := (false, true)) rfl (by decide)
  simp [v13BoolPairRepeatedStep, V13SwitchedStep.successEvent] at htarget

/-- After conditioning on the diagonal history event, the second-coordinate
field does determine first-coordinate success.  This is the prefix-relative
case that a purely global blocker would miss. -/
theorem v13BoolPairSecondCoordinateField_determinesSuccessOn_diagonal :
    V13HistoryFieldDeterminesSuccessOn v13BoolPairSecondCoordinateField
      [v13BoolPairDiagonalEvent] v13BoolPairRepeatedStep := by
  intro ω ω' hω hω' hcell hsucc
  cases ω with
  | mk a b =>
      cases ω' with
      | mk a' b' =>
          cases a <;> cases a' <;> cases b <;> cases b' <;>
            simp [v13BoolPairSecondCoordinateField, v13BoolPairRepeatedStep,
              v13BoolPairDiagonalEvent, V13SwitchedStep.successEvent,
              allEvents] at hω hω' hcell hsucc ⊢

/-- The first-coordinate switched step paired with the fixed field that reveals
that same coordinate. -/
def v13BoolPairFirstCoordinateFieldedStep : V13FieldedStep (Bool × Bool) where
  field := v13BoolPairFirstCoordinateField
  step := v13BoolPairRepeatedStep

/-- The one-cell field on the Boolean square.  It is the honest finite field
that certifies the first global half-success cut for the repeated-coordinate
test case. -/
def v13BoolPairUnitField : V13HistoryField (Bool × Bool) where
  Cell := PUnit
  cellOf := fun _ => PUnit.unit

/-- The repeated-coordinate switched step paired with the one-cell field. -/
def v13BoolPairUnitFieldedStep : V13FieldedStep (Bool × Bool) where
  field := v13BoolPairUnitField
  step := v13BoolPairRepeatedStep

/-- The repeated-step success event has numerator `2` over the four-point
Boolean square. -/
theorem v13BoolPairRepeatedStep_success_count :
    finiteHistoryCount (Bool × Bool) [v13BoolPairRepeatedStep.successEvent] = 2 := by
  decide

/-- On the diagonal prefix, first-coordinate success has positive mass. -/
theorem v13BoolPairDiagonal_repeatedStep_success_count :
    finiteHistoryCount (Bool × Bool)
      ([v13BoolPairDiagonalEvent] ++ [v13BoolPairRepeatedStep.successEvent]) = 1 := by
  decide

/-- The first success event is globally half-admissible from the empty history. -/
theorem prefixHalfStep_v13BoolPairRepeatedStep_empty :
    PrefixHalfStep ([] : List (FiniteEvent (Bool × Bool)))
      v13BoolPairRepeatedStep.successEvent := by
  rw [PrefixHalfStep]
  decide

/-- The one-cell field certifies the first repeated-coordinate step from the
empty history: the first-coordinate success event has exactly half the four
Boolean-square points. -/
theorem v13FieldPrefixInstantiation_unitField_empty :
    V13FieldPrefixInstantiation v13BoolPairUnitField
      ([] : List (FiniteEvent (Bool × Bool))) v13BoolPairRepeatedStep := by
  refine v13FieldPrefixInstantiation_of_cellHalf ?_
  intro cell
  cases cell
  decide

/-- In the first-coordinate field, the `true` cell has two points before the
step. -/
theorem v13BoolPairFirstCoordinateField_prefix_true_count :
    v13ConcretePrefixCount (Ω := Bool × Bool)
      ([] : List (FiniteEvent (Bool × Bool)))
      v13BoolPairFirstCoordinateField.cellOf true = 2 := by
  decide

/-- In the first-coordinate field, the `true` cell is entirely successful for
the first-coordinate exact-success event. -/
theorem v13BoolPairFirstCoordinateField_success_true_count :
    v13ConcreteSuccessCount (Ω := Bool × Bool)
      ([] : List (FiniteEvent (Bool × Bool))) v13BoolPairRepeatedStep
      v13BoolPairFirstCoordinateField.cellOf true = 2 := by
  decide

/-- Global half-success does not imply the fixed-field cellwise half-success
obligation.  The field that reveals the successful first coordinate has a
`true` cell where success has conditional mass `1`. -/
theorem not_v13FieldPrefixInstantiation_firstCoordinateField_empty :
    ¬ V13FieldPrefixInstantiation v13BoolPairFirstCoordinateField
      ([] : List (FiniteEvent (Bool × Bool))) v13BoolPairRepeatedStep := by
  exact not_v13FieldPrefixInstantiation_of_cell_half_violation true (by
    rw [v13BoolPairFirstCoordinateField_prefix_true_count,
      v13BoolPairFirstCoordinateField_success_true_count]
    decide)

/-- The same first-coordinate field failure follows from the general theorem:
a success-determining field with positive next-success mass cannot satisfy a
fixed-field certificate. -/
theorem not_v13FieldPrefixInstantiation_firstCoordinateField_empty_by_determined_success :
    ¬ V13FieldPrefixInstantiation v13BoolPairFirstCoordinateField
      ([] : List (FiniteEvent (Bool × Bool))) v13BoolPairRepeatedStep := by
  exact
    not_v13FieldPrefixInstantiation_of_fieldDeterminesSuccess_positive_success
      v13BoolPairFirstCoordinateField_determinesSuccess (by decide)

/-- Prefix-relative success determination is enough to block a fixed-field
certificate even when the field is not globally success-determining. -/
theorem not_v13FieldPrefixInstantiation_secondCoordinateField_diagonal_by_determines_success_on :
    ¬ V13FieldPrefixInstantiation v13BoolPairSecondCoordinateField
      [v13BoolPairDiagonalEvent] v13BoolPairRepeatedStep := by
  exact
    not_v13FieldPrefixInstantiation_of_fieldDeterminesSuccessOn_positive_success
      v13BoolPairSecondCoordinateField_determinesSuccessOn_diagonal
      (by
        rw [v13BoolPairDiagonal_repeatedStep_success_count]
        decide)

/-- The same diagonal-prefix obstruction blocks the operational same-cell
success-to-failure matching formulation. -/
theorem not_v13FieldFailureMatching_secondCoordinateField_diagonal_by_determines_success_on :
    ¬ V13FieldFailureMatching v13BoolPairSecondCoordinateField
      [v13BoolPairDiagonalEvent] v13BoolPairRepeatedStep := by
  exact
    not_v13FieldFailureMatching_of_fieldDeterminesSuccessOn_positive_success
      v13BoolPairSecondCoordinateField_determinesSuccessOn_diagonal
      (by
        rw [v13BoolPairDiagonal_repeatedStep_success_count]
        decide)

/-- A compact separation theorem: the generic prefix half-step can hold while
the natural fixed first-coordinate history field fails the v13 cellwise
instantiation. -/
theorem prefixHalfStep_without_firstCoordinateFieldInstantiation :
    PrefixHalfStep ([] : List (FiniteEvent (Bool × Bool)))
        v13BoolPairRepeatedStep.successEvent ∧
      ¬ V13FieldPrefixInstantiation v13BoolPairFirstCoordinateField
        ([] : List (FiniteEvent (Bool × Bool))) v13BoolPairRepeatedStep := by
  exact ⟨prefixHalfStep_v13BoolPairRepeatedStep_empty,
    not_v13FieldPrefixInstantiation_firstCoordinateField_empty⟩

/-- The fixed first-coordinate one-step switching claim is blocked already at
its first field certificate. -/
theorem not_v13FieldSwitchingInstantiated_firstCoordinateOneStep :
    ¬ V13FieldSwitchingInstantiated
      [v13BoolPairFirstCoordinateFieldedStep] := by
  exact
    not_v13FieldSwitchingInstantiatedFrom_cons_of_not_fieldPrefixInstantiation
      not_v13FieldPrefixInstantiation_firstCoordinateField_empty

/-- Even after a valid one-cell certificate for the first cut, using the
first-coordinate field for the repeated second cut is blocked because that
later field determines the next success event on a positive-mass prefix. -/
theorem unitField_first_step_then_firstCoordinateField_second_blocked :
    V13FieldPrefixInstantiation v13BoolPairUnitField
        ([] : List (FiniteEvent (Bool × Bool))) v13BoolPairRepeatedStep ∧
      ¬ V13FieldSwitchingInstantiated
        [v13BoolPairUnitFieldedStep, v13BoolPairFirstCoordinateFieldedStep] := by
  refine ⟨v13FieldPrefixInstantiation_unitField_empty, ?_⟩
  exact
    not_v13FieldSwitchingInstantiatedFrom_append_cons_of_fieldDeterminesSuccess_positive_success
      (hist := ([] : List (FiniteEvent (Bool × Bool))))
      (pre := [v13BoolPairUnitFieldedStep])
      (item := v13BoolPairFirstCoordinateFieldedStep)
      (suffix := [])
      v13BoolPairFirstCoordinateField_determinesSuccess
      (by
        decide)

/-- Repeating the same success event does not cut the already-successful
history class at all. -/
theorem v13BoolPairRepeatedStep_success_success_count :
    finiteHistoryCount (Bool × Bool)
      ([v13BoolPairRepeatedStep.successEvent] ++
        [v13BoolPairRepeatedStep.successEvent]) = 2 := by
  decide

/-- The second occurrence of an identical success event fails the positive-mass
prefix half-step: inside the first success event, the same event has conditional
mass `1`, not `1/2`. -/
theorem not_prefixHalfStep_v13BoolPairRepeatedStep_after_success :
    ¬ PrefixHalfStep [v13BoolPairRepeatedStep.successEvent]
      v13BoolPairRepeatedStep.successEvent := by
  rw [PrefixHalfStep, v13BoolPairRepeatedStep_success_count,
    v13BoolPairRepeatedStep_success_success_count]
  decide

/-- Consequently, the v13 atom-ledger certificate cannot be instantiated for
the second repeated switched step. -/
theorem not_v13PrefixInstantiated_boolPairRepeatedStep_second :
    ¬ V13PrefixInstantiated [v13BoolPairRepeatedStep.successEvent]
      v13BoolPairRepeatedStep := by
  exact not_v13PrefixInstantiated_of_not_prefixHalfStep
    not_prefixHalfStep_v13BoolPairRepeatedStep_after_success

/-- The repeated two-step Boolean-square model already violates the global
tower product bound: two identical half-mass events still have half-mass
intersection, not quarter-mass intersection. -/
theorem v13BoolPairRepeatedTwoSteps_product_bound_violation :
    ¬ 2 ^ [v13BoolPairRepeatedStep, v13BoolPairRepeatedStep].length *
        finiteHistoryCount (Bool × Bool)
          (v13SuccessEvents
            [v13BoolPairRepeatedStep, v13BoolPairRepeatedStep]) ≤
      finiteHistoryCount (Bool × Bool) ([] : List (FiniteEvent (Bool × Bool))) := by
  decide

/-- The same product-bound violation appears at the fixed-field layer even if
both repeated cuts use the non-revealing one-cell field. -/
theorem v13BoolPairUnitFieldedRepeatedTwoSteps_product_bound_violation :
    ¬ 2 ^ [v13BoolPairUnitFieldedStep, v13BoolPairUnitFieldedStep].length *
        finiteHistoryCount (Bool × Bool)
          (v13FieldedSuccessEvents
            [v13BoolPairUnitFieldedStep, v13BoolPairUnitFieldedStep]) ≤
      finiteHistoryCount (Bool × Bool) ([] : List (FiniteEvent (Bool × Bool))) := by
  decide

/-- The whole two-step repeated-coordinate switching claim is therefore not
instantiable in the v13 atom-ledger interface. -/
theorem not_v13SwitchingInstantiated_boolPairRepeatedTwoSteps :
    ¬ V13SwitchingInstantiated
      [v13BoolPairRepeatedStep, v13BoolPairRepeatedStep] := by
  intro h
  exact not_v13PrefixInstantiated_boolPairRepeatedStep_second h.2.1

/-- The same repeated-coordinate switching claim is also blocked at the global
product-bound level, before looking for the first failed prefix. -/
theorem not_v13SwitchingInstantiated_boolPairRepeatedTwoSteps_by_product_bound :
    ¬ V13SwitchingInstantiated
      [v13BoolPairRepeatedStep, v13BoolPairRepeatedStep] := by
  exact not_v13SwitchingInstantiated_of_product_bound_violation
    v13BoolPairRepeatedTwoSteps_product_bound_violation

/-- Therefore no concrete-cell v13 instantiation can exist for the repeated
two-step Boolean-square model either. -/
theorem not_v13ConcreteSwitchingInstantiated_boolPairRepeatedTwoSteps_by_product_bound :
    ¬ V13ConcreteSwitchingInstantiated
      [v13BoolPairRepeatedStep, v13BoolPairRepeatedStep] := by
  exact not_v13ConcreteSwitchingInstantiated_of_product_bound_violation
    v13BoolPairRepeatedTwoSteps_product_bound_violation

/-- Even the non-revealing one-cell fixed field cannot instantiate both
repeated cuts: the fielded product bound already fails. -/
theorem not_v13FieldSwitchingInstantiated_unitField_repeatedTwoSteps_by_product_bound :
    ¬ V13FieldSwitchingInstantiated
      [v13BoolPairUnitFieldedStep, v13BoolPairUnitFieldedStep] := by
  exact not_v13FieldSwitchingInstantiated_of_product_bound_violation
    v13BoolPairUnitFieldedRepeatedTwoSteps_product_bound_violation

/-- The same fielded product failure blocks the operational same-cell matching
obligation itself. -/
theorem not_v13FieldSwitchingFailureMatching_unitField_repeatedTwoSteps_by_product_bound :
    ¬ V13FieldSwitchingFailureMatching
      [v13BoolPairUnitFieldedStep, v13BoolPairUnitFieldedStep] := by
  exact not_v13FieldSwitchingFailureMatching_of_product_bound_violation
    v13BoolPairUnitFieldedRepeatedTwoSteps_product_bound_violation

end BoolPairRepeatedStep

end Mettapedia.Computability.PNP
