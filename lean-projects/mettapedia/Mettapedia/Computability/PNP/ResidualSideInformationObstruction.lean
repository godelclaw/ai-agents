import Mathlib.Tactic

/-!
# P vs NP crux: residual side information cannot be source-only data

This file isolates a small but robust obstruction for the broad residual-side
information repair class.  If two conditioned worlds have the same source
summary but different residual side information, then the residual is not a
function of the source summary.  Moreover, even a single equality predicate for
one residual value cannot be pushed down to a source-only predicate.

The result is intentionally finite-free: it is a pure functional obstruction.
Any repair that keeps such residual information must either prove that the
residual is determined by the source summary, or expose it as a genuine side
channel to be handled by the side-channel/resolving-mass theory.
-/

namespace Mettapedia.Computability.PNP

/-- Residual side information is determined by a source summary if it factors
through that summary. -/
def SideInfoDeterminedBy {Ω Base Side : Type*}
    (base : Ω → Base) (side : Ω → Side) : Prop :=
  ∃ decode : Base → Side, ∀ ω, decode (base ω) = side ω

/-- A concrete residual collision: two worlds have the same source summary but
different residual side information. -/
def SideInfoCollisionOverBase {Ω Base Side : Type*}
    (base : Ω → Base) (side : Ω → Side) : Prop :=
  ∃ x y : Ω, base x = base y ∧ side x ≠ side y

/-- A residual collision whose left endpoint lies on positive weight support. -/
def PositiveWeightSideInfoCollisionOverBase {Ω Base Side : Type*}
    (base : Ω → Base) (side : Ω → Side) (w : Ω → ℕ) : Prop :=
  ∃ x y : Ω, 0 < w x ∧ base x = base y ∧ side x ≠ side y

/-- A source-only predicate captures one residual equality test when it can be
decided from the source summary alone. -/
def SourceOnlyPredicateCapturesSideEq {Ω Base Side : Type*}
    (base : Ω → Base) (side : Ω → Side) (s : Side) : Prop :=
  ∃ predicate : Base → Prop, ∀ ω, predicate (base ω) ↔ side ω = s

/-- A source-only Boolean classifier captures a residual Boolean target when it
factors through the source summary. -/
def SourceOnlyBooleanClassifier {Ω Base : Type*}
    (base : Ω → Base) (target : Ω → Bool) : Prop :=
  ∃ classifier : Base → Bool, ∀ ω, classifier (base ω) = target ω

/-- A classifier on `(base, side)` is source-only on positive support when
some source-only Boolean classifier gives the same predictions at every
positive-weight world. -/
def SupportwiseSourceOnlyPairClassifier {Ω Base Side : Type*}
    (base : Ω → Base) (side : Ω → Side) (w : Ω → ℕ)
    (h : Base × Side → Bool) : Prop :=
  ∃ classifier : Base → Bool,
    ∀ ω, 0 < w ω → classifier (base ω) = h (base ω, side ω)

/-- A single same-source/different-residual pair rules out source-only residual
decoding. -/
theorem not_sideInfoDeterminedBy_of_same_base_ne_side
    {Ω Base Side : Type*} {base : Ω → Base} {side : Ω → Side}
    {x y : Ω} (hbase : base x = base y) (hside : side x ≠ side y) :
    ¬ SideInfoDeterminedBy base side := by
  rintro ⟨decode, hdecode⟩
  apply hside
  calc
    side x = decode (base x) := (hdecode x).symm
    _ = decode (base y) := congrArg decode hbase
    _ = side y := hdecode y

/-- Collision form of the same obstruction. -/
theorem not_sideInfoDeterminedBy_of_collision
    {Ω Base Side : Type*} {base : Ω → Base} {side : Ω → Side}
    (hcollision : SideInfoCollisionOverBase base side) :
    ¬ SideInfoDeterminedBy base side := by
  rcases hcollision with ⟨x, y, hbase, hside⟩
  exact not_sideInfoDeterminedBy_of_same_base_ne_side hbase hside

/-- A positive-weight residual collision is, in particular, a residual
collision. -/
theorem sideInfoCollisionOverBase_of_positiveWeight_collision
    {Ω Base Side : Type*} {base : Ω → Base} {side : Ω → Side} {w : Ω → ℕ}
    (hcollision : PositiveWeightSideInfoCollisionOverBase base side w) :
    SideInfoCollisionOverBase base side := by
  rcases hcollision with ⟨x, y, _hxw, hbase, hside⟩
  exact ⟨x, y, hbase, hside⟩

/-- A positive-weight residual collision rules out source-only residual
decoding. -/
theorem not_sideInfoDeterminedBy_of_positiveWeight_collision
    {Ω Base Side : Type*} {base : Ω → Base} {side : Ω → Side} {w : Ω → ℕ}
    (hcollision : PositiveWeightSideInfoCollisionOverBase base side w) :
    ¬ SideInfoDeterminedBy base side :=
  not_sideInfoDeterminedBy_of_collision
    (sideInfoCollisionOverBase_of_positiveWeight_collision hcollision)

/-- If two worlds have the same source summary, one has residual value `s`, and
the other does not, then no source-only predicate can capture equality to `s`. -/
theorem not_sourceOnlyPredicateCapturesSideEq_of_same_base_eq_value_ne
    {Ω Base Side : Type*} {base : Ω → Base} {side : Ω → Side}
    {x y : Ω} {s : Side}
    (hbase : base x = base y) (hx : side x = s) (hy : side y ≠ s) :
    ¬ SourceOnlyPredicateCapturesSideEq base side s := by
  rintro ⟨predicate, hpredicate⟩
  have hxpred : predicate (base x) := (hpredicate x).2 hx
  have hypred : ¬ predicate (base y) := by
    intro h
    exact hy ((hpredicate y).1 h)
  exact hypred (by simpa [hbase] using hxpred)

/-- A same-source/different-residual pair rules out source-only capture of the
left residual equality predicate. -/
theorem not_sourceOnlyPredicateCapturesSideEq_left_of_same_base_ne_side
    {Ω Base Side : Type*} {base : Ω → Base} {side : Ω → Side}
    {x y : Ω} (hbase : base x = base y) (hside : side x ≠ side y) :
    ¬ SourceOnlyPredicateCapturesSideEq base side (side x) := by
  exact
    not_sourceOnlyPredicateCapturesSideEq_of_same_base_eq_value_ne
      hbase rfl (fun hyx => hside hyx.symm)

/-- A positive-weight residual collision exposes a supported residual value
whose equality predicate cannot be source-only. -/
theorem exists_positive_not_sourceOnlyPredicateCapturesSideEq_of_positiveWeight_collision
    {Ω Base Side : Type*} {base : Ω → Base} {side : Ω → Side} {w : Ω → ℕ}
    (hcollision : PositiveWeightSideInfoCollisionOverBase base side w) :
    ∃ x, 0 < w x ∧ ¬ SourceOnlyPredicateCapturesSideEq base side (side x) := by
  rcases hcollision with ⟨x, y, hxw, hbase, hside⟩
  exact
    ⟨x, hxw,
      not_sourceOnlyPredicateCapturesSideEq_left_of_same_base_ne_side
        hbase hside⟩

/-- A same-source/different-Boolean-target pair cannot be classified by a
source-only Boolean classifier. -/
theorem not_sourceOnlyBooleanClassifier_of_same_base_ne_target
    {Ω Base : Type*} {base : Ω → Base} {target : Ω → Bool}
    {x y : Ω} (hbase : base x = base y) (htarget : target x ≠ target y) :
    ¬ SourceOnlyBooleanClassifier base target := by
  rintro ⟨classifier, hclassifier⟩
  apply htarget
  calc
    target x = classifier (base x) := (hclassifier x).symm
    _ = classifier (base y) := congrArg classifier hbase
    _ = target y := hclassifier y

/-- Toy source summary for a residual-side-information collision: both worlds
have the same source summary. -/
def residualSideInfoToyBase (_ : Bool) : Bool := false

/-- Toy residual side information that varies inside the same source fiber. -/
def residualSideInfoToySide (b : Bool) : Bool := b

theorem residualSideInfoToy_collision :
    SideInfoCollisionOverBase residualSideInfoToyBase residualSideInfoToySide := by
  exact ⟨false, true, rfl, by simp [residualSideInfoToySide]⟩

theorem residualSideInfoToy_not_determinedBy_base :
    ¬ SideInfoDeterminedBy residualSideInfoToyBase residualSideInfoToySide := by
  exact not_sideInfoDeterminedBy_of_collision residualSideInfoToy_collision

theorem residualSideInfoToy_not_sourceOnlyPredicate_false :
    ¬ SourceOnlyPredicateCapturesSideEq
      residualSideInfoToyBase residualSideInfoToySide false := by
  exact
    not_sourceOnlyPredicateCapturesSideEq_of_same_base_eq_value_ne
      (x := false) (y := true) rfl rfl
      (by simp [residualSideInfoToySide])

theorem residualSideInfoToy_not_sourceOnlyBooleanClassifier :
    ¬ SourceOnlyBooleanClassifier
      residualSideInfoToyBase residualSideInfoToySide := by
  exact
    not_sourceOnlyBooleanClassifier_of_same_base_ne_target
      (x := false) (y := true) rfl
      (by simp [residualSideInfoToySide])

end Mettapedia.Computability.PNP
