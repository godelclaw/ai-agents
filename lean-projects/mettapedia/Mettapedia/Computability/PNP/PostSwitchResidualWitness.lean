import Mettapedia.Computability.PNP.PostSwitchForkObstruction
import Mettapedia.Computability.PNP.ResidualSideInformationResolutionCost
import Mettapedia.Computability.PNP.VisiblePostSwitchSurface
import Mathlib.Tactic

/-!
# P vs NP crux: a concrete residual prediction witness on the exact post-switch surface

The recent residual-side packets proved only conditional statements of the
form "if an invariant-base residual route has positive advantage, then it must
produce a supported prediction-separation witness."

This file supplies such a witness concretely on the manuscript's exact
post-switch surface.  We stay on the actual local-input object

`u = (z, a, b)`

with involution

`T(u) = (z, a, b xor a)`,

fix the active one-bit column `a = 1`, support exactly one two-point
`T`-orbit, and let the classifier read the retained side bit `b`.

The resulting classifier:

* uses an invariant base `(z, a)`;
* has symmetric support weights;
* is correct on every supported point; and
* achieves strictly positive doubled advantage with an explicit supported
  prediction-separation witness.
-/

namespace Mettapedia.Computability.PNP

section

variable {Z : Type*}

/-- The unique active one-bit VV column. -/
def oneBitVec : BitVec 1 := fun _ => true

/-- The supported exact post-switch input with side bit `false`. -/
def activeOrbitInputFalse (z0 : Z) : ExactVisiblePostSwitchSurface Z 1 :=
  ⟨z0, oneBitVec, zeroVec⟩

/-- The supported exact post-switch input with side bit `true`. -/
def activeOrbitInputTrue (z0 : Z) : ExactVisiblePostSwitchSurface Z 1 :=
  ⟨z0, oneBitVec, oneBitVec⟩

/-- The invariant-base plus side-channel feature used by the witness route. -/
def activeOrbitFeatures (u : ExactVisiblePostSwitchSurface Z 1) :
    InvariantPostSwitchSurface Z 1 × BitVec 1 :=
  (invariantVisibleData u, u.b)

/-- The target bit is the retained one-bit side channel itself. -/
def activeOrbitTarget (u : ExactVisiblePostSwitchSurface Z 1) : Bool :=
  u.b 0

/-- The classifier simply reads that retained side bit. -/
def activeOrbitClassifier :
    InvariantPostSwitchSurface Z 1 × BitVec 1 → Bool :=
  fun t => t.2 0

/-- Weight one on the chosen active two-point orbit, and zero elsewhere. -/
noncomputable def activeOrbitWeight (z0 : Z) (u : ExactVisiblePostSwitchSurface Z 1) : ℕ := by
  classical
  exact if u = activeOrbitInputFalse z0 ∨ u = activeOrbitInputTrue z0 then 1 else 0

@[simp] theorem oneBitVec_apply (i : Fin 1) : oneBitVec i = true := by
  fin_cases i
  rfl

@[simp] theorem activeOrbitInputFalse_b_apply (z0 : Z) (i : Fin 1) :
    (activeOrbitInputFalse z0).b i = false := by
  simp [activeOrbitInputFalse, zeroVec]

@[simp] theorem activeOrbitInputTrue_b_apply (z0 : Z) (i : Fin 1) :
    (activeOrbitInputTrue z0).b i = true := by
  simp [activeOrbitInputTrue, oneBitVec_apply]

theorem activeOrbitInputFalse_ne_inputTrue (z0 : Z) :
    activeOrbitInputFalse z0 ≠ activeOrbitInputTrue z0 := by
  intro h
  have h0 := congrArg (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b 0) h
  simp at h0

@[simp] theorem tiInputMap_activeOrbitInputFalse (z0 : Z) :
    tiInputMap (activeOrbitInputFalse z0) = activeOrbitInputTrue z0 := by
  rfl

@[simp] theorem tiInputMap_activeOrbitInputTrue (z0 : Z) :
    tiInputMap (activeOrbitInputTrue z0) = activeOrbitInputFalse z0 := by
  rfl

@[simp] theorem activeOrbitWeight_false (z0 : Z) :
    activeOrbitWeight z0 (activeOrbitInputFalse z0) = 1 := by
  classical
  simp [activeOrbitWeight]

@[simp] theorem activeOrbitWeight_true (z0 : Z) :
    activeOrbitWeight z0 (activeOrbitInputTrue z0) = 1 := by
  classical
  simp [activeOrbitWeight]

theorem activeOrbitWeight_tiInputMap (z0 : Z) (u : ExactVisiblePostSwitchSurface Z 1) :
    activeOrbitWeight z0 (tiInputMap u) = activeOrbitWeight z0 u := by
  classical
  by_cases h : u = activeOrbitInputFalse z0 ∨ u = activeOrbitInputTrue z0
  · rcases h with rfl | rfl <;> simp [activeOrbitWeight]
  · have hti :
        ¬ (tiInputMap u = activeOrbitInputFalse z0 ∨
            tiInputMap u = activeOrbitInputTrue z0) := by
      intro hsupp
      apply h
      rcases hsupp with hfalse | htrue
      · right
        have hfalse' := congrArg tiInputMap hfalse
        simpa [tiInputMap_involutive u] using hfalse'
      · left
        have htrue' := congrArg tiInputMap htrue
        simpa [tiInputMap_involutive u] using htrue'
    simp [activeOrbitWeight, h, hti]

theorem activeOrbitTarget_flip_of_positiveWeight
    (z0 : Z) (u : ExactVisiblePostSwitchSurface Z 1)
    (hu : 0 < activeOrbitWeight z0 u) :
    activeOrbitTarget (tiInputMap u) = !(activeOrbitTarget u) := by
  classical
  have hsupp : u = activeOrbitInputFalse z0 ∨ u = activeOrbitInputTrue z0 := by
    by_cases h : u = activeOrbitInputFalse z0 ∨ u = activeOrbitInputTrue z0
    · exact h
    · have hzero : activeOrbitWeight z0 u = 0 := by
        simp [activeOrbitWeight, h]
      omega
  rcases hsupp with rfl | rfl <;> simp [activeOrbitTarget]

theorem activeOrbitCorrect_of_positiveWeight
    (z0 : Z) (u : ExactVisiblePostSwitchSurface Z 1)
    (hu : 0 < activeOrbitWeight z0 u) :
    Correct activeOrbitFeatures activeOrbitTarget activeOrbitClassifier u := by
  classical
  have hsupp : u = activeOrbitInputFalse z0 ∨ u = activeOrbitInputTrue z0 := by
    by_cases h : u = activeOrbitInputFalse z0 ∨ u = activeOrbitInputTrue z0
    · exact h
    · have hzero : activeOrbitWeight z0 u = 0 := by
        simp [activeOrbitWeight, h]
      omega
  rcases hsupp with rfl | rfl <;> rfl

theorem activeOrbitWeight_eq_zero_of_not_correct
    (z0 : Z) (u : ExactVisiblePostSwitchSurface Z 1)
    (hu : ¬ Correct activeOrbitFeatures activeOrbitTarget activeOrbitClassifier u) :
    activeOrbitWeight z0 u = 0 := by
  by_cases hpos : 0 < activeOrbitWeight z0 u
  · exact False.elim (hu (activeOrbitCorrect_of_positiveWeight z0 u hpos))
  · exact Nat.eq_zero_of_not_pos hpos

theorem weightedCorrectMass_activeOrbit_eq_weightedTotalMass
    [Fintype Z] (z0 : Z) :
    weightedCorrectMass
        activeOrbitFeatures
        activeOrbitTarget
        (activeOrbitWeight z0)
        activeOrbitClassifier
      =
    weightedTotalMass (activeOrbitWeight z0) := by
  have hsplit :=
    weightedTotalMass_eq_slice_add_outside
      (p := Correct activeOrbitFeatures activeOrbitTarget activeOrbitClassifier)
      (w := activeOrbitWeight z0)
  have hout :
      outsideMass
          (Correct activeOrbitFeatures activeOrbitTarget activeOrbitClassifier)
          (activeOrbitWeight z0)
        = 0 := by
    classical
    unfold outsideMass sliceMass
    apply Finset.sum_eq_zero
    intro u _
    exact activeOrbitWeight_eq_zero_of_not_correct z0 u.1 u.2
  simpa [weightedCorrectMass, sliceMass, hout, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    using hsplit.symm

def activeOrbitSupport (z0 : Z) :=
  {u : ExactVisiblePostSwitchSurface Z 1 //
    u = activeOrbitInputFalse z0 ∨ u = activeOrbitInputTrue z0}

noncomputable def activeOrbitSupportEquivBool (z0 : Z) :
    {u : ExactVisiblePostSwitchSurface Z 1 //
      u = activeOrbitInputFalse z0 ∨ u = activeOrbitInputTrue z0} ≃ Bool := by
  classical
  refine
    { toFun := fun u =>
        if u.1 = activeOrbitInputFalse z0 then false else true
      invFun := fun b =>
        cond b
          ⟨activeOrbitInputTrue z0, Or.inr rfl⟩
          ⟨activeOrbitInputFalse z0, Or.inl rfl⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro u
    rcases u with ⟨u, hu⟩
    rcases hu with rfl | rfl
    · simp
    · have hneq : activeOrbitInputTrue z0 ≠ activeOrbitInputFalse z0 := by
        intro h
        exact activeOrbitInputFalse_ne_inputTrue z0 h.symm
      simp [hneq]
  · intro b
    cases b with
    | false =>
        simp
    | true =>
        have hneq : activeOrbitInputTrue z0 ≠ activeOrbitInputFalse z0 := by
          intro h
          exact activeOrbitInputFalse_ne_inputTrue z0 h.symm
        simp [hneq]

theorem sliceMass_activeOrbitSupport [Fintype Z] (z0 : Z) :
    (by
      classical
      exact
        sliceMass
            (fun u : ExactVisiblePostSwitchSurface Z 1 =>
              u = activeOrbitInputFalse z0 ∨ u = activeOrbitInputTrue z0)
            (activeOrbitWeight z0)
          = 2) := by
  classical
  unfold sliceMass
  calc
    (∑ u : {u : ExactVisiblePostSwitchSurface Z 1 //
        u = activeOrbitInputFalse z0 ∨ u = activeOrbitInputTrue z0},
        activeOrbitWeight z0 u.1)
        = ∑ b : Bool, 1 := by
            exact Fintype.sum_equiv
              (activeOrbitSupportEquivBool z0)
              (fun u : {u : ExactVisiblePostSwitchSurface Z 1 //
                u = activeOrbitInputFalse z0 ∨ u = activeOrbitInputTrue z0} =>
                activeOrbitWeight z0 u.1)
                  (fun _ : Bool => 1)
                  (by
                    intro u
                    rcases u with ⟨u, hu⟩
                    rcases hu with rfl | rfl <;> simp [activeOrbitWeight])
    _ = 2 := by simp

theorem outsideMass_activeOrbitSupport [Fintype Z] (z0 : Z) :
    (by
      classical
      exact
        outsideMass
            (fun u : ExactVisiblePostSwitchSurface Z 1 =>
              u = activeOrbitInputFalse z0 ∨ u = activeOrbitInputTrue z0)
            (activeOrbitWeight z0)
          = 0) := by
  classical
  unfold outsideMass sliceMass
  apply Finset.sum_eq_zero
  intro u _
  simp [activeOrbitWeight, u.2]

theorem weightedTotalMass_activeOrbitWeight (z0 : Z) [Fintype Z] :
    weightedTotalMass (activeOrbitWeight z0) = 2 := by
  classical
  have hsplit :=
    weightedTotalMass_eq_slice_add_outside
      (p := fun u : ExactVisiblePostSwitchSurface Z 1 =>
        u = activeOrbitInputFalse z0 ∨ u = activeOrbitInputTrue z0)
      (w := activeOrbitWeight z0)
  simpa [sliceMass_activeOrbitSupport (Z := Z) z0,
    outsideMass_activeOrbitSupport (Z := Z) z0] using hsplit

theorem activeOrbitSide_ne_of_positiveWeight
    (z0 : Z) (u : ExactVisiblePostSwitchSurface Z 1)
    (hu : 0 < activeOrbitWeight z0 u) :
    (tiInputMap u).b ≠ u.b := by
  classical
  have hsupp : u = activeOrbitInputFalse z0 ∨ u = activeOrbitInputTrue z0 := by
    by_cases h : u = activeOrbitInputFalse z0 ∨ u = activeOrbitInputTrue z0
    · exact h
    · have hzero : activeOrbitWeight z0 u = 0 := by
        simp [activeOrbitWeight, h]
      omega
  rcases hsupp with rfl | rfl
  · intro h
    have h0 := congrArg (fun b : BitVec 1 => b 0) h
    simp at h0
  · intro h
    have h0 := congrArg (fun b : BitVec 1 => b 0) h
    simp at h0

/-- The active two-point exact post-switch witness is correct on every
positive-weight point, so the abstract invariant-base exact-success theorem
already forces the whole supported mass to be orbit-resolving mass. -/
theorem resolvedMass_activeOrbit_eq_weightedTotalMass
    [Fintype Z] (z0 : Z) :
    resolvedMass tiInputMap
      (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b)
      (activeOrbitWeight z0) =
    weightedTotalMass (activeOrbitWeight z0) := by
  exact
    resolvedMass_eq_weightedTotalMass_of_supportwise_correct_invariant_base
      tiInputMap
      invariantVisibleData
      (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b)
      activeOrbitTarget
      (activeOrbitWeight z0)
      activeOrbitClassifier
      invariantVisibleData_tiInputMap
      (activeOrbitTarget_flip_of_positiveWeight z0)
      (activeOrbitWeight_tiInputMap z0)
      (activeOrbitCorrect_of_positiveWeight z0)

/-- On the exact active two-point post-switch witness, every supported point is
resolved by the retained side bit, so the resolved mass is the whole support
mass. -/
theorem resolvedMass_activeOrbit_eq_two
    [Fintype Z] (z0 : Z) :
    resolvedMass tiInputMap
      (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b)
      (activeOrbitWeight z0) = 2 := by
  rw [resolvedMass_activeOrbit_eq_weightedTotalMass (Z := Z) z0,
    weightedTotalMass_activeOrbitWeight (Z := Z) z0]

theorem doubledAdvantage_activeOrbit_eq_two
    [Fintype Z] (z0 : Z) :
    doubledAdvantage
        activeOrbitFeatures
        activeOrbitTarget
        (activeOrbitWeight z0)
        activeOrbitClassifier
      = 2 := by
  rw [doubledAdvantage_eq_weightedTotalMass_of_supportwise_correct
    activeOrbitFeatures
    activeOrbitTarget
    (activeOrbitWeight z0)
    activeOrbitClassifier
    (activeOrbitCorrect_of_positiveWeight z0)]
  exact weightedTotalMass_activeOrbitWeight (Z := Z) z0

theorem doubledAdvantage_activeOrbit_eq_resolvedMass
    [Fintype Z] (z0 : Z) :
    doubledAdvantage
        activeOrbitFeatures
        activeOrbitTarget
        (activeOrbitWeight z0)
        activeOrbitClassifier =
      resolvedMass tiInputMap
        (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b)
        (activeOrbitWeight z0) := by
  exact
    doubledAdvantage_eq_resolvedMass_of_supportwise_correct_invariant_base
      tiInputMap
      invariantVisibleData
      (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b)
      activeOrbitTarget
      (activeOrbitWeight z0)
      activeOrbitClassifier
      invariantVisibleData_tiInputMap
      (activeOrbitTarget_flip_of_positiveWeight z0)
      (activeOrbitWeight_tiInputMap z0)
      (activeOrbitCorrect_of_positiveWeight z0)

theorem pos_doubledAdvantage_activeOrbit
    [Fintype Z] (z0 : Z) :
    0 <
      doubledAdvantage
        activeOrbitFeatures
        activeOrbitTarget
        (activeOrbitWeight z0)
        activeOrbitClassifier := by
  rw [doubledAdvantage_activeOrbit_eq_two (Z := Z) z0]
  decide

theorem total_lt_two_mul_weightedCorrectMass_activeOrbit
    [Fintype Z] (z0 : Z) :
    weightedTotalMass (activeOrbitWeight z0) <
      2 * weightedCorrectMass
        activeOrbitFeatures
        activeOrbitTarget
        (activeOrbitWeight z0)
        activeOrbitClassifier := by
  have hcorrect :=
    weightedCorrectMass_activeOrbit_eq_weightedTotalMass (Z := Z) z0
  have htotal := weightedTotalMass_activeOrbitWeight (Z := Z) z0
  omega

theorem pos_nonzeroColumnMass_activeOrbit
    [Fintype Z] (z0 : Z) :
    0 <
      sliceMass
        (fun u : ExactVisiblePostSwitchSurface Z 1 => nonzeroColumn u.a)
        (activeOrbitWeight z0) := by
  classical
  let u0 :
      {u : ExactVisiblePostSwitchSurface Z 1 // nonzeroColumn u.a} :=
    ⟨activeOrbitInputFalse z0, ⟨0, by simp [activeOrbitInputFalse, oneBitVec_apply]⟩⟩
  have hterm : 0 < activeOrbitWeight z0 u0.1 := by
    simp [u0, activeOrbitWeight]
  unfold sliceMass
  have hle :
      activeOrbitWeight z0 u0.1 ≤
        ∑ u :
          {u : ExactVisiblePostSwitchSurface Z 1 // nonzeroColumn u.a},
            activeOrbitWeight z0 u.1 := by
    simpa [u0] using
      (Finset.single_le_sum
        (fun u _ => Nat.zero_le (activeOrbitWeight z0 u.1))
        (Finset.mem_univ u0))
  exact lt_of_lt_of_le hterm hle

theorem not_exactInputInvariantWeightedSupport_activeOrbit
    (z0 : Z) :
    ¬ exactInputInvariantWeightedSupport (activeOrbitWeight z0) := by
  intro hsupport
  have hpos : 0 < activeOrbitWeight z0 (activeOrbitInputFalse z0) := by
    simp [activeOrbitWeight]
  have hfix := hsupport (activeOrbitInputFalse z0) hpos
  have hneq : tiInputMap (activeOrbitInputFalse z0) ≠ activeOrbitInputFalse z0 := by
    simpa using (activeOrbitInputFalse_ne_inputTrue z0).symm
  exact hneq hfix

theorem exactPostSwitch_activeOrbit_forces_fork_obstruction
    [Fintype Z] (z0 : Z) :
    weightedTotalMass (activeOrbitWeight z0) <
        2 * weightedCorrectMass
          activeOrbitFeatures
          activeOrbitTarget
          (activeOrbitWeight z0)
          activeOrbitClassifier ∧
      0 <
        sliceMass
          (fun u : ExactVisiblePostSwitchSurface Z 1 => nonzeroColumn u.a)
          (activeOrbitWeight z0) ∧
      ¬ exactInputInvariantWeightedSupport (activeOrbitWeight z0) := by
  refine ⟨total_lt_two_mul_weightedCorrectMass_activeOrbit (Z := Z) z0,
    pos_nonzeroColumnMass_activeOrbit (Z := Z) z0,
    not_exactInputInvariantWeightedSupport_activeOrbit (Z := Z) z0⟩

theorem exists_positive_prediction_separation_activeOrbit
    (z0 : Z) :
    ∃ u : ExactVisiblePostSwitchSurface Z 1,
      0 < activeOrbitWeight z0 u ∧
      activeOrbitClassifier (activeOrbitFeatures (tiInputMap u)) ≠
        activeOrbitClassifier (activeOrbitFeatures u) := by
  classical
  refine ⟨activeOrbitInputFalse z0, by simp [activeOrbitWeight], ?_⟩
  simp [activeOrbitFeatures, activeOrbitClassifier]

theorem exists_positive_same_base_ne_side_activeOrbit
    (z0 : Z) :
    ∃ u : ExactVisiblePostSwitchSurface Z 1,
      0 < activeOrbitWeight z0 u ∧
      invariantVisibleData (tiInputMap u) = invariantVisibleData u ∧
      (tiInputMap u).b ≠ u.b := by
  classical
  refine ⟨activeOrbitInputFalse z0, by simp [activeOrbitWeight], ?_, ?_⟩
  · rfl
  · intro h
    have h0 := congrArg (fun b : BitVec 1 => b 0) h
    simp at h0

/-- The active two-point exact post-switch witness has positive ordinary
orbit-resolving mass for the retained side bit itself. -/
theorem pos_resolvedMass_activeOrbit
    [Fintype Z]
    (z0 : Z) :
    0 < resolvedMass tiInputMap (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b)
      (activeOrbitWeight z0) := by
  rw [resolvedMass_activeOrbit_eq_two (Z := Z) z0]
  decide

/-- On the exact visible post-switch surface, positive resolving mass for the
retained side bit already forces the pure residual obstruction package. -/
theorem exactPostSwitch_pos_resolvedMass_forces_pure_residual_obstruction_package
    [Fintype Z]
    (w : ExactVisiblePostSwitchSurface Z 1 → ℕ)
    (hmass :
      0 < resolvedMass tiInputMap (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b) w) :
    ¬ SideInfoDeterminedBy invariantVisibleData
        (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b) ∧
      PositiveWeightSideInfoCollisionOverBase invariantVisibleData
        (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b) w ∧
      (∃ u : ExactVisiblePostSwitchSurface Z 1,
        0 < w u ∧
          invariantVisibleData (tiInputMap u) = invariantVisibleData u ∧
          (tiInputMap u).b ≠ u.b) ∧
      (∃ u : ExactVisiblePostSwitchSurface Z 1,
        0 < w u ∧
          ¬ SourceOnlyPredicateCapturesSideEq
            invariantVisibleData
            (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b) (u.b)) := by
  simpa [invariantVisibleData] using
    pos_resolvedMass_obstruction_package_invariant_base
      tiInputMap
      invariantVisibleData
      (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b)
      w
      invariantVisibleData_tiInputMap
      hmass

/-- The concrete active two-point exact post-switch witness already realizes
the pure residual obstruction package, before any classifier-level
prediction-separation fact is invoked. -/
theorem exactPostSwitch_activeOrbit_realizes_pure_residual_obstruction_package
    [Fintype Z] (z0 : Z) :
    0 < resolvedMass tiInputMap (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b)
        (activeOrbitWeight z0) ∧
      ¬ SideInfoDeterminedBy invariantVisibleData
          (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b) ∧
      PositiveWeightSideInfoCollisionOverBase
        invariantVisibleData
        (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b)
        (activeOrbitWeight z0) ∧
      (∃ u : ExactVisiblePostSwitchSurface Z 1,
        0 < activeOrbitWeight z0 u ∧
          invariantVisibleData (tiInputMap u) = invariantVisibleData u ∧
          (tiInputMap u).b ≠ u.b) ∧
      (∃ u : ExactVisiblePostSwitchSurface Z 1,
        0 < activeOrbitWeight z0 u ∧
          ¬ SourceOnlyPredicateCapturesSideEq
            invariantVisibleData
            (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b) (u.b)) := by
  have hmass := pos_resolvedMass_activeOrbit (Z := Z) z0
  refine ⟨hmass, ?_⟩
  exact
    exactPostSwitch_pos_resolvedMass_forces_pure_residual_obstruction_package
      (Z := Z) (activeOrbitWeight z0) hmass

theorem exactPostSwitch_activeOrbit_realizes_residual_prediction_witness
    [Fintype Z] (z0 : Z) :
    (∀ u : ExactVisiblePostSwitchSurface Z 1,
      invariantVisibleData (tiInputMap u) = invariantVisibleData u) ∧
    (∀ u : ExactVisiblePostSwitchSurface Z 1,
      activeOrbitWeight z0 (tiInputMap u) = activeOrbitWeight z0 u) ∧
    (∀ u : ExactVisiblePostSwitchSurface Z 1, 0 < activeOrbitWeight z0 u →
      activeOrbitTarget (tiInputMap u) = !(activeOrbitTarget u)) ∧
    0 <
      doubledAdvantage
        activeOrbitFeatures
        activeOrbitTarget
        (activeOrbitWeight z0)
        activeOrbitClassifier ∧
    ∃ u : ExactVisiblePostSwitchSurface Z 1,
      0 < activeOrbitWeight z0 u ∧
      activeOrbitClassifier (activeOrbitFeatures (tiInputMap u)) ≠
        activeOrbitClassifier (activeOrbitFeatures u) := by
  refine ⟨invariantVisibleData_tiInputMap, activeOrbitWeight_tiInputMap z0,
    activeOrbitTarget_flip_of_positiveWeight z0,
    pos_doubledAdvantage_activeOrbit (Z := Z) z0,
    exists_positive_prediction_separation_activeOrbit (Z := Z) z0⟩

/-- On the concrete active two-point exact post-switch witness, the retained
classifier output cannot already be source-only over the invariant base,
because some positive-weight involution pair is separated by the final
prediction. -/
theorem activeOrbitClassifier_not_supportwiseSourceOnly
    [Fintype Z] (z0 : Z) :
    ¬ SupportwiseSourceOnlyPairClassifier
        invariantVisibleData
        (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b)
        (activeOrbitWeight z0)
        activeOrbitClassifier := by
  intro hsource
  rcases exists_positive_prediction_separation_activeOrbit (Z := Z) z0 with
    ⟨u, hu, hsep⟩
  have heq :=
    prediction_eq_under_involution_of_supportwiseSourceOnlyPairClassifier_invariant_base
      tiInputMap
      invariantVisibleData
      (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b)
      (activeOrbitWeight z0)
      activeOrbitClassifier
      invariantVisibleData_tiInputMap
      (activeOrbitWeight_tiInputMap z0)
      hsource
      u
      hu
  exact hsep heq

/-- The manuscript's concrete active exact post-switch orbit already realizes
the full supported proof-relevant residual obstruction package with the actual
successful classifier, and that same visible surface cannot admit any
supportwise visible-pair balancing involution. -/
theorem exactPostSwitch_activeOrbit_realizes_supported_obstruction_package_and_no_visiblePairBalancing
    [Fintype Z] (z0 : Z) :
    0 <
      doubledAdvantage
        activeOrbitFeatures
        activeOrbitTarget
        (activeOrbitWeight z0)
        activeOrbitClassifier ∧
      0 < resolvedMass tiInputMap
        (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b)
        (activeOrbitWeight z0) ∧
      ¬ SideInfoDeterminedBy invariantVisibleData
          (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b) ∧
      ¬ SupportwiseSourceOnlyPairClassifier
          invariantVisibleData
          (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b)
          (activeOrbitWeight z0)
          activeOrbitClassifier ∧
      (∃ u : ExactVisiblePostSwitchSurface Z 1,
        0 < activeOrbitWeight z0 u ∧
          invariantVisibleData (tiInputMap u) = invariantVisibleData u ∧
          (tiInputMap u).b ≠ u.b) ∧
      (∃ u : ExactVisiblePostSwitchSurface Z 1,
        0 < activeOrbitWeight z0 u ∧
          ¬ SourceOnlyPredicateCapturesSideEq
            invariantVisibleData
            (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b) (u.b)) ∧
      (∃ u : ExactVisiblePostSwitchSurface Z 1,
        0 < activeOrbitWeight z0 u ∧
          activeOrbitClassifier (activeOrbitFeatures (tiInputMap u)) ≠
            activeOrbitClassifier (activeOrbitFeatures u)) ∧
      ¬ SupportwiseVisiblePairBalancing
          invariantVisibleData
          (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b)
          activeOrbitTarget
          (activeOrbitWeight z0) := by
  have hpackage :=
    exactPostSwitch_activeOrbit_realizes_pure_residual_obstruction_package
      (Z := Z) z0
  rcases hpackage with
    ⟨hmass, hnot, _hcollision, hwitness, hpred⟩
  have hadv := pos_doubledAdvantage_activeOrbit (Z := Z) z0
  refine ⟨hadv, hmass, hnot, ?_, hwitness, hpred, ?_, ?_⟩
  · exact activeOrbitClassifier_not_supportwiseSourceOnly (Z := Z) z0
  · exact exists_positive_prediction_separation_activeOrbit (Z := Z) z0
  · exact
      not_supportwiseVisiblePairBalancing_of_pos_doubledAdvantage_pair
        invariantVisibleData
        (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b)
        activeOrbitTarget
        (activeOrbitWeight z0)
        activeOrbitClassifier
        hadv

end

end Mettapedia.Computability.PNP
