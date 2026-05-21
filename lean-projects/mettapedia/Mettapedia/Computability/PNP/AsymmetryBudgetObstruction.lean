import Mettapedia.Computability.PNP.ResidualSymmetryObstruction
import Mathlib.Tactic

/-!
# P vs NP crux: advantage is bounded by symmetry-breaking mass

The residual-symmetry obstruction shows that every slice where the retained
features are still involution-invariant remains exactly at chance under
symmetry-respecting weights.

This file turns that into a quantitative budget theorem.  Any excess over chance
must come from the mass where the symmetry is genuinely broken.  So a proof that
keeps only a little non-invariant information must also prove that almost all
relevant mass lies outside the unresolved symmetric slice.
-/

namespace Mettapedia.Computability.PNP

section

variable {α U : Type*} [Fintype α]

/-- The total weight of a finite domain. -/
def weightedTotalMass (w : α → ℕ) : ℕ :=
  ∑ x : α, w x

/-- The total weight of one slice. -/
def sliceMass (p : α → Prop) [DecidablePred p] (w : α → ℕ) : ℕ :=
  ∑ x : {x : α // p x}, w x.1

/-- The weight outside one slice. -/
def outsideMass (p : α → Prop) [DecidablePred p] (w : α → ℕ) : ℕ :=
  sliceMass (fun x => ¬ p x) w

/-- The correct mass restricted to one slice. -/
def correctSliceMass
    (p : α → Prop) [DecidablePred p]
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool) : ℕ :=
  weightedCorrectMass (fun x : {x : α // p x} => u x.1)
    (fun x : {x : α // p x} => y x.1)
    (fun x : {x : α // p x} => w x.1) h

/-- The incorrect mass restricted to one slice. -/
def incorrectSliceMass
    (p : α → Prop) [DecidablePred p]
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool) : ℕ :=
  weightedIncorrectMass (fun x : {x : α // p x} => u x.1)
    (fun x : {x : α // p x} => y x.1)
    (fun x : {x : α // p x} => w x.1) h

/-- The correct mass outside one slice. -/
def correctOutsideMass
    (p : α → Prop) [DecidablePred p]
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool) : ℕ :=
  correctSliceMass (fun x => ¬ p x) u y w h

/-- The incorrect mass outside one slice. -/
def incorrectOutsideMass
    (p : α → Prop) [DecidablePred p]
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool) : ℕ :=
  incorrectSliceMass (fun x => ¬ p x) u y w h

/-- The correct points can be restricted first by correctness and then by the
slice predicate, or the other way around. -/
def correctSubtypeSliceEquiv
    (p : α → Prop) [DecidablePred p]
    (u : α → U) (y : α → Bool) (h : U → Bool) :
    {x : {x : α // Correct u y h x} // p x.1} ≃
      {x : {x : α // p x} //
        Correct (fun z : {x : α // p x} => u z.1)
          (fun z : {x : α // p x} => y z.1) h x} where
  toFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩
  invFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl

/-- The same rearrangement for correct points outside the slice. -/
def correctSubtypeOutsideEquiv
    (p : α → Prop) [DecidablePred p]
    (u : α → U) (y : α → Bool) (h : U → Bool) :
    {x : {x : α // Correct u y h x} // ¬ p x.1} ≃
      {x : {x : α // ¬ p x} //
        Correct (fun z : {x : α // ¬ p x} => u z.1)
          (fun z : {x : α // ¬ p x} => y z.1) h x} where
  toFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩
  invFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl

theorem weightedTotalMass_eq_slice_add_outside
    (p : α → Prop) [DecidablePred p] (w : α → ℕ) :
    weightedTotalMass w = sliceMass p w + outsideMass p w := by
  classical
  unfold weightedTotalMass sliceMass outsideMass
  simpa using (Fintype.sum_subtype_add_sum_subtype p w).symm

theorem sliceMass_eq_correct_add_incorrect
    (p : α → Prop) [DecidablePred p]
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool) :
    sliceMass p w = correctSliceMass p u y w h + incorrectSliceMass p u y w h := by
  classical
  let u' : {x : α // p x} → U := fun x => u x.1
  let y' : {x : α // p x} → Bool := fun x => y x.1
  unfold sliceMass correctSliceMass incorrectSliceMass
  unfold weightedCorrectMass weightedIncorrectMass
  simpa [u', y', incorrect_iff_not_correct] using
    (Fintype.sum_subtype_add_sum_subtype
      (fun x : {x : α // p x} => Correct u' y' h x)
      (fun x : {x : α // p x} => w x.1)).symm

theorem weightedCorrectMass_eq_correctSlice_add_correctOutside
    (p : α → Prop) [DecidablePred p]
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool) :
    weightedCorrectMass u y w h =
      correctSliceMass p u y w h + correctOutsideMass p u y w h := by
  classical
  let q : {x : α // Correct u y h x} → Prop := fun x => p x.1
  have hsplit :
      weightedCorrectMass u y w h =
        (∑ x : {x : {x : α // Correct u y h x} // q x}, w x.1.1) +
        ∑ x : {x : {x : α // Correct u y h x} // ¬ q x}, w x.1.1 := by
    simpa [weightedCorrectMass, q] using
      (Fintype.sum_subtype_add_sum_subtype q
        (fun x : {x : α // Correct u y h x} => w x.1)).symm
  have hleft :
      (∑ x : {x : {x : α // Correct u y h x} // q x}, w x.1.1) =
        correctSliceMass p u y w h := by
    unfold correctSliceMass weightedCorrectMass
    exact Fintype.sum_equiv (correctSubtypeSliceEquiv p u y h)
      (fun x : {x : {x : α // Correct u y h x} // q x} => w x.1.1)
      (fun x : {x : {x : α // p x} //
        Correct (fun z : {x : α // p x} => u z.1)
          (fun z : {x : α // p x} => y z.1) h x} => w x.1.1)
      (fun x => rfl)
  have hright :
      (∑ x : {x : {x : α // Correct u y h x} // ¬ q x}, w x.1.1) =
        correctOutsideMass p u y w h := by
    unfold correctOutsideMass correctSliceMass weightedCorrectMass
    exact Fintype.sum_equiv (correctSubtypeOutsideEquiv p u y h)
      (fun x : {x : {x : α // Correct u y h x} // ¬ q x} => w x.1.1)
      (fun x : {x : {x : α // ¬ p x} //
        Correct (fun z : {x : α // ¬ p x} => u z.1)
          (fun z : {x : α // ¬ p x} => y z.1) h x} => w x.1.1)
      (fun x => rfl)
  rw [hsplit, hleft, hright]

theorem correctOutsideMass_le_outsideMass
    (p : α → Prop) [DecidablePred p]
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool) :
    correctOutsideMass p u y w h ≤ outsideMass p w := by
  have hsplit :
      outsideMass p w =
        correctOutsideMass p u y w h + incorrectOutsideMass p u y w h := by
    simpa [outsideMass, correctOutsideMass, incorrectOutsideMass] using
      sliceMass_eq_correct_add_incorrect (p := fun x => ¬ p x) u y w h
  omega

/-- On a residual slice where symmetry remains exact, the correct mass is
exactly half of the slice mass. -/
theorem two_mul_correctSliceMass_eq_sliceMass
    (τ : α → α) (p : α → Prop) [DecidablePred p]
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool)
    (hτ : Function.Involutive τ)
    (hp : ∀ x, p x → p (τ x))
    (hu : ∀ x, p x → u (τ x) = u x)
    (hy : ∀ x, p x → y (τ x) = !(y x))
    (hw : ∀ x, p x → w (τ x) = w x) :
    2 * correctSliceMass p u y w h = sliceMass p w := by
  have heq :
      correctSliceMass p u y w h = incorrectSliceMass p u y w h := by
    simpa [correctSliceMass, incorrectSliceMass] using
      (weightedCorrectMass_eq_weightedIncorrectMass_on_slice
        (α := α) (U := U) (β := ℕ)
        τ p u y w h hτ hp hu hy hw)
  have hsplit := sliceMass_eq_correct_add_incorrect p u y w h
  omega

/-- Quantitative form: any advantage over chance is bounded by the weight
outside the unresolved symmetric slice. -/
theorem two_mul_weightedCorrectMass_le_total_plus_outside
    (τ : α → α) (p : α → Prop) [DecidablePred p]
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool)
    (hτ : Function.Involutive τ)
    (hp : ∀ x, p x → p (τ x))
    (hu : ∀ x, p x → u (τ x) = u x)
    (hy : ∀ x, p x → y (τ x) = !(y x))
    (hw : ∀ x, p x → w (τ x) = w x) :
    2 * weightedCorrectMass u y w h ≤ weightedTotalMass w + outsideMass p w := by
  have hcorr :
      weightedCorrectMass u y w h =
        correctSliceMass p u y w h + correctOutsideMass p u y w h :=
    weightedCorrectMass_eq_correctSlice_add_correctOutside p u y w h
  have hslice :
      2 * correctSliceMass p u y w h = sliceMass p w :=
    two_mul_correctSliceMass_eq_sliceMass τ p u y w h hτ hp hu hy hw
  have hout :
      correctOutsideMass p u y w h ≤ outsideMass p w :=
    correctOutsideMass_le_outsideMass p u y w h
  have htotal :
      weightedTotalMass w = sliceMass p w + outsideMass p w :=
    weightedTotalMass_eq_slice_add_outside p w
  omega

/-- If all positive weight lies inside the unresolved symmetric slice, then
the outside budget is zero. -/
theorem outsideMass_eq_zero_of_support_subset
    (p : α → Prop) [DecidablePred p] (w : α → ℕ)
    (hsupport : ∀ x, 0 < w x → p x) :
    outsideMass p w = 0 := by
  classical
  unfold outsideMass sliceMass
  apply Finset.sum_eq_zero
  intro x _
  exact Nat.eq_zero_of_not_pos fun hpos => x.2 (hsupport x.1 hpos)

/-- If every positive-weight point remains in the unresolved symmetric slice,
then no classifier on the retained features can have strict advantage over
half accuracy. -/
theorem not_total_lt_two_mul_weightedCorrectMass_of_support_subset
    (τ : α → α) (p : α → Prop) [DecidablePred p]
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool)
    (hτ : Function.Involutive τ)
    (hp : ∀ x, p x → p (τ x))
    (hu : ∀ x, p x → u (τ x) = u x)
    (hy : ∀ x, p x → y (τ x) = !(y x))
    (hw : ∀ x, p x → w (τ x) = w x)
    (hsupport : ∀ x, 0 < w x → p x) :
    ¬ weightedTotalMass w < 2 * weightedCorrectMass u y w h := by
  have hle :=
    two_mul_weightedCorrectMass_le_total_plus_outside
      τ p u y w h hτ hp hu hy hw
  have hout : outsideMass p w = 0 :=
    outsideMass_eq_zero_of_support_subset p w hsupport
  omega

/-- Strict advantage over half accuracy forces positive outside mass. -/
theorem pos_outsideMass_of_total_lt_two_mul_weightedCorrectMass
    (τ : α → α) (p : α → Prop) [DecidablePred p]
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool)
    (hτ : Function.Involutive τ)
    (hp : ∀ x, p x → p (τ x))
    (hu : ∀ x, p x → u (τ x) = u x)
    (hy : ∀ x, p x → y (τ x) = !(y x))
    (hw : ∀ x, p x → w (τ x) = w x)
    (hadv : weightedTotalMass w < 2 * weightedCorrectMass u y w h) :
    0 < outsideMass p w := by
  by_contra hnot
  have hle :=
    two_mul_weightedCorrectMass_le_total_plus_outside
      τ p u y w h hτ hp hu hy hw
  have hout : outsideMass p w = 0 := Nat.eq_zero_of_not_pos hnot
  omega

/-- Positive outside mass exposes a concrete positive-weight point outside the
unresolved symmetric slice. -/
theorem exists_support_outside_of_pos_outsideMass
    (p : α → Prop) [DecidablePred p] (w : α → ℕ)
    (hpos : 0 < outsideMass p w) :
    ∃ x, 0 < w x ∧ ¬ p x := by
  classical
  unfold outsideMass sliceMass at hpos
  by_contra hnone
  have hzero :
      (∑ x : {x : α // ¬ p x}, w x.1) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    exact Nat.eq_zero_of_not_pos fun hweight =>
      hnone ⟨x.1, hweight, x.2⟩
  exact (Nat.ne_of_gt hpos) hzero

/-- Therefore any strict advantage claim must provide a positive-weight point
outside the unresolved symmetric slice. -/
theorem exists_support_outside_of_total_lt_two_mul_weightedCorrectMass
    (τ : α → α) (p : α → Prop) [DecidablePred p]
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool)
    (hτ : Function.Involutive τ)
    (hp : ∀ x, p x → p (τ x))
    (hu : ∀ x, p x → u (τ x) = u x)
    (hy : ∀ x, p x → y (τ x) = !(y x))
    (hw : ∀ x, p x → w (τ x) = w x)
    (hadv : weightedTotalMass w < 2 * weightedCorrectMass u y w h) :
    ∃ x, 0 < w x ∧ ¬ p x :=
  exists_support_outside_of_pos_outsideMass p w
    (pos_outsideMass_of_total_lt_two_mul_weightedCorrectMass
      τ p u y w h hτ hp hu hy hw hadv)

end

end Mettapedia.Computability.PNP
