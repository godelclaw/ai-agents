import Mathlib.Data.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Mettapedia.GraphTheory.FourColor

/-- The scalar field `𝔽₂` used in the boundary-color algebra. -/
abbrev F2 := ZMod 2

/-- The edge-color group `𝔽₂ × 𝔽₂` used in the Goertzel/Kauffman route. -/
abbrev Color := F2 × F2

variable {a b : Color}

/-- The standard red basis color. -/
def red : Color := (1, 0)

/-- The standard blue basis color. -/
def blue : Color := (0, 1)

/-- The standard purple basis color. -/
def purple : Color := (1, 1)

@[simp] theorem zmod2_add_self (x : F2) : x + x = 0 := by
  fin_cases x <;> decide

@[simp] theorem color_add_self (c : Color) : c + c = 0 := by
  ext <;> simp

@[simp] theorem red_add_blue : red + blue = purple := by
  rfl

@[simp] theorem red_add_purple : red + purple = blue := by
  rfl

@[simp] theorem blue_add_purple : blue + purple = red := by
  rfl

@[simp] theorem blue_add_red : blue + red = purple := by
  simpa [add_comm] using red_add_blue

@[simp] theorem purple_add_red : purple + red = blue := by
  simpa [add_comm] using red_add_purple

@[simp] theorem purple_add_blue : purple + blue = red := by
  simp [add_comm]

@[simp] theorem red_ne_zero : red ≠ 0 := by
  decide

@[simp] theorem blue_ne_zero : blue ≠ 0 := by
  decide

@[simp] theorem purple_ne_zero : purple ≠ 0 := by
  decide

@[simp] theorem red_ne_blue : red ≠ blue := by
  decide

@[simp] theorem red_ne_purple : red ≠ purple := by
  decide

@[simp] theorem blue_ne_purple : blue ≠ purple := by
  decide

@[simp] theorem color_neg_eq (c : Color) : -c = c := by
  exact (eq_neg_of_add_eq_zero_left (color_add_self c)).symm

theorem add_eq_zero_iff_eq (a b : Color) : a + b = 0 ↔ a = b := by
  constructor
  · intro hab
    calc
      a = a + 0 := by simp
      _ = a + (b + b) := by rw [color_add_self]
      _ = (a + b) + b := by abel
      _ = 0 + b := by rw [hab]
      _ = b := by simp
  · intro hab
    simp [hab]

theorem add_ne_zero_of_ne (hab : a ≠ b) : a + b ≠ 0 := by
  intro hzero
  exact hab ((add_eq_zero_iff_eq a b).mp hzero)

theorem add_ne_left_of_ne_zero (hb : b ≠ 0) : a + b ≠ a := by
  intro hab
  have : b = 0 := by
    calc
      b = 0 + b := by simp
      _ = (a + a) + b := by rw [color_add_self]
      _ = a + (a + b) := by abel
      _ = a + a := by rw [hab]
      _ = 0 := color_add_self a
  exact hb this

theorem add_ne_right_of_ne_zero (ha : a ≠ 0) : a + b ≠ b := by
  intro hab
  have : a = 0 := by
    calc
      a = a + 0 := by simp
      _ = a + (b + b) := by rw [color_add_self]
      _ = (a + b) + b := by abel
      _ = b + b := by rw [hab]
      _ = 0 := color_add_self b
  exact ha this

theorem third_color_properties (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    a + b ≠ 0 ∧ a + b ≠ a ∧ a + b ≠ b := by
  exact ⟨add_ne_zero_of_ne hab, add_ne_left_of_ne_zero hb, add_ne_right_of_ne_zero ha⟩

/-- The color-valued indicator of a finite edge set. -/
def indicatorChain {E : Type*} [DecidableEq E] (γ : Color) (S : Finset E) : E → Color :=
  fun e => if e ∈ S then γ else 0

@[simp] theorem indicatorChain_apply_of_mem {E : Type*} [DecidableEq E]
    (γ : Color) {S : Finset E} {e : E} (he : e ∈ S) :
    indicatorChain γ S e = γ := by
  simp [indicatorChain, he]

@[simp] theorem indicatorChain_apply_of_not_mem {E : Type*} [DecidableEq E]
    (γ : Color) {S : Finset E} {e : E} (he : e ∉ S) :
    indicatorChain γ S e = 0 := by
  simp [indicatorChain, he]

end Mettapedia.GraphTheory.FourColor
