import Mettapedia.GraphTheory.FourColor.Orthogonality

namespace Mettapedia.GraphTheory.FourColor

example : colorDot red blue = 0 := by
  decide

example : colorDot purple blue = 1 := by
  decide

example (z : Color) (hzBlue : colorDot z blue = 0) (hzPurple : colorDot z purple = 0) : z = 0 := by
  apply eq_zero_of_colorDot_eq_zero_for_all_nonzero_ne red_ne_zero
  intro γ hγ0 hγred
  rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero γ hγ0 with rfl | rfl | rfl
  · exact False.elim (hγred rfl)
  · simpa using hzBlue
  · simpa using hzPurple

example (x : Unit → Color) (γ : Color) :
    chainDot ({()} : Finset Unit) x (indicatorChain γ {()}) = colorDot (x ()) γ := by
  apply chainDot_indicatorChain_eq_colorDot_of_erase_zero γ
  · simp
  · intro e' he'
    simp at he'

end Mettapedia.GraphTheory.FourColor
