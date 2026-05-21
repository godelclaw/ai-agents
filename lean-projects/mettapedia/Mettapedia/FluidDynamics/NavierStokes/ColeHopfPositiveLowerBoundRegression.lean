import Mettapedia.FluidDynamics.NavierStokes.ColeHopfPositiveLowerBound

/-!
# Regression Tests for Cole-Hopf Positive Lower Bounds
-/

set_option autoImplicit false

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace ColeHopfPositiveLowerBoundRegression

theorem constant_one_has_lower_bound_regression :
    HasColeHopfPointwiseLowerBound (fun _ : Unit => (1 : ℝ)) 1 := by
  constructor
  · norm_num
  · intro x
    norm_num

theorem zero_value_has_no_lower_bound_regression :
    ¬ ∃ m : ℝ, HasColeHopfPointwiseLowerBound (fun _ : Unit => (0 : ℝ)) m := by
  exact not_exists_hasColeHopfPointwiseLowerBound_of_zero_value
    (phi := fun _ : Unit => (0 : ℝ)) (x := ()) rfl

theorem nonpositive_value_has_no_fixed_lower_bound_regression :
    ¬ HasColeHopfPointwiseLowerBound (fun _ : Unit => (-1 : ℝ)) (1 / 2) := by
  exact not_hasColeHopfPointwiseLowerBound_of_nonpos_value
    (phi := fun _ : Unit => (-1 : ℝ)) (m := 1 / 2) (x := ()) (by norm_num)

theorem gamma_div_le_from_lower_bound_regression :
    gamma (fun i : Fin 2 => (if i = 0 then (3 : ℝ) else 4) / (2 : ℝ)) ≤
      gamma (fun i : Fin 2 => if i = 0 then (3 : ℝ) else 4) / (1 : ℝ) ^ 2 := by
  have hbound :
      HasColeHopfPointwiseLowerBound (fun _ : Unit => (2 : ℝ)) 1 := by
    constructor
    · norm_num
    · intro x
      norm_num
  exact
    (hbound.gamma_div_le
      (D := fun i : Fin 2 => if i = 0 then (3 : ℝ) else 4) ())

theorem no_identity_data_with_zero_phi_regression :
    ¬ ∃ S : ColeHopfIdentityData (Time := Unit) (ι := Fin 1) (X := Unit),
      S.Phi = (fun _ : Unit => (0 : ℝ)) := by
  exact not_exists_ColeHopfIdentityData_of_zero_phi
    (Time := Unit) (ι := Fin 1) (X := Unit)
    (phi := fun _ : Unit => (0 : ℝ)) (t0 := ()) rfl

/-- A concrete strictly positive field with no uniform positive lower bound. -/
def positiveRayValue (x : {r : ℝ // 0 < r}) : ℝ :=
  x.1

theorem positiveRayValue_pointwise_positive_regression
    (x : {r : ℝ // 0 < r}) :
    0 < positiveRayValue x :=
  x.2

theorem positiveRayValue_arbitrarilySmall_regression :
    HasArbitrarilySmallColeHopfValues positiveRayValue := by
  intro m hm
  refine ⟨⟨m / 2, by nlinarith⟩, ?_⟩
  simp [positiveRayValue]
  nlinarith

theorem positiveRayValue_has_no_lower_bound_regression :
    ¬ ∃ m : ℝ, HasColeHopfPointwiseLowerBound positiveRayValue m := by
  exact not_exists_hasColeHopfPointwiseLowerBound_of_arbitrarilySmallValues
    positiveRayValue_arbitrarilySmall_regression

theorem no_identity_data_with_arbitrarily_small_positive_phi_regression :
    ¬ ∃ S :
      ColeHopfIdentityData (Time := {r : ℝ // 0 < r}) (ι := Fin 1) (X := Unit),
      S.Phi = positiveRayValue := by
  exact not_exists_ColeHopfIdentityData_of_arbitrarilySmall_phi
    (Time := {r : ℝ // 0 < r}) (ι := Fin 1) (X := Unit)
    (phi := positiveRayValue)
    positiveRayValue_arbitrarilySmall_regression

theorem positiveRayValue_derivative_lower_bound_regression :
    HasUniformAbsDerivativeLowerBound (fun _ : {r : ℝ // 0 < r} => (1 : ℝ)) 1 := by
  constructor
  · norm_num
  · intro x
    norm_num

theorem positiveRayValue_logDerivative_unbounded_regression :
    ¬ ∃ B : ℝ,
      ∀ x : {r : ℝ // 0 < r}, |(1 : ℝ) / positiveRayValue x| ≤ B := by
  exact not_exists_uniform_abs_logDerivative_bound_of_arbitrarilySmallValues
    (phi := positiveRayValue)
    (dphi := fun _ : {r : ℝ // 0 < r} => (1 : ℝ))
    positiveRayValue_pointwise_positive_regression
    positiveRayValue_arbitrarilySmall_regression
    positiveRayValue_derivative_lower_bound_regression

theorem positiveRayValue_singleton_logEnergy_unbounded_regression :
    ¬ ∃ B : ℝ,
      ∀ x : {r : ℝ // 0 < r},
        gamma (fun _ : Fin 1 => (1 : ℝ) / positiveRayValue x) ≤ B := by
  exact not_exists_uniform_singleton_logDerivative_gamma_bound_of_arbitrarilySmallValues
    (phi := positiveRayValue)
    (dphi := fun _ : {r : ℝ // 0 < r} => (1 : ℝ))
    positiveRayValue_pointwise_positive_regression
    positiveRayValue_arbitrarilySmall_regression
    positiveRayValue_derivative_lower_bound_regression

/-- The proportional repair model where the derivative vanishes with `Phi`. -/
def positiveRaySelfDerivative (x : {r : ℝ // 0 < r}) : ℝ :=
  positiveRayValue x

theorem positiveRaySelfDerivative_logDerivative_bound_regression :
    ∀ x : {r : ℝ // 0 < r},
      |positiveRaySelfDerivative x / positiveRayValue x| ≤ 1 := by
  intro x
  have hx : positiveRayValue x ≠ 0 :=
    ne_of_gt (positiveRayValue_pointwise_positive_regression x)
  rw [positiveRaySelfDerivative, div_self hx]
  norm_num

theorem positiveRaySelfDerivative_arbitrarilySmall_abs_regression :
    HasArbitrarilySmallAbsValues positiveRaySelfDerivative := by
  exact abs_derivative_arbitrarilySmall_of_uniform_abs_logDerivative_bound
    (phi := positiveRayValue)
    (dphi := positiveRaySelfDerivative)
    positiveRayValue_pointwise_positive_regression
    positiveRayValue_arbitrarilySmall_regression
    positiveRaySelfDerivative_logDerivative_bound_regression

theorem positiveRaySelfDerivative_has_no_derivative_lower_bound_regression :
    ¬ ∃ a : ℝ, HasUniformAbsDerivativeLowerBound positiveRaySelfDerivative a := by
  exact not_exists_absDerivativeLowerBound_of_uniform_abs_logDerivative_bound
    (phi := positiveRayValue)
    (dphi := positiveRaySelfDerivative)
    positiveRayValue_pointwise_positive_regression
    positiveRayValue_arbitrarilySmall_regression
    positiveRaySelfDerivative_logDerivative_bound_regression

end ColeHopfPositiveLowerBoundRegression
end NavierStokes
end FluidDynamics
end Mettapedia
