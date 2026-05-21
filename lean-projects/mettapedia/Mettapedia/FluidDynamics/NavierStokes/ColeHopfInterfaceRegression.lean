import Mettapedia.FluidDynamics.NavierStokes.ColeHopfInterface

/-!
# Regression Tests for Explicit Finite-Frame Vorticity Constants
-/

set_option autoImplicit false

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace ColeHopfInterfaceRegression

theorem gamma_le_card_mul_sq_of_abs_le_regression :
    gamma (fun i : Fin 3 => if i.1 = 0 then (1 : ℝ) else -1) ≤ (3 : ℝ) * 1 ^ 2 := by
  refine gamma_le_card_mul_sq_of_abs_le
    (D := fun i : Fin 3 => if i.1 = 0 then (1 : ℝ) else -1) ?_ ?_
  · norm_num
  · intro i
    fin_cases i <;> norm_num

def constantCurlFrame : Fin 2 → Unit → ℝ := fun _ _ => 2

def zeroEnergyColeHopfIdentityData :
    ColeHopfIdentityData (Time := Unit) (ι := Fin 2) (X := Unit) where
  Phi := fun _ => 1
  dPhi := fun _ _ => 0
  ν := 3
  mPhi := 1
  energyBound := 0
  curlFrame := constantCurlFrame
  curlBound := 8
  mPhi_pos := by norm_num
  energyBound_nonneg := by norm_num
  curlBound_nonneg := by norm_num
  Phi_lower := by
    intro t
    norm_num
  dPhi_energy := by
    intro t
    simp [gamma]
  curl_energy := by
    intro x
    simp [constantCurlFrame, gamma]
    norm_num

theorem zero_energy_componentwise_curl_regression
    (t : Unit) (x : Unit) :
    |zeroEnergyColeHopfIdentityData.vorticity t x| ≤
      Real.sqrt ((4 * (3 : ℝ) ^ 2 / 1 ^ 2) * 0) *
        Real.sqrt ((Fintype.card (Fin 2) : ℝ) * 2 ^ 2) := by
  simpa [zeroEnergyColeHopfIdentityData, constantCurlFrame] using
    zeroEnergyColeHopfIdentityData.abs_vorticity_le_of_componentwise_abs_le
      (M := 2)
      (by norm_num)
      (by
        intro x i
        change |constantCurlFrame i x| ≤ 2
        norm_num [constantCurlFrame])
      t x

end ColeHopfInterfaceRegression
end NavierStokes
end FluidDynamics
end Mettapedia
