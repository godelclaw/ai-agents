import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Probability.Distributions.Uniform

namespace Mettapedia.Computability.PNP

namespace PMF

open scoped ENNReal

variable {α : Type*} [Fintype α] [Nonempty α]

/-- Every PMF on a finite nonempty type places at most the uniform mass
`1 / |α|` on some point. -/
theorem exists_apply_le_inv_card (μ : PMF α) :
    ∃ a : α, μ a ≤ (Fintype.card α : ℝ≥0∞)⁻¹ := by
  classical
  have hsumμ : Finset.sum (Finset.univ : Finset α) (fun a => μ a) = 1 := by
    simpa [tsum_fintype] using μ.tsum_coe
  have hsumUniform :
      Finset.sum (Finset.univ : Finset α) (fun _ => (Fintype.card α : ℝ≥0∞)⁻¹) = 1 := by
    calc
      Finset.sum (Finset.univ : Finset α) (fun _ => (Fintype.card α : ℝ≥0∞)⁻¹) =
          Finset.sum (Finset.univ : Finset α) (fun a => PMF.uniformOfFintype α a) := by
        simp [PMF.uniformOfFintype_apply]
      _ = 1 := by
        simpa [tsum_fintype] using (PMF.uniformOfFintype α).tsum_coe
  have hsum :
      Finset.sum (Finset.univ : Finset α) (fun a => μ a) ≤
        Finset.sum (Finset.univ : Finset α) (fun _ => (Fintype.card α : ℝ≥0∞)⁻¹) := by
    exact le_of_eq (hsumμ.trans hsumUniform.symm)
  obtain ⟨a, _ha, hle⟩ :=
    ENNReal.exists_le_of_sum_le
      (s := (Finset.univ : Finset α))
      Finset.univ_nonempty
      hsum
  exact ⟨a, hle⟩

end PMF

end Mettapedia.Computability.PNP
