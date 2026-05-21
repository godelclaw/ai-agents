import Mettapedia.Computability.PNP.BitFamilyERM
import Mettapedia.Computability.PNP.FiniteUniformRecovery

/-!
# P vs NP grassroots: bit-family uniform recovery

This file connects the pure finite uniform recovery threshold to the
`BitEncodedClassifierFamily` ERM wrapper.  The generic recovery theorem uses an
encoded-family ERM selector requiring a nonempty code type; the bit-family
wrapper already packages the canonical inhabitant of `BitCode s`.
-/

namespace Mettapedia.Computability.PNP

universe u

namespace BitEncodedClassifierFamily

section UniformRecovery

variable {Input : Type u} [Fintype Input]
variable {s : ℕ} (F : BitEncodedClassifierFamily Input s)

/-- Bit-budget exact-recovery existence theorem.  Once the target is realized
by an `s`-bit family and the finite counting threshold holds, bit-family ERM
exactly recovers the target on at least one labeled point sample. -/
theorem exists_sample_empiricalRiskPredictor_eq_target_of_bitBudget_bound_lt
    (target : Input → Bool) (m : ℕ)
    (htarget : ∃ c : BitCode s, F.decode c = target)
    (hbound :
      2 ^ s * (Fintype.card Input - 1) ^ m <
        Fintype.card Input ^ m) :
    ∃ sample : PointSample Input m,
      F.empiricalRiskPredictor (labeledByTarget target sample) = target := by
  letI : Nonempty F.toEncodedFamily.Code := by
    change Nonempty (BitCode s)
    exact ⟨fun _ => false⟩
  have htarget' :
      ∃ c : F.toEncodedFamily.Code, F.toEncodedFamily.decode c = target := by
    change ∃ c : BitCode s, F.decode c = target
    exact htarget
  have hbound' :
      Fintype.card F.toEncodedFamily.Code * (Fintype.card Input - 1) ^ m <
        Fintype.card Input ^ m := by
    change Fintype.card (BitCode s) * (Fintype.card Input - 1) ^ m <
      Fintype.card Input ^ m
    rw [card_bitCode]
    exact hbound
  rcases
      F.toEncodedFamily.exists_sample_empiricalRiskPredictor_eq_target_of_bound_lt
        target m htarget' hbound' with
    ⟨sample, hsample⟩
  refine ⟨sample, ?_⟩
  simpa [BitEncodedClassifierFamily.empiricalRiskPredictor,
    BitEncodedClassifierFamily.empiricalRiskCode] using hsample

end UniformRecovery

end BitEncodedClassifierFamily

end Mettapedia.Computability.PNP
