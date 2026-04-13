import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSchwartzPartialPeriodization

/-!
# Navier-Stokes Schwartz Periodization Boxes

This file packages the finite cubic truncation family that underlies the
manuscript's large-torus exhaustion route.  The boxes `[-N, N]^3 ⊂ ℤ^3`
specialize the general finite partial-periodization interface from
`NavierStokesSchwartzPartialPeriodization.lean` to the concrete exhaustion net
used in Appendix H.2/H.4.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

/-- The centered cubic lattice box `[-N, N]^3 ⊂ ℤ^3`. -/
def centeredLatticeBox (N : ℕ) : Finset NSLatticeIndex :=
  Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-((N : ℤ))) (N : ℤ))

/-- Membership in the centered cubic lattice box is coordinatewise bounded. -/
theorem mem_centeredLatticeBox_iff {N : ℕ} {n : NSLatticeIndex} :
    n ∈ centeredLatticeBox N ↔
      ∀ i, n i ∈ Finset.Icc (-((N : ℤ))) (N : ℤ) := by
  simp [centeredLatticeBox, Fintype.mem_piFinset]

/-- Membership in the centered cubic lattice box is equivalent to coordinatewise
absolute-value bounds. -/
theorem mem_centeredLatticeBox_iff_abs_le {N : ℕ} {n : NSLatticeIndex} :
    n ∈ centeredLatticeBox N ↔
      ∀ i, |n i| ≤ (N : ℤ) := by
  rw [mem_centeredLatticeBox_iff]
  simp [Finset.mem_Icc, ← abs_le]

/-- The zero lattice index lies in every centered box. -/
theorem zero_mem_centeredLatticeBox (N : ℕ) :
    (0 : NSLatticeIndex) ∈ centeredLatticeBox N := by
  simp [mem_centeredLatticeBox_iff_abs_le]

/-- The radius-zero centered box contains only the zero lattice index. -/
theorem centeredLatticeBox_zero :
    centeredLatticeBox 0 = ({0} : Finset NSLatticeIndex) := by
  ext n
  simp [mem_centeredLatticeBox_iff_abs_le, funext_iff]

/-- Centered lattice boxes form a monotone exhaustion family. -/
theorem centeredLatticeBox_mono {N M : ℕ} (hNM : N ≤ M) :
    centeredLatticeBox N ⊆ centeredLatticeBox M := by
  have hNM' : (N : ℤ) ≤ (M : ℤ) := by
    exact_mod_cast hNM
  intro n hn
  rw [mem_centeredLatticeBox_iff] at hn ⊢
  intro i
  rcases Finset.mem_Icc.mp (hn i) with ⟨hlo, hhi⟩
  exact Finset.mem_Icc.mpr
    ⟨(neg_le_neg hNM').trans hlo, hhi.trans hNM'⟩

/-- The outer shell added when enlarging the centered lattice box from radius
`N` to radius `N + 1`. -/
def centeredLatticeShell (N : ℕ) : Finset NSLatticeIndex :=
  centeredLatticeBox (N + 1) \ centeredLatticeBox N

/-- The old box and the new shell are disjoint. -/
theorem disjoint_centeredLatticeBox_centeredLatticeShell (N : ℕ) :
    Disjoint (centeredLatticeBox N) (centeredLatticeShell N) := by
  simpa [centeredLatticeShell] using
    (Finset.disjoint_sdiff :
      Disjoint (centeredLatticeBox N)
        (centeredLatticeBox (N + 1) \ centeredLatticeBox N))

/-- Enlarging the centered lattice box by one radius step is the disjoint union
of the previous box and the new shell. -/
theorem centeredLatticeBox_succ_eq_union_shell (N : ℕ) :
    centeredLatticeBox (N + 1) =
      centeredLatticeBox N ∪ centeredLatticeShell N := by
  simpa [centeredLatticeShell] using
    (Finset.union_sdiff_of_subset (centeredLatticeBox_mono (Nat.le_succ N))).symm

/-- The radius-`N` boxed partial periodization of initial data. -/
def boxedPartialPeriodizedInitialVelocity
    (N : ℕ) (L : ℝ) (u₀ : NSInitialVelocity) :
    NSInitialVelocity :=
  finitePartialPeriodizedInitialVelocity (centeredLatticeBox N) L u₀

/-- The radius-zero boxed partial periodization is the original initial datum. -/
theorem boxedPartialPeriodizedInitialVelocity_zero
    (L : ℝ) (u₀ : NSInitialVelocity) :
    boxedPartialPeriodizedInitialVelocity 0 L u₀ = u₀ := by
  unfold boxedPartialPeriodizedInitialVelocity
  rw [centeredLatticeBox_zero]
  ext x
  simp [finitePartialPeriodizedInitialVelocity, periodizationShift_zero]

/-- Boxed partial periodizations of smooth data are smooth. -/
theorem smoothInitialVelocityData_boxedPartialPeriodizedInitialVelocity
    (N : ℕ) (L : ℝ) {u₀ : NSInitialVelocity}
    (hsmooth : smoothInitialVelocityData u₀) :
    smoothInitialVelocityData (boxedPartialPeriodizedInitialVelocity N L u₀) :=
  smoothInitialVelocityData_finitePartialPeriodizedInitialVelocity
    (centeredLatticeBox N) L hsmooth

/-- Boxed partial periodizations preserve divergence freeness on smooth data. -/
theorem divergenceFreeInitialVelocityData_boxedPartialPeriodizedInitialVelocity
    (N : ℕ) (L : ℝ) {u₀ : NSInitialVelocity}
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0) :
    ∀ x, initialSpatialDivergence (boxedPartialPeriodizedInitialVelocity N L u₀) x = 0 :=
  divergenceFreeInitialVelocityData_finitePartialPeriodizedInitialVelocity
    (centeredLatticeBox N) L hsmooth hdiv

/-- The boxed partial periodization at radius `N + 1` splits into the old box
plus the newly added shell. -/
theorem boxedPartialPeriodizedInitialVelocity_succ
    (N : ℕ) (L : ℝ) (u₀ : NSInitialVelocity) :
    boxedPartialPeriodizedInitialVelocity (N + 1) L u₀ =
      boxedPartialPeriodizedInitialVelocity N L u₀ +
        finitePartialPeriodizedInitialVelocity (centeredLatticeShell N) L u₀ := by
  classical
  ext x
  unfold boxedPartialPeriodizedInitialVelocity finitePartialPeriodizedInitialVelocity
  rw [centeredLatticeBox_succ_eq_union_shell]
  rw [Finset.sum_union (disjoint_centeredLatticeBox_centeredLatticeShell N)]
  rfl

/-- The radius-`N` boxed partial periodization of Schwartz initial data. -/
def boxedPartialPeriodizationSchwartzInitialVelocity
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzInitialVelocity) :
    NSSchwartzInitialVelocity :=
  finitePartialPeriodizationSchwartzInitialVelocity (centeredLatticeBox N) L u₀

/-- The boxed Schwartz partial periodization is the expected finite lattice
sum over the centered box. -/
@[simp] theorem boxedPartialPeriodizationSchwartzInitialVelocity_apply
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzInitialVelocity) (x : NSSpace) :
    boxedPartialPeriodizationSchwartzInitialVelocity N L u₀ x =
      (centeredLatticeBox N).sum (fun n => u₀ (x + periodizationShift L n)) := by
  simp [boxedPartialPeriodizationSchwartzInitialVelocity]

/-- The radius-zero boxed Schwartz partial periodization is the original
Schwartz datum. -/
theorem boxedPartialPeriodizationSchwartzInitialVelocity_zero
    (L : ℝ) (u₀ : NSSchwartzInitialVelocity) :
    boxedPartialPeriodizationSchwartzInitialVelocity 0 L u₀ = u₀ := by
  unfold boxedPartialPeriodizationSchwartzInitialVelocity
  rw [centeredLatticeBox_zero]
  ext x
  simp [finitePartialPeriodizationSchwartzInitialVelocity, periodizationShift_zero]

/-- The radius-`N` boxed partial periodization on the manuscript's
`Sσ(ℝ^3)` input class. -/
def boxedPartialPeriodizationSchwartzDivergenceFreeInitialVelocity
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity) :
    NSSchwartzDivergenceFreeInitialVelocity :=
  finitePartialPeriodizationSchwartzDivergenceFreeInitialVelocity
    (centeredLatticeBox N) L u₀

/-- The radius-zero boxed partial periodization on `Sσ(ℝ^3)` is the original
datum. -/
theorem boxedPartialPeriodizationSchwartzDivergenceFreeInitialVelocity_zero
    (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity) :
    boxedPartialPeriodizationSchwartzDivergenceFreeInitialVelocity 0 L u₀ = u₀ := by
  ext x
  simp [boxedPartialPeriodizationSchwartzDivergenceFreeInitialVelocity,
    finitePartialPeriodizationSchwartzDivergenceFreeInitialVelocity,
    centeredLatticeBox_zero, periodizationShift_zero]

end NavierStokes
end FluidDynamics
end Mettapedia
