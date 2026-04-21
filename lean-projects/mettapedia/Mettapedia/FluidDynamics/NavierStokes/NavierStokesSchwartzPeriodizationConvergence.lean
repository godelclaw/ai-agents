import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSchwartzPeriodizationBoxes
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Basis.Submodule

/-!
# Navier-Stokes Schwartz Periodization Convergence Interface

This file packages the first explicit local convergence interface sitting above
the finite box exhaustion family from `NavierStokesSchwartzPeriodizationBoxes`.
Instead of proving the Schwartz periodization limit outright, we isolate the
exact theorem surface that Appendix H.4 uses on fixed cubes `Q_R`: if the boxed
partial periodizations converge locally, then the shell increments must vanish
locally as well.
-/

set_option autoImplicit false

noncomputable section

open Filter

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open scoped BigOperators

/-- The standard integer lattice `ℤ^3 ⊂ ℝ^3` inside the fixed concrete space. -/
abbrev NSCoordinateLattice : Submodule ℤ NSSpace :=
  Submodule.span ℤ (Set.range ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis))

/-- The standard Euclidean basis, restricted from `ℝ`-coefficients to the
integer lattice it spans, gives a concrete `ℤ`-basis of `ℤ^3 ⊂ ℝ^3`. -/
noncomputable abbrev nsCoordinateLatticeBasis : Module.Basis (Fin 3) ℤ NSCoordinateLattice :=
  (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.restrictScalars ℤ

/-- Coordinate-lattice points are equivalent to the raw index type `Fin 3 → ℤ`
used by the periodization boxes. -/
noncomputable abbrev nsCoordinateLatticeEquiv :
    NSCoordinateLattice ≃ₗ[ℤ] NSLatticeIndex :=
  (nsCoordinateLatticeBasis.repr).trans
    (Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin 3))

/-- The raw lattice-index type `ℤ^3` viewed as the concrete coordinate lattice
subtype. -/
noncomputable abbrev nsCoordinateLatticePointEquiv : NSLatticeIndex ≃ NSCoordinateLattice :=
  (nsCoordinateLatticeEquiv : NSCoordinateLattice ≃ₗ[ℤ] NSLatticeIndex).toEquiv.symm

instance : DiscreteTopology NSCoordinateLattice := by
  refine DiscreteTopology.of_continuous_injective
    (f := (nsCoordinateLatticeEquiv : NSCoordinateLattice → NSLatticeIndex))
    continuous_of_discreteTopology nsCoordinateLatticeEquiv.injective

/-- The concrete lattice point associated to an index `n : ℤ^3`. -/
noncomputable def nsCoordinateLatticePoint (n : NSLatticeIndex) : NSCoordinateLattice :=
  nsCoordinateLatticePointEquiv n

/-- The concrete lattice point corresponding to `n` has the expected real
coordinates. -/
theorem nsCoordinateLatticePoint_coe_apply
    (n : NSLatticeIndex) (i : Fin 3) :
    ((nsCoordinateLatticePoint n : NSCoordinateLattice) : NSSpace) i = (n i : ℝ) := by
  have hrepr :
      nsCoordinateLatticeBasis.repr (nsCoordinateLatticePoint n) i = n i := by
    have hpoint : nsCoordinateLatticeEquiv (nsCoordinateLatticePoint n) = n := by
      simp [nsCoordinateLatticePoint]
    simpa [nsCoordinateLatticeEquiv] using congrFun hpoint i
  have hcast :
      ((nsCoordinateLatticeBasis.repr (nsCoordinateLatticePoint n) i : ℤ) : ℝ) =
        ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.repr
          (((nsCoordinateLatticePoint n : NSCoordinateLattice) : NSSpace)) i) := by
    simpa [nsCoordinateLatticeBasis] using
      (Module.Basis.restrictScalars_repr_apply
        (R := ℤ) ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis)
        (nsCoordinateLatticePoint n) i)
  simpa [EuclideanSpace.basisFun_repr, hrepr] using hcast.symm

/-- The periodization shift is exactly scalar multiplication of the associated
concrete lattice point. -/
theorem periodizationShift_eq_smul_nsCoordinateLatticePoint
    (L : ℝ) (n : NSLatticeIndex) :
    periodizationShift L n =
      (2 * Real.pi * L) • ((nsCoordinateLatticePoint n : NSCoordinateLattice) : NSSpace) := by
  ext i
  simp [periodizationShift, nsCoordinateLatticePoint_coe_apply]

/-- Every lattice index lies in some centered cubic box. -/
theorem exists_mem_centeredLatticeBox (n : NSLatticeIndex) :
    ∃ N : ℕ, n ∈ centeredLatticeBox N := by
  let M : ℤ := max (|n 0|) (max (|n 1|) (|n 2|))
  have hM : ∀ i : Fin 3, |n i| ≤ M := by
    intro i
    fin_cases i <;> simp [M]
  have hMnonneg : 0 ≤ M := by
    exact le_trans (abs_nonneg (n 0)) (hM 0)
  refine ⟨Int.toNat M, ?_⟩
  rw [mem_centeredLatticeBox_iff_abs_le]
  intro i
  simpa [Int.toNat_of_nonneg hMnonneg] using hM i

/-- The centered lattice boxes exhaust the raw index type `ℤ^3`. -/
theorem centeredLatticeBox_tendsto_atTop :
    Tendsto centeredLatticeBox Filter.atTop Filter.atTop :=
  Filter.tendsto_atTop_finset_of_monotone
    (fun _ _ hNM => centeredLatticeBox_mono hNM)
    exists_mem_centeredLatticeBox

/-- Explicit order-4 Schwartz bound on the norm of a vector-valued initial datum. -/
theorem schwartz_norm_le_orderFour
    (u₀ : NSSchwartzInitialVelocity) (x : NSSpace) :
    ‖u₀ x‖ ≤
      ((2 : ℝ) ^ (4 : ℕ) *
        (Finset.Iic (4, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) u₀) /
        (1 + ‖x‖) ^ 4 := by
  refine (le_div_iff₀ (by positivity)).2 ?_
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    (SchwartzMap.one_add_le_sup_seminorm_apply
      (m := (4, 0)) (k := 4) (n := 0) le_rfl le_rfl u₀ x)

/-- The uniform order-4 Schwartz seminorm constant used in the local
periodization estimates. -/
noncomputable def schwartzOrderFourConstant (u₀ : NSSchwartzInitialVelocity) : ℝ :=
  (2 : ℝ) ^ (4 : ℕ) *
    (Finset.Iic (4, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) u₀

theorem schwartzOrderFourConstant_nonneg (u₀ : NSSchwartzInitialVelocity) :
    0 ≤ schwartzOrderFourConstant u₀ := by
  dsimp [schwartzOrderFourConstant]
  positivity

/-- Recenter `x + c z` as a scaled translate of `z` when `c ≠ 0`. -/
theorem add_periodizationScale_eq_smul_sub
    {c : ℝ} (hc : c ≠ 0) (x z : NSSpace) :
    x + c • z = c • (z - (-(c⁻¹) • x)) := by
  calc
    x + c • z = c • (c⁻¹ • x) + c • z := by simp [hc, smul_smul]
    _ = c • (c⁻¹ • x + z) := by rw [smul_add]
    _ = c • (z + c⁻¹ • x) := by rw [add_comm]
    _ = c • (z - (-(c⁻¹) • x)) := by simp [sub_eq_add_neg]

/-- Only finitely many standard lattice points can lie in a fixed closed ball. -/
theorem finite_nsCoordinateLatticePoints_mem_closedBall
    (y : NSSpace) (r : ℝ) :
    Set.Finite {z : NSCoordinateLattice | ‖(z : NSSpace) - y‖ ≤ r} := by
  convert
    (ZSpan.setFinite_inter (b := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis)
      (s := Metric.closedBall y r)
      (hs := Metric.isBounded_closedBall)).preimage_embedding (.subtype _)
  ext z
  simp [NSCoordinateLattice, Metric.mem_closedBall, dist_eq_norm_sub]

/-- Off the small exceptional ball around `-(c⁻¹) • x`, a Schwartz translate is
dominated by the rank-3 lattice `‖·‖^{-4}` majorant needed for comparison. -/
theorem norm_schwartz_periodized_term_le_latticeDecay
    {c : ℝ} (hc : c ≠ 0) (u₀ : NSSchwartzInitialVelocity) (x : NSSpace)
    (z : NSCoordinateLattice)
    (hz :
      ‖(z : NSSpace) - (-(c⁻¹) • x)‖ > ‖c‖⁻¹) :
    ‖u₀ (x + c • (z : NSSpace))‖ ≤
      (schwartzOrderFourConstant u₀ * ‖c‖ ^ (-4 : ℤ)) *
        ‖(z : NSSpace) - (-(c⁻¹) • x)‖ ^ (-4 : ℤ) := by
  let y : NSSpace := -(c⁻¹) • x
  let C : ℝ := schwartzOrderFourConstant u₀
  have hCnonneg : 0 ≤ C := schwartzOrderFourConstant_nonneg u₀
  have hcnorm_pos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hznorm_pos : 0 < ‖(z : NSSpace) - y‖ := by
    have hcinv_pos : 0 < ‖c‖⁻¹ := by positivity
    linarith
  have hznorm : ‖(z : NSSpace) - y‖ ≠ 0 := ne_of_gt hznorm_pos
  have hv :
      x + c • (z : NSSpace) =
        c • ((z : NSSpace) - y) := by
    simpa [y] using add_periodizationScale_eq_smul_sub hc x (z : NSSpace)
  have hnormv :
      ‖x + c • (z : NSSpace)‖ = ‖c‖ * ‖(z : NSSpace) - y‖ := by
    rw [hv, norm_smul]
  have hvnorm_pos : 0 < ‖x + c • (z : NSSpace)‖ := by
    rw [hnormv]
    positivity
  have hvnorm : ‖x + c • (z : NSSpace)‖ ≠ 0 := ne_of_gt hvnorm_pos
  have hdiv :
      ‖u₀ (x + c • (z : NSSpace))‖ ≤
        C / ‖x + c • (z : NSSpace)‖ ^ 4 := by
    have hbase :
        ‖u₀ (x + c • (z : NSSpace))‖ ≤
          C / (1 + ‖x + c • (z : NSSpace)‖) ^ 4 := by
      simpa [C, schwartzOrderFourConstant] using
        schwartz_norm_le_orderFour u₀ (x + c • (z : NSSpace))
    have hpow :
        ‖x + c • (z : NSSpace)‖ ^ 4 ≤
          (1 + ‖x + c • (z : NSSpace)‖) ^ 4 := by
      gcongr
      linarith
    exact hbase.trans <|
      div_le_div_of_nonneg_left hCnonneg (by positivity) hpow
  have hmajor :
      C / ‖x + c • (z : NSSpace)‖ ^ 4 =
        (C * ‖c‖ ^ (-4 : ℤ)) *
          ‖(z : NSSpace) - y‖ ^ (-4 : ℤ) := by
    rw [hnormv]
    rw [zpow_neg, zpow_neg]
    field_simp [hznorm, norm_ne_zero_iff.mpr hc]
  exact hdiv.trans_eq hmajor

/-- The rank-3 order-4 majorant used to control the Schwartz periodization terms
is summable on the coordinate lattice. -/
theorem summable_schwartz_coordinateLatticeMajorant
    {c : ℝ} (u₀ : NSSchwartzInitialVelocity) (x : NSSpace) :
    Summable
      (fun z : NSCoordinateLattice =>
        (schwartzOrderFourConstant u₀ * ‖c‖ ^ (-4 : ℤ)) *
          ‖(z : NSSpace) - (-(c⁻¹) • x)‖ ^ (-4 : ℤ)) := by
  have hdim : Module.finrank ℤ NSCoordinateLattice = 3 := by
    rw [Module.finrank_eq_card_basis nsCoordinateLatticeBasis]
    norm_num
  have hzpow :
      (-4 : ℤ) < -Module.finrank ℤ NSCoordinateLattice := by
    rw [hdim]
    norm_num
  simpa using
    (ZLattice.summable_norm_sub_zpow (L := NSCoordinateLattice) (-4) hzpow (-(c⁻¹) • x)).mul_left
      (schwartzOrderFourConstant u₀ * ‖c‖ ^ (-4 : ℤ))

/-- The translated Schwartz periodization terms are summable on the coordinate
lattice when the scale parameter is nonzero. -/
theorem summable_schwartz_coordinateLatticeSeries
    {c : ℝ} (hc : c ≠ 0) (u₀ : NSSchwartzInitialVelocity) (x : NSSpace) :
    Summable (fun z : NSCoordinateLattice => u₀ (x + c • (z : NSSpace))) := by
  let y : NSSpace := -(c⁻¹) • x
  have hsumLat := summable_schwartz_coordinateLatticeMajorant (c := c) u₀ x
  have hfiniteBad :
      Set.Finite {z : NSCoordinateLattice | ‖(z : NSSpace) - y‖ ≤ ‖c‖⁻¹} :=
    finite_nsCoordinateLatticePoints_mem_closedBall y (‖c‖⁻¹)
  refine Summable.of_norm_bounded_eventually hsumLat ?_
  filter_upwards [hfiniteBad.eventually_cofinite_notMem] with z hz
  have hzfar :
      ‖((z : NSCoordinateLattice) : NSSpace) - y‖ > ‖c‖⁻¹ := by
    have : ¬ ‖((z : NSCoordinateLattice) : NSSpace) - y‖ ≤ ‖c‖⁻¹ := by
      simpa using hz
    linarith
  simpa [y] using norm_schwartz_periodized_term_le_latticeDecay hc u₀ x z hzfar

/-- The formal infinite Schwartz periodization candidate associated to a lattice
period `2πL`. The substantive convergence theorem below shows this `tsum`
agrees with the boxed partial periodization limit on each fixed cube once
`L ≠ 0`. -/
noncomputable def schwartzPeriodizedInitialVelocity
    (L : ℝ) (u₀ : NSSchwartzInitialVelocity) :
    NSInitialVelocity :=
  fun x => ∑' n : NSLatticeIndex, u₀ (x + periodizationShift L n)

set_option maxHeartbeats 800000 in
/-- For nonzero period parameter `L`, the Schwartz lattice series is summable at
each fixed spatial point. -/
theorem summable_schwartzPeriodizedInitialVelocity
    {L : ℝ} (hL : L ≠ 0) (u₀ : NSSchwartzInitialVelocity) (x : NSSpace) :
    Summable (fun n : NSLatticeIndex => u₀ (x + periodizationShift L n)) := by
  let c : ℝ := 2 * Real.pi * L
  have hc : c ≠ 0 := by
    refine mul_ne_zero ?_ hL
    positivity
  have hsumLatValue :
      Summable
        (fun z : NSCoordinateLattice =>
          u₀ (x + c • ((z : NSCoordinateLattice) : NSSpace))) :=
    summable_schwartz_coordinateLatticeSeries hc u₀ x
  have hsumIndex :
      Summable
        (fun n : NSLatticeIndex =>
          u₀ (x + c • ((nsCoordinateLatticePoint n : NSCoordinateLattice) : NSSpace))) := by
    have hsumIndex' :
        Summable
          (fun n : NSLatticeIndex =>
            u₀ (x + c • ((nsCoordinateLatticePointEquiv n : NSCoordinateLattice) : NSSpace))) :=
      nsCoordinateLatticePointEquiv.summable_iff.mpr hsumLatValue
    exact hsumIndex'.congr fun n => by rfl
  have hseriesEq :
      (fun n : NSLatticeIndex => u₀ (x + periodizationShift L n)) =
        (fun n : NSLatticeIndex =>
          u₀ (x + c • ((nsCoordinateLatticePoint n : NSCoordinateLattice) : NSSpace))) := by
    ext n
    simp [c, periodizationShift_eq_smul_nsCoordinateLatticePoint]
  exact hseriesEq.symm ▸ hsumIndex

/-- The `tsum` used in `schwartzPeriodizedInitialVelocity` is the actual sum of
the boxed periodization terms at each point once `L ≠ 0`. -/
theorem hasSum_schwartzPeriodizedInitialVelocity
    {L : ℝ} (hL : L ≠ 0) (u₀ : NSSchwartzInitialVelocity) (x : NSSpace) :
    HasSum (fun n : NSLatticeIndex => u₀ (x + periodizationShift L n))
      (schwartzPeriodizedInitialVelocity L u₀ x) :=
  (summable_schwartzPeriodizedInitialVelocity hL u₀ x).hasSum

/-- The infinite Schwartz periodization is invariant under its period lattice
shifts. This is the concrete periodicity property needed for the large-torus
exhaustion route. -/
theorem schwartzPeriodizedInitialVelocity_add_periodizationShift
    (L : ℝ) (u₀ : NSSchwartzInitialVelocity) (k : NSLatticeIndex) (x : NSSpace) :
    schwartzPeriodizedInitialVelocity L u₀ (x + periodizationShift L k) =
      schwartzPeriodizedInitialVelocity L u₀ x := by
  unfold schwartzPeriodizedInitialVelocity
  calc
    (∑' n : NSLatticeIndex, u₀ (x + periodizationShift L k + periodizationShift L n))
        = ∑' n : NSLatticeIndex, u₀ (x + periodizationShift L (k + n)) := by
          apply tsum_congr
          intro n
          congr 1
          simp [periodizationShift_add, add_assoc]
    _ = ∑' n : NSLatticeIndex, u₀ (x + periodizationShift L n) := by
          simpa using
            (Equiv.tsum_eq (Equiv.addLeft k)
              (fun n : NSLatticeIndex => u₀ (x + periodizationShift L n)))

/-- The structured boxed Schwartz partial periodizations converge pointwise to
the infinite Schwartz periodization whenever the period parameter is nonzero. -/
theorem boxedPartialPeriodizationSchwartzInitialVelocity_tendsto
    {L : ℝ} (hL : L ≠ 0) (u₀ : NSSchwartzInitialVelocity) (x : NSSpace) :
    Tendsto (fun N => boxedPartialPeriodizationSchwartzInitialVelocity N L u₀ x)
      Filter.atTop (nhds (schwartzPeriodizedInitialVelocity L u₀ x)) := by
  let f : NSLatticeIndex → NSSpace := fun n => u₀ (x + periodizationShift L n)
  have hsum : HasSum f (schwartzPeriodizedInitialVelocity L u₀ x) := by
    simpa [f, schwartzPeriodizedInitialVelocity] using
      hasSum_schwartzPeriodizedInitialVelocity hL u₀ x
  simpa [f, boxedPartialPeriodizationSchwartzInitialVelocity,
    finitePartialPeriodizationSchwartzInitialVelocity] using
    hsum.comp centeredLatticeBox_tendsto_atTop

/-- The boxed partial periodizations of manuscript-style divergence-free
Schwartz data converge pointwise to the same infinite periodization candidate. -/
theorem boxedPartialPeriodizationSchwartzDivergenceFreeInitialVelocity_tendsto
    {L : ℝ} (hL : L ≠ 0) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    (x : NSSpace) :
    Tendsto
      (fun N => (boxedPartialPeriodizationSchwartzDivergenceFreeInitialVelocity N L u₀).1 x)
      Filter.atTop (nhds (schwartzPeriodizedInitialVelocity L u₀.1 x)) := by
  simpa [boxedPartialPeriodizationSchwartzDivergenceFreeInitialVelocity,
    boxedPartialPeriodizationSchwartzInitialVelocity,
    finitePartialPeriodizationSchwartzDivergenceFreeInitialVelocity] using
    boxedPartialPeriodizationSchwartzInitialVelocity_tendsto hL u₀.1 x

/-- Each boxed divergence-free Schwartz partial periodization gives repaired
finite-energy Navier-Stokes problem data for any positive viscosity. -/
def boxedPartialPeriodizationFiniteEnergyAdmissibleProblemData
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    {ν : ℝ} (hν : 0 < ν) :
    FiniteEnergyAdmissibleNavierStokesProblemData :=
  let uN := boxedPartialPeriodizationSchwartzDivergenceFreeInitialVelocity N L u₀
  uN.toFiniteEnergyAdmissibleNavierStokesProblemData hν

/-- The same boxed approximants viewed on the fully concrete structured
Navier-Stokes problem surface. -/
def boxedPartialPeriodizationNavierStokesProblemData
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    {ν : ℝ} (hν : 0 < ν) :
    NavierStokesProblemData mkFullyConcreteNavierStokesSurface :=
  (boxedPartialPeriodizationFiniteEnergyAdmissibleProblemData N L u₀ hν).toNavierStokesProblemData

/-- The steady seed generated by a boxed partial-periodization datum.  This is
only a local-existence prerequisite: it packages the concrete smooth,
divergence-free, initial-matching seed before the nonlinear momentum equation
has been solved. -/
def boxedPartialPeriodizationSteadySeedVelocity
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    {ν : ℝ} (hν : 0 < ν) : NSVelocityField :=
  timeIndependentVelocity
    (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity

/-- Basic checked prerequisites for the steady seed attached to boxed
partial-periodization data.  The missing analytic step toward
`boxedPartialPeriodization_local_BKM_witness_exists` is still the construction
of an evolved velocity and pressure satisfying the momentum equation, not these
seed regularity and compatibility facts. -/
theorem boxedPartialPeriodizationSteadySeed_basic
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity) :
    smoothSpaceTimeVelocity (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) ∧
      MatchesInitialVelocity
        (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity
        (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) ∧
      (∀ t x,
        spatialDivergence (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x = 0) ∧
      (∀ t x,
        timeVelocityDerivative (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x = 0) ∧
      (∀ t,
        kineticEnergyDensity (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t =
          initialKineticEnergyDensity
            (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity) := by
  let P := boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [boxedPartialPeriodizationSteadySeedVelocity, P] using
      smoothSpaceTimeVelocity_timeIndependentVelocity (u₀ := P.initialVelocity) P.smooth_initial
  · simpa [boxedPartialPeriodizationSteadySeedVelocity, P] using
      MatchesInitialVelocity_timeIndependentVelocity P.initialVelocity
  · intro t x
    calc
      spatialDivergence (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x =
          initialSpatialDivergence P.initialVelocity x := by
            simpa [boxedPartialPeriodizationSteadySeedVelocity, P] using
              spatialDivergence_timeIndependentVelocity P.initialVelocity t x
      _ = 0 := P.divergence_free_initial x
  · intro t x
    simpa [boxedPartialPeriodizationSteadySeedVelocity, P] using
      timeVelocityDerivative_timeIndependentVelocity P.initialVelocity t x
  · intro t
    simpa [boxedPartialPeriodizationSteadySeedVelocity, P] using
      kineticEnergyDensity_timeIndependentVelocity P.initialVelocity t

/-- Any attempt to use the steady boxed seed as a positive-time
Navier-Stokes witness must already solve the stationary momentum balance at
time zero.  This exposes the obstruction: the seed supplies compatibility data,
but it does not produce the evolved `u,p` required by local existence. -/
theorem boxedPartialPeriodizationSteadySeed_momentum_zero_time_obstruction
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    {T : ℝ} (hT : 0 ≤ T) (p : NSPressureField)
    (hmom :
      ∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x +
            spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x +
            spatialPressureGradient p t x =
          ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) t x) :
    ∀ x,
      spatialConvection (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) 0 x +
          spatialPressureGradient p 0 x =
        ν • spatialLaplacian (boxedPartialPeriodizationSteadySeedVelocity N L u₀ hν) 0 x := by
  intro x
  have h := hmom 0 x le_rfl hT
  simpa [boxedPartialPeriodizationSteadySeedVelocity,
    timeVelocityDerivative_timeIndependentVelocity] using h

/-- The initial velocities of the admissible boxed problem data converge
pointwise to the infinite Schwartz periodization when the period parameter is
nonzero. -/
theorem boxedPartialPeriodizationFiniteEnergyAdmissibleProblemData_initialVelocity_tendsto
    {ν L : ℝ} (hν : 0 < ν) (hL : L ≠ 0)
    (u₀ : NSSchwartzDivergenceFreeInitialVelocity) (x : NSSpace) :
    Tendsto
      (fun N =>
        (boxedPartialPeriodizationFiniteEnergyAdmissibleProblemData N L u₀ hν).initialVelocity x)
      Filter.atTop (nhds (schwartzPeriodizedInitialVelocity L u₀.1 x)) := by
  simpa [boxedPartialPeriodizationFiniteEnergyAdmissibleProblemData,
    NSSchwartzDivergenceFreeInitialVelocity.toFiniteEnergyAdmissibleNavierStokesProblemData]
    using boxedPartialPeriodizationSchwartzDivergenceFreeInitialVelocity_tendsto hL u₀ x

/-- The same initial-velocity convergence holds after forgetting finite-energy
metadata and viewing the boxed approximants as structured Navier-Stokes problem
data. -/
theorem boxedPartialPeriodizationNavierStokesProblemData_initialVelocity_tendsto
    {ν L : ℝ} (hν : 0 < ν) (hL : L ≠ 0)
    (u₀ : NSSchwartzDivergenceFreeInitialVelocity) (x : NSSpace) :
    Tendsto
      (fun N => (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν).initialVelocity x)
      Filter.atTop (nhds (schwartzPeriodizedInitialVelocity L u₀.1 x)) := by
  simpa [boxedPartialPeriodizationNavierStokesProblemData,
    FiniteEnergyAdmissibleNavierStokesProblemData.toNavierStokesProblemData] using
    boxedPartialPeriodizationFiniteEnergyAdmissibleProblemData_initialVelocity_tendsto
      hν hL u₀ x

/-- Any proof of the repaired finite-energy millennium target applies directly
to every boxed divergence-free Schwartz periodization approximant. -/
theorem FiniteEnergyConcreteNavierStokesMillenniumTarget_apply_boxedPartialPeriodization
    (h : FiniteEnergyConcreteNavierStokesMillenniumTarget)
    {ν : ℝ} (hν : 0 < ν)
    (N : ℕ) (L : ℝ) (u₀ : NSSchwartzDivergenceFreeInitialVelocity) :
    NavierStokesGlobalRegularityClause mkFullyConcreteNavierStokesSurface
      (boxedPartialPeriodizationNavierStokesProblemData N L u₀ hν) := by
  simpa [boxedPartialPeriodizationNavierStokesProblemData] using
    h (boxedPartialPeriodizationFiniteEnergyAdmissibleProblemData N L u₀ hν)

/-- The centered spatial cube `Q_R = [-R, R]^3 ⊂ ℝ^3`. -/
def spatialCube (R : ℝ) : Set NSSpace :=
  { x | ∀ i : Fin 3, |x i| ≤ R }

/-- Membership in `Q_R` is the expected coordinatewise bound. -/
theorem mem_spatialCube_iff {R : ℝ} {x : NSSpace} :
    x ∈ spatialCube R ↔ ∀ i : Fin 3, |x i| ≤ R :=
  Iff.rfl

/-- Larger radii contain smaller centered cubes. -/
theorem spatialCube_mono {R S : ℝ} (hRS : R ≤ S) :
    spatialCube R ⊆ spatialCube S := by
  intro x hx
  rw [mem_spatialCube_iff] at hx ⊢
  intro i
  exact (hx i).trans hRS

/-- Local convergence of the boxed partial periodizations on a set `s`. -/
def BoxedPartialPeriodizationConvergesOn
    (s : Set NSSpace) (L : ℝ) (u₀ u : NSInitialVelocity) : Prop :=
  ∀ x ∈ s, Tendsto (fun N => boxedPartialPeriodizedInitialVelocity N L u₀ x)
    Filter.atTop (nhds (u x))

/-- Local convergence of the boxed partial periodizations on the centered cube
`Q_R`. -/
def BoxedPartialPeriodizationConvergesOnCube
    (R L : ℝ) (u₀ u : NSInitialVelocity) : Prop :=
  BoxedPartialPeriodizationConvergesOn (spatialCube R) L u₀ u

/-- The boxed partial periodizations of Schwartz data converge pointwise on any
fixed set to the `tsum`-defined whole-space periodization candidate whenever
`L ≠ 0`. -/
theorem BoxedPartialPeriodizationConvergesOn_of_schwartz
    {s : Set NSSpace} {L : ℝ} (hL : L ≠ 0) (u₀ : NSSchwartzInitialVelocity) :
    BoxedPartialPeriodizationConvergesOn s L (u₀ : NSInitialVelocity)
      (schwartzPeriodizedInitialVelocity L u₀) := by
  intro x hx
  let f : NSLatticeIndex → NSSpace := fun n => u₀ (x + periodizationShift L n)
  have hsum : HasSum f (schwartzPeriodizedInitialVelocity L u₀ x) := by
    simpa [f, schwartzPeriodizedInitialVelocity] using
      hasSum_schwartzPeriodizedInitialVelocity hL u₀ x
  simpa [f, boxedPartialPeriodizedInitialVelocity, finitePartialPeriodizedInitialVelocity] using
    hsum.comp centeredLatticeBox_tendsto_atTop

/-- Fixed-cube specialization of the Schwartz boxed-periodization convergence
theorem. -/
theorem BoxedPartialPeriodizationConvergesOnCube_of_schwartz
    {R L : ℝ} (hL : L ≠ 0) (u₀ : NSSchwartzInitialVelocity) :
    BoxedPartialPeriodizationConvergesOnCube R L (u₀ : NSInitialVelocity)
      (schwartzPeriodizedInitialVelocity L u₀) :=
  BoxedPartialPeriodizationConvergesOn_of_schwartz (s := spatialCube R) hL u₀

/-- Fixed-cube specialization of the Schwartz boxed-periodization convergence
theorem on the manuscript's `Sσ(ℝ^3)` input class. -/
theorem BoxedPartialPeriodizationConvergesOn_of_schwartzDivergenceFree
    {s : Set NSSpace} {L : ℝ} (hL : L ≠ 0)
    (u₀ : NSSchwartzDivergenceFreeInitialVelocity) :
    BoxedPartialPeriodizationConvergesOn s L (u₀.1 : NSInitialVelocity)
      (schwartzPeriodizedInitialVelocity L u₀.1) :=
  BoxedPartialPeriodizationConvergesOn_of_schwartz (s := s) hL u₀.1

/-- Fixed-cube specialization of the Schwartz boxed-periodization convergence
theorem on the manuscript's `Sσ(ℝ^3)` input class. -/
theorem BoxedPartialPeriodizationConvergesOnCube_of_schwartzDivergenceFree
    {R L : ℝ} (hL : L ≠ 0) (u₀ : NSSchwartzDivergenceFreeInitialVelocity) :
    BoxedPartialPeriodizationConvergesOnCube R L (u₀.1 : NSInitialVelocity)
      (schwartzPeriodizedInitialVelocity L u₀.1) :=
  BoxedPartialPeriodizationConvergesOn_of_schwartzDivergenceFree
    (s := spatialCube R) hL u₀

/-- The shell contribution added when enlarging the boxed partial periodization
from radius `N` to radius `N + 1`. -/
def boxedPeriodizationShellInitialVelocity
    (N : ℕ) (L : ℝ) (u₀ : NSInitialVelocity) :
    NSInitialVelocity :=
  finitePartialPeriodizedInitialVelocity (centeredLatticeShell N) L u₀

/-- The shell contribution is exactly the one-step difference of boxed partial
periodizations. -/
theorem boxedPeriodizationShellInitialVelocity_eq_sub
    (N : ℕ) (L : ℝ) (u₀ : NSInitialVelocity) :
    boxedPeriodizationShellInitialVelocity N L u₀ =
      boxedPartialPeriodizedInitialVelocity (N + 1) L u₀ -
        boxedPartialPeriodizedInitialVelocity N L u₀ := by
  funext x
  apply eq_sub_iff_add_eq.mpr
  simpa [boxedPeriodizationShellInitialVelocity, add_comm, add_left_comm, add_assoc] using
    (congrFun (boxedPartialPeriodizedInitialVelocity_succ N L u₀) x).symm

theorem BoxedPartialPeriodizationConvergesOn.mono
    {s t : Set NSSpace} {L : ℝ} {u₀ u : NSInitialVelocity}
    (hconv : BoxedPartialPeriodizationConvergesOn t L u₀ u)
    (hst : s ⊆ t) :
    BoxedPartialPeriodizationConvergesOn s L u₀ u := by
  intro x hx
  exact hconv x (hst hx)

theorem BoxedPartialPeriodizationConvergesOnCube.mono
    {R S L : ℝ} {u₀ u : NSInitialVelocity}
    (hconv : BoxedPartialPeriodizationConvergesOnCube S L u₀ u)
    (hRS : R ≤ S) :
    BoxedPartialPeriodizationConvergesOnCube R L u₀ u := by
  exact BoxedPartialPeriodizationConvergesOn.mono hconv (spatialCube_mono hRS)

/-- If the boxed partial periodizations converge locally, the added shell
contributions vanish locally. -/
theorem boxedPeriodizationShellInitialVelocity_tendsto_zero_on_of_convergesOn
    {s : Set NSSpace} {L : ℝ} {u₀ u : NSInitialVelocity}
    (hconv : BoxedPartialPeriodizationConvergesOn s L u₀ u) :
    ∀ x ∈ s, Tendsto (fun N => boxedPeriodizationShellInitialVelocity N L u₀ x)
      Filter.atTop (nhds 0) := by
  intro x hx
  have hconv_x := hconv x hx
  have hsucc_x :
      Tendsto (fun N => boxedPartialPeriodizedInitialVelocity (N + 1) L u₀ x)
        Filter.atTop (nhds (u x)) := by
    exact hconv_x.comp (tendsto_add_atTop_nat 1)
  have hdiff :
      Tendsto
        (fun N =>
          boxedPartialPeriodizedInitialVelocity (N + 1) L u₀ x -
            boxedPartialPeriodizedInitialVelocity N L u₀ x)
        Filter.atTop (nhds (u x - u x)) :=
    hsucc_x.sub hconv_x
  simpa [boxedPeriodizationShellInitialVelocity_eq_sub] using hdiff

/-- Cube-local convergence implies vanishing shell increments on the same cube. -/
theorem boxedPeriodizationShellInitialVelocity_tendsto_zero_onCube_of_convergesOnCube
    {R L : ℝ} {u₀ u : NSInitialVelocity}
    (hconv : BoxedPartialPeriodizationConvergesOnCube R L u₀ u) :
    ∀ x ∈ spatialCube R,
      Tendsto (fun N => boxedPeriodizationShellInitialVelocity N L u₀ x)
        Filter.atTop (nhds 0) :=
  boxedPeriodizationShellInitialVelocity_tendsto_zero_on_of_convergesOn hconv

/-- For Schwartz initial data and nonzero period parameter, the shell
increments of the boxed partial periodizations vanish pointwise on any fixed
set. -/
theorem boxedPeriodizationShellInitialVelocity_tendsto_zero_on_of_schwartz
    {s : Set NSSpace} {L : ℝ} (hL : L ≠ 0) (u₀ : NSSchwartzInitialVelocity) :
    ∀ x ∈ s,
      Tendsto (fun N => boxedPeriodizationShellInitialVelocity N L (u₀ : NSInitialVelocity) x)
        Filter.atTop (nhds 0) := by
  exact
    boxedPeriodizationShellInitialVelocity_tendsto_zero_on_of_convergesOn
      (BoxedPartialPeriodizationConvergesOn_of_schwartz (s := s) hL u₀)

/-- Fixed-cube specialization of the direct shell-vanishing corollary for
Schwartz initial data. -/
theorem boxedPeriodizationShellInitialVelocity_tendsto_zero_onCube_of_schwartz
    {R L : ℝ} (hL : L ≠ 0) (u₀ : NSSchwartzInitialVelocity) :
    ∀ x ∈ spatialCube R,
      Tendsto (fun N => boxedPeriodizationShellInitialVelocity N L (u₀ : NSInitialVelocity) x)
        Filter.atTop (nhds 0) := by
  exact
    boxedPeriodizationShellInitialVelocity_tendsto_zero_onCube_of_convergesOnCube
      (BoxedPartialPeriodizationConvergesOnCube_of_schwartz (R := R) hL u₀)

/-- Fixed-cube shell increments also vanish for manuscript-style
`Sσ(ℝ^3)` initial data once the period parameter is nonzero. -/
theorem boxedPeriodizationShellInitialVelocity_tendsto_zero_on_of_schwartzDivergenceFree
    {s : Set NSSpace} {L : ℝ} (hL : L ≠ 0)
    (u₀ : NSSchwartzDivergenceFreeInitialVelocity) :
    ∀ x ∈ s,
      Tendsto (fun N => boxedPeriodizationShellInitialVelocity N L (u₀.1 : NSInitialVelocity) x)
        Filter.atTop (nhds 0) := by
  exact
    boxedPeriodizationShellInitialVelocity_tendsto_zero_on_of_convergesOn
      (BoxedPartialPeriodizationConvergesOn_of_schwartzDivergenceFree (s := s) hL u₀)

/-- Fixed-cube shell increments also vanish for manuscript-style
`Sσ(ℝ^3)` initial data once the period parameter is nonzero. -/
theorem boxedPeriodizationShellInitialVelocity_tendsto_zero_onCube_of_schwartzDivergenceFree
    {R L : ℝ} (hL : L ≠ 0) (u₀ : NSSchwartzDivergenceFreeInitialVelocity) :
    ∀ x ∈ spatialCube R,
      Tendsto (fun N => boxedPeriodizationShellInitialVelocity N L (u₀.1 : NSInitialVelocity) x)
        Filter.atTop (nhds 0) := by
  exact
    boxedPeriodizationShellInitialVelocity_tendsto_zero_on_of_schwartzDivergenceFree
      (s := spatialCube R) hL u₀

end NavierStokes
end FluidDynamics
end Mettapedia
