import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.Finset.Max
import Mathlib.Probability.ProbabilityMassFunction.Basic

namespace Mettapedia.Computability.PNP

namespace PMF

open scoped ENNReal

variable {α : Type*} [Fintype α]

/-- The finite sum of a `PMF` over its whole support type is one. -/
theorem sum_univ_eq_one (μ : PMF α) :
    (Finset.univ : Finset α).sum (fun a => μ a) = 1 := by
  simpa [tsum_fintype] using μ.tsum_coe

section LightestPoint

variable [Nonempty α]

/-- Every finite PMF has a point whose mass is minimal among all points. -/
theorem exists_apply_le_all (μ : PMF α) :
    ∃ x : α, ∀ y : α, μ x ≤ μ y := by
  classical
  obtain ⟨x, _hx, hmin⟩ :=
    Finset.exists_min_image
      (s := (Finset.univ : Finset α))
      (f := fun a => μ a)
      Finset.univ_nonempty
  exact ⟨x, fun y => hmin y (by simp)⟩

/-- A chosen point of minimal PMF mass on a finite nonempty type. -/
noncomputable def lightestPoint (μ : PMF α) : α :=
  Classical.choose (exists_apply_le_all μ)

/-- The chosen `lightestPoint` has mass at most every other point mass. -/
theorem apply_lightestPoint_le_apply (μ : PMF α) (x : α) :
    μ (lightestPoint μ) ≤ μ x :=
  Classical.choose_spec (exists_apply_le_all μ) x

end LightestPoint

variable [DecidableEq α]

/-- On a finite type, the complement of one point has mass `1 - μ x`. -/
theorem sum_univ_erase_eq_one_sub_apply (μ : PMF α) (x : α) :
    (Finset.univ.erase x).sum (fun a => μ a) = 1 - μ x := by
  have hsum :
      (1 : ℝ≥0∞) =
        (Finset.univ.erase x).sum (fun a => μ a) + μ x := by
    simpa [sum_univ_eq_one μ, add_comm] using
      (Finset.sum_erase_add
        (s := (Finset.univ : Finset α))
        (a := x)
        (f := fun a : α => μ a)
        (Finset.mem_univ x)).symm
  symm
  exact ENNReal.sub_eq_of_eq_add (μ.apply_ne_top x) hsum

/-- Any finite region omitting `x` has mass at most the complement mass
`1 - μ x`. -/
theorem sum_le_one_sub_apply_of_not_mem
    (μ : PMF α)
    {region : Finset α}
    {x : α}
    (hx : x ∉ region) :
    region.sum (fun a => μ a) ≤ 1 - μ x := by
  have hsub : region ⊆ Finset.univ.erase x := by
    intro a ha
    refine Finset.mem_erase.mpr ?_
    constructor
    · intro hax
      subst hax
      exact hx ha
    · simp
  have hle :
      region.sum (fun a => μ a) ≤
        (Finset.univ.erase x).sum (fun a => μ a) := by
    exact
      Finset.sum_le_sum_of_subset_of_nonneg
        hsub
        (by
          intro a _ha _hnot
          exact bot_le)
  simpa [sum_univ_erase_eq_one_sub_apply] using hle

section LightestPointUpperBound

variable [Nonempty α]

/-- Every proper finite region has mass at most the complement mass of the
lightest point. -/
theorem sum_le_one_sub_apply_lightestPoint_of_exists_not_mem
    (μ : PMF α)
    {region : Finset α}
    (hout : ∃ x : α, x ∉ region) :
    region.sum (fun a => μ a) ≤ 1 - μ (lightestPoint μ) := by
  rcases hout with ⟨x, hx⟩
  exact le_trans
    (sum_le_one_sub_apply_of_not_mem μ hx)
    (tsub_le_tsub_left (apply_lightestPoint_le_apply μ x) 1)

/-- The complement of the lightest point attains the sharp upper bound on
proper-region mass. -/
theorem allProperRegionMass_le_iff_one_sub_apply_lightestPoint_le
    (μ : PMF α)
    (q : ℝ≥0∞) :
    (∀ region : Finset α,
        (∃ x : α, x ∉ region) →
          region.sum (fun a => μ a) ≤ q) ↔
      1 - μ (lightestPoint μ) ≤ q := by
  constructor
  · intro hregion
    have hlight :
        (Finset.univ.erase (lightestPoint μ)).sum (fun a => μ a) ≤ q :=
      hregion
        (Finset.univ.erase (lightestPoint μ))
        ⟨lightestPoint μ, by simp⟩
    simpa [sum_univ_erase_eq_one_sub_apply] using hlight
  · intro hq region hout
    exact le_trans
      (sum_le_one_sub_apply_lightestPoint_of_exists_not_mem μ hout)
      hq

end LightestPointUpperBound

/-- A finite PMF admits some proper region of mass `> q` exactly when some
single point already has complement mass `> q`. -/
theorem exists_heavyProperRegion_iff_exists_lt_one_sub_apply
    (μ : PMF α)
    (q : ℝ≥0∞) :
    (∃ region : Finset α, (∃ x : α, x ∉ region) ∧ q < region.sum (fun a => μ a)) ↔
      ∃ x : α, q < 1 - μ x := by
  constructor
  · rintro ⟨region, ⟨x, hx⟩, hq⟩
    exact ⟨x, lt_of_lt_of_le hq (sum_le_one_sub_apply_of_not_mem μ hx)⟩
  · rintro ⟨x, hx⟩
    exact
      ⟨Finset.univ.erase x, ⟨x, by simp⟩, by
        simpa [sum_univ_erase_eq_one_sub_apply] using hx⟩

section LightestPointThreshold

variable [Nonempty α]

/-- Therefore a finite PMF admits a proper region of mass `> q` exactly when
the complement of its lightest point already has mass `> q`. -/
theorem exists_heavyProperRegion_iff_lt_one_sub_apply_lightestPoint
    (μ : PMF α)
    (q : ℝ≥0∞) :
    (∃ region : Finset α, (∃ x : α, x ∉ region) ∧ q < region.sum (fun a => μ a)) ↔
      q < 1 - μ (lightestPoint μ) := by
  constructor
  · intro hregion
    rcases (exists_heavyProperRegion_iff_exists_lt_one_sub_apply (μ := μ) (q := q)).1 hregion with
      ⟨x, hx⟩
    exact
      lt_of_lt_of_le
        hx
        (tsub_le_tsub_left (apply_lightestPoint_le_apply μ x) 1)
  · intro hlight
    exact
      (exists_heavyProperRegion_iff_exists_lt_one_sub_apply (μ := μ) (q := q)).2
        ⟨lightestPoint μ, hlight⟩

end LightestPointThreshold

end PMF

end Mettapedia.Computability.PNP
