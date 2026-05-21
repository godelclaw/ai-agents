import Mettapedia.FluidDynamics.NavierStokes.ColeHopfInterface

/-!
# Cole-Hopf Positive Lower Bounds

The SG-Cole-Hopf manuscript uses the logarithmic transform
`W = -2 nu log Phi`.  The finite identity-energy algebra already present in
`IdentityEnergy.lean` proves the energy estimate once a strict pointwise lower
bound `0 < m <= Phi x` is available.  This file records the complementary
obligation: a heat field with a zero or nonpositive value cannot instantiate
the log side of the Cole-Hopf identity interface.
-/

set_option autoImplicit false

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section PositiveLowerBound

variable {A Time ι X : Type*}

/-- A pointwise positive lower bound for the scalar Cole-Hopf heat field. -/
def HasColeHopfPointwiseLowerBound (phi : A -> ℝ) (m : ℝ) : Prop :=
  0 < m ∧ ∀ x, m ≤ phi x

theorem HasColeHopfPointwiseLowerBound.m_pos
    {phi : A -> ℝ} {m : ℝ}
    (h : HasColeHopfPointwiseLowerBound phi m) :
    0 < m :=
  h.1

theorem HasColeHopfPointwiseLowerBound.lower
    {phi : A -> ℝ} {m : ℝ}
    (h : HasColeHopfPointwiseLowerBound phi m) (x : A) :
    m ≤ phi x :=
  h.2 x

/-- A strict positive lower bound makes every value of the heat field positive. -/
theorem HasColeHopfPointwiseLowerBound.pos
    {phi : A -> ℝ} {m : ℝ}
    (h : HasColeHopfPointwiseLowerBound phi m) (x : A) :
    0 < phi x :=
  lt_of_lt_of_le h.m_pos (h.lower x)

theorem HasColeHopfPointwiseLowerBound.ne_zero
    {phi : A -> ℝ} {m : ℝ}
    (h : HasColeHopfPointwiseLowerBound phi m) (x : A) :
    phi x ≠ 0 :=
  ne_of_gt (h.pos x)

theorem HasColeHopfPointwiseLowerBound.not_nonpos
    {phi : A -> ℝ} {m : ℝ}
    (h : HasColeHopfPointwiseLowerBound phi m) (x : A) :
    ¬ phi x ≤ 0 :=
  fun hx => not_lt_of_ge hx (h.pos x)

/-- A nonpositive value rules out a proposed strict lower-bound witness. -/
theorem not_hasColeHopfPointwiseLowerBound_of_nonpos_value
    {phi : A -> ℝ} {m : ℝ} {x : A}
    (hx : phi x ≤ 0) :
    ¬ HasColeHopfPointwiseLowerBound phi m := by
  intro h
  exact h.not_nonpos x hx

/-- A zero value rules out a proposed strict lower-bound witness. -/
theorem not_hasColeHopfPointwiseLowerBound_of_zero_value
    {phi : A -> ℝ} {m : ℝ} {x : A}
    (hx : phi x = 0) :
    ¬ HasColeHopfPointwiseLowerBound phi m := by
  exact not_hasColeHopfPointwiseLowerBound_of_nonpos_value
    (phi := phi) (m := m) (x := x) (by simp [hx])

/-- A nonpositive value rules out every strict lower-bound witness. -/
theorem not_exists_hasColeHopfPointwiseLowerBound_of_nonpos_value
    {phi : A -> ℝ} {x : A}
    (hx : phi x ≤ 0) :
    ¬ ∃ m : ℝ, HasColeHopfPointwiseLowerBound phi m := by
  rintro ⟨m, hm⟩
  exact not_hasColeHopfPointwiseLowerBound_of_nonpos_value
    (phi := phi) (m := m) (x := x) hx hm

/-- A zero value rules out every strict lower-bound witness. -/
theorem not_exists_hasColeHopfPointwiseLowerBound_of_zero_value
    {phi : A -> ℝ} {x : A}
    (hx : phi x = 0) :
    ¬ ∃ m : ℝ, HasColeHopfPointwiseLowerBound phi m := by
  exact not_exists_hasColeHopfPointwiseLowerBound_of_nonpos_value
    (phi := phi) (x := x) (by simp [hx])

/-- The heat field has values below every proposed positive denominator bound.

This captures the repair attempt where `Phi` is pointwise positive but has no
uniform positive lower bound.  The log transform can be pointwise meaningful in
that case, but the current identity-energy interface still cannot be
instantiated. -/
def HasArbitrarilySmallColeHopfValues (phi : A -> ℝ) : Prop :=
  ∀ m : ℝ, 0 < m -> ∃ x : A, phi x < m

theorem not_hasColeHopfPointwiseLowerBound_of_arbitrarilySmallValues
    {phi : A -> ℝ} {m : ℝ}
    (hsmall : HasArbitrarilySmallColeHopfValues phi) :
    ¬ HasColeHopfPointwiseLowerBound phi m := by
  intro h
  rcases hsmall m h.m_pos with ⟨x, hx⟩
  exact not_le_of_gt hx (h.lower x)

/-- Arbitrarily small values rule out every strict lower-bound witness. -/
theorem not_exists_hasColeHopfPointwiseLowerBound_of_arbitrarilySmallValues
    {phi : A -> ℝ}
    (hsmall : HasArbitrarilySmallColeHopfValues phi) :
    ¬ ∃ m : ℝ, HasColeHopfPointwiseLowerBound phi m := by
  rintro ⟨m, hm⟩
  exact not_hasColeHopfPointwiseLowerBound_of_arbitrarilySmallValues
    (phi := phi) (m := m) hsmall hm

/-- A uniform positive lower bound on the absolute value of a scalar
directional derivative. -/
def HasUniformAbsDerivativeLowerBound (dphi : A -> ℝ) (a : ℝ) : Prop :=
  0 < a ∧ ∀ x : A, a ≤ |dphi x|

theorem HasUniformAbsDerivativeLowerBound.a_pos
    {dphi : A -> ℝ} {a : ℝ}
    (h : HasUniformAbsDerivativeLowerBound dphi a) :
    0 < a :=
  h.1

theorem HasUniformAbsDerivativeLowerBound.lower
    {dphi : A -> ℝ} {a : ℝ}
    (h : HasUniformAbsDerivativeLowerBound dphi a) (x : A) :
    a ≤ |dphi x| :=
  h.2 x

/-- A scalar field has values with arbitrarily small absolute value. -/
def HasArbitrarilySmallAbsValues (f : A -> ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε -> ∃ x : A, |f x| < ε

theorem not_hasUniformAbsDerivativeLowerBound_of_arbitrarilySmallAbsValues
    {f : A -> ℝ} {a : ℝ}
    (hsmall : HasArbitrarilySmallAbsValues f) :
    ¬ HasUniformAbsDerivativeLowerBound f a := by
  intro h
  rcases hsmall a h.a_pos with ⟨x, hx⟩
  exact not_le_of_gt hx (h.lower x)

/-- Arbitrarily small absolute derivative values rule out every uniform
positive lower bound on that derivative. -/
theorem not_exists_hasUniformAbsDerivativeLowerBound_of_arbitrarilySmallAbsValues
    {f : A -> ℝ}
    (hsmall : HasArbitrarilySmallAbsValues f) :
    ¬ ∃ a : ℝ, HasUniformAbsDerivativeLowerBound f a := by
  rintro ⟨a, ha⟩
  exact not_hasUniformAbsDerivativeLowerBound_of_arbitrarilySmallAbsValues
    (f := f) (a := a) hsmall ha

/-- If `Phi` is pointwise positive but has arbitrarily small values, and one
directional derivative does not decay with `Phi`, then the pointwise log
derivative `dPhi / Phi` is arbitrarily large in absolute value. -/
theorem exists_abs_logDerivative_gt_of_arbitrarilySmallValues
    {phi dphi : A -> ℝ} {a M : ℝ}
    (hpos : ∀ x : A, 0 < phi x)
    (hsmall : HasArbitrarilySmallColeHopfValues phi)
    (hderiv : HasUniformAbsDerivativeLowerBound dphi a)
    (hM : 0 < M) :
    ∃ x : A, M < |dphi x / phi x| := by
  have hm : 0 < a / M := div_pos hderiv.a_pos hM
  rcases hsmall (a / M) hm with ⟨x, hxsmall⟩
  have hphipos : 0 < phi x := hpos x
  refine ⟨x, ?_⟩
  have hmul : M * phi x < a := by
    have hmul' : M * phi x < M * (a / M) :=
      mul_lt_mul_of_pos_left hxsmall hM
    have hcancel : M * (a / M) = a := by
      field_simp [ne_of_gt hM]
    simpa [hcancel] using hmul'
  have hmul_deriv : M * phi x < |dphi x| :=
    lt_of_lt_of_le hmul (hderiv.lower x)
  have hdiv : M < |dphi x| / phi x := by
    exact (lt_div_iff₀ hphipos).2 hmul_deriv
  simpa [abs_div, abs_of_pos hphipos] using hdiv

/-- Consequently there is no uniform absolute bound on `dPhi / Phi`. -/
theorem not_exists_uniform_abs_logDerivative_bound_of_arbitrarilySmallValues
    {phi dphi : A -> ℝ} {a : ℝ}
    (hpos : ∀ x : A, 0 < phi x)
    (hsmall : HasArbitrarilySmallColeHopfValues phi)
    (hderiv : HasUniformAbsDerivativeLowerBound dphi a) :
    ¬ ∃ B : ℝ, ∀ x : A, |dphi x / phi x| ≤ B := by
  rintro ⟨B, hB⟩
  let M : ℝ := max (B + 1) 1
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right (B + 1) 1)
  have hBM : B < M := by
    have hlt : B < B + 1 := by linarith
    exact lt_of_lt_of_le hlt (le_max_left (B + 1) 1)
  rcases exists_abs_logDerivative_gt_of_arbitrarilySmallValues
      (phi := phi) (dphi := dphi) hpos hsmall hderiv hMpos with ⟨x, hx⟩
  exact not_lt_of_ge (hB x) (lt_trans hBM hx)

/-- Conversely, if `dPhi / Phi` is uniformly bounded while `Phi` stays
pointwise positive and approaches zero, then `dPhi` itself has arbitrarily
small absolute values.  This is the exact proportional-vanishing obligation
left to any repair that avoids a uniform lower bound on `Phi`. -/
theorem abs_derivative_arbitrarilySmall_of_uniform_abs_logDerivative_bound
    {phi dphi : A -> ℝ} {B : ℝ}
    (hpos : ∀ x : A, 0 < phi x)
    (hsmall : HasArbitrarilySmallColeHopfValues phi)
    (hlog : ∀ x : A, |dphi x / phi x| ≤ B) :
    HasArbitrarilySmallAbsValues dphi := by
  intro ε hε
  have hBnonneg : 0 ≤ B := by
    rcases hsmall 1 zero_lt_one with ⟨x0, _⟩
    exact le_trans (abs_nonneg (dphi x0 / phi x0)) (hlog x0)
  have hB1pos : 0 < B + 1 := by linarith
  have hthreshold : 0 < ε / (B + 1) := div_pos hε hB1pos
  rcases hsmall (ε / (B + 1)) hthreshold with ⟨x, hxsmall⟩
  have hphipos : 0 < phi x := hpos x
  refine ⟨x, ?_⟩
  have hprod_le : |dphi x / phi x| * phi x ≤ B * phi x :=
    mul_le_mul_of_nonneg_right (hlog x) (le_of_lt hphipos)
  have hBphi_lt : B * phi x < (B + 1) * phi x := by
    have hBlt : B < B + 1 := by linarith
    exact mul_lt_mul_of_pos_right hBlt hphipos
  have hB1phi_lt : (B + 1) * phi x < ε := by
    have hmul :
        (B + 1) * phi x < (B + 1) * (ε / (B + 1)) :=
      mul_lt_mul_of_pos_left hxsmall hB1pos
    have hcancel : (B + 1) * (ε / (B + 1)) = ε := by
      field_simp [ne_of_gt hB1pos]
    simpa [hcancel] using hmul
  have hquot_prod_lt : |dphi x / phi x| * phi x < ε :=
    lt_of_le_of_lt hprod_le (lt_trans hBphi_lt hB1phi_lt)
  have hrewrite : dphi x = (dphi x / phi x) * phi x := by
    field_simp [ne_of_gt hphipos]
  calc
    |dphi x| = |(dphi x / phi x) * phi x| := congrArg abs hrewrite
    _ = |dphi x / phi x| * phi x := by rw [abs_mul, abs_of_pos hphipos]
    _ < ε := hquot_prod_lt

/-- A bounded log derivative on an arbitrarily-small positive `Phi` rules out
any uniform positive lower bound on the numerator derivative. -/
theorem not_exists_absDerivativeLowerBound_of_uniform_abs_logDerivative_bound
    {phi dphi : A -> ℝ} {B : ℝ}
    (hpos : ∀ x : A, 0 < phi x)
    (hsmall : HasArbitrarilySmallColeHopfValues phi)
    (hlog : ∀ x : A, |dphi x / phi x| ≤ B) :
    ¬ ∃ a : ℝ, HasUniformAbsDerivativeLowerBound dphi a := by
  exact not_exists_hasUniformAbsDerivativeLowerBound_of_arbitrarilySmallAbsValues
    (f := dphi)
    (abs_derivative_arbitrarilySmall_of_uniform_abs_logDerivative_bound
      (phi := phi) (dphi := dphi) hpos hsmall hlog)

/-- In one finite direction, the corresponding `gamma` log-energy can exceed
any proposed real bound. -/
theorem exists_gamma_singleton_logDerivative_gt_of_arbitrarilySmallValues
    {phi dphi : A -> ℝ} {a : ℝ}
    (hpos : ∀ x : A, 0 < phi x)
    (hsmall : HasArbitrarilySmallColeHopfValues phi)
    (hderiv : HasUniformAbsDerivativeLowerBound dphi a)
    (B : ℝ) :
    ∃ x : A, B < gamma (fun _ : Fin 1 => dphi x / phi x) := by
  let M : ℝ := max (|B| + 1) 1
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right (|B| + 1) 1)
  rcases exists_abs_logDerivative_gt_of_arbitrarilySmallValues
      (phi := phi) (dphi := dphi) hpos hsmall hderiv hMpos with ⟨x, hx⟩
  let q : ℝ := dphi x / phi x
  have hBltM : B < M := by
    have hBabs : B ≤ |B| := le_abs_self B
    have hlt : B < |B| + 1 := by linarith
    exact lt_of_lt_of_le hlt (le_max_left (|B| + 1) 1)
  have hMleM2 : M ≤ M ^ 2 := by
    have hMge : 1 ≤ M := le_max_right (|B| + 1) 1
    nlinarith
  have hBltM2 : B < M ^ 2 := lt_of_lt_of_le hBltM hMleM2
  have hqabs : M < |q| := by
    simpa [q] using hx
  have hMsq_lt_qsq : M ^ 2 < q ^ 2 := by
    have hMnonneg : 0 ≤ M := le_of_lt hMpos
    have hqabs_nonneg : 0 ≤ |q| := abs_nonneg q
    have hsq : M ^ 2 < |q| ^ 2 := by
      nlinarith
    simpa [sq_abs] using hsq
  refine ⟨x, ?_⟩
  have hgamma : gamma (fun _ : Fin 1 => q) = q ^ 2 := by
    simp [gamma]
  simpa [q, hgamma] using lt_trans hBltM2 hMsq_lt_qsq

/-- Therefore the one-direction log-energy has no finite uniform real bound. -/
theorem not_exists_uniform_singleton_logDerivative_gamma_bound_of_arbitrarilySmallValues
    {phi dphi : A -> ℝ} {a : ℝ}
    (hpos : ∀ x : A, 0 < phi x)
    (hsmall : HasArbitrarilySmallColeHopfValues phi)
    (hderiv : HasUniformAbsDerivativeLowerBound dphi a) :
    ¬ ∃ B : ℝ, ∀ x : A, gamma (fun _ : Fin 1 => dphi x / phi x) ≤ B := by
  rintro ⟨B, hB⟩
  rcases exists_gamma_singleton_logDerivative_gt_of_arbitrarilySmallValues
      (phi := phi) (dphi := dphi) hpos hsmall hderiv B with ⟨x, hx⟩
  exact not_lt_of_ge (hB x) hx

/-- The existing finite log-gradient estimate as a method on the lower-bound
certificate. -/
theorem HasColeHopfPointwiseLowerBound.gamma_div_le
    [Fintype ι]
    {phi : A -> ℝ} {m : ℝ}
    (h : HasColeHopfPointwiseLowerBound phi m)
    (D : ι -> ℝ) (x : A) :
    gamma (fun i => D i / phi x) ≤ gamma D / m ^ 2 :=
  Mettapedia.FluidDynamics.NavierStokes.gamma_div_le D h.m_pos (h.lower x)

/-- The existing `W = -2 nu log Phi` coefficient-energy estimate as a method on
the lower-bound certificate. -/
theorem HasColeHopfPointwiseLowerBound.gamma_negTwoNuLog_le
    [Fintype ι]
    {phi : A -> ℝ} {m nu : ℝ}
    (h : HasColeHopfPointwiseLowerBound phi m)
    (D : ι -> ℝ) (x : A) :
    gamma (fun i => (-2 * nu) * (D i / phi x)) ≤
      (4 * nu ^ 2 / m ^ 2) * gamma D :=
  Mettapedia.FluidDynamics.NavierStokes.gamma_negTwoNuLog_le
    (D := D) (Φ := phi x) (m := m) (ν := nu)
    h.m_pos (h.lower x)

/-- Every `ColeHopfIdentityData` package carries the required pointwise
positive lower bound on its heat field. -/
theorem ColeHopfIdentityData.hasPointwiseLowerBound
    [Fintype ι]
    (S : ColeHopfIdentityData (Time := Time) (ι := ι) (X := X)) :
    HasColeHopfPointwiseLowerBound S.Phi S.mPhi :=
  ⟨S.mPhi_pos, S.Phi_lower⟩

theorem ColeHopfIdentityData.Phi_pos
    [Fintype ι]
    (S : ColeHopfIdentityData (Time := Time) (ι := ι) (X := X))
    (t : Time) :
    0 < S.Phi t :=
  S.hasPointwiseLowerBound.pos t

theorem ColeHopfIdentityData.Phi_ne_zero
    [Fintype ι]
    (S : ColeHopfIdentityData (Time := Time) (ι := ι) (X := X))
    (t : Time) :
    S.Phi t ≠ 0 :=
  S.hasPointwiseLowerBound.ne_zero t

theorem ColeHopfIdentityData.not_Phi_nonpos
    [Fintype ι]
    (S : ColeHopfIdentityData (Time := Time) (ι := ι) (X := X))
    (t : Time) :
    ¬ S.Phi t ≤ 0 :=
  S.hasPointwiseLowerBound.not_nonpos t

/-- If a proposed heat field has a nonpositive value, no identity-level
Cole-Hopf package with that heat field exists. -/
theorem not_exists_ColeHopfIdentityData_of_nonpos_phi
    [Fintype ι]
    {phi : Time -> ℝ} {t0 : Time}
    (hphi : phi t0 ≤ 0) :
    ¬ ∃ S : ColeHopfIdentityData (Time := Time) (ι := ι) (X := X), S.Phi = phi := by
  rintro ⟨S, hS⟩
  have hpos : 0 < phi t0 := by
    rw [← hS]
    exact S.Phi_pos t0
  exact not_lt_of_ge hphi hpos

/-- Zero values are already enough to block the identity-level Cole-Hopf
package.  Nonnegative heat is therefore not a substitute for a strict positive
lower bound at the log-transform layer. -/
theorem not_exists_ColeHopfIdentityData_of_zero_phi
    [Fintype ι]
    {phi : Time -> ℝ} {t0 : Time}
    (hphi : phi t0 = 0) :
    ¬ ∃ S : ColeHopfIdentityData (Time := Time) (ι := ι) (X := X), S.Phi = phi := by
  exact not_exists_ColeHopfIdentityData_of_nonpos_phi
    (Time := Time) (ι := ι) (X := X) (phi := phi) (t0 := t0) (by simp [hphi])

/-- A pointwise-positive heat field still cannot enter the identity-level
Cole-Hopf package if its values are not bounded away from zero. -/
theorem not_exists_ColeHopfIdentityData_of_arbitrarilySmall_phi
    [Fintype ι]
    {phi : Time -> ℝ}
    (hsmall : HasArbitrarilySmallColeHopfValues phi) :
    ¬ ∃ S : ColeHopfIdentityData (Time := Time) (ι := ι) (X := X), S.Phi = phi := by
  rintro ⟨S, hS⟩
  have hbound : HasColeHopfPointwiseLowerBound phi S.mPhi := by
    rw [← hS]
    exact S.hasPointwiseLowerBound
  exact not_hasColeHopfPointwiseLowerBound_of_arbitrarilySmallValues
    (phi := phi) (m := S.mPhi) hsmall hbound

end PositiveLowerBound

end NavierStokes
end FluidDynamics
end Mettapedia
