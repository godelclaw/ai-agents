import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Yang-Mills Mass Gap Foundations

This file starts the Yang-Mills lane with a small, reusable spectral layer.
The Clay statement phrases the mass gap as the Hamiltonian having no spectrum
in an interval `(0, Δ)` above the vacuum.  We isolate that condition for a
bounded real-linear Hamiltonian and prove the basic audit lemmas that any
future Yang-Mills construction must satisfy.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills

/-- Euclidean coordinate model for four-dimensional spacetime used by the
reference Yang-Mills statement.  This file does not pretend that Euclidean
coordinates solve the analytic construction problem; they only fix the common
ambient coordinate type for later local-operator and field-strength work. -/
abbrev Spacetime := EuclideanSpace ℝ (Fin 4)

/-- Spatial coordinates used when discussing clustering estimates. -/
abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- Bounded real-linear operators on a normed state space.  This is the
bounded-operator surface used by Mathlib's current spectrum API. -/
abbrev LinearOperator
    (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H] :=
  H →L[ℝ] H

/-- Direct formalization of “the Hamiltonian has no spectrum in `(0, Δ)`”. -/
def SpectrumAvoidsOpenInterval
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (A : LinearOperator H) (lo hi : ℝ) : Prop :=
  ∀ E : ℝ, E ∈ spectrum ℝ A → E ∉ Set.Ioo lo hi

/-- Spectral mass gap for a bounded Hamiltonian: a positive `Δ` together with
absence of spectrum in `(0, Δ)`. -/
def HasSpectralMassGap
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (A : LinearOperator H) (Δ : ℝ) : Prop :=
  0 < Δ ∧ SpectrumAvoidsOpenInterval A 0 Δ

/-- Positive-energy spectral condition.  In a full Wightman/Osterwalder-Schrader
surface this is part of the theory data; here it is kept separate so the gap
predicate itself stays auditable. -/
def HasPositiveEnergySpectrum
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (A : LinearOperator H) : Prop :=
  ∀ E : ℝ, E ∈ spectrum ℝ A → 0 ≤ E

/-- Vacuum energy condition: zero is in the Hamiltonian spectrum. -/
def HasVacuumEnergyZero
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (A : LinearOperator H) : Prop :=
  0 ∈ spectrum ℝ A

/-- A first positive spectral value: `m` is spectral, strictly positive, and
every strictly positive spectral value lies at or above `m`.  This isolates the
bounded-operator audit target usually expressed informally as “the first
excitation has mass `m`”. -/
def HasFirstPositiveSpectralValue
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (A : LinearOperator H) (m : ℝ) : Prop :=
  m ∈ spectrum ℝ A ∧
    0 < m ∧
      ∀ E : ℝ, E ∈ spectrum ℝ A → 0 < E → m ≤ E

/-- The positive part of the Hamiltonian spectrum.  This is the order-theoretic
surface on which “first positive spectral value” becomes `IsLeast`. -/
def PositiveSpectrumSet
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (A : LinearOperator H) : Set ℝ :=
  {E : ℝ | E ∈ spectrum ℝ A ∧ 0 < E}

/-- The spectral gaps admitted by a bounded Hamiltonian. -/
def SpectralGapSet
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (A : LinearOperator H) : Set ℝ :=
  {Δ : ℝ | HasSpectralMassGap A Δ}

/-- Infimum of the positive spectrum.  As with `SpectralGapSup`, this is an
honest audit value only under hypotheses that make the positive spectrum
nonempty and appropriately bounded; the first-positive-value lemmas below give
the safe use case. -/
def PositiveSpectralInf
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (A : LinearOperator H) : ℝ :=
  sInf (PositiveSpectrumSet A)

/-- Supremum of the spectral gaps admitted by a bounded Hamiltonian.  This is
only a reliable mass audit value when the gap set is nonempty and bounded
above; the lemmas below make those hypotheses explicit. -/
def SpectralGapSup
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (A : LinearOperator H) : ℝ :=
  sSup (SpectralGapSet A)

/-- Finite mass, in the bounded-Hamiltonian spectral formulation: all admitted
spectral gaps have a positive upper bound. -/
def HasFiniteSpectralMass
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (A : LinearOperator H) : Prop :=
  ∃ M : ℝ, 0 < M ∧ ∀ Δ : ℝ, HasSpectralMassGap A Δ → Δ ≤ M

/-- A quadratic-form mass gap, matching the common Hilbert-space inequality
used as a proof obligation before passing to a spectral theorem. -/
def HasQuadraticMassGap
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : LinearOperator H) (Ω : H) (Δ : ℝ) : Prop :=
  0 < Δ ∧
    ∀ ψ : H, inner ℝ ψ Ω = 0 →
      Δ * inner ℝ ψ ψ ≤ inner ℝ (A ψ) ψ

theorem HasSpectralMassGap.positive
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {Δ : ℝ}
    (hgap : HasSpectralMassGap A Δ) :
    0 < Δ :=
  hgap.1

theorem HasSpectralMassGap.no_spectrum_in_gap
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {Δ E : ℝ}
    (hgap : HasSpectralMassGap A Δ)
    (hE : E ∈ spectrum ℝ A) :
    E ∉ Set.Ioo 0 Δ :=
  hgap.2 E hE

theorem HasFirstPositiveSpectralValue.spectrum_mem
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {m : ℝ}
    (hfirst : HasFirstPositiveSpectralValue A m) :
    m ∈ spectrum ℝ A :=
  hfirst.1

theorem HasFirstPositiveSpectralValue.positive
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {m : ℝ}
    (hfirst : HasFirstPositiveSpectralValue A m) :
    0 < m :=
  hfirst.2.1

theorem HasFirstPositiveSpectralValue.lower_bound
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {m E : ℝ}
    (hfirst : HasFirstPositiveSpectralValue A m)
    (hE : E ∈ spectrum ℝ A)
    (hEpos : 0 < E) :
    m ≤ E :=
  hfirst.2.2 E hE hEpos

theorem HasFirstPositiveSpectralValue.mem_positiveSpectrumSet
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {m : ℝ}
    (hfirst : HasFirstPositiveSpectralValue A m) :
    m ∈ PositiveSpectrumSet A :=
  ⟨hfirst.spectrum_mem, hfirst.positive⟩

/-- A first positive spectral value is exactly a least element of the positive
spectrum set. -/
theorem HasFirstPositiveSpectralValue.isLeast_positiveSpectrumSet
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {m : ℝ}
    (hfirst : HasFirstPositiveSpectralValue A m) :
    IsLeast (PositiveSpectrumSet A) m := by
  refine ⟨hfirst.mem_positiveSpectrumSet, ?_⟩
  intro E hE
  exact hfirst.lower_bound hE.1 hE.2

/-- Order-theoretic characterization of first positive spectral value. -/
theorem hasFirstPositiveSpectralValue_iff_isLeast_positiveSpectrumSet
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {m : ℝ} :
    HasFirstPositiveSpectralValue A m ↔
      IsLeast (PositiveSpectrumSet A) m := by
  constructor
  · intro hfirst
    exact hfirst.isLeast_positiveSpectrumSet
  · intro hleast
    exact ⟨hleast.1.1, hleast.1.2, by
      intro E hE hEpos
      exact hleast.2 ⟨hE, hEpos⟩⟩

/-- When the positive spectrum has a first value `m`, its infimum is exactly
`m`. -/
theorem HasFirstPositiveSpectralValue.positiveSpectralInf_eq
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {m : ℝ}
    (hfirst : HasFirstPositiveSpectralValue A m) :
    PositiveSpectralInf A = m := by
  unfold PositiveSpectralInf
  exact hfirst.isLeast_positiveSpectrumSet.csInf_eq

/-- The first positive spectral value, if supplied, is unique. -/
theorem HasFirstPositiveSpectralValue.unique
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {m n : ℝ}
    (hm : HasFirstPositiveSpectralValue A m)
    (hn : HasFirstPositiveSpectralValue A n) :
    m = n :=
  le_antisymm (hm.lower_bound hn.spectrum_mem hn.positive)
    (hn.lower_bound hm.spectrum_mem hm.positive)

/-- Pointwise obstruction: finding one spectral value in `(0, Δ)` rules out
`Δ` as a spectral mass gap. -/
theorem not_hasSpectralMassGap_of_spectrum_in_gap
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {Δ E : ℝ}
    (hE : E ∈ spectrum ℝ A)
    (hEpos : 0 < E) (hElt : E < Δ) :
    ¬ HasSpectralMassGap A Δ := by
  intro hgap
  exact hgap.no_spectrum_in_gap hE ⟨hEpos, hElt⟩

/-- Nonpositive windows cannot be mass gaps, regardless of the spectrum. -/
theorem not_hasSpectralMassGap_of_nonpos
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {Δ : ℝ}
    (hΔ : Δ ≤ 0) :
    ¬ HasSpectralMassGap A Δ := by
  intro hgap
  exact (not_lt_of_ge hΔ) hgap.positive

/-- A first positive spectral value excludes all lower positive spectral
values. -/
theorem HasFirstPositiveSpectralValue.not_spectrum_of_pos_lt
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {m E : ℝ}
    (hfirst : HasFirstPositiveSpectralValue A m)
    (hEpos : 0 < E) (hEm : E < m) :
    E ∉ spectrum ℝ A := by
  intro hE
  exact (not_lt_of_ge (hfirst.lower_bound hE hEpos)) hEm

/-- A first positive spectral value confines the whole spectrum to the
nonpositive half-line together with `[m,∞)`. -/
theorem HasFirstPositiveSpectralValue.spectrum_subset_nonpos_or_first
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {m : ℝ}
    (hfirst : HasFirstPositiveSpectralValue A m) :
    spectrum ℝ A ⊆ {E : ℝ | E ≤ 0 ∨ m ≤ E} := by
  intro E hE
  by_cases hEpos : 0 < E
  · exact Or.inr (hfirst.lower_bound hE hEpos)
  · exact Or.inl (le_of_not_gt hEpos)

/-- With positive energy, the first positive spectral value splits the spectrum
into the vacuum value and the closed interval `[m,∞)`. -/
theorem HasFirstPositiveSpectralValue.spectrum_subset_vacuum_or_first_of_positiveEnergy
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {m : ℝ}
    (hfirst : HasFirstPositiveSpectralValue A m)
    (hpos : HasPositiveEnergySpectrum A) :
    spectrum ℝ A ⊆ {E : ℝ | E = 0 ∨ m ≤ E} := by
  intro E hE
  by_cases hEpos : 0 < E
  · exact Or.inr (hfirst.lower_bound hE hEpos)
  · exact Or.inl (le_antisymm (le_of_not_gt hEpos) (hpos E hE))

/-- Spectral mass gaps are downward closed: a smaller positive interval is also
free of positive spectrum. -/
theorem HasSpectralMassGap.mono
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {δ Δ : ℝ}
    (hgap : HasSpectralMassGap A Δ)
    (hδ : 0 < δ) (hδΔ : δ ≤ Δ) :
    HasSpectralMassGap A δ := by
  refine ⟨hδ, ?_⟩
  intro E hE hEin
  exact hgap.no_spectrum_in_gap hE ⟨hEin.1, lt_of_lt_of_le hEin.2 hδΔ⟩

/-- Set-level form of downward closure for the admitted spectral gaps. -/
theorem SpectralGapSet.downward_closed
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {δ Δ : ℝ}
    (hΔ : Δ ∈ SpectralGapSet A)
    (hδ : 0 < δ) (hδΔ : δ ≤ Δ) :
    δ ∈ SpectralGapSet A :=
  hΔ.mono hδ hδΔ

/-- Every positive window at or below the first positive spectral value is an
admitted spectral mass gap. -/
theorem HasFirstPositiveSpectralValue.hasSpectralMassGap_of_le
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {m Δ : ℝ}
    (hfirst : HasFirstPositiveSpectralValue A m)
    (hΔpos : 0 < Δ) (hΔm : Δ ≤ m) :
    HasSpectralMassGap A Δ := by
  refine ⟨hΔpos, ?_⟩
  intro E hE hEin
  exact (not_lt_of_ge (hfirst.lower_bound hE hEin.1))
    (lt_of_lt_of_le hEin.2 hΔm)

/-- The first positive spectral value itself is an admitted spectral mass gap. -/
theorem HasFirstPositiveSpectralValue.hasSpectralMassGap_self
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {m : ℝ}
    (hfirst : HasFirstPositiveSpectralValue A m) :
    HasSpectralMassGap A m :=
  hfirst.hasSpectralMassGap_of_le hfirst.positive le_rfl

/-- If `m` is the first positive spectral value, admitted spectral gaps are
exactly the positive windows at or below `m`. -/
theorem HasFirstPositiveSpectralValue.hasSpectralMassGap_iff
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {m Δ : ℝ}
    (hfirst : HasFirstPositiveSpectralValue A m) :
    HasSpectralMassGap A Δ ↔ 0 < Δ ∧ Δ ≤ m := by
  constructor
  · intro hgap
    refine ⟨hgap.positive, ?_⟩
    by_contra hnot
    exact hgap.no_spectrum_in_gap hfirst.spectrum_mem
      ⟨hfirst.positive, lt_of_not_ge hnot⟩
  · intro hΔ
    exact hfirst.hasSpectralMassGap_of_le hΔ.1 hΔ.2

/-- Set-level audit identity: first positive spectral value `m` makes the
admitted gap set exactly `(0,m]`. -/
theorem HasFirstPositiveSpectralValue.spectralGapSet_eq_Ioc
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {m : ℝ}
    (hfirst : HasFirstPositiveSpectralValue A m) :
    SpectralGapSet A = Set.Ioc 0 m := by
  ext Δ
  exact hfirst.hasSpectralMassGap_iff

/-- With positive energy, a spectral mass gap says every spectral value is
either the vacuum value `0` or at least `Δ`. -/
theorem HasSpectralMassGap.eq_zero_or_gap_le_of_positive_energy
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {Δ E : ℝ}
    (hgap : HasSpectralMassGap A Δ)
    (hpos : HasPositiveEnergySpectrum A)
    (hE : E ∈ spectrum ℝ A) :
    E = 0 ∨ Δ ≤ E := by
  by_cases hlt : E < Δ
  · have hnotpos : ¬ 0 < E := by
      intro hEpos
      exact hgap.no_spectrum_in_gap hE ⟨hEpos, hlt⟩
    have hEle : E ≤ 0 := le_of_not_gt hnotpos
    exact Or.inl (le_antisymm hEle (hpos E hE))
  · exact Or.inr (le_of_not_gt hlt)

/-- If a positive spectral value exists for a Hamiltonian with gap `Δ`, then it
is at least `Δ`.  This is the constructive threshold form of the open-interval
exclusion. -/
theorem HasSpectralMassGap.gap_le_of_pos_spectrum
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {Δ E : ℝ}
    (hgap : HasSpectralMassGap A Δ)
    (hE : E ∈ spectrum ℝ A)
    (hEpos : 0 < E) :
    Δ ≤ E := by
  by_contra hnot
  exact hgap.no_spectrum_in_gap hE ⟨hEpos, lt_of_not_ge hnot⟩

/-- An admitted gap whose endpoint is actually spectral is exactly a first
positive spectral value at that endpoint. -/
theorem HasSpectralMassGap.hasFirstPositiveSpectralValue_of_spectrum_mem
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {m : ℝ}
    (hgap : HasSpectralMassGap A m)
    (hm : m ∈ spectrum ℝ A) :
    HasFirstPositiveSpectralValue A m := by
  refine ⟨hm, hgap.positive, ?_⟩
  intro E hE hEpos
  exact hgap.gap_le_of_pos_spectrum hE hEpos

/-- Endpoint formulation of first positive spectral value: `m` is first
positive iff it is spectral and the interval `(0,m)` is spectrally empty. -/
theorem hasFirstPositiveSpectralValue_iff_spectrum_mem_and_hasSpectralMassGap
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {m : ℝ} :
    HasFirstPositiveSpectralValue A m ↔
      m ∈ spectrum ℝ A ∧ HasSpectralMassGap A m := by
  constructor
  · intro hfirst
    exact ⟨hfirst.spectrum_mem, hfirst.hasSpectralMassGap_self⟩
  · intro h
    exact h.2.hasFirstPositiveSpectralValue_of_spectrum_mem h.1

/-- Equivalent operational form: a gap excludes every strictly positive
spectral value below the gap. -/
theorem HasSpectralMassGap.not_spectrum_of_pos_lt
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {Δ E : ℝ}
    (hgap : HasSpectralMassGap A Δ)
    (hEpos : 0 < E) (hElt : E < Δ) :
    E ∉ spectrum ℝ A := by
  intro hE
  exact hgap.no_spectrum_in_gap hE ⟨hEpos, hElt⟩

/-- A gap alone confines the spectrum to the nonpositive half-line together
with the closed interval `[Δ, ∞)`. -/
theorem HasSpectralMassGap.spectrum_subset_nonpos_or_gap
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {Δ : ℝ}
    (hgap : HasSpectralMassGap A Δ) :
    spectrum ℝ A ⊆ {E : ℝ | E ≤ 0 ∨ Δ ≤ E} := by
  intro E hE
  by_cases hEpos : 0 < E
  · exact Or.inr (hgap.gap_le_of_pos_spectrum hE hEpos)
  · exact Or.inl (le_of_not_gt hEpos)

/-- Exact set-level characterization of a spectral mass gap: positivity of the
endpoint together with confinement of the spectrum to the nonpositive half-line
and the closed interval `[Δ, ∞)`. -/
theorem hasSpectralMassGap_iff_positive_and_spectrum_subset_nonpos_or_gap
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {Δ : ℝ} :
    HasSpectralMassGap A Δ ↔
      0 < Δ ∧ spectrum ℝ A ⊆ {E : ℝ | E ≤ 0 ∨ Δ ≤ E} := by
  constructor
  · intro hgap
    exact ⟨hgap.positive, hgap.spectrum_subset_nonpos_or_gap⟩
  · rintro ⟨hΔpos, hsubset⟩
    refine ⟨hΔpos, ?_⟩
    intro E hE hIoo
    rcases hsubset hE with hnonpos | hΔle
    · exact (not_lt_of_ge hnonpos) hIoo.1
    · exact (not_lt_of_ge hΔle) hIoo.2

/-- With positive energy, every non-vacuum spectral value is at least the gap. -/
theorem HasSpectralMassGap.gap_le_of_positive_energy_of_ne_zero
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {Δ E : ℝ}
    (hgap : HasSpectralMassGap A Δ)
    (hpos : HasPositiveEnergySpectrum A)
    (hE : E ∈ spectrum ℝ A)
    (hne : E ≠ 0) :
    Δ ≤ E := by
  rcases hgap.eq_zero_or_gap_le_of_positive_energy hpos hE with hzero | hle
  · exact False.elim (hne hzero)
  · exact hle

/-- Set-level positive-energy version of the spectral split. -/
theorem HasSpectralMassGap.spectrum_subset_vacuum_or_gap_of_positive_energy
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {Δ : ℝ}
    (hgap : HasSpectralMassGap A Δ)
    (hpos : HasPositiveEnergySpectrum A) :
    spectrum ℝ A ⊆ {E : ℝ | E = 0 ∨ Δ ≤ E} := by
  intro E hE
  exact hgap.eq_zero_or_gap_le_of_positive_energy hpos hE

/-- Under positive energy, a spectral mass gap is exactly the statement that
the spectrum is confined to the vacuum value `0` together with `[Δ, ∞)`. -/
theorem hasSpectralMassGap_iff_positive_and_spectrum_subset_vacuum_or_gap_of_positive_energy
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {Δ : ℝ}
    (hpos : HasPositiveEnergySpectrum A) :
    HasSpectralMassGap A Δ ↔
      0 < Δ ∧ spectrum ℝ A ⊆ {E : ℝ | E = 0 ∨ Δ ≤ E} := by
  constructor
  · intro hgap
    exact ⟨hgap.positive, hgap.spectrum_subset_vacuum_or_gap_of_positive_energy hpos⟩
  · rintro ⟨hΔpos, hsubset⟩
    refine ⟨hΔpos, ?_⟩
    intro E hE
    rintro ⟨hEpos, hEΔ⟩
    rcases hsubset hE with hzero | hΔle
    · rw [hzero] at hEpos
      exact (lt_irrefl 0) hEpos
    · exact (not_lt_of_ge hΔle) hEΔ

/-- A single positive spectral value supplies a finite upper bound for every
admissible spectral gap. -/
theorem hasFiniteSpectralMass_of_pos_spectrum
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {E : ℝ}
    (hE : E ∈ spectrum ℝ A)
    (hEpos : 0 < E) :
    HasFiniteSpectralMass A := by
  refine ⟨E, hEpos, ?_⟩
  intro Δ hgap
  exact hgap.gap_le_of_pos_spectrum hE hEpos

/-- A first positive spectral value supplies finite spectral mass. -/
theorem HasFirstPositiveSpectralValue.hasFiniteSpectralMass
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {m : ℝ}
    (hfirst : HasFirstPositiveSpectralValue A m) :
    HasFiniteSpectralMass A :=
  hasFiniteSpectralMass_of_pos_spectrum hfirst.spectrum_mem hfirst.positive

/-- The finite spectral mass predicate is exactly boundedness above of the
admitted spectral-gap set.  The definition keeps an explicitly positive bound;
this theorem connects it to Mathlib's standard order-theoretic `BddAbove`
surface. -/
theorem hasFiniteSpectralMass_iff_bddAbove_spectralGapSet
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} :
    HasFiniteSpectralMass A ↔ BddAbove (SpectralGapSet A) := by
  constructor
  · intro hfinite
    rcases hfinite with ⟨M, _hMpos, hbound⟩
    exact ⟨M, by
      intro Δ hΔ
      exact hbound Δ hΔ⟩
  · intro hbdd
    rcases hbdd with ⟨M, hMbound⟩
    refine ⟨max M 1, lt_of_lt_of_le zero_lt_one (le_max_right M 1), ?_⟩
    intro Δ hgap
    exact le_trans (hMbound hgap) (le_max_left M 1)

/-- Under the two audit hypotheses that make the supremum meaningful
— boundedness above and an actually admitted gap — `SpectralGapSup` is the
least upper bound of all admitted spectral gaps. -/
theorem spectralGapSup_isLUB_of_hasFiniteSpectralMass_of_gap
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {Δ : ℝ}
    (hfinite : HasFiniteSpectralMass A)
    (hgap : HasSpectralMassGap A Δ) :
    IsLUB (SpectralGapSet A) (SpectralGapSup A) := by
  unfold SpectralGapSup
  exact isLUB_csSup ⟨Δ, hgap⟩
    ((hasFiniteSpectralMass_iff_bddAbove_spectralGapSet (A := A)).mp hfinite)

/-- Every admitted gap is bounded above by the audited supremum, provided the
finite-mass audit supplies boundedness above. -/
theorem HasSpectralMassGap.le_spectralGapSup_of_hasFiniteSpectralMass
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {Δ : ℝ}
    (hgap : HasSpectralMassGap A Δ)
    (hfinite : HasFiniteSpectralMass A) :
    Δ ≤ SpectralGapSup A := by
  have hbdd : BddAbove (SpectralGapSet A) :=
    (hasFiniteSpectralMass_iff_bddAbove_spectralGapSet (A := A)).mp hfinite
  unfold SpectralGapSup
  exact le_csSup hbdd hgap

/-- If a finite-mass Hamiltonian admits at least one gap, its spectral-gap
supremum is strictly positive. -/
theorem spectralGapSup_pos_of_hasFiniteSpectralMass_of_gap
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {Δ : ℝ}
    (hfinite : HasFiniteSpectralMass A)
    (hgap : HasSpectralMassGap A Δ) :
    0 < SpectralGapSup A := by
  exact lt_of_lt_of_le hgap.positive
    (hgap.le_spectralGapSup_of_hasFiniteSpectralMass hfinite)

/-- A uniform upper bound for all admitted gaps bounds the audited supremum,
as long as the gap set is nonempty. -/
theorem spectralGapSup_le_of_gap_bound
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {Δ₀ M : ℝ}
    (hgap₀ : HasSpectralMassGap A Δ₀)
    (hbound : ∀ Δ : ℝ, HasSpectralMassGap A Δ → Δ ≤ M) :
    SpectralGapSup A ≤ M := by
  unfold SpectralGapSup
  exact csSup_le ⟨Δ₀, hgap₀⟩ (by
    intro Δ hΔ
    exact hbound Δ hΔ)

/-- Any positive spectral value upper-bounds the supremum of admitted gaps.
This is the supremum-level version of the pointwise threshold obstruction. -/
theorem spectralGapSup_le_of_pos_spectrum_of_gap
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {Δ₀ E : ℝ}
    (hgap₀ : HasSpectralMassGap A Δ₀)
    (hE : E ∈ spectrum ℝ A)
    (hEpos : 0 < E) :
    SpectralGapSup A ≤ E := by
  exact spectralGapSup_le_of_gap_bound (A := A) hgap₀ (by
    intro Δ hgap
    exact hgap.gap_le_of_pos_spectrum hE hEpos)

/-- If `m` is the first positive spectral value, then the audited supremum of
all admitted spectral gaps is exactly `m`. -/
theorem HasFirstPositiveSpectralValue.spectralGapSup_eq
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {m : ℝ}
    (hfirst : HasFirstPositiveSpectralValue A m) :
    SpectralGapSup A = m := by
  have hgapm : HasSpectralMassGap A m := hfirst.hasSpectralMassGap_self
  have hfinite : HasFiniteSpectralMass A := hfirst.hasFiniteSpectralMass
  have hsup : IsLUB (SpectralGapSet A) (SpectralGapSup A) :=
    spectralGapSup_isLUB_of_hasFiniteSpectralMass_of_gap hfinite hgapm
  have hm : IsLUB (SpectralGapSet A) m := by
    refine ⟨?_, ?_⟩
    · intro Δ hgap
      exact hgap.gap_le_of_pos_spectrum hfirst.spectrum_mem hfirst.positive
    · intro b hb
      exact hb hgapm
  exact hsup.unique hm

/-- Under a first-positive-value hypothesis, the gap-supremum audit and the
positive-spectrum infimum audit agree. -/
theorem HasFirstPositiveSpectralValue.spectralGapSup_eq_positiveSpectralInf
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {m : ℝ}
    (hfirst : HasFirstPositiveSpectralValue A m) :
    SpectralGapSup A = PositiveSpectralInf A := by
  rw [hfirst.spectralGapSup_eq, hfirst.positiveSpectralInf_eq]

/-- If admitted spectral gaps occur above every proposed bound, then finite
spectral mass is impossible. -/
theorem not_hasFiniteSpectralMass_of_arbitrarily_large_gaps
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H}
    (hlarge : ∀ M : ℝ, ∃ Δ : ℝ, M < Δ ∧ HasSpectralMassGap A Δ) :
    ¬ HasFiniteSpectralMass A := by
  intro hfinite
  rcases hfinite with ⟨M, _hMpos, hbound⟩
  rcases hlarge M with ⟨Δ, hMlt, hgap⟩
  exact (not_lt_of_ge (hbound Δ hgap)) hMlt

/-- If every positive window is declared to be a spectral gap, then the
finite-mass predicate fails.  This separates a true finite first excitation
from the degenerate situation in which no positive spectrum is seen at all. -/
theorem not_hasFiniteSpectralMass_of_all_positive_gaps
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H}
    (hall : ∀ Δ : ℝ, 0 < Δ → HasSpectralMassGap A Δ) :
    ¬ HasFiniteSpectralMass A := by
  exact not_hasFiniteSpectralMass_of_arbitrarily_large_gaps (A := A) (by
    intro M
    refine ⟨max M 0 + 1, ?_, hall (max M 0 + 1) ?_⟩
    · exact lt_of_le_of_lt (le_max_left M 0) (lt_add_of_pos_right (max M 0) zero_lt_one)
    · exact lt_of_le_of_lt (le_max_right M 0) (lt_add_of_pos_right (max M 0) zero_lt_one))

/-- Quadratic-form gaps are also downward closed.  This theorem is intentionally
separate from the spectral theorem: it records the elementary monotonicity that
future analytic work can use before any unbounded-operator formalization is
available. -/
theorem HasQuadraticMassGap.mono
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {A : LinearOperator H} {Ω : H} {δ Δ : ℝ}
    (hgap : HasQuadraticMassGap A Ω Δ)
    (hδ : 0 < δ) (hδΔ : δ ≤ Δ) :
    HasQuadraticMassGap A Ω δ := by
  refine ⟨hδ, ?_⟩
  intro ψ horth
  have hnorm : 0 ≤ inner ℝ ψ ψ := real_inner_self_nonneg
  exact le_trans (mul_le_mul_of_nonneg_right hδΔ hnorm) (hgap.2 ψ horth)

/-- Any supplied finite spectral mass bound applies to every concrete spectral
gap. -/
theorem HasFiniteSpectralMass.bound_of_bound
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {M Δ : ℝ}
    (hM : 0 < M ∧ ∀ Δ' : ℝ, HasSpectralMassGap A Δ' → Δ' ≤ M)
    (hgap : HasSpectralMassGap A Δ) :
    Δ ≤ M :=
  hM.2 Δ hgap

end YangMills
end QuantumTheory
end Mettapedia
