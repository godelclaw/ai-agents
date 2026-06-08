import Mettapedia.Computability.PNP.ExactZABERMInterface
import Mettapedia.Computability.PNP.BitVecZABERMInterface

/-!
# P vs NP crux: atomic-measure obstruction to bad-code agreement bounds

The finite-class ERM recovery layer needs a uniform bad-code agreement bound:
every non-target code must agree with the target on at most `q` input mass.
This file tests that premise directly.

For any distribution `μ`, a bad code that agrees with the target on all
positive-mass inputs has agreement mass exactly `1`.  In particular, for an
atomic distribution `PMF.pure x`, agreeing at `x` is enough.  Hence no recovery
interface using a strict `q < 1` can be packaged unless the actual coded family
separates every bad code from the target on positive sampling mass.  This is not
a finite-image consequence; it is an additional support/disagreement obligation
on the actual switched predictor family.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

universe u

namespace BitEncodedClassifierFamily

section AtomicBadCodeAgreement

variable {Input : Type u} [Fintype Input]
variable {s : ℕ} (F : BitEncodedClassifierFamily Input s)

/-- A bad code that agrees on all positive-mass inputs blocks any strict
bad-code agreement bound for that distribution. -/
theorem not_badCodeAgreementBound_of_agrees_on_support
    {μ : PMF Input} {target : Input → Bool} {q : ℝ≥0∞}
    (c : F.toEncodedFamily.BadCodes target)
    (hagree : ∀ x, μ x ≠ 0 → F.decode c.1 x = target x)
    (hq_lt : q < 1) :
    ¬ (∀ d : F.toEncodedFamily.BadCodes target,
        agreementMass μ target (F.decode d.1) ≤ q) := by
  intro hbound
  have hone :
      agreementMass μ target (F.decode c.1) = 1 :=
    agreementMass_eq_one_of_agrees_on_support
      (μ := μ) (target := target) (predict := F.decode c.1) hagree
  have hle : (1 : ℝ≥0∞) ≤ q := by
    simpa [hone] using hbound c
  exact not_le_of_gt hq_lt hle

/-- A single bad code that agrees at the atom blocks any strict bad-code
agreement bound for the pure distribution at that atom. -/
theorem not_badCodeAgreementBound_pure_of_agrees
    {x : Input} {target : Input → Bool} {q : ℝ≥0∞}
    (c : F.toEncodedFamily.BadCodes target)
    (hagree : F.decode c.1 x = target x)
    (hq_lt : q < 1) :
    ¬ (∀ d : F.toEncodedFamily.BadCodes target,
        agreementMass (PMF.pure x) target (F.decode d.1) ≤ q) := by
  intro hbound
  have hone :
      agreementMass (PMF.pure x) target (F.decode c.1) = 1 :=
    agreementMass_pure_eq_one_of_agrees
      (x := x) (target := target) (predict := F.decode c.1) hagree
  have hle : (1 : ℝ≥0∞) ≤ q := by
    simpa [hone] using hbound c
  exact not_le_of_gt hq_lt hle

/-- A strict bad-code agreement bound must be at least the mass of any finite
region on which a bad code agrees with the target. -/
theorem regionMass_le_of_badCode_agrees_on
    {μ : PMF Input} {target : Input → Bool} {q : ℝ≥0∞}
    (hbound :
      ∀ d : F.toEncodedFamily.BadCodes target,
        agreementMass μ target (F.decode d.1) ≤ q)
    (c : F.toEncodedFamily.BadCodes target)
    (region : Finset Input)
    (hagree : ∀ x, x ∈ region → F.decode c.1 x = target x) :
    region.sum (fun x => μ x) ≤ q := by
  exact le_trans
    (finset_mass_le_agreementMass_of_agrees_on
      (μ := μ) (target := target) (predict := F.decode c.1) region hagree)
    (hbound c)

/-- If a bad code agrees with the target on a finite region whose mass is above
`q`, then no uniform bad-code agreement bound by `q` can hold. -/
theorem not_badCodeAgreementBound_of_agrees_on_region_gt
    {μ : PMF Input} {target : Input → Bool} {q : ℝ≥0∞}
    (c : F.toEncodedFamily.BadCodes target)
    (region : Finset Input)
    (hagree : ∀ x, x ∈ region → F.decode c.1 x = target x)
    (hmass : q < region.sum (fun x => μ x)) :
    ¬ (∀ d : F.toEncodedFamily.BadCodes target,
        agreementMass μ target (F.decode d.1) ≤ q) := by
  intro hbound
  exact not_le_of_gt hmass
    (F.regionMass_le_of_badCode_agrees_on hbound c region hagree)

/-- A strict bad-code agreement bound localizes: every finite region whose mass
is above the bound must contain a positive-mass disagreement for each bad code. -/
theorem exists_pos_mass_disagreement_in_region_of_badCodeAgreementBound_lt_mass
    {μ : PMF Input} {target : Input → Bool} {q : ℝ≥0∞}
    (hbound :
      ∀ d : F.toEncodedFamily.BadCodes target,
        agreementMass μ target (F.decode d.1) ≤ q)
    (c : F.toEncodedFamily.BadCodes target)
    (region : Finset Input)
    (hmass : q < region.sum (fun x => μ x)) :
    ∃ x, x ∈ region ∧ μ x ≠ 0 ∧ F.decode c.1 x ≠ target x := by
  exact
    exists_pos_mass_disagreement_in_region_of_agreementMass_le_of_lt_regionMass
      (μ := μ) (target := target) (predict := F.decode c.1) region
      (hbound c) hmass

/-- The same finite agreement region gives a lower bound on the IID deceptive
sample mass for the encoded family. -/
theorem regionMass_pow_le_deceptiveSampleMass_of_badCode_agrees_on
    {μ : PMF Input} {target : Input → Bool}
    (c : F.toEncodedFamily.BadCodes target)
    (region : Finset Input)
    (hagree : ∀ x, x ∈ region → F.decode c.1 x = target x)
    (m : ℕ) :
    region.sum (fun x => μ x) ^ m ≤
      F.toEncodedFamily.deceptiveSampleMass μ target m := by
  exact
    F.toEncodedFamily.regionMass_pow_le_deceptiveSampleMass_of_badCode_agrees_on
      c region hagree m

/-- Under a strict pure-atom agreement bound, every code that matches the target
at the atom must decode to the target globally. -/
theorem decode_eq_target_of_pure_agreementBound_lt_one
    {x : Input} {target : Input → Bool} {q : ℝ≥0∞}
    (hbound :
      ∀ c : F.toEncodedFamily.BadCodes target,
        agreementMass (PMF.pure x) target (F.decode c.1) ≤ q)
    (hq_lt : q < 1)
    {code : BitCode s}
    (hagree : F.decode code x = target x) :
    F.decode code = target := by
  classical
  by_contra hneq
  exact
    (F.not_badCodeAgreementBound_pure_of_agrees
      (x := x) (target := target) (q := q) ⟨code, hneq⟩ hagree hq_lt) hbound

/-- Contrapositive form useful at route interfaces: every bad code must
disagree with the target at the atom. -/
theorem badCode_disagrees_at_pure_atom_of_agreementBound_lt_one
    {x : Input} {target : Input → Bool} {q : ℝ≥0∞}
    (hbound :
      ∀ c : F.toEncodedFamily.BadCodes target,
        agreementMass (PMF.pure x) target (F.decode c.1) ≤ q)
    (hq_lt : q < 1)
    (c : F.toEncodedFamily.BadCodes target) :
    F.decode c.1 x ≠ target x := by
  intro hagree
  exact
    (F.not_badCodeAgreementBound_pure_of_agrees
      (x := x) (target := target) (q := q) c hagree hq_lt) hbound

/-- Under a strict agreement bound, every bad code must disagree on positive
sampling mass. -/
theorem exists_pos_mass_disagreement_of_badCode_agreementBound_lt_one
    {μ : PMF Input} {target : Input → Bool} {q : ℝ≥0∞}
    (hbound :
      ∀ c : F.toEncodedFamily.BadCodes target,
        agreementMass μ target (F.decode c.1) ≤ q)
    (hq_lt : q < 1)
    (c : F.toEncodedFamily.BadCodes target) :
    ∃ x, μ x ≠ 0 ∧ F.decode c.1 x ≠ target x := by
  classical
  by_contra hnone
  have hagree : ∀ x, μ x ≠ 0 → F.decode c.1 x = target x := by
    intro x hx
    by_contra hneq
    exact hnone ⟨x, hx, hneq⟩
  exact
    (F.not_badCodeAgreementBound_of_agrees_on_support
      (μ := μ) (target := target) (q := q) c hagree hq_lt) hbound

end AtomicBadCodeAgreement

end BitEncodedClassifierFamily

section ExactZABAtomicBadCodeAgreement

variable {Z : Type*} {r k : ℕ} {Index : Type*}
variable [Fintype Z]

/-- Pure-atom exact-ZAB ERM recovery with `q < 1` forces pointwise agreement at
the atom to collapse to global equality with the target predictor. -/
theorem ExactZABERMRecoveryData.decode_eq_predict_of_pure_atom_agreement_lt_one
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞} {x : ExactVisiblePostSwitchSurface Z k}
    (h :
      ExactZABERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index)
        (PMF.pure x) zfeat G q)
    (hq_lt : q < 1)
    (i : Index)
    {code : BitCode (r + (k + k) + 1)}
    (hagree :
      (rawExactZABDecisionListBitFamily Z r k zfeat).decode code x =
        G.predict i x) :
    (rawExactZABDecisionListBitFamily Z r k zfeat).decode code = G.predict i := by
  exact
    (rawExactZABDecisionListBitFamily Z r k zfeat).decode_eq_target_of_pure_agreementBound_lt_one
      (x := x) (target := G.predict i) (q := q)
      (h.agreement_le i) hq_lt hagree

/-- One exact-ZAB bad code agreeing at the pure atom refutes the strict recovery
package. -/
theorem not_ExactZABERMRecoveryData_of_pure_badCode_agrees
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞} {x : ExactVisiblePostSwitchSurface Z k}
    (i : Index)
    (c :
      (rawExactZABDecisionListBitFamily Z r k zfeat).toEncodedFamily.BadCodes
        (G.predict i))
    (hagree :
      (rawExactZABDecisionListBitFamily Z r k zfeat).decode c.1 x =
        G.predict i x)
    (hq_lt : q < 1) :
    ¬ Nonempty (ExactZABERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index)
        (PMF.pure x) zfeat G q) := by
  rintro ⟨h⟩
  exact
    ((rawExactZABDecisionListBitFamily Z r k zfeat).not_badCodeAgreementBound_pure_of_agrees
      (x := x) (target := G.predict i) (q := q) c hagree hq_lt) (h.agreement_le i)

/-- More generally, exact-ZAB recovery with `q < 1` forces every bad code to
disagree with the target on positive sampling mass. -/
theorem ExactZABERMRecoveryData.exists_pos_mass_disagreement_of_badCode
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hq_lt : q < 1)
    (i : Index)
    (c :
      (rawExactZABDecisionListBitFamily Z r k zfeat).toEncodedFamily.BadCodes
        (G.predict i)) :
    ∃ x, μ x ≠ 0 ∧
      (rawExactZABDecisionListBitFamily Z r k zfeat).decode c.1 x ≠
        G.predict i x := by
  exact
    (rawExactZABDecisionListBitFamily Z r k zfeat).exists_pos_mass_disagreement_of_badCode_agreementBound_lt_one
      (target := G.predict i) (q := q) (h.agreement_le i) hq_lt c

/-- Exact-ZAB recovery bounds must dominate the mass of every finite region on
which a bad code agrees with the selected target predictor. -/
theorem ExactZABERMRecoveryData.regionMass_le_of_badCode_agrees_on
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (i : Index)
    (c :
      (rawExactZABDecisionListBitFamily Z r k zfeat).toEncodedFamily.BadCodes
        (G.predict i))
    (region : Finset (ExactVisiblePostSwitchSurface Z k))
    (hagree :
      ∀ x, x ∈ region →
        (rawExactZABDecisionListBitFamily Z r k zfeat).decode c.1 x =
          G.predict i x) :
    region.sum (fun x => μ x) ≤ q := by
  exact
    (rawExactZABDecisionListBitFamily Z r k zfeat).regionMass_le_of_badCode_agrees_on
      (target := G.predict i) (h.agreement_le i) c region hagree

/-- Exact-ZAB recovery localizes the bad-code obligation: any finite region
whose mass is above the advertised agreement threshold must contain a
positive-mass point where the bad code disagrees with the target. -/
theorem ExactZABERMRecoveryData.exists_pos_mass_disagreement_in_region_of_badCode
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (i : Index)
    (c :
      (rawExactZABDecisionListBitFamily Z r k zfeat).toEncodedFamily.BadCodes
        (G.predict i))
    (region : Finset (ExactVisiblePostSwitchSurface Z k))
    (hmass : q < region.sum (fun x => μ x)) :
    ∃ x, x ∈ region ∧ μ x ≠ 0 ∧
      (rawExactZABDecisionListBitFamily Z r k zfeat).decode c.1 x ≠
        G.predict i x := by
  exact
    (rawExactZABDecisionListBitFamily Z r k zfeat).exists_pos_mass_disagreement_in_region_of_badCodeAgreementBound_lt_mass
      (target := G.predict i) (h.agreement_le i) c region hmass

/-- Therefore exact-ZAB recovery is impossible when one bad code agrees on a
finite region whose sampling mass already exceeds the advertised threshold. -/
theorem not_ExactZABERMRecoveryData_of_badCode_agrees_on_region_gt
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (i : Index)
    (c :
      (rawExactZABDecisionListBitFamily Z r k zfeat).toEncodedFamily.BadCodes
        (G.predict i))
    (region : Finset (ExactVisiblePostSwitchSurface Z k))
    (hagree :
      ∀ x, x ∈ region →
        (rawExactZABDecisionListBitFamily Z r k zfeat).decode c.1 x =
          G.predict i x)
    (hmass : q < region.sum (fun x => μ x)) :
    ¬ Nonempty (ExactZABERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ zfeat G q) := by
  rintro ⟨h⟩
  exact not_le_of_gt hmass
    (h.regionMass_le_of_badCode_agrees_on i c region hagree)

/-- A finite region on which one exact-ZAB bad code agrees also forces a
positive lower bound on the corresponding IID deceptive-sample mass. -/
theorem exactZAB_regionMass_pow_le_deceptiveSampleMass_of_badCode_agrees_on
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (i : Index)
    (c :
      (rawExactZABDecisionListBitFamily Z r k zfeat).toEncodedFamily.BadCodes
        (G.predict i))
    (region : Finset (ExactVisiblePostSwitchSurface Z k))
    (hagree :
      ∀ x, x ∈ region →
        (rawExactZABDecisionListBitFamily Z r k zfeat).decode c.1 x =
          G.predict i x)
    (m : ℕ) :
    region.sum (fun x => μ x) ^ m ≤
      (rawExactZABDecisionListBitFamily Z r k zfeat).toEncodedFamily.deceptiveSampleMass
        μ (G.predict i) m := by
  exact
    (rawExactZABDecisionListBitFamily Z r k zfeat).regionMass_pow_le_deceptiveSampleMass_of_badCode_agrees_on
      (target := G.predict i) c region hagree m

/-- The canonical ERM interface has the same atomic bad-code obstruction. -/
theorem not_CanonicalZABERMRecoveryData_of_pure_badCode_agrees
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞} {x : ExactVisiblePostSwitchSurface Z k}
    (i : Index)
    (c :
      (rawExactZABDecisionListBitFamily Z r k zfeat).toEncodedFamily.BadCodes
        (G.predict i))
    (hagree :
      (rawExactZABDecisionListBitFamily Z r k zfeat).decode c.1 x =
        G.predict i x)
    (hq_lt : q < 1) :
    ¬ Nonempty (CanonicalZABERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index)
        (PMF.pure x) zfeat G q) := by
  rintro ⟨h⟩
  exact
    ((rawExactZABDecisionListBitFamily Z r k zfeat).not_badCodeAgreementBound_pure_of_agrees
      (x := x) (target := G.predict i) (q := q) c hagree hq_lt) (h.agreement_le i)

end ExactZABAtomicBadCodeAgreement

section BitVecZABAtomicBadCodeAgreement

variable {r k : ℕ} {Index : Type*}

/-- Identity-`z` bit-vector ZAB recovery also fails under a strict pure-atom
bound as soon as a bad code agrees at the atom. -/
theorem not_BitVecZABERMRecoveryData_of_pure_badCode_agrees
    {G : ExactVisibleSwitchedFamily (BitVec r) k Index}
    {q : ℝ≥0∞} {x : ExactVisiblePostSwitchSurface (BitVec r) k}
    (i : Index)
    (c :
      (rawExactZABDecisionListBitFamily
        (BitVec r) r k identityZExtractor).toEncodedFamily.BadCodes
        (G.predict i))
    (hagree :
      (rawExactZABDecisionListBitFamily
        (BitVec r) r k identityZExtractor).decode c.1 x =
        G.predict i x)
    (hq_lt : q < 1) :
    ¬ Nonempty (BitVecZABERMRecoveryData
        (r := r) (k := k) (Index := Index) (PMF.pure x) G q) := by
  rintro ⟨h⟩
  exact
    ((rawExactZABDecisionListBitFamily
        (BitVec r) r k identityZExtractor).not_badCodeAgreementBound_pure_of_agrees
      (x := x) (target := G.predict i) (q := q) c hagree hq_lt) (h.agreement_le i)

end BitVecZABAtomicBadCodeAgreement

end Mettapedia.Computability.PNP
