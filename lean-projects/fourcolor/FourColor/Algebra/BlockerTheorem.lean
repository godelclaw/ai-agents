import FourColor.Triangulation

/-!
# Naive Run-Completion Blocker

The canonical proof source `4cp_proof_v23.pdf` explicitly warns that naive
additivity is not valid for mixed color pairs. This file isolates one concrete
failure mode.

Suppose a face-boundary run `R` is completed in two ways, using complementary
interior arcs `A` and `A'`, and one models the two corresponding chains by the
indicator chains of `R ∪ A` and `R ∪ A'`. The pointwise `chainXor` of those
two chains is not the indicator of `R`; the common run cancels, leaving only
the complementary interior arcs.

This explains why the current proof route must use the polarized boundary
generators of Section 4.2 together with the operator execution layer of
Section 8, rather than a direct run-by-run additivity principle.
-/

namespace FourColor

section RunCompletion

variable {ι : Type*} [DecidableEq ι]

/-- A run together with two disjoint complementary interior completion arcs. -/
structure NaiveRunCompletion (ι : Type*) [DecidableEq ι] where
  run : Finset ι
  leftArc : Finset ι
  rightArc : Finset ι
  run_left_disjoint : Disjoint run leftArc
  run_right_disjoint : Disjoint run rightArc
  left_right_disjoint : Disjoint leftArc rightArc
  leftArc_nonempty : leftArc.Nonempty

namespace NaiveRunCompletion

/-- The interior support left after cancelling the common run. -/
def interior (D : NaiveRunCompletion ι) : Finset ι :=
  D.leftArc ∪ D.rightArc

/-- The naive pre-switch chain `γ · 1_{R ∪ A}`. -/
def before (D : NaiveRunCompletion ι) (γ : Color) : ι → Color :=
  indicatorChain γ (D.run ∪ D.leftArc)

/-- The naive post-switch chain `γ · 1_{R ∪ A'}`. -/
def after (D : NaiveRunCompletion ι) (γ : Color) : ι → Color :=
  indicatorChain γ (D.run ∪ D.rightArc)

@[simp] lemma not_mem_leftArc_of_mem_run (D : NaiveRunCompletion ι) {e : ι}
    (he : e ∈ D.run) : e ∉ D.leftArc := by
  exact fun hleft => Finset.disjoint_left.mp D.run_left_disjoint he hleft

@[simp] lemma not_mem_rightArc_of_mem_run (D : NaiveRunCompletion ι) {e : ι}
    (he : e ∈ D.run) : e ∉ D.rightArc := by
  exact fun hright => Finset.disjoint_left.mp D.run_right_disjoint he hright

@[simp] lemma not_mem_run_of_mem_leftArc (D : NaiveRunCompletion ι) {e : ι}
    (he : e ∈ D.leftArc) : e ∉ D.run := by
  exact fun hrun => Finset.disjoint_left.mp D.run_left_disjoint hrun he

@[simp] lemma not_mem_run_of_mem_rightArc (D : NaiveRunCompletion ι) {e : ι}
    (he : e ∈ D.rightArc) : e ∉ D.run := by
  exact fun hrun => Finset.disjoint_left.mp D.run_right_disjoint hrun he

@[simp] lemma not_mem_rightArc_of_mem_leftArc (D : NaiveRunCompletion ι) {e : ι}
    (he : e ∈ D.leftArc) : e ∉ D.rightArc := by
  exact fun hright => Finset.disjoint_left.mp D.left_right_disjoint he hright

@[simp] lemma not_mem_leftArc_of_mem_rightArc (D : NaiveRunCompletion ι) {e : ι}
    (he : e ∈ D.rightArc) : e ∉ D.leftArc := by
  exact fun hleft => Finset.disjoint_left.mp D.left_right_disjoint hleft he

@[simp] lemma not_mem_interior_of_mem_run (D : NaiveRunCompletion ι) {e : ι}
    (he : e ∈ D.run) : e ∉ D.interior := by
  simp [interior, D.not_mem_leftArc_of_mem_run he, D.not_mem_rightArc_of_mem_run he]

@[simp] lemma mem_interior_of_mem_leftArc (D : NaiveRunCompletion ι) {e : ι}
    (he : e ∈ D.leftArc) : e ∈ D.interior := by
  simp [interior, he]

@[simp] lemma mem_interior_of_mem_rightArc (D : NaiveRunCompletion ι) {e : ι}
    (he : e ∈ D.rightArc) : e ∈ D.interior := by
  simp [interior, he]

@[simp] lemma color_neg_eq_self (γ : Color) : -γ = γ := by
  rcases γ with ⟨γ₁, γ₂⟩
  ext <;> simp

/-- Pointwise form of the cancellation calculation. -/
lemma chainXor_before_after_apply (D : NaiveRunCompletion ι) (γ : Color) (e : ι) :
    chainXor (D.before γ) (D.after γ) e = if e ∈ D.interior then γ else 0 := by
  by_cases hrun : e ∈ D.run
  · have hleft : e ∉ D.leftArc := D.not_mem_leftArc_of_mem_run hrun
    have hright : e ∉ D.rightArc := D.not_mem_rightArc_of_mem_run hrun
    simp [before, after, interior, chainXor, indicatorChain, hrun, hleft, hright,
      color_neg_eq_self, color_add_self]
  · by_cases hleft : e ∈ D.leftArc
    · have hrun' : e ∉ D.run := D.not_mem_run_of_mem_leftArc hleft
      have hright : e ∉ D.rightArc := D.not_mem_rightArc_of_mem_leftArc hleft
      simp [before, after, interior, chainXor, indicatorChain, hrun', hleft, hright]
    · by_cases hright : e ∈ D.rightArc
      · have hrun' : e ∉ D.run := D.not_mem_run_of_mem_rightArc hright
        have hleft' : e ∉ D.leftArc := D.not_mem_leftArc_of_mem_rightArc hright
        simp [before, after, interior, chainXor, indicatorChain, hrun', hleft', hright,
          color_neg_eq_self]
      · simp [before, after, interior, chainXor, indicatorChain, hrun, hleft, hright]

/-- The common run cancels, leaving only the complementary interior arcs. -/
theorem chainXor_before_after_eq_indicator_interior
    (D : NaiveRunCompletion ι) (γ : Color) :
    chainXor (D.before γ) (D.after γ) = indicatorChain γ D.interior := by
  funext e
  simpa [indicatorChain] using D.chainXor_before_after_apply γ e

end NaiveRunCompletion

/-- Main single-run obstruction: the naive completed-run `chainXor` is interior
support, not run support. -/
theorem per_run_xor_is_interior (D : NaiveRunCompletion ι) (γ : Color) :
    chainXor (D.before γ) (D.after γ) = indicatorChain γ D.interior :=
  D.chainXor_before_after_eq_indicator_interior γ

/-- On the run itself, the naive per-run `chainXor` always vanishes. -/
theorem per_run_xor_zero_on_run (D : NaiveRunCompletion ι) (γ : Color)
    {e : ι} (he : e ∈ D.run) :
    chainXor (D.before γ) (D.after γ) e = 0 := by
  rw [per_run_xor_is_interior]
  simp [indicatorChain, D.not_mem_interior_of_mem_run he]

/-- The naive completed-run model cannot produce the run indicator unless
`γ = 0`. -/
theorem paper_claim_impossible (D : NaiveRunCompletion ι) (γ : Color) (hγ : γ ≠ 0) :
    chainXor (D.before γ) (D.after γ) ≠ indicatorChain γ D.run := by
  intro hEq
  obtain ⟨e, he⟩ := D.leftArc_nonempty
  have hLhs : chainXor (D.before γ) (D.after γ) e = γ := by
    rw [per_run_xor_is_interior]
    simp [indicatorChain, D.mem_interior_of_mem_leftArc he]
  have he_not_run : e ∉ D.run := D.not_mem_run_of_mem_leftArc he
  have hRhs : indicatorChain γ D.run e = 0 := by
    simp [indicatorChain, he_not_run]
  have : γ = 0 := by
    calc
      γ = chainXor (D.before γ) (D.after γ) e := hLhs.symm
      _ = indicatorChain γ D.run e := congrFun hEq e
      _ = 0 := hRhs
  exact hγ this

/-- The singleton partition on one run. This packages the minimal interface
expected by `FaceRunPartition.SwitchData`. -/
def singletonRunPartition (R : Finset ι) : FaceRunPartition ι where
  runs := {R}
  boundary := R
  subset_boundary := by
    intro S hS
    have hEq : S = R := Finset.mem_singleton.mp hS
    subst hEq
    exact subset_rfl
  cover_boundary := by
    intro e he
    refine ⟨R, ?_, ?_⟩
    · exact ⟨Finset.mem_singleton_self R, he⟩
    · intro S hS
      exact Finset.mem_singleton.mp hS.1

/-- The existing `FaceRunPartition.SwitchData` interface cannot be instantiated
from the naive completed-run chains, even in the one-run case. -/
theorem no_switchdata_from_naive_completion
    (D : NaiveRunCompletion ι) (γ : Color) (hγ : γ ≠ 0) :
    ¬ ∃ S : FaceRunPartition.SwitchData (singletonRunPartition D.run),
      S.γ = γ ∧
      S.base = D.before γ ∧
      S.switched (R := D.run) (by simp [singletonRunPartition]) = D.after γ := by
  intro h
  rcases h with ⟨S, hSγ, hSbase, hSswitched⟩
  have hRun :
      chainXor S.base (S.switched (R := D.run) (by simp [singletonRunPartition])) =
        indicatorChain S.γ D.run := by
    simpa [singletonRunPartition] using
      S.run_chain (R := D.run) (by simp [singletonRunPartition])
  rw [hSγ, hSbase, hSswitched] at hRun
  exact paper_claim_impossible D γ hγ hRun

end RunCompletion

end FourColor
