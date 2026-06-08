import Mettapedia.GraphTheory.FourColor.ColorAlgebra

namespace Mettapedia.GraphTheory.FourColor

open Classical

variable {E : Type*} [DecidableEq E]

/-- Abstract data of one distinguished boundary run and the two complementary arcs that complete
the surrounding Kempe cycle. This models the older per-run purification surface `γ · 1_R`; it is
not the exact v23 Step 2 theorem surface, which uses the full boundary intersection `D ∩ ∂f`. -/
structure RunArcDecomposition (E : Type*) where
  run : Finset E
  leftArc : Finset E
  rightArc : Finset E
  run_left_disjoint : Disjoint run leftArc
  run_right_disjoint : Disjoint run rightArc
  left_right_disjoint : Disjoint leftArc rightArc
  leftArc_nonempty : leftArc.Nonempty
  rightArc_nonempty : rightArc.Nonempty

namespace RunArcDecomposition

/-- The interior part of the Kempe cycle decomposition, namely `A ∪ A'`. -/
def interior (D : RunArcDecomposition E) : Finset E :=
  D.leftArc ∪ D.rightArc

/-- The contribution used before the switch, supported on `R ∪ A`. -/
def before (D : RunArcDecomposition E) (γ : Color) : E → Color :=
  indicatorChain γ (D.run ∪ D.leftArc)

/-- The contribution used after the switch, supported on `R ∪ A'`. -/
def after (D : RunArcDecomposition E) (γ : Color) : E → Color :=
  indicatorChain γ (D.run ∪ D.rightArc)

lemma mem_run_of_mem_before_and_after (D : RunArcDecomposition E) {e : E}
    (hbefore : e ∈ D.run ∪ D.leftArc) (hafter : e ∈ D.run ∪ D.rightArc) :
    e ∈ D.run := by
  rcases Finset.mem_union.mp hbefore with hrun | hleft
  · exact hrun
  · rcases Finset.mem_union.mp hafter with hrun | hright
    · exact hrun
    · exact False.elim <| (Finset.disjoint_left.mp D.left_right_disjoint) hleft hright

lemma not_mem_interior_of_mem_run (D : RunArcDecomposition E) {e : E} (hrun : e ∈ D.run) :
    e ∉ D.interior := by
  intro hinterior
  rcases Finset.mem_union.mp hinterior with hleft | hright
  · exact (Finset.disjoint_left.mp D.run_left_disjoint) hrun hleft
  · exact (Finset.disjoint_left.mp D.run_right_disjoint) hrun hright

/-- The algebraic content of the older per-run purification setup: the two distinguished-run
contributions cancel on the run and survive on the complementary arcs. -/
theorem before_add_after_eq_indicator_interior (D : RunArcDecomposition E) (γ : Color) :
    D.before γ + D.after γ = indicatorChain γ D.interior := by
  funext e
  by_cases hbefore : e ∈ D.run ∪ D.leftArc
  · by_cases hafter : e ∈ D.run ∪ D.rightArc
    · have hrun : e ∈ D.run := D.mem_run_of_mem_before_and_after hbefore hafter
      have hinterior : e ∉ D.interior := D.not_mem_interior_of_mem_run hrun
      have hnoInterior : ¬ (e ∈ D.leftArc ∨ e ∈ D.rightArc) := by
        simpa [RunArcDecomposition.interior] using hinterior
      simp [RunArcDecomposition.before, RunArcDecomposition.after,
        RunArcDecomposition.interior, indicatorChain, hbefore, hafter, hnoInterior]
    · have hleft : e ∈ D.leftArc := by
        rcases Finset.mem_union.mp hbefore with hrun | hleft
        · exact False.elim <| hafter <| Finset.mem_union.mpr <| Or.inl hrun
        · exact hleft
      have hinterior : e ∈ D.interior := Finset.mem_union.mpr (Or.inl hleft)
      simp [RunArcDecomposition.before, RunArcDecomposition.after,
        RunArcDecomposition.interior, indicatorChain, hbefore, hafter, hleft]
  · by_cases hafter : e ∈ D.run ∪ D.rightArc
    · have hright : e ∈ D.rightArc := by
        rcases Finset.mem_union.mp hafter with hrun | hright
        · exact False.elim <| hbefore <| Finset.mem_union.mpr <| Or.inl hrun
        · exact hright
      have hinterior : e ∈ D.interior := Finset.mem_union.mpr (Or.inr hright)
      simp [RunArcDecomposition.before, RunArcDecomposition.after,
        RunArcDecomposition.interior, indicatorChain, hbefore, hafter, hright]
    · have hinterior : e ∉ D.interior := by
        intro hin
        rcases Finset.mem_union.mp hin with hleft | hright
        · exact hbefore <| Finset.mem_union.mpr <| Or.inr hleft
        · exact hafter <| Finset.mem_union.mpr <| Or.inr hright
      have hnoInterior : ¬ (e ∈ D.leftArc ∨ e ∈ D.rightArc) := by
        simpa [RunArcDecomposition.interior] using hinterior
      simp [RunArcDecomposition.before, RunArcDecomposition.after,
        RunArcDecomposition.interior, indicatorChain, hbefore, hafter, hnoInterior]

/-- On the run itself, the two contributions always cancel. -/
theorem before_add_after_eq_zero_on_run (D : RunArcDecomposition E) (γ : Color) {e : E}
    (hrun : e ∈ D.run) :
    (D.before γ + D.after γ) e = 0 := by
  rw [D.before_add_after_eq_indicator_interior]
  have hinterior : e ∉ D.interior := D.not_mem_interior_of_mem_run hrun
  simp [indicatorChain, hinterior]

/-- Abstract refutation of the older per-run boundary-only purification claim `γ · 1_R`.
This does not by itself refute the exact v23 Step 2 statement `c · 1_{D ∩ ∂f}`. -/
theorem goertzel_lemma43_boundary_claim_false (D : RunArcDecomposition E)
    (γ : Color) (hγ : γ ≠ 0) :
    D.before γ + D.after γ ≠ indicatorChain γ D.run := by
  intro hEq
  obtain ⟨e, he⟩ := D.leftArc_nonempty
  have hleft : (D.before γ + D.after γ) e = γ := by
    rw [D.before_add_after_eq_indicator_interior]
    have hinterior : e ∈ D.interior := Finset.mem_union.mpr (Or.inl he)
    simp [indicatorChain, hinterior]
  have hrun : indicatorChain γ D.run e = 0 := by
    have hnotrun : e ∉ D.run := by
      intro hrun
      exact (Finset.disjoint_left.mp D.run_left_disjoint) hrun he
    simp [indicatorChain, hnotrun]
  have : γ = 0 := by
    calc
      γ = (D.before γ + D.after γ) e := hleft.symm
      _ = indicatorChain γ D.run e := by simpa using congrFun hEq e
      _ = 0 := hrun
  exact hγ this

end RunArcDecomposition

end Mettapedia.GraphTheory.FourColor
