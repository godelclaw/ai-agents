import FourColor.Curriculum.Actual.SupportReduction
import FourColor.Curriculum.Actual.SevenVertexSeventeenProfileThreeTwoTwo

namespace FourColor.Curriculum.Actual

section IncidenceBranch

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- In the seven-vertex `|E| = 16` branch, every degree is one of `4`, `5`, or `6`.

Source: new theorem from the local lower bound `degree ≥ 4` together with the trivial upper bound
`degree ≤ 6` on seven vertices. -/
theorem IsIncidenceCriticalNonColorable.degree_eq_four_or_five_or_six_of_card_eq_seven_of_card_edgeFinset_eq_sixteen
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (_hedge : G.edgeFinset.card = 16) (v : V) :
    G.degree v = 4 ∨ G.degree v = 5 ∨ G.degree v = 6 := by
  have hge4 : 4 ≤ G.degree v := h.four_le_degree v
  have hle6 : G.degree v ≤ 6 := h.degree_le_six_of_card_eq_seven hcard v
  omega

/-- Exact degree-count split in the seven-vertex `|E| = 16` branch.

Source: new theorem from handshaking with all degrees constrained to lie in `{4,5,6}`. The three
integer solutions are the exact profiles that remain in the exact seven-vertex frontier. -/
theorem IsIncidenceCriticalNonColorable.degree_count_case_split_of_card_eq_seven_of_card_edgeFinset_eq_sixteen
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 16) :
    let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
    let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
    let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
    (d4 = 3 ∧ d5 = 4 ∧ d6 = 0) ∨
      (d4 = 4 ∧ d5 = 2 ∧ d6 = 1) ∨
      (d4 = 5 ∧ d5 = 0 ∧ d6 = 2) := by
  classical
  let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
  let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
  let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
  have hcount :
      d4 + d5 + d6 = 7 := by
    have hsum :
        Finset.sum Finset.univ (fun v : V =>
          (if G.degree v = 4 then 1 else 0) +
            (if G.degree v = 5 then 1 else 0) +
              (if G.degree v = 6 then 1 else 0)) = 7 := by
      calc
        Finset.sum Finset.univ (fun v : V =>
          (if G.degree v = 4 then 1 else 0) +
            (if G.degree v = 5 then 1 else 0) +
              (if G.degree v = 6 then 1 else 0))
            = Finset.sum Finset.univ (fun _ : V => 1) := by
                refine Finset.sum_congr rfl ?_
                intro v hv
                rcases h.degree_eq_four_or_five_or_six_of_card_eq_seven_of_card_edgeFinset_eq_sixteen
                    hcard hedge v with h4v | h5v | h6v
                · simp [h4v]
                · simp [h5v]
                · simp [h6v]
        _ = 7 := by simp [Finset.card_univ, hcard]
    have hcount4 :
        Finset.sum Finset.univ (fun v : V => if G.degree v = 4 then 1 else 0) = d4 := by
      simp [d4]
    have hcount5 :
        Finset.sum Finset.univ (fun v : V => if G.degree v = 5 then 1 else 0) = d5 := by
      simp [d5]
    have hcount6 :
        Finset.sum Finset.univ (fun v : V => if G.degree v = 6 then 1 else 0) = d6 := by
      simp [d6]
    calc
      d4 + d5 + d6
          = (Finset.sum Finset.univ (fun v : V => if G.degree v = 4 then 1 else 0) +
              Finset.sum Finset.univ (fun v : V => if G.degree v = 5 then 1 else 0) +
                Finset.sum Finset.univ (fun v : V => if G.degree v = 6 then 1 else 0)) := by
                  rw [hcount4, hcount5, hcount6]
      _ = 7 := by
            rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
            simpa [add_assoc] using hsum
  have hweighted :
      4 * d4 + 5 * d5 + 6 * d6 = 32 := by
    have hcount4 :
        Finset.sum Finset.univ (fun v : V => if G.degree v = 4 then 1 else 0) = d4 := by
      simp [d4]
    have hcount5 :
        Finset.sum Finset.univ (fun v : V => if G.degree v = 5 then 1 else 0) = d5 := by
      simp [d5]
    have hcount6 :
        Finset.sum Finset.univ (fun v : V => if G.degree v = 6 then 1 else 0) = d6 := by
      simp [d6]
    have hsum :
        Finset.sum Finset.univ (fun v : V =>
          (if G.degree v = 4 then 4 else 0) +
            (if G.degree v = 5 then 5 else 0) +
              (if G.degree v = 6 then 6 else 0)) = 32 := by
      calc
        Finset.sum Finset.univ (fun v : V =>
          (if G.degree v = 4 then 4 else 0) +
            (if G.degree v = 5 then 5 else 0) +
              (if G.degree v = 6 then 6 else 0))
            = Finset.sum Finset.univ (fun v : V => G.degree v) := by
                refine Finset.sum_congr rfl ?_
                intro v hv
                rcases h.degree_eq_four_or_five_or_six_of_card_eq_seven_of_card_edgeFinset_eq_sixteen
                    hcard hedge v with h4v | h5v | h6v
                · simp [h4v]
                · simp [h5v]
                · simp [h6v]
        _ = 2 * G.edgeFinset.card := by simpa using G.sum_degrees_eq_twice_card_edges
        _ = 32 := by rw [hedge]
    have hd4 :
        Finset.sum Finset.univ (fun v : V => if G.degree v = 4 then 4 else 0) = 4 * d4 := by
      calc
        Finset.sum Finset.univ (fun v : V => if G.degree v = 4 then 4 else 0)
            = 4 * Finset.sum Finset.univ (fun v : V => if G.degree v = 4 then 1 else 0) := by
                symm
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl ?_
                intro v hv
                by_cases hdeg : G.degree v = 4 <;> simp [hdeg]
        _ = 4 * d4 := by rw [hcount4]
    have hd5 :
        Finset.sum Finset.univ (fun v : V => if G.degree v = 5 then 5 else 0) = 5 * d5 := by
      calc
        Finset.sum Finset.univ (fun v : V => if G.degree v = 5 then 5 else 0)
            = 5 * Finset.sum Finset.univ (fun v : V => if G.degree v = 5 then 1 else 0) := by
                symm
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl ?_
                intro v hv
                by_cases hdeg : G.degree v = 5 <;> simp [hdeg]
        _ = 5 * d5 := by rw [hcount5]
    have hd6 :
        Finset.sum Finset.univ (fun v : V => if G.degree v = 6 then 6 else 0) = 6 * d6 := by
      calc
        Finset.sum Finset.univ (fun v : V => if G.degree v = 6 then 6 else 0)
            = 6 * Finset.sum Finset.univ (fun v : V => if G.degree v = 6 then 1 else 0) := by
                symm
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl ?_
                intro v hv
                by_cases hdeg : G.degree v = 6 <;> simp [hdeg]
        _ = 6 * d6 := by rw [hcount6]
    calc
      4 * d4 + 5 * d5 + 6 * d6
          = (Finset.sum Finset.univ (fun v : V => if G.degree v = 4 then 4 else 0) +
              Finset.sum Finset.univ (fun v : V => if G.degree v = 5 then 5 else 0) +
                Finset.sum Finset.univ (fun v : V => if G.degree v = 6 then 6 else 0)) := by
                  rw [hd4, hd5, hd6]
      _ = 32 := by
            rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
            simpa [add_assoc] using hsum
  have hcases :
      (d4 = 3 ∧ d5 = 4 ∧ d6 = 0) ∨
        (d4 = 4 ∧ d5 = 2 ∧ d6 = 1) ∨
        (d4 = 5 ∧ d5 = 0 ∧ d6 = 2) := by
    omega
  simpa [d4, d5, d6] using hcases

/-- In the seven-vertex `|E| = 16` branch, some vertex has degree `4`.

Source: new corollary of the exact degree-count split. -/
theorem IsIncidenceCriticalNonColorable.exists_degree_eq_four_of_card_eq_seven_of_card_edgeFinset_eq_sixteen
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 16) :
    ∃ v : V, G.degree v = 4 := by
  classical
  rcases h.degree_count_case_split_of_card_eq_seven_of_card_edgeFinset_eq_sixteen hcard hedge with
    hcase | hcase | hcase
  all_goals
    rcases hcase with ⟨hd4, _, _⟩
    let s : Finset V := Finset.univ.filter fun v : V => G.degree v = 4
    have hs : s.card ≠ 0 := by
      simp [s, hd4]
    rcases Finset.card_ne_zero.mp hs with ⟨v, hv⟩
    refine ⟨v, ?_⟩
    exact (Finset.mem_filter.mp hv).2

/-- Exact degree-count split in the live seven-vertex `K₅`-free incidence-critical branch.

Source: the exact seven-vertex frontier now has `|E| = 16`, so the previous `16`-edge
degree-count split becomes the current live case split. -/
theorem IsIncidenceCriticalNonColorable.degree_count_case_split_of_card_eq_seven_of_cliqueFree
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
    let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
    let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
    (d4 = 3 ∧ d5 = 4 ∧ d6 = 0) ∨
      (d4 = 4 ∧ d5 = 2 ∧ d6 = 1) ∨
      (d4 = 5 ∧ d5 = 0 ∧ d6 = 2) := by
  have hedge : G.edgeFinset.card = 16 :=
    h.card_edgeFinset_eq_sixteen_of_card_eq_seven_of_cliqueFree hcard hfree
  exact h.degree_count_case_split_of_card_eq_seven_of_card_edgeFinset_eq_sixteen hcard hedge

/-- In the live seven-vertex `K₅`-free incidence-critical branch, some vertex has degree `4`. -/
theorem IsIncidenceCriticalNonColorable.exists_degree_eq_four_of_card_eq_seven_of_cliqueFree
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    ∃ v : V, G.degree v = 4 := by
  have hedge : G.edgeFinset.card = 16 :=
    h.card_edgeFinset_eq_sixteen_of_card_eq_seven_of_cliqueFree hcard hfree
  exact h.exists_degree_eq_four_of_card_eq_seven_of_card_edgeFinset_eq_sixteen hcard hedge

end IncidenceBranch

section VertexBridge

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Vertex-critical lift of the seven-vertex `16`-edge degree-count split. -/
theorem IsVertexCriticalNonColorable.degree_count_case_split_of_card_eq_seven_of_card_edgeFinset_eq_sixteen
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 16) :
    let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
    let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
    let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
    (d4 = 3 ∧ d5 = 4 ∧ d6 = 0) ∨
      (d4 = 4 ∧ d5 = 2 ∧ d6 = 1) ∨
      (d4 = 5 ∧ d5 = 0 ∧ d6 = 2) :=
  h.toIncidenceCritical_four.degree_count_case_split_of_card_eq_seven_of_card_edgeFinset_eq_sixteen
    hcard hedge

/-- Vertex-critical lift of the seven-vertex `16`-edge degree-`4` existence theorem. -/
theorem IsVertexCriticalNonColorable.exists_degree_eq_four_of_card_eq_seven_of_card_edgeFinset_eq_sixteen
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 16) :
    ∃ v : V, G.degree v = 4 :=
  h.toIncidenceCritical_four.exists_degree_eq_four_of_card_eq_seven_of_card_edgeFinset_eq_sixteen
    hcard hedge

/-- Vertex-critical lift of the live seven-vertex `K₅`-free degree-count split. -/
theorem IsVertexCriticalNonColorable.degree_count_case_split_of_card_eq_seven_of_cliqueFree
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
    let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
    let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
    (d4 = 3 ∧ d5 = 4 ∧ d6 = 0) ∨
      (d4 = 4 ∧ d5 = 2 ∧ d6 = 1) ∨
      (d4 = 5 ∧ d5 = 0 ∧ d6 = 2) :=
  h.toIncidenceCritical_four.degree_count_case_split_of_card_eq_seven_of_cliqueFree hcard hfree

/-- Vertex-critical lift of the live seven-vertex `K₅`-free degree-`4` existence theorem. -/
theorem IsVertexCriticalNonColorable.exists_degree_eq_four_of_card_eq_seven_of_cliqueFree
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    ∃ v : V, G.degree v = 4 :=
  h.toIncidenceCritical_four.exists_degree_eq_four_of_card_eq_seven_of_cliqueFree hcard hfree

end VertexBridge

section MinimalBridge

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Minimal-counterexample lift of the seven-vertex `16`-edge degree-count split. -/
theorem IsMinimalNonColorable.degree_count_case_split_of_card_eq_seven_of_card_edgeFinset_eq_sixteen_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 16) :
    let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
    let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
    let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
    (d4 = 3 ∧ d5 = 4 ∧ d6 = 0) ∨
      (d4 = 4 ∧ d5 = 2 ∧ d6 = 1) ∨
      (d4 = 5 ∧ d5 = 0 ∧ d6 = 2) :=
  (h.toIncidenceCritical hadj).degree_count_case_split_of_card_eq_seven_of_card_edgeFinset_eq_sixteen
    hcard hedge

/-- Minimal-counterexample lift of the seven-vertex `16`-edge degree-`4` existence theorem. -/
theorem IsMinimalNonColorable.exists_degree_eq_four_of_card_eq_seven_of_card_edgeFinset_eq_sixteen_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 16) :
    ∃ v : V, G.degree v = 4 :=
  (h.toIncidenceCritical hadj).exists_degree_eq_four_of_card_eq_seven_of_card_edgeFinset_eq_sixteen
    hcard hedge

/-- Minimal-counterexample lift of the live seven-vertex `K₅`-free degree-count split. -/
theorem IsMinimalNonColorable.degree_count_case_split_of_card_eq_seven_of_cliqueFree_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
    let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
    let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
    (d4 = 3 ∧ d5 = 4 ∧ d6 = 0) ∨
      (d4 = 4 ∧ d5 = 2 ∧ d6 = 1) ∨
      (d4 = 5 ∧ d5 = 0 ∧ d6 = 2) :=
  (h.toIncidenceCritical hadj).degree_count_case_split_of_card_eq_seven_of_cliqueFree hcard hfree

/-- Minimal-counterexample lift of the live seven-vertex `K₅`-free degree-`4` existence theorem. -/
theorem IsMinimalNonColorable.exists_degree_eq_four_of_card_eq_seven_of_cliqueFree_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    ∃ v : V, G.degree v = 4 :=
  (h.toIncidenceCritical hadj).exists_degree_eq_four_of_card_eq_seven_of_cliqueFree hcard hfree

/-- Minimal-counterexample lift of the live seven-vertex `K₅`-free degree-count split without a
separate no-isolated-vertices hypothesis. -/
theorem IsMinimalNonColorable.degree_count_case_split_of_card_eq_seven_of_cliqueFree
    (h : IsMinimalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    let d4 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 4).card
    let d5 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 5).card
    let d6 : ℕ := (Finset.univ.filter fun v : V => G.degree v = 6).card
    (d4 = 3 ∧ d5 = 4 ∧ d6 = 0) ∨
      (d4 = 4 ∧ d5 = 2 ∧ d6 = 1) ∨
      (d4 = 5 ∧ d5 = 0 ∧ d6 = 2) := by
  let hadj : ∀ v : V, ∃ w, G.Adj v w :=
    h.forall_exists_adj_of_card_eq_seven_of_cliqueFree hcard hfree
  let hinc : IsIncidenceCriticalNonColorable G 4 := h.toIncidenceCritical hadj
  exact
    hinc.degree_count_case_split_of_card_eq_seven_of_cliqueFree hcard hfree

/-- Minimal-counterexample lift of the live seven-vertex `K₅`-free degree-`4` existence theorem
without a separate no-isolated-vertices hypothesis. -/
theorem IsMinimalNonColorable.exists_degree_eq_four_of_card_eq_seven_of_cliqueFree
    (h : IsMinimalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    ∃ v : V, G.degree v = 4 := by
  let hadj : ∀ v : V, ∃ w, G.Adj v w :=
    h.forall_exists_adj_of_card_eq_seven_of_cliqueFree hcard hfree
  let hinc : IsIncidenceCriticalNonColorable G 4 := h.toIncidenceCritical hadj
  exact
    hinc.exists_degree_eq_four_of_card_eq_seven_of_cliqueFree hcard hfree

end MinimalBridge

end FourColor.Curriculum.Actual
