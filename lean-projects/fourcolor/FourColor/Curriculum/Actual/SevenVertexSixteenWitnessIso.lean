import Mathlib.Logic.Equiv.Set
import FourColor.Curriculum.Actual.SupportReduction
import FourColor.Curriculum.Actual.SevenVertexSixteenCycleCharacterization
import FourColor.Curriculum.Actual.SevenVertexSixteenWitness

namespace FourColor.Curriculum.Actual

section Generic

variable {V : Type*} {H : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel H.Adj]

/-- Any seven-vertex graph with two isolated vertices and induced support exactly a transported
`5`-cycle is canonically the complement-side witness `2K₁ ⊔ C₅` up to isomorphism. -/
theorem nonempty_iso_sevenVertexSixteenWitnessCompl_of_card_eq_seven_of_degree_zero_zero_of_card_support_eq_five_and_induce_support_eq_cycleGraph_five
    (hcard : Fintype.card V = 7) {u v : V} (huv : u ≠ v)
    (hu0 : H.degree u = 0) (hv0 : H.degree v = 0)
    (hsupp : Fintype.card H.support = 5)
    (hcycle : ∃ e : Fin 5 ≃ H.support,
      H.induce H.support = (SimpleGraph.cycleGraph 5).map e.toEmbedding) :
    Nonempty (sevenVertexSixteenWitnessCompl ≃g H) := by
  classical
  rcases hcycle with ⟨e, hEq⟩
  have hu_not_mem : u ∉ H.support :=
    (SimpleGraph.degree_eq_zero_iff_notMem_support (G := H) (v := u)).mp hu0
  have hv_not_mem : v ∉ H.support :=
    (SimpleGraph.degree_eq_zero_iff_notMem_support (G := H) (v := v)).mp hv0
  have hsubset : H.support ⊆ ({u, v} : Set V)ᶜ := by
    intro x hx
    have hxu : x ≠ u := by
      intro hxu
      exact hu_not_mem (hxu ▸ hx)
    have hxv : x ≠ v := by
      intro hxv
      exact hv_not_mem (hxv ▸ hx)
    simp [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, hxu, hxv]
  have hsupp_ncard : H.support.ncard = 5 := by
    have hsupp_card_eq : Fintype.card H.support = H.support.ncard := by
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    simpa [hsupp_card_eq] using hsupp
  have hpair_card : Fintype.card ({u, v} : Set V) = 2 := by
    rw [← Set.toFinset_card]
    simp [huv]
  have hpair_compl_card : Fintype.card ↥((({u, v} : Set V)ᶜ)) = 5 := by
    calc
      Fintype.card ↥((({u, v} : Set V)ᶜ)) = Fintype.card V - Fintype.card ({u, v} : Set V) := by
        simpa using (Fintype.card_compl_set ({u, v} : Set V))
      _ = 7 - 2 := by rw [hcard, hpair_card]
      _ = 5 := by decide
  have hpair_compl_ncard : (({u, v} : Set V)ᶜ).ncard = 5 := by
    have hpair_compl_card_eq :
        Fintype.card ↥((({u, v} : Set V)ᶜ)) = (({u, v} : Set V)ᶜ).ncard := by
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    simpa [hpair_compl_card_eq] using hpair_compl_card
  have hsupport_eq : H.support = ({u, v} : Set V)ᶜ :=
    Set.eq_of_subset_of_ncard_le hsubset (by rw [hpair_compl_ncard, hsupp_ncard])
  let f : Fin 2 ⊕ Fin 5 → V :=
    Sum.elim (fun i : Fin 2 => if i = 0 then u else v) (fun i : Fin 5 => (e i : V))
  have hf_inl_zero : f (Sum.inl 0) = u := by
    simp [f]
  have hf_inl_one : f (Sum.inl 1) = v := by
    simp [f]
  have hf_inr (i : Fin 5) : f (Sum.inr i) = (e i : V) := by
    simp [f]
  have hf_inj : Function.Injective f := by
    intro a b hab
    cases a with
    | inl i =>
        cases b with
        | inl j =>
            fin_cases i <;> fin_cases j
            · rfl
            · exfalso
              exact huv (by simpa [f] using hab)
            · exfalso
              exact huv.symm (by simpa [f] using hab)
            · rfl
        | inr j =>
            fin_cases i
            · exfalso
              have hfj : f (Sum.inr j) ∈ H.support := by
                simpa [f] using (e j).property
              have hfu : f (Sum.inl 0) ∈ H.support := by
                rwa [← hab] at hfj
              exact hu_not_mem (by simpa [f] using hfu)
            · exfalso
              have hfj : f (Sum.inr j) ∈ H.support := by
                simpa [f] using (e j).property
              have hfv : f (Sum.inl 1) ∈ H.support := by
                rwa [← hab] at hfj
              exact hv_not_mem (by simpa [f] using hfv)
    | inr i =>
        cases b with
        | inl j =>
            fin_cases j
            · exfalso
              have hfi : f (Sum.inr i) ∈ H.support := by
                simpa [f] using (e i).property
              have hfu : f (Sum.inl 0) ∈ H.support := by
                rwa [hab] at hfi
              exact hu_not_mem (by simpa [f] using hfu)
            · exfalso
              have hfi : f (Sum.inr i) ∈ H.support := by
                simpa [f] using (e i).property
              have hfv : f (Sum.inl 1) ∈ H.support := by
                rwa [hab] at hfi
              exact hv_not_mem (by simpa [f] using hfv)
        | inr j =>
            exact congrArg Sum.inr (e.injective (Subtype.ext (by simpa [f] using hab)))
  have hf_surj : Function.Surjective f := by
    intro x
    by_cases hx : x ∈ H.support
    · rcases e.surjective ⟨x, hx⟩ with ⟨i, hi⟩
      refine ⟨Sum.inr i, ?_⟩
      exact (hf_inr i).trans (by simpa using congrArg Subtype.val hi)
    · have hxuv : x = u ∨ x = v := by
        have hxnot : x ∉ ({u, v} : Set V)ᶜ := by simpa [hsupport_eq] using hx
        have hxmem : x ∈ ({u, v} : Set V) := by
          by_contra hxmem
          exact hxnot (by simpa [Set.mem_compl_iff] using hxmem)
        simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hxmem
      rcases hxuv with rfl | rfl
      · exact ⟨Sum.inl 0, by simp [f]⟩
      · exact ⟨Sum.inl 1, by simp [f]⟩
  have hu_adj_cycle (i : Fin 5) : ¬ H.Adj u (e i : V) := by
    intro hui
    exact hu_not_mem ((SimpleGraph.mem_support (G := H)).2 ⟨(e i : V), hui⟩)
  have hv_adj_cycle (i : Fin 5) : ¬ H.Adj v (e i : V) := by
    intro hvi
    exact hv_not_mem ((SimpleGraph.mem_support (G := H)).2 ⟨(e i : V), hvi⟩)
  have hcycle_adj_u (i : Fin 5) : ¬ H.Adj (e i : V) u := by
    intro hiu
    exact hu_adj_cycle i hiu.symm
  have hcycle_adj_v (i : Fin 5) : ¬ H.Adj (e i : V) v := by
    intro hiv
    exact hv_adj_cycle i hiv.symm
  have huv_adj : ¬ H.Adj u v := by
    intro huv'
    exact hu_not_mem ((SimpleGraph.mem_support (G := H)).2 ⟨v, huv'⟩)
  have hvu_adj : ¬ H.Adj v u := by
    intro hvu'
    exact hv_not_mem ((SimpleGraph.mem_support (G := H)).2 ⟨u, hvu'⟩)
  have hcycle_adj (i j : Fin 5) :
      H.Adj (e i : V) (e j : V) ↔ (SimpleGraph.cycleGraph 5).Adj i j := by
    simpa [SimpleGraph.map_adj_apply] using
      congrArg (fun K : SimpleGraph H.support => K.Adj (e i) (e j)) hEq
  let ef : Fin 2 ⊕ Fin 5 ≃ V := Equiv.ofBijective f ⟨hf_inj, hf_surj⟩
  refine ⟨{
    toEquiv := ef
    map_rel_iff' := ?_
  }⟩
  intro a b
  change H.Adj (f a) (f b) ↔ sevenVertexSixteenWitnessCompl.Adj a b
  cases a with
  | inl i =>
      cases b with
      | inl j =>
          fin_cases i <;> fin_cases j
          · simp [sevenVertexSixteenWitnessCompl, hf_inl_zero]
          · simp [sevenVertexSixteenWitnessCompl, hf_inl_zero, hf_inl_one, huv_adj]
          · simp [sevenVertexSixteenWitnessCompl, hf_inl_zero, hf_inl_one, hvu_adj]
          · simp [sevenVertexSixteenWitnessCompl, hf_inl_one]
      | inr j =>
          fin_cases i
          · simp [sevenVertexSixteenWitnessCompl, hf_inl_zero, hf_inr, hu_adj_cycle]
          · simp [sevenVertexSixteenWitnessCompl, hf_inl_one, hf_inr, hv_adj_cycle]
  | inr i =>
      cases b with
      | inl j =>
          fin_cases j
          · simp [sevenVertexSixteenWitnessCompl, hf_inl_zero, hf_inr, hcycle_adj_u]
          · simp [sevenVertexSixteenWitnessCompl, hf_inl_one, hf_inr, hcycle_adj_v]
      | inr j =>
          simpa [sevenVertexSixteenWitnessCompl, hf_inr, SimpleGraph.map_adj_apply] using
            hcycle_adj i j

/-- The same canonical realization viewed on the original-graph side: the graph is `K₂ ⋈ C₅`
up to isomorphism. -/
theorem nonempty_iso_sevenVertexSixteenWitness_of_card_eq_seven_of_degree_zero_zero_of_card_support_eq_five_and_induce_support_eq_cycleGraph_five
    (hcard : Fintype.card V = 7) {u v : V} (huv : u ≠ v)
    (hu0 : H.degree u = 0) (hv0 : H.degree v = 0)
    (hsupp : Fintype.card H.support = 5)
    (hcycle : ∃ e : Fin 5 ≃ H.support,
      H.induce H.support = (SimpleGraph.cycleGraph 5).map e.toEmbedding) :
    Nonempty (sevenVertexSixteenWitness ≃g Hᶜ) := by
  rcases
      nonempty_iso_sevenVertexSixteenWitnessCompl_of_card_eq_seven_of_degree_zero_zero_of_card_support_eq_five_and_induce_support_eq_cycleGraph_five
        (H := H) hcard huv hu0 hv0 hsupp hcycle with
    ⟨φ⟩
  refine ⟨{
    toEquiv := φ.toEquiv
    map_rel_iff' := ?_
  }⟩
  intro a b
  obtain rfl | hab := eq_or_ne a b
  · simp [sevenVertexSixteenWitness]
  · have hφab : φ a ≠ φ b := φ.injective.ne hab
    constructor
    · intro habH
      have habNot : ¬ H.Adj (φ a) (φ b) := (SimpleGraph.compl_adj H (φ a) (φ b)).1 habH |>.2
      have habW : ¬ sevenVertexSixteenWitnessCompl.Adj a b := by
        intro habW
        exact habNot ((φ.map_adj_iff (v := a) (w := b)).2 habW)
      exact (SimpleGraph.compl_adj sevenVertexSixteenWitnessCompl a b).2 ⟨hab, habW⟩
    · intro habW
      have habNot : ¬ sevenVertexSixteenWitnessCompl.Adj a b :=
        (SimpleGraph.compl_adj sevenVertexSixteenWitnessCompl a b).1 habW |>.2
      have habH : ¬ H.Adj (φ a) (φ b) := by
        intro habH
        exact habNot ((φ.map_adj_iff (v := a) (w := b)).1 habH)
      exact (SimpleGraph.compl_adj H (φ a) (φ b)).2 ⟨hφab, habH⟩

end Generic

section IncidenceBranch

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- In the live seven-vertex `K₅`-free exact frontier, the complement is uniquely realized as the
canonical witness `2K₁ ⊔ C₅` up to isomorphism. -/
theorem IsIncidenceCriticalNonColorable.nonempty_iso_sevenVertexSixteenWitnessCompl_compl_of_card_eq_seven_of_cliqueFree
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    Nonempty (sevenVertexSixteenWitnessCompl ≃g Gᶜ) := by
  rcases h.exists_distinct_two_compl_degree_eq_zero_and_compl_support_eq_cycleGraph_five_of_card_eq_seven_of_cliqueFree
      hcard hfree with ⟨u, v, huv, hu0, hv0, e, hEq⟩
  have hsupp : Fintype.card Gᶜ.support = 5 := by
    simpa using (Fintype.card_congr e).symm
  exact
    nonempty_iso_sevenVertexSixteenWitnessCompl_of_card_eq_seven_of_degree_zero_zero_of_card_support_eq_five_and_induce_support_eq_cycleGraph_five
      (H := Gᶜ) hcard huv hu0 hv0 hsupp ⟨e, hEq⟩

/-- In the live seven-vertex `K₅`-free exact frontier, the original graph is uniquely realized as
the canonical witness `K₂ ⋈ C₅` up to isomorphism. -/
theorem IsIncidenceCriticalNonColorable.nonempty_iso_sevenVertexSixteenWitness_of_card_eq_seven_of_cliqueFree
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    Nonempty (sevenVertexSixteenWitness ≃g G) := by
  rcases h.exists_distinct_two_compl_degree_eq_zero_and_compl_support_eq_cycleGraph_five_of_card_eq_seven_of_cliqueFree
      hcard hfree with ⟨u, v, huv, hu0, hv0, e, hEq⟩
  have hsupp : Fintype.card Gᶜ.support = 5 := by
    simpa using (Fintype.card_congr e).symm
  simpa using
    nonempty_iso_sevenVertexSixteenWitness_of_card_eq_seven_of_degree_zero_zero_of_card_support_eq_five_and_induce_support_eq_cycleGraph_five
      (H := Gᶜ) hcard huv hu0 hv0 hsupp ⟨e, hEq⟩

end IncidenceBranch

section VertexBridge

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Vertex-critical lift of the canonical complement-side witness realization. -/
theorem IsVertexCriticalNonColorable.nonempty_iso_sevenVertexSixteenWitnessCompl_compl_of_card_eq_seven_of_cliqueFree
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    Nonempty (sevenVertexSixteenWitnessCompl ≃g Gᶜ) := by
  let hinc : IsIncidenceCriticalNonColorable G 4 := h.toIncidenceCritical_four
  exact
    hinc.nonempty_iso_sevenVertexSixteenWitnessCompl_compl_of_card_eq_seven_of_cliqueFree
      hcard hfree

/-- Vertex-critical lift of the canonical `K₂ ⋈ C₅` realization. -/
theorem IsVertexCriticalNonColorable.nonempty_iso_sevenVertexSixteenWitness_of_card_eq_seven_of_cliqueFree
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    Nonempty (sevenVertexSixteenWitness ≃g G) := by
  let hinc : IsIncidenceCriticalNonColorable G 4 := h.toIncidenceCritical_four
  exact
    hinc.nonempty_iso_sevenVertexSixteenWitness_of_card_eq_seven_of_cliqueFree
      hcard hfree

end VertexBridge

section MinimalBridge

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Minimal-counterexample lift of the canonical complement-side witness realization. -/
theorem IsMinimalNonColorable.nonempty_iso_sevenVertexSixteenWitnessCompl_compl_of_card_eq_seven_of_cliqueFree_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    Nonempty (sevenVertexSixteenWitnessCompl ≃g Gᶜ) := by
  let hinc : IsIncidenceCriticalNonColorable G 4 := h.toIncidenceCritical hadj
  exact
    hinc.nonempty_iso_sevenVertexSixteenWitnessCompl_compl_of_card_eq_seven_of_cliqueFree
      hcard hfree

/-- Minimal-counterexample lift of the canonical `K₂ ⋈ C₅` realization. -/
theorem IsMinimalNonColorable.nonempty_iso_sevenVertexSixteenWitness_of_card_eq_seven_of_cliqueFree_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    Nonempty (sevenVertexSixteenWitness ≃g G) := by
  let hinc : IsIncidenceCriticalNonColorable G 4 := h.toIncidenceCritical hadj
  exact
    hinc.nonempty_iso_sevenVertexSixteenWitness_of_card_eq_seven_of_cliqueFree
      hcard hfree

/-- Minimal-counterexample lift of the canonical complement-side witness realization without a
separate no-isolated-vertices hypothesis. -/
theorem IsMinimalNonColorable.nonempty_iso_sevenVertexSixteenWitnessCompl_compl_of_card_eq_seven_of_cliqueFree
    (h : IsMinimalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    Nonempty (sevenVertexSixteenWitnessCompl ≃g Gᶜ) := by
  let hadj : ∀ v : V, ∃ w, G.Adj v w :=
    h.forall_exists_adj_of_card_eq_seven_of_cliqueFree hcard hfree
  let hinc : IsIncidenceCriticalNonColorable G 4 := h.toIncidenceCritical hadj
  exact
    hinc.nonempty_iso_sevenVertexSixteenWitnessCompl_compl_of_card_eq_seven_of_cliqueFree
      hcard hfree

/-- Minimal-counterexample lift of the canonical `K₂ ⋈ C₅` realization without a separate
no-isolated-vertices hypothesis. -/
theorem IsMinimalNonColorable.nonempty_iso_sevenVertexSixteenWitness_of_card_eq_seven_of_cliqueFree
    (h : IsMinimalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    Nonempty (sevenVertexSixteenWitness ≃g G) := by
  let hadj : ∀ v : V, ∃ w, G.Adj v w :=
    h.forall_exists_adj_of_card_eq_seven_of_cliqueFree hcard hfree
  let hinc : IsIncidenceCriticalNonColorable G 4 := h.toIncidenceCritical hadj
  exact
    hinc.nonempty_iso_sevenVertexSixteenWitness_of_card_eq_seven_of_cliqueFree
      hcard hfree

end MinimalBridge

end FourColor.Curriculum.Actual
