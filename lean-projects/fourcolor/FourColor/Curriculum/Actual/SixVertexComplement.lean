import Mathlib.Combinatorics.SimpleGraph.Matching
import FourColor.Curriculum.Actual.SixVertexCaseSplit

namespace FourColor.Curriculum.Actual

section IncidenceBranch

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- In the six-vertex `K₅`-free `|E| = 12` branch, the complement is `1`-regular.

Source: new theorem from the exact `4`-regularity of the original graph together with Mathlib's
complement-regularity theorem. -/
theorem IsIncidenceCriticalNonColorable.compl_isRegularOfDegree_one_of_card_edgeFinset_eq_twelve
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 6) (hfree : G.CliqueFree 5)
    (hedge : G.edgeFinset.card = 12) :
    Gᶜ.IsRegularOfDegree 1 := by
  have hreg : G.IsRegularOfDegree 4 := fun v =>
    h.degree_eq_four_of_card_edgeFinset_eq_twelve hcard hfree hedge v
  simpa [hcard] using (SimpleGraph.IsRegularOfDegree.compl (G := G) (k := 4) hreg)

/-- In the six-vertex `K₅`-free `|E| = 12` branch, the full complement graph is a perfect
matching.

Source: new theorem from the complement `1`-regularity classification and Mathlib's perfect
matching criterion `isPerfectMatching_iff_forall_degree`. -/
theorem IsIncidenceCriticalNonColorable.compl_top_isPerfectMatching_of_card_edgeFinset_eq_twelve
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 6) (hfree : G.CliqueFree 5)
    (hedge : G.edgeFinset.card = 12) :
    (⊤ : SimpleGraph.Subgraph Gᶜ).IsPerfectMatching := by
  letI : DecidableRel (⊤ : SimpleGraph.Subgraph Gᶜ).Adj := by
    intro v w
    change Decidable (Gᶜ.Adj v w)
    infer_instance
  letI : ∀ v : V, Fintype ↑((⊤ : SimpleGraph.Subgraph Gᶜ).neighborSet v) := fun v =>
    SimpleGraph.Subgraph.finiteAt
      (G := Gᶜ) (G' := (⊤ : SimpleGraph.Subgraph Gᶜ)) ⟨v, by simp⟩
  letI : ∀ v : V, Fintype ↑((⊤ : SimpleGraph.Subgraph Gᶜ).spanningCoe.neighborSet v) := fun v =>
    by simpa [SimpleGraph.Subgraph.spanningCoe_top] using
      (inferInstance : Fintype ↑(Gᶜ.neighborSet v))
  refine (SimpleGraph.Subgraph.isPerfectMatching_iff
    (M := (⊤ : SimpleGraph.Subgraph Gᶜ))).2 ?_
  intro v
  have hdeg : Gᶜ.degree v = 1 := by
    rw [SimpleGraph.degree_compl]
    simp [hcard, h.degree_eq_four_of_card_edgeFinset_eq_twelve hcard hfree hedge v]
  have hsubdeg : (⊤ : SimpleGraph.Subgraph Gᶜ).degree v = 1 := by
    rw [← SimpleGraph.Subgraph.degree_spanningCoe
        (G' := (⊤ : SimpleGraph.Subgraph Gᶜ)) (v := v)]
    simpa [SimpleGraph.Subgraph.spanningCoe_top] using hdeg
  exact (SimpleGraph.Subgraph.degree_eq_one_iff_unique_adj
    (G' := (⊤ : SimpleGraph.Subgraph Gᶜ)) (v := v)).mp hsubdeg

/-- In the six-vertex `K₅`-free `|E| = 13` branch, the complement has two isolated vertices and
every other vertex has complement-degree `1`.

Source: new theorem from the exact degree profile of the original graph plus Mathlib's complement
degree formula. -/
theorem IsIncidenceCriticalNonColorable.exists_distinct_compl_degree_eq_zero_forall_compl_degree_eq_one_of_card_edgeFinset_eq_thirteen
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 6) (hfree : G.CliqueFree 5)
    (hedge : G.edgeFinset.card = 13) :
    ∃ u v : V, u ≠ v ∧ Gᶜ.degree u = 0 ∧ Gᶜ.degree v = 0 ∧
      ∀ w : V, w ≠ u → w ≠ v → Gᶜ.degree w = 1 := by
  rcases h.exists_distinct_degree_eq_five_forall_degree_eq_four_else_of_card_edgeFinset_eq_thirteen
      hcard hfree hedge with ⟨u, v, huv, hu5, hv5, hrest⟩
  refine ⟨u, v, huv, ?_, ?_, ?_⟩
  · simpa [hcard, hu5] using (SimpleGraph.degree_compl (G := G) (v := u))
  · simpa [hcard, hv5] using (SimpleGraph.degree_compl (G := G) (v := v))
  · intro w hwu hwv
    simpa [hcard, hrest w hwu hwv] using (SimpleGraph.degree_compl (G := G) (v := w))

/-- In the six-vertex `K₅`-free `|E| = 13` branch, the complement restricted to its support is a
perfect matching.

Source: new theorem from the exact complement degree profile together with support-restriction
preserving positive degrees. -/
theorem IsIncidenceCriticalNonColorable.compl_induce_support_top_isPerfectMatching_of_card_edgeFinset_eq_thirteen
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 6) (hfree : G.CliqueFree 5)
    (hedge : G.edgeFinset.card = 13) :
    (⊤ : SimpleGraph.Subgraph ((Gᶜ).induce (Gᶜ.support))).IsPerfectMatching := by
  rcases h.exists_distinct_compl_degree_eq_zero_forall_compl_degree_eq_one_of_card_edgeFinset_eq_thirteen
      hcard hfree hedge with ⟨u, v, huv, hu0, hv0, hrest⟩
  have hu_not_mem : u ∉ Gᶜ.support := by
    exact (SimpleGraph.degree_eq_zero_iff_notMem_support (G := Gᶜ) (v := u)).mp hu0
  have hv_not_mem : v ∉ Gᶜ.support := by
    exact (SimpleGraph.degree_eq_zero_iff_notMem_support (G := Gᶜ) (v := v)).mp hv0
  letI : DecidableRel (⊤ : SimpleGraph.Subgraph ((Gᶜ).induce (Gᶜ.support))).Adj := by
    intro a b
    change Decidable (((Gᶜ).induce (Gᶜ.support)).Adj a b)
    infer_instance
  letI : ∀ w : Gᶜ.support,
      Fintype ↑((⊤ : SimpleGraph.Subgraph ((Gᶜ).induce (Gᶜ.support))).neighborSet w) := fun w =>
    SimpleGraph.Subgraph.finiteAt
      (G := (Gᶜ).induce (Gᶜ.support))
      (G' := (⊤ : SimpleGraph.Subgraph ((Gᶜ).induce (Gᶜ.support)))) ⟨w, by simp⟩
  letI : ∀ w : Gᶜ.support,
      Fintype ↑((⊤ : SimpleGraph.Subgraph ((Gᶜ).induce (Gᶜ.support))).spanningCoe.neighborSet w) :=
    fun w => by
      simpa [SimpleGraph.Subgraph.spanningCoe_top] using
        (inferInstance : Fintype ↑(((Gᶜ).induce (Gᶜ.support)).neighborSet w))
  refine (SimpleGraph.Subgraph.isPerfectMatching_iff
    (M := (⊤ : SimpleGraph.Subgraph ((Gᶜ).induce (Gᶜ.support))))).2 ?_
  intro w
  have hdeg : ((Gᶜ).induce (Gᶜ.support)).degree w = 1 := by
    rw [SimpleGraph.degree_induce_support]
    have hwu : (w : V) ≠ u := by
      intro hwu
      exact hu_not_mem (hwu ▸ w.property)
    have hwv : (w : V) ≠ v := by
      intro hwv
      exact hv_not_mem (hwv ▸ w.property)
    exact hrest w hwu hwv
  have hsubdeg :
      (⊤ : SimpleGraph.Subgraph ((Gᶜ).induce (Gᶜ.support))).degree w = 1 := by
    rw [← SimpleGraph.Subgraph.degree_spanningCoe
        (G' := (⊤ : SimpleGraph.Subgraph ((Gᶜ).induce (Gᶜ.support)))) (v := w)]
    simpa [SimpleGraph.Subgraph.spanningCoe_top] using hdeg
  exact (SimpleGraph.Subgraph.degree_eq_one_iff_unique_adj
    (G' := (⊤ : SimpleGraph.Subgraph ((Gᶜ).induce (Gᶜ.support)))) (v := w)).mp hsubdeg

/-- Refined six-vertex `K₅`-free complement case split for incidence-critical non-4-colorable
graphs.

Source: new theorem combining the exact six-vertex case split with the corresponding complement
structure in each branch. -/
theorem IsIncidenceCriticalNonColorable.six_vertex_compl_case_split_of_cliqueFree
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 6) (hfree : G.CliqueFree 5) :
    (G.edgeFinset.card = 12 ∧ Gᶜ.IsRegularOfDegree 1) ∨
    (G.edgeFinset.card = 13 ∧
      ∃ u v : V, u ≠ v ∧ Gᶜ.degree u = 0 ∧ Gᶜ.degree v = 0 ∧
        ∀ w : V, w ≠ u → w ≠ v → Gᶜ.degree w = 1) := by
  rcases h.six_vertex_edge_degree_case_split_refined_of_cliqueFree hcard hfree with h12 | h13
  · refine Or.inl ⟨h12.1, ?_⟩
    exact h.compl_isRegularOfDegree_one_of_card_edgeFinset_eq_twelve hcard hfree h12.1
  · refine Or.inr ⟨h13.1, ?_⟩
    exact h.exists_distinct_compl_degree_eq_zero_forall_compl_degree_eq_one_of_card_edgeFinset_eq_thirteen
      hcard hfree h13.1

/-- Refined six-vertex `K₅`-free complement case split in matching form for incidence-critical
non-4-colorable graphs.

Source: new theorem packaging the exact six-vertex branch as a dichotomy between a perfect
matching on the full complement and a perfect matching on the complement support. -/
theorem IsIncidenceCriticalNonColorable.six_vertex_compl_matching_case_split_of_cliqueFree
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 6) (hfree : G.CliqueFree 5) :
    (G.edgeFinset.card = 12 ∧ (⊤ : SimpleGraph.Subgraph Gᶜ).IsPerfectMatching) ∨
    (G.edgeFinset.card = 13 ∧
      (⊤ : SimpleGraph.Subgraph ((Gᶜ).induce (Gᶜ.support))).IsPerfectMatching) := by
  rcases h.six_vertex_edge_degree_case_split_refined_of_cliqueFree hcard hfree with h12 | h13
  · refine Or.inl ⟨h12.1, ?_⟩
    exact h.compl_top_isPerfectMatching_of_card_edgeFinset_eq_twelve hcard hfree h12.1
  · refine Or.inr ⟨h13.1, ?_⟩
    exact h.compl_induce_support_top_isPerfectMatching_of_card_edgeFinset_eq_thirteen
      hcard hfree h13.1

end IncidenceBranch

end FourColor.Curriculum.Actual
