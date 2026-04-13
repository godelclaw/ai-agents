import Mathlib.Combinatorics.SimpleGraph.Maps
import FourColor.Curriculum.Actual.CriticalSynthesis
import FourColor.Curriculum.Actual.SixVertexExclusion

namespace FourColor.Curriculum.Actual

namespace SimpleGraph

section SupportLemmas

variable {V : Type*}
variable {G H : SimpleGraph V} [DecidableRel G.Adj]

/-- Re-embedding the support-induced graph back into the ambient vertex type recovers the original
graph, because isolated vertices contribute no edges.

Source: new support-reduction lemma via edge-finset extensionality. -/
theorem map_induce_support_eq_self (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.induce G.support).map (Function.Embedding.subtype G.support) = G := by
  ext v w
  constructor
  · rintro ⟨v', w', hvw, rfl, rfl⟩
    exact hvw
  · intro hvw
    refine ⟨⟨v, (SimpleGraph.mem_support (G := G)).2 ⟨w, hvw⟩⟩,
      ⟨w, (SimpleGraph.mem_support (G := G)).2 ⟨v, hvw.symm⟩⟩, hvw, rfl, rfl⟩

section FiniteSupport

variable [Fintype V] [DecidableEq V]

/-- On positive color counts, coloring the support-induced graph is equivalent to coloring the
ambient graph.

Source: new support-reduction theorem combining the induced-subgraph pullback with
`map_induce_support_eq_self`. -/
theorem colorable_iff_colorable_induce_support {n : ℕ} [NeZero n] :
    G.Colorable n ↔ (G.induce G.support).Colorable n := by
  classical
  letI : Fintype G.support := Fintype.ofFinite G.support
  constructor
  · intro hG
    exact SimpleGraph.Colorable.of_hom (f := (SimpleGraph.Embedding.induce (G := G) G.support).toHom) hG
  · intro hS
    have hmap :
        ((G.induce G.support).map (Function.Embedding.subtype G.support)).Colorable n :=
      SimpleGraph.Colorable.map (f := Function.Embedding.subtype G.support) hS
    simpa [map_induce_support_eq_self (G := G)] using hmap

end FiniteSupport

/-- Every vertex of the support-induced graph has a neighbor.

Source: new support-reduction lemma unpacking the definition of support. -/
theorem induce_support_forall_exists_adj (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∀ v : G.support, ∃ w : G.support, (G.induce G.support).Adj v w := by
  intro v
  rcases v.property with ⟨w, hvw⟩
  refine ⟨⟨w, ?_⟩, hvw⟩
  exact (SimpleGraph.mem_support (G := G)).2 ⟨v, hvw.symm⟩

end SupportLemmas

end SimpleGraph

section MinimalExtraction

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Any finite non-`n`-colorable graph contains an edge-minimal non-`n`-colorable spanning
subgraph on the same vertex type.

Source: new finite extraction lemma by minimizing `edgeFinset.card`. -/
theorem exists_minimalNonColorable_le (G : SimpleGraph V) {n : ℕ} (hG : ¬ G.Colorable n) :
    ∃ H : SimpleGraph V, H ≤ G ∧ IsMinimalNonColorable H n := by
  classical
  let P : ℕ → Prop := fun m =>
    ∃ H : SimpleGraph V, H ≤ G ∧ ¬ H.Colorable n ∧ H.edgeFinset.card = m
  have hP : ∃ m, P m := ⟨G.edgeFinset.card, ⟨G, le_rfl, hG, rfl⟩⟩
  rcases Nat.find_spec hP with ⟨H, hHG, hHnot, hHcard⟩
  refine ⟨H, hHG, hHnot, ?_⟩
  intro J hJ
  by_contra hJnot
  have hJG : J ≤ G := le_trans (le_of_lt hJ) hHG
  have hJmin : Nat.find hP ≤ J.edgeFinset.card := by
    apply Nat.find_min' hP
    exact ⟨J, hJG, hJnot, rfl⟩
  have hlt : J.edgeFinset.card < H.edgeFinset.card := by
    exact Finset.card_lt_card ((SimpleGraph.edgeFinset_ssubset_edgeFinset).2 hJ)
  have hle : H.edgeFinset.card ≤ J.edgeFinset.card := by
    simpa [hHcard] using hJmin
  exact (Nat.not_lt_of_ge hle) hlt

end MinimalExtraction

namespace IsMinimalNonColorable

section InduceSupport

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {n : ℕ} [NeZero n]

/-- Edge-minimal non-colorability passes to the support-induced graph.

Source: new support-reduction theorem obtained by mapping strict subgraphs of the support-induced
graph back to strict subgraphs of the ambient graph. -/
theorem induce_support (h : IsMinimalNonColorable G n) :
    IsMinimalNonColorable (G.induce G.support) n := by
  classical
  letI : Fintype G.support := Fintype.ofFinite G.support
  refine ⟨?_, ?_⟩
  · intro hcol
    exact h.not_colorable ((SimpleGraph.colorable_iff_colorable_induce_support (G := G)).2 hcol)
  · intro H hH
    let f : G.support ↪ V := Function.Embedding.subtype G.support
    let H' : SimpleGraph V := H.spanningCoe
    have hH'lt : H' < G := by
      have hmaple : H' ≤ (G.induce G.support).spanningCoe := by
        simpa [H', SimpleGraph.spanningCoe] using
          (SimpleGraph.map_monotone f) (le_of_lt hH)
      have hmapne : H' ≠ (G.induce G.support).spanningCoe := by
        intro hEq
        apply hH.ne
        exact (SimpleGraph.map_injective f) (by simpa [H', SimpleGraph.spanningCoe] using hEq)
      have hlt : H' < (G.induce G.support).spanningCoe := lt_of_le_of_ne hmaple hmapne
      have hEq : (G.induce G.support).spanningCoe = G := by
        simpa [SimpleGraph.spanningCoe] using
          (SimpleGraph.map_induce_support_eq_self (G := G))
      exact hEq ▸ hlt
    have hcolH' : H'.Colorable n := h.colorable_of_lt hH'lt
    exact SimpleGraph.Colorable.of_hom (SimpleGraph.Embedding.spanningCoe H).toHom hcolH'

end InduceSupport

section SmallSupportColoring

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A `K₅`-free graph whose support has size at most six is `4`-colorable.

Source: new finite reduction: pass to the support, extract a minimal non-colorable core, reduce to
its full-support induced graph, and invoke the five-vertex and six-vertex exclusions. -/
theorem colorable_four_of_cliqueFree_and_card_support_le_six
    (hfree : G.CliqueFree 5) (hsupp : Fintype.card G.support ≤ 6) :
    G.Colorable 4 := by
  classical
  by_contra hnot
  let S : SimpleGraph G.support := G.induce G.support
  have hfreeS : S.CliqueFree 5 := by
    exact SimpleGraph.CliqueFree.comap (SimpleGraph.Embedding.induce (G := G) G.support) hfree
  have hnotS : ¬ S.Colorable 4 := by
    rw [← SimpleGraph.colorable_iff_colorable_induce_support (G := G)]
    exact hnot
  rcases exists_minimalNonColorable_le (G := S) hnotS with ⟨H, hHS, hminH⟩
  let K : SimpleGraph H.support := H.induce H.support
  have hminK : IsMinimalNonColorable K 4 := hminH.induce_support
  have hcardK : Fintype.card H.support ≤ 6 := by
    let finj : H.support ↪ G.support :=
      ⟨fun v => v.1, fun _ _ hEq => Subtype.ext hEq⟩
    exact le_trans (Fintype.card_le_of_injective finj finj.injective) hsupp
  have hfreeH : H.CliqueFree 5 := SimpleGraph.CliqueFree.anti hHS hfreeS
  have hfreeK : K.CliqueFree 5 := by
    exact SimpleGraph.CliqueFree.comap (SimpleGraph.Embedding.induce (G := H) H.support) hfreeH
  have hadjK : ∀ v : H.support, ∃ w, K.Adj v w :=
    SimpleGraph.induce_support_forall_exists_adj H
  have hnonemptyK : Nonempty H.support := by
    by_contra hempty
    haveI : IsEmpty H.support := not_nonempty_iff.mp hempty
    exact hminK.not_colorable (SimpleGraph.colorable_of_isEmpty K 4)
  letI : Nonempty H.support := hnonemptyK
  have hge5 : 5 ≤ Fintype.card H.support := by
    exact hminK.card_verts_ge_five_of_forall_exists_adj hadjK
  have hcardK_cases : Fintype.card H.support = 5 ∨ Fintype.card H.support = 6 := by
    omega
  rcases hcardK_cases with h5 | h6
  · exact
      (hminK.not_cliqueFree_five_of_card_eq_five_and_forall_exists_adj hadjK h5) hfreeK
  · exact
      (hminK.not_cliqueFree_six_of_card_eq_six_and_forall_exists_adj hadjK h6) hfreeK

/-- On the seven-vertex `K₅`-free frontier, edge-minimal non-`4`-colorability forces every vertex
to have a neighbor.

Source: new support-size contradiction using `colorable_four_of_cliqueFree_and_card_support_le_six`.
-/
theorem forall_exists_adj_of_card_eq_seven_of_cliqueFree
    (h : IsMinimalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    ∀ v : V, ∃ w, G.Adj v w := by
  intro v
  by_contra hv
  have hvnot : v ∉ G.support := by
    simpa [SimpleGraph.mem_support] using hv
  have hsub : G.support ⊆ ({v} : Set V)ᶜ := by
    intro w hw
    simp [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hEq
    exact hvnot (hEq ▸ hw)
  let s : Set V := ({v} : Set V)ᶜ
  let finj : G.support ↪ s :=
    ⟨fun w => ⟨w, hsub w.property⟩, fun x y hEq => by
      apply Subtype.ext
      simpa using congrArg Subtype.val hEq⟩
  have hsupp_le_compl : Fintype.card G.support ≤ Fintype.card s :=
    Fintype.card_le_of_injective finj finj.injective
  have hcard_compl : Fintype.card s = 6 := by
    simpa [s, hcard] using (Fintype.card_compl_set ({v} : Set V))
  have hsupp : Fintype.card G.support ≤ 6 := by
    rwa [hcard_compl] at hsupp_le_compl
  exact h.not_colorable (colorable_four_of_cliqueFree_and_card_support_le_six hfree hsupp)

end SmallSupportColoring

end IsMinimalNonColorable

end FourColor.Curriculum.Actual
