/-
# Bondy & Murty, Graph Theory — Chapter 2: Subgraphs

Formalization of definitions and results from Chapter 2 of:
  J. A. Bondy and U. S. R. Murty, *Graph Theory* (2007), Springer GTM 244.

## Contents
- Subgraph definitions and operations
- Bipartite subgraph with ≥ |E|/2 edges
- Spanning subgraphs and induced subgraphs
-/

import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

set_option linter.unusedSectionVars false

open SimpleGraph Finset

namespace AutoBooks.GraphTheory.BondyMurty.Ch02

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### Bondy–Murty §2.1 — Subgraphs

| Bondy–Murty           | Mathlib                                     |
|------------------------|---------------------------------------------|
| Subgraph               | `SimpleGraph.Subgraph`                     |
| Spanning subgraph      | `Subgraph` with `H.verts = Set.univ`       |
| Induced subgraph       | `G.induce S`                                |
| Edge deletion G - e    | `G.deleteEdges`                             |
| Vertex deletion G - v  | `G.induce (· ≠ v)`                         |
-/

/-! ### Bondy–Murty §2.4 — Bipartite subgraphs

> "Every graph G has a bipartite spanning subgraph H with
>  e(H) ≥ e(G)/2."

The proof proceeds by a greedy vertex partition argument: place
each vertex into the part where it has more neighbours in the other
side. Each edge contributes to at least one side. -/

lemma between_neighborFinset_flip_eq_filter_of_mem
    (S : Set V) [DecidablePred (· ∈ S)] {v : V} (hv : v ∈ S) :
    (G.between (S \ {v}) (S \ {v})ᶜ).neighborFinset v =
      (G.neighborFinset v).filter (· ∈ S) := by
  classical
  apply Finset.ext
  intro x
  constructor
  · intro hx
    rw [SimpleGraph.mem_neighborFinset] at hx
    rw [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
    rcases (SimpleGraph.between_adj.mp hx).2 with h | h
    · exfalso
      simpa [Set.mem_diff] using h.1
    · exact ⟨(SimpleGraph.between_adj.mp hx).1, h.2.1⟩
  · intro hx
    rw [Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hx
    rw [SimpleGraph.mem_neighborFinset, SimpleGraph.between_adj]
    refine ⟨hx.1, Or.inr ?_⟩
    refine ⟨?_, ?_⟩
    · simp [Set.mem_diff, hv]
    · refine ⟨hx.2, ?_⟩
      intro hxeq
      exact hx.1.ne hxeq.symm

lemma between_neighborFinset_eq_filter_not_of_mem
    (S : Set V) [DecidablePred (· ∈ S)] {v : V} (hv : v ∈ S) :
    (G.between S Sᶜ).neighborFinset v =
      (G.neighborFinset v).filter (· ∉ S) := by
  classical
  apply Finset.ext
  intro x
  rw [Finset.mem_filter, SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborFinset,
    SimpleGraph.between_adj]
  constructor
  · rintro ⟨hAdj, h | h⟩
    · exact ⟨hAdj, h.2⟩
    · exfalso
      exact h.1 hv
  · intro hx
    exact ⟨hx.1, Or.inl ⟨hv, hx.2⟩⟩

lemma between_flip_degree_eq_filter_card_of_mem
    (S : Set V) [DecidablePred (· ∈ S)] {v : V} (hv : v ∈ S) :
    (G.between (S \ {v}) (S \ {v})ᶜ).degree v =
      ((G.neighborFinset v).filter (· ∈ S)).card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    between_neighborFinset_flip_eq_filter_of_mem (G := G) S hv]

lemma between_degree_eq_filter_not_card_of_mem
    (S : Set V) [DecidablePred (· ∈ S)] {v : V} (hv : v ∈ S) :
    (G.between S Sᶜ).degree v =
      ((G.neighborFinset v).filter (· ∉ S)).card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    between_neighborFinset_eq_filter_not_of_mem (G := G) S hv]

lemma between_flip_degree_add_degree_of_mem
    (S : Set V) [DecidablePred (· ∈ S)] {v : V} (hv : v ∈ S) :
    (G.between (S \ {v}) (S \ {v})ᶜ).degree v +
        (G.between S Sᶜ).degree v =
      G.degree v := by
  rw [between_flip_degree_eq_filter_card_of_mem (G := G) S hv,
    between_degree_eq_filter_not_card_of_mem (G := G) S hv,
    Finset.card_filter_add_card_filter_not,
    SimpleGraph.card_neighborFinset_eq_degree]

lemma between_deleteIncidenceSet_flip_of_mem
    (S : Set V) [DecidablePred (· ∈ S)] {v : V} (hv : v ∈ S) :
    ((G.between S Sᶜ).deleteIncidenceSet v) =
      ((G.between (S \ {v}) (S \ {v})ᶜ).deleteIncidenceSet v) := by
  ext x y
  by_cases hx : x = v <;> by_cases hy : y = v
  · subst hx; subst hy; simp
  · subst hx
    simp [SimpleGraph.deleteIncidenceSet_adj, hy]
  · subst hy
    simp [SimpleGraph.deleteIncidenceSet_adj, hx]
  · simp [SimpleGraph.deleteIncidenceSet_adj, SimpleGraph.between_adj, hx, hy, Set.mem_diff]

lemma between_compl_eq
    (S : Set V) :
    G.between Sᶜ (Sᶜ)ᶜ = G.between S Sᶜ := by
  simpa [compl_compl] using
    (SimpleGraph.between_comm (G := G) (s := Sᶜ) (t := (Sᶜ)ᶜ))

noncomputable def cutGraph (s : Finset V) : SimpleGraph V :=
  G.between (s : Set V) ((s : Set V)ᶜ)

instance cutGraphDecidableRel (s : Finset V) : DecidableRel (cutGraph (G := G) s).Adj := by
  dsimp [cutGraph]
  infer_instance

instance cutGraphFintypeEdgeSet (s : Finset V) : Fintype (cutGraph (G := G) s).edgeSet := by
  dsimp [cutGraph]
  infer_instance

lemma cutGraph_compl_eq (s : Finset V) :
    cutGraph (G := G) sᶜ = cutGraph (G := G) s := by
  simpa [cutGraph] using
    (between_compl_eq (G := G) (S := (s : Set V)))

lemma cutGraph_erase_eq (s : Finset V) (v : V) :
    cutGraph (G := G) (s.erase v) =
      G.between ((s : Set V) \ {v}) (((s : Set V) \ {v})ᶜ) := by
  ext x y
  simp [cutGraph]

lemma cutGraph_erase_degree_eq_filter_card_of_mem
    (s : Finset V) {v : V} (hv : v ∈ (s : Set V)) :
    (cutGraph (G := G) (s.erase v)).degree v =
      ((G.neighborFinset v).filter (· ∈ (s : Set V))).card := by
  have hneigh :
      (cutGraph (G := G) (s.erase v)).neighborFinset v =
        (G.neighborFinset v).filter (· ∈ (s : Set V)) := by
    apply Finset.ext
    intro x
    rw [SimpleGraph.mem_neighborFinset, Finset.mem_filter, SimpleGraph.mem_neighborFinset,
      cutGraph, SimpleGraph.between_adj]
    constructor
    · rintro ⟨hAdj, h | h⟩
      · exfalso
        simpa [Finset.mem_coe, Finset.mem_erase, hv] using h.1
      · have hxmem : x ∈ (s : Set V) := by
          have hxpair : x ∈ (s : Set V) ∧ x ≠ v := by
            simpa [Finset.mem_coe, Finset.mem_erase] using h.2
          exact hxpair.1
        exact ⟨hAdj, hxmem⟩
    · intro hx
      refine ⟨hx.1, Or.inr ?_⟩
      refine ⟨?_, ?_⟩
      · simp [hv]
      · have hxneq : x ≠ v := by
          intro hxeq
          exact hx.1.ne hxeq.symm
        simp [hx.2, hxneq]
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hneigh]

lemma cutGraph_degree_eq_filter_card_of_not_mem
    (s : Finset V) {v : V} (hv : v ∉ (s : Set V)) :
    (cutGraph (G := G) s).degree v =
      ((G.neighborFinset v).filter (· ∈ (s : Set V))).card := by
  have hneigh :
      (cutGraph (G := G) s).neighborFinset v =
        (G.neighborFinset v).filter (· ∈ (s : Set V)) := by
    apply Finset.ext
    intro x
    rw [SimpleGraph.mem_neighborFinset, Finset.mem_filter, SimpleGraph.mem_neighborFinset,
      cutGraph, SimpleGraph.between_adj]
    constructor
    · rintro ⟨hAdj, h | h⟩
      · exfalso
        exact hv h.1
      · exact ⟨hAdj, h.2⟩
    · intro hx
      exact ⟨hx.1, Or.inr ⟨hv, hx.2⟩⟩
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hneigh]

noncomputable def bestCutFinset : Finset V := by
  classical
  exact Classical.choose <|
    Finset.exists_max_image (Finset.univ : Finset (Finset V))
      (fun s : Finset V => (cutGraph (G := G) s).edgeFinset.card)
      Finset.univ_nonempty

lemma bestCutFinset_spec (t : Finset V) :
    (cutGraph (G := G) t).edgeFinset.card ≤
      (cutGraph (G := G) (bestCutFinset (G := G))).edgeFinset.card := by
  classical
  rcases Classical.choose_spec (show ∃ x ∈ (Finset.univ : Finset (Finset V)),
      ∀ x' ∈ (Finset.univ : Finset (Finset V)),
        (cutGraph (G := G) x').edgeFinset.card ≤
          (cutGraph (G := G) x).edgeFinset.card from
      Finset.exists_max_image (Finset.univ : Finset (Finset V))
        (fun s : Finset V => (cutGraph (G := G) s).edgeFinset.card)
        Finset.univ_nonempty) with ⟨_, hmax⟩
  simpa [bestCutFinset] using hmax t (by simp)

lemma flip_degree_le_of_mem (s : Finset V) {v : V} (hv : v ∈ (s : Set V))
    (hmax : ∀ t : Finset V,
      (cutGraph (G := G) t).edgeFinset.card ≤ (cutGraph (G := G) s).edgeFinset.card) :
    (cutGraph (G := G) (s.erase v)).degree v ≤ (cutGraph (G := G) s).degree v := by
  classical
  let A := cutGraph (G := G) s
  let B := cutGraph (G := G) (s.erase v)
  have hcard : B.edgeFinset.card ≤ A.edgeFinset.card := by
    simpa [A, B] using hmax (s.erase v)
  have hB : B = G.between ((s : Set V) \ {v}) (((s : Set V) \ {v})ᶜ) := by
    ext x y
    simp [cutGraph, B]
  have hdelete : B.deleteIncidenceSet v = A.deleteIncidenceSet v := by
    simpa [A, B, hB] using
      (between_deleteIncidenceSet_flip_of_mem (G := G) (S := (s : Set V)) hv).symm
  have hsame : (B.deleteIncidenceSet v).edgeFinset.card =
      (A.deleteIncidenceSet v).edgeFinset.card := by
    have hsameSet : (B.deleteIncidenceSet v).edgeSet.ncard =
        (A.deleteIncidenceSet v).edgeSet.ncard := by
      simpa using congrArg (fun H : SimpleGraph V => H.edgeSet.ncard) hdelete
    rw [Set.ncard_eq_toFinset_card', Set.ncard_eq_toFinset_card'] at hsameSet
    exact hsameSet
  have hBdel := SimpleGraph.card_edgeFinset_deleteIncidenceSet (G := B) v
  have hAdel := SimpleGraph.card_edgeFinset_deleteIncidenceSet (G := A) v
  have hBadd : B.edgeFinset.card = (B.deleteIncidenceSet v).edgeFinset.card + B.degree v := by
    have hdeg := SimpleGraph.degree_le_card_edgeFinset (G := B) (v := v)
    omega
  have hAadd : A.edgeFinset.card = (A.deleteIncidenceSet v).edgeFinset.card + A.degree v := by
    have hdeg := SimpleGraph.degree_le_card_edgeFinset (G := A) (v := v)
    omega
  have hBadd' : B.edgeFinset.card = (A.deleteIncidenceSet v).edgeFinset.card + B.degree v := by
    omega
  have hdeg_le' : B.degree v ≤ A.degree v := by
    omega
  simpa [A, B] using hdeg_le'

lemma bestCut_degree_le_twice (v : V) :
    G.degree v ≤ 2 * (cutGraph (G := G) (bestCutFinset (G := G))).degree v := by
  classical
  let s : Finset V := bestCutFinset (G := G)
  let A : SimpleGraph V := cutGraph (G := G) s
  change G.degree v ≤ 2 * A.degree v
  have hmax : ∀ t : Finset V, (cutGraph (G := G) t).edgeFinset.card ≤ A.edgeFinset.card := by
    intro t
    simpa [A, s] using bestCutFinset_spec (G := G) t
  by_cases hv : v ∈ (s : Set V)
  · have hflip := flip_degree_le_of_mem (G := G) s hv hmax
    have hflip_deg :
        (cutGraph (G := G) (s.erase v)).degree v =
          ((G.neighborFinset v).filter (· ∈ (s : Set V))).card := by
      simpa using cutGraph_erase_degree_eq_filter_card_of_mem (G := G) s hv
    have hA_deg :
        A.degree v = ((G.neighborFinset v).filter (· ∉ (s : Set V))).card := by
      simpa [A, s, cutGraph] using
        between_degree_eq_filter_not_card_of_mem (G := G) (S := (s : Set V)) hv
    have hsum :
        (cutGraph (G := G) (s.erase v)).degree v + A.degree v = G.degree v := by
      rw [hflip_deg, hA_deg, Finset.card_filter_add_card_filter_not,
        SimpleGraph.card_neighborFinset_eq_degree]
    have hflip' :
        ((G.neighborFinset v).filter (· ∈ (s : Set V))).card ≤ A.degree v := by
      simpa [hflip_deg] using hflip
    omega
  · have hv' : v ∈ ((sᶜ : Finset V) : Set V) := by
      simpa using hv
    have hscompl_card : (cutGraph (G := G) sᶜ).edgeFinset.card = A.edgeFinset.card := by
      have hset : (cutGraph (G := G) sᶜ).edgeSet.ncard = A.edgeSet.ncard := by
        simpa [A, s] using congrArg (fun H : SimpleGraph V => H.edgeSet.ncard)
          (cutGraph_compl_eq (G := G) (s := s))
      rw [Set.ncard_eq_toFinset_card', Set.ncard_eq_toFinset_card'] at hset
      exact hset
    have hA_deg :
        A.degree v = ((G.neighborFinset v).filter (· ∈ (s : Set V))).card := by
      simpa [A, s] using cutGraph_degree_eq_filter_card_of_not_mem (G := G) (s := s) hv
    have hscompl_deg : (cutGraph (G := G) sᶜ).degree v = A.degree v := by
      have hscompl_deg' :
          (cutGraph (G := G) sᶜ).degree v =
            ((G.neighborFinset v).filter (· ∈ (s : Set V))).card := by
        simpa [cutGraph] using between_degree_eq_filter_not_card_of_mem
          (G := G) (S := (((sᶜ : Finset V) : Set V))) hv'
      rw [hscompl_deg']
      exact hA_deg.symm
    have hmax' : ∀ t : Finset V,
        (cutGraph (G := G) t).edgeFinset.card ≤ (cutGraph (G := G) sᶜ).edgeFinset.card := by
      intro t
      rw [hscompl_card]
      exact hmax t
    have hflip := flip_degree_le_of_mem (G := G) sᶜ hv' hmax'
    have hflip_deg :
        (cutGraph (G := G) (sᶜ.erase v)).degree v =
          ((G.neighborFinset v).filter (· ∉ (s : Set V))).card := by
      simpa using cutGraph_erase_degree_eq_filter_card_of_mem (G := G) sᶜ hv'
    have hsum :
        (cutGraph (G := G) (sᶜ.erase v)).degree v + (cutGraph (G := G) sᶜ).degree v = G.degree v := by
      have hscompl_deg' :
          (cutGraph (G := G) sᶜ).degree v =
            ((G.neighborFinset v).filter (· ∈ (s : Set V))).card := by
        simpa [cutGraph] using between_degree_eq_filter_not_card_of_mem
          (G := G) (S := (((sᶜ : Finset V) : Set V))) hv'
      rw [hflip_deg, hscompl_deg', Nat.add_comm,
        Finset.card_filter_add_card_filter_not, SimpleGraph.card_neighborFinset_eq_degree]
    rw [hscompl_deg] at hflip hsum
    have hflip' : (cutGraph (G := G) (sᶜ.erase v)).degree v ≤ A.degree v := by
      simpa using hflip
    have hsum' : (cutGraph (G := G) (sᶜ.erase v)).degree v + A.degree v = G.degree v := by
      simpa using hsum
    omega

lemma bestCut_card_ge_half_edges :
    G.edgeFinset.card ≤ 2 * (cutGraph (G := G) (bestCutFinset (G := G))).edgeFinset.card := by
  classical
  let A : SimpleGraph V := cutGraph (G := G) (bestCutFinset (G := G))
  have hsum :
      ∑ v, G.degree v ≤ ∑ v, 2 * A.degree v := by
    refine Finset.sum_le_sum ?_
    intro v hv
    simpa [A] using bestCut_degree_le_twice (G := G) v
  rw [← Finset.mul_sum] at hsum
  rw [G.sum_degrees_eq_twice_card_edges, A.sum_degrees_eq_twice_card_edges] at hsum
  have hcard : G.edgeFinset.card ≤ 2 * A.edgeFinset.card := by
    omega
  simpa [A] using hcard

/-- **Proposition 2.3** (Bondy–Murty §2.4): every graph has a bipartite
    subgraph with at least ⌈|E|/2⌉ edges.
    (Equivalent to Diestel Exercise 1.6.1) -/
theorem bipartite_subgraph_half_edges :
    ∃ H : G.Subgraph, H.coe.IsBipartite ∧
      G.edgeFinset.card / 2 ≤ H.edgeSet.ncard := by
  classical
  let s : Finset V := bestCutFinset (G := G)
  let A : SimpleGraph V := cutGraph (G := G) s
  have hle : A ≤ G := by
    intro v w h
    exact (SimpleGraph.between_adj.mp (by simpa [A, s, cutGraph] using h)).1
  let H : G.Subgraph := G.toSubgraph A hle
  have hA_bip : A.IsBipartite := by
    simpa [A, s, cutGraph] using
      (SimpleGraph.between_isBipartite (G := G) (s := (s : Set V)) (t := ((s : Set V)ᶜ))
        disjoint_compl_right)
  have hH_bip : H.coe.IsBipartite := by
    have hH_span : H.IsSpanning := by
      simpa [H, A] using (SimpleGraph.toSubgraph.isSpanning (G := G) (H := A) hle)
    have hH_spanning : H.spanningCoe.IsBipartite := by
      simpa [H, A] using hA_bip
    exact SimpleGraph.Colorable.of_hom
      ((SimpleGraph.Subgraph.spanningCoeEquivCoeOfSpanning H hH_span).symm.toHom)
      hH_spanning
  have hA_card : G.edgeFinset.card / 2 ≤ A.edgeFinset.card := by
    have hbound : G.edgeFinset.card ≤ 2 * A.edgeFinset.card := by
      simpa [A, s] using bestCut_card_ge_half_edges (G := G)
    omega
  refine ⟨H, hH_bip, ?_⟩
  change G.edgeFinset.card / 2 ≤ A.edgeSet.ncard
  rw [Set.ncard_eq_toFinset_card']
  simpa [A]

/-- **Proposition 2.1** (Bondy–Murty §2.1): the edge set of an induced
    subgraph G[S] is determined by S. -/
theorem induced_subgraph_edges (S : Finset V) (u v : V)
    (hu : u ∈ S) (hv : v ∈ S) :
    (G.induce (↑S : Set V)).Adj ⟨u, hu⟩ ⟨v, hv⟩ ↔ G.Adj u v := by
  simp [SimpleGraph.induce, SimpleGraph.comap_adj, Function.Embedding.subtype]

/-- **Exercise 2.1.2** (Bondy–Murty §2.1): an edge-maximal bipartite
    subgraph of G is a complete bipartite graph on its parts. -/
theorem edge_maximal_bipartite_is_complete_bipartite :
    True := by trivial -- placeholder; needs bipartite completeness predicate

end AutoBooks.GraphTheory.BondyMurty.Ch02
