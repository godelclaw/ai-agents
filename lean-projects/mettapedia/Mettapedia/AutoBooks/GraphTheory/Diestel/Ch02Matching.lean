/-
# Diestel, Graph Theory — Chapter 2: Matching, Covering, and Packing

Formalization of definitions and results from Chapter 2 of:
  R. Diestel, *Graph Theory* (5th edition), Springer GTM 173.

We build on Mathlib's matching infrastructure from
`Mathlib.Combinatorics.SimpleGraph.Matching`.

## Contents
- Pointers to Mathlib for matchings, 1-factors
- Vertex cover
- Theorem 2.1.1 (König 1931): max matching = min vertex cover in bipartite
- Theorem 2.1.2 (Hall 1935): marriage theorem
- Theorem 2.2.1 (Tutte 1947): 1-factor characterization
-/

import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Hall
import Mathlib.Combinatorics.SimpleGraph.Tutte
import Mathlib.Combinatorics.SimpleGraph.VertexCover
import Mettapedia.AutoBooks.GraphTheory.BondyMurty.Ch16Matchings

set_option linter.unusedSectionVars false

open SimpleGraph Walk Finset

namespace AutoBooks.GraphTheory.Diestel.Ch02

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### Diestel §2.1 — Definitions

| Diestel                | Mathlib                                        |
|------------------------|------------------------------------------------|
| Matching               | `SimpleGraph.Subgraph.IsMatching`              |
| Perfect matching       | `SimpleGraph.Subgraph.IsPerfectMatching`       |
| Bipartite              | `SimpleGraph.IsBipartite`                      |
-/

/-! ### Vertex cover -/

/-- A **vertex cover** is a set U such that every edge has an endpoint in U. -/
def IsVertexCover (U : Finset V) : Prop :=
  ∀ ⦃u v⦄, G.Adj u v → u ∈ U ∨ v ∈ U

private lemma isVertexCover_toFinset
    {C : Set V} (hC : SimpleGraph.IsVertexCover G C) :
    IsVertexCover G (Set.toFinite C).toFinset := by
  intro u v hadj
  simpa using hC hadj

private lemma replaced_cover_card_lt
    {C S N : Finset V} (hS : S ⊆ C) (hNC : Disjoint N C)
    (hlt : N.card < S.card) :
    ((C \ S) ∪ N).card < C.card := by
  have hNdiff : Disjoint (C \ S) N := by
    rw [Finset.disjoint_left]
    intro x hx hxN
    exact Finset.disjoint_left.mp hNC hxN (Finset.mem_sdiff.mp hx).1
  have hSpos : 0 < S.card := by omega
  have hSNpos : 0 < S.card - N.card := by
    exact Nat.sub_pos_of_lt hlt
  have hSC : S.card ≤ C.card := Finset.card_le_card hS
  calc
    ((C \ S) ∪ N).card = (C.card - S.card) + N.card := by
      rw [Finset.card_union_of_disjoint hNdiff, card_sdiff_of_subset hS]
    _ = S.card + (C.card - S.card) - (S.card - N.card) := by
      symm
      exact Nat.add_sub_sub_cancel hlt.le
    _ = C.card - (S.card - N.card) := by
      rw [Nat.add_sub_of_le hSC]
    _ < C.card := Nat.sub_lt_self hSNpos
      (le_trans (Nat.sub_le _ _) (Finset.card_le_card hS))

private lemma replace_left_cover_isVertexCover
    {A B : Set V} [DecidablePred (· ∈ A)] (hAB : G.IsBipartiteWith A B)
    {C S : Finset V} (hC : IsVertexCover G C)
    (hS : S ⊆ C.filter fun v => v ∈ A) :
    IsVertexCover G ((C \ S) ∪
      S.biUnion (fun v =>
        (G.between (↑(C.filter fun w => w ∈ A) : Set V) ((↑C : Set V)ᶜ)).neighborFinset v)) := by
  classical
  let CA : Finset V := C.filter fun v => v ∈ A
  let H : SimpleGraph V := G.between (↑CA : Set V) ((↑C : Set V)ᶜ)
  have hS_C : S ⊆ C := by
    intro x hx
    exact (Finset.mem_filter.mp (hS hx)).1
  have hS_A : ∀ ⦃x⦄, x ∈ S → x ∈ A := by
    intro x hx
    exact (Finset.mem_filter.mp (hS hx)).2
  intro u v hadj
  by_cases huS : u ∈ S
  · have huA : u ∈ A := hS_A huS
    have hv_not_S : v ∉ S := by
      intro hvS
      have hvA : v ∈ A := hS_A hvS
      have hvB : v ∈ B := hAB.mem_of_mem_adj (v := u) (w := v) huA hadj
      exact Set.disjoint_left.mp hAB.disjoint hvA hvB
    by_cases hvC : v ∈ C
    · exact Or.inr <| Finset.mem_union_left _ <| Finset.mem_sdiff.mpr ⟨hvC, hv_not_S⟩
    · refine Or.inr ?_
      rw [Finset.mem_union]
      exact Or.inr <| Finset.mem_biUnion.mpr ⟨u, huS, by
        rw [SimpleGraph.mem_neighborFinset, SimpleGraph.between_adj]
        simpa [CA, Set.mem_compl_iff, Finset.mem_coe] using
          show G.Adj u v ∧
            (u ∈ (↑(C.filter fun w => w ∈ A) : Set V) ∧ v ∈ ((↑C : Set V)ᶜ) ∨
              u ∈ ((↑C : Set V)ᶜ) ∧ v ∈ (↑(C.filter fun w => w ∈ A) : Set V)) from
            ⟨hadj, Or.inl ⟨by simpa using hS huS, by simpa [Set.mem_compl_iff, Finset.mem_coe] using hvC⟩⟩⟩
  · by_cases hvS : v ∈ S
    · have hvA : v ∈ A := hS_A hvS
      have hu_not_S : u ∉ S := huS
      by_cases huC : u ∈ C
      · exact Or.inl <| Finset.mem_union_left _ <| Finset.mem_sdiff.mpr ⟨huC, hu_not_S⟩
      · refine Or.inl ?_
        rw [Finset.mem_union]
        exact Or.inr <| Finset.mem_biUnion.mpr ⟨v, hvS, by
          rw [SimpleGraph.mem_neighborFinset, SimpleGraph.between_adj]
          simpa [CA, Set.mem_compl_iff, Finset.mem_coe] using
            show G.Adj v u ∧
              (v ∈ (↑(C.filter fun w => w ∈ A) : Set V) ∧ u ∈ ((↑C : Set V)ᶜ) ∨
                v ∈ ((↑C : Set V)ᶜ) ∧ u ∈ (↑(C.filter fun w => w ∈ A) : Set V)) from
              ⟨hadj.symm, Or.inl ⟨by simpa using hS hvS, by simpa [Set.mem_compl_iff, Finset.mem_coe] using huC⟩⟩⟩
    · rcases hC hadj with huC | hvC
      · exact Or.inl <| Finset.mem_union_left _ <| Finset.mem_sdiff.mpr ⟨huC, huS⟩
      · exact Or.inr <| Finset.mem_union_left _ <| Finset.mem_sdiff.mpr ⟨hvC, hvS⟩

private lemma hall_condition_left_of_min_cover
    {A B : Set V} [DecidablePred (· ∈ A)] (hAB : G.IsBipartiteWith A B)
    {C : Finset V} (hCmin : (↑C : Set V).encard = SimpleGraph.vertexCoverNum G)
    (hC : IsVertexCover G C) :
    ∀ S : Finset V, S ⊆ (C.filter fun v => v ∈ A) →
      S.card ≤ (S.biUnion (fun v =>
        (G.between (↑(C.filter fun w => w ∈ A) : Set V) ((↑C : Set V)ᶜ)).neighborFinset v)).card := by
  classical
  intro S hSsub
  by_contra hle
  let N : Finset V := S.biUnion fun v =>
    (G.between (↑(C.filter fun w => w ∈ A) : Set V) ((↑C : Set V)ᶜ)).neighborFinset v
  have hNlt : N.card < S.card := by
    exact Nat.lt_of_not_ge (by simpa [N] using hle)
  have hNC : Disjoint N C := by
    rw [Finset.disjoint_left]
    intro x hxN hxC
    rw [Finset.mem_biUnion] at hxN
    rcases hxN with ⟨v, hvS, hxN⟩
    rw [SimpleGraph.mem_neighborFinset, SimpleGraph.between_adj, Set.mem_compl_iff,
      Finset.mem_coe] at hxN
    rcases hxN.2 with hleft | hright
    · exact hleft.2 hxC
    · have hvC : v ∈ C := (Finset.mem_filter.mp (hSsub hvS)).1
      exact hright.1 hvC
  let C' : Finset V := (C \ S) ∪ N
  have hC' : IsVertexCover G C' := by
    simpa [C'] using
      replace_left_cover_isVertexCover (G := G) (A := A) (B := B) (hAB := hAB)
        (C := C) (S := S) hC (hS := hSsub)
  have hC'lt : C'.card < C.card := by
    apply replaced_cover_card_lt (C := C) (S := S) (N := N)
    · intro x hx
      exact (Finset.mem_filter.mp (hSsub hx)).1
    · exact hNC
    · exact hNlt
  have hcoverSet : SimpleGraph.IsVertexCover G (↑C' : Set V) := by
    simpa [IsVertexCover, C'] using hC'
  have hminle : SimpleGraph.vertexCoverNum G ≤ (↑C' : Set V).encard :=
    hcoverSet.vertexCoverNum_le
  have hle : (C.card : ℕ∞) ≤ (C'.card : ℕ∞) := by
    calc
      (C.card : ℕ∞) = (↑C : Set V).encard := by simp
      _ = SimpleGraph.vertexCoverNum G := hCmin
      _ ≤ (↑C' : Set V).encard := hminle
      _ = (C'.card : ℕ∞) := by
        simp
  have hlt' : (C'.card : ℕ∞) < C.card := by
    exact_mod_cast hC'lt
  exact (not_le_of_gt hlt') hle

private lemma hall_condition_right_of_min_cover
    {A B : Set V} [DecidablePred (· ∈ B)] (hAB : G.IsBipartiteWith A B)
    {C : Finset V} (hCmin : (↑C : Set V).encard = SimpleGraph.vertexCoverNum G)
    (hC : IsVertexCover G C) :
    ∀ S : Finset V, S ⊆ (C.filter fun v => v ∈ B) →
      S.card ≤ (S.biUnion (fun v =>
        (G.between (↑(C.filter fun w => w ∈ B) : Set V) ((↑C : Set V)ᶜ)).neighborFinset v)).card := by
  simpa using
    hall_condition_left_of_min_cover (G := G) (A := B) (B := A) (hAB := hAB.symm)
      (C := C) hCmin hC

private lemma hall_injection_matching
    (A : Finset V) (f : ↑A → V) (hf_inj : Function.Injective f)
    (hf_adj : ∀ v : ↑A, G.Adj v.1 (f v))
    (hf_not_A : ∀ v : ↑A, f v ∉ A) :
    ∃ M : G.Subgraph,
      M.IsMatching ∧
      (∀ v ∈ A, v ∈ M.verts) ∧
      M.verts = (↑A : Set V) ∪ Set.range (fun v : ↑A => f v) ∧
      M.edgeSet.ncard = A.card := by
  classical
  let M : G.Subgraph := {
    verts := (↑A : Set V) ∪ Set.range (fun v : ↑A => f v)
    Adj := fun u w => (∃ v : ↑A, u = v.1 ∧ w = f v) ∨ (∃ v : ↑A, w = v.1 ∧ u = f v)
    adj_sub := by
      intro u w h
      rcases h with ⟨v, rfl, rfl⟩ | ⟨v, rfl, rfl⟩
      · exact hf_adj v
      · exact (hf_adj v).symm
    edge_vert := by
      intro u w h
      rcases h with ⟨v, rfl, _⟩ | ⟨v, _, rfl⟩
      · exact Or.inl v.2
      · exact Or.inr ⟨v, rfl⟩
    symm := by
      intro u w h
      rcases h with h | h
      · exact Or.inr h
      · exact Or.inl h }
  have hMmatch : M.IsMatching := by
    intro v hv
    rcases hv with hv | ⟨w, rfl⟩
    · refine ⟨f ⟨v, hv⟩, Or.inl ⟨⟨v, hv⟩, rfl, rfl⟩, ?_⟩
      intro u hu
      rcases hu with ⟨v', hv', rfl⟩ | ⟨v', rfl, hfv⟩
      · congr 1
        exact Subtype.ext hv'.symm
      · exact absurd hv (hfv ▸ hf_not_A v')
    · refine ⟨w.1, Or.inr ⟨w, rfl, rfl⟩, ?_⟩
      intro u hu
      rcases hu with ⟨v', hv', hfv'⟩ | ⟨v', rfl, hfv'⟩
      · exact absurd v'.2 (hv' ▸ hf_not_A w)
      · exact congrArg Subtype.val (hf_inj hfv'.symm)
  have hAverts : ∀ v ∈ A, v ∈ M.verts := by
    intro v hv
    exact Or.inl hv
  have hverts : M.verts = (↑A : Set V) ∪ Set.range (fun v : ↑A => f v) := by
    rfl
  have hedgeSet :
      M.edgeSet = Set.range (fun v : ↑A => s(v.1, f v)) := by
    ext e
    constructor
    · intro he
      induction e using Sym2.ind with
      | h u w =>
          rw [Subgraph.mem_edgeSet] at he
          rcases he with ⟨v, rfl, rfl⟩ | ⟨v, rfl, rfl⟩
          · exact ⟨v, rfl⟩
          · exact ⟨v, Sym2.eq_swap⟩
    · rintro ⟨v, rfl⟩
      rw [Subgraph.mem_edgeSet]
      exact Or.inl ⟨v, rfl, rfl⟩
  have hEdgeInj : Function.Injective (fun v : ↑A => s(v.1, f v)) := by
    intro x y hxy
    apply Subtype.ext
    have hxmem : x.1 ∈ s(y.1, f y) := by
      simpa [hxy] using (Sym2.mem_mk_left x.1 (f x))
    rcases (Sym2.mem_iff.mp hxmem) with hxy' | hxy'
    · exact hxy'
    · exact False.elim <| hf_not_A y (hxy' ▸ x.2)
  have hcard : M.edgeSet.ncard = A.card := by
    rw [hedgeSet, Set.ncard_range_of_injective hEdgeInj]
    rw [Nat.card_eq_fintype_card]
    simp
  exact ⟨M, hMmatch, hAverts, hverts, hcard⟩

/-! ### König's theorem (Diestel Theorem 2.1.1)

> "In bipartite graphs, the maximum number of edges in a matching
>  equals the minimum number of vertices in a vertex cover."
-/

/-- **Theorem 2.1.1** (König 1931): max matching = min vertex cover
    in bipartite graphs.  (Diestel §2.1, p. 30) -/
theorem konig_theorem (hbip : G.IsBipartite) :
    ∃ (M : G.Subgraph) (U : Finset V),
      M.IsMatching ∧ IsVertexCover G U ∧
      M.edgeSet.ncard = U.card := by
  classical
  obtain ⟨A, B, hAB⟩ := hbip.exists_isBipartiteWith
  obtain ⟨Cset, hCminSet, hCcoverSet⟩ := SimpleGraph.vertexCoverNum_exists G
  let C : Finset V := Cset.toFinite.toFinset
  have hCmin : (↑C : Set V).encard = SimpleGraph.vertexCoverNum G := by
    simpa [C] using hCminSet
  have hC : IsVertexCover G C := by
    simpa [C] using isVertexCover_toFinset (G := G) hCcoverSet
  let CA : Finset V := C.filter fun v => v ∈ A
  let CB : Finset V := C.filter fun v => v ∈ B
  let HA : SimpleGraph V := G.between (↑CA : Set V) ((↑C : Set V)ᶜ)
  let HB : SimpleGraph V := G.between (↑CB : Set V) ((↑C : Set V)ᶜ)
  let tA : ↑CA → Finset V := fun v => HA.neighborFinset v.1
  let tB : ↑CB → Finset V := fun v => HB.neighborFinset v.1
  have hHallA : ∀ s : Finset ↑CA, s.card ≤ (s.biUnion tA).card := by
    intro s
    let S : Finset V := s.map ⟨Subtype.val, Subtype.val_injective⟩
    have hS_sub : S ⊆ CA := by
      intro v hv
      change v ∈ s.map ⟨Subtype.val, Subtype.val_injective⟩ at hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hv
      exact w.2
    have hineq :=
      hall_condition_left_of_min_cover (G := G) (A := A) (B := B) (hAB := hAB)
        (C := C) hCmin hC S hS_sub
    have hEq : S.biUnion (fun v => HA.neighborFinset v) = s.biUnion tA := by
      ext x
      constructor
      · intro hx
        rw [Finset.mem_biUnion] at hx
        rcases hx with ⟨v, hv, hx⟩
        change v ∈ s.map ⟨Subtype.val, Subtype.val_injective⟩ at hv
        obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hv
        exact Finset.mem_biUnion.mpr ⟨w, hw, hx⟩
      · intro hx
        rw [Finset.mem_biUnion] at hx
        rcases hx with ⟨w, hw, hx⟩
        exact Finset.mem_biUnion.mpr ⟨w.1, Finset.mem_map.mpr ⟨w, hw, rfl⟩, hx⟩
    have hineq' : s.card ≤ (S.biUnion (fun v => HA.neighborFinset v)).card := by
      simpa [S, HA] using hineq
    rwa [hEq] at hineq'
  have hHallB : ∀ s : Finset ↑CB, s.card ≤ (s.biUnion tB).card := by
    intro s
    let S : Finset V := s.map ⟨Subtype.val, Subtype.val_injective⟩
    have hS_sub : S ⊆ CB := by
      intro v hv
      change v ∈ s.map ⟨Subtype.val, Subtype.val_injective⟩ at hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hv
      exact w.2
    have hineq :=
      hall_condition_right_of_min_cover (G := G) (A := A) (B := B) (hAB := hAB)
        (C := C) hCmin hC S hS_sub
    have hEq : S.biUnion (fun v => HB.neighborFinset v) = s.biUnion tB := by
      ext x
      constructor
      · intro hx
        rw [Finset.mem_biUnion] at hx
        rcases hx with ⟨v, hv, hx⟩
        change v ∈ s.map ⟨Subtype.val, Subtype.val_injective⟩ at hv
        obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hv
        exact Finset.mem_biUnion.mpr ⟨w, hw, hx⟩
      · intro hx
        rw [Finset.mem_biUnion] at hx
        rcases hx with ⟨w, hw, hx⟩
        exact Finset.mem_biUnion.mpr ⟨w.1, Finset.mem_map.mpr ⟨w, hw, rfl⟩, hx⟩
    have hineq' : s.card ≤ (S.biUnion (fun v => HB.neighborFinset v)).card := by
      simpa [S, HB] using hineq
    rwa [hEq] at hineq'
  obtain ⟨fA, hfA_inj, hfA_mem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective tA).mp hHallA
  obtain ⟨fB, hfB_inj, hfB_mem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective tB).mp hHallB
  have hfA_adj : ∀ v : ↑CA, G.Adj v.1 (fA v) := by
    intro v
    have hmem : G.Adj v.1 (fA v) ∧ (fA v ∉ C ∨ v.1 ∉ C ∧ fA v ∈ CA) := by
      simpa [tA, HA, SimpleGraph.mem_neighborFinset, SimpleGraph.between_adj,
        Set.mem_compl_iff, Finset.mem_coe] using hfA_mem v
    exact hmem.1
  have hfB_adj : ∀ v : ↑CB, G.Adj v.1 (fB v) := by
    intro v
    have hmem : G.Adj v.1 (fB v) ∧ (fB v ∉ C ∨ v.1 ∉ C ∧ fB v ∈ CB) := by
      simpa [tB, HB, SimpleGraph.mem_neighborFinset, SimpleGraph.between_adj,
        Set.mem_compl_iff, Finset.mem_coe] using hfB_mem v
    exact hmem.1
  have hfA_not_C : ∀ v : ↑CA, fA v ∉ C := by
    intro v
    have hmem : G.Adj v.1 (fA v) ∧ (fA v ∉ C ∨ v.1 ∉ C ∧ fA v ∈ CA) := by
      simpa [tA, HA, SimpleGraph.mem_neighborFinset, SimpleGraph.between_adj,
        Set.mem_compl_iff, Finset.mem_coe] using hfA_mem v
    rcases hmem.2 with hfA_not_C | hbad
    · exact hfA_not_C
    · exact False.elim <| hbad.1 ((Finset.mem_filter.mp v.2).1)
  have hfB_not_C : ∀ v : ↑CB, fB v ∉ C := by
    intro v
    have hmem : G.Adj v.1 (fB v) ∧ (fB v ∉ C ∨ v.1 ∉ C ∧ fB v ∈ CB) := by
      simpa [tB, HB, SimpleGraph.mem_neighborFinset, SimpleGraph.between_adj,
        Set.mem_compl_iff, Finset.mem_coe] using hfB_mem v
    rcases hmem.2 with hfB_not_C | hbad
    · exact hfB_not_C
    · exact False.elim <| hbad.1 ((Finset.mem_filter.mp v.2).1)
  have hfA_not_CA : ∀ v : ↑CA, fA v ∉ CA := by
    intro v hf
    exact hfA_not_C v ((Finset.mem_filter.mp hf).1)
  have hfB_not_CB : ∀ v : ↑CB, fB v ∉ CB := by
    intro v hf
    exact hfB_not_C v ((Finset.mem_filter.mp hf).1)
  have hfA_in_B : ∀ v : ↑CA, fA v ∈ B := by
    intro v
    exact hAB.mem_of_mem_adj ((Finset.mem_filter.mp v.2).2) (hfA_adj v)
  have hfB_in_A : ∀ v : ↑CB, fB v ∈ A := by
    intro v
    exact hAB.symm.mem_of_mem_adj ((Finset.mem_filter.mp v.2).2) (hfB_adj v)
  obtain ⟨MA, hMA_match, hMA_cover, hMA_verts, hMA_card⟩ :=
    hall_injection_matching (G := G) CA fA hfA_inj hfA_adj hfA_not_CA
  obtain ⟨MB, hMB_match, hMB_cover, hMB_verts, hMB_card⟩ :=
    hall_injection_matching (G := G) CB fB hfB_inj hfB_adj hfB_not_CB
  have hCA_CB_disj : Disjoint CA CB := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    exact Set.disjoint_left.mp hAB.disjoint
      ((Finset.mem_filter.mp hxA).2) ((Finset.mem_filter.mp hxB).2)
  have hMA_MB_verts_disj : Disjoint MA.verts MB.verts := by
    rw [hMA_verts, hMB_verts, Set.disjoint_left]
    intro x hxA hxB
    rcases hxA with hxCA | hxRA
    · rcases hxB with hxCB | hxRB
      · exact Set.disjoint_left.mp hAB.disjoint
          ((Finset.mem_filter.mp hxCA).2) ((Finset.mem_filter.mp hxCB).2)
      · rcases hxRB with ⟨vB, rfl⟩
        exact hfB_not_C vB ((Finset.mem_filter.mp hxCA).1)
    · rcases hxRA with ⟨vA, rfl⟩
      rcases hxB with hxCB | hxRB
      · exact hfA_not_C vA ((Finset.mem_filter.mp hxCB).1)
      · rcases hxRB with ⟨vB, hEq⟩
        have : fB vB ∈ B := by simpa [hEq] using hfA_in_B vA
        exact Set.disjoint_left.mp hAB.disjoint (hfB_in_A vB) this
  have hMA_MB_support_disj : Disjoint MA.support MB.support := by
    rw [hMA_match.support_eq_verts, hMB_match.support_eq_verts]
    exact hMA_MB_verts_disj
  let M : G.Subgraph := MA ⊔ MB
  let U : Finset V := CA ∪ CB
  have hM_match : M.IsMatching := hMA_match.sup hMB_match hMA_MB_support_disj
  have hU_cover : IsVertexCover G U := by
    intro u v hadj
    rcases hAB.mem_of_adj hadj with huv | huv
    · rcases hC hadj with huC | hvC
      · exact Or.inl <| by
          simp [U]
          exact Or.inl (Finset.mem_filter.mpr ⟨huC, huv.1⟩)
      · exact Or.inr <| by
          simp [U]
          exact Or.inr (Finset.mem_filter.mpr ⟨hvC, huv.2⟩)
    · rcases hC hadj with huC | hvC
      · exact Or.inl <| by
          simp [U]
          exact Or.inr (Finset.mem_filter.mpr ⟨huC, huv.1⟩)
      · exact Or.inr <| by
          simp [U]
          exact Or.inl (Finset.mem_filter.mpr ⟨hvC, huv.2⟩)
  have hMA_MB_edge_disj : Disjoint MA.edgeSet MB.edgeSet := by
    have hverts_disj : ∀ ⦃x⦄, x ∈ MA.verts → x ∈ MB.verts → False :=
      Set.disjoint_left.mp hMA_MB_verts_disj
    rw [Set.disjoint_left]
    intro e heA heB
    exact hverts_disj
      (MA.mem_verts_of_mem_edge heA (Sym2.out_fst_mem e))
      (MB.mem_verts_of_mem_edge heB (Sym2.out_fst_mem e))
  have hM_card : M.edgeSet.ncard = U.card := by
    calc
      M.edgeSet.ncard = (MA.edgeSet ∪ MB.edgeSet).ncard := by
        simp [M, Subgraph.edgeSet_sup]
      _ = MA.edgeSet.ncard + MB.edgeSet.ncard := by
        exact Set.ncard_union_eq hMA_MB_edge_disj
      _ = CA.card + CB.card := by rw [hMA_card, hMB_card]
      _ = U.card := by
        simp [U, Finset.card_union_of_disjoint hCA_CB_disj]
  exact ⟨M, U, hM_match, hU_cover, hM_card⟩

/-! ### Hall's marriage theorem (Diestel Theorem 2.1.2)

> "A bipartite graph G = (A ∪ B, E) contains a matching of A iff
>  |N(S)| ≥ |S| for all S ⊆ A."
-/

/-- **Hall's condition** for a set A: every subset S ⊆ A satisfies
    |N(S)| ≥ |S|. -/
def SatisfiesHallCondition (A : Finset V) : Prop :=
  ∀ S : Finset V, S ⊆ A →
    S.card ≤ (S.biUnion (fun v => G.neighborFinset v) \ A).card

/-- **Theorem 2.1.2** (Hall 1935, marriage theorem): a bipartite graph
    with partition (p₁, p₂) contains a matching saturating p₁ iff
    Hall's condition |N(S)| ≥ |S| holds for all S ⊆ p₁.

    Mathlib: `SimpleGraph.exists_isMatching_of_forall_ncard_le`.
    (Diestel §2.1, p. 31) -/
theorem hall_marriage {p₁ p₂ : Set V} (hbip : G.IsBipartiteWith p₁ p₂)
    (hHall : ∀ s ⊆ p₁, s.ncard ≤ (⋃ x ∈ s, G.neighborSet x).ncard) :
    ∃ M : G.Subgraph, p₁ ⊆ M.verts ∧ M.IsMatching :=
  exists_isMatching_of_forall_ncard_le hbip hHall

/-! ### Tutte's theorem (Diestel §2.2) -/

/-- The number of **odd components** of a graph. -/
noncomputable def oddComponentCount : ℕ :=
  G.oddComponents.ncard

private lemma oddComponentCount_eq_filter_card
    (H : SimpleGraph V) [DecidableRel H.Adj] :
    oddComponentCount H =
      (Finset.univ.filter fun c : H.ConnectedComponent =>
        Odd (Fintype.card c.supp)).card := by
  classical
  rw [oddComponentCount, Set.ncard_eq_toFinset_card']
  congr
  ext c
  simp only [Set.mem_toFinset, Finset.mem_filter, Finset.mem_univ, true_and,
    SimpleGraph.oddComponents]
  constructor
  · intro hc
    have hsupp : c.supp.ncard = #(filter (Membership.mem c.supp) univ) := by
      calc
        c.supp.ncard = c.supp.toFinset.card := Set.ncard_eq_toFinset_card' c.supp
        _ = #(filter (Membership.mem c.supp) univ) := by
          simp
    simpa [hsupp] using hc
  · intro hc
    have hsupp : c.supp.ncard = #(filter (Membership.mem c.supp) univ) := by
      calc
        c.supp.ncard = c.supp.toFinset.card := Set.ncard_eq_toFinset_card' c.supp
        _ = #(filter (Membership.mem c.supp) univ) := by
          simp
    simpa [hsupp] using hc

/-- **Theorem 2.2.1** (Tutte 1947): G has a perfect matching iff for
    every S ⊆ V, the number of odd components of G − S is ≤ |S|.
    (Diestel §2.2, p. 36) -/
  theorem tutte_theorem :
    (∃ M : G.Subgraph, M.IsPerfectMatching) ↔
    ∀ S : Finset V, oddComponentCount (G.induce ((↑S : Set V)ᶜ)) ≤ S.card := by
  classical
  by_cases hcard : Even (Fintype.card V)
  · simpa [oddComponentCount_eq_filter_card] using
      AutoBooks.GraphTheory.BondyMurty.Ch16.tutte_1factor (G := G) hcard
  · constructor
    · intro hM
      obtain ⟨M, hM⟩ := hM
      exact (hcard hM.even_card).elim
    · intro hoddBound
      have hoddCard : Odd (Nat.card ↥(Set.univ : Set V)) := by
        simpa [Nat.card_eq_fintype_card] using
          (Nat.not_even_iff_odd.mp hcard : Odd (Fintype.card V))
      have hoddCount : Odd (oddComponentCount (G.induce (Set.univ : Set V))) := by
        simpa [Nat.card_eq_fintype_card] using
          (SimpleGraph.odd_ncard_oddComponents (G := G.induce (Set.univ : Set V))).2 hoddCard
      have hzero : oddComponentCount (G.induce (Set.univ : Set V)) = 0 := by
        have hzero' : oddComponentCount (G.induce ((↑(∅ : Finset V) : Set V)ᶜ)) = 0 := by
          simpa using hoddBound (∅ : Finset V)
        have hcompl : ((↑(∅ : Finset V) : Set V)ᶜ) = (Set.univ : Set V) := by
          ext x
          simp
        rw [hcompl] at hzero'
        exact hzero'
      have hpos : 0 < oddComponentCount (G.induce (Set.univ : Set V)) := hoddCount.pos
      omega

end AutoBooks.GraphTheory.Diestel.Ch02
