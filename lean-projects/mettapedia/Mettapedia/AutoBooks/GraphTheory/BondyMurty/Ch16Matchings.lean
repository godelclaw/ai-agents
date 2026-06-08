/-
# Bondy & Murty, Graph Theory — Chapter 16: Matchings

Formalization of definitions and results from Chapter 16 of:
  J. A. Bondy and U. S. R. Murty, *Graph Theory* (2007), Springer GTM 244.

## Contents
- Matchings and covers
- König's theorem (bipartite matching duality)
- Hall's theorem (marriage condition)
- Tutte's theorem (1-factor condition)
-/

import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Combinatorics.SimpleGraph.Tutte

set_option linter.unusedSectionVars false

open SimpleGraph Finset

namespace AutoBooks.GraphTheory.BondyMurty.Ch16

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### Bondy–Murty §16.2 — Hall's theorem

> "Let G[A, B] be a bipartite graph. Then G has a matching that
>  saturates every vertex of A if and only if |N(S)| ≥ |S| for
>  every subset S of A."
-/

/-- **Theorem 16.4** (Hall 1935): a bipartite graph has a matching
    saturating A iff |N(S)| ≥ |S| for all S ⊆ A.
    (Bondy–Murty §16.2, p. 396)

    Proof: apply Mathlib's combinatorial Hall theorem to get an injection
    from A to V \ A, then construct a matching subgraph. -/
theorem hall_theorem (A : Finset V) :
    (∀ S : Finset V, S ⊆ A →
      S.card ≤ (S.biUnion (fun v => G.neighborFinset v) \ A).card) →
    ∃ M : G.Subgraph, M.IsMatching ∧ ∀ v ∈ A, v ∈ M.verts := by
  intro hHall
  -- Step 1: Convert Hall condition to the Finset injection form.
  let t : ↑A → Finset V := fun v => G.neighborFinset v.val \ A
  have hHall' : ∀ s : Finset ↑A, s.card ≤ (s.biUnion t).card := by
    intro s
    let S := s.map ⟨Subtype.val, Subtype.val_injective⟩
    have hS_sub : S ⊆ A := by
      intro v hv; obtain ⟨w, _, rfl⟩ := Finset.mem_map.mp hv; exact w.property
    have hineq := hHall S hS_sub
    rw [Finset.card_map] at hineq
    suffices heq : S.biUnion (fun v => G.neighborFinset v) \ A = s.biUnion t by
      rw [← heq]; exact hineq
    ext x
    constructor
    · intro hx
      rw [Finset.mem_sdiff, Finset.mem_biUnion] at hx
      obtain ⟨⟨v, hv, hvx⟩, hxA⟩ := hx
      rw [Finset.mem_map] at hv
      obtain ⟨w, hw, rfl⟩ := hv
      exact Finset.mem_biUnion.mpr ⟨w, hw, Finset.mem_sdiff.mpr ⟨hvx, hxA⟩⟩
    · intro hx
      rw [Finset.mem_biUnion] at hx
      obtain ⟨w, hw, hxw⟩ := hx
      rw [Finset.mem_sdiff] at hxw
      rw [Finset.mem_sdiff, Finset.mem_biUnion]
      exact ⟨⟨w.val, Finset.mem_map.mpr ⟨w, hw, rfl⟩, hxw.1⟩, hxw.2⟩
  -- Step 2: Apply Mathlib's Hall theorem to get an injection.
  obtain ⟨f, hf_inj, hf_mem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hHall'
  have hf_adj : ∀ v : ↑A, G.Adj v.val (f v) := fun v => by
    have := hf_mem v; simp only [t, Finset.mem_sdiff, mem_neighborFinset] at this; exact this.1
  have hf_not_A : ∀ v : ↑A, f v ∉ A := fun v => by
    have := hf_mem v; simp only [t, Finset.mem_sdiff] at this; exact this.2
  -- Step 3: Construct the matching subgraph.
  let M : G.Subgraph := {
    verts := (↑A : Set V) ∪ Set.range (fun v : ↑A => f v)
    Adj := fun u w => (∃ v : ↑A, u = v.val ∧ w = f v) ∨ (∃ v : ↑A, w = v.val ∧ u = f v)
    adj_sub := by
      intro u w h
      rcases h with ⟨v, rfl, rfl⟩ | ⟨v, rfl, rfl⟩
      · exact hf_adj v
      · exact (hf_adj v).symm
    edge_vert := by
      intro u w h
      rcases h with ⟨v, rfl, _⟩ | ⟨v, _, rfl⟩
      · exact Or.inl v.property
      · exact Or.inr ⟨v, rfl⟩
    symm := by intro u w h; rcases h with h | h <;> [exact Or.inr h; exact Or.inl h]
  }
  refine ⟨M, ?_, fun v hv => Set.mem_union_left _ hv⟩
  -- Step 4: Prove M.IsMatching.
  intro v hv
  rcases hv with hv | ⟨w, rfl⟩
  · -- v ∈ A: unique match is f(⟨v, hv⟩)
    refine ⟨f ⟨v, hv⟩, Or.inl ⟨⟨v, hv⟩, rfl, rfl⟩, ?_⟩
    intro u hu
    rcases hu with ⟨v', hv', rfl⟩ | ⟨v', rfl, hfv⟩
    · congr 1; exact Subtype.ext hv'.symm
    · exact absurd hv (hfv ▸ hf_not_A v')
  · -- v = f w for some w ∈ A: unique match is w.val
    refine ⟨w.val, Or.inr ⟨w, rfl, rfl⟩, ?_⟩
    intro u hu
    rcases hu with ⟨v', hv', hfv'⟩ | ⟨v', rfl, hfv'⟩
    · exact absurd v'.property (hv' ▸ hf_not_A w)
    · exact congrArg Subtype.val (hf_inj hfv'.symm)

/-! ### Bondy–Murty §16.4 — Tutte's theorem -/

private lemma oddComponents_deleteVerts_card_eq_filter_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    (((⊤ : G.Subgraph).deleteVerts (↑S : Set V)).coe.oddComponents.ncard : ℕ) =
      (Finset.univ.filter fun c : (G.induce ((↑S : Set V)ᶜ)).ConnectedComponent =>
        Odd (Fintype.card c.supp)).card := by
  classical
  let φdel := ((⊤ : G.Subgraph).coeDeleteVertsIso (↑S : Set V))
  let eVerts : {v : (⊤ : G.Subgraph).verts | ↑v ∉ (↑S : Set V)} ≃ ↑((↑S : Set V)ᶜ) :=
    { toFun := fun v => ⟨v.1, v.2⟩
      invFun := fun v => ⟨⟨v, trivial⟩, v.property⟩
      left_inv := by
        intro v
        cases v
        rfl
      right_inv := by
        intro v
        rfl }
  let φind : ((⊤ : G.Subgraph).coe.induce {v : (⊤ : G.Subgraph).verts | ↑v ∉ (↑S : Set V)}) ≃g
      G.induce ((↑S : Set V)ᶜ) :=
    { toEquiv := eVerts
      map_rel_iff' := by
        intro a b
        rfl }
  let φ : (((⊤ : G.Subgraph).deleteVerts (↑S : Set V)).coe) ≃g G.induce ((↑S : Set V)ᶜ) :=
    φdel.trans φind
  let eComp := φ.connectedComponentEquiv
  have hmem : ∀ c,
      c ∈ (((⊤ : G.Subgraph).deleteVerts (↑S : Set V)).coe.oddComponents.toFinite.toFinset) ↔
        eComp c ∈
          Finset.univ.filter
            (fun d : (G.induce ((↑S : Set V)ᶜ)).ConnectedComponent => Odd (Fintype.card d.supp)) := by
    intro c
    have hodd₁ : Odd c.supp.ncard ↔ Odd (eComp c).supp.ncard := by
      have hc : c.supp.ncard = (eComp c).supp.ncard :=
        Set.ncard_congr' (ConnectedComponent.isoEquivSupp φ c)
      simp [hc]
    have hodd₂ : Odd c.supp.ncard ↔ Odd (Fintype.card (eComp c).supp) := by
      calc
        Odd c.supp.ncard ↔ Odd (eComp c).supp.ncard := hodd₁
        _ ↔ Odd (Fintype.card (eComp c).supp) := by
          simp [Set.ncard_eq_toFinset_card', Set.toFinset_card]
    simp [SimpleGraph.oddComponents, hodd₂]
  simpa [Set.ncard_eq_toFinset_card', Set.toFinite_toFinset] using
    (Finset.card_equiv eComp hmem)

/-- **Theorem 16.11** (Tutte 1947): G has a perfect matching iff
    o(G - S) ≤ |S| for all S ⊆ V.
    (Bondy–Murty §16.4, p. 407) -/
theorem tutte_1factor (hcard : Even (Fintype.card V)) :
    (∃ M : G.Subgraph, M.IsPerfectMatching) ↔
    ∀ S : Finset V,
      (Finset.univ.filter fun c : (G.induce ((↑S : Set V)ᶜ)).ConnectedComponent =>
        Odd (Fintype.card c.supp)).card ≤ S.card := by
  classical
  let _ := hcard
  rw [SimpleGraph.tutte (G := G)]
  constructor
  · intro h S
    have hS0 := h (↑S : Set V)
    have hS : (((⊤ : G.Subgraph).deleteVerts (↑S : Set V)).coe.oddComponents.ncard : ℕ) ≤ S.card := by
      simpa [SimpleGraph.IsTutteViolator, Set.ncard_eq_toFinset_card', Set.toFinset_card, not_lt] using hS0
    rw [oddComponents_deleteVerts_card_eq_filter_card (G := G) S] at hS
    exact hS
  · intro h u
    let uf : u.Finite := Set.toFinite u
    let S : Finset V := uf.toFinset
    have hu : ((↑S : Set V)) = u := by
      simpa [S] using uf.coe_toFinset
    have hS0 : (Finset.univ.filter fun c : (G.induce ((↑S : Set V)ᶜ)).ConnectedComponent =>
        Odd (Fintype.card c.supp)).card ≤ S.card := h S
    have hS : (((⊤ : G.Subgraph).deleteVerts (↑S : Set V)).coe.oddComponents.ncard : ℕ) ≤ S.card := by
      rw [oddComponents_deleteVerts_card_eq_filter_card (G := G) S]
      exact hS0
    rw [hu] at hS
    simpa [S, SimpleGraph.IsTutteViolator, Set.ncard_eq_toFinset_card', Set.toFinset_card, not_lt] using hS

end AutoBooks.GraphTheory.BondyMurty.Ch16
