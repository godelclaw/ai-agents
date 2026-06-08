/-
# Diestel, Graph Theory — Section 1.6: Bipartite Graphs

Formalization of definitions and results from Section 1.6 of:
  R. Diestel, *Graph Theory* (5th edition), Springer GTM 173.

We build on Mathlib's bipartite and coloring infrastructure.

## Contents
- Pointers to Mathlib for bipartite, colorable, r-partite
- Proposition 1.6.1: bipartite ↔ no odd cycle
-/

import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.ConcreteColorings

set_option linter.unusedSectionVars false

open SimpleGraph Walk Finset

namespace AutoBooks.GraphTheory.Diestel.Ch01

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### Diestel §1.6 — Definitions (pointers to Mathlib)

| Diestel              | Mathlib                                    |
|----------------------|--------------------------------------------|
| Bipartite            | `SimpleGraph.IsBipartite` (= `Colorable 2`)|
| r-partite            | `SimpleGraph.Colorable r`                  |
| Complete bipartite   | `SimpleGraph.completeBipartiteGraph`       |
| Chromatic number     | `SimpleGraph.chromaticNumber`              |
-/

/-! ### Proposition 1.6.1 (Diestel §1.6, p. 17)

> "A graph is bipartite if and only if it contains no odd cycle."

This is one of the most fundamental characterizations in graph theory.
The forward direction is straightforward (parity argument).
The reverse uses a spanning-tree coloring argument.
-/

/-- In `Fin 2`, if `a ≠ b` and `b ≠ c` then `a = c`. -/
private lemma fin2_eq_of_ne_ne {a b c : Fin 2}
    (hab : a ≠ b) (hbc : b ≠ c) : a = c := by
  revert a b c; decide

/-- Along any walk in a 2-colored graph, the start and end colors
    agree iff the walk has even length. -/
private theorem coloring_walk_parity {u v : V} (f : G.Coloring (Fin 2))
    (w : G.Walk u v) : (f u = f v) ↔ Even w.length := by
  induction w with
  | nil => simp
  | @cons a b c hab w ih =>
    have hne := f.valid hab
    rw [length_cons, Nat.even_add_one, ← ih]
    exact ⟨fun hac hbc => hne (hac.trans hbc.symm),
           fun hbc => fin2_eq_of_ne_ne hne hbc⟩

/-- An **odd cycle** in G is a cycle of odd length. -/
def HasOddCycle : Prop :=
  ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ Odd c.length

/-- **Proposition 1.6.1, forward direction** (Diestel §1.6):
    A bipartite graph has no odd cycle.

    Proof: in a bipartition (A, B), traversing a cycle alternates
    between A and B, so any cycle returning to its start has even length. -/
theorem IsBipartite.no_odd_cycle (h : G.IsBipartite) :
    ¬HasOddCycle G := by
  intro ⟨v, c, _, hodd⟩
  obtain ⟨f⟩ := h
  have hev := (coloring_walk_parity G f c).mp rfl
  obtain ⟨k, hk⟩ := hev; obtain ⟨m, hm⟩ := hodd; omega

/-! ### Reverse direction: no odd cycle → bipartite

We use Mathlib's `two_colorable_iff_forall_loop_even`:
  `G.Colorable 2 ↔ ∀ u, ∀ (w : G.Walk u u), Even w.length`

It suffices to show: if G has no odd cycle, then every closed walk
has even length.  The proof proceeds by strong induction on walk length. -/

/-- Key lemma: any odd-length closed walk in a simple graph yields
    an odd cycle.  Proof by strong induction on walk length. -/
private theorem odd_walk_has_odd_cycle :
    ∀ (n : ℕ), ∀ {u : V} (w : G.Walk u u), w.length = n → Odd n →
      HasOddCycle G := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro u w hlen hodd
    -- n ≥ 3: length 1 needs a self-loop (impossible in SimpleGraph)
    have hn1 : n ≠ 1 := by
      intro hn; subst hn
      have hadj := w.adj_getVert_succ (show 0 < w.length by omega)
      simp only [w.getVert_zero] at hadj
      have : w.getVert (0 + w.length) = u := by
        rw [Nat.zero_add]; exact w.getVert_length
      rw [show (0 + 1 : ℕ) = 0 + w.length from by omega] at hadj
      rw [this] at hadj
      exact G.irrefl hadj
    have hge3 : 3 ≤ n := by obtain ⟨k, hk⟩ := hodd; omega
    by_cases hnd : w.support.tail.Nodup
    · -- w is a cycle: tail is nodup + length ≥ 3 ⟹ cycle
      have hnnil : ¬w.Nil := by
        intro h; exact absurd h.eq_nil (by intro h'; simp [h'] at hlen; omega)
      -- w.tail.support = w.support.tail
      have htail_supp : w.tail.support = w.support.tail := by
        have h := cons_support_tail w hnnil
        -- h : u :: w.tail.support = w.support
        simpa using congrArg List.tail h
      have htail_path : w.tail.IsPath :=
        (isPath_def _).mpr (htail_supp ▸ hnd)
      exact ⟨u, w, isCycle_iff_isPath_tail_and_le_length.mpr ⟨htail_path, hlen ▸ hge3⟩,
             hlen ▸ hodd⟩
    · -- support.tail not nodup ⟹ repeated vertex ⟹ split
      -- Extract two indices where the same vertex appears
      rw [List.nodup_iff_getElem?_ne_getElem?] at hnd
      push_neg at hnd
      obtain ⟨i, j, hij, hjlen, heqopt⟩ := hnd
      have htail_len : w.support.tail.length = w.length := by
        simp [Walk.length_support, List.length_tail]
      have hilen : i < w.length := by omega
      have hjlen' : j < w.length := by omega
      -- Convert getElem? to getElem
      have hi_valid : i < w.support.tail.length := by omega
      have hj_valid : j < w.support.tail.length := by omega
      rw [List.getElem?_eq_getElem hi_valid, List.getElem?_eq_getElem hj_valid] at heqopt
      have heq_tail : w.support.tail[i] = w.support.tail[j] := by
        exact Option.some_injective _ heqopt
      -- Convert tail indices to support indices: tail[k] = support[k+1]
      have hi1_valid : i + 1 < w.support.length := by
        simp [Walk.length_support]; omega
      have hj1_valid : j + 1 < w.support.length := by
        simp [Walk.length_support]; omega
      have htail_to_supp_i : w.support.tail[i] = w.support[i + 1] := by
        rw [List.getElem_tail]
      have htail_to_supp_j : w.support.tail[j] = w.support[j + 1] := by
        rw [List.getElem_tail]
      -- Now get equality on getVert
      have hi1_le : i + 1 ≤ w.length := by omega
      have hj1_le : j + 1 ≤ w.length := by omega
      have hgv_i : w.getVert (i + 1) = w.support[i + 1] :=
        w.getVert_eq_support_getElem hi1_le
      have hgv_j : w.getVert (j + 1) = w.support[j + 1] :=
        w.getVert_eq_support_getElem hj1_le
      have heq : w.getVert (i + 1) = w.getVert (j + 1) := by
        rw [hgv_i, hgv_j, ← htail_to_supp_i, ← htail_to_supp_j, heq_tail]
      -- Split: inner loop from position (i+1) to (j+1), outer is the rest
      set k := i + 1 with hk_def
      set m := j + 1 with hm_def
      have hkm : k < m := by omega
      have hm_le : m ≤ w.length := by omega
      have hk_le : k ≤ w.length := by omega
      -- Inner walk: (w.drop k).take (m - k), a closed walk of length m - k
      have hdrop_gv : (w.drop k).getVert (m - k) = w.getVert m := by
        rw [Walk.drop_getVert]; congr 1; omega
      set w_inner := ((w.drop k).take (m - k)).copy rfl
        (show (w.drop k).getVert (m - k) = w.getVert k from
          hdrop_gv ▸ heq.symm)
      have hlen_inner : w_inner.length = m - k := by
        simp only [w_inner, Walk.length_copy, Walk.take_length, Walk.drop_length]
        exact Nat.min_eq_left (by omega)
      -- Outer walk: (w.take k).append ((w.drop m).copy ...)
      set w_outer := (w.take k).append ((w.drop m).copy heq.symm rfl)
      have hlen_outer : w_outer.length = w.length - (m - k) := by
        simp only [w_outer, Walk.length_append, Walk.length_copy,
                    Walk.take_length, Walk.drop_length]
        rw [Nat.min_eq_left hk_le]; omega
      -- Their lengths sum to n, one is odd
      have hlen_sum : w_inner.length + w_outer.length = n := by
        rw [hlen_inner, hlen_outer, hlen]; omega
      have hinner_lt : w_inner.length < n := by omega
      have houter_lt : w_outer.length < n := by omega
      have hodd_one : Odd w_inner.length ∨ Odd w_outer.length := by
        by_contra h; push_neg at h
        simp only [Nat.not_odd_iff_even] at h
        exact (Nat.not_even_iff_odd.mpr hodd) (hlen_sum ▸ h.1.add h.2)
      rcases hodd_one with hodd_i | hodd_o
      · exact ih w_inner.length hinner_lt w_inner rfl hodd_i
      · exact ih w_outer.length houter_lt w_outer rfl hodd_o

/-- **Proposition 1.6.1, reverse direction** (Diestel §1.6):
    A graph with no odd cycle is bipartite. -/
theorem no_odd_cycle_isBipartite (h : ¬HasOddCycle G) :
    G.IsBipartite := by
  rw [show G.IsBipartite = G.Colorable 2 from rfl, two_colorable_iff_forall_loop_even]
  intro u w
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  exact h (odd_walk_has_odd_cycle G w.length w rfl hodd)

/-- **Proposition 1.6.1** (Diestel §1.6):
    A graph is bipartite if and only if it contains no odd cycle. -/
theorem isBipartite_iff_no_odd_cycle :
    G.IsBipartite ↔ ¬HasOddCycle G :=
  ⟨IsBipartite.no_odd_cycle G, no_odd_cycle_isBipartite G⟩

end AutoBooks.GraphTheory.Diestel.Ch01
