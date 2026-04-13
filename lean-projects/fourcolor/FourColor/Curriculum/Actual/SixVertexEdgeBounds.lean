import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import FourColor.Curriculum.Actual.SixVertexStructure

namespace FourColor.Curriculum.Actual

section IncidenceBranch

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- On six vertices, any incidence-critical non-4-colorable graph has at least `12` edges.

Source: new theorem from the handshake lower bound `2|V| ≤ |E|`. -/
theorem IsIncidenceCriticalNonColorable.card_edgeFinset_ge_twelve_of_card_eq_six
    (h : IsIncidenceCriticalNonColorable G 4) (hcard : Fintype.card V = 6) :
    12 ≤ G.edgeFinset.card := by
  have hlow : 2 * Fintype.card V ≤ G.edgeFinset.card := h.two_mul_card_le_card_edgeFinset
  simpa [hcard] using hlow

/-- On six vertices, a `K₅`-free incidence-critical non-4-colorable graph has at most `14` edges.

Source: new theorem from existence of a degree-`4` vertex, incidence deletion cardinality, and the
five-vertex edge cap on the induced complement graph. -/
theorem IsIncidenceCriticalNonColorable.card_edgeFinset_le_fourteen_of_card_eq_six_of_cliqueFree
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 6) (hfree : G.CliqueFree 5) :
    G.edgeFinset.card ≤ 14 := by
  rcases h.exists_degree_eq_four_of_card_eq_six_of_cliqueFree hcard hfree with ⟨v, hv4⟩
  have hdel_le10 : (G.deleteIncidenceSet v).edgeFinset.card ≤ 10 := by
    calc
      (G.deleteIncidenceSet v).edgeFinset.card = (G.induce ({v}ᶜ)).edgeFinset.card := by
        simpa using
          (SimpleGraph.card_edgeFinset_induce_compl_singleton (G := G) (x := v)).symm
      _ ≤ (Fintype.card ({v}ᶜ : Set V)).choose 2 := by
        exact (G.induce ({v}ᶜ)).card_edgeFinset_le_card_choose_two
      _ = 10 := by
        have hcard_compl : Fintype.card ({v}ᶜ : Set V) = 5 := by
          calc
            Fintype.card ({v}ᶜ : Set V) = Fintype.card V - Fintype.card ({v} : Set V) := by
              simpa using (Fintype.card_compl_set ({v} : Set V))
            _ = Fintype.card V - 1 := by simp
            _ = 5 := by rw [hcard]
        calc
          (Fintype.card ({v}ᶜ : Set V)).choose 2 = (5).choose 2 := by
            rw [hcard_compl]
          _ = 10 := by decide
  have hsub : G.edgeFinset.card - 4 ≤ 10 := by
    have hsub' : G.edgeFinset.card - G.degree v ≤ 10 := by
      simpa [SimpleGraph.card_edgeFinset_deleteIncidenceSet (G := G) (x := v)] using hdel_le10
    simpa [hv4] using hsub'
  have hle : G.edgeFinset.card ≤ 10 + 4 := (Nat.sub_le_iff_le_add).1 hsub
  simpa [Nat.add_comm] using hle

/-- On six vertices, a `K₅`-free incidence-critical non-4-colorable graph has edge count in
`[12, 14]`.

Source: new theorem combining the previous lower and upper bounds. -/
theorem IsIncidenceCriticalNonColorable.card_edgeFinset_window_of_card_eq_six_of_cliqueFree
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 6) (hfree : G.CliqueFree 5) :
    12 ≤ G.edgeFinset.card ∧ G.edgeFinset.card ≤ 14 :=
  ⟨h.card_edgeFinset_ge_twelve_of_card_eq_six hcard,
    h.card_edgeFinset_le_fourteen_of_card_eq_six_of_cliqueFree hcard hfree⟩

end IncidenceBranch

section IncidenceTuranBranch

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableRel G.Adj]

/-- On six vertices, a `K₅`-free incidence-critical non-4-colorable graph has at most `13` edges.

Source: new theorem from Mathlib's Turán bound `CliqueFree.card_edgeFinset_le` at `r = 4`. -/
theorem IsIncidenceCriticalNonColorable.card_edgeFinset_le_thirteen_of_card_eq_six_of_cliqueFree
    (_h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 6) (hfree : G.CliqueFree 5) :
    G.edgeFinset.card ≤ 13 := by
  have hbound :=
    (SimpleGraph.CliqueFree.card_edgeFinset_le (G := G) (r := 4) hfree)
  simpa [hcard] using hbound

/-- On six vertices, `|E| = 14` is impossible for `K₅`-free incidence-critical non-4-colorable
graphs.

Source: new theorem from the Turán upper bound `|E| ≤ 13`. -/
theorem IsIncidenceCriticalNonColorable.card_edgeFinset_ne_fourteen_of_card_eq_six_of_cliqueFree
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 6) (hfree : G.CliqueFree 5) :
    G.edgeFinset.card ≠ 14 := by
  intro hedge
  have hle13 : G.edgeFinset.card ≤ 13 :=
    h.card_edgeFinset_le_thirteen_of_card_eq_six_of_cliqueFree hcard hfree
  have hlt14 : G.edgeFinset.card < 14 := lt_of_le_of_lt hle13 (by decide : 13 < 14)
  exact Nat.ne_of_lt hlt14 hedge

end IncidenceTuranBranch

section IncidenceBranch

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- On six vertices, a `K₅`-free incidence-critical non-4-colorable graph has edge count in
`[12, 13]`.

Source: new theorem combining the handshake lower bound with Turán's upper bound. -/
theorem IsIncidenceCriticalNonColorable.card_edgeFinset_window_twelve_thirteen_of_card_eq_six_of_cliqueFree
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 6) (hfree : G.CliqueFree 5) :
    12 ≤ G.edgeFinset.card ∧ G.edgeFinset.card ≤ 13 := by
  have hlow : 2 * Fintype.card V ≤ G.edgeFinset.card :=
    two_mul_card_le_card_edgeFinset_of_forall_four_le_degree (G := G) (fun v => h.four_le_degree v)
  refine ⟨?_, h.card_edgeFinset_le_thirteen_of_card_eq_six_of_cliqueFree hcard hfree⟩
  simpa [hcard] using hlow

/-- On six vertices, if a `K₅`-free incidence-critical non-4-colorable graph has at least `13`
edges, then it has a degree-`5` vertex.

Source: new theorem from the degree window `[4,5]` plus handshaking: if no degree is `5`, then all
degrees are at most `4`, forcing total degree at most `24`, contradicting `|E| ≥ 13` (total degree
at least `26`). -/
theorem IsIncidenceCriticalNonColorable.exists_degree_eq_five_of_card_edgeFinset_ge_thirteen
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 6) (hfree : G.CliqueFree 5)
    (hedge : 13 ≤ G.edgeFinset.card) :
    ∃ v : V, G.degree v = 5 := by
  by_contra hno
  have hle4 : ∀ v : V, G.degree v ≤ 4 := by
    intro v
    rcases h.degree_window_of_card_eq_six_of_cliqueFree hcard hfree v with ⟨_, hle5⟩
    have hne5 : G.degree v ≠ 5 := by
      intro hv5
      exact hno ⟨v, hv5⟩
    exact Nat.lt_succ_iff.mp (lt_of_le_of_ne hle5 (by simpa using hne5))
  have hsum_le24 : (∑ v : V, G.degree v) ≤ 24 := by
    calc
      (∑ v : V, G.degree v) ≤ ∑ _ : V, 4 := by
        exact Finset.sum_le_sum (fun v hv => hle4 v)
      _ = 4 * Fintype.card V := by simp [Nat.mul_comm]
      _ = 24 := by simp [hcard]
  have hsum_ge26 : 26 ≤ (∑ v : V, G.degree v) := by
    calc
      26 = 2 * 13 := by decide
      _ ≤ 2 * G.edgeFinset.card := Nat.mul_le_mul_left 2 hedge
      _ = ∑ v : V, G.degree v := by
        simpa [Nat.mul_comm] using (G.sum_degrees_eq_twice_card_edges).symm
  have : 26 ≤ 24 := le_trans hsum_ge26 hsum_le24
  exact (by decide : ¬ (26 ≤ 24)) this

/-- On six vertices, edge count `14` in a `K₅`-free incidence-critical non-4-colorable graph
forces a degree-`5` vertex.

Source: new specialization of the previous theorem. -/
theorem IsIncidenceCriticalNonColorable.exists_degree_eq_five_of_card_edgeFinset_eq_fourteen
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 6) (hfree : G.CliqueFree 5)
    (hedge : G.edgeFinset.card = 14) :
    ∃ v : V, G.degree v = 5 := by
  have h13 : 13 ≤ G.edgeFinset.card := by
    rw [hedge]
    decide
  exact h.exists_degree_eq_five_of_card_edgeFinset_ge_thirteen hcard hfree h13

/-- On six vertices, a `K₅`-free incidence-critical non-4-colorable graph with exactly `14` edges
has two distinct degree-`5` vertices.

Source: new theorem from one degree-`5` witness plus handshaking and the degree window `[4,5]`. -/
theorem IsIncidenceCriticalNonColorable.exists_distinct_degree_eq_five_of_card_edgeFinset_eq_fourteen
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 6) (hfree : G.CliqueFree 5)
    (hedge : G.edgeFinset.card = 14) :
    ∃ u v : V, u ≠ v ∧ G.degree u = 5 ∧ G.degree v = 5 := by
  rcases h.exists_degree_eq_five_of_card_edgeFinset_eq_fourteen hcard hfree hedge with ⟨v0, hv0⟩
  have hother : ∃ v : V, v ≠ v0 ∧ G.degree v = 5 := by
    by_contra hnone
    have hnone' : ∀ v : V, v ≠ v0 → G.degree v ≠ 5 := by
      intro v hv
      intro hv5
      exact hnone ⟨v, hv, hv5⟩
    have hsum_erase_le20 :
        Finset.sum (Finset.univ.erase v0) (fun v => G.degree v) ≤ 20 := by
      have hv0_mem : v0 ∈ Finset.univ := by simp
      have hcard_erase : (Finset.univ.erase v0).card = 5 := by
        rw [Finset.card_erase_of_mem hv0_mem, Finset.card_univ, hcard]
      calc
        Finset.sum (Finset.univ.erase v0) (fun v => G.degree v)
            ≤ Finset.sum (Finset.univ.erase v0) (fun _ => 4) := by
              refine Finset.sum_le_sum ?_
              intro v hv
              have hv_ne : v ≠ v0 := (Finset.mem_erase.mp hv).1
              rcases h.degree_window_of_card_eq_six_of_cliqueFree hcard hfree v with ⟨_, hle5⟩
              have hne5 : G.degree v ≠ 5 := hnone' v hv_ne
              exact Nat.lt_succ_iff.mp (lt_of_le_of_ne hle5 (by simpa using hne5))
        _ = 4 * (Finset.univ.erase v0).card := by simp [Nat.mul_comm]
        _ = 20 := by rw [hcard_erase]
    have hsum_le25 : Finset.sum Finset.univ (fun v => G.degree v) ≤ 25 := by
      have hsplit :
          G.degree v0 + Finset.sum (Finset.univ.erase v0) (fun v => G.degree v) =
            Finset.sum Finset.univ (fun v => G.degree v) := by
        simpa using (Finset.add_sum_erase (s := Finset.univ) (f := fun v => G.degree v) (by simp))
      calc
        Finset.sum Finset.univ (fun v => G.degree v)
            = G.degree v0 + Finset.sum (Finset.univ.erase v0) (fun v => G.degree v) := by
              simpa using hsplit.symm
        _ = 5 + Finset.sum (Finset.univ.erase v0) (fun v => G.degree v) := by rw [hv0]
        _ ≤ 5 + 20 := Nat.add_le_add_left hsum_erase_le20 5
        _ = 25 := by decide
    have hsum_eq28 : Finset.sum Finset.univ (fun v => G.degree v) = 28 := by
      calc
        Finset.sum Finset.univ (fun v => G.degree v) = ∑ v : V, G.degree v := by simp
        _ = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
        _ = 28 := by rw [hedge]
    have hsum_le25' : 28 ≤ 25 := by
      have htmp : Finset.sum Finset.univ (fun v => G.degree v) ≤ 25 := hsum_le25
      rwa [hsum_eq28] at htmp
    exact (by decide : ¬ (28 ≤ 25)) hsum_le25'
  rcases hother with ⟨v1, hv1ne, hv1⟩
  exact ⟨v0, v1, hv1ne.symm, hv0, hv1⟩

/-- On six vertices, a degree-`5` vertex in a `K₅`-free incidence-critical non-4-colorable graph
forces at least `13` edges.

Source: new theorem from handshaking and the degree window `[4,5]`. -/
theorem IsIncidenceCriticalNonColorable.card_edgeFinset_ge_thirteen_of_exists_degree_eq_five
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 6) (hfree : G.CliqueFree 5)
    (hdeg5 : ∃ v : V, G.degree v = 5) :
    13 ≤ G.edgeFinset.card := by
  rcases hdeg5 with ⟨v0, hv0⟩
  have hsum_erase_ge20 : 20 ≤ Finset.sum (Finset.univ.erase v0) (fun v => G.degree v) := by
    have hv0_mem : v0 ∈ Finset.univ := by simp
    have hcard_erase : (Finset.univ.erase v0).card = 5 := by
      rw [Finset.card_erase_of_mem hv0_mem, Finset.card_univ, hcard]
    calc
      20 = 4 * (Finset.univ.erase v0).card := by
        rw [hcard_erase]
      _ = Finset.sum (Finset.univ.erase v0) (fun _ => 4) := by simp [Nat.mul_comm]
      _ ≤ Finset.sum (Finset.univ.erase v0) (fun v => G.degree v) := by
        refine Finset.sum_le_sum ?_
        intro v hv
        exact (h.degree_window_of_card_eq_six_of_cliqueFree hcard hfree v).1
  have hsum_ge25 : 25 ≤ Finset.sum Finset.univ (fun v => G.degree v) := by
    have hsplit :
        G.degree v0 + Finset.sum (Finset.univ.erase v0) (fun v => G.degree v) =
          Finset.sum Finset.univ (fun v => G.degree v) := by
      simpa using (Finset.add_sum_erase (s := Finset.univ) (f := fun v => G.degree v) (by simp))
    calc
      25 = 5 + 20 := by decide
      _ ≤ G.degree v0 + Finset.sum (Finset.univ.erase v0) (fun v => G.degree v) := by
        exact Nat.add_le_add (by simp [hv0]) hsum_erase_ge20
      _ = Finset.sum Finset.univ (fun v => G.degree v) := hsplit
  have h2e_ge25 : 25 ≤ 2 * G.edgeFinset.card := by
    calc
      25 ≤ Finset.sum Finset.univ (fun v => G.degree v) := hsum_ge25
      _ = ∑ v : V, G.degree v := by simp
      _ = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
  by_contra h13
  have he_lt13 : G.edgeFinset.card < 13 := Nat.lt_of_not_ge h13
  have he_le12 : G.edgeFinset.card ≤ 12 := Nat.lt_succ_iff.mp he_lt13
  have h2e_le24 : 2 * G.edgeFinset.card ≤ 24 := by
    calc
      2 * G.edgeFinset.card ≤ 2 * 12 := Nat.mul_le_mul_left 2 he_le12
      _ = 24 := by decide
  have : 25 ≤ 24 := le_trans h2e_ge25 h2e_le24
  exact (by decide : ¬ (25 ≤ 24)) this

/-- On six vertices, in a `K₅`-free incidence-critical non-4-colorable graph with exactly `12`
edges, every vertex has degree `4`.

Source: new theorem from the degree window and exclusion of degree `5` by the previous bound. -/
theorem IsIncidenceCriticalNonColorable.degree_eq_four_of_card_edgeFinset_eq_twelve
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 6) (hfree : G.CliqueFree 5)
    (hedge : G.edgeFinset.card = 12) (v : V) :
    G.degree v = 4 := by
  rcases h.degree_window_of_card_eq_six_of_cliqueFree hcard hfree v with ⟨hge4, hle5⟩
  have hne5 : G.degree v ≠ 5 := by
    intro hv5
    have h13 : 13 ≤ G.edgeFinset.card :=
      h.card_edgeFinset_ge_thirteen_of_exists_degree_eq_five hcard hfree ⟨v, hv5⟩
    have hnot13 : ¬ (13 ≤ G.edgeFinset.card) := by simp [hedge]
    exact hnot13 h13
  have hle4 : G.degree v ≤ 4 :=
    Nat.lt_succ_iff.mp (lt_of_le_of_ne hle5 (by simpa using hne5))
  exact Nat.le_antisymm hle4 hge4

/-- On six vertices, a `K₅`-free incidence-critical non-4-colorable graph with exactly `13` edges
has two distinct degree-`5` vertices.

Source: new theorem from the degree window `[4,5]` plus handshaking. -/
theorem IsIncidenceCriticalNonColorable.exists_distinct_degree_eq_five_of_card_edgeFinset_eq_thirteen
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 6) (hfree : G.CliqueFree 5)
    (hedge : G.edgeFinset.card = 13) :
    ∃ u v : V, u ≠ v ∧ G.degree u = 5 ∧ G.degree v = 5 := by
  have h13 : 13 ≤ G.edgeFinset.card := by simp [hedge]
  rcases h.exists_degree_eq_five_of_card_edgeFinset_ge_thirteen hcard hfree h13 with ⟨v0, hv0⟩
  have hother : ∃ v : V, v ≠ v0 ∧ G.degree v = 5 := by
    by_contra hnone
    have hnone' : ∀ v : V, v ≠ v0 → G.degree v ≠ 5 := by
      intro v hv
      intro hv5
      exact hnone ⟨v, hv, hv5⟩
    have hcard_erase : (Finset.univ.erase v0).card = 5 := by
      have hv0_mem : v0 ∈ Finset.univ := by simp
      rw [Finset.card_erase_of_mem hv0_mem, Finset.card_univ, hcard]
    have hsum_erase_le20 :
        Finset.sum (Finset.univ.erase v0) (fun v => G.degree v) ≤ 20 := by
      calc
        Finset.sum (Finset.univ.erase v0) (fun v => G.degree v)
            ≤ Finset.sum (Finset.univ.erase v0) (fun _ => 4) := by
              refine Finset.sum_le_sum ?_
              intro v hv
              have hv_ne : v ≠ v0 := (Finset.mem_erase.mp hv).1
              rcases h.degree_window_of_card_eq_six_of_cliqueFree hcard hfree v with ⟨_, hle5⟩
              have hne5 : G.degree v ≠ 5 := hnone' v hv_ne
              exact Nat.lt_succ_iff.mp (lt_of_le_of_ne hle5 (by simpa using hne5))
        _ = 4 * (Finset.univ.erase v0).card := by simp [Nat.mul_comm]
        _ = 20 := by rw [hcard_erase]
    have hsum_le25 : Finset.sum Finset.univ (fun v => G.degree v) ≤ 25 := by
      have hsplit :
          G.degree v0 + Finset.sum (Finset.univ.erase v0) (fun v => G.degree v) =
            Finset.sum Finset.univ (fun v => G.degree v) := by
        simpa using (Finset.add_sum_erase (s := Finset.univ) (f := fun v => G.degree v) (by simp))
      calc
        Finset.sum Finset.univ (fun v => G.degree v)
            = G.degree v0 + Finset.sum (Finset.univ.erase v0) (fun v => G.degree v) := by
              simpa using hsplit.symm
        _ = 5 + Finset.sum (Finset.univ.erase v0) (fun v => G.degree v) := by rw [hv0]
        _ ≤ 5 + 20 := Nat.add_le_add_left hsum_erase_le20 5
        _ = 25 := by decide
    have hsum_eq26 : Finset.sum Finset.univ (fun v => G.degree v) = 26 := by
      calc
        Finset.sum Finset.univ (fun v => G.degree v) = ∑ v : V, G.degree v := by simp
        _ = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
        _ = 26 := by rw [hedge]
    have hsum_le25' : 26 ≤ 25 := by
      have htmp : Finset.sum Finset.univ (fun v => G.degree v) ≤ 25 := hsum_le25
      rwa [hsum_eq26] at htmp
    exact (by decide : ¬ (26 ≤ 25)) hsum_le25'
  rcases hother with ⟨v1, hv1ne, hv1⟩
  exact ⟨v0, v1, hv1ne.symm, hv0, hv1⟩

/-- On six vertices, once two distinct degree-`5` vertices are fixed in the `|E| = 13` branch,
every other vertex has degree `4`.

Source: new theorem from the degree window `[4,5]` plus handshaking: a third degree-`5` vertex
would force total degree at least `27`, contradicting `2|E| = 26`. -/
theorem IsIncidenceCriticalNonColorable.degree_eq_four_of_card_edgeFinset_eq_thirteen_of_distinct_degree_eq_five
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 6) (hfree : G.CliqueFree 5)
    (hedge : G.edgeFinset.card = 13)
    {u v w : V} (huv : u ≠ v) (hwu : w ≠ u) (hwv : w ≠ v)
    (hu5 : G.degree u = 5) (hv5 : G.degree v = 5) :
    G.degree w = 4 := by
  rcases h.degree_window_of_card_eq_six_of_cliqueFree hcard hfree w with ⟨hge4, hle5⟩
  have hw4_or_5 : G.degree w = 4 ∨ G.degree w = 5 := by
    rcases Nat.lt_or_eq_of_le hle5 with hlt5 | hw5
    · left
      exact Nat.le_antisymm (Nat.lt_succ_iff.mp hlt5) hge4
    · right
      exact hw5
  rcases hw4_or_5 with hw4 | hw5
  · exact hw4
  · have hu_mem : u ∈ Finset.univ := by simp
    have hv_mem : v ∈ Finset.univ.erase u := by simpa using huv.symm
    have hw_mem : w ∈ (Finset.univ.erase u).erase v := by simp [hwu, hwv]
    let rest : Finset V := ((Finset.univ.erase u).erase v).erase w
    have hcard_rest : rest.card = 3 := by
      unfold rest
      rw [Finset.card_erase_of_mem hw_mem, Finset.card_erase_of_mem hv_mem,
        Finset.card_erase_of_mem hu_mem, Finset.card_univ, hcard]
    have hsum_rest_ge12 : 12 ≤ rest.sum (fun x => G.degree x) := by
      calc
        12 = 4 * rest.card := by rw [hcard_rest]
        _ = rest.sum (fun _ => 4) := by simp [Nat.mul_comm]
        _ ≤ rest.sum (fun x => G.degree x) := by
          refine Finset.sum_le_sum ?_
          intro x hx
          exact (h.degree_window_of_card_eq_six_of_cliqueFree hcard hfree x).1
    have hsplit_w :
        G.degree w + rest.sum (fun x => G.degree x) =
          ((Finset.univ.erase u).erase v).sum (fun x => G.degree x) := by
      unfold rest
      simpa using
        (Finset.add_sum_erase (s := (Finset.univ.erase u).erase v) (f := fun x => G.degree x) hw_mem)
    have hsplit_v :
        G.degree v + ((Finset.univ.erase u).erase v).sum (fun x => G.degree x) =
          (Finset.univ.erase u).sum (fun x => G.degree x) := by
      simpa using
        (Finset.add_sum_erase (s := Finset.univ.erase u) (f := fun x => G.degree x) hv_mem)
    have hsplit_u :
        G.degree u + (Finset.univ.erase u).sum (fun x => G.degree x) =
          Finset.sum Finset.univ (fun x => G.degree x) := by
      simpa using
        (Finset.add_sum_erase (s := Finset.univ) (f := fun x => G.degree x) hu_mem)
    have hsum_ge27 : 27 ≤ Finset.sum Finset.univ (fun x => G.degree x) := by
      have hbase :
          5 + (5 + (5 + 12)) ≤
            G.degree u + (G.degree v + (G.degree w + rest.sum (fun x => G.degree x))) := by
        exact Nat.add_le_add (by simp [hu5]) <|
          Nat.add_le_add (by simp [hv5]) <|
            Nat.add_le_add (by simp [hw5]) hsum_rest_ge12
      calc
        27 = 5 + (5 + (5 + 12)) := by decide
        _ ≤ G.degree u + (G.degree v + (G.degree w + rest.sum (fun x => G.degree x))) := hbase
        _ = G.degree u + (G.degree v + ((Finset.univ.erase u).erase v).sum (fun x => G.degree x)) := by
          rw [hsplit_w]
        _ = G.degree u + (Finset.univ.erase u).sum (fun x => G.degree x) := by
          rw [hsplit_v]
        _ = Finset.sum Finset.univ (fun x => G.degree x) := hsplit_u
    have hsum_eq26 : Finset.sum Finset.univ (fun x => G.degree x) = 26 := by
      calc
        Finset.sum Finset.univ (fun x => G.degree x) = ∑ x : V, G.degree x := by simp
        _ = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
        _ = 26 := by rw [hedge]
    have : 27 ≤ 26 := by
      have htmp : 27 ≤ Finset.sum Finset.univ (fun x => G.degree x) := hsum_ge27
      rwa [hsum_eq26] at htmp
    exact False.elim ((by decide : ¬ (27 ≤ 26)) this)

/-- On six vertices, the `|E| = 13` branch has the exact degree pattern: two vertices of degree
`5`, and every other vertex has degree `4`.

Source: new theorem from the previous existence theorem plus the exclusion of a third degree-`5`
vertex. -/
theorem IsIncidenceCriticalNonColorable.exists_distinct_degree_eq_five_forall_degree_eq_four_else_of_card_edgeFinset_eq_thirteen
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 6) (hfree : G.CliqueFree 5)
    (hedge : G.edgeFinset.card = 13) :
    ∃ u v : V, u ≠ v ∧ G.degree u = 5 ∧ G.degree v = 5 ∧
      ∀ w : V, w ≠ u → w ≠ v → G.degree w = 4 := by
  rcases h.exists_distinct_degree_eq_five_of_card_edgeFinset_eq_thirteen hcard hfree hedge with
    ⟨u, v, huv, hu5, hv5⟩
  refine ⟨u, v, huv, hu5, hv5, ?_⟩
  intro w hwu hwv
  exact h.degree_eq_four_of_card_edgeFinset_eq_thirteen_of_distinct_degree_eq_five
    hcard hfree hedge huv hwu hwv hu5 hv5

end IncidenceBranch

section VertexBranch

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- On six vertices, any vertex-critical non-4-colorable graph has at least `12` edges.

Source: new theorem via the vertex-to-incidence bridge. -/
theorem IsVertexCriticalNonColorable.card_edgeFinset_ge_twelve_of_card_eq_six
    (h : IsVertexCriticalNonColorable G 4) (hcard : Fintype.card V = 6) :
    12 ≤ G.edgeFinset.card :=
  h.toIncidenceCritical_four.card_edgeFinset_ge_twelve_of_card_eq_six hcard

/-- On six vertices, a `K₅`-free vertex-critical non-4-colorable graph has at most `14` edges.

Source: new theorem via the vertex-to-incidence bridge. -/
theorem IsVertexCriticalNonColorable.card_edgeFinset_le_fourteen_of_card_eq_six_of_cliqueFree
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 6) (hfree : G.CliqueFree 5) :
    G.edgeFinset.card ≤ 14 :=
  h.toIncidenceCritical_four.card_edgeFinset_le_fourteen_of_card_eq_six_of_cliqueFree hcard hfree

/-- On six vertices, a `K₅`-free vertex-critical non-4-colorable graph has edge count in `[12,14]`.

Source: new theorem via the vertex-to-incidence bridge. -/
theorem IsVertexCriticalNonColorable.card_edgeFinset_window_of_card_eq_six_of_cliqueFree
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 6) (hfree : G.CliqueFree 5) :
    12 ≤ G.edgeFinset.card ∧ G.edgeFinset.card ≤ 14 :=
  h.toIncidenceCritical_four.card_edgeFinset_window_of_card_eq_six_of_cliqueFree hcard hfree

/-- On six vertices, a `K₅`-free vertex-critical non-4-colorable graph has at most `13` edges.

Source: new theorem via the vertex-to-incidence bridge, using Turán's bound. -/
theorem IsVertexCriticalNonColorable.card_edgeFinset_le_thirteen_of_card_eq_six_of_cliqueFree
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 6) (hfree : G.CliqueFree 5) :
    G.edgeFinset.card ≤ 13 :=
  h.toIncidenceCritical_four.card_edgeFinset_le_thirteen_of_card_eq_six_of_cliqueFree hcard hfree

/-- On six vertices, a `K₅`-free vertex-critical non-4-colorable graph has edge count in `[12,13]`.

Source: new theorem via the vertex-to-incidence bridge. -/
theorem IsVertexCriticalNonColorable.card_edgeFinset_window_twelve_thirteen_of_card_eq_six_of_cliqueFree
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 6) (hfree : G.CliqueFree 5) :
    12 ≤ G.edgeFinset.card ∧ G.edgeFinset.card ≤ 13 :=
  h.toIncidenceCritical_four.card_edgeFinset_window_twelve_thirteen_of_card_eq_six_of_cliqueFree
    hcard hfree

/-- On six vertices, `|E| = 14` is impossible for `K₅`-free vertex-critical non-4-colorable graphs.

Source: new theorem via the vertex-to-incidence bridge. -/
theorem IsVertexCriticalNonColorable.card_edgeFinset_ne_fourteen_of_card_eq_six_of_cliqueFree
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 6) (hfree : G.CliqueFree 5) :
    G.edgeFinset.card ≠ 14 :=
  h.toIncidenceCritical_four.card_edgeFinset_ne_fourteen_of_card_eq_six_of_cliqueFree hcard hfree

/-- On six vertices, if a `K₅`-free vertex-critical non-4-colorable graph has at least `13` edges,
then it has a degree-`5` vertex.

Source: new theorem via the vertex-to-incidence bridge. -/
theorem IsVertexCriticalNonColorable.exists_degree_eq_five_of_card_edgeFinset_ge_thirteen
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 6) (hfree : G.CliqueFree 5)
    (hedge : 13 ≤ G.edgeFinset.card) :
    ∃ v : V, G.degree v = 5 :=
  h.toIncidenceCritical_four.exists_degree_eq_five_of_card_edgeFinset_ge_thirteen hcard hfree hedge

/-- On six vertices, edge count `14` in a `K₅`-free vertex-critical non-4-colorable graph forces a
degree-`5` vertex.

Source: new theorem via the vertex-to-incidence bridge. -/
theorem IsVertexCriticalNonColorable.exists_degree_eq_five_of_card_edgeFinset_eq_fourteen
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 6) (hfree : G.CliqueFree 5)
    (hedge : G.edgeFinset.card = 14) :
    ∃ v : V, G.degree v = 5 :=
  h.toIncidenceCritical_four.exists_degree_eq_five_of_card_edgeFinset_eq_fourteen hcard hfree hedge

/-- On six vertices, a `K₅`-free vertex-critical non-4-colorable graph with exactly `14` edges has
two distinct degree-`5` vertices.

Source: new theorem via the vertex-to-incidence bridge. -/
theorem IsVertexCriticalNonColorable.exists_distinct_degree_eq_five_of_card_edgeFinset_eq_fourteen
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 6) (hfree : G.CliqueFree 5)
    (hedge : G.edgeFinset.card = 14) :
    ∃ u v : V, u ≠ v ∧ G.degree u = 5 ∧ G.degree v = 5 :=
  h.toIncidenceCritical_four.exists_distinct_degree_eq_five_of_card_edgeFinset_eq_fourteen
    hcard hfree hedge

/-- On six vertices, a degree-`5` vertex in a `K₅`-free vertex-critical non-4-colorable graph
forces at least `13` edges.

Source: new theorem via the vertex-to-incidence bridge. -/
theorem IsVertexCriticalNonColorable.card_edgeFinset_ge_thirteen_of_exists_degree_eq_five
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 6) (hfree : G.CliqueFree 5)
    (hdeg5 : ∃ v : V, G.degree v = 5) :
    13 ≤ G.edgeFinset.card :=
  h.toIncidenceCritical_four.card_edgeFinset_ge_thirteen_of_exists_degree_eq_five hcard hfree hdeg5

/-- On six vertices, in a `K₅`-free vertex-critical non-4-colorable graph with exactly `12` edges,
every vertex has degree `4`.

Source: new theorem via the vertex-to-incidence bridge. -/
theorem IsVertexCriticalNonColorable.degree_eq_four_of_card_edgeFinset_eq_twelve
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 6) (hfree : G.CliqueFree 5)
    (hedge : G.edgeFinset.card = 12) (v : V) :
    G.degree v = 4 :=
  h.toIncidenceCritical_four.degree_eq_four_of_card_edgeFinset_eq_twelve hcard hfree hedge v

/-- On six vertices, a `K₅`-free vertex-critical non-4-colorable graph with exactly `13` edges has
two distinct degree-`5` vertices.

Source: new theorem via the vertex-to-incidence bridge. -/
theorem IsVertexCriticalNonColorable.exists_distinct_degree_eq_five_of_card_edgeFinset_eq_thirteen
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 6) (hfree : G.CliqueFree 5)
    (hedge : G.edgeFinset.card = 13) :
    ∃ u v : V, u ≠ v ∧ G.degree u = 5 ∧ G.degree v = 5 :=
  h.toIncidenceCritical_four.exists_distinct_degree_eq_five_of_card_edgeFinset_eq_thirteen
    hcard hfree hedge

end VertexBranch

section MinimalBranch

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- On six vertices, an edge-minimal non-4-colorable graph with no isolated vertices has at least
`12` edges.

Source: new theorem via the minimal-to-incidence bridge. -/
theorem IsMinimalNonColorable.card_edgeFinset_ge_twelve_of_card_eq_six_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 6) :
    12 ≤ G.edgeFinset.card :=
  (h.toIncidenceCritical hadj).card_edgeFinset_ge_twelve_of_card_eq_six hcard

/-- On six vertices, a `K₅`-free edge-minimal non-4-colorable graph with no isolated vertices has
at most `14` edges.

Source: new theorem via the minimal-to-incidence bridge. -/
theorem IsMinimalNonColorable.card_edgeFinset_le_fourteen_of_card_eq_six_of_cliqueFree_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 6) (hfree : G.CliqueFree 5) :
    G.edgeFinset.card ≤ 14 :=
  (h.toIncidenceCritical hadj).card_edgeFinset_le_fourteen_of_card_eq_six_of_cliqueFree hcard hfree

/-- On six vertices, a `K₅`-free edge-minimal non-4-colorable graph with no isolated vertices has
edge count in `[12,14]`.

Source: new theorem via the minimal-to-incidence bridge. -/
theorem IsMinimalNonColorable.card_edgeFinset_window_of_card_eq_six_of_cliqueFree_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 6) (hfree : G.CliqueFree 5) :
    12 ≤ G.edgeFinset.card ∧ G.edgeFinset.card ≤ 14 :=
  (h.toIncidenceCritical hadj).card_edgeFinset_window_of_card_eq_six_of_cliqueFree hcard hfree

/-- On six vertices, a `K₅`-free edge-minimal non-4-colorable graph with no isolated vertices has
at most `13` edges.

Source: new theorem via the minimal-to-incidence bridge, using Turán's bound. -/
theorem IsMinimalNonColorable.card_edgeFinset_le_thirteen_of_card_eq_six_of_cliqueFree_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 6) (hfree : G.CliqueFree 5) :
    G.edgeFinset.card ≤ 13 := by
  let _ := (inferInstance : DecidableEq V)
  exact (h.toIncidenceCritical hadj).card_edgeFinset_le_thirteen_of_card_eq_six_of_cliqueFree
    hcard hfree

/-- On six vertices, a `K₅`-free edge-minimal non-4-colorable graph with no isolated vertices has
edge count in `[12,13]`.

Source: new theorem via the minimal-to-incidence bridge. -/
theorem IsMinimalNonColorable.card_edgeFinset_window_twelve_thirteen_of_card_eq_six_of_cliqueFree_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 6) (hfree : G.CliqueFree 5) :
    12 ≤ G.edgeFinset.card ∧ G.edgeFinset.card ≤ 13 :=
  (h.toIncidenceCritical hadj).card_edgeFinset_window_twelve_thirteen_of_card_eq_six_of_cliqueFree
    hcard hfree

/-- On six vertices, `|E| = 14` is impossible for `K₅`-free edge-minimal non-4-colorable graphs
with no isolated vertices.

Source: new theorem via the minimal-to-incidence bridge. -/
theorem IsMinimalNonColorable.card_edgeFinset_ne_fourteen_of_card_eq_six_of_cliqueFree_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 6) (hfree : G.CliqueFree 5) :
    G.edgeFinset.card ≠ 14 := by
  let _ := (inferInstance : DecidableEq V)
  exact (h.toIncidenceCritical hadj).card_edgeFinset_ne_fourteen_of_card_eq_six_of_cliqueFree
    hcard hfree

/-- On six vertices, if a `K₅`-free edge-minimal non-4-colorable graph with no isolated vertices
has at least `13` edges, then it has a degree-`5` vertex.

Source: new theorem via the minimal-to-incidence bridge. -/
theorem IsMinimalNonColorable.exists_degree_eq_five_of_card_edgeFinset_ge_thirteen_of_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 6) (hfree : G.CliqueFree 5)
    (hedge : 13 ≤ G.edgeFinset.card) :
    ∃ v : V, G.degree v = 5 :=
  (h.toIncidenceCritical hadj).exists_degree_eq_five_of_card_edgeFinset_ge_thirteen hcard hfree hedge

/-- On six vertices, edge count `14` in a `K₅`-free edge-minimal non-4-colorable graph with no
isolated vertices forces a degree-`5` vertex.

Source: new theorem via the minimal-to-incidence bridge. -/
theorem IsMinimalNonColorable.exists_degree_eq_five_of_card_edgeFinset_eq_fourteen_of_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 6) (hfree : G.CliqueFree 5)
    (hedge : G.edgeFinset.card = 14) :
    ∃ v : V, G.degree v = 5 :=
  (h.toIncidenceCritical hadj).exists_degree_eq_five_of_card_edgeFinset_eq_fourteen hcard hfree hedge

/-- On six vertices, a `K₅`-free edge-minimal non-4-colorable graph with no isolated vertices and
exactly `14` edges has two distinct degree-`5` vertices.

Source: new theorem via the minimal-to-incidence bridge. -/
theorem IsMinimalNonColorable.exists_distinct_degree_eq_five_of_card_edgeFinset_eq_fourteen_of_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 6) (hfree : G.CliqueFree 5)
    (hedge : G.edgeFinset.card = 14) :
    ∃ u v : V, u ≠ v ∧ G.degree u = 5 ∧ G.degree v = 5 :=
  (h.toIncidenceCritical hadj).exists_distinct_degree_eq_five_of_card_edgeFinset_eq_fourteen
    hcard hfree hedge

/-- On six vertices, a degree-`5` vertex in a `K₅`-free edge-minimal non-4-colorable graph with no
isolated vertices forces at least `13` edges.

Source: new theorem via the minimal-to-incidence bridge. -/
theorem IsMinimalNonColorable.card_edgeFinset_ge_thirteen_of_exists_degree_eq_five_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 6) (hfree : G.CliqueFree 5)
    (hdeg5 : ∃ v : V, G.degree v = 5) :
    13 ≤ G.edgeFinset.card :=
  (h.toIncidenceCritical hadj).card_edgeFinset_ge_thirteen_of_exists_degree_eq_five hcard hfree hdeg5

/-- On six vertices, in a `K₅`-free edge-minimal non-4-colorable graph with no isolated vertices
and exactly `12` edges, every vertex has degree `4`.

Source: new theorem via the minimal-to-incidence bridge. -/
theorem IsMinimalNonColorable.degree_eq_four_of_card_edgeFinset_eq_twelve_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 6) (hfree : G.CliqueFree 5)
    (hedge : G.edgeFinset.card = 12) (v : V) :
    G.degree v = 4 :=
  (h.toIncidenceCritical hadj).degree_eq_four_of_card_edgeFinset_eq_twelve hcard hfree hedge v

/-- On six vertices, a `K₅`-free edge-minimal non-4-colorable graph with no isolated vertices and
exactly `13` edges has two distinct degree-`5` vertices.

Source: new theorem via the minimal-to-incidence bridge. -/
theorem IsMinimalNonColorable.exists_distinct_degree_eq_five_of_card_edgeFinset_eq_thirteen_of_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 6) (hfree : G.CliqueFree 5)
    (hedge : G.edgeFinset.card = 13) :
    ∃ u v : V, u ≠ v ∧ G.degree u = 5 ∧ G.degree v = 5 :=
  (h.toIncidenceCritical hadj).exists_distinct_degree_eq_five_of_card_edgeFinset_eq_thirteen
    hcard hfree hedge

end MinimalBranch

end FourColor.Curriculum.Actual
