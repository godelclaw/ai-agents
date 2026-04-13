import FourColor.Curriculum.Actual.SevenVertexRefinedBounds
import FourColor.Curriculum.Actual.SupportReduction

namespace FourColor.Curriculum.Actual

section IncidenceBranch

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- On seven vertices, every degree is at most `6`. -/
theorem IsIncidenceCriticalNonColorable.degree_le_six_of_card_eq_seven
    (_h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (v : V) :
    G.degree v ≤ 6 := by
  have hlt : G.degree v < 7 := by
    simpa [hcard] using G.degree_lt_card_verts v
  exact Nat.lt_succ_iff.mp hlt

/-- In the seven-vertex `15`-edge branch, some vertex has degree `4`.

Source: new theorem from `minDegree ≥ 4` plus handshaking: if every degree were at least `5`, then
the total degree would be at least `35`, contradicting `2|E| = 30`. -/
theorem IsIncidenceCriticalNonColorable.exists_degree_eq_four_of_card_eq_seven_of_card_edgeFinset_eq_fifteen
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 15) :
    ∃ v, G.degree v = 4 := by
  by_contra hnone
  have hge5 : ∀ v : V, 5 ≤ G.degree v := by
    intro v
    have hge4 : 4 ≤ G.degree v := h.four_le_degree v
    have hne4 : G.degree v ≠ 4 := by
      intro hv4
      exact hnone ⟨v, hv4⟩
    exact Nat.succ_le_of_lt (lt_of_le_of_ne hge4 (by simpa [eq_comm] using hne4))
  have hsum_ge35 : 35 ≤ Finset.sum Finset.univ (fun v => G.degree v) := by
    calc
      35 = Finset.sum Finset.univ (fun _ : V => 5) := by
        simp [Finset.card_univ, hcard, Nat.mul_comm]
      _ ≤ Finset.sum Finset.univ (fun v => G.degree v) := by
        refine Finset.sum_le_sum ?_
        intro v hv
        exact hge5 v
  have hsum_eq30 : Finset.sum Finset.univ (fun v => G.degree v) = 30 := by
    calc
      Finset.sum Finset.univ (fun v => G.degree v) = ∑ v : V, G.degree v := by simp
      _ = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
      _ = 30 := by rw [hedge]
  have : 35 ≤ 30 := by
    have htmp : 35 ≤ Finset.sum Finset.univ (fun v => G.degree v) := hsum_ge35
    rwa [hsum_eq30] at htmp
  exact (by decide : ¬ (35 ≤ 30)) this

/-- In the seven-vertex `15`-edge branch, a degree-`6` vertex forces every other vertex to have
degree `4`.

Source: new theorem from handshaking: once one vertex contributes degree `6`, any second vertex of
degree at least `5` would force total degree at least `31`, contradicting `2|E| = 30`. -/
theorem IsIncidenceCriticalNonColorable.degree_eq_four_of_card_eq_seven_of_card_edgeFinset_eq_fifteen_of_degree_eq_six
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 15)
    {u w : V} (hwu : w ≠ u) (hu6 : G.degree u = 6) :
    G.degree w = 4 := by
  have hge4 : 4 ≤ G.degree w := h.four_le_degree w
  by_contra hne4
  have hge5 : 5 ≤ G.degree w := by
    exact Nat.succ_le_of_lt (lt_of_le_of_ne hge4 (by simpa [eq_comm] using hne4))
  have hu_mem : u ∈ Finset.univ := by simp
  have hw_mem : w ∈ Finset.univ.erase u := by simp [hwu]
  let rest : Finset V := (Finset.univ.erase u).erase w
  have hcard_rest : rest.card = 5 := by
    unfold rest
    rw [Finset.card_erase_of_mem hw_mem, Finset.card_erase_of_mem hu_mem, Finset.card_univ, hcard]
  have hsum_rest_ge20 : 20 ≤ rest.sum (fun x => G.degree x) := by
    calc
      20 = 4 * rest.card := by rw [hcard_rest]
      _ = rest.sum (fun _ => 4) := by simp [Nat.mul_comm]
      _ ≤ rest.sum (fun x => G.degree x) := by
        refine Finset.sum_le_sum ?_
        intro x hx
        exact h.four_le_degree x
  have hsplit_w :
      G.degree w + rest.sum (fun x => G.degree x) =
        (Finset.univ.erase u).sum (fun x => G.degree x) := by
    unfold rest
    simpa using
      (Finset.add_sum_erase (s := Finset.univ.erase u) (f := fun x => G.degree x) hw_mem)
  have hsplit_u :
      G.degree u + (Finset.univ.erase u).sum (fun x => G.degree x) =
        Finset.sum Finset.univ (fun x => G.degree x) := by
    simpa using
      (Finset.add_sum_erase (s := Finset.univ) (f := fun x => G.degree x) hu_mem)
  have hsum_ge31 : 31 ≤ Finset.sum Finset.univ (fun x => G.degree x) := by
    calc
      31 = 6 + (5 + 20) := by decide
      _ ≤ G.degree u + (G.degree w + rest.sum (fun x => G.degree x)) := by
        exact Nat.add_le_add (by simp [hu6]) (Nat.add_le_add hge5 hsum_rest_ge20)
      _ = G.degree u + (Finset.univ.erase u).sum (fun x => G.degree x) := by
        rw [hsplit_w]
      _ = Finset.sum Finset.univ (fun x => G.degree x) := hsplit_u
  have hsum_eq30 : Finset.sum Finset.univ (fun x => G.degree x) = 30 := by
    calc
      Finset.sum Finset.univ (fun x => G.degree x) = ∑ x : V, G.degree x := by simp
      _ = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
      _ = 30 := by rw [hedge]
  have : 31 ≤ 30 := by
    have htmp : 31 ≤ Finset.sum Finset.univ (fun x => G.degree x) := hsum_ge31
    rwa [hsum_eq30] at htmp
  exact (by decide : ¬ (31 ≤ 30)) this

/-- In the seven-vertex `15`-edge branch, if no vertex has degree `6`, then some vertex has degree
`5`.

Source: new theorem from handshaking: without degree `6`, if every degree were at most `4`, then
the total degree would be at most `28`, contradicting `2|E| = 30`. -/
theorem IsIncidenceCriticalNonColorable.exists_degree_eq_five_of_card_eq_seven_of_card_edgeFinset_eq_fifteen_of_forall_degree_ne_six
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 15)
    (hno6 : ∀ v : V, G.degree v ≠ 6) :
    ∃ v, G.degree v = 5 := by
  by_contra hnone
  have hle4 : ∀ v : V, G.degree v ≤ 4 := by
    intro v
    by_contra hgt4
    have hge5 : 5 ≤ G.degree v := Nat.succ_le_of_lt (Nat.lt_of_not_ge hgt4)
    have hle6 : G.degree v ≤ 6 := h.degree_le_six_of_card_eq_seven hcard v
    have hdeg5_or_6 : G.degree v = 5 ∨ G.degree v = 6 := by
      rcases Nat.lt_or_eq_of_le hle6 with hlt6 | hEq6
      · left
        exact Nat.le_antisymm (Nat.lt_succ_iff.mp hlt6) hge5
      · right
        exact hEq6
    rcases hdeg5_or_6 with hv5 | hv6
    · exact hnone ⟨v, hv5⟩
    · exact hno6 v hv6
  have hsum_le28 : Finset.sum Finset.univ (fun v => G.degree v) ≤ 28 := by
    calc
      Finset.sum Finset.univ (fun v => G.degree v) ≤ Finset.sum Finset.univ (fun _ : V => 4) := by
        refine Finset.sum_le_sum ?_
        intro v hv
        exact hle4 v
      _ = 28 := by simp [Finset.card_univ, hcard, Nat.mul_comm]
  have hsum_eq30 : Finset.sum Finset.univ (fun v => G.degree v) = 30 := by
    calc
      Finset.sum Finset.univ (fun v => G.degree v) = ∑ v : V, G.degree v := by simp
      _ = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
      _ = 30 := by rw [hedge]
  have : 30 ≤ 28 := by
    have htmp : Finset.sum Finset.univ (fun v => G.degree v) ≤ 28 := hsum_le28
    rwa [hsum_eq30] at htmp
  exact (by decide : ¬ (30 ≤ 28)) this

/-- In the seven-vertex `15`-edge branch, if one vertex has degree `5` and no vertex has degree
`6`, then there is a second distinct vertex of degree `5`.

Source: new theorem from handshaking: otherwise the chosen degree-`5` vertex and six degree-`4`
vertices would give total degree at most `29`, contradicting `2|E| = 30`. -/
theorem IsIncidenceCriticalNonColorable.exists_distinct_degree_eq_five_of_card_eq_seven_of_card_edgeFinset_eq_fifteen_of_degree_eq_five_of_forall_degree_ne_six
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 15)
    (hno6 : ∀ v : V, G.degree v ≠ 6)
    {u : V} (hu5 : G.degree u = 5) :
    ∃ v, v ≠ u ∧ G.degree v = 5 := by
  by_contra hnone
  have hu_mem : u ∈ Finset.univ := by simp
  have hle4 : ∀ v ∈ Finset.univ.erase u, G.degree v ≤ 4 := by
    intro v hv
    by_contra hgt4
    have hge5 : 5 ≤ G.degree v := Nat.succ_le_of_lt (Nat.lt_of_not_ge hgt4)
    have hle6 : G.degree v ≤ 6 := h.degree_le_six_of_card_eq_seven hcard v
    have hdeg5_or_6 : G.degree v = 5 ∨ G.degree v = 6 := by
      rcases Nat.lt_or_eq_of_le hle6 with hlt6 | hEq6
      · left
        exact Nat.le_antisymm (Nat.lt_succ_iff.mp hlt6) hge5
      · right
        exact hEq6
    rcases hdeg5_or_6 with hv5 | hv6
    · exact hnone ⟨v, by simp at hv; exact hv, hv5⟩
    · exact hno6 v hv6
  have hsum_erase_le24 : (Finset.univ.erase u).sum (fun v => G.degree v) ≤ 24 := by
    calc
      (Finset.univ.erase u).sum (fun v => G.degree v) ≤ (Finset.univ.erase u).sum (fun _ : V => 4) := by
        refine Finset.sum_le_sum ?_
        intro v hv
        exact hle4 v hv
      _ = 24 := by
        simp [Finset.card_erase_of_mem hu_mem, Finset.card_univ, hcard, Nat.mul_comm]
  have hsplit_u :
      G.degree u + (Finset.univ.erase u).sum (fun v => G.degree v) =
        Finset.sum Finset.univ (fun v => G.degree v) := by
    simpa using
      (Finset.add_sum_erase (s := Finset.univ) (f := fun v => G.degree v) hu_mem)
  have hsum_le29 : Finset.sum Finset.univ (fun v => G.degree v) ≤ 29 := by
    calc
      Finset.sum Finset.univ (fun v => G.degree v)
          = G.degree u + (Finset.univ.erase u).sum (fun v => G.degree v) := by
            symm
            exact hsplit_u
      _ = 5 + (Finset.univ.erase u).sum (fun v => G.degree v) := by rw [hu5]
      _ ≤ 5 + 24 := Nat.add_le_add_left hsum_erase_le24 5
      _ = 29 := by decide
  have hsum_eq30 : Finset.sum Finset.univ (fun v => G.degree v) = 30 := by
    calc
      Finset.sum Finset.univ (fun v => G.degree v) = ∑ v : V, G.degree v := by simp
      _ = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
      _ = 30 := by rw [hedge]
  have : 30 ≤ 29 := by
    have htmp : Finset.sum Finset.univ (fun v => G.degree v) ≤ 29 := hsum_le29
    rwa [hsum_eq30] at htmp
  exact (by decide : ¬ (30 ≤ 29)) this

/-- In the seven-vertex `15`-edge branch, once two distinct degree-`5` vertices are fixed and no
vertex has degree `6`, every other vertex has degree `4`.

Source: new theorem from handshaking: a third vertex of degree at least `5` would force total
degree at least `31`, contradicting `2|E| = 30`. -/
theorem IsIncidenceCriticalNonColorable.degree_eq_four_of_card_eq_seven_of_card_edgeFinset_eq_fifteen_of_distinct_degree_eq_five_of_forall_degree_ne_six
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 15)
    (hno6 : ∀ x : V, G.degree x ≠ 6)
    {u v w : V} (huv : u ≠ v) (hwu : w ≠ u) (hwv : w ≠ v)
    (hu5 : G.degree u = 5) (hv5 : G.degree v = 5) :
    G.degree w = 4 := by
  have hge4 : 4 ≤ G.degree w := h.four_le_degree w
  by_contra hne4
  have hge5 : 5 ≤ G.degree w := by
    exact Nat.succ_le_of_lt (lt_of_le_of_ne hge4 (by simpa [eq_comm] using hne4))
  have hle6 : G.degree w ≤ 6 := h.degree_le_six_of_card_eq_seven hcard w
  have hwne6 : G.degree w ≠ 6 := hno6 w
  have hw5 : G.degree w = 5 := by
    rcases Nat.lt_or_eq_of_le hle6 with hlt6 | hEq6
    · exact Nat.le_antisymm (Nat.lt_succ_iff.mp hlt6) hge5
    · exact False.elim (hwne6 hEq6)
  have hu_mem : u ∈ Finset.univ := by simp
  have hv_mem : v ∈ Finset.univ.erase u := by simpa using huv.symm
  have hw_mem : w ∈ (Finset.univ.erase u).erase v := by simp [hwu, hwv]
  let rest : Finset V := ((Finset.univ.erase u).erase v).erase w
  have hcard_rest : rest.card = 4 := by
    unfold rest
    rw [Finset.card_erase_of_mem hw_mem, Finset.card_erase_of_mem hv_mem,
      Finset.card_erase_of_mem hu_mem, Finset.card_univ, hcard]
  have hsum_rest_ge16 : 16 ≤ rest.sum (fun x => G.degree x) := by
    calc
      16 = 4 * rest.card := by rw [hcard_rest]
      _ = rest.sum (fun _ => 4) := by simp [Nat.mul_comm]
      _ ≤ rest.sum (fun x => G.degree x) := by
        refine Finset.sum_le_sum ?_
        intro x hx
        exact h.four_le_degree x
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
  have hsum_ge31 : 31 ≤ Finset.sum Finset.univ (fun x => G.degree x) := by
    calc
      31 = 5 + (5 + (5 + 16)) := by decide
      _ ≤ G.degree u + (G.degree v + (G.degree w + rest.sum (fun x => G.degree x))) := by
        exact Nat.add_le_add (by simp [hu5]) <|
          Nat.add_le_add (by simp [hv5]) <|
            Nat.add_le_add (by simp [hw5]) hsum_rest_ge16
      _ = G.degree u + (G.degree v + ((Finset.univ.erase u).erase v).sum (fun x => G.degree x)) := by
        rw [hsplit_w]
      _ = G.degree u + (Finset.univ.erase u).sum (fun x => G.degree x) := by
        rw [hsplit_v]
      _ = Finset.sum Finset.univ (fun x => G.degree x) := hsplit_u
  have hsum_eq30 : Finset.sum Finset.univ (fun x => G.degree x) = 30 := by
    calc
      Finset.sum Finset.univ (fun x => G.degree x) = ∑ x : V, G.degree x := by simp
      _ = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
      _ = 30 := by rw [hedge]
  have : 31 ≤ 30 := by
    have htmp : 31 ≤ Finset.sum Finset.univ (fun x => G.degree x) := hsum_ge31
    rwa [hsum_eq30] at htmp
  exact (by decide : ¬ (31 ≤ 30)) this

/-- On seven vertices, the `|E| = 15` branch has an exact degree profile: either one vertex has
degree `6` and every other vertex has degree `4`, or two distinct vertices have degree `5` and
every other vertex has degree `4`.

Source: new theorem from the previous handshaking lemmas, giving a finite classification of the
live seven-vertex low-edge branch after excluding `|E| = 14`. -/
theorem IsIncidenceCriticalNonColorable.degree_profile_of_card_eq_seven_of_card_edgeFinset_eq_fifteen
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 15) :
    (∃ u : V, G.degree u = 6 ∧ ∀ w : V, w ≠ u → G.degree w = 4) ∨
      ∃ u v : V, u ≠ v ∧ G.degree u = 5 ∧ G.degree v = 5 ∧
        ∀ w : V, w ≠ u → w ≠ v → G.degree w = 4 := by
  by_cases hdeg6 : ∃ u : V, G.degree u = 6
  · rcases hdeg6 with ⟨u, hu6⟩
    exact Or.inl ⟨u, hu6, fun w hw => h.degree_eq_four_of_card_eq_seven_of_card_edgeFinset_eq_fifteen_of_degree_eq_six hcard hedge hw hu6⟩
  · have hno6 : ∀ v : V, G.degree v ≠ 6 := by
      intro v hv6
      exact hdeg6 ⟨v, hv6⟩
    rcases h.exists_degree_eq_five_of_card_eq_seven_of_card_edgeFinset_eq_fifteen_of_forall_degree_ne_six
      hcard hedge hno6 with ⟨u, hu5⟩
    rcases h.exists_distinct_degree_eq_five_of_card_eq_seven_of_card_edgeFinset_eq_fifteen_of_degree_eq_five_of_forall_degree_ne_six
      hcard hedge hno6 hu5 with ⟨v, hvu, hv5⟩
    refine Or.inr ⟨u, v, hvu.symm, hu5, hv5, ?_⟩
    intro w hwu hwv
    exact h.degree_eq_four_of_card_eq_seven_of_card_edgeFinset_eq_fifteen_of_distinct_degree_eq_five_of_forall_degree_ne_six
      hcard hedge hno6 hvu.symm hwu hwv hu5 hv5

end IncidenceBranch

section VertexBranch

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Vertex-critical lift of the seven-vertex `15`-edge degree profile classification. -/
theorem IsVertexCriticalNonColorable.degree_profile_of_card_eq_seven_of_card_edgeFinset_eq_fifteen
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 15) :
    (∃ u : V, G.degree u = 6 ∧ ∀ w : V, w ≠ u → G.degree w = 4) ∨
      ∃ u v : V, u ≠ v ∧ G.degree u = 5 ∧ G.degree v = 5 ∧
        ∀ w : V, w ≠ u → w ≠ v → G.degree w = 4 :=
  h.toIncidenceCritical_four.degree_profile_of_card_eq_seven_of_card_edgeFinset_eq_fifteen
    hcard hedge

end VertexBranch

section MinimalBranch

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Minimal-counterexample lift of the seven-vertex `15`-edge degree profile classification. -/
theorem IsMinimalNonColorable.degree_profile_of_card_eq_seven_of_card_edgeFinset_eq_fifteen_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 7) (hedge : G.edgeFinset.card = 15) :
    (∃ u : V, G.degree u = 6 ∧ ∀ w : V, w ≠ u → G.degree w = 4) ∨
      ∃ u v : V, u ≠ v ∧ G.degree u = 5 ∧ G.degree v = 5 ∧
        ∀ w : V, w ≠ u → w ≠ v → G.degree w = 4 :=
  (h.toIncidenceCritical hadj).degree_profile_of_card_eq_seven_of_card_edgeFinset_eq_fifteen
    hcard hedge

/-- Minimal-counterexample lift of the seven-vertex `15`-edge degree profile classification under
`K₅`-freeness without a separate no-isolated-vertices hypothesis. -/
theorem IsMinimalNonColorable.degree_profile_of_card_eq_seven_of_card_edgeFinset_eq_fifteen_of_cliqueFree
    (h : IsMinimalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) (hedge : G.edgeFinset.card = 15) :
    (∃ u : V, G.degree u = 6 ∧ ∀ w : V, w ≠ u → G.degree w = 4) ∨
      ∃ u v : V, u ≠ v ∧ G.degree u = 5 ∧ G.degree v = 5 ∧
        ∀ w : V, w ≠ u → w ≠ v → G.degree w = 4 := by
  have hadj : ∀ v : V, ∃ w, G.Adj v w :=
    h.forall_exists_adj_of_card_eq_seven_of_cliqueFree hcard hfree
  exact
    IsIncidenceCriticalNonColorable.degree_profile_of_card_eq_seven_of_card_edgeFinset_eq_fifteen
      (G := G) (h := h.toIncidenceCritical hadj) hcard hedge

end MinimalBranch

end FourColor.Curriculum.Actual
