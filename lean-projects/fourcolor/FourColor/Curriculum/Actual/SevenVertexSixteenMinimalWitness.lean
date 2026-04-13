import Mathlib.Data.Fintype.EquivFin
import FourColor.Curriculum.Actual.MinimalCounterexample
import FourColor.Curriculum.Actual.SevenVertexSixteenInhabited

namespace FourColor.Curriculum.Actual

private abbrev WitnessV := Fin 2 ⊕ Fin 5

private def witnessCycleColor : Fin 5 → Fin 4
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 1
  | 4 => 2

private def witnessCyclePathColor : Fin 5 → Fin 5 → Fin 4
  | 0, 0 => 0
  | 0, 1 => 0
  | 0, 2 => 0
  | 0, 3 => 1
  | 0, 4 => 1
  | 1, 0 => 1
  | 1, 1 => 0
  | 1, 2 => 0
  | 1, 3 => 0
  | 1, 4 => 1
  | 2, 0 => 1
  | 2, 1 => 1
  | 2, 2 => 0
  | 2, 3 => 0
  | 2, 4 => 0
  | 3, 0 => 0
  | 3, 1 => 1
  | 3, 2 => 1
  | 3, 3 => 0
  | 3, 4 => 0
  | 4, 0 => 0
  | 4, 1 => 0
  | 4, 2 => 1
  | 4, 3 => 1
  | 4, 4 => 0

private def witnessColorDeleteApexEdge : WitnessV → Fin 4
  | Sum.inl _ => 3
  | Sum.inr j => witnessCycleColor j

private def witnessColorDeleteJoin (i : Fin 2) (j : Fin 5) : WitnessV → Fin 4
  | Sum.inl k => if k = i then 3 else 2
  | Sum.inr k => if k = j then 3 else witnessCyclePathColor j k

private def witnessCycleEdgePathColor : Fin 5 → Fin 5 → Fin 4
  | 0, 0 => 0
  | 0, 1 => 0
  | 0, 2 => 0
  | 0, 3 => 1
  | 0, 4 => 1
  | 1, 0 => 1
  | 1, 1 => 1
  | 1, 2 => 0
  | 1, 3 => 0
  | 1, 4 => 0
  | 2, 0 => 0
  | 2, 1 => 0
  | 2, 2 => 1
  | 2, 3 => 1
  | 2, 4 => 0
  | 3, 0 => 1
  | 3, 1 => 0
  | 3, 2 => 0
  | 3, 3 => 0
  | 3, 4 => 1
  | 4, 0 => 0
  | 4, 1 => 1
  | 4, 2 => 1
  | 4, 3 => 0
  | 4, 4 => 0

private def witnessColorDeleteCycleEdge (t : Fin 5) : WitnessV → Fin 4
  | Sum.inl 0 => 2
  | Sum.inl 1 => 3
  | Sum.inr j => witnessCycleEdgePathColor t j

private theorem sevenVertexSixteenWitness_colorable_deleteApexEdge :
    (sevenVertexSixteenWitness.deleteEdges ({s(Sum.inl 0, Sum.inl 1)} : Set (Sym2 WitnessV))).Colorable 4 := by
  refine ⟨SimpleGraph.Coloring.mk witnessColorDeleteApexEdge ?_⟩
  intro x y hxy
  revert x y hxy
  decide

private theorem sevenVertexSixteenWitness_colorable_deleteApexEdge_symm :
    (sevenVertexSixteenWitness.deleteEdges ({s(Sum.inl 1, Sum.inl 0)} : Set (Sym2 WitnessV))).Colorable 4 := by
  convert sevenVertexSixteenWitness_colorable_deleteApexEdge using 1
  ext e
  simp [Sym2.eq_swap]

private theorem sevenVertexSixteenWitness_colorable_deleteJoin
    (i : Fin 2) (j : Fin 5) :
    (sevenVertexSixteenWitness.deleteEdges ({s(Sum.inl i, Sum.inr j)} : Set (Sym2 WitnessV))).Colorable 4 := by
  refine ⟨SimpleGraph.Coloring.mk (witnessColorDeleteJoin i j) ?_⟩
  intro x y hxy
  fin_cases i <;> fin_cases j <;> revert x y hxy <;> decide

private theorem sevenVertexSixteenWitness_colorable_deleteCycleEdge02 :
    (sevenVertexSixteenWitness.deleteEdges ({s(Sum.inr 0, Sum.inr 2)} : Set (Sym2 WitnessV))).Colorable 4 := by
  refine ⟨SimpleGraph.Coloring.mk (witnessColorDeleteCycleEdge 0) ?_⟩
  intro x y hxy
  revert x y hxy
  decide

private theorem sevenVertexSixteenWitness_colorable_deleteCycleEdge24 :
    (sevenVertexSixteenWitness.deleteEdges ({s(Sum.inr 2, Sum.inr 4)} : Set (Sym2 WitnessV))).Colorable 4 := by
  refine ⟨SimpleGraph.Coloring.mk (witnessColorDeleteCycleEdge 1) ?_⟩
  intro x y hxy
  revert x y hxy
  decide

private theorem sevenVertexSixteenWitness_colorable_deleteCycleEdge41 :
    (sevenVertexSixteenWitness.deleteEdges ({s(Sum.inr 4, Sum.inr 1)} : Set (Sym2 WitnessV))).Colorable 4 := by
  refine ⟨SimpleGraph.Coloring.mk (witnessColorDeleteCycleEdge 2) ?_⟩
  intro x y hxy
  revert x y hxy
  decide

private theorem sevenVertexSixteenWitness_colorable_deleteCycleEdge13 :
    (sevenVertexSixteenWitness.deleteEdges ({s(Sum.inr 1, Sum.inr 3)} : Set (Sym2 WitnessV))).Colorable 4 := by
  refine ⟨SimpleGraph.Coloring.mk (witnessColorDeleteCycleEdge 3) ?_⟩
  intro x y hxy
  revert x y hxy
  decide

private theorem sevenVertexSixteenWitness_colorable_deleteCycleEdge30 :
    (sevenVertexSixteenWitness.deleteEdges ({s(Sum.inr 3, Sum.inr 0)} : Set (Sym2 WitnessV))).Colorable 4 := by
  refine ⟨SimpleGraph.Coloring.mk (witnessColorDeleteCycleEdge 4) ?_⟩
  intro x y hxy
  revert x y hxy
  decide

private theorem sevenVertexSixteenWitness_colorable_deleteCycleEdge20 :
    (sevenVertexSixteenWitness.deleteEdges ({s(Sum.inr 2, Sum.inr 0)} : Set (Sym2 WitnessV))).Colorable 4 := by
  convert sevenVertexSixteenWitness_colorable_deleteCycleEdge02 using 1
  ext e
  simp [Sym2.eq_swap]

private theorem sevenVertexSixteenWitness_colorable_deleteCycleEdge03 :
    (sevenVertexSixteenWitness.deleteEdges ({s(Sum.inr 0, Sum.inr 3)} : Set (Sym2 WitnessV))).Colorable 4 := by
  convert sevenVertexSixteenWitness_colorable_deleteCycleEdge30 using 1
  ext e
  simp [Sym2.eq_swap]

private theorem sevenVertexSixteenWitness_colorable_deleteCycleEdge14 :
    (sevenVertexSixteenWitness.deleteEdges ({s(Sum.inr 1, Sum.inr 4)} : Set (Sym2 WitnessV))).Colorable 4 := by
  convert sevenVertexSixteenWitness_colorable_deleteCycleEdge41 using 1
  ext e
  simp [Sym2.eq_swap]

private theorem sevenVertexSixteenWitness_colorable_deleteCycleEdge31 :
    (sevenVertexSixteenWitness.deleteEdges ({s(Sum.inr 3, Sum.inr 1)} : Set (Sym2 WitnessV))).Colorable 4 := by
  convert sevenVertexSixteenWitness_colorable_deleteCycleEdge13 using 1
  ext e
  simp [Sym2.eq_swap]

private theorem sevenVertexSixteenWitness_colorable_deleteCycleEdge42 :
    (sevenVertexSixteenWitness.deleteEdges ({s(Sum.inr 4, Sum.inr 2)} : Set (Sym2 WitnessV))).Colorable 4 := by
  convert sevenVertexSixteenWitness_colorable_deleteCycleEdge24 using 1
  ext e
  simp [Sym2.eq_swap]

private theorem sevenVertexSixteenWitness_colorable_deleteJoin_symm
    (i : Fin 2) (j : Fin 5) :
    (sevenVertexSixteenWitness.deleteEdges ({s(Sum.inr j, Sum.inl i)} : Set (Sym2 WitnessV))).Colorable 4 := by
  convert sevenVertexSixteenWitness_colorable_deleteJoin i j using 1
  ext e
  simp [Sym2.eq_swap]

/-- Deleting any present edge from the concrete witness `K₂ ⋈ C₅` leaves a `4`-colorable graph.

Source: finite verification on the explicit seven-vertex witness. -/
theorem sevenVertexSixteenWitness_colorable_deleteEdge
    {u v : WitnessV} (huv : sevenVertexSixteenWitness.Adj u v) :
    (sevenVertexSixteenWitness.deleteEdges ({s(u, v)} : Set (Sym2 WitnessV))).Colorable 4 := by
  cases u with
  | inl i =>
      cases v with
      | inl j =>
          fin_cases i <;> fin_cases j
          · exact (False.elim <| sevenVertexSixteenWitness.loopless _ huv)
          · simpa using sevenVertexSixteenWitness_colorable_deleteApexEdge
          · simpa using sevenVertexSixteenWitness_colorable_deleteApexEdge_symm
          · exact (False.elim <| sevenVertexSixteenWitness.loopless _ huv)
      | inr j =>
          simpa using sevenVertexSixteenWitness_colorable_deleteJoin i j
  | inr i =>
      cases v with
      | inl j =>
          simpa using (sevenVertexSixteenWitness_colorable_deleteJoin_symm j i)
      | inr j =>
          fin_cases i <;> fin_cases j
          · exact (False.elim <| sevenVertexSixteenWitness.loopless _ huv)
          · have : ¬ sevenVertexSixteenWitness.Adj (Sum.inr 0) (Sum.inr 1) := by decide
            exact False.elim (this huv)
          · simpa using sevenVertexSixteenWitness_colorable_deleteCycleEdge02
          · simpa using sevenVertexSixteenWitness_colorable_deleteCycleEdge03
          · have : ¬ sevenVertexSixteenWitness.Adj (Sum.inr 0) (Sum.inr 4) := by decide
            exact False.elim (this huv)
          · have : ¬ sevenVertexSixteenWitness.Adj (Sum.inr 1) (Sum.inr 0) := by decide
            exact False.elim (this huv)
          · exact (False.elim <| sevenVertexSixteenWitness.loopless _ huv)
          · have : ¬ sevenVertexSixteenWitness.Adj (Sum.inr 1) (Sum.inr 2) := by decide
            exact False.elim (this huv)
          · simpa using sevenVertexSixteenWitness_colorable_deleteCycleEdge13
          · simpa using sevenVertexSixteenWitness_colorable_deleteCycleEdge14
          · simpa using sevenVertexSixteenWitness_colorable_deleteCycleEdge20
          · have : ¬ sevenVertexSixteenWitness.Adj (Sum.inr 2) (Sum.inr 1) := by decide
            exact False.elim (this huv)
          · exact (False.elim <| sevenVertexSixteenWitness.loopless _ huv)
          · have : ¬ sevenVertexSixteenWitness.Adj (Sum.inr 2) (Sum.inr 3) := by decide
            exact False.elim (this huv)
          · simpa using sevenVertexSixteenWitness_colorable_deleteCycleEdge24
          · simpa using sevenVertexSixteenWitness_colorable_deleteCycleEdge30
          · simpa using sevenVertexSixteenWitness_colorable_deleteCycleEdge31
          · have : ¬ sevenVertexSixteenWitness.Adj (Sum.inr 3) (Sum.inr 2) := by decide
            exact False.elim (this huv)
          · exact (False.elim <| sevenVertexSixteenWitness.loopless _ huv)
          · have : ¬ sevenVertexSixteenWitness.Adj (Sum.inr 3) (Sum.inr 4) := by decide
            exact False.elim (this huv)
          · have : ¬ sevenVertexSixteenWitness.Adj (Sum.inr 4) (Sum.inr 0) := by decide
            exact False.elim (this huv)
          · simpa using sevenVertexSixteenWitness_colorable_deleteCycleEdge41
          · simpa using sevenVertexSixteenWitness_colorable_deleteCycleEdge42
          · have : ¬ sevenVertexSixteenWitness.Adj (Sum.inr 4) (Sum.inr 3) := by decide
            exact False.elim (this huv)
          · exact (False.elim <| sevenVertexSixteenWitness.loopless _ huv)

/-- Deleting any nonempty set of present edges from the concrete witness leaves a `4`-colorable
graph.

Source: reduce to the single-edge deletion case and use coloring monotonicity under subgraphs. -/
theorem sevenVertexSixteenWitness_colorable_deleteEdges_of_subset_nonempty
    {s : Set (Sym2 WitnessV)}
    (hsub : s ⊆ sevenVertexSixteenWitness.edgeSet) (hsne : s.Nonempty) :
    (sevenVertexSixteenWitness.deleteEdges s).Colorable 4 := by
  classical
  rcases hsne with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | hf u v =>
      have huv : sevenVertexSixteenWitness.Adj u v := by
        simpa [SimpleGraph.mem_edgeSet] using hsub he
      have hsingle :
          (sevenVertexSixteenWitness.deleteEdges ({s(u, v)} : Set (Sym2 WitnessV))).Colorable 4 :=
        sevenVertexSixteenWitness_colorable_deleteEdge huv
      have hle :
          sevenVertexSixteenWitness.deleteEdges s ≤
            sevenVertexSixteenWitness.deleteEdges ({s(u, v)} : Set (Sym2 WitnessV)) := by
        apply SimpleGraph.deleteEdges_anti
        intro x hx
        have hx' : x = s(u, v) := by simpa using hx
        simpa [hx'] using he
      exact SimpleGraph.Colorable.mono_left hle hsingle

/-- The explicit seven-vertex witness `K₂ ⋈ C₅` is minimal non-`4`-colorable.

Source: the witness itself is non-`4`-colorable, and every strict subgraph misses at least one
edge, hence is contained in a corresponding edge-deleted witness graph, which is `4`-colorable. -/
theorem sevenVertexSixteenWitness_isMinimalNonColorable :
    IsMinimalNonColorable sevenVertexSixteenWitness 4 := by
  classical
  refine ⟨sevenVertexSixteenWitness_not_colorable_four, ?_⟩
  intro H hHG
  have hss : H.edgeFinset ⊂ sevenVertexSixteenWitness.edgeFinset :=
    (SimpleGraph.edgeFinset_ssubset_edgeFinset).2 hHG
  rcases Finset.exists_of_ssubset hss with ⟨e, heG, heH⟩
  have hsne : (sevenVertexSixteenWitness.edgeSet \ H.edgeSet).Nonempty := by
    refine ⟨e, ?_⟩
    exact ⟨(SimpleGraph.mem_edgeFinset).1 heG, by simpa [SimpleGraph.mem_edgeFinset] using heH⟩
  have hdel :
      (sevenVertexSixteenWitness.deleteEdges (sevenVertexSixteenWitness.edgeSet \ H.edgeSet)).Colorable 4 :=
    sevenVertexSixteenWitness_colorable_deleteEdges_of_subset_nonempty
      (hsub := by intro x hx; exact hx.1) hsne
  simpa [SimpleGraph.deleteEdges_sdiff_eq_of_le (le_of_lt hHG)] using hdel

/-- The concrete witness packages the exact seven-vertex `16`-edge frontier data together with
minimal non-`4`-colorability. -/
theorem sevenVertexSixteenWitness_minimal_package :
    Fintype.card WitnessV = 7 ∧
      sevenVertexSixteenWitness.edgeFinset.card = 16 ∧
      sevenVertexSixteenWitness.CliqueFree 5 ∧
      IsMinimalNonColorable sevenVertexSixteenWitness 4 := by
  exact ⟨sevenVertexSixteenWitness_card, sevenVertexSixteenWitness_card_edgeFinset,
    sevenVertexSixteenWitness_cliqueFree_five,
    sevenVertexSixteenWitness_isMinimalNonColorable⟩

section Transfer

variable {V : Type*} [Fintype V] [DecidableEq V]

private noncomputable def sevenVertexSixteenWitnessEquiv
    (hcard : Fintype.card V = 7) : V ≃ WitnessV :=
  Fintype.equivOfCardEq (hcard.trans sevenVertexSixteenWitness_card.symm)

/-- The transported seven-vertex witness remains minimal non-`4`-colorable on any seven-vertex
type.

Source: transport strict subgraphs back along the witness equivalence, apply the concrete minimal
witness theorem, then push the coloring forward again. -/
theorem sevenVertexSixteenWitnessOn_isMinimalNonColorable
    (hcard : Fintype.card V = 7) :
    IsMinimalNonColorable (sevenVertexSixteenWitnessOn (V := V) hcard) 4 := by
  classical
  let e := sevenVertexSixteenWitnessEquiv (V := V) hcard
  refine ⟨sevenVertexSixteenWitnessOn_not_colorable_four (V := V) hcard, ?_⟩
  intro H hHG
  let K : SimpleGraph WitnessV := H.map e.toEmbedding
  have hK_lt : K < sevenVertexSixteenWitness := by
    refine lt_of_le_of_ne ?_ ?_
    · have hmap :
          H.map e.toEmbedding ≤
            (sevenVertexSixteenWitnessOn (V := V) hcard).map e.toEmbedding :=
        SimpleGraph.map_monotone e.toEmbedding (le_of_lt hHG)
      have htarget :
          (sevenVertexSixteenWitnessOn (V := V) hcard).map e.toEmbedding =
            sevenVertexSixteenWitness := by
        have htrans : e.symm.toEmbedding.trans e.toEmbedding = Function.Embedding.refl _ := by
          ext x
          simp
        change (sevenVertexSixteenWitness.map e.symm.toEmbedding).map e.toEmbedding =
          sevenVertexSixteenWitness
        rw [SimpleGraph.map_map, htrans, SimpleGraph.map_id]
      simpa [K, htarget] using hmap
    · intro hEq
      have hEqComap :
          K.comap e.toEmbedding = sevenVertexSixteenWitness.comap e.toEmbedding := by
        exact congrArg (fun G => G.comap e.toEmbedding) hEq
      have hKcomap : K.comap e.toEmbedding = H := by
        simpa [K] using (SimpleGraph.comap_map_eq e.toEmbedding H)
      have hcomapEq :
          H = sevenVertexSixteenWitness.comap e.toEmbedding := by
        calc
          H = K.comap e.toEmbedding := hKcomap.symm
          _ = sevenVertexSixteenWitness.comap e.toEmbedding := hEqComap
      have : H = sevenVertexSixteenWitnessOn (V := V) hcard := by
        calc
          H = sevenVertexSixteenWitness.comap e.toEmbedding := hcomapEq
          _ = sevenVertexSixteenWitnessOn (V := V) hcard := by
                simpa [sevenVertexSixteenWitnessOn, e] using
                  (SimpleGraph.map_symm (G := sevenVertexSixteenWitness) e).symm
      exact hHG.ne this
  have hcolK : K.Colorable 4 :=
    sevenVertexSixteenWitness_isMinimalNonColorable.colorable_of_lt hK_lt
  exact
    SimpleGraph.Colorable.of_hom
      (SimpleGraph.Embedding.map e.toEmbedding H)
      (by simpa [K] using hcolK)

/-- On any seven-vertex type, there exists a `16`-edge `K₅`-free graph that is minimal
non-`4`-colorable. This is the minimal-counterexample witness for the repaired frontier. -/
theorem exists_sixteen_edge_cliqueFree_five_minimal_nonColorable_four_of_card_eq_seven
    (hcard : Fintype.card V = 7) :
    ∃ G : SimpleGraph V, ∃ _ : DecidableRel G.Adj,
      G.edgeFinset.card = 16 ∧
      G.CliqueFree 5 ∧
      IsMinimalNonColorable G 4 := by
  refine ⟨sevenVertexSixteenWitnessOn (V := V) hcard, inferInstance, ?_⟩
  exact
    ⟨sevenVertexSixteenWitnessOn_card_edgeFinset (V := V) hcard,
      sevenVertexSixteenWitnessOn_cliqueFree_five (V := V) hcard,
      sevenVertexSixteenWitnessOn_isMinimalNonColorable (V := V) hcard⟩

/-- The transported minimal witness can be packaged together with the no-isolated-vertices fact
needed by the minimal-to-incidence bridge. -/
theorem exists_sixteen_edge_cliqueFree_five_minimal_nonColorable_four_with_forall_exists_adj_of_card_eq_seven
    (hcard : Fintype.card V = 7) :
    ∃ G : SimpleGraph V, ∃ _ : DecidableRel G.Adj,
      G.edgeFinset.card = 16 ∧
      G.CliqueFree 5 ∧
      IsMinimalNonColorable G 4 ∧
      (∀ v : V, ∃ w, G.Adj v w) := by
  refine ⟨sevenVertexSixteenWitnessOn (V := V) hcard, inferInstance, ?_⟩
  refine ⟨sevenVertexSixteenWitnessOn_card_edgeFinset (V := V) hcard,
    sevenVertexSixteenWitnessOn_cliqueFree_five (V := V) hcard,
    sevenVertexSixteenWitnessOn_isMinimalNonColorable (V := V) hcard, ?_⟩
  intro v
  exact (sevenVertexSixteenWitnessOn_isVertexCriticalNonColorable (V := V) hcard).exists_adj v

end Transfer

end FourColor.Curriculum.Actual
