import Mathlib.Combinatorics.SimpleGraph.FiveWheelLike

namespace FourColor.Curriculum.Actual

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Andrásfai-Erdős-Sós style coloring bound via Mathlib's `FiveWheelLike` development. -/
theorem colorable_of_cliqueFree_lt_minDegree
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ)
    (hfree : G.CliqueFree (r + 1))
    (hdeg : (3 * r - 4) * Fintype.card V / (3 * r - 1) < G.minDegree) :
    G.Colorable r :=
  SimpleGraph.colorable_of_cliqueFree_lt_minDegree (G := G) (r := r) hfree hdeg

/-- Contrapositive form: a non-`r`-colorable `K_{r+1}`-free graph has bounded minimum degree. -/
theorem minDegree_le_bound_of_cliqueFree_not_colorable
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ)
    (hfree : G.CliqueFree (r + 1))
    (hncol : ¬ G.Colorable r) :
    G.minDegree ≤ (3 * r - 4) * Fintype.card V / (3 * r - 1) := by
  by_contra hgt
  have hdeg : (3 * r - 4) * Fintype.card V / (3 * r - 1) < G.minDegree := Nat.lt_of_not_ge hgt
  exact hncol (colorable_of_cliqueFree_lt_minDegree G r hfree hdeg)

/-- Specialized AES corollary for four colors. -/
theorem colorable_four_of_cliqueFree_five_and_minDegree
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : G.CliqueFree 5)
    (hdeg : 8 * Fintype.card V / 11 < G.minDegree) :
    G.Colorable 4 := by
  simpa using colorable_of_cliqueFree_lt_minDegree G 4 hfree hdeg

/-- Four-color contrapositive under `K₅`-freeness. -/
theorem minDegree_le_eight_mul_card_div_eleven_of_cliqueFree_five_not_colorable_four
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : G.CliqueFree 5)
    (hncol : ¬ G.Colorable 4) :
    G.minDegree ≤ 8 * Fintype.card V / 11 := by
  simpa using minDegree_le_bound_of_cliqueFree_not_colorable G 4 hfree hncol

/-- A non-4-colorable graph either has a `K₅` obstruction or low minimum degree. -/
theorem not_colorable_four_forces_k5_or_low_minDegree
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hncol : ¬ G.Colorable 4) :
    ¬ G.CliqueFree 5 ∨ G.minDegree ≤ 8 * Fintype.card V / 11 := by
  by_cases hfree : G.CliqueFree 5
  · right
    exact minDegree_le_eight_mul_card_div_eleven_of_cliqueFree_five_not_colorable_four
      G hfree hncol
  · exact Or.inl hfree

/-- Equivalent `K₅`-copy formulation of the previous dichotomy. -/
theorem not_colorable_four_forces_k5_copy_or_low_minDegree
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hncol : ¬ G.Colorable 4) :
    ¬ (⊤ : SimpleGraph (Fin 5)).Free G ∨ G.minDegree ≤ 8 * Fintype.card V / 11 := by
  rcases not_colorable_four_forces_k5_or_low_minDegree G hncol with h | h
  · left
    intro hfree
    have hcf : G.CliqueFree 5 := (SimpleGraph.cliqueFree_iff_top_free (G := G) (β := Fin 5)).2 hfree
    exact h hcf
  · exact Or.inr h

/-- Embedding-level version of the non-4-colorable dichotomy. -/
theorem not_colorable_four_forces_k5_embedding_or_low_minDegree
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hncol : ¬ G.Colorable 4) :
    Nonempty (SimpleGraph.completeGraph (Fin 5) ↪g G) ∨
      G.minDegree ≤ 8 * Fintype.card V / 11 := by
  rcases not_colorable_four_forces_k5_or_low_minDegree G hncol with h | h
  · exact Or.inl ((SimpleGraph.not_cliqueFree_iff (G := G) 5).1 h)
  · exact Or.inr h

/-- High minimum degree + no `K₅` embedding forces 4-colorability. -/
theorem colorable_four_of_no_k5_embedding_and_minDegree
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hK5 : IsEmpty (SimpleGraph.completeGraph (Fin 5) ↪g G))
    (hdeg : 8 * Fintype.card V / 11 < G.minDegree) :
    G.Colorable 4 := by
  have hfree : G.CliqueFree 5 := (SimpleGraph.cliqueFree_iff (G := G) (n := 5)).2 hK5
  exact colorable_four_of_cliqueFree_five_and_minDegree G hfree hdeg

/-- High minimum degree + `K₅`-copy-freeness forces 4-colorability. -/
theorem colorable_four_of_top_fin5_free_and_minDegree
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : (⊤ : SimpleGraph (Fin 5)).Free G)
    (hdeg : 8 * Fintype.card V / 11 < G.minDegree) :
    G.Colorable 4 := by
  have hcf : G.CliqueFree 5 := (SimpleGraph.cliqueFree_iff_top_free (G := G) (β := Fin 5)).2 hfree
  exact colorable_four_of_cliqueFree_five_and_minDegree G hcf hdeg

/-- Contrapositive with explicit embedding premise. -/
theorem minDegree_le_bound_of_not_colorable_four_and_no_k5_embedding
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hncol : ¬ G.Colorable 4)
    (hK5 : IsEmpty (SimpleGraph.completeGraph (Fin 5) ↪g G)) :
    G.minDegree ≤ 8 * Fintype.card V / 11 := by
  have hfree : G.CliqueFree 5 := (SimpleGraph.cliqueFree_iff (G := G) (n := 5)).2 hK5
  exact minDegree_le_eight_mul_card_div_eleven_of_cliqueFree_five_not_colorable_four G hfree hncol

/-- If a graph is not 4-colorable and has high minimum degree, a `K₅` embedding must exist. -/
theorem exists_k5_embedding_of_not_colorable_four_and_large_minDegree
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hncol : ¬ G.Colorable 4)
    (hdeg : 8 * Fintype.card V / 11 < G.minDegree) :
    Nonempty (SimpleGraph.completeGraph (Fin 5) ↪g G) := by
  rcases not_colorable_four_forces_k5_embedding_or_low_minDegree G hncol with h | h
  · exact h
  · exact False.elim ((Nat.not_lt_of_ge h) hdeg)

/-- If a graph is not 4-colorable and has high minimum degree, it cannot be `K₅`-free. -/
theorem not_top_fin5_free_of_not_colorable_four_and_large_minDegree
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hncol : ¬ G.Colorable 4)
    (hdeg : 8 * Fintype.card V / 11 < G.minDegree) :
    ¬ (⊤ : SimpleGraph (Fin 5)).Free G := by
  rcases not_colorable_four_forces_k5_copy_or_low_minDegree G hncol with h | h
  · exact h
  · exact False.elim ((Nat.not_lt_of_ge h) hdeg)

end FourColor.Curriculum.Actual
