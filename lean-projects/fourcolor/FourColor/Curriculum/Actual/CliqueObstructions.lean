import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.ENat.Basic
import Mathlib.Data.Finset.Card

namespace FourColor.Curriculum.Actual

variable {V : Type*}

/-- Any subgraph of a 4-colorable graph is 4-colorable. -/
theorem colorable_four_of_subgraph
    {G H : SimpleGraph V} (hHG : H ≤ G) (hG : G.Colorable 4) :
    H.Colorable 4 :=
  SimpleGraph.Colorable.mono_left hHG hG

/-- Chromatic number is monotone under subgraph inclusion. -/
theorem chromaticNumber_mono_of_subgraph
    {G H : SimpleGraph V} (hHG : H ≤ G) :
    H.chromaticNumber ≤ G.chromaticNumber :=
  SimpleGraph.chromaticNumber_mono (G := H) (G' := G) hHG

/-- A 4-coloring gives the expected chromatic-number upper bound. -/
theorem colorable_four_implies_chromaticNumber_le_four
    (G : SimpleGraph V) (h4 : G.Colorable 4) :
    G.chromaticNumber ≤ 4 :=
  h4.chromaticNumber_le

/-- Characterization of 4-colorability via chromatic number. -/
theorem chromaticNumber_le_four_iff_colorable_four
    (G : SimpleGraph V) :
    G.chromaticNumber ≤ 4 ↔ G.Colorable 4 :=
  G.chromaticNumber_le_iff_colorable (n := 4)

/-- Every 4-colorable graph is `K₅`-free at the clique level. -/
theorem colorable_four_implies_cliqueFree_five
    (G : SimpleGraph V) (h4 : G.Colorable 4) :
    G.CliqueFree 5 :=
  h4.cliqueFree (by decide)

/-- `K₅`-copy freeness and 5-clique-freeness are equivalent. -/
theorem cliqueFree_five_iff_top_fin5_free
    (G : SimpleGraph V) :
    G.CliqueFree 5 ↔ (⊤ : SimpleGraph (Fin 5)).Free G := by
  simpa using (SimpleGraph.cliqueFree_iff_top_free (G := G) (β := Fin 5))

/-- Any finite clique in a 4-colorable graph has size at most `4`. -/
theorem clique_card_le_four_of_colorable_four
    (G : SimpleGraph V) (h4 : G.Colorable 4) {s : Finset V} (hs : G.IsClique s) :
    s.card ≤ 4 :=
  hs.card_le_of_colorable h4

/-- A concrete 5-clique witness obstructs 4-colorability. -/
theorem not_colorable_four_of_five_clique
    (G : SimpleGraph V)
    (hK5 : ∃ s : Finset V, G.IsClique s ∧ s.card = 5) :
    ¬ G.Colorable 4 := by
  intro h4
  rcases hK5 with ⟨s, hs, hs5⟩
  have hs_le : s.card ≤ 4 := hs.card_le_of_colorable h4
  have h_bad : 5 ≤ 4 := by
    rw [← hs5]
    exact hs_le
  exact (Nat.not_succ_le_self 4) h_bad

/-- A concrete 5-clique witness gives a lower bound on chromatic number. -/
theorem five_clique_forces_chromaticNumber_ge_five
    (G : SimpleGraph V)
    (hK5 : ∃ s : Finset V, G.IsClique s ∧ s.card = 5) :
    5 ≤ G.chromaticNumber := by
  rcases hK5 with ⟨s, hs, hs5⟩
  have hs_le : s.card ≤ G.chromaticNumber := hs.card_le_chromaticNumber
  simpa [hs5] using hs_le

/-- Finite graphs are colorable with at most `|V|` colors. -/
theorem colorable_card_vertices
    (G : SimpleGraph V) [Fintype V] :
    G.Colorable (Fintype.card V) :=
  SimpleGraph.colorable_of_fintype G

/-- Finite graphs satisfy the trivial upper bound `χ(G) ≤ |V|`. -/
theorem chromaticNumber_le_card_vertices
    (G : SimpleGraph V) [Fintype V] :
    G.chromaticNumber ≤ Fintype.card V :=
  (colorable_card_vertices G).chromaticNumber_le

/-- The complete graph on 5 vertices is not 4-colorable. -/
theorem top_fin5_not_colorable_four :
    ¬ (⊤ : SimpleGraph (Fin 5)).Colorable 4 := by
  intro h4
  have hχ : (⊤ : SimpleGraph (Fin 5)).chromaticNumber = 5 := by
    simp
  have hle : (5 : ℕ∞) ≤ 4 := by
    simpa [hχ] using
      (h4.chromaticNumber_le : (⊤ : SimpleGraph (Fin 5)).chromaticNumber ≤ 4)
  exact (by decide : ¬ ((5 : ℕ∞) ≤ 4)) hle

/-- Any graph receiving a homomorphism from `K₅` is not 4-colorable. -/
theorem not_colorable_four_of_top_fin5_hom
    {W : Type*} (G : SimpleGraph W)
    (f : (⊤ : SimpleGraph (Fin 5)) →g G) :
    ¬ G.Colorable 4 := by
  intro h4
  have h_top : (⊤ : SimpleGraph (Fin 5)).Colorable 4 :=
    SimpleGraph.Colorable.of_hom f h4
  exact top_fin5_not_colorable_four h_top

/-- A 4-colorable graph is free of `K₅` copies. -/
theorem colorable_four_implies_top_fin5_free
    (G : SimpleGraph V) (h4 : G.Colorable 4) :
    (⊤ : SimpleGraph (Fin 5)).Free G :=
  SimpleGraph.free_of_colorable
    (G := G) (H := (⊤ : SimpleGraph (Fin 5)))
    top_fin5_not_colorable_four h4

/-- A `K₅` embedding in a graph obstructs 4-colorability. -/
theorem not_colorable_four_of_top_fin5_embedding
    {W : Type*} (G : SimpleGraph W)
    (f : (⊤ : SimpleGraph (Fin 5)) ↪g G) :
    ¬ G.Colorable 4 := by
  intro h4
  have hcf : G.CliqueFree 5 := colorable_four_implies_cliqueFree_five G h4
  exact (SimpleGraph.not_cliqueFree_of_top_embedding f) hcf

/-- Any failure of 5-clique-freeness obstructs 4-colorability. -/
theorem not_colorable_four_of_not_cliqueFree_five
    (G : SimpleGraph V) (h : ¬ G.CliqueFree 5) :
    ¬ G.Colorable 4 := by
  intro h4
  exact h (colorable_four_implies_cliqueFree_five G h4)

/-- Any failure of `K₅`-copy freeness obstructs 4-colorability. -/
theorem not_colorable_four_of_not_top_fin5_free
    (G : SimpleGraph V) (h : ¬ (⊤ : SimpleGraph (Fin 5)).Free G) :
    ¬ G.Colorable 4 := by
  intro h4
  exact h (colorable_four_implies_top_fin5_free G h4)

end FourColor.Curriculum.Actual
