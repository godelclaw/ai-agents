import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.ENat.Basic
import Mathlib.Data.Finset.Card

namespace FourColor.Curriculum.Actual

/-- The complete graph on `n + 1` vertices is not `n`-colorable. -/
theorem top_fin_succ_not_colorable (n : ℕ) :
    ¬ (⊤ : SimpleGraph (Fin (n + 1))).Colorable n := by
  intro hcol
  have hχ : (⊤ : SimpleGraph (Fin (n + 1))).chromaticNumber = n + 1 := by
    simp
  have hle : ((n + 1 : ℕ) : ℕ∞) ≤ n := by
    simpa [hχ] using
      (hcol.chromaticNumber_le :
        (⊤ : SimpleGraph (Fin (n + 1))).chromaticNumber ≤ n)
  have hle_nat : n + 1 ≤ n := ENat.coe_le_coe.mp hle
  exact (Nat.not_succ_le_self n) hle_nat

/-- A graph receiving a homomorphism from `K_{n+1}` is not `n`-colorable. -/
theorem not_colorable_of_top_fin_succ_hom
    {W : Type*} (G : SimpleGraph W) (n : ℕ)
    (f : (⊤ : SimpleGraph (Fin (n + 1))) →g G) :
    ¬ G.Colorable n := by
  intro hcol
  have htop : (⊤ : SimpleGraph (Fin (n + 1))).Colorable n :=
    SimpleGraph.Colorable.of_hom f hcol
  exact top_fin_succ_not_colorable n htop

/-- A graph containing an embedding of `K_{n+1}` is not `n`-colorable. -/
theorem not_colorable_of_top_fin_succ_embedding
    {W : Type*} (G : SimpleGraph W) (n : ℕ)
    (f : (⊤ : SimpleGraph (Fin (n + 1))) ↪g G) :
    ¬ G.Colorable n := by
  intro hcol
  have hcf : G.CliqueFree (n + 1) := hcol.cliqueFree (Nat.lt_succ_self n)
  exact (SimpleGraph.not_cliqueFree_of_top_embedding f) hcf

/-- If a graph has a clique with more than `n` vertices, it is not `n`-colorable. -/
theorem not_colorable_of_isClique_card_gt
    {V : Type*} (G : SimpleGraph V) {n : ℕ} {s : Finset V}
    (hs : G.IsClique s) (hgt : n < s.card) :
    ¬ G.Colorable n := by
  intro hcol
  exact (Nat.not_lt_of_ge (hs.card_le_of_colorable hcol)) hgt

end FourColor.Curriculum.Actual
