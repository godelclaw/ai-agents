import Mathlib.Combinatorics.SimpleGraph.Finite
import FourColor.Curriculum.Actual.IncidenceCritical

namespace FourColor.Curriculum.Actual

variable {V : Type*}

/-- `G` is vertex-critical non-`n`-colorable if:
`G` is not `n`-colorable, but deleting any one vertex (as an induced complement graph) gives an
`n`-colorable graph.

Source: new definition built on Mathlib's induced-subgraph machinery. -/
def IsVertexCriticalNonColorable
    (G : SimpleGraph V) (n : ℕ) : Prop :=
  ¬ G.Colorable n ∧ ∀ v : V, (G.induce ({v}ᶜ)).Colorable n

namespace IsVertexCriticalNonColorable

variable {G : SimpleGraph V} {n : ℕ}

/-- Extract the non-colorability component.

Source: new (definition unpacking). -/
theorem not_colorable (h : IsVertexCriticalNonColorable G n) : ¬ G.Colorable n :=
  h.1

/-- Deleting any single vertex yields an `n`-colorable induced graph.

Source: new (definition unpacking). -/
theorem colorable_induce_compl_singleton
    (h : IsVertexCriticalNonColorable G n) (v : V) :
    (G.induce ({v}ᶜ)).Colorable n :=
  h.2 v

end IsVertexCriticalNonColorable

section RecolorBridge

variable {G : SimpleGraph V} [DecidableEq V] {n : ℕ} {v : V}

/-- Convert an `n`-coloring of the vertex-deleted induced graph `G[{v}ᶜ]` into an
`n`-coloring of `G.deleteIncidenceSet v` by coloring `v` with an arbitrary color.

Requires `n > 0` to provide that default color.

Source: new theorem using Mathlib's `deleteIncidenceSet_adj` and induced-adjacency semantics. -/
theorem colorable_deleteIncidenceSet_of_colorable_induce_compl_singleton
    (hn : 0 < n) (hcol : (G.induce ({v}ᶜ)).Colorable n) :
    (G.deleteIncidenceSet v).Colorable n := by
  rcases hcol with ⟨C⟩
  let c0 : Fin n := ⟨0, hn⟩
  let D : V → Fin n := fun w =>
    if hw : w = v then c0 else C ⟨w, by simp [hw]⟩
  refine ⟨SimpleGraph.Coloring.mk D ?_⟩
  intro x y hxy
  rcases (SimpleGraph.deleteIncidenceSet_adj (G := G) (x := v) (v₁ := x) (v₂ := y)).1 hxy with
    ⟨hxyG, hxv, hyv⟩
  have hx_mem : x ∈ ({v}ᶜ : Set V) := by simpa using hxv
  have hy_mem : y ∈ ({v}ᶜ : Set V) := by simpa using hyv
  have hxy_ind : (G.induce ({v}ᶜ)).Adj ⟨x, hx_mem⟩ ⟨y, hy_mem⟩ := hxyG
  have hneq : C ⟨x, hx_mem⟩ ≠ C ⟨y, hy_mem⟩ := C.valid hxy_ind
  have hDx : D x = C ⟨x, hx_mem⟩ := by simp [D, hxv]
  have hDy : D y = C ⟨y, hy_mem⟩ := by simp [D, hyv]
  exact hDx ▸ hDy ▸ hneq

end RecolorBridge

namespace IsVertexCriticalNonColorable

section Bridge

variable {G : SimpleGraph V} [DecidableEq V] [DecidableRel G.Adj] {n : ℕ}

/-- Vertex-critical non-`n`-colorability implies incidence-critical non-`n`-colorability
for `n > 0`.

Source: new bridge theorem from vertex deletion to incidence deletion. -/
theorem toIncidenceCritical
    (h : IsVertexCriticalNonColorable G n) (hn : 0 < n) :
    IsIncidenceCriticalNonColorable G n := by
  refine ⟨h.not_colorable, ?_⟩
  intro v
  exact colorable_deleteIncidenceSet_of_colorable_induce_compl_singleton
    (G := G) (v := v) hn (h.colorable_induce_compl_singleton v)

end Bridge

section Finite

variable {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj] {n : ℕ}

/-- In a vertex-critical non-`n`-colorable graph (`n > 0`), every vertex has degree at least `n`.

Source: new consequence through the incidence-critical bridge. -/
theorem le_degree (h : IsVertexCriticalNonColorable G n) (hn : 0 < n) (v : V) :
    n ≤ G.degree v :=
  (h.toIncidenceCritical hn).le_degree v

/-- In a nonempty vertex-critical non-`n`-colorable graph (`n > 0`), minimum degree is at least `n`.

Source: new consequence through the incidence-critical bridge. -/
theorem le_minDegree [Nonempty V]
    (h : IsVertexCriticalNonColorable G n) (hn : 0 < n) :
    n ≤ G.minDegree :=
  (h.toIncidenceCritical hn).le_minDegree

/-- In a vertex-critical non-`n`-colorable graph (`n > 0`), each vertex has a neighbor.

Source: new consequence through the incidence-critical bridge. -/
theorem exists_adj_of_pos (h : IsVertexCriticalNonColorable G n) (hn : 0 < n) (v : V) :
    ∃ w, G.Adj v w :=
  (h.toIncidenceCritical hn).exists_adj_of_pos hn v

/-- In a vertex-critical non-`n`-colorable graph (`n > 0`), every vertex lies in graph support.

Source: new consequence through the incidence-critical bridge. -/
theorem mem_support_of_pos (h : IsVertexCriticalNonColorable G n) (hn : 0 < n) (v : V) :
    v ∈ G.support :=
  (h.toIncidenceCritical hn).mem_support_of_pos hn v

end Finite

end IsVertexCriticalNonColorable

section FourColorSpecialization

variable {G : SimpleGraph V} [DecidableEq V] [DecidableRel G.Adj]

/-- Four-color specialization: vertex-critical non-4-colorable graphs are incidence-critical. -/
theorem IsVertexCriticalNonColorable.toIncidenceCritical_four
    (h : IsVertexCriticalNonColorable G 4) :
    IsIncidenceCriticalNonColorable G 4 :=
  h.toIncidenceCritical (by decide : 0 < 4)

/-- Four-color specialization: each vertex has degree at least `4` in a vertex-critical
non-4-colorable graph. -/
theorem IsVertexCriticalNonColorable.four_le_degree
    [Fintype V]
    (h : IsVertexCriticalNonColorable G 4) (v : V) :
    4 ≤ G.degree v :=
  h.le_degree (by decide : 0 < 4) v

/-- Four-color specialization: nonempty vertex-critical non-4-colorable graphs satisfy
`minDegree ≥ 4`. -/
theorem IsVertexCriticalNonColorable.four_le_minDegree
    [Fintype V] [Nonempty V] (h : IsVertexCriticalNonColorable G 4) :
    4 ≤ G.minDegree :=
  h.le_minDegree (by decide : 0 < 4)

/-- Four-color + vertex-criticality inherits the standard AES/K₅ dichotomy. -/
theorem IsVertexCriticalNonColorable.k5_or_low_minDegree
    [Fintype V] (h : IsVertexCriticalNonColorable G 4) :
    ¬ G.CliqueFree 5 ∨ G.minDegree ≤ 8 * Fintype.card V / 11 :=
  h.toIncidenceCritical_four.k5_or_low_minDegree

/-- Embedding-level AES/K₅ dichotomy for vertex-critical non-4-colorable graphs. -/
theorem IsVertexCriticalNonColorable.k5_embedding_or_low_minDegree
    [Fintype V] (h : IsVertexCriticalNonColorable G 4) :
    Nonempty (SimpleGraph.completeGraph (Fin 5) ↪g G) ∨
      G.minDegree ≤ 8 * Fintype.card V / 11 :=
  h.toIncidenceCritical_four.k5_embedding_or_low_minDegree

/-- Combined structural consequence for vertex-critical non-4-colorable graphs:
either a `K₅` obstruction exists, or `minDegree` lies in the explicit interval
forced by local-critical and AES constraints. -/
theorem IsVertexCriticalNonColorable.k5_or_minDegree_window
    [Fintype V] [Nonempty V] (h : IsVertexCriticalNonColorable G 4) :
    ¬ G.CliqueFree 5 ∨
      (4 ≤ G.minDegree ∧ G.minDegree ≤ 8 * Fintype.card V / 11) :=
  h.toIncidenceCritical_four.k5_or_minDegree_window

/-- Four-color specialization: each vertex is non-isolated in a vertex-critical non-4-colorable
graph. -/
theorem IsVertexCriticalNonColorable.exists_adj
    [Fintype V]
    (h : IsVertexCriticalNonColorable G 4) (v : V) :
    ∃ w, G.Adj v w :=
  h.exists_adj_of_pos (by decide : 0 < 4) v

/-- Four-color specialization: all vertices lie in support in a vertex-critical non-4-colorable
graph. -/
theorem IsVertexCriticalNonColorable.mem_support
    [Fintype V]
    (h : IsVertexCriticalNonColorable G 4) (v : V) :
    v ∈ G.support :=
  h.mem_support_of_pos (by decide : 0 < 4) v

/-- Any nonempty vertex-critical non-4-colorable finite graph has at least five vertices. -/
theorem IsVertexCriticalNonColorable.card_verts_ge_five
    [Fintype V] [Nonempty V] (h : IsVertexCriticalNonColorable G 4) :
    5 ≤ Fintype.card V := by
  have h4 : 4 ≤ G.minDegree := h.four_le_minDegree
  have hlt : G.minDegree < Fintype.card V := G.minDegree_lt_card
  exact Nat.succ_le_of_lt (lt_of_le_of_lt h4 hlt)

/-- Under `K₅`-freeness, a nonempty vertex-critical non-4-colorable finite graph has at least
six vertices. -/
theorem IsVertexCriticalNonColorable.card_verts_ge_six_of_cliqueFree
    [Fintype V] [Nonempty V]
    (h : IsVertexCriticalNonColorable G 4) (hfree : G.CliqueFree 5) :
    6 ≤ Fintype.card V :=
  h.toIncidenceCritical_four.card_verts_ge_six_of_cliqueFree hfree

/-- Embedding-level version of the previous finite-size sharpening. -/
theorem IsVertexCriticalNonColorable.card_verts_ge_six_of_no_k5_embedding
    [Fintype V] [Nonempty V]
    (h : IsVertexCriticalNonColorable G 4)
    (hK5 : IsEmpty (SimpleGraph.completeGraph (Fin 5) ↪g G)) :
    6 ≤ Fintype.card V :=
  h.toIncidenceCritical_four.card_verts_ge_six_of_no_k5_embedding hK5

end FourColorSpecialization

end FourColor.Curriculum.Actual
