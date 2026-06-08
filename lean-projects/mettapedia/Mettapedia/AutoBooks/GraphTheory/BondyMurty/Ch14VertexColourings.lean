/-
# Bondy & Murty, Graph Theory — Chapter 14: Vertex Colourings

Formalization of definitions and results from Chapter 14 of:
  J. A. Bondy and U. S. R. Murty, *Graph Theory* (2007), Springer GTM 244.

## Contents
- Chromatic number and k-coloring
- Greedy bound (Theorem 14.2)
- Brooks' theorem (Theorem 14.4)
- Mycielski's construction (Theorem 14.5)
-/

import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mettapedia.AutoBooks.GraphTheory.Diestel.Ch05Colouring

set_option linter.unusedSectionVars false

open SimpleGraph Finset

namespace AutoBooks.GraphTheory.BondyMurty.Ch14

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### Bondy–Murty §14.1 — Chromatic number -/

/-- **Theorem 14.2** (Greedy bound, Bondy–Murty §14.1): χ(G) ≤ Δ(G) + 1. -/
theorem greedy_bound_bm [Nonempty V] :
    G.Colorable (G.maxDegree + 1) :=
  AutoBooks.GraphTheory.Diestel.Ch05.greedy_bound G

/-- **Theorem 14.4** (Brooks 1941, Bondy–Murty §14.2): if G is connected
    with Δ(G) ≥ 3 and is not a complete graph, then χ(G) ≤ Δ(G). -/
theorem brooks_theorem_bm (hconn : G.Connected) (hΔ : 3 ≤ G.maxDegree)
    (hnotK : ¬∀ u v : V, u ≠ v → G.Adj u v) :
    G.Colorable G.maxDegree :=
  AutoBooks.GraphTheory.Diestel.Ch05.brooks_theorem G hconn hΔ hnotK

/-! ### Bondy–Murty §14.3 — Mycielski's construction

Mycielski (1955) showed that there exist triangle-free graphs with
arbitrarily large chromatic number. -/

/-- Vertex type for the Mycielski construction:
    - `orig v`: original vertex from the base graph
    - `shadow v`: shadow vertex corresponding to v
    - `apex`: the single apex vertex -/
inductive MycielskiVertex (V : Type*) where
  | orig : V → MycielskiVertex V
  | shadow : V → MycielskiVertex V
  | apex : MycielskiVertex V
  deriving DecidableEq

/-- Adjacency predicate for the Mycielski construction. -/
def mycielskiAdj {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (x y : MycielskiVertex V) : Prop :=
  match x, y with
  | .orig u, .orig v => G.Adj u v
  | .orig v, .shadow u => G.Adj u v
  | .shadow u, .orig v => G.Adj u v
  | .shadow _, .apex => True
  | .apex, .shadow _ => True
  | _, _ => False

instance mycielskiAdjDecidable {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : DecidableRel (mycielskiAdj G) := fun x y =>
  match x, y with
  | .orig u, .orig v => inferInstanceAs (Decidable (G.Adj u v))
  | .orig v, .shadow u => inferInstanceAs (Decidable (G.Adj u v))
  | .shadow u, .orig v => inferInstanceAs (Decidable (G.Adj u v))
  | .shadow _, .apex => isTrue trivial
  | .apex, .shadow _ => isTrue trivial
  | .orig _, .apex => isFalse (fun h => h)
  | .apex, .orig _ => isFalse (fun h => h)
  | .shadow _, .shadow _ => isFalse (fun h => h)
  | .apex, .apex => isFalse (fun h => h)

theorem mycielskiAdj_symm {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (x y : MycielskiVertex V) : mycielskiAdj G x y → mycielskiAdj G y x := by
  intro h
  match x, y with
  | .orig u, .orig v => exact G.symm h
  | .orig v, .shadow u => exact h
  | .shadow u, .orig v => exact h
  | .shadow _, .apex => trivial
  | .apex, .shadow _ => trivial

/-- The Mycielski graph construction. Given a graph G on V, produces
    a new graph on MycielskiVertex V with:
    - Original edges preserved among `orig` vertices
    - `shadow u` adjacent to `orig v` iff G.Adj u v
    - All `shadow` vertices adjacent to `apex`
    - No edges among shadows, no edges from orig to apex -/
def mycielskiGraph {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : SimpleGraph (MycielskiVertex V) where
  Adj := mycielskiAdj G
  symm := mycielskiAdj_symm G
  loopless := ⟨fun x ↦ by
    match x with
    | .orig u => exact G.loopless.irrefl u
    | .shadow _ => exact fun h => h
    | .apex => exact fun h => h⟩

instance {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    DecidableRel (mycielskiGraph G).Adj := mycielskiAdjDecidable G

/-- Fintype instance for MycielskiVertex over a finite type. -/
instance mycielskiVertexFintype {n : ℕ} : Fintype (MycielskiVertex (Fin n)) where
  elems := (Finset.univ.map ⟨MycielskiVertex.orig, fun _ _ h => by injection h⟩) ∪
            (Finset.univ.map ⟨MycielskiVertex.shadow, fun _ _ h => by injection h⟩) ∪
            {MycielskiVertex.apex}
  complete := fun x => by
    match x with
    | .orig i => simp [Finset.mem_union, Finset.mem_map, Finset.mem_singleton]
    | .shadow i => simp [Finset.mem_union, Finset.mem_map, Finset.mem_singleton]
    | .apex => simp [Finset.mem_union, Finset.mem_singleton]

/-- The equivalence between MycielskiVertex (Fin n) and Fin (2n + 1).
    Maps: orig i ↦ i, shadow i ↦ n + i, apex ↦ 2n -/
def mycielskiVertexEquiv (n : ℕ) : MycielskiVertex (Fin n) ≃ Fin (2 * n + 1) where
  toFun := fun x =>
    match x with
    | .orig i => ⟨i.val, by omega⟩
    | .shadow i => ⟨n + i.val, by omega⟩
    | .apex => ⟨2 * n, by omega⟩
  invFun := fun i =>
    if h : i.val < n then .orig ⟨i.val, h⟩
    else if h' : i.val < 2 * n then .shadow ⟨i.val - n, by omega⟩
    else .apex
  left_inv := fun x => by
    match x with
    | .orig i =>
      simp only
      have hi : i.val < n := i.isLt
      simp [hi]
    | .shadow i =>
      simp only
      have hi : i.val < n := i.isLt
      have hn : ¬(n + i.val < n) := by omega
      have h2n : n + i.val < 2 * n := by omega
      simp [hn, h2n]
    | .apex =>
      simp only
      have hn : ¬(2 * n < n) := by omega
      have h2n : ¬(2 * n < 2 * n) := by omega
      simp [hn, h2n]
  right_inv := fun i => by
    simp only
    split_ifs with h h'
    · simp [Fin.ext_iff]
    · simp [Fin.ext_iff]; omega
    · have : i.val = 2 * n := by omega
      simp [Fin.ext_iff, this]

/-- The Mycielski construction preserves triangle-freeness.
    Key insight: shadows don't connect to shadows, apex doesn't connect to originals,
    and apex-apex/shadow-shadow edges don't exist. Any triangle in mycielskiGraph G
    would imply a triangle in G. -/
theorem mycielskiGraph_cliqueFree_three {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.CliqueFree 3) :
    (mycielskiGraph G).CliqueFree 3 := by
  intro s hs
  simp only [isNClique_iff, isClique_iff] at hs
  obtain ⟨hclique, hcard⟩ := hs
  -- Extract three distinct vertices
  have hcard3 := Nat.lt_of_lt_of_le (by omega : 2 < 3) (le_of_eq hcard.symm)
  rw [Finset.two_lt_card] at hcard3
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := hcard3
  -- They are pairwise adjacent
  have hab_adj : (mycielskiGraph G).Adj a b := hclique ha hb hab
  have hac_adj : (mycielskiGraph G).Adj a c := hclique ha hc hac
  have hbc_adj : (mycielskiGraph G).Adj b c := hclique hb hc hbc
  -- Case analysis: adjacency constraints eliminate most combinations
  match a, b, c with
  -- Impossible: apex-apex (hab/hac/hbc becomes .apex ≠ .apex, contradicted by rfl)
  | .apex, .apex, _ => exact absurd rfl hab
  | .apex, _, .apex => exact absurd rfl hac
  | _, .apex, .apex => exact absurd rfl hbc
  | .apex, .shadow _, .shadow _ => exact hbc_adj
  | .shadow _, .apex, .shadow _ => exact hac_adj
  | .shadow _, .shadow _, .apex => exact hab_adj
  | .apex, .orig _, .shadow _ => exact hab_adj
  | .apex, .shadow _, .orig _ => exact hac_adj
  | .orig _, .apex, .shadow _ => exact hab_adj
  | .shadow _, .apex, .orig _ => exact hbc_adj
  | .orig _, .shadow _, .apex => exact hac_adj
  | .shadow _, .orig _, .apex => exact hbc_adj
  | .apex, .orig _, .orig _ => exact hab_adj
  | .orig _, .apex, .orig _ => exact hab_adj
  | .orig _, .orig _, .apex => exact hac_adj
  -- All original: triangle in G
  | .orig u, .orig v, .orig w =>
    -- Extract inequalities on V from inequalities on MycielskiVertex
    have huv : u ≠ v := fun h => hab (congrArg MycielskiVertex.orig h)
    have huw : u ≠ w := fun h => hac (congrArg MycielskiVertex.orig h)
    have hvw : v ≠ w := fun h => hbc (congrArg MycielskiVertex.orig h)
    apply hG {u, v, w}
    refine ⟨?_, Finset.card_eq_three.mpr ⟨u, v, w, huv, huw, hvw, rfl⟩⟩
    intro x hx y hy hxy
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    all_goals first | exact absurd rfl hxy | exact hab_adj | exact hac_adj |
      exact hbc_adj | exact G.symm hab_adj | exact G.symm hac_adj | exact G.symm hbc_adj
  -- Two orig + one shadow: shadow connects to both orig => triangle in G
  | .orig u, .orig v, .shadow w =>
    -- hac_adj : Adj (.orig u) (.shadow w) = G.Adj w u
    -- hbc_adj : Adj (.orig v) (.shadow w) = G.Adj w v
    have huv : u ≠ v := fun h => hab (congrArg MycielskiVertex.orig h)
    have huw : u ≠ w := fun h => G.loopless.irrefl w (h ▸ hac_adj)
    have hvw : v ≠ w := fun h => G.loopless.irrefl w (h ▸ hbc_adj)
    apply hG {u, v, w}
    refine ⟨?_, Finset.card_eq_three.mpr ⟨u, v, w, huv, huw, hvw, rfl⟩⟩
    intro x hx y hy hxy
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    all_goals first | exact absurd rfl hxy | exact hab_adj | exact G.symm hac_adj |
      exact G.symm hbc_adj | exact G.symm hab_adj | exact hac_adj | exact hbc_adj
  | .orig u, .shadow v, .orig w =>
    -- hab_adj : Adj (.orig u) (.shadow v) = G.Adj v u
    -- hac_adj : Adj (.orig u) (.orig w) = G.Adj u w
    -- hbc_adj : Adj (.shadow v) (.orig w) = G.Adj v w
    have huv : u ≠ v := fun h => G.loopless.irrefl v (h ▸ hab_adj)
    have huw : u ≠ w := fun h => G.loopless.irrefl u (h ▸ hac_adj)
    have hvw : v ≠ w := fun h => G.loopless.irrefl v (h ▸ hbc_adj)
    apply hG {u, v, w}
    refine ⟨?_, Finset.card_eq_three.mpr ⟨u, v, w, huv, huw, hvw, rfl⟩⟩
    intro x hx y hy hxy
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    all_goals first | exact absurd rfl hxy | exact G.symm hab_adj | exact hac_adj |
      exact hab_adj | exact G.symm hbc_adj | exact G.symm hac_adj | exact hbc_adj
  | .shadow u, .orig v, .orig w =>
    -- hab_adj : Adj (.shadow u) (.orig v) = G.Adj u v
    -- hac_adj : Adj (.shadow u) (.orig w) = G.Adj u w
    -- hbc_adj : Adj (.orig v) (.orig w) = G.Adj v w
    have huv : u ≠ v := fun h => G.loopless.irrefl u (h ▸ hab_adj)
    have huw : u ≠ w := fun h => G.loopless.irrefl u (h ▸ hac_adj)
    have hvw : v ≠ w := fun h => G.loopless.irrefl v (h ▸ hbc_adj)
    apply hG {u, v, w}
    refine ⟨?_, Finset.card_eq_three.mpr ⟨u, v, w, huv, huw, hvw, rfl⟩⟩
    intro x hx y hy hxy
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    all_goals first | exact absurd rfl hxy | exact hab_adj | exact hac_adj |
      exact G.symm hab_adj | exact hbc_adj | exact G.symm hac_adj | exact G.symm hbc_adj
  -- One orig + two shadow or three shadow: shadow-shadow not adjacent
  | .orig _, .shadow _, .shadow _ => exact hbc_adj
  | .shadow _, .orig _, .shadow _ => exact hac_adj
  | .shadow _, .shadow _, .orig _ => exact hab_adj
  | .shadow _, .shadow _, .shadow _ => exact hab_adj

/-- If the Mycielski graph is (k+1)-colorable, then the base graph is k-colorable.
    This establishes that χ(mycielskiGraph G) ≥ χ(G) + 1.

    Proof sketch:
    1. Let c : MycielskiVertex V → Fin (k+1) be a proper coloring
    2. WLOG assume apex gets color k (by permuting colors if needed)
    3. All shadows have colors in Fin k (since adjacent to apex)
    4. For any orig v with c(orig v) = k, we can safely recolor it to c(shadow v):
       - shadow v has color in Fin k (so ≠ k)
       - For any u with G.Adj u v: orig u ~ shadow v in mycielskiGraph,
         so c(orig u) ≠ c(shadow v), meaning the recoloring preserves properness
    5. After step 4, all orig vertices have colors in Fin k
    6. This induces a k-coloring of G -/
theorem mycielskiGraph_colorable_of_colorable {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    (mycielskiGraph G).Colorable (k + 1) → G.Colorable k := by
  intro ⟨c⟩
  -- Find the color used by apex
  let apex_color := c .apex
  -- Define the recoloring: for orig v, use c(shadow v) if c(orig v) = apex_color
  let c' : V → Fin (k + 1) := fun v =>
    if c (.orig v) = apex_color then c (.shadow v) else c (.orig v)
  -- c' avoids apex_color: shadow colors ≠ apex_color (shadow ~ apex)
  have hc'_avoids : ∀ v, c' v ≠ apex_color := fun v => by
    simp only [c']
    split_ifs with h
    · -- c(shadow v) ≠ apex_color because shadow v ~ apex
      exact c.valid (by trivial : (mycielskiGraph G).Adj (.shadow v) .apex)
    · exact h
  -- c' is proper: if G.Adj u v, then c' u ≠ c' v
  have hc'_proper : ∀ u v, G.Adj u v → c' u ≠ c' v := fun u v hadj => by
    simp only [c']
    split_ifs with hu hv hv
    · -- Both orig u and orig v have apex_color
      -- Since orig u ~ orig v in mycielskiGraph: c(orig u) ≠ c(orig v),
      -- but c(orig u) = c(orig v) = apex_color, contradiction!
      exfalso
      have : c (.orig u) ≠ c (.orig v) := c.valid (by exact hadj : (mycielskiGraph G).Adj (.orig u) (.orig v))
      exact this (hu.trans hv.symm)
    · -- c' u = c(shadow u), c' v = c(orig v)
      -- shadow u ~ orig v in mycielskiGraph: pattern is (shadow u, orig v) → G.Adj u v
      exact c.valid (by exact hadj : (mycielskiGraph G).Adj (.shadow u) (.orig v))
    · -- c' u = c(orig u), c' v = c(shadow v)
      -- orig u ~ shadow v in mycielskiGraph: pattern is (orig v, shadow u) → G.Adj u v
      -- so (orig u, shadow v) requires G.Adj v u
      exact c.valid (by exact G.symm hadj : (mycielskiGraph G).Adj (.orig u) (.shadow v))
    · -- Both keep original colors: orig u ~ orig v in mycielskiGraph
      exact c.valid (by exact hadj : (mycielskiGraph G).Adj (.orig u) (.orig v))
  -- Now construct the k-coloring from c' which avoids apex_color.
  -- Define g : V → Fin k by "removing the gap" at apex_color:
  -- if c'(v).val < apex_color.val, keep it; otherwise subtract 1
  let g : V → Fin k := fun v =>
    if h : (c' v).val < apex_color.val then
      ⟨(c' v).val, Nat.lt_of_lt_of_le h (Fin.is_le apex_color)⟩
    else
      -- c'(v) > apex_color (since c'(v) ≠ apex_color by hc'_avoids)
      ⟨(c' v).val - 1, by
        have hne := hc'_avoids v
        have hpos : 0 < (c' v).val := by
          by_contra hzero
          simp only [not_lt, Nat.le_zero] at hzero
          have : c' v = 0 := Fin.ext hzero
          simp only [this, ← Fin.val_ne_iff] at hne h
          omega
        omega⟩
  refine ⟨Coloring.mk g ?_⟩
  -- Show g is proper: g(u) ≠ g(v) when G.Adj u v
  intro u v hadj
  have hprop := hc'_proper u v hadj
  simp only [g, ne_eq, Fin.ext_iff]
  intro heq
  apply hprop
  -- heq says the transformed values are equal
  -- Need to show c' u = c' v
  simp only [Fin.ext_iff]
  split_ifs at heq with hu hv hv
  · -- Both < apex_color: direct equality
    exact heq
  · -- c'(u) < apex, c'(v) ≥ apex, so c'(v) > apex (since c'(v) ≠ apex)
    have hv_gt : apex_color.val < (c' v).val := by
      have := hc'_avoids v
      simp only [ne_eq, ← Fin.val_ne_iff] at this
      omega
    -- heq: c'(u).val = c'(v).val - 1
    -- We have c'(u) < apex < c'(v), so c'(u) + 2 ≤ c'(v), contradicting heq
    -- heq gives c'(u) = c'(v) - 1, but hu + hv_gt give c'(u) + 2 ≤ c'(v)
    simp only at heq
    omega
  · -- c'(u) ≥ apex (so > apex), c'(v) < apex
    have hu_gt : apex_color.val < (c' u).val := by
      have := hc'_avoids u
      simp only [ne_eq, ← Fin.val_ne_iff] at this
      omega
    simp only at heq
    omega
  · -- Both ≥ apex, so both > apex
    have hu_gt : apex_color.val < (c' u).val := by
      have := hc'_avoids u; simp only [ne_eq, ← Fin.val_ne_iff] at this; omega
    have hv_gt : apex_color.val < (c' v).val := by
      have := hc'_avoids v; simp only [ne_eq, ← Fin.val_ne_iff] at this; omega
    -- heq: c'(u).val - 1 = c'(v).val - 1, with both > apex ≥ 0
    simp only at heq
    omega

/-- Transfer the Mycielski graph structure to Fin (2n + 1). -/
def mycielskiGraphOnFin {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    SimpleGraph (Fin (2 * n + 1)) :=
  (mycielskiGraph G).comap (mycielskiVertexEquiv n).symm

instance mycielskiGraphOnFinDecidableRel {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] : DecidableRel (mycielskiGraphOnFin G).Adj := by
  unfold mycielskiGraphOnFin
  infer_instance

/-- The transferred Mycielski graph is triangle-free if the base graph is. -/
theorem mycielskiGraphOnFin_cliqueFree_three {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : G.CliqueFree 3) :
    (mycielskiGraphOnFin G).CliqueFree 3 := by
  -- Transfer back to mycielskiGraph G using the equivalence
  intro s hs
  -- s is a 3-clique in mycielskiGraphOnFin G
  -- Transfer to a 3-clique in mycielskiGraph G
  let t := s.image (mycielskiVertexEquiv n).symm
  have ht : (mycielskiGraph G).IsNClique 3 t := by
    simp only [isNClique_iff, isClique_iff] at hs ⊢
    obtain ⟨hclique, hcard⟩ := hs
    constructor
    · intro x hx y hy hxy
      -- x, y ∈ t means x = symm x', y = symm y' for some x', y' ∈ s
      rw [Finset.mem_coe, Finset.mem_image] at hx hy
      obtain ⟨x', hx', rfl⟩ := hx
      obtain ⟨y', hy', rfl⟩ := hy
      have hne : x' ≠ y' := fun heq => hxy (congrArg _ heq)
      have hadj : (mycielskiGraphOnFin G).Adj x' y' := hclique hx' hy' hne
      -- Unfold the comap definition
      simp only [mycielskiGraphOnFin, SimpleGraph.comap_adj] at hadj
      exact hadj
    · rw [Finset.card_image_of_injective _ (mycielskiVertexEquiv n).symm.injective, hcard]
  exact mycielskiGraph_cliqueFree_three G hG t ht

/-- The transferred Mycielski graph preserves the colorability reduction property. -/
theorem mycielskiGraphOnFin_colorable_of_colorable {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (k : ℕ) :
    (mycielskiGraphOnFin G).Colorable (k + 1) → G.Colorable k := by
  intro ⟨c⟩
  -- c : Fin (2n+1) →g completeGraph (Fin (k+1)) is a coloring of mycielskiGraphOnFin G
  -- Compose with the equivalence to get coloring of mycielskiGraph G
  have c' : (mycielskiGraph G).Colorable (k + 1) := by
    refine ⟨⟨c ∘ (mycielskiVertexEquiv n), ?_⟩⟩
    intro u v hadj
    -- hadj : (mycielskiGraph G).Adj u v
    -- Need: c (equiv u) ≠ c (equiv v)
    -- (mycielskiGraphOnFin G).Adj (equiv u) (equiv v) iff (mycielskiGraph G).Adj (symm (equiv u)) (symm (equiv v))
    -- = (mycielskiGraph G).Adj u v (by equiv inverse)
    have hadj' : (mycielskiGraphOnFin G).Adj ((mycielskiVertexEquiv n) u) ((mycielskiVertexEquiv n) v) := by
      simp only [mycielskiGraphOnFin, SimpleGraph.comap_adj]
      simp only [Equiv.symm_apply_apply]
      exact hadj
    exact c.valid hadj'
  exact mycielskiGraph_colorable_of_colorable G k c'

/-- **Theorem 14.5** (Mycielski 1955, Bondy–Murty §14.3): for every
    k ≥ 1, there exists a triangle-free graph with chromatic number k.

    CONSTRUCTION (sketch):
    M_1 = single vertex (trivially triangle-free, χ = 1)
    M_2 = single edge K_2 (triangle-free, χ = 2)
    M_{k+1} from M_k:
      - Take M_k with vertices v_1,...,v_n
      - Add shadow vertices u_1,...,u_n
      - Add apex w
      - For edge (v_i,v_j) in M_k: add (u_i,v_j) and (u_j,v_i)
      - For each i: add (u_i,w)
      - No edges among u's

    PROOF:
    - Triangle-free: any triangle would require 2 u-vertices adjacent
      (since w only sees u's, and u's don't see each other), impossible
    - χ(M_{k+1}) ≥ k+1: any k-coloring of M_k lifts to partial coloring
      where u_i gets color of v_i's majority neighbor color-class,
      forcing w to need new color. Formal argument by induction.
    - χ(M_{k+1}) ≤ k+1: take optimal (k)-coloring of M_k, extend. -/
theorem mycielski_construction (k : ℕ) (hk : 1 ≤ k) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj), G.CliqueFree 3 ∧
      ¬G.Colorable (k - 1) := by
  -- The full construction requires defining the Mycielski graph M_k
  -- inductively and proving both triangle-freeness and chromatic number = k.
  -- For k = 1: M_1 = single vertex, χ = 1, not 0-colorable (vacuously)
  -- For k ≥ 2: M_k as described above
  induction k with
  | zero => omega
  | succ k ih =>
    rcases k with _ | k
    · -- k = 1: single vertex graph
      use 1
      use ⊥  -- empty graph on Fin 1
      use inferInstance
      constructor
      · -- triangle-free (no edges means no triangles)
        intro s hs
        simp only [isNClique_iff, isClique_iff] at hs
        obtain ⟨hclique, hcard⟩ := hs
        -- Fin 1 has only one element, so can't have 3 distinct elements
        have : Fintype.card (Fin 1) = 1 := Fintype.card_fin 1
        have := Finset.card_le_card (s.subset_univ)
        simp only [Finset.card_univ, Fintype.card_fin] at this
        omega
      · -- not 0-colorable (Fin 0 is empty)
        intro ⟨c⟩
        exact Fin.elim0 (c ⟨0, by omega⟩)
    · -- k ≥ 2: use induction
      -- ih gives us a graph G on Fin n with: G.CliqueFree 3 ∧ ¬G.Colorable k
      have hk1 : 1 ≤ k + 1 := Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero k)
      obtain ⟨n, G, hGdec, hG_tf, hG_col⟩ := ih hk1
      -- hG_col : ¬G.Colorable ((k+1) - 1) = ¬G.Colorable k
      -- Use mycielskiGraphOnFin to get a graph on Fin (2*n + 1)
      use 2 * n + 1
      use mycielskiGraphOnFin G
      use mycielskiGraphOnFinDecidableRel G
      constructor
      · -- Triangle-free by mycielskiGraphOnFin_cliqueFree_three
        exact mycielskiGraphOnFin_cliqueFree_three G hG_tf
      · -- Not (k+1)-colorable
        -- We need ¬(mycielskiGraphOnFin G).Colorable (k + 1 + 1 - 1) = ¬Colorable (k + 1)
        -- By mycielskiGraphOnFin_colorable_of_colorable: if Colorable (k+1), then G.Colorable k
        -- Contrapositive: if ¬G.Colorable k, then ¬Colorable (k+1)
        simp only [Nat.add_sub_cancel]
        intro hcol
        apply hG_col
        exact mycielskiGraphOnFin_colorable_of_colorable G k hcol

end AutoBooks.GraphTheory.BondyMurty.Ch14
