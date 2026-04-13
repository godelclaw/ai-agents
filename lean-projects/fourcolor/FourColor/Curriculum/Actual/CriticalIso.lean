import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import FourColor.Curriculum.Actual.VertexCritical

namespace FourColor.Curriculum.Actual

namespace SimpleGraph.Iso

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- Graph isomorphisms preserve and reflect finite colorability.

Source: new reusable transport lemma built from Mathlib's `Colorable.of_hom`. -/
theorem colorable_iff (f : G ≃g H) {n : ℕ} :
    G.Colorable n ↔ H.Colorable n := by
  constructor
  · intro hG
    exact SimpleGraph.Colorable.of_hom f.symm.toHom hG
  · intro hH
    exact SimpleGraph.Colorable.of_hom f.toHom hH

/-- Graph isomorphisms preserve and reflect clique-freeness.

Source: new reusable transport lemma built from Mathlib's `CliqueFree.comap`. -/
theorem cliqueFree_iff (f : G ≃g H) {n : ℕ} :
    G.CliqueFree n ↔ H.CliqueFree n := by
  constructor
  · intro hG
    exact SimpleGraph.CliqueFree.comap f.symm.toEmbedding hG
  · intro hH
    exact SimpleGraph.CliqueFree.comap f.toEmbedding hH

/-- Delete-incidence-set transport across a graph isomorphism.

Source: new exact compatibility lemma with Mathlib's `deleteIncidenceSet`. -/
def deleteIncidenceSetIso (f : G ≃g H) (v : V) :
    G.deleteIncidenceSet v ≃g H.deleteIncidenceSet (f v) where
  toEquiv := f.toEquiv
  map_rel_iff' := by
    intro a b
    simpa [SimpleGraph.deleteIncidenceSet_adj, f.map_adj_iff, f.injective.eq_iff]

/-- Delete-one-vertex induced-subgraph transport across a graph isomorphism.

Source: new exact compatibility lemma with Mathlib's induced-subgraph API. -/
def induceComplSingletonIso (f : G ≃g H) (v : V) :
    G.induce ({v}ᶜ) ≃g H.induce ({f v}ᶜ) where
  toEquiv :=
    { toFun := fun x =>
        ⟨f x, by
          rcases x with ⟨x, hx⟩
          have hx' : x ≠ v := by
            simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hx
          intro h
          exact hx' (f.injective h)⟩
      invFun := fun y =>
        ⟨f.symm y, by
          rcases y with ⟨y, hy⟩
          have hy' : y ≠ f v := by
            simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hy
          intro h
          exact hy' (by simpa using congrArg f h)⟩
      left_inv := by
        intro x
        ext
        simp
      right_inv := by
        intro y
        ext
        simp }
  map_rel_iff' := by
    intro a b
    simpa using f.map_adj_iff (v := (a : V)) (w := (b : V))

/-- Incidence-critical non-colorability is invariant under graph isomorphism.

Source: new transport theorem using `deleteIncidenceSetIso`. -/
theorem isIncidenceCriticalNonColorable_iff
    (f : G ≃g H) [DecidableRel G.Adj] [DecidableRel H.Adj] {n : ℕ} :
    IsIncidenceCriticalNonColorable G n ↔ IsIncidenceCriticalNonColorable H n := by
  constructor
  · intro hG
    refine ⟨?_, ?_⟩
    · intro hHcol
      exact hG.not_colorable ((colorable_iff (f := f)).2 hHcol)
    · intro w
      let v : V := f.symm w
      have hdel : (G.deleteIncidenceSet v).Colorable n :=
        hG.colorable_deleteIncidenceSet v
      have hw : f v = w := by
        simp [v]
      simpa [hw] using
        (colorable_iff (f := deleteIncidenceSetIso (f := f) v)).1 hdel
  · intro hH
    refine ⟨?_, ?_⟩
    · intro hGcol
      exact hH.not_colorable ((colorable_iff (f := f)).1 hGcol)
    · intro v
      let w : W := f v
      have hdel : (H.deleteIncidenceSet w).Colorable n :=
        hH.colorable_deleteIncidenceSet w
      have hw : w = f v := by
        simp [w]
      simpa [hw] using
        (colorable_iff (f := deleteIncidenceSetIso (f := f) v)).2 hdel

/-- Vertex-critical non-colorability is invariant under graph isomorphism.

Source: new transport theorem using `induceComplSingletonIso`. -/
theorem isVertexCriticalNonColorable_iff
    (f : G ≃g H) {n : ℕ} :
    IsVertexCriticalNonColorable G n ↔ IsVertexCriticalNonColorable H n := by
  constructor
  · intro hG
    refine ⟨?_, ?_⟩
    · intro hHcol
      exact hG.not_colorable ((colorable_iff (f := f)).2 hHcol)
    · intro w
      let v : V := f.symm w
      have hdel : (G.induce ({v}ᶜ)).Colorable n :=
        hG.colorable_induce_compl_singleton v
      have hw : f v = w := by
        simp [v]
      rw [← hw]
      exact (colorable_iff (f := induceComplSingletonIso (f := f) v)).1 hdel
  · intro hH
    refine ⟨?_, ?_⟩
    · intro hGcol
      exact hH.not_colorable ((colorable_iff (f := f)).1 hGcol)
    · intro v
      let w : W := f v
      have hdel : (H.induce ({w}ᶜ)).Colorable n :=
        hH.colorable_induce_compl_singleton w
      have hdel' : (H.induce ({f v}ᶜ)).Colorable n := by
        simpa [w] using hdel
      exact (colorable_iff (f := induceComplSingletonIso (f := f) v)).2 hdel'

/-- Minimal non-colorability is invariant under graph isomorphism.

Source: new transport theorem using strict-subgraph pullback along `comap`. -/
theorem isMinimalNonColorable_iff
    (f : G ≃g H) {n : ℕ} :
    IsMinimalNonColorable G n ↔ IsMinimalNonColorable H n := by
  constructor
  · intro hG
    refine ⟨?_, ?_⟩
    · intro hHcol
      exact hG.not_colorable ((colorable_iff (f := f)).2 hHcol)
    · intro J hJ
      let K : SimpleGraph V := J.comap f.toEmbedding
      have hKle : K ≤ G := by
        intro x y hxy
        have hJxy : J.Adj (f x) (f y) := by
          simpa [K] using hxy
        have hHxy : H.Adj (f x) (f y) := (le_of_lt hJ) hJxy
        exact (f.map_adj_iff).1 hHxy
      have hKne : K ≠ G := by
        intro hEq
        have hJEq : J = H := by
          ext a b
          constructor
          · intro hab
            have hK : K.Adj (f.symm a) (f.symm b) := by
              simpa [K] using hab
            have hGab : G.Adj (f.symm a) (f.symm b) := by
              simpa [hEq] using hK
            simpa using (f.map_adj_iff (v := f.symm a) (w := f.symm b)).2 hGab
          · intro hab
            have hHab : H.Adj (f (f.symm a)) (f (f.symm b)) := by
              simpa using hab
            have hGab : G.Adj (f.symm a) (f.symm b) :=
              (f.map_adj_iff (v := f.symm a) (w := f.symm b)).1 hHab
            have hK : K.Adj (f.symm a) (f.symm b) := by
              simpa [hEq] using hGab
            simpa [K] using hK
        exact hJ.ne hJEq
      have hKlt : K < G := lt_of_le_of_ne hKle hKne
      have hcolK : K.Colorable n := hG.colorable_of_lt hKlt
      have hIsoK : K ≃g J := by
        simpa [K] using (SimpleGraph.Iso.comap f.toEquiv J)
      exact (colorable_iff (f := hIsoK)).1 hcolK
  · intro hH
    refine ⟨?_, ?_⟩
    · intro hGcol
      exact hH.not_colorable ((colorable_iff (f := f)).1 hGcol)
    · intro J hJ
      let K : SimpleGraph W := J.comap f.symm.toEmbedding
      have hKle : K ≤ H := by
        intro x y hxy
        have hJxy : J.Adj (f.symm x) (f.symm y) := by
          simpa [K] using hxy
        have hGxy : G.Adj (f.symm x) (f.symm y) := (le_of_lt hJ) hJxy
        simpa using (f.map_adj_iff (v := f.symm x) (w := f.symm y)).2 hGxy
      have hKne : K ≠ H := by
        intro hEq
        have hJEq : J = G := by
          ext a b
          constructor
          · intro hab
            have hK : K.Adj (f a) (f b) := by
              simpa [K] using hab
            have hHab : H.Adj (f a) (f b) := by
              simpa [hEq] using hK
            exact (f.map_adj_iff (v := a) (w := b)).1 hHab
          · intro hab
            have hHab : H.Adj (f a) (f b) :=
              (f.map_adj_iff (v := a) (w := b)).2 hab
            have hK : K.Adj (f a) (f b) := by
              simpa [hEq] using hHab
            simpa [K] using hK
        exact hJ.ne hJEq
      have hKlt : K < H := lt_of_le_of_ne hKle hKne
      have hcolK : K.Colorable n := hH.colorable_of_lt hKlt
      have hIsoK : K ≃g J := by
        simpa [K] using (SimpleGraph.Iso.comap f.symm.toEquiv J)
      exact (colorable_iff (f := hIsoK)).1 hcolK

end SimpleGraph.Iso

end FourColor.Curriculum.Actual
