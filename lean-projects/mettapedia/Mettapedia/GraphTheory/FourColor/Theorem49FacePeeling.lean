import Mettapedia.GraphTheory.FourColor.Theorem49Step

namespace Mettapedia.GraphTheory.FourColor

variable {V F E : Type*} [DecidableEq V] [DecidableEq F] [DecidableEq E]

/-- The witness-edge support of a face peel order: the finite set of edges chosen as the unique
surviving edges for the successive peeled faces. -/
def facePeelWitnessSupport (faceOrder : List F) (witnessEdge : F → E) : Finset E :=
  faceOrder.toFinset.image witnessEdge

theorem mem_facePeelWitnessSupport_iff (faceOrder : List F) (witnessEdge : F → E) {e : E} :
    e ∈ facePeelWitnessSupport faceOrder witnessEdge ↔
      ∃ f ∈ faceOrder, witnessEdge f = e := by
  simp [facePeelWitnessSupport]

theorem mem_facePeelWitnessSupport_cons_of_ne {faceOrder : List F}
    {witnessEdge : F → E} {f : F} {e : E}
    (hne : witnessEdge f ≠ e) :
    e ∈ facePeelWitnessSupport (f :: faceOrder) witnessEdge ↔
      e ∈ facePeelWitnessSupport faceOrder witnessEdge := by
  rw [mem_facePeelWitnessSupport_iff, mem_facePeelWitnessSupport_iff]
  constructor
  · rintro ⟨g, hg, hge⟩
    rcases (by simpa using hg : g = f ∨ g ∈ faceOrder) with rfl | hgTail
    · exact False.elim (hne hge)
    · exact ⟨g, hgTail, hge⟩
  · rintro ⟨g, hg, hge⟩
    exact ⟨g, by simp [hg], hge⟩

/-- A finite peel order cannot realize a two-edge prefix dependency cycle.  If every face whose
witness is `e₁` requires an earlier `e₂` witness unless `e₂` is already in the base support, and
symmetrically every `e₂` witness requires an earlier `e₁`, then no `e₁` witness occurs.  The
statement deliberately allows repeated faces in `faceOrder`; the contradiction is by descent to
the first occurrence of either witness edge. -/
theorem not_exists_mem_of_twoWitnessPrefixCycle
    {base : Finset E} {witnessEdge : F → E} {e₁ e₂ : E}
    (hbase₁ : e₁ ∉ base) (hbase₂ : e₂ ∉ base) :
    ∀ faceOrder : List F,
      (∀ l₁ l₂ f, faceOrder = l₁ ++ f :: l₂ →
        witnessEdge f = e₁ → e₂ ∈ base ∪ facePeelWitnessSupport l₁ witnessEdge) →
      (∀ l₁ l₂ f, faceOrder = l₁ ++ f :: l₂ →
        witnessEdge f = e₂ → e₁ ∈ base ∪ facePeelWitnessSupport l₁ witnessEdge) →
      ¬ ∃ f ∈ faceOrder, witnessEdge f = e₁ := by
  intro faceOrder
  induction faceOrder with
  | nil =>
      intro _hstep₁ _hstep₂
      rintro ⟨_, hf, _⟩
      simp at hf
  | cons head tail ih =>
      intro hstep₁ hstep₂
      by_cases hhead₁ : witnessEdge head = e₁
      · have hbad := hstep₁ [] tail head (by simp) hhead₁
        rcases Finset.mem_union.1 hbad with hbase | hprev
        · exact False.elim (hbase₂ hbase)
        · simp [facePeelWitnessSupport] at hprev
      · by_cases hhead₂ : witnessEdge head = e₂
        · have hbad := hstep₂ [] tail head (by simp) hhead₂
          rcases Finset.mem_union.1 hbad with hbase | hprev
          · exact False.elim (hbase₁ hbase)
          · simp [facePeelWitnessSupport] at hprev
        · have hstep₁Tail :
              ∀ l₁ l₂ f, tail = l₁ ++ f :: l₂ →
                witnessEdge f = e₁ →
                  e₂ ∈ base ∪ facePeelWitnessSupport l₁ witnessEdge := by
            intro l₁ l₂ f hsplit hf
            have hfull : head :: tail = (head :: l₁) ++ f :: l₂ := by
              simp [hsplit]
            have hbad := hstep₁ (head :: l₁) l₂ f hfull hf
            rcases Finset.mem_union.1 hbad with hbase | hprev
            · exact Finset.mem_union.2 <| Or.inl hbase
            · exact Finset.mem_union.2 <| Or.inr <|
                (mem_facePeelWitnessSupport_cons_of_ne
                  (faceOrder := l₁) (witnessEdge := witnessEdge)
                  (f := head) (e := e₂) hhead₂).1 hprev
          have hstep₂Tail :
              ∀ l₁ l₂ f, tail = l₁ ++ f :: l₂ →
                witnessEdge f = e₂ →
                  e₁ ∈ base ∪ facePeelWitnessSupport l₁ witnessEdge := by
            intro l₁ l₂ f hsplit hf
            have hfull : head :: tail = (head :: l₁) ++ f :: l₂ := by
              simp [hsplit]
            have hbad := hstep₂ (head :: l₁) l₂ f hfull hf
            rcases Finset.mem_union.1 hbad with hbase | hprev
            · exact Finset.mem_union.2 <| Or.inl hbase
            · exact Finset.mem_union.2 <| Or.inr <|
                (mem_facePeelWitnessSupport_cons_of_ne
                  (faceOrder := l₁) (witnessEdge := witnessEdge)
                  (f := head) (e := e₁) hhead₁).1 hprev
          rintro ⟨f, hf, hfw⟩
          rcases (by simpa using hf : f = head ∨ f ∈ tail) with rfl | hfTail
          · exact hhead₁ hfw
          · exact ih hstep₁Tail hstep₂Tail ⟨f, hfTail, hfw⟩

/-- Support-level version of `not_exists_mem_of_twoWitnessPrefixCycle`.  A two-edge prefix
dependency cycle excludes both cyclic witness edges from the realized witness support. -/
theorem not_mem_facePeelWitnessSupport_pair_of_twoWitnessPrefixCycle
    {base : Finset E} {witnessEdge : F → E} {e₁ e₂ : E}
    (hbase₁ : e₁ ∉ base) (hbase₂ : e₂ ∉ base)
    (faceOrder : List F)
    (hstep₁ : ∀ l₁ l₂ f, faceOrder = l₁ ++ f :: l₂ →
      witnessEdge f = e₁ → e₂ ∈ base ∪ facePeelWitnessSupport l₁ witnessEdge)
    (hstep₂ : ∀ l₁ l₂ f, faceOrder = l₁ ++ f :: l₂ →
      witnessEdge f = e₂ → e₁ ∈ base ∪ facePeelWitnessSupport l₁ witnessEdge) :
    e₁ ∉ facePeelWitnessSupport faceOrder witnessEdge ∧
      e₂ ∉ facePeelWitnessSupport faceOrder witnessEdge := by
  constructor
  · intro hmem
    exact
      (not_exists_mem_of_twoWitnessPrefixCycle
        (base := base) (witnessEdge := witnessEdge)
        (e₁ := e₁) (e₂ := e₂)
        hbase₁ hbase₂ faceOrder hstep₁ hstep₂)
        ((mem_facePeelWitnessSupport_iff faceOrder witnessEdge).1 hmem)
  · intro hmem
    exact
      (not_exists_mem_of_twoWitnessPrefixCycle
        (base := base) (witnessEdge := witnessEdge)
        (e₁ := e₂) (e₂ := e₁)
        hbase₂ hbase₁ faceOrder hstep₂ hstep₁)
        ((mem_facePeelWitnessSupport_iff faceOrder witnessEdge).1 hmem)

/-- Face-ordered form of the Theorem 4.9 peeling step. A list of faces is a valid peel order
relative to `baseZero` if each face comes with a witness edge on its boundary whose remaining
boundary edges already lie in `baseZero` or in the witness-edge support of earlier faces. Under
orthogonality to the corresponding polarized face generators, all witness edges vanish. -/
theorem zero_on_facePeelOrder_from {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (baseZero : Finset G.edgeSet) (faceBoundary : F → Finset G.edgeSet)
    (witnessEdge : F → G.edgeSet) :
    ∀ faceOrder : List F,
      (∀ e ∈ baseZero, z e = 0) →
      (∀ l₁ l₂ f, faceOrder = l₁ ++ f :: l₂ →
        witnessEdge f ∈ faceBoundary f ∧
          (faceBoundary f).erase (witnessEdge f) ⊆
            baseZero ∪ facePeelWitnessSupport l₁ witnessEdge) →
      (∀ f ∈ faceOrder,
        ∀ γ, γ ≠ 0 → γ ≠ C (witnessEdge f) →
          chainDot
              (boundaryBicoloredEdges C (C (witnessEdge f)) (C (witnessEdge f) + γ)
                (faceBoundary f))
              z
              (polarizedFaceGenerator C (C (witnessEdge f)) (C (witnessEdge f) + γ)
                (faceBoundary f)) = 0) →
      ∀ f ∈ faceOrder, z (witnessEdge f) = 0
  | [], hzeroBase, _hstep, _horth => by
      intro f hf
      simp at hf
  | f :: fs, hzeroBase, hstep, horth => by
      rcases hstep [] fs f rfl with ⟨heFace, hsubset⟩
      have hzerof : z (witnessEdge f) = 0 := by
        apply edge_eq_zero_of_polarizedFaceGenerator_annihilation_of_subset_zero C z
        · exact htait (witnessEdge f)
        · exact heFace
        · exact hsubset
        · intro e he
          exact hzeroBase e (by simpa [facePeelWitnessSupport] using he)
        · intro γ hγ0 hγd
          exact horth f (by simp) γ hγ0 hγd
      have hzeroBase' : ∀ e ∈ insert (witnessEdge f) baseZero, z e = 0 := by
        intro e he
        rcases Finset.mem_insert.1 he with rfl | hmem
        · exact hzerof
        · exact hzeroBase e hmem
      have hstep' :
          ∀ l₁ l₂ f', fs = l₁ ++ f' :: l₂ →
            witnessEdge f' ∈ faceBoundary f' ∧
              (faceBoundary f').erase (witnessEdge f') ⊆
                insert (witnessEdge f) baseZero ∪ facePeelWitnessSupport l₁ witnessEdge := by
        intro l₁ l₂ f' hs
        have hs' : f :: fs = (f :: l₁) ++ f' :: l₂ := by
          simp [hs]
        rcases hstep (f :: l₁) l₂ f' hs' with ⟨heFace', hsubset'⟩
        refine ⟨heFace', ?_⟩
        intro e he
        have he' : e ∈ baseZero ∪ facePeelWitnessSupport (f :: l₁) witnessEdge := hsubset' he
        simpa [facePeelWitnessSupport, Finset.union_assoc, Finset.union_left_comm,
          Finset.union_comm] using he'
      have horth' :
          ∀ f' ∈ fs,
            ∀ γ, γ ≠ 0 → γ ≠ C (witnessEdge f') →
              chainDot
                  (boundaryBicoloredEdges C (C (witnessEdge f')) (C (witnessEdge f') + γ)
                    (faceBoundary f'))
                  z
                  (polarizedFaceGenerator C (C (witnessEdge f')) (C (witnessEdge f') + γ)
                    (faceBoundary f')) = 0 := by
        intro f' hf' γ hγ0 hγd
        exact horth f' (by simp [hf']) γ hγ0 hγd
      have htail :
          ∀ f' ∈ fs, z (witnessEdge f') = 0 :=
        zero_on_facePeelOrder_from C htait z (insert (witnessEdge f) baseZero) faceBoundary
          witnessEdge fs hzeroBase' hstep' horth'
      intro f' hf'
      rcases (by simpa using hf' : f' = f ∨ f' ∈ fs) with rfl | hfs
      · exact hzerof
      · exact htail f' hfs

/-- Edge-facing corollary of the face-ordered peel theorem: `z` vanishes on the entire witness-edge
support extracted from the face peel order. -/
theorem zero_on_facePeelWitnessSupport_from {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (baseZero : Finset G.edgeSet) (faceBoundary : F → Finset G.edgeSet)
    (witnessEdge : F → G.edgeSet) (faceOrder : List F)
    (hzeroBase : ∀ e ∈ baseZero, z e = 0)
    (hstep : ∀ l₁ l₂ f, faceOrder = l₁ ++ f :: l₂ →
      witnessEdge f ∈ faceBoundary f ∧
        (faceBoundary f).erase (witnessEdge f) ⊆
          baseZero ∪ facePeelWitnessSupport l₁ witnessEdge)
    (horth : ∀ f ∈ faceOrder,
      ∀ γ, γ ≠ 0 → γ ≠ C (witnessEdge f) →
        chainDot
            (boundaryBicoloredEdges C (C (witnessEdge f)) (C (witnessEdge f) + γ)
              (faceBoundary f))
            z
            (polarizedFaceGenerator C (C (witnessEdge f)) (C (witnessEdge f) + γ)
              (faceBoundary f)) = 0) :
    ∀ e ∈ facePeelWitnessSupport faceOrder witnessEdge, z e = 0 := by
  have hfaces :
      ∀ f ∈ faceOrder, z (witnessEdge f) = 0 :=
    zero_on_facePeelOrder_from C htait z baseZero faceBoundary witnessEdge
      faceOrder hzeroBase hstep horth
  intro e he
  rcases (mem_facePeelWitnessSupport_iff faceOrder witnessEdge).1 he with ⟨f, hf, rfl⟩
  exact hfaces f hf

end Mettapedia.GraphTheory.FourColor
