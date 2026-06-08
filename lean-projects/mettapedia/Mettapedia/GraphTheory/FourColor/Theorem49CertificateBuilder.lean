import Mathlib.Data.List.Sort
import Mettapedia.GraphTheory.FourColor.Theorem49Certificate

namespace Mettapedia.GraphTheory.FourColor

section

variable {F : Type*}

/-- The strict parent relation induced by a partial parent map. -/
def ParentRel (parentFace : F → Option F) : F → F → Prop :=
  fun f g => parentFace g = some f

/-- A parent map is well founded whenever some natural-valued height decreases strictly along
every parent edge. -/
theorem wellFounded_parentRel_of_lt_height (parentFace : F → Option F) (height : F → ℕ)
    (hheight : ∀ {g f : F}, parentFace g = some f → height f < height g) :
    WellFounded (ParentRel parentFace) := by
  have hSub : Subrelation (ParentRel parentFace) (InvImage (· < ·) height) := by
    intro x y hxy
    exact hheight (g := y) (f := x) hxy
  exact Subrelation.wf hSub <| InvImage.wf _ (Nat.lt_wfRel).2

/-- A two-cycle in the parent map already obstructs well foundedness. -/
theorem not_wellFounded_parentRel_of_twoCycle (parentFace : F → Option F) {f g : F}
    (hfg : parentFace g = some f) (hgf : parentFace f = some g) :
    ¬ WellFounded (ParentRel parentFace) := by
  intro hWF
  exact hWF.asymmetric _ _ hfg hgf

/-- Reflexive-transitive closure of strict height increase gives weak height increase. -/
theorem le_of_reflTransGen_height_lt (height : F → ℕ) {a b : F}
    (h : Relation.ReflTransGen (fun f g => height f < height g) a b) :
    height a ≤ height b := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact le_rfl
  | head hfg _ ih => exact le_trans (le_of_lt hfg) ih

/-- A finite strict-height chain cannot close by a final strict edge from its last element back to
its head.  This is the list-level obstruction behind witness-dependency cycles. -/
theorem false_of_isChain_height_lt_and_getLast_lt_head (height : F → ℕ) {cycle : List F}
    (hne : cycle ≠ [])
    (hchain : List.IsChain (fun f g => height f < height g) cycle)
    (hloop : height (cycle.getLast hne) < height (cycle.head hne)) :
    False := by
  have hrt : Relation.ReflTransGen (fun f g => height f < height g)
      (cycle.head hne) (cycle.getLast hne) :=
    List.relationReflTransGen_of_exists_isChain cycle hchain hne
  have hle : height (cycle.head hne) ≤ height (cycle.getLast hne) :=
    le_of_reflTransGen_height_lt height hrt
  exact (not_lt_of_ge hle) hloop

end

variable {V F : Type*} [DecidableEq V] [DecidableEq F]

/-- Canonical height attached to a well-founded parent map: roots have height `0`, and every child
has height one more than its parent. This removes the need to carry an explicit numeric height
function when the parent relation is already known to be well founded. -/
noncomputable def parentHeight (parentFace : F → Option F)
    (hWF : WellFounded (ParentRel parentFace)) : F → ℕ :=
  hWF.fix (C := fun _ => ℕ) fun g ih =>
    match h : parentFace g with
    | some f => ih f h + 1
    | none => 0

omit [DecidableEq F] in
theorem parentHeight_eq_zero_of_parent_eq_none (parentFace : F → Option F)
    (hWF : WellFounded (ParentRel parentFace)) {f : F} (hf : parentFace f = none) :
    parentHeight parentFace hWF f = 0 := by
  unfold parentHeight
  rw [WellFounded.fix_eq]
  split
  · rename_i p h
    cases hf.symm.trans h
  · rfl

omit [DecidableEq F] in
theorem parentHeight_eq_succ_of_parent_eq_some (parentFace : F → Option F)
    (hWF : WellFounded (ParentRel parentFace)) {g f : F} (hgf : parentFace g = some f) :
    parentHeight parentFace hWF g = parentHeight parentFace hWF f + 1 := by
  unfold parentHeight
  rw [WellFounded.fix_eq]
  split
  · rename_i p h
    have hp : p = f := by
      apply Option.some.inj
      exact h.symm.trans hgf
    subst hp
    rfl
  · rename_i h
    cases h.symm.trans hgf

omit [DecidableEq F] in
theorem parentHeight_lt_of_parent (parentFace : F → Option F)
    (hWF : WellFounded (ParentRel parentFace)) {g f : F} (hgf : parentFace g = some f) :
    parentHeight parentFace hWF f < parentHeight parentFace hWF g := by
  rw [parentHeight_eq_succ_of_parent_eq_some parentFace hWF hgf]
  exact Nat.lt_succ_self _

omit [DecidableEq F] in
/-- A well-founded parent map cannot contain a nonempty finite closed parent chain.  This is the
parent-map analogue of `false_of_isChain_height_lt_and_getLast_lt_head`. -/
theorem false_of_isChain_parentRel_and_getLast_parent_head (parentFace : F → Option F)
    (hWF : WellFounded (ParentRel parentFace)) {cycle : List F}
    (hne : cycle ≠ [])
    (hchain : List.IsChain (ParentRel parentFace) cycle)
    (hloop : ParentRel parentFace (cycle.getLast hne) (cycle.head hne)) :
    False := by
  have hheightChain :
      List.IsChain
        (fun f g => parentHeight parentFace hWF f < parentHeight parentFace hWF g)
        cycle := by
    exact hchain.imp (by
      intro f g hparent
      exact parentHeight_lt_of_parent parentFace hWF hparent)
  have hloopHeight :
      parentHeight parentFace hWF (cycle.getLast hne) <
        parentHeight parentFace hWF (cycle.head hne) :=
    parentHeight_lt_of_parent parentFace hWF hloop
  exact false_of_isChain_height_lt_and_getLast_lt_head
    (parentHeight parentFace hWF) hne hheightChain hloopHeight

/-- Canonical decreasing-height order on a finite face set. Ties are left arbitrary; only the
weak height monotonicity matters for the peeling argument. -/
noncomputable def heightOrderedFaceOrder (peelFaces : Finset F) (height : F → ℕ) : List F :=
  peelFaces.toList.mergeSort (fun f g => height g ≤ height f)

omit [DecidableEq F] in
theorem mem_heightOrderedFaceOrder_iff (peelFaces : Finset F) (height : F → ℕ) {f : F} :
    f ∈ heightOrderedFaceOrder peelFaces height ↔ f ∈ peelFaces := by
  unfold heightOrderedFaceOrder
  rw [List.Perm.mem_iff (List.mergeSort_perm _ _), Finset.mem_toList]

omit [DecidableEq F] in
theorem pairwise_heightOrderedFaceOrder (peelFaces : Finset F) (height : F → ℕ) :
    List.Pairwise (fun f g => height g ≤ height f) (heightOrderedFaceOrder peelFaces height) := by
  unfold heightOrderedFaceOrder
  let r : F → F → Prop := fun f g => height g ≤ height f
  let _ : IsTrans F r := ⟨by
    intro a b c hab hbc
    exact le_trans hbc hab⟩
  let _ : Std.Total r := ⟨by
    intro a b
    exact le_total (height b) (height a)⟩
  simpa [r] using (List.pairwise_mergeSort' (r := r) peelFaces.toList)

omit [DecidableEq F] in
theorem height_le_of_mem_suffix_of_pairwise_heightOrder {height : F → ℕ} :
    ∀ {faceOrder : List F},
      List.Pairwise (fun f g => height g ≤ height f) faceOrder →
      ∀ l₁ l₂ f g, faceOrder = l₁ ++ f :: l₂ → g ∈ l₂ → height g ≤ height f := by
  intro faceOrder hpair l₁
  induction l₁ generalizing faceOrder with
  | nil =>
      intro l₂ f g hsplit hg
      rw [hsplit] at hpair
      simpa using List.rel_of_pairwise_cons hpair hg
  | cons a l₁ ih =>
      intro l₂ f g hsplit hg
      rw [List.cons_append] at hsplit
      rw [hsplit] at hpair
      rcases List.pairwise_cons.1 hpair with ⟨_, htail⟩
      exact ih htail l₂ f g rfl hg

omit [DecidableEq F] in
theorem heightOrderedFaceOrder_order (peelFaces : Finset F) (height : F → ℕ) :
    ∀ l₁ l₂ f g, heightOrderedFaceOrder peelFaces height = l₁ ++ f :: l₂ →
      g ∈ l₂ → height g ≤ height f :=
  height_le_of_mem_suffix_of_pairwise_heightOrder
    (pairwise_heightOrderedFaceOrder peelFaces height)

/-- Partial height-ordered certificate builder: a witness list covering the ambient interior-edge
support is enough. Faces outside the peel list may be boundary-rooted and need no witness edge. -/
def boundaryRootedFacePeelCertificate_of_heightOrdered_facePeelWitnessCover {G : SimpleGraph V}
    (allFaces : Finset F) (faceBoundary : F → Finset G.edgeSet)
    (faceOrder : List F) (witnessEdge : F → G.edgeSet) (height : F → ℕ)
    (hcover : interiorEdgeSupport faceBoundary allFaces ⊆
      facePeelWitnessSupport faceOrder witnessEdge)
    (horder : ∀ l₁ l₂ f g, faceOrder = l₁ ++ f :: l₂ → g ∈ l₂ → height g ≤ height f)
    (hwitness : ∀ f ∈ faceOrder, witnessEdge f ∈ faceBoundary f)
    (hrest : ∀ f ∈ faceOrder, ∀ e ∈ (faceBoundary f).erase (witnessEdge f),
      e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
        ∃ g ∈ faceOrder, witnessEdge g = e ∧ height f < height g) :
    BoundaryRootedFacePeelCertificate allFaces faceBoundary where
  faceOrder := faceOrder
  witnessEdge := witnessEdge
  coverInterior := hcover
  step := by
    intro l₁ l₂ f hsplit
    refine ⟨hwitness f (by rw [hsplit]; simp), ?_⟩
    intro e he
    rcases hrest f (by rw [hsplit]; simp) e he with hboundary | ⟨g, hg, hge, hlt⟩
    · exact Finset.mem_union.2 <| Or.inl hboundary
    · have hgPrefix : g ∈ l₁ := by
        rw [hsplit] at hg
        rcases (by simpa using hg : g ∈ l₁ ∨ g = f ∨ g ∈ l₂) with hgL | rfl | hgR
        · exact hgL
        · exact (lt_irrefl _ hlt).elim
        · have hle : height g ≤ height f := horder l₁ l₂ f g hsplit hgR
          exact (Nat.not_le_of_lt hlt hle).elim
      exact Finset.mem_union.2 <| Or.inr <|
        (mem_facePeelWitnessSupport_iff l₁ witnessEdge).2 ⟨g, hgPrefix, hge⟩

/-- Parent-linked partial certificate builder. This is the form closest to a rooted interior-dual
forest: a peeled face only needs to know which later face is its parent, and every non-witness edge
must belong either to the ambient boundary support or to one of its children. -/
def boundaryRootedFacePeelCertificate_of_heightOrdered_parentFacePeelWitnessCover {G : SimpleGraph V}
    (allFaces : Finset F) (faceBoundary : F → Finset G.edgeSet)
    (faceOrder : List F) (parentFace : F → Option F)
    (witnessEdge : F → G.edgeSet) (height : F → ℕ)
    (hcover : interiorEdgeSupport faceBoundary allFaces ⊆
      facePeelWitnessSupport faceOrder witnessEdge)
    (horder : ∀ l₁ l₂ f g, faceOrder = l₁ ++ f :: l₂ → g ∈ l₂ → height g ≤ height f)
    (hwitness : ∀ f ∈ faceOrder, witnessEdge f ∈ faceBoundary f)
    (hchildren : ∀ f ∈ faceOrder, ∀ e ∈ (faceBoundary f).erase (witnessEdge f),
      e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
        ∃ g ∈ faceOrder, parentFace g = some f ∧ witnessEdge g = e)
    (hheight : ∀ g ∈ faceOrder, ∀ f, parentFace g = some f → height f < height g) :
    BoundaryRootedFacePeelCertificate allFaces faceBoundary :=
  boundaryRootedFacePeelCertificate_of_heightOrdered_facePeelWitnessCover
    allFaces faceBoundary faceOrder witnessEdge height hcover horder hwitness
      (by
        intro f hf e he
        rcases hchildren f hf e he with hboundary | ⟨g, hg, hparent, hge⟩
        · exact Or.inl hboundary
        · exact Or.inr ⟨g, hg, hge, hheight g hg f hparent⟩)

/-- Root-aware height-ordered peeling form of the Theorem 4.9 annihilator step. Unlike the
certificate-packaged wrapper below, this theorem does not require every ambient face to carry a
witness edge. It is enough to specify a list of faces whose witness-edge support covers the ambient
interior edges, provided the list is compatible with a height function and every non-witness edge
on a listed face is either ambient boundary support or the witness edge of a strictly higher listed
face. This matches the actual dual-forest peeling geometry more closely, since boundary-rooted
faces need not own witness edges. -/
theorem zero_on_ambientFaceSupport_of_heightOrdered_facePeelWitnessCover {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (allFaces : Finset F) (faceBoundary : F → Finset G.edgeSet)
    (faceOrder : List F) (witnessEdge : F → G.edgeSet) (height : F → ℕ)
    (hcover : interiorEdgeSupport faceBoundary allFaces ⊆
      facePeelWitnessSupport faceOrder witnessEdge)
    (horder : ∀ l₁ l₂ f g, faceOrder = l₁ ++ f :: l₂ → g ∈ l₂ → height g ≤ height f)
    (hwitness : ∀ f ∈ faceOrder, witnessEdge f ∈ faceBoundary f)
    (hrest : ∀ f ∈ faceOrder, ∀ e ∈ (faceBoundary f).erase (witnessEdge f),
      e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
        ∃ g ∈ faceOrder, witnessEdge g = e ∧ height f < height g)
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport faceBoundary allFaces allFaces, z e = 0)
    (horth : ∀ f ∈ faceOrder,
      ∀ γ, γ ≠ 0 → γ ≠ C (witnessEdge f) →
        chainDot
            (boundaryBicoloredEdges C (C (witnessEdge f)) (C (witnessEdge f) + γ)
              (faceBoundary f))
            z
            (polarizedFaceGenerator C (C (witnessEdge f)) (C (witnessEdge f) + γ)
              (faceBoundary f)) = 0) :
    ∀ e ∈ allFaces.biUnion faceBoundary, z e = 0 := by
  exact zero_on_ambientFaceSupport_of_boundaryRootedFacePeelCertificate
    (C := C) (htait := htait) (z := z)
    (allFaces := allFaces) (faceBoundary := faceBoundary)
    (cert := boundaryRootedFacePeelCertificate_of_heightOrdered_facePeelWitnessCover
      allFaces faceBoundary faceOrder witnessEdge height hcover horder hwitness hrest)
    hall hzeroBoundary horth

/-- Parent-linked form of the height-ordered witness-cover theorem. This matches the usual forest
picture more closely: every non-witness edge on a peeled face is either ambient boundary support
or is the witness edge of one of its children, and the height function is only required to increase
strictly along parent edges. -/
theorem zero_on_ambientFaceSupport_of_heightOrdered_parentFacePeelWitnessCover
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (allFaces : Finset F) (faceBoundary : F → Finset G.edgeSet)
    (faceOrder : List F) (parentFace : F → Option F)
    (witnessEdge : F → G.edgeSet) (height : F → ℕ)
    (hcover : interiorEdgeSupport faceBoundary allFaces ⊆
      facePeelWitnessSupport faceOrder witnessEdge)
    (horder : ∀ l₁ l₂ f g, faceOrder = l₁ ++ f :: l₂ → g ∈ l₂ → height g ≤ height f)
    (hwitness : ∀ f ∈ faceOrder, witnessEdge f ∈ faceBoundary f)
    (hchildren : ∀ f ∈ faceOrder, ∀ e ∈ (faceBoundary f).erase (witnessEdge f),
      e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
        ∃ g ∈ faceOrder, parentFace g = some f ∧ witnessEdge g = e)
    (hheight : ∀ g ∈ faceOrder, ∀ f, parentFace g = some f → height f < height g)
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport faceBoundary allFaces allFaces, z e = 0)
    (horth : ∀ f ∈ faceOrder,
      ∀ γ, γ ≠ 0 → γ ≠ C (witnessEdge f) →
        chainDot
            (boundaryBicoloredEdges C (C (witnessEdge f)) (C (witnessEdge f) + γ)
              (faceBoundary f))
            z
            (polarizedFaceGenerator C (C (witnessEdge f)) (C (witnessEdge f) + γ)
              (faceBoundary f)) = 0) :
    ∀ e ∈ allFaces.biUnion faceBoundary, z e = 0 := by
  exact zero_on_ambientFaceSupport_of_boundaryRootedFacePeelCertificate
    (C := C) (htait := htait) (z := z)
    (allFaces := allFaces) (faceBoundary := faceBoundary)
    (cert := boundaryRootedFacePeelCertificate_of_heightOrdered_parentFacePeelWitnessCover
      allFaces faceBoundary faceOrder parentFace witnessEdge height
      hcover horder hwitness hchildren hheight)
    hall hzeroBoundary horth

/-- Height-ordered witness-cover theorem with the face order synthesized canonically from the face
set and height function. This removes the explicit ordering obligation from downstream forest-based
instantiations. -/
theorem zero_on_ambientFaceSupport_of_sortedHeightOrdered_facePeelWitnessCover {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (allFaces peelFaces : Finset F) (faceBoundary : F → Finset G.edgeSet)
    (witnessEdge : F → G.edgeSet) (height : F → ℕ)
    (hcover : interiorEdgeSupport faceBoundary allFaces ⊆ peelFaces.image witnessEdge)
    (hwitness : ∀ f ∈ peelFaces, witnessEdge f ∈ faceBoundary f)
    (hrest : ∀ f ∈ peelFaces, ∀ e ∈ (faceBoundary f).erase (witnessEdge f),
      e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
        ∃ g ∈ peelFaces, witnessEdge g = e ∧ height f < height g)
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport faceBoundary allFaces allFaces, z e = 0)
    (horth : ∀ f ∈ peelFaces,
      ∀ γ, γ ≠ 0 → γ ≠ C (witnessEdge f) →
        chainDot
            (boundaryBicoloredEdges C (C (witnessEdge f)) (C (witnessEdge f) + γ)
              (faceBoundary f))
            z
            (polarizedFaceGenerator C (C (witnessEdge f)) (C (witnessEdge f) + γ)
              (faceBoundary f)) = 0) :
    ∀ e ∈ allFaces.biUnion faceBoundary, z e = 0 := by
  exact zero_on_ambientFaceSupport_of_heightOrdered_facePeelWitnessCover
    (C := C) (htait := htait) (z := z) (allFaces := allFaces) (faceBoundary := faceBoundary)
    (faceOrder := heightOrderedFaceOrder peelFaces height)
    (witnessEdge := witnessEdge) (height := height)
    (hcover := by
      intro e he
      rcases Finset.mem_image.1 (hcover he) with ⟨f, hf, rfl⟩
      exact (mem_facePeelWitnessSupport_iff _ _).2
        ⟨f, (mem_heightOrderedFaceOrder_iff peelFaces height).2 hf, rfl⟩)
    (horder := heightOrderedFaceOrder_order peelFaces height)
    (hwitness := by
      intro f hf
      exact hwitness f ((mem_heightOrderedFaceOrder_iff peelFaces height).1 hf))
    (hrest := by
      intro f hf e he
      rcases hrest f ((mem_heightOrderedFaceOrder_iff peelFaces height).1 hf) e he with
        hboundary | ⟨g, hg, hge, hlt⟩
      · exact Or.inl hboundary
      · exact Or.inr ⟨g, (mem_heightOrderedFaceOrder_iff peelFaces height).2 hg, hge, hlt⟩)
    hall hzeroBoundary
    (by
      intro f hf γ hγ0 hγd
      exact horth f ((mem_heightOrderedFaceOrder_iff peelFaces height).1 hf) γ hγ0 hγd)

/-- Parent-linked version of the automatic height-sorted witness-cover theorem. This is the most
direct current bridge from a finite rooted forest description to the Theorem 4.9 annihilator
conclusion. -/
noncomputable def boundaryRootedFacePeelCertificate_of_sortedHeightOrdered_parentFacePeelWitnessCover
    {G : SimpleGraph V}
    (allFaces peelFaces : Finset F) (faceBoundary : F → Finset G.edgeSet)
    (parentFace : F → Option F) (witnessEdge : F → G.edgeSet) (height : F → ℕ)
    (hcover : interiorEdgeSupport faceBoundary allFaces ⊆ peelFaces.image witnessEdge)
    (hwitness : ∀ f ∈ peelFaces, witnessEdge f ∈ faceBoundary f)
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (faceBoundary f).erase (witnessEdge f),
      e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
        ∃ g ∈ peelFaces, parentFace g = some f ∧ witnessEdge g = e)
    (hheight : ∀ g ∈ peelFaces, ∀ f, parentFace g = some f → height f < height g) :
    BoundaryRootedFacePeelCertificate allFaces faceBoundary :=
  boundaryRootedFacePeelCertificate_of_heightOrdered_parentFacePeelWitnessCover
    allFaces faceBoundary (heightOrderedFaceOrder peelFaces height)
    parentFace witnessEdge height
    (by
      intro e he
      rcases Finset.mem_image.1 (hcover he) with ⟨f, hf, rfl⟩
      exact (mem_facePeelWitnessSupport_iff _ _).2
        ⟨f, (mem_heightOrderedFaceOrder_iff peelFaces height).2 hf, rfl⟩)
    (heightOrderedFaceOrder_order peelFaces height)
    (by
      intro f hf
      exact hwitness f ((mem_heightOrderedFaceOrder_iff peelFaces height).1 hf))
    (by
      intro f hf e he
      rcases hchildren f ((mem_heightOrderedFaceOrder_iff peelFaces height).1 hf) e he with
        hboundary | ⟨g, hg, hparent, hge⟩
      · exact Or.inl hboundary
      · exact Or.inr
          ⟨g, (mem_heightOrderedFaceOrder_iff peelFaces height).2 hg, hparent, hge⟩)
    (by
      intro g hg f hgf
      exact hheight g ((mem_heightOrderedFaceOrder_iff peelFaces height).1 hg) f hgf)

/-- Parent-linked version of the automatic height-sorted witness-cover theorem. This is the most
direct current bridge from a finite rooted forest description to the Theorem 4.9 annihilator
conclusion. -/
theorem zero_on_ambientFaceSupport_of_sortedHeightOrdered_parentFacePeelWitnessCover
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (allFaces peelFaces : Finset F) (faceBoundary : F → Finset G.edgeSet)
    (parentFace : F → Option F) (witnessEdge : F → G.edgeSet) (height : F → ℕ)
    (hcover : interiorEdgeSupport faceBoundary allFaces ⊆ peelFaces.image witnessEdge)
    (hwitness : ∀ f ∈ peelFaces, witnessEdge f ∈ faceBoundary f)
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (faceBoundary f).erase (witnessEdge f),
      e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
        ∃ g ∈ peelFaces, parentFace g = some f ∧ witnessEdge g = e)
    (hheight : ∀ g ∈ peelFaces, ∀ f, parentFace g = some f → height f < height g)
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport faceBoundary allFaces allFaces, z e = 0)
    (horth : ∀ f ∈ peelFaces,
      ∀ γ, γ ≠ 0 → γ ≠ C (witnessEdge f) →
        chainDot
            (boundaryBicoloredEdges C (C (witnessEdge f)) (C (witnessEdge f) + γ)
              (faceBoundary f))
            z
            (polarizedFaceGenerator C (C (witnessEdge f)) (C (witnessEdge f) + γ)
              (faceBoundary f)) = 0) :
    ∀ e ∈ allFaces.biUnion faceBoundary, z e = 0 := by
  exact zero_on_ambientFaceSupport_of_boundaryRootedFacePeelCertificate
    (C := C) (htait := htait) (z := z)
    (allFaces := allFaces) (faceBoundary := faceBoundary)
    (cert :=
      boundaryRootedFacePeelCertificate_of_sortedHeightOrdered_parentFacePeelWitnessCover
        allFaces peelFaces faceBoundary parentFace witnessEdge height
        hcover hwitness hchildren hheight)
    hall hzeroBoundary
    (by
      intro f hf γ hγ0 hγd
      exact horth f ((mem_heightOrderedFaceOrder_iff peelFaces height).1 hf) γ hγ0 hγd)

/-- Well-founded-parent version of the automatic height-sorted witness-cover theorem. This is the
closest interface to an abstract rooted forest: rather than carrying a separate numeric height
function, it is enough to know that the parent relation is well founded. -/
noncomputable def boundaryRootedFacePeelCertificate_of_wellFounded_parentFacePeelWitnessCover
    {G : SimpleGraph V}
    (allFaces peelFaces : Finset F) (faceBoundary : F → Finset G.edgeSet)
    (parentFace : F → Option F) (witnessEdge : F → G.edgeSet)
    (hWF : WellFounded (ParentRel parentFace))
    (hcover : interiorEdgeSupport faceBoundary allFaces ⊆ peelFaces.image witnessEdge)
    (hwitness : ∀ f ∈ peelFaces, witnessEdge f ∈ faceBoundary f)
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (faceBoundary f).erase (witnessEdge f),
      e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
        ∃ g ∈ peelFaces, parentFace g = some f ∧ witnessEdge g = e) :
    BoundaryRootedFacePeelCertificate allFaces faceBoundary :=
  boundaryRootedFacePeelCertificate_of_sortedHeightOrdered_parentFacePeelWitnessCover
    allFaces peelFaces faceBoundary parentFace witnessEdge (parentHeight parentFace hWF)
    hcover hwitness hchildren
    (by
      intro g hg f hgf
      exact parentHeight_lt_of_parent parentFace hWF hgf)

/-- Well-founded-parent version of the automatic height-sorted witness-cover theorem. This is the
closest interface to an abstract rooted forest: rather than carrying a separate numeric height
function, it is enough to know that the parent relation is well founded. -/
theorem zero_on_ambientFaceSupport_of_wellFounded_parentFacePeelWitnessCover
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (allFaces peelFaces : Finset F) (faceBoundary : F → Finset G.edgeSet)
    (parentFace : F → Option F) (witnessEdge : F → G.edgeSet)
    (hWF : WellFounded (ParentRel parentFace))
    (hcover : interiorEdgeSupport faceBoundary allFaces ⊆ peelFaces.image witnessEdge)
    (hwitness : ∀ f ∈ peelFaces, witnessEdge f ∈ faceBoundary f)
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (faceBoundary f).erase (witnessEdge f),
      e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
        ∃ g ∈ peelFaces, parentFace g = some f ∧ witnessEdge g = e)
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport faceBoundary allFaces allFaces, z e = 0)
    (horth : ∀ f ∈ peelFaces,
      ∀ γ, γ ≠ 0 → γ ≠ C (witnessEdge f) →
        chainDot
            (boundaryBicoloredEdges C (C (witnessEdge f)) (C (witnessEdge f) + γ)
              (faceBoundary f))
            z
            (polarizedFaceGenerator C (C (witnessEdge f)) (C (witnessEdge f) + γ)
              (faceBoundary f)) = 0) :
    ∀ e ∈ allFaces.biUnion faceBoundary, z e = 0 := by
  exact zero_on_ambientFaceSupport_of_boundaryRootedFacePeelCertificate
    (C := C) (htait := htait) (z := z)
    (allFaces := allFaces) (faceBoundary := faceBoundary)
    (cert :=
      boundaryRootedFacePeelCertificate_of_wellFounded_parentFacePeelWitnessCover
        allFaces peelFaces faceBoundary parentFace witnessEdge
        hWF hcover hwitness hchildren)
    hall hzeroBoundary
    (by
      intro f hf γ hγ0 hγd
      exact horth f
        ((mem_heightOrderedFaceOrder_iff peelFaces (parentHeight parentFace hWF)).1 hf)
        γ hγ0 hγd)

/-- Build a boundary-rooted peel certificate from a face order that respects a height function.
The local combinatorial condition is now height-based rather than prefix-based: every non-witness
edge on a face is either ambient boundary support or is the witness edge of some strictly higher
face. Any face order compatible with decreasing height then yields the prefix condition required by
`BoundaryRootedFacePeelCertificate`. -/
def boundaryRootedFacePeelCertificate_of_heightOrdered_faces {G : SimpleGraph V}
    (allFaces : Finset F) (faceBoundary : F → Finset G.edgeSet)
    (faceOrder : List F) (witnessEdge : F → G.edgeSet) (height : F → ℕ)
    (hfaces : ∀ f, f ∈ faceOrder ↔ f ∈ allFaces)
    (horder : ∀ l₁ l₂ f g, faceOrder = l₁ ++ f :: l₂ → g ∈ l₂ → height g ≤ height f)
    (hcover : interiorEdgeSupport faceBoundary allFaces ⊆ allFaces.image witnessEdge)
    (hwitness : ∀ f ∈ allFaces, witnessEdge f ∈ faceBoundary f)
    (hrest : ∀ f ∈ allFaces, ∀ e ∈ (faceBoundary f).erase (witnessEdge f),
      e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
        ∃ g ∈ allFaces, witnessEdge g = e ∧ height f < height g) :
    BoundaryRootedFacePeelCertificate allFaces faceBoundary where
  faceOrder := faceOrder
  witnessEdge := witnessEdge
  coverInterior := by
    intro e he
    rcases Finset.mem_image.1 (hcover he) with ⟨f, hf, rfl⟩
    exact (mem_facePeelWitnessSupport_iff faceOrder witnessEdge).2 ⟨f, (hfaces f).2 hf, rfl⟩
  step := by
    intro l₁ l₂ f hsplit
    refine ⟨hwitness f ((hfaces f).1 ?_), ?_⟩
    · rw [hsplit]
      simp
    · intro e he
      rcases hrest f ((hfaces f).1 (by rw [hsplit]; simp)) e he with hboundary | ⟨g, hg, hge, hlt⟩
      · exact Finset.mem_union.2 <| Or.inl hboundary
      · have hgOrder : g ∈ faceOrder := (hfaces g).2 hg
        have hgPrefix : g ∈ l₁ := by
          rw [hsplit] at hgOrder
          rcases (by simpa using hgOrder : g ∈ l₁ ∨ g = f ∨ g ∈ l₂) with hgL | rfl | hgR
          · exact hgL
          · exact (lt_irrefl _ hlt).elim
          · have hle : height g ≤ height f := horder l₁ l₂ f g hsplit hgR
            exact (Nat.not_le_of_lt hlt hle).elim
        exact Finset.mem_union.2 <| Or.inr <|
          (mem_facePeelWitnessSupport_iff l₁ witnessEdge).2 ⟨g, hgPrefix, hge⟩

/-- Direct annihilator form of the height-based certificate builder. Once the face order is known
to be compatible with decreasing height, and every non-witness boundary edge points either to the
ambient boundary support or to the witness edge of a strictly higher face, the full Theorem 4.9
annihilator conclusion on the ambient face-edge support follows immediately. -/
theorem zero_on_ambientFaceSupport_of_heightOrdered_faces {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (allFaces : Finset F) (faceBoundary : F → Finset G.edgeSet)
    (faceOrder : List F) (witnessEdge : F → G.edgeSet) (height : F → ℕ)
    (hfaces : ∀ f, f ∈ faceOrder ↔ f ∈ allFaces)
    (horder : ∀ l₁ l₂ f g, faceOrder = l₁ ++ f :: l₂ → g ∈ l₂ → height g ≤ height f)
    (hcover : interiorEdgeSupport faceBoundary allFaces ⊆ allFaces.image witnessEdge)
    (hwitness : ∀ f ∈ allFaces, witnessEdge f ∈ faceBoundary f)
    (hrest : ∀ f ∈ allFaces, ∀ e ∈ (faceBoundary f).erase (witnessEdge f),
      e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
        ∃ g ∈ allFaces, witnessEdge g = e ∧ height f < height g)
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport faceBoundary allFaces allFaces, z e = 0)
    (horth : ∀ f ∈ faceOrder,
      ∀ γ, γ ≠ 0 → γ ≠ C (witnessEdge f) →
        chainDot
            (boundaryBicoloredEdges C (C (witnessEdge f)) (C (witnessEdge f) + γ)
              (faceBoundary f))
            z
            (polarizedFaceGenerator C (C (witnessEdge f)) (C (witnessEdge f) + γ)
              (faceBoundary f)) = 0) :
    ∀ e ∈ allFaces.biUnion faceBoundary, z e = 0 := by
  exact zero_on_ambientFaceSupport_of_heightOrdered_facePeelWitnessCover
    (C := C) (htait := htait) (z := z) (allFaces := allFaces) (faceBoundary := faceBoundary)
    (faceOrder := faceOrder) (witnessEdge := witnessEdge) (height := height)
    (hcover := by
      intro e he
      rcases Finset.mem_image.1 (hcover he) with ⟨f, hf, rfl⟩
      exact (mem_facePeelWitnessSupport_iff faceOrder witnessEdge).2 ⟨f, (hfaces f).2 hf, rfl⟩)
    horder
    (by
      intro f hf
      exact hwitness f ((hfaces f).1 hf))
    (by
      intro f hf e he
      rcases hrest f ((hfaces f).1 hf) e he with hboundary | ⟨g, hg, hge, hlt⟩
      · exact Or.inl hboundary
      · exact Or.inr ⟨g, (hfaces g).2 hg, hge, hlt⟩)
    hall hzeroBoundary horth

end Mettapedia.GraphTheory.FourColor
