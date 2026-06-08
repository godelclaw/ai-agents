import Mettapedia.GraphTheory.FourColor.PlanarBoundaryFaceBoundaryRun
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Infix

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- Boundary-edge vertices for a boundary-aware plane embedding: the ambient selected boundary
support, viewed as a type. This is the smallest concrete carrier on which one can talk about
connected boundary components without adding more topological structure than the current embedding
API provides. -/
abbrev PlanarBoundaryEdgeVertex {G : SimpleGraph V} (emb : PlaneEmbeddingWithBoundary G) :=
  ↥(selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)

/-- The primal shared-endpoint graph on ambient boundary edges. Two boundary edges are adjacent when
they are distinct and meet at a graph vertex. Reachability in this graph is the current concrete
proxy for belonging to the same boundary component. -/
def planarBoundarySupportEndpointAdjGraph {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) :
    SimpleGraph (PlanarBoundaryEdgeVertex emb) where
  Adj e f := e ≠ f ∧ ∃ v : V, v ∈ (e.1 : Sym2 V) ∧ v ∈ (f.1 : Sym2 V)
  symm := by
    intro e f h
    rcases h with ⟨hne, v, hvE, hvF⟩
    exact ⟨hne.symm, v, hvF, hvE⟩
  loopless := ⟨fun e h => h.1 rfl⟩

/-- Facewise boundary-component coherence in the root-free boundary graph: any two
selected-boundary edges on the same ambient face are connected in the primal shared-endpoint
boundary graph. -/
def BoundaryComponentReachableOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (f : AmbientFace emb.faces) : Prop :=
  ∀ ⦃e₁ e₂ : G.edgeSet⦄,
    e₁ ∈ emb.faceBoundary f.1 →
      e₂ ∈ emb.faceBoundary f.1 →
        (he₁ : e₁ ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) →
        (he₂ : e₂ ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) →
          (planarBoundarySupportEndpointAdjGraph emb).Reachable ⟨e₁, he₁⟩ ⟨e₂, he₂⟩

/-- A local facewise endpoint-sharing criterion for the selected-boundary graph: any two
selected-boundary edges on the same ambient face meet at a primal graph vertex. -/
def BoundaryEdgesShareEndpointOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (f : AmbientFace emb.faces) : Prop :=
  ∀ ⦃e₁ e₂ : G.edgeSet⦄,
    e₁ ∈ emb.faceBoundary f.1 →
      e₂ ∈ emb.faceBoundary f.1 →
        (he₁ : e₁ ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) →
          (he₂ : e₂ ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) →
            ∃ v : V, v ∈ (e₁ : Sym2 V) ∧ v ∈ (e₂ : Sym2 V)

private theorem exists_walk_of_isChain_head?_getLast?
    {α : Type*} {G : SimpleGraph α} :
    ∀ {l : List α} {u v : α},
      List.IsChain G.Adj l →
      l.head? = some u →
      l.getLast? = some v →
      ∃ p : G.Walk u v, p.support = l
  | [], u, v, _, hhead, _ => by
      simp at hhead
  | [a], u, v, _, hhead, hlast => by
      simp at hhead hlast
      subst hhead
      subst hlast
      exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | a :: b :: tl, u, v, hchain, hhead, hlast => by
      have hau : a = u := by
        simpa using hhead
      subst u
      have hab : G.Adj a b := by
        simpa using (List.isChain_cons_cons.mp hchain).1
      have htail : List.IsChain G.Adj (b :: tl) := by
        simpa using (List.isChain_cons_cons.mp hchain).2
      rcases exists_walk_of_isChain_head?_getLast? (u := b) (v := v) htail (by simp)
          (by simpa using hlast) with
        ⟨p, hp⟩
      refine ⟨SimpleGraph.Walk.cons hab p, ?_⟩
      simp [hp, SimpleGraph.Walk.support_cons]

private theorem nonempty_walk_from_head_of_isChain_mem
    {α : Type*} {G : SimpleGraph α} :
    ∀ {a : α} {tail : List α} {x : α},
      List.IsChain G.Adj (a :: tail) →
      x ∈ a :: tail →
      Nonempty (G.Walk a x)
  | a, [], x, _, hx => by
      simp at hx
      subst hx
      exact ⟨SimpleGraph.Walk.nil⟩
  | a, b :: tl, x, hchain, hx => by
      simp at hx
      rcases hx with rfl | hxTail
      · exact ⟨SimpleGraph.Walk.nil⟩
      · have hab : G.Adj a b := by
          simpa using (List.isChain_cons_cons.mp hchain).1
        have htail : List.IsChain G.Adj (b :: tl) := by
          simpa using (List.isChain_cons_cons.mp hchain).2
        rcases nonempty_walk_from_head_of_isChain_mem (a := b) (tail := tl) htail
            (by simpa using hxTail) with
          ⟨p⟩
        exact ⟨SimpleGraph.Walk.cons hab p⟩

/-- A source-facing face-local boundary-run witness: any two selected-boundary edges on the same
ambient face occur as the endpoints of an ordered chain of ambient selected-boundary edges lying on
that same face. This records the run as a list rather than as an already-built graph walk. -/
def BoundaryComponentRunOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (f : AmbientFace emb.faces) : Prop :=
  ∀ ⦃e₁ e₂ : G.edgeSet⦄,
    e₁ ∈ emb.faceBoundary f.1 →
      e₂ ∈ emb.faceBoundary f.1 →
        (he₁ : e₁ ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) →
          (he₂ : e₂ ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) →
            ∃ run : List (PlanarBoundaryEdgeVertex emb),
              List.IsChain (planarBoundarySupportEndpointAdjGraph emb).Adj run ∧
              run.head? = some ⟨e₁, he₁⟩ ∧
              run.getLast? = some ⟨e₂, he₂⟩ ∧
              ∀ x ∈ run, x.1 ∈ emb.faceBoundary f.1

/-- A stronger source-facing face-local shell: the selected-boundary edges on one ambient face can
be listed once and for all in an order whose consecutive edges share a primal endpoint. This is
closer to actual face-boundary geometry than demanding a fresh pairwise run for every two boundary
edges on the face. -/
def BoundarySelectedBoundaryRunOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (f : AmbientFace emb.faces) : Prop :=
  ∃ run : List (PlanarBoundaryEdgeVertex emb),
    List.IsChain (planarBoundarySupportEndpointAdjGraph emb).Adj run ∧
    ∀ x : PlanarBoundaryEdgeVertex emb,
      x ∈ run ↔
        x.1 ∈ emb.faceBoundary f.1 ∧
          x.1 ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces

/-- Graph-level root-free target for the selected-boundary run shell: there exists a
boundary-aware plane embedding of `G` on which every ambient face carries one ordered run of its
selected-boundary edges. -/
def AdmitsPlanarBoundarySelectedBoundaryRunOnFace (G : SimpleGraph V) : Prop :=
  ∃ emb : PlaneEmbeddingWithBoundary G,
    ∀ f : AmbientFace emb.faces, BoundarySelectedBoundaryRunOnFace (emb := emb) f

/-- Graph-level root-free target for boundary-component coherence: there exists a boundary-aware
plane embedding of `G` on which any two selected-boundary edges on the same ambient face are
connected in the shared-endpoint support graph. -/
def AdmitsPlanarBoundaryComponentReachableOnFace (G : SimpleGraph V) : Prop :=
  ∃ emb : PlaneEmbeddingWithBoundary G,
    ∀ f : AmbientFace emb.faces, BoundaryComponentReachableOnFace (emb := emb) f

theorem boundaryComponentRunOnFace_of_boundaryEdgesShareEndpointOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {f : AmbientFace emb.faces}
    (hshare : BoundaryEdgesShareEndpointOnFace (emb := emb) f) :
    BoundaryComponentRunOnFace (emb := emb) f := by
  intro e₁ e₂ he₁Face he₂Face he₁ he₂
  by_cases hEq : e₁ = e₂
  · refine ⟨[⟨e₁, he₁⟩], List.isChain_singleton _, by simp [hEq], by simp [hEq], ?_⟩
    intro x hx
    simp at hx
    subst hx
    exact he₁Face
  · rcases hshare he₁Face he₂Face he₁ he₂ with ⟨v, hv₁, hv₂⟩
    let hadj :
        (planarBoundarySupportEndpointAdjGraph emb).Adj ⟨e₁, he₁⟩ ⟨e₂, he₂⟩ :=
      ⟨by
        intro hSubtype
        apply hEq
        exact congrArg Subtype.val hSubtype,
        v, hv₁, hv₂⟩
    refine ⟨[⟨e₁, he₁⟩, ⟨e₂, he₂⟩], (List.isChain_pair).2 hadj, by simp, by simp, ?_⟩
    intro x hx
    simp at hx
    rcases hx with rfl | rfl
    · exact he₁Face
    · exact he₂Face

/-- A face-local walk witness for boundary-component coherence: any two selected-boundary edges on
the same ambient face are connected by a walk in the shared-endpoint boundary graph whose every
visited boundary edge still lies on that same ambient face. This is weaker than pairwise
endpoint-sharing and closer to the boundary-run geometry used in the paper. -/
def BoundaryComponentWalkOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (f : AmbientFace emb.faces) : Prop :=
  ∀ ⦃e₁ e₂ : G.edgeSet⦄,
    e₁ ∈ emb.faceBoundary f.1 →
      e₂ ∈ emb.faceBoundary f.1 →
        (he₁ : e₁ ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) →
          (he₂ : e₂ ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) →
            ∃ p :
                (planarBoundarySupportEndpointAdjGraph emb).Walk
                  ⟨e₁, he₁⟩ ⟨e₂, he₂⟩,
              ∀ x ∈ p.support, x.1 ∈ emb.faceBoundary f.1

theorem boundaryComponentWalkOnFace_of_boundaryComponentRunOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {f : AmbientFace emb.faces}
    (hrun : BoundaryComponentRunOnFace (emb := emb) f) :
    BoundaryComponentWalkOnFace (emb := emb) f := by
  intro e₁ e₂ he₁Face he₂Face he₁ he₂
  rcases hrun he₁Face he₂Face he₁ he₂ with ⟨run, hchain, hhead, hlast, hface⟩
  rcases exists_walk_of_isChain_head?_getLast? hchain hhead hlast with ⟨p, hp⟩
  refine ⟨p, ?_⟩
  intro x hx
  exact hface x (hp ▸ hx)

theorem boundarySelectedBoundaryRunOnFace_of_boundarySelectedBoundaryArcOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {f : AmbientFace emb.faces}
    (harc : BoundarySelectedBoundaryArcOnFace (emb := emb) f) :
    BoundarySelectedBoundaryRunOnFace (emb := emb) f := by
  classical
  rcases harc with ⟨faceRun, selectedRun, hinfix, hselected⟩
  have hselectedChain :
      List.IsChain planarBoundaryEdgeEndpointAdj selectedRun :=
    faceRun.hchain.infix hinfix
  have hselectedSupport :
      ∀ e ∈ selectedRun, e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces := by
    intro e he
    exact (hselected e).1 he |>.2
  let run :
      List (PlanarBoundaryEdgeVertex emb) :=
    selectedRun.pmap (fun e he => (⟨e, he⟩ : PlanarBoundaryEdgeVertex emb)) hselectedSupport
  refine ⟨run, ?_, ?_⟩
  · exact List.isChain_pmap_of_isChain
      (f := fun e he => (⟨e, he⟩ : PlanarBoundaryEdgeVertex emb))
      (H := by
        intro a b ha hb hab
        exact ⟨by
          intro hEq
          exact hab.1 (congrArg Subtype.val hEq), hab.2⟩)
      hselectedChain hselectedSupport
  · intro x
    constructor
    · intro hx
      rcases (List.mem_pmap.1 hx) with ⟨e, he, hEq⟩
      have hval : e = x.1 := by
        simpa using congrArg Subtype.val hEq
      subst hval
      exact (hselected x.1).1 he
    · intro hx
      have hxRun : x.1 ∈ selectedRun := (hselected x.1).2 hx
      exact (List.mem_pmap.2 ⟨x.1, hxRun, Subtype.ext (by rfl)⟩)

theorem PlanarBoundarySelectedBoundaryArcGeometry.boundarySelectedBoundaryRunOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : PlanarBoundarySelectedBoundaryArcGeometry emb) :
    ∀ f : AmbientFace emb.faces, BoundarySelectedBoundaryRunOnFace (emb := emb) f := by
  intro f
  exact
    boundarySelectedBoundaryRunOnFace_of_boundarySelectedBoundaryArcOnFace
      (geom.boundarySelectedBoundaryArcOnFace f)

theorem PlanarBoundaryFaceBoundaryRunGeometry.boundarySelectedBoundaryRunOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : PlanarBoundaryFaceBoundaryRunGeometry emb)
    (harc : ∀ f : AmbientFace emb.faces, geom.SelectedBoundaryArcOnFace f) :
    ∀ f : AmbientFace emb.faces, BoundarySelectedBoundaryRunOnFace (emb := emb) f := by
  intro f
  exact
    boundarySelectedBoundaryRunOnFace_of_boundarySelectedBoundaryArcOnFace
      ((geom.boundarySelectedBoundaryArcOnFace harc) f)

theorem boundaryComponentReachableOnFace_of_boundarySelectedBoundaryRunOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {f : AmbientFace emb.faces}
    (hrun : BoundarySelectedBoundaryRunOnFace (emb := emb) f) :
    BoundaryComponentReachableOnFace (emb := emb) f := by
  intro e₁ e₂ he₁Face he₂Face he₁ he₂
  let x₁ : PlanarBoundaryEdgeVertex emb := ⟨e₁, he₁⟩
  let x₂ : PlanarBoundaryEdgeVertex emb := ⟨e₂, he₂⟩
  rcases hrun with ⟨run, hchain, hmem⟩
  have hx₁ : x₁ ∈ run := (hmem x₁).2 ⟨he₁Face, he₁⟩
  have hx₂ : x₂ ∈ run := (hmem x₂).2 ⟨he₂Face, he₂⟩
  cases run with
  | nil =>
      cases hx₁
  | cons a tail =>
      have hw₁ :
          (planarBoundarySupportEndpointAdjGraph emb).Reachable a x₁ := by
        rcases nonempty_walk_from_head_of_isChain_mem (a := a) (tail := tail) hchain hx₁ with
          ⟨p⟩
        exact ⟨p⟩
      have hw₂ :
          (planarBoundarySupportEndpointAdjGraph emb).Reachable a x₂ := by
        rcases nonempty_walk_from_head_of_isChain_mem (a := a) (tail := tail) hchain hx₂ with
          ⟨p⟩
        exact ⟨p⟩
      exact hw₁.symm.trans hw₂

theorem boundaryComponentReachableOnFace_of_boundarySelectedBoundaryArcOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {f : AmbientFace emb.faces}
    (harc : BoundarySelectedBoundaryArcOnFace (emb := emb) f) :
    BoundaryComponentReachableOnFace (emb := emb) f := by
  exact
    boundaryComponentReachableOnFace_of_boundarySelectedBoundaryRunOnFace
      (boundarySelectedBoundaryRunOnFace_of_boundarySelectedBoundaryArcOnFace harc)

theorem PlanarBoundarySelectedBoundaryArcGeometry.boundaryComponentReachableOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : PlanarBoundarySelectedBoundaryArcGeometry emb) :
    ∀ f : AmbientFace emb.faces, BoundaryComponentReachableOnFace (emb := emb) f := by
  intro f
  exact
    boundaryComponentReachableOnFace_of_boundarySelectedBoundaryRunOnFace
      (geom.boundarySelectedBoundaryRunOnFace f)

theorem PlanarBoundaryFaceBoundaryRunGeometry.boundaryComponentReachableOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : PlanarBoundaryFaceBoundaryRunGeometry emb)
    (harc : ∀ f : AmbientFace emb.faces, geom.SelectedBoundaryArcOnFace f) :
    ∀ f : AmbientFace emb.faces, BoundaryComponentReachableOnFace (emb := emb) f := by
  intro f
  exact
    boundaryComponentReachableOnFace_of_boundarySelectedBoundaryRunOnFace
      (geom.boundarySelectedBoundaryRunOnFace harc f)

theorem boundaryComponentWalkOnFace_of_boundaryEdgesShareEndpointOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {f : AmbientFace emb.faces}
    (hshare : BoundaryEdgesShareEndpointOnFace (emb := emb) f) :
    BoundaryComponentWalkOnFace (emb := emb) f := by
  exact
    boundaryComponentWalkOnFace_of_boundaryComponentRunOnFace
      (boundaryComponentRunOnFace_of_boundaryEdgesShareEndpointOnFace hshare)

theorem boundaryComponentReachableOnFace_of_boundaryComponentWalkOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {f : AmbientFace emb.faces}
    (hwalk : BoundaryComponentWalkOnFace (emb := emb) f) :
    BoundaryComponentReachableOnFace (emb := emb) f := by
  intro e₁ e₂ he₁Face he₂Face he₁ he₂
  rcases hwalk he₁Face he₂Face he₁ he₂ with ⟨p, _⟩
  exact ⟨p⟩

theorem boundaryComponentReachableOnFace_of_boundaryComponentRunOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {f : AmbientFace emb.faces}
    (hrun : BoundaryComponentRunOnFace (emb := emb) f) :
    BoundaryComponentReachableOnFace (emb := emb) f := by
  exact
    boundaryComponentReachableOnFace_of_boundaryComponentWalkOnFace
      (boundaryComponentWalkOnFace_of_boundaryComponentRunOnFace hrun)

theorem boundaryComponentReachableOnFace_of_boundaryEdgesShareEndpointOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {f : AmbientFace emb.faces}
    (hshare : BoundaryEdgesShareEndpointOnFace (emb := emb) f) :
    BoundaryComponentReachableOnFace (emb := emb) f := by
  exact
    boundaryComponentReachableOnFace_of_boundaryComponentWalkOnFace
      (boundaryComponentWalkOnFace_of_boundaryEdgesShareEndpointOnFace hshare)

theorem admitsPlanarBoundarySelectedBoundaryRunOnFace_of_admitsPlanarBoundarySelectedBoundaryArcGeometry
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundarySelectedBoundaryArcGeometry G) :
    AdmitsPlanarBoundarySelectedBoundaryRunOnFace G := by
  rcases hG with ⟨emb, ⟨geom⟩⟩
  exact ⟨emb, geom.boundarySelectedBoundaryRunOnFace⟩

theorem
    admitsPlanarBoundarySelectedBoundaryRunOnFace_of_admitsPlanarBoundaryFaceBoundaryRunGeometryAndSelectedBoundaryArcOnFace
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryFaceBoundaryRunGeometryAndSelectedBoundaryArcOnFace G) :
    AdmitsPlanarBoundarySelectedBoundaryRunOnFace G := by
  rcases hG with ⟨emb, geom, harc⟩
  exact ⟨emb, geom.boundarySelectedBoundaryRunOnFace harc⟩

theorem admitsPlanarBoundaryComponentReachableOnFace_of_admitsPlanarBoundarySelectedBoundaryRunOnFace
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundarySelectedBoundaryRunOnFace G) :
    AdmitsPlanarBoundaryComponentReachableOnFace G := by
  rcases hG with ⟨emb, hrun⟩
  exact ⟨emb, fun f => boundaryComponentReachableOnFace_of_boundarySelectedBoundaryRunOnFace
    (hrun f)⟩

theorem admitsPlanarBoundaryComponentReachableOnFace_of_admitsPlanarBoundarySelectedBoundaryArcGeometry
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundarySelectedBoundaryArcGeometry G) :
    AdmitsPlanarBoundaryComponentReachableOnFace G := by
  rcases hG with ⟨emb, ⟨geom⟩⟩
  exact ⟨emb, geom.boundaryComponentReachableOnFace⟩

theorem
    admitsPlanarBoundaryComponentReachableOnFace_of_admitsPlanarBoundaryFaceBoundaryRunGeometryAndSelectedBoundaryArcOnFace
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryFaceBoundaryRunGeometryAndSelectedBoundaryArcOnFace G) :
    AdmitsPlanarBoundaryComponentReachableOnFace G := by
  rcases hG with ⟨emb, geom, harc⟩
  exact ⟨emb, geom.boundaryComponentReachableOnFace harc⟩

end Mettapedia.GraphTheory.FourColor
