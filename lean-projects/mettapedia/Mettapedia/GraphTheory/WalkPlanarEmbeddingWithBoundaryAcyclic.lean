import Mettapedia.GraphTheory.WalkPlanarEmbeddingWithBoundary
import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace Mettapedia.GraphTheory

universe u

variable {V : Type u} [DecidableEq V]

namespace PlaneEmbeddingWithBoundary

theorem faces_nonempty_of_nonempty_edgeSet {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) (hE : Nonempty G.edgeSet) :
    emb.faces.Nonempty := by
  rcases hE with ⟨e⟩
  rcases Finset.mem_biUnion.1 (emb.edge_mem_faceSupport e) with ⟨f, hf, _⟩
  exact ⟨f, hf⟩

end PlaneEmbeddingWithBoundary

theorem not_nonempty_faceBoundaryClosedWalkGeometry_of_isAcyclic_of_faces_nonempty
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} (hAcyc : G.IsAcyclic)
    (hfaces : emb.faces.Nonempty) :
    ¬ Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalkGeometry emb) := by
  rintro ⟨geom⟩
  rcases hfaces with ⟨f, hf⟩
  let data := geom.faceBoundaryClosedWalk ⟨f, hf⟩
  have htrail : data.walk.IsTrail := by
    simpa [SimpleGraph.Walk.isTrail_def] using data.hnodup_edges
  have hpath : data.walk.IsPath := (hAcyc.isPath_iff_isTrail data.walk).2 htrail
  have hnil : data.walk = .nil := (SimpleGraph.Walk.isPath_iff_eq_nil data.walk).1 hpath
  have hnonempty := data.hnonempty
  rw [hnil] at hnonempty
  simp at hnonempty

theorem not_nonempty_faceBoundaryClosedWalkGeometry_of_isAcyclic_of_nonempty_edgeSet
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} (hAcyc : G.IsAcyclic)
    (hE : Nonempty G.edgeSet) :
    ¬ Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalkGeometry emb) := by
  exact
    not_nonempty_faceBoundaryClosedWalkGeometry_of_isAcyclic_of_faces_nonempty hAcyc
      (emb.faces_nonempty_of_nonempty_edgeSet hE)

theorem not_admitsFaceBoundaryClosedWalkGeometry_of_isAcyclic_of_nonempty_edgeSet
    {G : SimpleGraph V} (hAcyc : G.IsAcyclic) (hE : Nonempty G.edgeSet) :
    ¬ AdmitsFaceBoundaryClosedWalkGeometry G := by
  rintro ⟨emb, hgeom⟩
  exact
    not_nonempty_faceBoundaryClosedWalkGeometry_of_isAcyclic_of_nonempty_edgeSet hAcyc hE hgeom

end Mettapedia.GraphTheory
