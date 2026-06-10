import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryAnnulusBoundary
import Mettapedia.GraphTheory.OrderedPlanarEmbeddingWithBoundary
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Infix

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- The raw shared-endpoint adjacency relation on graph edges. This is the edge-level adjacency
used by the face-boundary order layer, before any restriction to the selected boundary support. -/
abbrev planarBoundaryEdgeEndpointAdj {G : SimpleGraph V} (e f : G.edgeSet) : Prop :=
  Mettapedia.GraphTheory.planarEmbeddingBoundaryEdgeEndpointAdj e f

/-- The generic per-face ordered endpoint-sharing run, specialized to the current annulus route. -/
abbrev FaceBoundaryEndpointRun {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) (f : AmbientFace emb.faces) :=
  PlaneEmbeddingWithBoundary.FaceBoundaryEndpointRun emb f

/-- The generic bundled face-boundary run geometry, specialized to the current annulus route. -/
abbrev PlanarBoundaryFaceBoundaryRunGeometry {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) :=
  PlaneEmbeddingWithBoundary.FaceBoundaryRunGeometry emb

/-- The existential face-local selected-boundary arc predicate obtained by forgetting any global
choice of per-face run package: a face admits some full ordered boundary run on which the
selected-boundary edges form one contiguous subrun. This is the raw local face-boundary geometry
input consumed downstream by the annulus boundary-component reductions. -/
def BoundarySelectedBoundaryArcOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (f : AmbientFace emb.faces) : Prop :=
  ∃ faceRun : FaceBoundaryEndpointRun emb f, ∃ selectedRun : List G.edgeSet,
    selectedRun <:+: faceRun.run ∧
    ∀ e : G.edgeSet,
      e ∈ selectedRun ↔
        e ∈ emb.faceBoundary f.1 ∧
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces

/-- On a fixed ordered face-boundary run, the selected-boundary edges form a single contiguous
block. This is the local contiguity half of the raw geometry target once face-boundary order data
is available. -/
def PlanarBoundaryFaceBoundaryRunGeometry.SelectedBoundaryArcOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : PlanarBoundaryFaceBoundaryRunGeometry emb)
    (f : AmbientFace emb.faces) : Prop :=
  ∃ selectedRun : List G.edgeSet,
    selectedRun <:+: (geom.faceBoundaryRun f).run ∧
      ∀ e : G.edgeSet,
        e ∈ selectedRun ↔
          e ∈ emb.faceBoundary f.1 ∧
            e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces

/-- A bundled face-boundary-geometry witness for the current annulus boundary route: every ambient
face comes with one ordered listing of its full boundary, and the selected-boundary edges on that
face form a single contiguous arc on that order. This is the direct embedding-side target behind
the paper's language of contiguous face-boundary runs. -/
structure PlanarBoundarySelectedBoundaryArcGeometry {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) where
  faceBoundaryRun : ∀ f : AmbientFace emb.faces, FaceBoundaryEndpointRun emb f
  selectedBoundaryArc :
    ∀ f : AmbientFace emb.faces,
      ∃ selectedRun : List G.edgeSet,
        selectedRun <:+: (faceBoundaryRun f).run ∧
        ∀ e : G.edgeSet,
          e ∈ selectedRun ↔
            e ∈ emb.faceBoundary f.1 ∧
              e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces

/-- Graph-level existence form of the pure face-boundary order target. -/
abbrev AdmitsPlanarBoundaryFaceBoundaryRunGeometry (G : SimpleGraph V) : Prop :=
  AdmitsFaceBoundaryRunGeometry G

/-- Graph-level existence form of the bundled face-boundary order plus selected-boundary
contiguity target. -/
def AdmitsPlanarBoundarySelectedBoundaryArcGeometry (G : SimpleGraph V) : Prop :=
  ∃ emb : PlaneEmbeddingWithBoundary G,
    Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb)

/-- Split graph-level existence form of the same local geometry burden: one ordered full
face-boundary run per ambient face, together with a separate proof that the selected-boundary
edges form one contiguous arc on each chosen run. -/
def AdmitsPlanarBoundaryFaceBoundaryRunGeometryAndSelectedBoundaryArcOnFace
    (G : SimpleGraph V) : Prop :=
  ∃ emb : PlaneEmbeddingWithBoundary G,
    ∃ geom : PlanarBoundaryFaceBoundaryRunGeometry emb,
      ∀ f : AmbientFace emb.faces, geom.SelectedBoundaryArcOnFace f

/-- Forget the contiguity witnesses and retain only the ordered full face-boundary runs. -/
def PlanarBoundarySelectedBoundaryArcGeometry.toFaceBoundaryRunGeometry
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : PlanarBoundarySelectedBoundaryArcGeometry emb) :
    PlanarBoundaryFaceBoundaryRunGeometry emb where
  faceBoundaryRun := geom.faceBoundaryRun

/-- Recombine ordered full face-boundary runs and per-face selected-boundary contiguity witnesses
into the bundled face-boundary arc geometry package. -/
def PlanarBoundaryFaceBoundaryRunGeometry.toSelectedBoundaryArcGeometry
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : PlanarBoundaryFaceBoundaryRunGeometry emb)
    (harc : ∀ f : AmbientFace emb.faces, geom.SelectedBoundaryArcOnFace f) :
    PlanarBoundarySelectedBoundaryArcGeometry emb where
  faceBoundaryRun := geom.faceBoundaryRun
  selectedBoundaryArc := harc

theorem PlanarBoundarySelectedBoundaryArcGeometry.boundarySelectedBoundaryArcOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : PlanarBoundarySelectedBoundaryArcGeometry emb) :
    ∀ f : AmbientFace emb.faces, BoundarySelectedBoundaryArcOnFace (emb := emb) f := by
  intro f
  rcases geom.selectedBoundaryArc f with ⟨selectedRun, hinfix, hselected⟩
  exact ⟨geom.faceBoundaryRun f, selectedRun, hinfix, hselected⟩

theorem PlanarBoundaryFaceBoundaryRunGeometry.boundarySelectedBoundaryArcOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : PlanarBoundaryFaceBoundaryRunGeometry emb)
    (harc : ∀ f : AmbientFace emb.faces, geom.SelectedBoundaryArcOnFace f) :
    ∀ f : AmbientFace emb.faces, BoundarySelectedBoundaryArcOnFace (emb := emb) f := by
  intro f
  rcases harc f with ⟨selectedRun, hinfix, hselected⟩
  exact ⟨geom.faceBoundaryRun f, selectedRun, hinfix, hselected⟩

theorem
    nonempty_planarBoundarySelectedBoundaryArcGeometry_iff_exists_planarBoundaryFaceBoundaryRunGeometryAndSelectedBoundaryArcOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} :
    Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb) ↔
      ∃ geom : PlanarBoundaryFaceBoundaryRunGeometry emb,
        ∀ f : AmbientFace emb.faces, geom.SelectedBoundaryArcOnFace f := by
  constructor
  · rintro ⟨geom⟩
    exact ⟨geom.toFaceBoundaryRunGeometry, geom.selectedBoundaryArc⟩
  · rintro ⟨geom, harc⟩
    exact ⟨geom.toSelectedBoundaryArcGeometry harc⟩

theorem admitsPlanarBoundaryFaceBoundaryRunGeometry_of_admitsPlanarBoundarySelectedBoundaryArcGeometry
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundarySelectedBoundaryArcGeometry G) :
    AdmitsPlanarBoundaryFaceBoundaryRunGeometry G := by
  rcases hG with ⟨emb, ⟨geom⟩⟩
  exact ⟨emb, ⟨geom.toFaceBoundaryRunGeometry⟩⟩

theorem
    admitsPlanarBoundaryFaceBoundaryRunGeometryAndSelectedBoundaryArcOnFace_of_admitsPlanarBoundarySelectedBoundaryArcGeometry
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundarySelectedBoundaryArcGeometry G) :
    AdmitsPlanarBoundaryFaceBoundaryRunGeometryAndSelectedBoundaryArcOnFace G := by
  rcases hG with ⟨emb, ⟨geom⟩⟩
  exact ⟨emb, geom.toFaceBoundaryRunGeometry, geom.selectedBoundaryArc⟩

theorem
    admitsPlanarBoundarySelectedBoundaryArcGeometry_of_admitsPlanarBoundaryFaceBoundaryRunGeometryAndSelectedBoundaryArcOnFace
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryFaceBoundaryRunGeometryAndSelectedBoundaryArcOnFace G) :
    AdmitsPlanarBoundarySelectedBoundaryArcGeometry G := by
  rcases hG with ⟨emb, geom, harc⟩
  exact ⟨emb, ⟨geom.toSelectedBoundaryArcGeometry harc⟩⟩

theorem
    admitsPlanarBoundarySelectedBoundaryArcGeometry_iff_admitsPlanarBoundaryFaceBoundaryRunGeometryAndSelectedBoundaryArcOnFace
    {G : SimpleGraph V} :
    AdmitsPlanarBoundarySelectedBoundaryArcGeometry G ↔
      AdmitsPlanarBoundaryFaceBoundaryRunGeometryAndSelectedBoundaryArcOnFace G := by
  constructor
  · exact
      admitsPlanarBoundaryFaceBoundaryRunGeometryAndSelectedBoundaryArcOnFace_of_admitsPlanarBoundarySelectedBoundaryArcGeometry
  · exact
      admitsPlanarBoundarySelectedBoundaryArcGeometry_of_admitsPlanarBoundaryFaceBoundaryRunGeometryAndSelectedBoundaryArcOnFace

end Mettapedia.GraphTheory.FourColor
