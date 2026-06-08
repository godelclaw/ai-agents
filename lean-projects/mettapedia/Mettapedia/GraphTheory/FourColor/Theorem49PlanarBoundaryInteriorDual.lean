import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryEmbedding
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryCertificate
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryCollarPeeling
import Mettapedia.GraphTheory.FourColor.Theorem49InteriorDualForest

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- The weakest current Step 2 package over a genuine plane embedding with boundary. This is the
annulus-shaped interior-dual data expected from the remaining geometric argument for a between-
region `H`, where some boundary edges have incidence count `1`. -/
abbrev PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) :=
  InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary

/-- The strongest current boundary-rooted parent package over a genuine plane embedding with
boundary. This keeps the explicit separated covering root set together with the canonical
`parentTowardsRoot` relation on the chosen interior-dual spanning forest. -/
abbrev PlanarBoundaryInteriorDualBoundaryRootParentPeelData {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) :=
  InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary

/-- The weakest current graph-level annulus target: there exists a plane embedding with boundary
of `G` together with the boundary-root adjacency-distance interior-dual data expected from the
remaining geometric argument. -/
def AdmitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    (G : SimpleGraph V) : Prop :=
  ∃ emb : PlaneEmbeddingWithBoundary G,
    Nonempty (PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb)

/-- Strongest graph-level annulus target currently exposed on the boundary-rooted branch: there
exists a plane embedding with boundary together with the canonical parent package over a separated
covering root set in the interior-dual spanning forest. -/
def AdmitsPlanarBoundaryInteriorDualBoundaryRootParentPeelData
    (G : SimpleGraph V) : Prop :=
  ∃ emb : PlaneEmbeddingWithBoundary G,
    Nonempty (PlanarBoundaryInteriorDualBoundaryRootParentPeelData emb)

theorem admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData_iff
    {G : SimpleGraph V} :
    AdmitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData G ↔
      ∃ emb : PlaneEmbeddingWithBoundary G,
        Nonempty (InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) :=
  Iff.rfl

theorem admitsPlanarBoundaryInteriorDualBoundaryRootParentPeelData_iff
    {G : SimpleGraph V} :
    AdmitsPlanarBoundaryInteriorDualBoundaryRootParentPeelData G ↔
      ∃ emb : PlaneEmbeddingWithBoundary G,
        Nonempty (InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary) :=
  Iff.rfl

/-- The explicit-root-distance parent package over a genuine plane embedding with boundary. This
matches annulus arguments that produce a parent relation in the interior-dual spanning forest and
show the chosen root-distance strictly decreases along parent edges. -/
abbrev PlanarBoundaryInteriorDualRootDistanceParentPeelData {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) :=
  InteriorDualRootDistanceParentPeelData emb.faces emb.faceBoundary

/-- The root-free height-and-parent package over a genuine plane embedding with boundary. This is
the closest current formal target to an outside-in collar peeling: each peeled face has a parent
adjacent in the interior-dual spanning forest and a strictly smaller layer/height. -/
abbrev PlanarBoundaryInteriorDualHeightParentPeelData {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) :=
  InteriorDualHeightParentPeelData emb.faces emb.faceBoundary

/-- The root-free well-founded-parent package over a genuine plane embedding with boundary. This is
the weakest current annulus-side interior-dual target: peeled faces only need a well-founded
parent relation in the chosen spanning forest together with the child face-membership cover
condition. -/
abbrev PlanarBoundaryInteriorDualWellFoundedParentPeelData {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) :=
  InteriorDualWellFoundedParentPeelData emb.faces emb.faceBoundary

/-- Weaker annulus target phrased with explicit root-distance parents instead of boundary-root
adjacency-distance witnesses. -/
def AdmitsPlanarBoundaryInteriorDualRootDistanceParentPeelData
    (G : SimpleGraph V) : Prop :=
  ∃ emb : PlaneEmbeddingWithBoundary G,
    Nonempty (PlanarBoundaryInteriorDualRootDistanceParentPeelData emb)

/-- Weakest root-free annulus target currently available on the boundary-aware side: a parent
relation and a strictly increasing height along parent edges. -/
def AdmitsPlanarBoundaryInteriorDualHeightParentPeelData
    (G : SimpleGraph V) : Prop :=
  ∃ emb : PlaneEmbeddingWithBoundary G,
    Nonempty (PlanarBoundaryInteriorDualHeightParentPeelData emb)

/-- Weakest root-free annulus target currently available on the boundary-aware side: a
well-founded parent relation together with the parent-shared-edge face-membership cover
condition. -/
def AdmitsPlanarBoundaryInteriorDualWellFoundedParentPeelData
    (G : SimpleGraph V) : Prop :=
  ∃ emb : PlaneEmbeddingWithBoundary G,
    Nonempty (PlanarBoundaryInteriorDualWellFoundedParentPeelData emb)

theorem admitsPlanarBoundaryInteriorDualRootDistanceParentPeelData_of_admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData G) :
    AdmitsPlanarBoundaryInteriorDualRootDistanceParentPeelData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.toInteriorDualBoundaryRootParentPeelData.toInteriorDualRootDistanceParentPeelData⟩⟩

theorem admitsPlanarBoundaryInteriorDualBoundaryRootParentPeelData_of_admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData G) :
    AdmitsPlanarBoundaryInteriorDualBoundaryRootParentPeelData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.toInteriorDualBoundaryRootParentPeelData⟩⟩

theorem admitsPlanarBoundaryInteriorDualRootDistanceParentPeelData_of_admitsPlanarBoundaryInteriorDualBoundaryRootParentPeelData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryInteriorDualBoundaryRootParentPeelData G) :
    AdmitsPlanarBoundaryInteriorDualRootDistanceParentPeelData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.toInteriorDualRootDistanceParentPeelData⟩⟩

theorem admitsPlanarBoundaryInteriorDualHeightParentPeelData_of_admitsPlanarBoundaryInteriorDualRootDistanceParentPeelData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryInteriorDualRootDistanceParentPeelData G) :
    AdmitsPlanarBoundaryInteriorDualHeightParentPeelData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.toInteriorDualHeightParentPeelData⟩⟩

theorem admitsPlanarBoundaryInteriorDualHeightParentPeelData_of_admitsPlanarBoundaryInteriorDualBoundaryRootParentPeelData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryInteriorDualBoundaryRootParentPeelData G) :
    AdmitsPlanarBoundaryInteriorDualHeightParentPeelData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.toInteriorDualHeightParentPeelData⟩⟩

theorem admitsPlanarBoundaryInteriorDualHeightParentPeelData_of_admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData G) :
    AdmitsPlanarBoundaryInteriorDualHeightParentPeelData G :=
  admitsPlanarBoundaryInteriorDualHeightParentPeelData_of_admitsPlanarBoundaryInteriorDualRootDistanceParentPeelData
    (admitsPlanarBoundaryInteriorDualRootDistanceParentPeelData_of_admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      hG)

theorem admitsPlanarBoundaryInteriorDualWellFoundedParentPeelData_of_admitsPlanarBoundaryInteriorDualHeightParentPeelData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryInteriorDualHeightParentPeelData G) :
    AdmitsPlanarBoundaryInteriorDualWellFoundedParentPeelData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.toInteriorDualWellFoundedParentPeelData⟩⟩

theorem admitsPlanarBoundaryInteriorDualWellFoundedParentPeelData_of_admitsPlanarBoundaryInteriorDualBoundaryRootParentPeelData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryInteriorDualBoundaryRootParentPeelData G) :
    AdmitsPlanarBoundaryInteriorDualWellFoundedParentPeelData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.toInteriorDualWellFoundedParentPeelData⟩⟩

theorem admitsPlanarBoundaryInteriorDualWellFoundedParentPeelData_of_admitsPlanarBoundaryInteriorDualRootDistanceParentPeelData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryInteriorDualRootDistanceParentPeelData G) :
    AdmitsPlanarBoundaryInteriorDualWellFoundedParentPeelData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.toInteriorDualWellFoundedParentPeelData⟩⟩

theorem admitsPlanarBoundaryInteriorDualWellFoundedParentPeelData_of_admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData G) :
    AdmitsPlanarBoundaryInteriorDualWellFoundedParentPeelData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.toInteriorDualWellFoundedParentPeelData⟩⟩

theorem admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_of_admitsPlanarBoundaryInteriorDualHeightParentPeelData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryInteriorDualHeightParentPeelData G) :
    AdmitsPlanarBoundaryHeightOrderedFacePeelWitnessData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨planarBoundaryHeightOrderedFacePeelWitnessData_of_interiorDualHeightParentPeelData
    data⟩⟩

theorem admitsPlanarBoundaryWellFoundedFacePeelWitnessData_of_admitsPlanarBoundaryInteriorDualHeightParentPeelData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryInteriorDualHeightParentPeelData G) :
    AdmitsPlanarBoundaryWellFoundedFacePeelWitnessData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨planarBoundaryWellFoundedFacePeelWitnessData_of_interiorDualHeightParentPeelData
    data⟩⟩

theorem admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_admitsPlanarBoundaryInteriorDualHeightParentPeelData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryInteriorDualHeightParentPeelData G) :
    AdmitsPlanarBoundaryCollarLayerFacePeelWitnessData G := by
  exact admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_exists_planarBoundaryHeightOrderedFacePeelWitnessData
    (admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_of_admitsPlanarBoundaryInteriorDualHeightParentPeelData
      hG)

theorem admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData G) :
    AdmitsPlanarBoundaryCollarLayerFacePeelWitnessData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨
    planarBoundaryCollarLayerFacePeelWitnessData_of_interiorDualBoundaryRootAdjDistancePeelData
      data⟩⟩

theorem admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_admitsPlanarBoundaryInteriorDualBoundaryRootParentPeelData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryInteriorDualBoundaryRootParentPeelData G) :
    AdmitsPlanarBoundaryCollarLayerFacePeelWitnessData G := by
  exact
    admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_admitsPlanarBoundaryInteriorDualHeightParentPeelData
      (admitsPlanarBoundaryInteriorDualHeightParentPeelData_of_admitsPlanarBoundaryInteriorDualBoundaryRootParentPeelData
        hG)

theorem admitsPlanarBoundaryWellFoundedFacePeelWitnessData_of_admitsPlanarBoundaryInteriorDualWellFoundedParentPeelData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryInteriorDualWellFoundedParentPeelData G) :
    AdmitsPlanarBoundaryWellFoundedFacePeelWitnessData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨
    planarBoundaryWellFoundedFacePeelWitnessData_of_interiorDualWellFoundedParentPeelData
      data⟩⟩

theorem
    admitsPlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData_of_admitsPlanarBoundaryInteriorDualWellFoundedParentPeelData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryInteriorDualWellFoundedParentPeelData G) :
    AdmitsPlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨
    planarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData_of_interiorDualWellFoundedParentPeelData
      data⟩⟩

theorem admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_admitsPlanarBoundaryInteriorDualWellFoundedParentPeelData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryInteriorDualWellFoundedParentPeelData G) :
    AdmitsPlanarBoundaryCollarLayerFacePeelWitnessData G := by
  exact
    admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_admitsPlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
      (admitsPlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData_of_admitsPlanarBoundaryInteriorDualWellFoundedParentPeelData
        hG)

/-- The weakest current annulus-facing Step 2 package canonically yields the attached-face peel
certificate consumed by the boundary-aware Theorem 4.9 bridge. -/
noncomputable def
    attachedBoundaryRootedFacePeelCertificate_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb) :
    BoundaryRootedFacePeelCertificate emb.faces.attach
      (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary) :=
  data.toBoundaryRootedFacePeelCertificate

/-- The strongest current boundary-root parent package also canonically yields the attached-face
peel certificate consumed by the boundary-aware Theorem 4.9 bridge. -/
noncomputable def
    attachedBoundaryRootedFacePeelCertificate_of_planarBoundaryInteriorDualBoundaryRootParentPeelData
    {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryInteriorDualBoundaryRootParentPeelData emb) :
    BoundaryRootedFacePeelCertificate emb.faces.attach
      (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary) :=
  data.toBoundaryRootedFacePeelCertificate

/-- The explicit root-distance parent package also yields the attached-face peel certificate
consumed by the boundary-aware Theorem 4.9 bridge. -/
noncomputable def
    attachedBoundaryRootedFacePeelCertificate_of_planarBoundaryInteriorDualRootDistanceParentPeelData
    {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryInteriorDualRootDistanceParentPeelData emb) :
    BoundaryRootedFacePeelCertificate emb.faces.attach
      (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary) :=
  data.toBoundaryRootedFacePeelCertificate

/-- The height-parent package yields the attached-face peel certificate consumed by the
boundary-aware Theorem 4.9 bridge. -/
noncomputable def
    attachedBoundaryRootedFacePeelCertificate_of_planarBoundaryInteriorDualHeightParentPeelData
    {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryInteriorDualHeightParentPeelData emb) :
    BoundaryRootedFacePeelCertificate emb.faces.attach
      (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary) :=
  data.toBoundaryRootedFacePeelCertificate

/-- The well-founded-parent package yields the attached-face peel certificate consumed by the
boundary-aware Theorem 4.9 bridge. -/
noncomputable def
    attachedBoundaryRootedFacePeelCertificate_of_planarBoundaryInteriorDualWellFoundedParentPeelData
    {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryInteriorDualWellFoundedParentPeelData emb) :
    BoundaryRootedFacePeelCertificate emb.faces.attach
      (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary) :=
  data.toBoundaryRootedFacePeelCertificate

/-- Graph-level attached-certificate package obtained directly from the boundary-rooted
interior-dual adjacency-distance data. -/
noncomputable def
    planarBoundaryAttachedRootedFacePeelCertificate_of_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb) :
    PlanarBoundaryAttachedRootedFacePeelCertificate G where
  embedding := emb
  certificate :=
    attachedBoundaryRootedFacePeelCertificate_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      emb data

/-- Existence of the boundary-rooted interior-dual adjacency-distance data is already enough to
produce the graph-level attached peel certificate consumed by the boundary-aware Theorem 4.9
bridge. -/
theorem
    admitsPlanarBoundaryAttachedRootedFacePeelCertificate_of_admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData G) :
    AdmitsPlanarBoundaryAttachedRootedFacePeelCertificate G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨
    planarBoundaryAttachedRootedFacePeelCertificate_of_interiorDualBoundaryRootAdjDistancePeelData
      emb data⟩

/-- The explicit canonical-parent interior-dual package also gives the graph-level attached peel
certificate directly. -/
noncomputable def
    planarBoundaryAttachedRootedFacePeelCertificate_of_interiorDualBoundaryRootParentPeelData
    {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryInteriorDualBoundaryRootParentPeelData emb) :
    PlanarBoundaryAttachedRootedFacePeelCertificate G where
  embedding := emb
  certificate :=
    attachedBoundaryRootedFacePeelCertificate_of_planarBoundaryInteriorDualBoundaryRootParentPeelData
      emb data

/-- Existence of the canonical-parent interior-dual package gives the graph-level attached peel
certificate. -/
theorem
    admitsPlanarBoundaryAttachedRootedFacePeelCertificate_of_admitsPlanarBoundaryInteriorDualBoundaryRootParentPeelData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryInteriorDualBoundaryRootParentPeelData G) :
    AdmitsPlanarBoundaryAttachedRootedFacePeelCertificate G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨
    planarBoundaryAttachedRootedFacePeelCertificate_of_interiorDualBoundaryRootParentPeelData
      emb data⟩

/-- Explicit root-distance parent data gives the graph-level attached peel certificate directly.
-/
noncomputable def
    planarBoundaryAttachedRootedFacePeelCertificate_of_interiorDualRootDistanceParentPeelData
    {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryInteriorDualRootDistanceParentPeelData emb) :
    PlanarBoundaryAttachedRootedFacePeelCertificate G where
  embedding := emb
  certificate :=
    attachedBoundaryRootedFacePeelCertificate_of_planarBoundaryInteriorDualRootDistanceParentPeelData
      emb data

/-- Existence of explicit root-distance parent data gives the graph-level attached peel
certificate. -/
theorem
    admitsPlanarBoundaryAttachedRootedFacePeelCertificate_of_admitsPlanarBoundaryInteriorDualRootDistanceParentPeelData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryInteriorDualRootDistanceParentPeelData G) :
    AdmitsPlanarBoundaryAttachedRootedFacePeelCertificate G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨
    planarBoundaryAttachedRootedFacePeelCertificate_of_interiorDualRootDistanceParentPeelData
      emb data⟩

/-- Height-parent data gives the graph-level attached peel certificate directly. -/
noncomputable def
    planarBoundaryAttachedRootedFacePeelCertificate_of_interiorDualHeightParentPeelData
    {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryInteriorDualHeightParentPeelData emb) :
    PlanarBoundaryAttachedRootedFacePeelCertificate G where
  embedding := emb
  certificate :=
    attachedBoundaryRootedFacePeelCertificate_of_planarBoundaryInteriorDualHeightParentPeelData
      emb data

/-- Existence of height-parent data gives the graph-level attached peel certificate. -/
theorem
    admitsPlanarBoundaryAttachedRootedFacePeelCertificate_of_admitsPlanarBoundaryInteriorDualHeightParentPeelData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryInteriorDualHeightParentPeelData G) :
    AdmitsPlanarBoundaryAttachedRootedFacePeelCertificate G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨
    planarBoundaryAttachedRootedFacePeelCertificate_of_interiorDualHeightParentPeelData
      emb data⟩

/-- Well-founded-parent data gives the graph-level attached peel certificate directly. -/
noncomputable def
    planarBoundaryAttachedRootedFacePeelCertificate_of_interiorDualWellFoundedParentPeelData
    {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryInteriorDualWellFoundedParentPeelData emb) :
    PlanarBoundaryAttachedRootedFacePeelCertificate G where
  embedding := emb
  certificate :=
    attachedBoundaryRootedFacePeelCertificate_of_planarBoundaryInteriorDualWellFoundedParentPeelData
      emb data

/-- Existence of well-founded-parent data gives the graph-level attached peel certificate. -/
theorem
    admitsPlanarBoundaryAttachedRootedFacePeelCertificate_of_admitsPlanarBoundaryInteriorDualWellFoundedParentPeelData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryInteriorDualWellFoundedParentPeelData G) :
    AdmitsPlanarBoundaryAttachedRootedFacePeelCertificate G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨
    planarBoundaryAttachedRootedFacePeelCertificate_of_interiorDualWellFoundedParentPeelData
      emb data⟩

/-- Boundary-rooted interior-dual adjacency-distance data reaches the graph-level annihilator
endpoint through the attached peel certificate and the Definition 4.8 generator-family
orthogonality hypothesis. -/
theorem zero_on_allEdges_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData_of_annihilatesKempeClosureGeneratorFamily
    {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G)
    (C₀ C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C)
    (hC : C ∈ G.EdgeKempeClosure C₀) (z : G.edgeSet → Color)
    (data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0)
    (hgen : AnnihilatesKempeClosureGeneratorFamily emb.faceBoundary C₀ z) :
    ∀ e, z e = 0 := by
  exact
    zero_on_allEdges_of_boundary_zero_and_planarBoundaryAttachedRootedFacePeelCertificate_of_annihilatesKempeClosureGeneratorFamily
      (data :=
        planarBoundaryAttachedRootedFacePeelCertificate_of_interiorDualBoundaryRootAdjDistancePeelData
          emb data)
      (C₀ := C₀) (C := C) (htait := htait) (hC := hC) (z := z)
      (hzeroBoundary := hzeroBoundary) (hgen := hgen)

/-- The canonical-parent interior-dual package reaches the same graph-level annihilator endpoint
through its attached peel certificate. -/
theorem zero_on_allEdges_of_planarBoundaryInteriorDualBoundaryRootParentPeelData_of_annihilatesKempeClosureGeneratorFamily
    {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G)
    (C₀ C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C)
    (hC : C ∈ G.EdgeKempeClosure C₀) (z : G.edgeSet → Color)
    (data : PlanarBoundaryInteriorDualBoundaryRootParentPeelData emb)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0)
    (hgen : AnnihilatesKempeClosureGeneratorFamily emb.faceBoundary C₀ z) :
    ∀ e, z e = 0 := by
  exact
    zero_on_allEdges_of_boundary_zero_and_planarBoundaryAttachedRootedFacePeelCertificate_of_annihilatesKempeClosureGeneratorFamily
      (data :=
        planarBoundaryAttachedRootedFacePeelCertificate_of_interiorDualBoundaryRootParentPeelData
          emb data)
      (C₀ := C₀) (C := C) (htait := htait) (hC := hC) (z := z)
      (hzeroBoundary := hzeroBoundary) (hgen := hgen)

/-- Explicit root-distance parent data reaches the graph-level annihilator endpoint through its
attached peel certificate. -/
theorem zero_on_allEdges_of_planarBoundaryInteriorDualRootDistanceParentPeelData_of_annihilatesKempeClosureGeneratorFamily
    {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G)
    (C₀ C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C)
    (hC : C ∈ G.EdgeKempeClosure C₀) (z : G.edgeSet → Color)
    (data : PlanarBoundaryInteriorDualRootDistanceParentPeelData emb)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0)
    (hgen : AnnihilatesKempeClosureGeneratorFamily emb.faceBoundary C₀ z) :
    ∀ e, z e = 0 := by
  exact
    zero_on_allEdges_of_boundary_zero_and_planarBoundaryAttachedRootedFacePeelCertificate_of_annihilatesKempeClosureGeneratorFamily
      (data :=
        planarBoundaryAttachedRootedFacePeelCertificate_of_interiorDualRootDistanceParentPeelData
          emb data)
      (C₀ := C₀) (C := C) (htait := htait) (hC := hC) (z := z)
      (hzeroBoundary := hzeroBoundary) (hgen := hgen)

/-- Height-parent data reaches the graph-level annihilator endpoint through its attached peel
certificate. -/
theorem zero_on_allEdges_of_planarBoundaryInteriorDualHeightParentPeelData_of_annihilatesKempeClosureGeneratorFamily
    {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G)
    (C₀ C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C)
    (hC : C ∈ G.EdgeKempeClosure C₀) (z : G.edgeSet → Color)
    (data : PlanarBoundaryInteriorDualHeightParentPeelData emb)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0)
    (hgen : AnnihilatesKempeClosureGeneratorFamily emb.faceBoundary C₀ z) :
    ∀ e, z e = 0 := by
  exact
    zero_on_allEdges_of_boundary_zero_and_planarBoundaryAttachedRootedFacePeelCertificate_of_annihilatesKempeClosureGeneratorFamily
      (data :=
        planarBoundaryAttachedRootedFacePeelCertificate_of_interiorDualHeightParentPeelData
          emb data)
      (C₀ := C₀) (C := C) (htait := htait) (hC := hC) (z := z)
      (hzeroBoundary := hzeroBoundary) (hgen := hgen)

/-- Well-founded-parent data reaches the graph-level annihilator endpoint through its attached
peel certificate. -/
theorem zero_on_allEdges_of_planarBoundaryInteriorDualWellFoundedParentPeelData_of_annihilatesKempeClosureGeneratorFamily
    {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G)
    (C₀ C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C)
    (hC : C ∈ G.EdgeKempeClosure C₀) (z : G.edgeSet → Color)
    (data : PlanarBoundaryInteriorDualWellFoundedParentPeelData emb)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0)
    (hgen : AnnihilatesKempeClosureGeneratorFamily emb.faceBoundary C₀ z) :
    ∀ e, z e = 0 := by
  exact
    zero_on_allEdges_of_boundary_zero_and_planarBoundaryAttachedRootedFacePeelCertificate_of_annihilatesKempeClosureGeneratorFamily
      (data :=
        planarBoundaryAttachedRootedFacePeelCertificate_of_interiorDualWellFoundedParentPeelData
          emb data)
      (C₀ := C₀) (C := C) (htait := htait) (hC := hC) (z := z)
      (hzeroBoundary := hzeroBoundary) (hgen := hgen)

/-- Existential graph-level annihilator form of the boundary-rooted interior-dual adjacency-distance
certificate route. -/
theorem zero_on_allEdges_of_exists_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData_of_annihilatesKempeClosureGeneratorFamily
    {G : SimpleGraph V}
    (C₀ C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C)
    (hC : C ∈ G.EdgeKempeClosure C₀) (z : G.edgeSet → Color)
    (hdata : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        (∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0) ∧
        AnnihilatesKempeClosureGeneratorFamily emb.faceBoundary C₀ z) :
    ∀ e, z e = 0 := by
  rcases hdata with ⟨emb, data, hzeroBoundary, hgen⟩
  exact
    zero_on_allEdges_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData_of_annihilatesKempeClosureGeneratorFamily
      (emb := emb) (C₀ := C₀) (C := C) (htait := htait) (hC := hC)
      (z := z) (data := data) (hzeroBoundary := hzeroBoundary) (hgen := hgen)

/-- Existential graph-level annihilator form of the canonical-parent interior-dual certificate
route. -/
theorem zero_on_allEdges_of_exists_planarBoundaryInteriorDualBoundaryRootParentPeelData_of_annihilatesKempeClosureGeneratorFamily
    {G : SimpleGraph V}
    (C₀ C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C)
    (hC : C ∈ G.EdgeKempeClosure C₀) (z : G.edgeSet → Color)
    (hdata : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryInteriorDualBoundaryRootParentPeelData emb,
        (∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0) ∧
        AnnihilatesKempeClosureGeneratorFamily emb.faceBoundary C₀ z) :
    ∀ e, z e = 0 := by
  rcases hdata with ⟨emb, data, hzeroBoundary, hgen⟩
  exact
    zero_on_allEdges_of_planarBoundaryInteriorDualBoundaryRootParentPeelData_of_annihilatesKempeClosureGeneratorFamily
      (emb := emb) (C₀ := C₀) (C := C) (htait := htait) (hC := hC)
      (z := z) (data := data) (hzeroBoundary := hzeroBoundary) (hgen := hgen)

/-- Existential graph-level annihilator form of the explicit root-distance parent certificate
route. -/
theorem zero_on_allEdges_of_exists_planarBoundaryInteriorDualRootDistanceParentPeelData_of_annihilatesKempeClosureGeneratorFamily
    {G : SimpleGraph V}
    (C₀ C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C)
    (hC : C ∈ G.EdgeKempeClosure C₀) (z : G.edgeSet → Color)
    (hdata : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryInteriorDualRootDistanceParentPeelData emb,
        (∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0) ∧
        AnnihilatesKempeClosureGeneratorFamily emb.faceBoundary C₀ z) :
    ∀ e, z e = 0 := by
  rcases hdata with ⟨emb, data, hzeroBoundary, hgen⟩
  exact
    zero_on_allEdges_of_planarBoundaryInteriorDualRootDistanceParentPeelData_of_annihilatesKempeClosureGeneratorFamily
      (emb := emb) (C₀ := C₀) (C := C) (htait := htait) (hC := hC)
      (z := z) (data := data) (hzeroBoundary := hzeroBoundary) (hgen := hgen)

/-- Existential graph-level annihilator form of the height-parent certificate route. -/
theorem zero_on_allEdges_of_exists_planarBoundaryInteriorDualHeightParentPeelData_of_annihilatesKempeClosureGeneratorFamily
    {G : SimpleGraph V}
    (C₀ C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C)
    (hC : C ∈ G.EdgeKempeClosure C₀) (z : G.edgeSet → Color)
    (hdata : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryInteriorDualHeightParentPeelData emb,
        (∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0) ∧
        AnnihilatesKempeClosureGeneratorFamily emb.faceBoundary C₀ z) :
    ∀ e, z e = 0 := by
  rcases hdata with ⟨emb, data, hzeroBoundary, hgen⟩
  exact
    zero_on_allEdges_of_planarBoundaryInteriorDualHeightParentPeelData_of_annihilatesKempeClosureGeneratorFamily
      (emb := emb) (C₀ := C₀) (C := C) (htait := htait) (hC := hC)
      (z := z) (data := data) (hzeroBoundary := hzeroBoundary) (hgen := hgen)

/-- Existential graph-level annihilator form of the well-founded-parent certificate route. -/
theorem zero_on_allEdges_of_exists_planarBoundaryInteriorDualWellFoundedParentPeelData_of_annihilatesKempeClosureGeneratorFamily
    {G : SimpleGraph V}
    (C₀ C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C)
    (hC : C ∈ G.EdgeKempeClosure C₀) (z : G.edgeSet → Color)
    (hdata : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryInteriorDualWellFoundedParentPeelData emb,
        (∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0) ∧
        AnnihilatesKempeClosureGeneratorFamily emb.faceBoundary C₀ z) :
    ∀ e, z e = 0 := by
  rcases hdata with ⟨emb, data, hzeroBoundary, hgen⟩
  exact
    zero_on_allEdges_of_planarBoundaryInteriorDualWellFoundedParentPeelData_of_annihilatesKempeClosureGeneratorFamily
      (emb := emb) (C₀ := C₀) (C := C) (htait := htait) (hC := hC)
      (z := z) (data := data) (hzeroBoundary := hzeroBoundary) (hgen := hgen)

/-- Annulus-shaped global annihilator form of the weakest current Step 2 package. For a genuine
plane embedding with boundary, the current interior-dual adjacency-plus-distance data plus the
boundary vanishing hypothesis already suffices for the present Theorem 4.9 route. -/
theorem zero_on_allEdges_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G)
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0)
    (horth : ∀ f ∈ data.peelFaces,
      ∀ γ, γ ≠ 0 → γ ≠ C
        (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces data.roots
            data.hcoverRoots data.hsepRoots)
          data.fallbackEdge f) →
        chainDot
            (boundaryBicoloredEdges C
              (C (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces data.roots
                  data.hcoverRoots data.hsepRoots)
                data.fallbackEdge f))
              (C (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces data.roots
                  data.hcoverRoots data.hsepRoots)
                data.fallbackEdge f) + γ)
              (emb.faceBoundary f.1))
            z
            (polarizedFaceGenerator C
              (C (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces data.roots
                  data.hcoverRoots data.hsepRoots)
                data.fallbackEdge f))
              (C (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces data.roots
                  data.hcoverRoots data.hsepRoots)
                data.fallbackEdge f) + γ)
              (emb.faceBoundary f.1)) = 0) :
    ∀ e, z e = 0 := by
  let heightData :=
    planarBoundaryHeightOrderedFacePeelWitnessData_of_interiorDualBoundaryRootAdjDistancePeelData
      data
  let collarData :=
    planarBoundaryCollarLayerFacePeelWitnessData_of_heightOrderedFacePeelWitnessData heightData
  have horth' :
      ∀ i f, f ∈ collarData.layerFaces i →
        ∀ γ, γ ≠ 0 → γ ≠ C (collarData.witnessEdge f) →
          chainDot
              (boundaryBicoloredEdges C
                (C (collarData.witnessEdge f))
                (C (collarData.witnessEdge f) + γ)
                (emb.faceBoundary f.1))
              z
              (polarizedFaceGenerator C
                (C (collarData.witnessEdge f))
                (C (collarData.witnessEdge f) + γ)
                (emb.faceBoundary f.1)) = 0 := by
    intro i f hfi γ hγ0 hγd
    have hf : f ∈ heightData.peelFaces := (Finset.mem_filter.1 hfi).1
    exact horth f hf γ hγ0 (by simpa [heightData, collarData] using hγd)
  exact zero_on_allEdges_of_planarBoundaryCollarLayerFacePeelWitnessData
    (emb := emb) (C := C) (htait := htait) (z := z)
    (data := collarData)
    (hzeroBoundary := hzeroBoundary) (horth := horth')

/-- Annulus-shaped global annihilator form of the strongest current boundary-root parent package.
This is the direct boundary-aware wrapper around the generic canonical-parent interior-dual
theorem. -/
theorem zero_on_allEdges_of_planarBoundaryInteriorDualBoundaryRootParentPeelData
    {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G)
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (data : PlanarBoundaryInteriorDualBoundaryRootParentPeelData emb)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0)
    (horth : ∀ f ∈ data.peelFaces,
      ∀ γ, γ ≠ 0 → γ ≠ C
        (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces data.roots
            data.hcoverRoots data.hsepRoots)
          data.fallbackEdge f) →
        chainDot
            (boundaryBicoloredEdges C
              (C (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces data.roots
                  data.hcoverRoots data.hsepRoots)
                data.fallbackEdge f))
              (C (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces data.roots
                  data.hcoverRoots data.hsepRoots)
                data.fallbackEdge f) + γ)
              (emb.faceBoundary f.1))
            z
            (polarizedFaceGenerator C
              (C (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces data.roots
                  data.hcoverRoots data.hsepRoots)
                data.fallbackEdge f))
              (C (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces data.roots
                  data.hcoverRoots data.hsepRoots)
                data.fallbackEdge f) + γ)
              (emb.faceBoundary f.1)) = 0) :
    ∀ e, z e = 0 := by
  have hzeroSupport :
      ∀ e ∈ emb.faces.biUnion emb.faceBoundary, z e = 0 :=
    zero_on_ambientFaceSupport_of_interiorDualBoundaryRootParentPeelData
      (C := C) (htait := htait) (z := z)
      (allFaces := emb.faces) (faceBoundary := emb.faceBoundary)
      (data := data) (hzeroBoundary := hzeroBoundary) (horth := horth)
  intro e
  exact hzeroSupport e (by simpa [PlaneEmbeddingWithBoundary.faceSupport] using emb.mem_faceSupport e)

/-- Annulus-shaped global annihilator form of the explicit root-distance parent package. This is a
weaker target than boundary-root adjacency-distance data and may be closer to direct geometric
construction from the interior-dual spanning forest. -/
theorem zero_on_allEdges_of_planarBoundaryInteriorDualRootDistanceParentPeelData
    {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G)
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (data : PlanarBoundaryInteriorDualRootDistanceParentPeelData emb)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0)
    (horth : ∀ f ∈ data.peelFaces,
      ∀ γ, γ ≠ 0 → γ ≠ C
        (parentSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
          data.parentFace data.fallbackEdge data.hparentAdj f) →
        chainDot
            (boundaryBicoloredEdges C
              (C (parentSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
                data.parentFace data.fallbackEdge data.hparentAdj f))
              (C (parentSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
                data.parentFace data.fallbackEdge data.hparentAdj f) + γ)
              (emb.faceBoundary f.1))
            z
            (polarizedFaceGenerator C
              (C (parentSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
                data.parentFace data.fallbackEdge data.hparentAdj f))
              (C (parentSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
                data.parentFace data.fallbackEdge data.hparentAdj f) + γ)
              (emb.faceBoundary f.1)) = 0) :
    ∀ e, z e = 0 := by
  have hzeroSupport :
      ∀ e ∈ emb.faces.biUnion emb.faceBoundary, z e = 0 :=
    zero_on_ambientFaceSupport_of_interiorDualRootDistanceParentPeelData
      (C := C) (htait := htait) (z := z)
      (allFaces := emb.faces) (faceBoundary := emb.faceBoundary)
      (data := data) (hzeroBoundary := hzeroBoundary) (horth := horth)
  intro e
  exact hzeroSupport e (by simpa [PlaneEmbeddingWithBoundary.faceSupport] using emb.mem_faceSupport e)

/-- Annulus-shaped global annihilator form of the weakest current root-free interior-dual package.
This is the first boundary-aware theorem endpoint that asks only for a well-founded parent
relation plus the child face-membership cover condition. -/
theorem zero_on_allEdges_of_planarBoundaryInteriorDualWellFoundedParentPeelData
    {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G)
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (data : PlanarBoundaryInteriorDualWellFoundedParentPeelData emb)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0)
    (horth : ∀ f ∈ data.peelFaces,
      ∀ γ, γ ≠ 0 → γ ≠ C
        (parentSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
          data.parentFace data.fallbackEdge data.hparentAdj f) →
        chainDot
            (boundaryBicoloredEdges C
              (C (parentSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
                data.parentFace data.fallbackEdge data.hparentAdj f))
              (C (parentSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
                data.parentFace data.fallbackEdge data.hparentAdj f) + γ)
              (emb.faceBoundary f.1))
            z
            (polarizedFaceGenerator C
              (C (parentSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
                data.parentFace data.fallbackEdge data.hparentAdj f))
              (C (parentSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
                  data.parentFace data.fallbackEdge data.hparentAdj f) + γ)
              (emb.faceBoundary f.1)) = 0) :
    ∀ e, z e = 0 := by
  have hzeroSupport :
      ∀ e ∈ emb.faces.biUnion emb.faceBoundary, z e = 0 :=
    zero_on_ambientFaceSupport_of_interiorDualWellFoundedParentPeelData
      (C := C) (htait := htait) (z := z)
      (allFaces := emb.faces) (faceBoundary := emb.faceBoundary)
      (data := data) (hzeroBoundary := hzeroBoundary) (horth := horth)
  intro e
  exact hzeroSupport e (by simpa [PlaneEmbeddingWithBoundary.faceSupport] using emb.mem_faceSupport e)

/-- Annulus-shaped global annihilator form of the weakest root-free height/parent package. This is
the theorem-level endpoint closest to the paper's outside-in collar peeling picture. -/
theorem zero_on_allEdges_of_planarBoundaryInteriorDualHeightParentPeelData
    {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G)
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (data : PlanarBoundaryInteriorDualHeightParentPeelData emb)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0)
    (horth : ∀ f ∈ data.peelFaces,
      ∀ γ, γ ≠ 0 → γ ≠ C
        (parentSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
          data.parentFace data.fallbackEdge data.hparentAdj f) →
        chainDot
            (boundaryBicoloredEdges C
              (C (parentSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
                data.parentFace data.fallbackEdge data.hparentAdj f))
              (C (parentSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
                data.parentFace data.fallbackEdge data.hparentAdj f) + γ)
              (emb.faceBoundary f.1))
            z
            (polarizedFaceGenerator C
              (C (parentSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
                data.parentFace data.fallbackEdge data.hparentAdj f))
              (C (parentSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
                  data.parentFace data.fallbackEdge data.hparentAdj f) + γ)
              (emb.faceBoundary f.1)) = 0) :
    ∀ e, z e = 0 := by
  have hzeroSupport :
      ∀ e ∈ emb.faces.biUnion emb.faceBoundary, z e = 0 :=
    zero_on_ambientFaceSupport_of_interiorDualHeightParentPeelData
      (C := C) (htait := htait) (z := z)
      (allFaces := emb.faces) (faceBoundary := emb.faceBoundary)
      (data := data) (hzeroBoundary := hzeroBoundary) (horth := horth)
  intro e
  exact hzeroSupport e (by simpa [PlaneEmbeddingWithBoundary.faceSupport] using emb.mem_faceSupport e)

/-- Existential annulus-shaped global annihilator form of the weakest current Step 2 package. -/
theorem zero_on_allEdges_of_exists_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (hdata : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        (∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0) ∧
        (∀ f ∈ data.peelFaces,
          ∀ γ, γ ≠ 0 → γ ≠ C
            (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces data.roots
                data.hcoverRoots data.hsepRoots)
              data.fallbackEdge f) →
            chainDot
                (boundaryBicoloredEdges C
                  (C (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
                    (interiorDualSpanningForestRoot emb.faceBoundary emb.faces data.roots
                      data.hcoverRoots data.hsepRoots)
                    data.fallbackEdge f))
                  (C (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
                    (interiorDualSpanningForestRoot emb.faceBoundary emb.faces data.roots
                      data.hcoverRoots data.hsepRoots)
                    data.fallbackEdge f) + γ)
                  (emb.faceBoundary f.1))
                z
                (polarizedFaceGenerator C
                  (C (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
                    (interiorDualSpanningForestRoot emb.faceBoundary emb.faces data.roots
                      data.hcoverRoots data.hsepRoots)
                    data.fallbackEdge f))
                  (C (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
                    (interiorDualSpanningForestRoot emb.faceBoundary emb.faces data.roots
                      data.hcoverRoots data.hsepRoots)
                    data.fallbackEdge f) + γ)
                  (emb.faceBoundary f.1)) = 0)) :
    ∀ e, z e = 0 := by
  rcases hdata with ⟨emb, data, hzeroBoundary, horth⟩
  exact zero_on_allEdges_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    (emb := emb) (C := C) (htait := htait) (z := z) (data := data)
    (hzeroBoundary := hzeroBoundary) (horth := horth)

theorem zero_on_allEdges_of_exists_planarBoundaryInteriorDualBoundaryRootParentPeelData
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (hdata : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryInteriorDualBoundaryRootParentPeelData emb,
        (∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0) ∧
        (∀ f ∈ data.peelFaces,
          ∀ γ, γ ≠ 0 → γ ≠ C
            (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces data.roots
                data.hcoverRoots data.hsepRoots)
              data.fallbackEdge f) →
            chainDot
                (boundaryBicoloredEdges C
                  (C (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
                    (interiorDualSpanningForestRoot emb.faceBoundary emb.faces data.roots
                      data.hcoverRoots data.hsepRoots)
                    data.fallbackEdge f))
                  (C (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
                    (interiorDualSpanningForestRoot emb.faceBoundary emb.faces data.roots
                      data.hcoverRoots data.hsepRoots)
                    data.fallbackEdge f) + γ)
                  (emb.faceBoundary f.1))
                z
                (polarizedFaceGenerator C
                  (C (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
                    (interiorDualSpanningForestRoot emb.faceBoundary emb.faces data.roots
                      data.hcoverRoots data.hsepRoots)
                    data.fallbackEdge f))
                  (C (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
                    (interiorDualSpanningForestRoot emb.faceBoundary emb.faces data.roots
                      data.hcoverRoots data.hsepRoots)
                    data.fallbackEdge f) + γ)
                  (emb.faceBoundary f.1)) = 0)) :
    ∀ e, z e = 0 := by
  rcases hdata with ⟨emb, data, hzeroBoundary, horth⟩
  exact zero_on_allEdges_of_planarBoundaryInteriorDualBoundaryRootParentPeelData
    (emb := emb) (C := C) (htait := htait) (z := z) (data := data)
    (hzeroBoundary := hzeroBoundary) (horth := horth)

theorem zero_on_allEdges_of_exists_planarBoundaryInteriorDualRootDistanceParentPeelData
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (hdata : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryInteriorDualRootDistanceParentPeelData emb,
        (∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0) ∧
        (∀ f ∈ data.peelFaces,
          ∀ γ, γ ≠ 0 → γ ≠ C
            (parentSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
              data.parentFace data.fallbackEdge data.hparentAdj f) →
            chainDot
                (boundaryBicoloredEdges C
                  (C (parentSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
                    data.parentFace data.fallbackEdge data.hparentAdj f))
                  (C (parentSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
                    data.parentFace data.fallbackEdge data.hparentAdj f) + γ)
                  (emb.faceBoundary f.1))
                z
                (polarizedFaceGenerator C
                  (C (parentSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
                    data.parentFace data.fallbackEdge data.hparentAdj f))
                  (C (parentSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
                    data.parentFace data.fallbackEdge data.hparentAdj f) + γ)
                  (emb.faceBoundary f.1)) = 0)) :
    ∀ e, z e = 0 := by
  rcases hdata with ⟨emb, data, hzeroBoundary, horth⟩
  exact zero_on_allEdges_of_planarBoundaryInteriorDualRootDistanceParentPeelData
    (emb := emb) (C := C) (htait := htait) (z := z) (data := data)
    (hzeroBoundary := hzeroBoundary) (horth := horth)

theorem zero_on_allEdges_of_exists_planarBoundaryInteriorDualWellFoundedParentPeelData
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (hdata : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryInteriorDualWellFoundedParentPeelData emb,
        (∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0) ∧
        (∀ f ∈ data.peelFaces,
          ∀ γ, γ ≠ 0 → γ ≠ C
            (parentSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
              data.parentFace data.fallbackEdge data.hparentAdj f) →
            chainDot
                (boundaryBicoloredEdges C
                  (C (parentSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
                    data.parentFace data.fallbackEdge data.hparentAdj f))
                  (C (parentSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
                    data.parentFace data.fallbackEdge data.hparentAdj f) + γ)
                  (emb.faceBoundary f.1))
                z
                (polarizedFaceGenerator C
                  (C (parentSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
                    data.parentFace data.fallbackEdge data.hparentAdj f))
                  (C (parentSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
                    data.parentFace data.fallbackEdge data.hparentAdj f) + γ)
                  (emb.faceBoundary f.1)) = 0)) :
    ∀ e, z e = 0 := by
  rcases hdata with ⟨emb, data, hzeroBoundary, horth⟩
  exact zero_on_allEdges_of_planarBoundaryInteriorDualWellFoundedParentPeelData
    (emb := emb) (C := C) (htait := htait) (z := z) (data := data)
    (hzeroBoundary := hzeroBoundary) (horth := horth)

theorem zero_on_allEdges_of_exists_planarBoundaryInteriorDualHeightParentPeelData
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (hdata : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryInteriorDualHeightParentPeelData emb,
        (∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0) ∧
        (∀ f ∈ data.peelFaces,
          ∀ γ, γ ≠ 0 → γ ≠ C
            (parentSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
              data.parentFace data.fallbackEdge data.hparentAdj f) →
            chainDot
                (boundaryBicoloredEdges C
                  (C (parentSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
                    data.parentFace data.fallbackEdge data.hparentAdj f))
                  (C (parentSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
                    data.parentFace data.fallbackEdge data.hparentAdj f) + γ)
                  (emb.faceBoundary f.1))
                z
                (polarizedFaceGenerator C
                  (C (parentSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
                    data.parentFace data.fallbackEdge data.hparentAdj f))
                  (C (parentSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
                    data.parentFace data.fallbackEdge data.hparentAdj f) + γ)
                  (emb.faceBoundary f.1)) = 0)) :
    ∀ e, z e = 0 := by
  rcases hdata with ⟨emb, data, hzeroBoundary, horth⟩
  exact zero_on_allEdges_of_planarBoundaryInteriorDualHeightParentPeelData
    (emb := emb) (C := C) (htait := htait) (z := z) (data := data)
    (hzeroBoundary := hzeroBoundary) (horth := horth)

end Mettapedia.GraphTheory.FourColor
