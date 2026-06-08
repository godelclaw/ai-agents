import Mettapedia.GraphTheory.FourColor.PlanarBoundarySupportGraph
import Mettapedia.GraphTheory.FacialCyclePlanarEmbeddingWithBoundary
import Mettapedia.GraphTheory.OrderedPlanarEmbeddingWithBoundary
import Mettapedia.GraphTheory.WalkPlanarEmbeddingWithBoundaryAcyclic

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- A stronger embedding-side interface than `PlaneEmbeddingWithBoundary`: for each ambient face,
the boundary edges are presented in one explicit endpoint-sharing order. This is the honest local
data needed by the face-boundary run layer after the regression obstruction showing it cannot be
recovered from unordered face-edge incidence alone. -/
abbrev PlanarBoundaryOrderedFaceEmbeddingData {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) :=
  PlaneEmbeddingWithBoundary.OrderedFaceBoundaryData emb

/-- A walk-anchored strengthening of the boundary-order source layer: every ambient face comes
with an actual nonempty simple closed walk whose traversed graph edges lie exactly on that face
boundary. This is the new stronger source object introduced to address the boundary-order blocker
at the level of honest graph walks before later lowering to edge-list order data. -/
abbrev PlanarBoundaryClosedWalkEmbeddingData {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) :=
  PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalkGeometry emb

/-- A rotation/dart-side source for the walk-anchored boundary layer: every ambient face carries
one realized cyclic dart list whose unoriented edge support is exactly that face boundary. -/
abbrev PlanarBoundaryDartCycleEmbeddingData {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) :=
  PlaneEmbeddingWithBoundary.FaceBoundaryDartCycleGeometry emb

/-- A pure rotation/dart-side source for the walk-anchored boundary layer: every ambient face
carries one cyclic dart list whose adjacency proof is sufficient to construct the closed walk. -/
abbrev PlanarBoundaryPureDartCycleEmbeddingData {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) :=
  PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycleGeometry emb

/-- A successor-based rotation/dart-side source for the walk-anchored boundary layer: every
ambient face carries a cyclic dart list together with the local successor map around that face. -/
abbrev PlanarBoundaryDartSuccessorCycleEmbeddingData {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) :=
  PlaneEmbeddingWithBoundary.FaceBoundaryDartSuccessorCycleGeometry emb

/-- A proof-relevant strengthening of the ordered face-boundary interface: each adjacent pair of
boundary edges carries one explicit chosen shared primal endpoint. -/
abbrev PlanarBoundaryOrderedFaceVertexEmbeddingData {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) :=
  PlaneEmbeddingWithBoundary.OrderedFaceBoundaryVertexData emb

/-- An explicit ordered list of shared primal vertices between consecutive boundary edges. This
stores the chosen boundary-step vertices in the same order as the face boundary itself. -/
abbrev PlanarBoundaryOrderedFaceVertexSequenceEmbeddingData {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) :=
  PlaneEmbeddingWithBoundary.OrderedFaceBoundaryVertexSequenceData emb

/-- The ordered boundary list for one face repackaged as a `FaceBoundaryEndpointRun`. -/
def PlanarBoundaryOrderedFaceEmbeddingData.faceBoundaryRun
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryOrderedFaceEmbeddingData emb)
    (f : AmbientFace emb.faces) :
    FaceBoundaryEndpointRun emb f :=
  PlaneEmbeddingWithBoundary.OrderedFaceBoundaryData.faceBoundaryRun data f

/-- Ordered-boundary embedding data lowers directly to the existing face-boundary run geometry
package. -/
def PlanarBoundaryOrderedFaceEmbeddingData.toPlanarBoundaryFaceBoundaryRunGeometry
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryOrderedFaceEmbeddingData emb) :
    PlanarBoundaryFaceBoundaryRunGeometry emb :=
  PlaneEmbeddingWithBoundary.OrderedFaceBoundaryData.toFaceBoundaryRunGeometry data

/-- Ordered face-boundary data upgrades canonically to the proof-relevant boundary-step vertex
layer by choosing one shared endpoint for each adjacent pair. -/
noncomputable def
    PlanarBoundaryOrderedFaceEmbeddingData.toPlanarBoundaryOrderedFaceVertexEmbeddingData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryOrderedFaceEmbeddingData emb) :
    PlanarBoundaryOrderedFaceVertexEmbeddingData emb :=
  data.toOrderedFaceBoundaryVertexData

/-- Ordered face-boundary data upgrades canonically to the explicit ordered boundary-step vertex
sequence layer. -/
noncomputable def
    PlanarBoundaryOrderedFaceEmbeddingData.toPlanarBoundaryOrderedFaceVertexSequenceEmbeddingData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryOrderedFaceEmbeddingData emb) :
    PlanarBoundaryOrderedFaceVertexSequenceEmbeddingData emb :=
  data.toOrderedFaceBoundaryVertexSequenceData

/-- Facial dart-cycle embedding data lowers to the walk-anchored source on the same embedding.
This is the explicit bridge from rotation/dart-side face cycles to
`PlanarBoundaryClosedWalkEmbeddingData`. -/
def PlanarBoundaryDartCycleEmbeddingData.toPlanarBoundaryClosedWalkEmbeddingData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryDartCycleEmbeddingData emb) :
    PlanarBoundaryClosedWalkEmbeddingData emb :=
  data.toFaceBoundaryClosedWalkGeometry

/-- Pure facial dart-cycle embedding data lowers to the realized dart-cycle source on the same
embedding by constructing the closed walks from cyclic dart adjacency. -/
def PlanarBoundaryPureDartCycleEmbeddingData.toPlanarBoundaryDartCycleEmbeddingData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryPureDartCycleEmbeddingData emb) :
    PlanarBoundaryDartCycleEmbeddingData emb :=
  data.toFaceBoundaryDartCycleGeometry

/-- Pure facial dart-cycle embedding data lowers directly to the walk-anchored source on the same
embedding. -/
def PlanarBoundaryPureDartCycleEmbeddingData.toPlanarBoundaryClosedWalkEmbeddingData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryPureDartCycleEmbeddingData emb) :
    PlanarBoundaryClosedWalkEmbeddingData emb :=
  data.toFaceBoundaryClosedWalkGeometry

/-- Successor-based facial dart-cycle embedding data lowers to the pure dart-cycle source on the
same embedding. -/
def PlanarBoundaryDartSuccessorCycleEmbeddingData.toPlanarBoundaryPureDartCycleEmbeddingData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryDartSuccessorCycleEmbeddingData emb) :
    PlanarBoundaryPureDartCycleEmbeddingData emb :=
  data.toFaceBoundaryPureDartCycleGeometry

/-- Successor-based facial dart-cycle embedding data lowers to the realized dart-cycle source on
the same embedding. -/
def PlanarBoundaryDartSuccessorCycleEmbeddingData.toPlanarBoundaryDartCycleEmbeddingData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryDartSuccessorCycleEmbeddingData emb) :
    PlanarBoundaryDartCycleEmbeddingData emb :=
  data.toFaceBoundaryDartCycleGeometry

/-- Successor-based facial dart-cycle embedding data lowers directly to the walk-anchored source
on the same embedding. -/
def PlanarBoundaryDartSuccessorCycleEmbeddingData.toPlanarBoundaryClosedWalkEmbeddingData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryDartSuccessorCycleEmbeddingData emb) :
    PlanarBoundaryClosedWalkEmbeddingData emb :=
  data.toFaceBoundaryClosedWalkGeometry

/-- Forget the chosen boundary-step vertices and retain only the ordered boundary-edge data. -/
def PlanarBoundaryOrderedFaceVertexEmbeddingData.toPlanarBoundaryOrderedFaceEmbeddingData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryOrderedFaceVertexEmbeddingData emb) :
    PlanarBoundaryOrderedFaceEmbeddingData emb :=
  data.toOrderedFaceBoundaryData

/-- Forget the explicit ordered boundary-step vertex sequence and retain only the ordered
boundary-edge data. -/
def PlanarBoundaryOrderedFaceVertexSequenceEmbeddingData.toPlanarBoundaryOrderedFaceEmbeddingData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryOrderedFaceVertexSequenceEmbeddingData emb) :
    PlanarBoundaryOrderedFaceEmbeddingData emb :=
  data.toOrderedFaceBoundaryData

/-- Graph-level existence form of the stronger ordered-boundary embedding interface. -/
abbrev AdmitsPlanarBoundaryOrderedFaceEmbeddingData (G : SimpleGraph V) : Prop :=
  AdmitsOrderedFaceBoundaryPlaneEmbeddingData G

/-- Graph-level existence form of the walk-anchored boundary source interface. -/
abbrev AdmitsPlanarBoundaryClosedWalkEmbeddingData (G : SimpleGraph V) : Prop :=
  AdmitsFaceBoundaryClosedWalkGeometry G

/-- An acyclic graph with at least one edge cannot support the honest facial closed-walk source on
any embedding, because every ambient face would have to carry a nonempty closed trail in an
acyclic graph. -/
theorem not_nonempty_planarBoundaryClosedWalkEmbeddingData_of_isAcyclic_of_nonempty_edgeSet
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} (hAcyc : G.IsAcyclic)
    (hE : Nonempty G.edgeSet) :
    ¬ Nonempty (PlanarBoundaryClosedWalkEmbeddingData emb) := by
  exact
    not_nonempty_faceBoundaryClosedWalkGeometry_of_isAcyclic_of_nonempty_edgeSet hAcyc hE

/-- Consequently, an acyclic graph with at least one edge never admits the honest facial
closed-walk source at graph level. -/
theorem not_admitsPlanarBoundaryClosedWalkEmbeddingData_of_isAcyclic_of_nonempty_edgeSet
    {G : SimpleGraph V} (hAcyc : G.IsAcyclic) (hE : Nonempty G.edgeSet) :
    ¬ AdmitsPlanarBoundaryClosedWalkEmbeddingData G := by
  exact not_admitsFaceBoundaryClosedWalkGeometry_of_isAcyclic_of_nonempty_edgeSet hAcyc hE

/-- Any explicit acyclic positive-edge witness carrying a graph-level property `P` refutes a
generic derivation theorem from `P` to honest facial closed-walk data. -/
theorem not_forall_admitsPlanarBoundaryClosedWalkEmbeddingData_of_exists_isAcyclic_of_nonempty_edgeSet_and_property
    (P : SimpleGraph V → Prop)
    (hWitness : ∃ G : SimpleGraph V, G.IsAcyclic ∧ Nonempty G.edgeSet ∧ P G) :
    ¬ ∀ G : SimpleGraph V, P G → AdmitsPlanarBoundaryClosedWalkEmbeddingData G := by
  intro h
  rcases hWitness with ⟨G, hAcyc, hE, hP⟩
  exact
    not_admitsPlanarBoundaryClosedWalkEmbeddingData_of_isAcyclic_of_nonempty_edgeSet hAcyc hE
      (h G hP)

/-- Graph-level existence form of the rotation/dart-side facial cycle source. -/
abbrev AdmitsPlanarBoundaryDartCycleEmbeddingData (G : SimpleGraph V) : Prop :=
  AdmitsFaceBoundaryDartCycleGeometry G

/-- Graph-level existence form of the pure rotation/dart-side facial cycle source. -/
abbrev AdmitsPlanarBoundaryPureDartCycleEmbeddingData (G : SimpleGraph V) : Prop :=
  AdmitsFaceBoundaryPureDartCycleGeometry G

/-- Graph-level existence form of the successor-based rotation/dart-side facial cycle source. -/
abbrev AdmitsPlanarBoundaryDartSuccessorCycleEmbeddingData (G : SimpleGraph V) : Prop :=
  AdmitsFaceBoundaryDartSuccessorCycleGeometry G

/-- Graph-level existence form of the proof-relevant ordered-boundary vertex interface. -/
abbrev AdmitsPlanarBoundaryOrderedFaceVertexEmbeddingData (G : SimpleGraph V) : Prop :=
  AdmitsOrderedFaceBoundaryVertexPlaneEmbeddingData G

/-- Graph-level existence form of the explicit ordered boundary-step vertex sequence interface. -/
abbrev AdmitsPlanarBoundaryOrderedFaceVertexSequenceEmbeddingData (G : SimpleGraph V) : Prop :=
  AdmitsOrderedFaceBoundaryVertexSequencePlaneEmbeddingData G

/-- A cyclic strengthening of the ordered face-boundary source interface: each ambient face
boundary list closes up at the ends as well as being an endpoint-sharing chain. This is the
closest current source-facing proxy to genuine cyclic face-boundary order on the embedding. -/
abbrev PlanarBoundaryCyclicOrderedFaceEmbeddingData {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) :=
  PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryData emb

/-- A proof-relevant cyclic strengthening of the face-boundary source interface: each adjacent pair
in the closed face-boundary cycle carries one explicit chosen shared primal endpoint. -/
abbrev PlanarBoundaryCyclicOrderedFaceVertexEmbeddingData {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) :=
  PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryVertexData emb

/-- An explicit cyclic list of shared primal vertices between each boundary edge and its cyclic
successor. -/
abbrev PlanarBoundaryCyclicOrderedFaceVertexSequenceEmbeddingData {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) :=
  PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryVertexSequenceData emb

/-- Cyclic ordered face-boundary data forgets to the weaker linear ordered interface. -/
def PlanarBoundaryCyclicOrderedFaceEmbeddingData.toPlanarBoundaryOrderedFaceEmbeddingData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryCyclicOrderedFaceEmbeddingData emb) :
    PlanarBoundaryOrderedFaceEmbeddingData emb :=
  data.toOrderedFaceBoundaryData

/-- Cyclic ordered face-boundary data also lowers to the bundled pure face-boundary run geometry
shell used downstream. -/
def PlanarBoundaryCyclicOrderedFaceEmbeddingData.toPlanarBoundaryFaceBoundaryRunGeometry
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryCyclicOrderedFaceEmbeddingData emb) :
    PlanarBoundaryFaceBoundaryRunGeometry emb :=
  data.toFaceBoundaryRunGeometry

/-- Cyclic ordered face-boundary data upgrades canonically to the proof-relevant cyclic
boundary-step vertex layer by choosing one shared endpoint for each adjacent pair in the closed
boundary cycle. -/
noncomputable def
    PlanarBoundaryCyclicOrderedFaceEmbeddingData.toPlanarBoundaryCyclicOrderedFaceVertexEmbeddingData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryCyclicOrderedFaceEmbeddingData emb) :
    PlanarBoundaryCyclicOrderedFaceVertexEmbeddingData emb :=
  data.toCyclicOrderedFaceBoundaryVertexData

/-- Cyclic ordered face-boundary data upgrades canonically to the explicit cyclic boundary-step
vertex sequence layer. -/
noncomputable def
    PlanarBoundaryCyclicOrderedFaceEmbeddingData.toPlanarBoundaryCyclicOrderedFaceVertexSequenceEmbeddingData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryCyclicOrderedFaceEmbeddingData emb) :
    PlanarBoundaryCyclicOrderedFaceVertexSequenceEmbeddingData emb :=
  data.toCyclicOrderedFaceBoundaryVertexSequenceData

/-- Forget the chosen cyclic boundary-step vertices and retain only the cyclic boundary-edge data.
-/
def PlanarBoundaryCyclicOrderedFaceVertexEmbeddingData.toPlanarBoundaryCyclicOrderedFaceEmbeddingData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryCyclicOrderedFaceVertexEmbeddingData emb) :
    PlanarBoundaryCyclicOrderedFaceEmbeddingData emb :=
  data.toCyclicOrderedFaceBoundaryData

/-- Forget the explicit cyclic boundary-step vertex sequence and retain only the cyclic
boundary-edge data. -/
def PlanarBoundaryCyclicOrderedFaceVertexSequenceEmbeddingData.toPlanarBoundaryCyclicOrderedFaceEmbeddingData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryCyclicOrderedFaceVertexSequenceEmbeddingData emb) :
    PlanarBoundaryCyclicOrderedFaceEmbeddingData emb :=
  data.toCyclicOrderedFaceBoundaryData

/-- The pure local cyclic boundary-walk layer corresponding to cyclic ordered face-boundary data.
Each ambient face carries one closed boundary run listed exactly once. -/
abbrev PlanarBoundaryCyclicFaceBoundaryRunGeometry {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) :=
  PlaneEmbeddingWithBoundary.FaceBoundaryClosedRunGeometry emb

/-- The pure local cyclic alternating edge/vertex boundary-walk layer corresponding to the
explicit cyclic ordered shared-vertex sequence interface. -/
abbrev PlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) :=
  PlaneEmbeddingWithBoundary.FaceBoundaryClosedVertexWalkGeometry emb

/-- Cyclic ordered face-boundary data repackaged as the bundled pure cyclic boundary-walk layer. -/
def PlanarBoundaryCyclicOrderedFaceEmbeddingData.toPlanarBoundaryCyclicFaceBoundaryRunGeometry
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryCyclicOrderedFaceEmbeddingData emb) :
    PlanarBoundaryCyclicFaceBoundaryRunGeometry emb :=
  data.toFaceBoundaryClosedRunGeometry

/-- Cyclic ordered face-boundary vertex-sequence data repackaged as the bundled pure cyclic
alternating edge/vertex boundary-walk layer. -/
def PlanarBoundaryCyclicOrderedFaceVertexSequenceEmbeddingData.toPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryCyclicOrderedFaceVertexSequenceEmbeddingData emb) :
    PlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry emb :=
  data.toFaceBoundaryClosedVertexWalkGeometry

/-- Cyclic ordered face-boundary data lowers to the bundled pure cyclic alternating edge/vertex
boundary-walk layer via the explicit shared-vertex sequence interface. -/
noncomputable def PlanarBoundaryCyclicOrderedFaceEmbeddingData.toPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryCyclicOrderedFaceEmbeddingData emb) :
    PlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry emb :=
  data.toCyclicOrderedFaceBoundaryVertexSequenceData.toFaceBoundaryClosedVertexWalkGeometry

/-- Bundled pure cyclic boundary-walk geometry can be repackaged back into cyclic ordered
face-boundary embedding data. -/
def PlanarBoundaryCyclicFaceBoundaryRunGeometry.toPlanarBoundaryCyclicOrderedFaceEmbeddingData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : PlanarBoundaryCyclicFaceBoundaryRunGeometry emb) :
    PlanarBoundaryCyclicOrderedFaceEmbeddingData emb :=
  geom.toCyclicOrderedFaceBoundaryData

/-- Bundled pure cyclic alternating edge/vertex boundary-walk geometry can be repackaged back
into the explicit cyclic ordered shared-vertex sequence interface. -/
def PlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry.toPlanarBoundaryCyclicOrderedFaceVertexSequenceEmbeddingData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : PlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry emb) :
    PlanarBoundaryCyclicOrderedFaceVertexSequenceEmbeddingData emb :=
  geom.toCyclicOrderedFaceBoundaryVertexSequenceData

/-- Bundled pure cyclic alternating edge/vertex boundary-walk geometry can also be repackaged
back into cyclic ordered face-boundary embedding data. -/
def PlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry.toPlanarBoundaryCyclicOrderedFaceEmbeddingData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : PlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry emb) :
    PlanarBoundaryCyclicOrderedFaceEmbeddingData emb :=
  geom.toCyclicOrderedFaceBoundaryVertexSequenceData.toCyclicOrderedFaceBoundaryData

/-- Bundled pure cyclic alternating edge/vertex boundary-walk geometry forgets to the linear
face-boundary run shell used by the selected-boundary arc layer. -/
def PlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry.toPlanarBoundaryFaceBoundaryRunGeometry
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : PlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry emb) :
    PlanarBoundaryFaceBoundaryRunGeometry emb :=
  geom.toPlanarBoundaryCyclicOrderedFaceEmbeddingData.toPlanarBoundaryFaceBoundaryRunGeometry

/-- Graph-level existence form of the cyclic ordered face-boundary source interface. -/
abbrev AdmitsPlanarBoundaryCyclicOrderedFaceEmbeddingData (G : SimpleGraph V) : Prop :=
  AdmitsCyclicOrderedFaceBoundaryPlaneEmbeddingData G

/-- Graph-level existence form of the proof-relevant cyclic ordered face-boundary vertex
interface. -/
abbrev AdmitsPlanarBoundaryCyclicOrderedFaceVertexEmbeddingData (G : SimpleGraph V) : Prop :=
  AdmitsCyclicOrderedFaceBoundaryVertexPlaneEmbeddingData G

/-- Graph-level existence form of the explicit cyclic boundary-step vertex sequence interface. -/
abbrev AdmitsPlanarBoundaryCyclicOrderedFaceVertexSequenceEmbeddingData (G : SimpleGraph V) :
    Prop :=
  AdmitsCyclicOrderedFaceBoundaryVertexSequencePlaneEmbeddingData G

/-- Graph-level existence form of the bundled pure cyclic boundary-walk layer. -/
abbrev AdmitsPlanarBoundaryCyclicFaceBoundaryRunGeometry (G : SimpleGraph V) : Prop :=
  AdmitsFaceBoundaryClosedRunGeometry G

/-- Graph-level existence form of the bundled pure cyclic alternating edge/vertex boundary-walk
layer. -/
abbrev AdmitsPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry (G : SimpleGraph V) : Prop :=
  AdmitsFaceBoundaryClosedVertexWalkGeometry G

/-- Honest facial walks lower directly to the bundled cyclic boundary-run shell. -/
def PlanarBoundaryClosedWalkEmbeddingData.toPlanarBoundaryCyclicFaceBoundaryRunGeometry
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryClosedWalkEmbeddingData emb) :
    PlanarBoundaryCyclicFaceBoundaryRunGeometry emb :=
  data.toFaceBoundaryClosedRunGeometry

/-- Honest facial walks also yield cyclic ordered face-boundary data. -/
def PlanarBoundaryClosedWalkEmbeddingData.toPlanarBoundaryCyclicOrderedFaceEmbeddingData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryClosedWalkEmbeddingData emb) :
    PlanarBoundaryCyclicOrderedFaceEmbeddingData emb :=
  data.toCyclicOrderedFaceBoundaryData

/-- Honest facial walks lower all the way to the cyclic alternating edge/vertex boundary-walk
geometry used later in the FourColor route. -/
noncomputable def PlanarBoundaryClosedWalkEmbeddingData.toPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryClosedWalkEmbeddingData emb) :
    PlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry emb :=
  data.toFaceBoundaryClosedVertexWalkGeometry

/-- Honest facial walks forget further to the linear ordered face-boundary source layer. -/
def PlanarBoundaryClosedWalkEmbeddingData.toPlanarBoundaryOrderedFaceEmbeddingData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryClosedWalkEmbeddingData emb) :
    PlanarBoundaryOrderedFaceEmbeddingData emb :=
  data.toPlanarBoundaryCyclicOrderedFaceEmbeddingData.toPlanarBoundaryOrderedFaceEmbeddingData

/-- Honest facial walks also yield the linear face-boundary run shell used by selected-boundary
arc arguments. -/
def PlanarBoundaryClosedWalkEmbeddingData.toPlanarBoundaryFaceBoundaryRunGeometry
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryClosedWalkEmbeddingData emb) :
    PlanarBoundaryFaceBoundaryRunGeometry emb :=
  data.toPlanarBoundaryCyclicOrderedFaceEmbeddingData.toPlanarBoundaryFaceBoundaryRunGeometry

theorem
    nonempty_planarBoundaryOrderedFaceEmbeddingData_iff_nonempty_planarBoundaryOrderedFaceVertexEmbeddingData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} :
    Nonempty (PlanarBoundaryOrderedFaceEmbeddingData emb) ↔
      Nonempty (PlanarBoundaryOrderedFaceVertexEmbeddingData emb) := by
  exact nonempty_orderedFaceBoundaryData_iff_nonempty_orderedFaceBoundaryVertexData

theorem
    nonempty_planarBoundaryClosedWalkEmbeddingData_implies_nonempty_planarBoundaryCyclicFaceBoundaryRunGeometry
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} :
    Nonempty (PlanarBoundaryClosedWalkEmbeddingData emb) →
      Nonempty (PlanarBoundaryCyclicFaceBoundaryRunGeometry emb) := by
  exact nonempty_faceBoundaryClosedWalkGeometry_implies_nonempty_faceBoundaryClosedRunGeometry

theorem
    nonempty_planarBoundaryClosedWalkEmbeddingData_implies_nonempty_planarBoundaryCyclicOrderedFaceEmbeddingData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} :
    Nonempty (PlanarBoundaryClosedWalkEmbeddingData emb) →
      Nonempty (PlanarBoundaryCyclicOrderedFaceEmbeddingData emb) := by
  exact nonempty_faceBoundaryClosedWalkGeometry_implies_nonempty_cyclicOrderedFaceBoundaryData

theorem
    nonempty_planarBoundaryClosedWalkEmbeddingData_implies_nonempty_planarBoundaryCyclicFaceBoundaryVertexWalkGeometry
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} :
    Nonempty (PlanarBoundaryClosedWalkEmbeddingData emb) →
      Nonempty (PlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry emb) := by
  exact nonempty_faceBoundaryClosedWalkGeometry_implies_nonempty_faceBoundaryClosedVertexWalkGeometry

theorem
    nonempty_planarBoundaryClosedWalkEmbeddingData_implies_nonempty_planarBoundaryOrderedFaceEmbeddingData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} :
    Nonempty (PlanarBoundaryClosedWalkEmbeddingData emb) →
      Nonempty (PlanarBoundaryOrderedFaceEmbeddingData emb) := by
  intro h
  exact
    nonempty_cyclicOrderedFaceBoundaryData_implies_nonempty_orderedFaceBoundaryData <|
      nonempty_planarBoundaryClosedWalkEmbeddingData_implies_nonempty_planarBoundaryCyclicOrderedFaceEmbeddingData
        h

theorem nonempty_planarBoundaryClosedWalkEmbeddingData_implies_nonempty_planarBoundaryFaceBoundaryRunGeometry
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} :
    Nonempty (PlanarBoundaryClosedWalkEmbeddingData emb) →
      Nonempty (PlanarBoundaryFaceBoundaryRunGeometry emb) := by
  exact nonempty_faceBoundaryClosedWalkGeometry_implies_nonempty_faceBoundaryRunGeometry

theorem
    nonempty_planarBoundaryOrderedFaceEmbeddingData_iff_nonempty_planarBoundaryOrderedFaceVertexSequenceEmbeddingData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} :
    Nonempty (PlanarBoundaryOrderedFaceEmbeddingData emb) ↔
      Nonempty (PlanarBoundaryOrderedFaceVertexSequenceEmbeddingData emb) := by
  exact nonempty_orderedFaceBoundaryData_iff_nonempty_orderedFaceBoundaryVertexSequenceData

theorem nonempty_planarBoundaryOrderedFaceEmbeddingData_iff_nonempty_planarBoundaryFaceBoundaryRunGeometry
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} :
    Nonempty (PlanarBoundaryOrderedFaceEmbeddingData emb) ↔
      Nonempty (PlanarBoundaryFaceBoundaryRunGeometry emb) := by
  exact nonempty_orderedFaceBoundaryData_iff_nonempty_faceBoundaryRunGeometry

theorem
    nonempty_planarBoundaryCyclicOrderedFaceEmbeddingData_implies_nonempty_planarBoundaryOrderedFaceEmbeddingData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} :
    Nonempty (PlanarBoundaryCyclicOrderedFaceEmbeddingData emb) →
      Nonempty (PlanarBoundaryOrderedFaceEmbeddingData emb) := by
  exact nonempty_cyclicOrderedFaceBoundaryData_implies_nonempty_orderedFaceBoundaryData

theorem
    nonempty_planarBoundaryCyclicOrderedFaceEmbeddingData_iff_nonempty_planarBoundaryCyclicFaceBoundaryRunGeometry
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} :
    Nonempty (PlanarBoundaryCyclicOrderedFaceEmbeddingData emb) ↔
      Nonempty (PlanarBoundaryCyclicFaceBoundaryRunGeometry emb) := by
  exact nonempty_cyclicOrderedFaceBoundaryData_iff_nonempty_faceBoundaryClosedRunGeometry

theorem
    nonempty_planarBoundaryCyclicOrderedFaceEmbeddingData_iff_nonempty_planarBoundaryCyclicOrderedFaceVertexEmbeddingData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} :
    Nonempty (PlanarBoundaryCyclicOrderedFaceEmbeddingData emb) ↔
      Nonempty (PlanarBoundaryCyclicOrderedFaceVertexEmbeddingData emb) := by
  exact nonempty_cyclicOrderedFaceBoundaryData_iff_nonempty_cyclicOrderedFaceBoundaryVertexData

theorem
    nonempty_planarBoundaryCyclicOrderedFaceEmbeddingData_iff_nonempty_planarBoundaryCyclicOrderedFaceVertexSequenceEmbeddingData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} :
    Nonempty (PlanarBoundaryCyclicOrderedFaceEmbeddingData emb) ↔
      Nonempty (PlanarBoundaryCyclicOrderedFaceVertexSequenceEmbeddingData emb) := by
  exact nonempty_cyclicOrderedFaceBoundaryData_iff_nonempty_cyclicOrderedFaceBoundaryVertexSequenceData

theorem
    nonempty_planarBoundaryCyclicOrderedFaceVertexSequenceEmbeddingData_iff_nonempty_planarBoundaryCyclicFaceBoundaryVertexWalkGeometry
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} :
    Nonempty (PlanarBoundaryCyclicOrderedFaceVertexSequenceEmbeddingData emb) ↔
      Nonempty (PlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry emb) := by
  exact
    nonempty_cyclicOrderedFaceBoundaryVertexSequenceData_iff_nonempty_faceBoundaryClosedVertexWalkGeometry

theorem
    nonempty_planarBoundaryCyclicOrderedFaceEmbeddingData_iff_nonempty_planarBoundaryCyclicFaceBoundaryVertexWalkGeometry
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} :
    Nonempty (PlanarBoundaryCyclicOrderedFaceEmbeddingData emb) ↔
      Nonempty (PlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry emb) := by
  exact nonempty_cyclicOrderedFaceBoundaryData_iff_nonempty_faceBoundaryClosedVertexWalkGeometry

theorem
    nonempty_planarBoundaryCyclicFaceBoundaryRunGeometry_iff_nonempty_planarBoundaryCyclicFaceBoundaryVertexWalkGeometry
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} :
    Nonempty (PlanarBoundaryCyclicFaceBoundaryRunGeometry emb) ↔
      Nonempty (PlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry emb) := by
  exact nonempty_faceBoundaryClosedRunGeometry_iff_nonempty_faceBoundaryClosedVertexWalkGeometry

/-- On a fixed embedding, the dart-cycle source instantiates the walk-anchored boundary source. -/
theorem
    nonempty_planarBoundaryDartCycleEmbeddingData_implies_nonempty_planarBoundaryClosedWalkEmbeddingData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} :
    Nonempty (PlanarBoundaryDartCycleEmbeddingData emb) →
      Nonempty (PlanarBoundaryClosedWalkEmbeddingData emb) := by
  exact nonempty_faceBoundaryDartCycleGeometry_implies_nonempty_faceBoundaryClosedWalkGeometry

/-- On a fixed embedding, the pure dart-cycle source instantiates the realized dart-cycle source.
-/
theorem
    nonempty_planarBoundaryPureDartCycleEmbeddingData_implies_nonempty_planarBoundaryDartCycleEmbeddingData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} :
    Nonempty (PlanarBoundaryPureDartCycleEmbeddingData emb) →
      Nonempty (PlanarBoundaryDartCycleEmbeddingData emb) := by
  exact nonempty_faceBoundaryPureDartCycleGeometry_implies_nonempty_faceBoundaryDartCycleGeometry

/-- On a fixed embedding, the pure dart-cycle source instantiates the walk-anchored boundary
source. -/
theorem
    nonempty_planarBoundaryPureDartCycleEmbeddingData_implies_nonempty_planarBoundaryClosedWalkEmbeddingData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} :
    Nonempty (PlanarBoundaryPureDartCycleEmbeddingData emb) →
      Nonempty (PlanarBoundaryClosedWalkEmbeddingData emb) := by
  exact nonempty_faceBoundaryPureDartCycleGeometry_implies_nonempty_faceBoundaryClosedWalkGeometry

/-- On a fixed embedding, the successor-based dart-cycle source instantiates the pure dart-cycle
source. -/
theorem
    nonempty_planarBoundaryDartSuccessorCycleEmbeddingData_implies_nonempty_planarBoundaryPureDartCycleEmbeddingData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} :
    Nonempty (PlanarBoundaryDartSuccessorCycleEmbeddingData emb) →
      Nonempty (PlanarBoundaryPureDartCycleEmbeddingData emb) := by
  exact
    nonempty_faceBoundaryDartSuccessorCycleGeometry_implies_nonempty_faceBoundaryPureDartCycleGeometry

/-- On a fixed embedding, the successor-based dart-cycle source instantiates the realized
dart-cycle source. -/
theorem
    nonempty_planarBoundaryDartSuccessorCycleEmbeddingData_implies_nonempty_planarBoundaryDartCycleEmbeddingData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} :
    Nonempty (PlanarBoundaryDartSuccessorCycleEmbeddingData emb) →
      Nonempty (PlanarBoundaryDartCycleEmbeddingData emb) := by
  exact
    nonempty_faceBoundaryDartSuccessorCycleGeometry_implies_nonempty_faceBoundaryDartCycleGeometry

/-- On a fixed embedding, the successor-based dart-cycle source instantiates the walk-anchored
boundary source. -/
theorem
    nonempty_planarBoundaryDartSuccessorCycleEmbeddingData_implies_nonempty_planarBoundaryClosedWalkEmbeddingData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} :
    Nonempty (PlanarBoundaryDartSuccessorCycleEmbeddingData emb) →
      Nonempty (PlanarBoundaryClosedWalkEmbeddingData emb) := by
  exact
    nonempty_faceBoundaryDartSuccessorCycleGeometry_implies_nonempty_faceBoundaryClosedWalkGeometry

theorem admitsPlanarBoundaryOrderedFaceEmbeddingData_of_admitsPlanarBoundaryOrderedFaceVertexEmbeddingData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryOrderedFaceVertexEmbeddingData G) :
    AdmitsPlanarBoundaryOrderedFaceEmbeddingData G := by
  exact admitsOrderedFaceBoundaryPlaneEmbeddingData_of_admitsOrderedFaceBoundaryVertexPlaneEmbeddingData hG

theorem admitsPlanarBoundaryOrderedFaceVertexEmbeddingData_of_admitsPlanarBoundaryOrderedFaceEmbeddingData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryOrderedFaceEmbeddingData G) :
    AdmitsPlanarBoundaryOrderedFaceVertexEmbeddingData G := by
  exact admitsOrderedFaceBoundaryVertexPlaneEmbeddingData_of_admitsOrderedFaceBoundaryPlaneEmbeddingData hG

theorem
    admitsPlanarBoundaryOrderedFaceEmbeddingData_of_admitsPlanarBoundaryOrderedFaceVertexSequenceEmbeddingData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryOrderedFaceVertexSequenceEmbeddingData G) :
    AdmitsPlanarBoundaryOrderedFaceEmbeddingData G := by
  exact
    admitsOrderedFaceBoundaryPlaneEmbeddingData_of_admitsOrderedFaceBoundaryVertexSequencePlaneEmbeddingData
      hG

theorem
    admitsPlanarBoundaryOrderedFaceVertexSequenceEmbeddingData_of_admitsPlanarBoundaryOrderedFaceEmbeddingData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryOrderedFaceEmbeddingData G) :
    AdmitsPlanarBoundaryOrderedFaceVertexSequenceEmbeddingData G := by
  exact
    admitsOrderedFaceBoundaryVertexSequencePlaneEmbeddingData_of_admitsOrderedFaceBoundaryPlaneEmbeddingData
      hG

theorem admitsPlanarBoundaryOrderedFaceEmbeddingData_of_admitsPlanarBoundaryCyclicOrderedFaceEmbeddingData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryCyclicOrderedFaceEmbeddingData G) :
    AdmitsPlanarBoundaryOrderedFaceEmbeddingData G := by
  exact
    admitsOrderedFaceBoundaryPlaneEmbeddingData_of_admitsCyclicOrderedFaceBoundaryPlaneEmbeddingData
      hG

theorem admitsPlanarBoundaryFaceBoundaryRunGeometry_of_admitsPlanarBoundaryCyclicOrderedFaceEmbeddingData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryCyclicOrderedFaceEmbeddingData G) :
    AdmitsPlanarBoundaryFaceBoundaryRunGeometry G := by
  exact
    admitsFaceBoundaryRunGeometry_of_admitsCyclicOrderedFaceBoundaryPlaneEmbeddingData hG

/-- Graph-level rotation/dart facial cycles instantiate the walk-anchored source used by the
Theorem 4.9 boundary route. -/
theorem admitsPlanarBoundaryClosedWalkEmbeddingData_of_admitsPlanarBoundaryDartCycleEmbeddingData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryDartCycleEmbeddingData G) :
    AdmitsPlanarBoundaryClosedWalkEmbeddingData G := by
  exact admitsFaceBoundaryClosedWalkGeometry_of_admitsFaceBoundaryDartCycleGeometry hG

/-- On a fixed embedding, realized facial dart cycles are impossible on an acyclic graph with at
least one edge, because they lower to honest facial closed walks. -/
theorem not_nonempty_planarBoundaryDartCycleEmbeddingData_of_isAcyclic_of_nonempty_edgeSet
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} (hAcyc : G.IsAcyclic)
    (hE : Nonempty G.edgeSet) :
    ¬ Nonempty (PlanarBoundaryDartCycleEmbeddingData emb) := by
  intro hgeom
  exact
    not_nonempty_planarBoundaryClosedWalkEmbeddingData_of_isAcyclic_of_nonempty_edgeSet hAcyc hE
      (nonempty_planarBoundaryDartCycleEmbeddingData_implies_nonempty_planarBoundaryClosedWalkEmbeddingData
        hgeom)

/-- Consequently, graph-level realized facial dart cycles are impossible on an acyclic graph with
at least one edge. -/
theorem not_admitsPlanarBoundaryDartCycleEmbeddingData_of_isAcyclic_of_nonempty_edgeSet
    {G : SimpleGraph V} (hAcyc : G.IsAcyclic) (hE : Nonempty G.edgeSet) :
    ¬ AdmitsPlanarBoundaryDartCycleEmbeddingData G := by
  intro hgeom
  exact
    not_admitsPlanarBoundaryClosedWalkEmbeddingData_of_isAcyclic_of_nonempty_edgeSet hAcyc hE
      (admitsPlanarBoundaryClosedWalkEmbeddingData_of_admitsPlanarBoundaryDartCycleEmbeddingData hgeom)

/-- Graph-level pure rotation/dart facial cycles instantiate realized dart cycles. -/
theorem admitsPlanarBoundaryDartCycleEmbeddingData_of_admitsPlanarBoundaryPureDartCycleEmbeddingData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryPureDartCycleEmbeddingData G) :
    AdmitsPlanarBoundaryDartCycleEmbeddingData G := by
  exact admitsFaceBoundaryDartCycleGeometry_of_admitsFaceBoundaryPureDartCycleGeometry hG

/-- Graph-level pure rotation/dart facial cycles instantiate the walk-anchored source used by the
Theorem 4.9 boundary route. -/
theorem
    admitsPlanarBoundaryClosedWalkEmbeddingData_of_admitsPlanarBoundaryPureDartCycleEmbeddingData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryPureDartCycleEmbeddingData G) :
    AdmitsPlanarBoundaryClosedWalkEmbeddingData G := by
  exact admitsFaceBoundaryClosedWalkGeometry_of_admitsFaceBoundaryPureDartCycleGeometry hG

/-- On a fixed embedding, pure facial dart cycles are impossible on an acyclic graph with at
least one edge, because they still lower to honest facial closed walks. -/
theorem not_nonempty_planarBoundaryPureDartCycleEmbeddingData_of_isAcyclic_of_nonempty_edgeSet
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} (hAcyc : G.IsAcyclic)
    (hE : Nonempty G.edgeSet) :
    ¬ Nonempty (PlanarBoundaryPureDartCycleEmbeddingData emb) := by
  intro hgeom
  exact
    not_nonempty_planarBoundaryClosedWalkEmbeddingData_of_isAcyclic_of_nonempty_edgeSet hAcyc hE
      (nonempty_planarBoundaryPureDartCycleEmbeddingData_implies_nonempty_planarBoundaryClosedWalkEmbeddingData
        hgeom)

/-- Consequently, graph-level pure facial dart cycles are impossible on an acyclic graph with at
least one edge. -/
theorem not_admitsPlanarBoundaryPureDartCycleEmbeddingData_of_isAcyclic_of_nonempty_edgeSet
    {G : SimpleGraph V} (hAcyc : G.IsAcyclic) (hE : Nonempty G.edgeSet) :
    ¬ AdmitsPlanarBoundaryPureDartCycleEmbeddingData G := by
  intro hgeom
  exact
    not_admitsPlanarBoundaryClosedWalkEmbeddingData_of_isAcyclic_of_nonempty_edgeSet hAcyc hE
      (admitsPlanarBoundaryClosedWalkEmbeddingData_of_admitsPlanarBoundaryPureDartCycleEmbeddingData
        hgeom)

/-- Graph-level successor-based rotation/dart facial cycles instantiate pure dart cycles. -/
theorem
    admitsPlanarBoundaryPureDartCycleEmbeddingData_of_admitsPlanarBoundaryDartSuccessorCycleEmbeddingData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryDartSuccessorCycleEmbeddingData G) :
    AdmitsPlanarBoundaryPureDartCycleEmbeddingData G := by
  exact admitsFaceBoundaryPureDartCycleGeometry_of_admitsFaceBoundaryDartSuccessorCycleGeometry hG

/-- Graph-level successor-based rotation/dart facial cycles instantiate realized dart cycles. -/
theorem
    admitsPlanarBoundaryDartCycleEmbeddingData_of_admitsPlanarBoundaryDartSuccessorCycleEmbeddingData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryDartSuccessorCycleEmbeddingData G) :
    AdmitsPlanarBoundaryDartCycleEmbeddingData G := by
  exact admitsFaceBoundaryDartCycleGeometry_of_admitsFaceBoundaryDartSuccessorCycleGeometry hG

/-- Graph-level successor-based rotation/dart facial cycles instantiate the walk-anchored source
used by the Theorem 4.9 boundary route. -/
theorem
    admitsPlanarBoundaryClosedWalkEmbeddingData_of_admitsPlanarBoundaryDartSuccessorCycleEmbeddingData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryDartSuccessorCycleEmbeddingData G) :
    AdmitsPlanarBoundaryClosedWalkEmbeddingData G := by
  exact admitsFaceBoundaryClosedWalkGeometry_of_admitsFaceBoundaryDartSuccessorCycleGeometry hG

/-- On a fixed embedding, successor-based facial dart cycles are impossible on an acyclic graph
with at least one edge, because they lower to honest facial closed walks. -/
theorem not_nonempty_planarBoundaryDartSuccessorCycleEmbeddingData_of_isAcyclic_of_nonempty_edgeSet
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} (hAcyc : G.IsAcyclic)
    (hE : Nonempty G.edgeSet) :
    ¬ Nonempty (PlanarBoundaryDartSuccessorCycleEmbeddingData emb) := by
  intro hgeom
  exact
    not_nonempty_planarBoundaryClosedWalkEmbeddingData_of_isAcyclic_of_nonempty_edgeSet hAcyc hE
      (nonempty_planarBoundaryDartSuccessorCycleEmbeddingData_implies_nonempty_planarBoundaryClosedWalkEmbeddingData
        hgeom)

/-- Consequently, graph-level successor-based facial dart cycles are impossible on an acyclic
graph with at least one edge. -/
theorem not_admitsPlanarBoundaryDartSuccessorCycleEmbeddingData_of_isAcyclic_of_nonempty_edgeSet
    {G : SimpleGraph V} (hAcyc : G.IsAcyclic) (hE : Nonempty G.edgeSet) :
    ¬ AdmitsPlanarBoundaryDartSuccessorCycleEmbeddingData G := by
  intro hgeom
  exact
    not_admitsPlanarBoundaryClosedWalkEmbeddingData_of_isAcyclic_of_nonempty_edgeSet hAcyc hE
      (admitsPlanarBoundaryClosedWalkEmbeddingData_of_admitsPlanarBoundaryDartSuccessorCycleEmbeddingData
        hgeom)

theorem admitsPlanarBoundaryCyclicOrderedFaceEmbeddingData_of_admitsPlanarBoundaryClosedWalkEmbeddingData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryClosedWalkEmbeddingData G) :
    AdmitsPlanarBoundaryCyclicOrderedFaceEmbeddingData G := by
  exact
    admitsCyclicOrderedFaceBoundaryPlaneEmbeddingData_of_admitsFaceBoundaryClosedWalkGeometry hG

theorem admitsPlanarBoundaryOrderedFaceEmbeddingData_of_admitsPlanarBoundaryClosedWalkEmbeddingData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryClosedWalkEmbeddingData G) :
    AdmitsPlanarBoundaryOrderedFaceEmbeddingData G := by
  exact
    admitsPlanarBoundaryOrderedFaceEmbeddingData_of_admitsPlanarBoundaryCyclicOrderedFaceEmbeddingData
      (admitsPlanarBoundaryCyclicOrderedFaceEmbeddingData_of_admitsPlanarBoundaryClosedWalkEmbeddingData
        hG)

theorem admitsPlanarBoundaryCyclicFaceBoundaryRunGeometry_of_admitsPlanarBoundaryClosedWalkEmbeddingData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryClosedWalkEmbeddingData G) :
    AdmitsPlanarBoundaryCyclicFaceBoundaryRunGeometry G := by
  exact admitsFaceBoundaryClosedRunGeometry_of_admitsFaceBoundaryClosedWalkGeometry hG

theorem
    admitsPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry_of_admitsPlanarBoundaryClosedWalkEmbeddingData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryClosedWalkEmbeddingData G) :
    AdmitsPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry G := by
  exact admitsFaceBoundaryClosedVertexWalkGeometry_of_admitsFaceBoundaryClosedWalkGeometry hG

theorem admitsPlanarBoundaryFaceBoundaryRunGeometry_of_admitsPlanarBoundaryClosedWalkEmbeddingData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryClosedWalkEmbeddingData G) :
    AdmitsPlanarBoundaryFaceBoundaryRunGeometry G := by
  exact admitsFaceBoundaryRunGeometry_of_admitsFaceBoundaryClosedWalkGeometry hG

theorem admitsPlanarBoundaryCyclicFaceBoundaryRunGeometry_of_admitsPlanarBoundaryCyclicOrderedFaceEmbeddingData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryCyclicOrderedFaceEmbeddingData G) :
    AdmitsPlanarBoundaryCyclicFaceBoundaryRunGeometry G := by
  exact admitsFaceBoundaryClosedRunGeometry_of_admitsCyclicOrderedFaceBoundaryPlaneEmbeddingData hG

theorem
    admitsPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry_of_admitsPlanarBoundaryCyclicOrderedFaceEmbeddingData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryCyclicOrderedFaceEmbeddingData G) :
    AdmitsPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry G := by
  exact
    admitsFaceBoundaryClosedVertexWalkGeometry_of_admitsCyclicOrderedFaceBoundaryPlaneEmbeddingData
      hG

theorem
    admitsPlanarBoundaryCyclicOrderedFaceEmbeddingData_of_admitsPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry G) :
    AdmitsPlanarBoundaryCyclicOrderedFaceEmbeddingData G := by
  exact
    admitsCyclicOrderedFaceBoundaryPlaneEmbeddingData_of_admitsFaceBoundaryClosedVertexWalkGeometry
      hG

theorem admitsPlanarBoundaryCyclicOrderedFaceEmbeddingData_of_admitsPlanarBoundaryCyclicFaceBoundaryRunGeometry
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryCyclicFaceBoundaryRunGeometry G) :
    AdmitsPlanarBoundaryCyclicOrderedFaceEmbeddingData G := by
  exact admitsCyclicOrderedFaceBoundaryPlaneEmbeddingData_of_admitsFaceBoundaryClosedRunGeometry hG

theorem
    admitsPlanarBoundaryCyclicOrderedFaceEmbeddingData_of_admitsPlanarBoundaryCyclicOrderedFaceVertexEmbeddingData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryCyclicOrderedFaceVertexEmbeddingData G) :
    AdmitsPlanarBoundaryCyclicOrderedFaceEmbeddingData G := by
  exact
    admitsCyclicOrderedFaceBoundaryPlaneEmbeddingData_of_admitsCyclicOrderedFaceBoundaryVertexPlaneEmbeddingData
      hG

theorem
    admitsPlanarBoundaryCyclicOrderedFaceVertexEmbeddingData_of_admitsPlanarBoundaryCyclicOrderedFaceEmbeddingData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryCyclicOrderedFaceEmbeddingData G) :
    AdmitsPlanarBoundaryCyclicOrderedFaceVertexEmbeddingData G := by
  exact
    admitsCyclicOrderedFaceBoundaryVertexPlaneEmbeddingData_of_admitsCyclicOrderedFaceBoundaryPlaneEmbeddingData
      hG

theorem
    admitsPlanarBoundaryCyclicOrderedFaceEmbeddingData_of_admitsPlanarBoundaryCyclicOrderedFaceVertexSequenceEmbeddingData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryCyclicOrderedFaceVertexSequenceEmbeddingData G) :
    AdmitsPlanarBoundaryCyclicOrderedFaceEmbeddingData G := by
  exact
    admitsCyclicOrderedFaceBoundaryPlaneEmbeddingData_of_admitsCyclicOrderedFaceBoundaryVertexSequencePlaneEmbeddingData
      hG

theorem
    admitsPlanarBoundaryCyclicOrderedFaceVertexSequenceEmbeddingData_of_admitsPlanarBoundaryCyclicOrderedFaceEmbeddingData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryCyclicOrderedFaceEmbeddingData G) :
    AdmitsPlanarBoundaryCyclicOrderedFaceVertexSequenceEmbeddingData G := by
  exact
    admitsCyclicOrderedFaceBoundaryVertexSequencePlaneEmbeddingData_of_admitsCyclicOrderedFaceBoundaryPlaneEmbeddingData
      hG

theorem admitsPlanarBoundaryCyclicOrderedFaceEmbeddingData_iff_admitsPlanarBoundaryCyclicFaceBoundaryRunGeometry
    {G : SimpleGraph V} :
    AdmitsPlanarBoundaryCyclicOrderedFaceEmbeddingData G ↔
      AdmitsPlanarBoundaryCyclicFaceBoundaryRunGeometry G := by
  exact admitsCyclicOrderedFaceBoundaryPlaneEmbeddingData_iff_admitsFaceBoundaryClosedRunGeometry

theorem admitsPlanarBoundaryCyclicOrderedFaceEmbeddingData_iff_admitsPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry
    {G : SimpleGraph V} :
    AdmitsPlanarBoundaryCyclicOrderedFaceEmbeddingData G ↔
      AdmitsPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry G := by
  simpa [Iff.comm] using
    (admitsFaceBoundaryClosedVertexWalkGeometry_iff_admitsCyclicOrderedFaceBoundaryPlaneEmbeddingData
      (V := V) (G := G))

theorem admitsPlanarBoundaryFaceBoundaryRunGeometry_of_admitsPlanarBoundaryCyclicFaceBoundaryRunGeometry
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryCyclicFaceBoundaryRunGeometry G) :
    AdmitsPlanarBoundaryFaceBoundaryRunGeometry G := by
  exact admitsFaceBoundaryRunGeometry_of_admitsFaceBoundaryClosedRunGeometry hG

theorem admitsPlanarBoundaryCyclicFaceBoundaryRunGeometry_of_admitsPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry G) :
    AdmitsPlanarBoundaryCyclicFaceBoundaryRunGeometry G := by
  exact admitsFaceBoundaryClosedRunGeometry_of_admitsFaceBoundaryClosedVertexWalkGeometry hG

theorem admitsPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry_of_admitsPlanarBoundaryCyclicFaceBoundaryRunGeometry
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryCyclicFaceBoundaryRunGeometry G) :
    AdmitsPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry G := by
  exact admitsFaceBoundaryClosedVertexWalkGeometry_of_admitsFaceBoundaryClosedRunGeometry hG

theorem
    admitsPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry_iff_admitsPlanarBoundaryCyclicFaceBoundaryRunGeometry
    {G : SimpleGraph V} :
    AdmitsPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry G ↔
      AdmitsPlanarBoundaryCyclicFaceBoundaryRunGeometry G := by
  exact admitsFaceBoundaryClosedVertexWalkGeometry_iff_admitsFaceBoundaryClosedRunGeometry

theorem admitsPlanarBoundaryFaceBoundaryRunGeometry_of_admitsPlanarBoundaryOrderedFaceEmbeddingData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryOrderedFaceEmbeddingData G) :
    AdmitsPlanarBoundaryFaceBoundaryRunGeometry G := by
  exact admitsFaceBoundaryRunGeometry_of_admitsOrderedFaceBoundaryPlaneEmbeddingData hG

theorem admitsPlanarBoundaryOrderedFaceEmbeddingData_of_admitsPlanarBoundaryFaceBoundaryRunGeometry
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryFaceBoundaryRunGeometry G) :
    AdmitsPlanarBoundaryOrderedFaceEmbeddingData G := by
  exact admitsOrderedFaceBoundaryPlaneEmbeddingData_of_admitsFaceBoundaryRunGeometry hG

theorem admitsPlanarBoundaryOrderedFaceEmbeddingData_iff_admitsPlanarBoundaryFaceBoundaryRunGeometry
    {G : SimpleGraph V} :
    AdmitsPlanarBoundaryOrderedFaceEmbeddingData G ↔
      AdmitsPlanarBoundaryFaceBoundaryRunGeometry G := by
  exact admitsOrderedFaceBoundaryPlaneEmbeddingData_iff_admitsFaceBoundaryRunGeometry

theorem admitsPlanarBoundaryOrderedFaceVertexEmbeddingData_iff_admitsPlanarBoundaryOrderedFaceEmbeddingData
    {G : SimpleGraph V} :
    AdmitsPlanarBoundaryOrderedFaceVertexEmbeddingData G ↔
      AdmitsPlanarBoundaryOrderedFaceEmbeddingData G := by
  exact admitsOrderedFaceBoundaryVertexPlaneEmbeddingData_iff_admitsOrderedFaceBoundaryPlaneEmbeddingData

theorem
    admitsPlanarBoundaryOrderedFaceVertexSequenceEmbeddingData_iff_admitsPlanarBoundaryOrderedFaceEmbeddingData
    {G : SimpleGraph V} :
    AdmitsPlanarBoundaryOrderedFaceVertexSequenceEmbeddingData G ↔
      AdmitsPlanarBoundaryOrderedFaceEmbeddingData G := by
  exact
    admitsOrderedFaceBoundaryVertexSequencePlaneEmbeddingData_iff_admitsOrderedFaceBoundaryPlaneEmbeddingData

theorem
    admitsPlanarBoundaryCyclicOrderedFaceVertexEmbeddingData_iff_admitsPlanarBoundaryCyclicOrderedFaceEmbeddingData
    {G : SimpleGraph V} :
    AdmitsPlanarBoundaryCyclicOrderedFaceVertexEmbeddingData G ↔
      AdmitsPlanarBoundaryCyclicOrderedFaceEmbeddingData G := by
  exact
    admitsCyclicOrderedFaceBoundaryVertexPlaneEmbeddingData_iff_admitsCyclicOrderedFaceBoundaryPlaneEmbeddingData

theorem
    admitsPlanarBoundaryCyclicOrderedFaceVertexSequenceEmbeddingData_iff_admitsPlanarBoundaryCyclicOrderedFaceEmbeddingData
    {G : SimpleGraph V} :
    AdmitsPlanarBoundaryCyclicOrderedFaceVertexSequenceEmbeddingData G ↔
      AdmitsPlanarBoundaryCyclicOrderedFaceEmbeddingData G := by
  exact
    admitsCyclicOrderedFaceBoundaryVertexSequencePlaneEmbeddingData_iff_admitsCyclicOrderedFaceBoundaryPlaneEmbeddingData

/-- Ordered-boundary embedding data together with one contiguous selected-boundary arc on each
ambient face. This is the direct source-facing primitive behind the bundled
`PlanarBoundarySelectedBoundaryArcGeometry` shell. -/
structure PlanarBoundaryOrderedFaceArcEmbeddingData {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G)
    extends PlanarBoundaryOrderedFaceEmbeddingData emb where
  selectedBoundaryArc :
    ∀ f : AmbientFace emb.faces,
      ∃ selectedRun : List G.edgeSet,
        selectedRun <:+: faceBoundaryOrder f ∧
          ∀ e : G.edgeSet,
            e ∈ selectedRun ↔
            e ∈ emb.faceBoundary f.1 ∧
                e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces

/-- The cyclic strengthening of the ordered face-boundary-plus-selected-arc interface. The full
face-boundary order on each ambient face closes up at the ends, in addition to supporting one
contiguous selected-boundary arc. -/
structure PlanarBoundaryCyclicOrderedFaceArcEmbeddingData {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G)
    extends PlanarBoundaryOrderedFaceArcEmbeddingData emb where
  hwrap : ∀ f : AmbientFace emb.faces, ∀ first last : G.edgeSet,
    (faceBoundaryOrder f).head? = some first →
      (faceBoundaryOrder f).getLast? = some last →
        planarBoundaryEdgeEndpointAdj last first

/-- Forget the selected-boundary arc witnesses and retain only the ordered full face-boundary
data. This explicit map avoids relying on projection naming through the local abbreviation. -/
def PlanarBoundaryOrderedFaceArcEmbeddingData.toPlanarBoundaryOrderedFaceEmbeddingData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryOrderedFaceArcEmbeddingData emb) :
    PlanarBoundaryOrderedFaceEmbeddingData emb where
  faceBoundaryOrder := data.faceBoundaryOrder
  hchain := data.hchain
  hnodup := data.hnodup
  hmem := data.hmem

/-- Forget the selected-boundary arc witnesses and retain only the cyclic full face-boundary
data. -/
def PlanarBoundaryCyclicOrderedFaceArcEmbeddingData.toPlanarBoundaryCyclicOrderedFaceEmbeddingData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb) :
    PlanarBoundaryCyclicOrderedFaceEmbeddingData emb where
  faceBoundaryOrder := data.faceBoundaryOrder
  hchain := data.hchain
  hnodup := data.hnodup
  hmem := data.hmem
  hwrap := data.hwrap

/-- The facewise contiguity half of the ordered-boundary arc interface, expressed on top of the
existing `PlanarBoundaryFaceBoundaryRunGeometry` shell. -/
theorem PlanarBoundaryOrderedFaceArcEmbeddingData.selectedBoundaryArcOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryOrderedFaceArcEmbeddingData emb) :
    ∀ f : AmbientFace emb.faces,
      (PlanarBoundaryOrderedFaceEmbeddingData.toPlanarBoundaryFaceBoundaryRunGeometry
        data.toPlanarBoundaryOrderedFaceEmbeddingData).SelectedBoundaryArcOnFace f := by
  intro f
  rcases data.selectedBoundaryArc f with ⟨selectedRun, hinfix, hselected⟩
  exact ⟨selectedRun, hinfix, hselected⟩

/-- Ordered-boundary arc embedding data lowers directly to the bundled selected-boundary arc
geometry package. -/
def PlanarBoundaryOrderedFaceArcEmbeddingData.toPlanarBoundarySelectedBoundaryArcGeometry
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryOrderedFaceArcEmbeddingData emb) :
    PlanarBoundarySelectedBoundaryArcGeometry emb where
  faceBoundaryRun := PlanarBoundaryOrderedFaceEmbeddingData.faceBoundaryRun
    data.toPlanarBoundaryOrderedFaceEmbeddingData
  selectedBoundaryArc := by
    intro f
    simpa [PlanarBoundaryOrderedFaceEmbeddingData.faceBoundaryRun,
      PlaneEmbeddingWithBoundary.OrderedFaceBoundaryData.faceBoundaryRun]
      using data.selectedBoundaryArc f

/-- Bundled selected-boundary arc geometry can be repackaged back into the stronger ordered
face-boundary-plus-arc embedding interface. -/
def PlanarBoundarySelectedBoundaryArcGeometry.toPlanarBoundaryOrderedFaceArcEmbeddingData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : PlanarBoundarySelectedBoundaryArcGeometry emb) :
    PlanarBoundaryOrderedFaceArcEmbeddingData emb where
  faceBoundaryOrder := fun f => (geom.faceBoundaryRun f).run
  hchain := fun f => (geom.faceBoundaryRun f).hchain
  hnodup := fun f => (geom.faceBoundaryRun f).hnodup
  hmem := fun f => (geom.faceBoundaryRun f).hmem
  selectedBoundaryArc := geom.selectedBoundaryArc

/-- Ordered-boundary arc embedding data also lowers to the split graph-level target
`PlanarBoundaryFaceBoundaryRunGeometry + SelectedBoundaryArcOnFace`. -/
theorem
    PlanarBoundaryOrderedFaceArcEmbeddingData.toPlanarBoundaryFaceBoundaryRunGeometryAndSelectedBoundaryArcOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryOrderedFaceArcEmbeddingData emb) :
    ∀ f : AmbientFace emb.faces,
      (PlanarBoundaryOrderedFaceEmbeddingData.toPlanarBoundaryFaceBoundaryRunGeometry
        data.toPlanarBoundaryOrderedFaceEmbeddingData).SelectedBoundaryArcOnFace f :=
  data.selectedBoundaryArcOnFace

/-- Ordered full face-boundary runs together with per-face selected-boundary contiguity witnesses
can be repackaged into the stronger ordered face-arc embedding interface. -/
def PlanarBoundaryFaceBoundaryRunGeometry.toPlanarBoundaryOrderedFaceArcEmbeddingData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : PlanarBoundaryFaceBoundaryRunGeometry emb)
    (harc : ∀ f : AmbientFace emb.faces, geom.SelectedBoundaryArcOnFace f) :
    PlanarBoundaryOrderedFaceArcEmbeddingData emb where
  faceBoundaryOrder := fun f => (geom.faceBoundaryRun f).run
  hchain := fun f => (geom.faceBoundaryRun f).hchain
  hnodup := fun f => (geom.faceBoundaryRun f).hnodup
  hmem := fun f => (geom.faceBoundaryRun f).hmem
  selectedBoundaryArc := by
    intro f
    exact harc f

theorem nonempty_planarBoundaryOrderedFaceArcEmbeddingData_iff_nonempty_planarBoundarySelectedBoundaryArcGeometry
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} :
    Nonempty (PlanarBoundaryOrderedFaceArcEmbeddingData emb) ↔
      Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb) := by
  constructor
  · rintro ⟨data⟩
    exact ⟨data.toPlanarBoundarySelectedBoundaryArcGeometry⟩
  · rintro ⟨geom⟩
    exact ⟨geom.toPlanarBoundaryOrderedFaceArcEmbeddingData⟩

theorem
    nonempty_planarBoundaryOrderedFaceArcEmbeddingData_iff_exists_planarBoundaryFaceBoundaryRunGeometryAndSelectedBoundaryArcOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} :
    Nonempty (PlanarBoundaryOrderedFaceArcEmbeddingData emb) ↔
      ∃ geom : PlanarBoundaryFaceBoundaryRunGeometry emb,
        ∀ f : AmbientFace emb.faces, geom.SelectedBoundaryArcOnFace f := by
  constructor
  · rintro ⟨data⟩
    exact
      ⟨PlanarBoundaryOrderedFaceEmbeddingData.toPlanarBoundaryFaceBoundaryRunGeometry
          data.toPlanarBoundaryOrderedFaceEmbeddingData,
        data.toPlanarBoundaryFaceBoundaryRunGeometryAndSelectedBoundaryArcOnFace⟩
  · rintro ⟨geom, harc⟩
    exact ⟨geom.toPlanarBoundaryOrderedFaceArcEmbeddingData harc⟩

/-- Ordered-boundary arc embedding data lowers directly to the root-free facewise reachability
shell on the selected-boundary support graph. -/
theorem PlanarBoundaryOrderedFaceArcEmbeddingData.boundaryComponentReachableOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryOrderedFaceArcEmbeddingData emb) :
    ∀ f : AmbientFace emb.faces, BoundaryComponentReachableOnFace (emb := emb) f := by
  intro f
  exact
    (PlanarBoundaryOrderedFaceArcEmbeddingData.toPlanarBoundarySelectedBoundaryArcGeometry data
      |>.boundaryComponentReachableOnFace) f

/-- The cyclic source-facing ordered face-arc data lowers directly to the bundled selected-arc
geometry shell. -/
def PlanarBoundaryCyclicOrderedFaceArcEmbeddingData.toPlanarBoundarySelectedBoundaryArcGeometry
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb) :
    PlanarBoundarySelectedBoundaryArcGeometry emb :=
  data.toPlanarBoundaryOrderedFaceArcEmbeddingData.toPlanarBoundarySelectedBoundaryArcGeometry

/-- The cyclic source-facing ordered face-arc data also lowers to the split run-plus-contiguity
geometry shell. -/
theorem
    PlanarBoundaryCyclicOrderedFaceArcEmbeddingData.toPlanarBoundaryFaceBoundaryRunGeometryAndSelectedBoundaryArcOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb) :
    ∀ f : AmbientFace emb.faces,
      (PlanarBoundaryOrderedFaceEmbeddingData.toPlanarBoundaryFaceBoundaryRunGeometry
        data.toPlanarBoundaryOrderedFaceEmbeddingData).SelectedBoundaryArcOnFace f :=
  data.toPlanarBoundaryOrderedFaceArcEmbeddingData
    |>.toPlanarBoundaryFaceBoundaryRunGeometryAndSelectedBoundaryArcOnFace

/-- Cyclic alternating edge/vertex face-boundary walks together with per-face selected-boundary
contiguity on the induced linear runs can be repackaged into the cyclic ordered face-arc
embedding interface. -/
def PlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry.toPlanarBoundaryCyclicOrderedFaceArcEmbeddingData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : PlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry emb)
    (harc : ∀ f : AmbientFace emb.faces,
      (geom.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) :
    PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb where
  faceBoundaryOrder := geom.toPlanarBoundaryCyclicOrderedFaceEmbeddingData.faceBoundaryOrder
  hchain := geom.toPlanarBoundaryCyclicOrderedFaceEmbeddingData.hchain
  hnodup := geom.toPlanarBoundaryCyclicOrderedFaceEmbeddingData.hnodup
  hmem := geom.toPlanarBoundaryCyclicOrderedFaceEmbeddingData.hmem
  selectedBoundaryArc := by
    intro f
    exact harc f
  hwrap := geom.toPlanarBoundaryCyclicOrderedFaceEmbeddingData.hwrap

/-- Honest facial closed walks together with per-face selected-boundary contiguity on the induced
linear runs can also be repackaged directly into the cyclic ordered face-arc embedding interface.
This keeps the stronger walk-anchored source surface visible instead of forcing an intermediate
manual detour through the cyclic surrogate layers. -/
noncomputable def PlanarBoundaryClosedWalkEmbeddingData.toPlanarBoundaryCyclicOrderedFaceArcEmbeddingData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryClosedWalkEmbeddingData emb)
    (harc : ∀ f : AmbientFace emb.faces,
      (data.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) :
    PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb :=
  PlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry.toPlanarBoundaryCyclicOrderedFaceArcEmbeddingData
    (data.toPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry)
    (by
      intro f
      simpa
        [PlanarBoundaryClosedWalkEmbeddingData.toPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry,
          PlanarBoundaryClosedWalkEmbeddingData.toPlanarBoundaryFaceBoundaryRunGeometry,
          PlanarBoundaryClosedWalkEmbeddingData.toPlanarBoundaryCyclicOrderedFaceEmbeddingData,
          PlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry.toPlanarBoundaryFaceBoundaryRunGeometry]
        using harc f)

theorem
    nonempty_planarBoundaryCyclicOrderedFaceArcEmbeddingData_iff_exists_planarBoundaryCyclicFaceBoundaryVertexWalkGeometryAndSelectedBoundaryArcOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} :
    Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb) ↔
      ∃ geom : PlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry emb,
        ∀ f : AmbientFace emb.faces,
          (geom.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f := by
  constructor
  · rintro ⟨data⟩
    refine ⟨data.toPlanarBoundaryCyclicOrderedFaceEmbeddingData.toPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry, ?_⟩
    simpa [PlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry.toPlanarBoundaryFaceBoundaryRunGeometry,
      PlanarBoundaryCyclicOrderedFaceEmbeddingData.toPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry]
      using data.toPlanarBoundaryFaceBoundaryRunGeometryAndSelectedBoundaryArcOnFace
  · rintro ⟨geom, harc⟩
    exact ⟨geom.toPlanarBoundaryCyclicOrderedFaceArcEmbeddingData harc⟩

/-- The cyclic source-facing ordered face-arc data lowers directly to the root-free facewise
reachability shell. -/
theorem PlanarBoundaryCyclicOrderedFaceArcEmbeddingData.boundaryComponentReachableOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb) :
    ∀ f : AmbientFace emb.faces, BoundaryComponentReachableOnFace (emb := emb) f := by
  exact data.toPlanarBoundaryOrderedFaceArcEmbeddingData.boundaryComponentReachableOnFace

/-- Graph-level existence form of the stronger ordered-boundary-plus-selected-arc interface. -/
def AdmitsPlanarBoundaryOrderedFaceArcEmbeddingData (G : SimpleGraph V) : Prop :=
  ∃ emb : PlaneEmbeddingWithBoundary G,
    Nonempty (PlanarBoundaryOrderedFaceArcEmbeddingData emb)

/-- Graph-level existence form of the cyclic strengthening of the ordered-boundary-plus-selected-arc
interface. -/
def AdmitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData (G : SimpleGraph V) : Prop :=
  ∃ emb : PlaneEmbeddingWithBoundary G,
    Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb)

/-- Split graph-level existence form of the cyclic edge/vertex face-boundary walk shell together
with per-face selected-boundary contiguity on the induced linear runs. -/
def AdmitsPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometryAndSelectedBoundaryArcOnFace
    (G : SimpleGraph V) : Prop :=
  ∃ emb : PlaneEmbeddingWithBoundary G,
    ∃ geom : PlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry emb,
      ∀ f : AmbientFace emb.faces,
        (geom.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f

/-- Split graph-level existence form of the honest facial closed-walk source together with
per-face selected-boundary contiguity on the induced linear runs. This is the current strongest
local source interface below actual planar-topology derivations. -/
def AdmitsPlanarBoundaryClosedWalkEmbeddingDataAndSelectedBoundaryArcOnFace
    (G : SimpleGraph V) : Prop :=
  ∃ emb : PlaneEmbeddingWithBoundary G,
    ∃ geom : PlanarBoundaryClosedWalkEmbeddingData emb,
      ∀ f : AmbientFace emb.faces,
        (geom.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f

theorem admitsPlanarBoundaryFaceBoundaryRunGeometryAndSelectedBoundaryArcOnFace_of_admitsPlanarBoundaryOrderedFaceArcEmbeddingData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryOrderedFaceArcEmbeddingData G) :
    AdmitsPlanarBoundaryFaceBoundaryRunGeometryAndSelectedBoundaryArcOnFace G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact
    ⟨emb,
      PlanarBoundaryOrderedFaceEmbeddingData.toPlanarBoundaryFaceBoundaryRunGeometry
        data.toPlanarBoundaryOrderedFaceEmbeddingData,
      data.toPlanarBoundaryFaceBoundaryRunGeometryAndSelectedBoundaryArcOnFace⟩

theorem admitsPlanarBoundarySelectedBoundaryArcGeometry_of_admitsPlanarBoundaryOrderedFaceArcEmbeddingData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryOrderedFaceArcEmbeddingData G) :
    AdmitsPlanarBoundarySelectedBoundaryArcGeometry G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨PlanarBoundaryOrderedFaceArcEmbeddingData.toPlanarBoundarySelectedBoundaryArcGeometry data⟩⟩

theorem admitsPlanarBoundaryOrderedFaceArcEmbeddingData_of_admitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData G) :
    AdmitsPlanarBoundaryOrderedFaceArcEmbeddingData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.toPlanarBoundaryOrderedFaceArcEmbeddingData⟩⟩

theorem admitsPlanarBoundaryCyclicOrderedFaceEmbeddingData_of_admitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData G) :
    AdmitsPlanarBoundaryCyclicOrderedFaceEmbeddingData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.toPlanarBoundaryCyclicOrderedFaceEmbeddingData⟩⟩

theorem admitsPlanarBoundarySelectedBoundaryArcGeometry_of_admitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData G) :
    AdmitsPlanarBoundarySelectedBoundaryArcGeometry G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.toPlanarBoundarySelectedBoundaryArcGeometry⟩⟩

theorem
    admitsPlanarBoundaryFaceBoundaryRunGeometryAndSelectedBoundaryArcOnFace_of_admitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData G) :
    AdmitsPlanarBoundaryFaceBoundaryRunGeometryAndSelectedBoundaryArcOnFace G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact
    ⟨emb,
      data.toPlanarBoundaryOrderedFaceEmbeddingData.toPlanarBoundaryFaceBoundaryRunGeometry,
      data.toPlanarBoundaryFaceBoundaryRunGeometryAndSelectedBoundaryArcOnFace⟩

theorem
    admitsPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometryAndSelectedBoundaryArcOnFace_of_admitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData G) :
    AdmitsPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometryAndSelectedBoundaryArcOnFace G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  refine ⟨emb, data.toPlanarBoundaryCyclicOrderedFaceEmbeddingData.toPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry, ?_⟩
  simpa [PlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry.toPlanarBoundaryFaceBoundaryRunGeometry,
    PlanarBoundaryCyclicOrderedFaceEmbeddingData.toPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry]
    using data.toPlanarBoundaryFaceBoundaryRunGeometryAndSelectedBoundaryArcOnFace

theorem
    admitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData_of_admitsPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometryAndSelectedBoundaryArcOnFace
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometryAndSelectedBoundaryArcOnFace G) :
    AdmitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData G := by
  rcases hG with ⟨emb, geom, harc⟩
  exact ⟨emb, ⟨geom.toPlanarBoundaryCyclicOrderedFaceArcEmbeddingData harc⟩⟩

theorem
    admitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData_iff_admitsPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometryAndSelectedBoundaryArcOnFace
    {G : SimpleGraph V} :
    AdmitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData G ↔
      AdmitsPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometryAndSelectedBoundaryArcOnFace G := by
  constructor
  · exact
      admitsPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometryAndSelectedBoundaryArcOnFace_of_admitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData
  · exact
      admitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData_of_admitsPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometryAndSelectedBoundaryArcOnFace

theorem
    admitsPlanarBoundaryFaceBoundaryRunGeometryAndSelectedBoundaryArcOnFace_of_admitsPlanarBoundaryClosedWalkEmbeddingDataAndSelectedBoundaryArcOnFace
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryClosedWalkEmbeddingDataAndSelectedBoundaryArcOnFace G) :
    AdmitsPlanarBoundaryFaceBoundaryRunGeometryAndSelectedBoundaryArcOnFace G := by
  rcases hG with ⟨emb, geom, harc⟩
  exact ⟨emb, geom.toPlanarBoundaryFaceBoundaryRunGeometry, harc⟩

theorem
    admitsPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometryAndSelectedBoundaryArcOnFace_of_admitsPlanarBoundaryClosedWalkEmbeddingDataAndSelectedBoundaryArcOnFace
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryClosedWalkEmbeddingDataAndSelectedBoundaryArcOnFace G) :
    AdmitsPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometryAndSelectedBoundaryArcOnFace G := by
  rcases hG with ⟨emb, geom, harc⟩
  refine ⟨emb, geom.toPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry, ?_⟩
  intro f
  simpa
    [PlanarBoundaryClosedWalkEmbeddingData.toPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry,
      PlanarBoundaryClosedWalkEmbeddingData.toPlanarBoundaryFaceBoundaryRunGeometry,
      PlanarBoundaryClosedWalkEmbeddingData.toPlanarBoundaryCyclicOrderedFaceEmbeddingData,
      PlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry.toPlanarBoundaryFaceBoundaryRunGeometry]
    using harc f

theorem
    admitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData_of_admitsPlanarBoundaryClosedWalkEmbeddingDataAndSelectedBoundaryArcOnFace
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryClosedWalkEmbeddingDataAndSelectedBoundaryArcOnFace G) :
    AdmitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData G := by
  rcases hG with ⟨emb, geom, harc⟩
  exact ⟨emb, ⟨geom.toPlanarBoundaryCyclicOrderedFaceArcEmbeddingData harc⟩⟩

theorem
    admitsPlanarBoundarySelectedBoundaryArcGeometry_of_admitsPlanarBoundaryClosedWalkEmbeddingDataAndSelectedBoundaryArcOnFace
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryClosedWalkEmbeddingDataAndSelectedBoundaryArcOnFace G) :
    AdmitsPlanarBoundarySelectedBoundaryArcGeometry G := by
  exact
    admitsPlanarBoundarySelectedBoundaryArcGeometry_of_admitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData
      (admitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData_of_admitsPlanarBoundaryClosedWalkEmbeddingDataAndSelectedBoundaryArcOnFace
        hG)

theorem admitsPlanarBoundaryOrderedFaceArcEmbeddingData_of_admitsPlanarBoundarySelectedBoundaryArcGeometry
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundarySelectedBoundaryArcGeometry G) :
    AdmitsPlanarBoundaryOrderedFaceArcEmbeddingData G := by
  rcases hG with ⟨emb, ⟨geom⟩⟩
  exact ⟨emb, ⟨geom.toPlanarBoundaryOrderedFaceArcEmbeddingData⟩⟩

theorem admitsPlanarBoundaryOrderedFaceArcEmbeddingData_iff_admitsPlanarBoundarySelectedBoundaryArcGeometry
    {G : SimpleGraph V} :
    AdmitsPlanarBoundaryOrderedFaceArcEmbeddingData G ↔
      AdmitsPlanarBoundarySelectedBoundaryArcGeometry G := by
  constructor
  · exact admitsPlanarBoundarySelectedBoundaryArcGeometry_of_admitsPlanarBoundaryOrderedFaceArcEmbeddingData
  · exact admitsPlanarBoundaryOrderedFaceArcEmbeddingData_of_admitsPlanarBoundarySelectedBoundaryArcGeometry

theorem
    admitsPlanarBoundaryOrderedFaceArcEmbeddingData_of_admitsPlanarBoundaryFaceBoundaryRunGeometryAndSelectedBoundaryArcOnFace
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryFaceBoundaryRunGeometryAndSelectedBoundaryArcOnFace G) :
    AdmitsPlanarBoundaryOrderedFaceArcEmbeddingData G := by
  rcases hG with ⟨emb, geom, harc⟩
  exact ⟨emb, ⟨geom.toPlanarBoundaryOrderedFaceArcEmbeddingData harc⟩⟩

theorem
    admitsPlanarBoundaryOrderedFaceArcEmbeddingData_iff_admitsPlanarBoundaryFaceBoundaryRunGeometryAndSelectedBoundaryArcOnFace
    {G : SimpleGraph V} :
    AdmitsPlanarBoundaryOrderedFaceArcEmbeddingData G ↔
      AdmitsPlanarBoundaryFaceBoundaryRunGeometryAndSelectedBoundaryArcOnFace G := by
  constructor
  · exact
      admitsPlanarBoundaryFaceBoundaryRunGeometryAndSelectedBoundaryArcOnFace_of_admitsPlanarBoundaryOrderedFaceArcEmbeddingData
  · exact
      admitsPlanarBoundaryOrderedFaceArcEmbeddingData_of_admitsPlanarBoundaryFaceBoundaryRunGeometryAndSelectedBoundaryArcOnFace

theorem admitsPlanarBoundarySelectedBoundaryRunOnFace_of_admitsPlanarBoundaryOrderedFaceArcEmbeddingData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryOrderedFaceArcEmbeddingData G) :
    AdmitsPlanarBoundarySelectedBoundaryRunOnFace G := by
  exact
    admitsPlanarBoundarySelectedBoundaryRunOnFace_of_admitsPlanarBoundarySelectedBoundaryArcGeometry
      (admitsPlanarBoundarySelectedBoundaryArcGeometry_of_admitsPlanarBoundaryOrderedFaceArcEmbeddingData
        hG)

theorem admitsPlanarBoundarySelectedBoundaryRunOnFace_of_admitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData G) :
    AdmitsPlanarBoundarySelectedBoundaryRunOnFace G := by
  exact
    admitsPlanarBoundarySelectedBoundaryRunOnFace_of_admitsPlanarBoundarySelectedBoundaryArcGeometry
      (admitsPlanarBoundarySelectedBoundaryArcGeometry_of_admitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData
        hG)

theorem admitsPlanarBoundaryComponentReachableOnFace_of_admitsPlanarBoundaryOrderedFaceArcEmbeddingData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryOrderedFaceArcEmbeddingData G) :
    AdmitsPlanarBoundaryComponentReachableOnFace G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data.boundaryComponentReachableOnFace⟩

theorem admitsPlanarBoundaryComponentReachableOnFace_of_admitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData G) :
    AdmitsPlanarBoundaryComponentReachableOnFace G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data.boundaryComponentReachableOnFace⟩

end Mettapedia.GraphTheory.FourColor
