import Mettapedia.GraphTheory.FourColor.Theorem49PositiveGeometricSource
import Mettapedia.GraphTheory.FourColor.Legacy.Theorem49PlanarBoundaryAnnulusWheelWitnessRegression

/-!
# Regression checks for positive geometric source packages

The wheel-with-inner-triangle benchmark has a Tait coloring and a nonempty purified carrier, but
its fixed embedding cannot inhabit the current canonical-choice or one-collar positive geometry
packages.  These theorems keep the constructive target honest: nonempty carrier alone is not the
missing geometric source.
-/

namespace Mettapedia.GraphTheory.FourColor

open Theorem49PlanarBoundaryAnnulusWheelWitnessRegression

/-- On the wheel benchmark's fixed embedding, the closed-walk canonical package fails because
every annulus boundary split blocks canonical witness choice. -/
theorem not_theorem49ClosedWalkCanonicalPositiveGeometryOn_wheelWithInnerTriangle :
    ¬ Theorem49ClosedWalkCanonicalPositiveGeometryOn wheelWithInnerTriangleEmbedding := by
  rintro ⟨source, hchoice, _hCarrier⟩
  exact
    not_nonempty_planarBoundaryCanonicalWitnessChoice_wheelWithInnerTriangle
      source.toPlanarBoundaryAnnulusBoundaryData hchoice

/-- On the wheel benchmark's fixed embedding, the closed-walk one-collar package fails because no
one-collar annulus collar geometry exists. -/
theorem not_theorem49ClosedWalkOneCollarPositiveGeometryOn_wheelWithInnerTriangle :
    ¬ Theorem49ClosedWalkOneCollarPositiveGeometryOn wheelWithInnerTriangleEmbedding := by
  rintro ⟨_source, collar, hnum, _hboundary, _hCarrier⟩
  exact
    not_exists_oneCollar_planarBoundaryAnnulusCollarGeometry_wheelWithInnerTriangle
      ⟨collar, hnum⟩

/-- The same fixed-embedding canonical-choice obstruction blocks the route-facing
successor-cycle package as well. -/
theorem not_theorem49SuccessorCycleCanonicalPositiveGeometryOn_wheelWithInnerTriangle :
    ¬ Theorem49SuccessorCycleCanonicalPositiveGeometryOn wheelWithInnerTriangleEmbedding := by
  rintro ⟨boundaryData, _dartCycles, _hselected, hchoice, _hCarrier⟩
  exact
    not_nonempty_planarBoundaryCanonicalWitnessChoice_wheelWithInnerTriangle
      boundaryData.toPlanarBoundaryAnnulusBoundaryData hchoice

/-- The fixed-embedding absence of one-collar geometry blocks the route-facing successor-cycle
one-collar package. -/
theorem not_theorem49SuccessorCycleOneCollarPositiveGeometryOn_wheelWithInnerTriangle :
    ¬ Theorem49SuccessorCycleOneCollarPositiveGeometryOn wheelWithInnerTriangleEmbedding := by
  rintro ⟨_boundaryData, _dartCycles, collar, _hselected, hnum, _hboundary, _hCarrier⟩
  exact
    not_exists_oneCollar_planarBoundaryAnnulusCollarGeometry_wheelWithInnerTriangle
      ⟨collar, hnum⟩

/-- The wheel benchmark pinpoints the current missing field: it has a Tait coloring and a
nonempty purified carrier, but none of the fixed-embedding positive geometry packages currently
available for the route. -/
theorem wheelWithInnerTriangle_tait_nonempty_carrier_without_positiveGeometricSourcePackageOn :
    IsTaitEdgeColoring wheelWithInnerTriangleGraph
        wheelWithInnerTriangleTaitEdgeColoring ∧
      (selectedBoundaryInteriorEdgeEndpointVertices
        wheelWithInnerTriangleEmbedding).Nonempty ∧
      ¬ Theorem49ClosedWalkCanonicalPositiveGeometryOn wheelWithInnerTriangleEmbedding ∧
      ¬ Theorem49ClosedWalkOneCollarPositiveGeometryOn wheelWithInnerTriangleEmbedding ∧
      ¬ Theorem49SuccessorCycleCanonicalPositiveGeometryOn wheelWithInnerTriangleEmbedding ∧
      ¬ Theorem49SuccessorCycleOneCollarPositiveGeometryOn wheelWithInnerTriangleEmbedding := by
  exact
    ⟨wheelWithInnerTriangleTaitEdgeColoring_isTait,
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle,
      not_theorem49ClosedWalkCanonicalPositiveGeometryOn_wheelWithInnerTriangle,
      not_theorem49ClosedWalkOneCollarPositiveGeometryOn_wheelWithInnerTriangle,
      not_theorem49SuccessorCycleCanonicalPositiveGeometryOn_wheelWithInnerTriangle,
      not_theorem49SuccessorCycleOneCollarPositiveGeometryOn_wheelWithInnerTriangle⟩

end Mettapedia.GraphTheory.FourColor
