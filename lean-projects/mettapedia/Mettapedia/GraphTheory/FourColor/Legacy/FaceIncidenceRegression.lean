import Mettapedia.GraphTheory.FourColor.FaceIncidence

namespace Mettapedia.GraphTheory.FourColor

namespace FaceIncidenceRegression

def allFaces : Finset Bool := Finset.univ

def faceBoundary : Bool → Finset (Fin 2) := fun _ => Finset.univ

example (e : Fin 2) : totalIncidenceCount faceBoundary allFaces e = 2 := by
  simp [totalIncidenceCount, allFaces, faceBoundary]

example : (sharedInteriorEdges faceBoundary allFaces false true).card = 2 := by
  simp [sharedInteriorEdges, interiorEdgeSupport, totalIncidenceCount, allFaces, faceBoundary]

example :
    (interiorDualGraph faceBoundary allFaces).Adj
      ⟨false, by simp [allFaces]⟩
      ⟨true, by simp [allFaces]⟩ := by
  refine (interiorDualGraph_adj_iff_sharedInteriorEdges_nonempty faceBoundary allFaces).2 ?_
  refine ⟨by decide, ?_⟩
  refine ⟨0, ?_⟩
  simp [sharedInteriorEdges, interiorEdgeSupport, totalIncidenceCount, allFaces, faceBoundary]

example : ¬ PairwiseUniqueSharedInteriorEdges faceBoundary allFaces := by
  intro hunique
  have hle := hunique false (by simp [allFaces]) true (by simp [allFaces]) (by decide)
  simp [sharedInteriorEdges, interiorEdgeSupport, totalIncidenceCount, allFaces, faceBoundary] at hle

end FaceIncidenceRegression

end Mettapedia.GraphTheory.FourColor
