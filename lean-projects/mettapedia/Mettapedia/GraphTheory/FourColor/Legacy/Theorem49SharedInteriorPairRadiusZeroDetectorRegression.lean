import Mettapedia.GraphTheory.FourColor.Theorem49ColoringGeneratorFamily
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryAnnulusHonestWitnessRegression
import Mathlib.Tactic

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open Theorem49PlanarBoundaryAnnulusHonestWitnessRegression

namespace Theorem49SharedInteriorPairRadiusZeroDetectorRegression

private noncomputable instance sharedInteriorPairAnnulusGraph_edgeSet_fintype :
    Fintype sharedInteriorPairAnnulusGraph.edgeSet :=
  Fintype.ofFinite _

attribute [simp] sip23_mem_selectedBoundarySupport
attribute [simp] sip30_mem_selectedBoundarySupport
attribute [simp] sip24_mem_selectedBoundarySupport
attribute [simp] sip40_mem_selectedBoundarySupport
attribute [simp] sip56_mem_selectedBoundarySupport
attribute [simp] sip67_mem_selectedBoundarySupport
attribute [simp] sip75_mem_selectedBoundarySupport
attribute [simp] sip01_not_mem_selectedBoundarySupport
attribute [simp] sip12_not_mem_selectedBoundarySupport

private def sharedInteriorPairRadiusZeroColorings :
    Set (sharedInteriorPairAnnulusGraph.EdgeColoring Color) :=
  {sharedInteriorPairTaitEdgeColoring}

private def sharedInteriorPairSelectedBoundaryProjection :
    (sharedInteriorPairAnnulusGraph.edgeSet → Color) →ₗ[F2]
      (sharedInteriorPairAnnulusGraph.edgeSet → Color) :=
  boundaryZeroProjection
    (selectedBoundarySupport
      sharedInteriorPairAnnulusEmbedding.faceBoundary
      sharedInteriorPairAnnulusEmbedding.faces
      sharedInteriorPairAnnulusEmbedding.faces)

private def sharedInteriorPairRadiusZeroWitness :
    sharedInteriorPairAnnulusGraph.edgeSet → Color :=
  Pi.single sip01 red + Pi.single sip12 blue

private def sharedInteriorPairRadiusZeroProjectedGeneratorEnvelope :
    Set (sharedInteriorPairAnnulusGraph.edgeSet → Color) :=
  {x | x = 0 ∨
      x = Pi.single sip01 blue ∨
      x = Pi.single sip12 red ∨
      x = Pi.single sip01 purple + Pi.single sip12 purple}

private theorem polarizedFaceGenerator_symm {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (a b : Color) (faceBoundary : Finset G.edgeSet) :
    polarizedFaceGenerator C a b faceBoundary =
      polarizedFaceGenerator C b a faceBoundary := by
  funext e
  simp [polarizedFaceGenerator, boundaryBicoloredEdges, add_comm, or_left_comm, or_comm,
    or_assoc]

private theorem validColorPair_cases {a b : Color} (hab : ValidColorPair a b) :
    (a = red ∧ b = blue) ∨
      (a = blue ∧ b = red) ∨
      (a = red ∧ b = purple) ∨
      (a = purple ∧ b = red) ∨
      (a = blue ∧ b = purple) ∨
      (a = purple ∧ b = blue) := by
  rcases a with ⟨a₀, a₁⟩
  rcases b with ⟨b₀, b₁⟩
  fin_cases a₀ <;> fin_cases a₁ <;> fin_cases b₀ <;> fin_cases b₁ <;>
    simp [ValidColorPair, red, blue, purple] at hab ⊢

private theorem face0_red_blue_support :
    boundaryBicoloredEdges sharedInteriorPairTaitEdgeColoring red blue
      (sharedInteriorPairAnnulusEmbedding.faceBoundary (0 : SharedInteriorPairFace)) =
      ({sip01, sip12, sip30} : Finset sharedInteriorPairAnnulusGraph.edgeSet) := by
  decide

private theorem face0_red_purple_support :
    boundaryBicoloredEdges sharedInteriorPairTaitEdgeColoring red purple
      (sharedInteriorPairAnnulusEmbedding.faceBoundary (0 : SharedInteriorPairFace)) =
      ({sip01, sip23} : Finset sharedInteriorPairAnnulusGraph.edgeSet) := by
  decide

private theorem face0_blue_purple_support :
    boundaryBicoloredEdges sharedInteriorPairTaitEdgeColoring blue purple
      (sharedInteriorPairAnnulusEmbedding.faceBoundary (0 : SharedInteriorPairFace)) =
      ({sip12, sip23, sip30} : Finset sharedInteriorPairAnnulusGraph.edgeSet) := by
  decide

private theorem face1_red_blue_support :
    boundaryBicoloredEdges sharedInteriorPairTaitEdgeColoring red blue
      (sharedInteriorPairAnnulusEmbedding.faceBoundary (1 : SharedInteriorPairFace)) =
      ({sip01, sip12, sip24} : Finset sharedInteriorPairAnnulusGraph.edgeSet) := by
  decide

private theorem face1_red_purple_support :
    boundaryBicoloredEdges sharedInteriorPairTaitEdgeColoring red purple
      (sharedInteriorPairAnnulusEmbedding.faceBoundary (1 : SharedInteriorPairFace)) =
      ({sip01, sip24, sip40} : Finset sharedInteriorPairAnnulusGraph.edgeSet) := by
  decide

private theorem face1_blue_purple_support :
    boundaryBicoloredEdges sharedInteriorPairTaitEdgeColoring blue purple
      (sharedInteriorPairAnnulusEmbedding.faceBoundary (1 : SharedInteriorPairFace)) =
      ({sip12, sip40} : Finset sharedInteriorPairAnnulusGraph.edgeSet) := by
  decide

private theorem face2_red_blue_support :
    boundaryBicoloredEdges sharedInteriorPairTaitEdgeColoring red blue
      (sharedInteriorPairAnnulusEmbedding.faceBoundary (2 : SharedInteriorPairFace)) =
      ({sip56, sip67} : Finset sharedInteriorPairAnnulusGraph.edgeSet) := by
  decide

private theorem face2_red_purple_support :
    boundaryBicoloredEdges sharedInteriorPairTaitEdgeColoring red purple
      (sharedInteriorPairAnnulusEmbedding.faceBoundary (2 : SharedInteriorPairFace)) =
      ({sip56, sip75} : Finset sharedInteriorPairAnnulusGraph.edgeSet) := by
  decide

private theorem face2_blue_purple_support :
    boundaryBicoloredEdges sharedInteriorPairTaitEdgeColoring blue purple
      (sharedInteriorPairAnnulusEmbedding.faceBoundary (2 : SharedInteriorPairFace)) =
      ({sip67, sip75} : Finset sharedInteriorPairAnnulusGraph.edgeSet) := by
  decide

private theorem projected_face0_red_blue_eq :
    sharedInteriorPairSelectedBoundaryProjection
      (polarizedFaceGenerator sharedInteriorPairTaitEdgeColoring red blue
        (sharedInteriorPairAnnulusEmbedding.faceBoundary (0 : SharedInteriorPairFace))) =
      Pi.single sip01 purple + Pi.single sip12 purple := by
  funext e
  rcases sharedInteriorPairAnnulus_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [sharedInteriorPairSelectedBoundaryProjection, polarizedFaceGenerator,
      face0_red_blue_support, Pi.single, Function.update] <;>
    decide

private theorem projected_face0_red_purple_eq :
    sharedInteriorPairSelectedBoundaryProjection
      (polarizedFaceGenerator sharedInteriorPairTaitEdgeColoring red purple
        (sharedInteriorPairAnnulusEmbedding.faceBoundary (0 : SharedInteriorPairFace))) =
      Pi.single sip01 blue := by
  funext e
  rcases sharedInteriorPairAnnulus_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [sharedInteriorPairSelectedBoundaryProjection, polarizedFaceGenerator,
      face0_red_purple_support, Pi.single, Function.update] <;>
    decide

private theorem projected_face0_blue_purple_eq :
    sharedInteriorPairSelectedBoundaryProjection
      (polarizedFaceGenerator sharedInteriorPairTaitEdgeColoring blue purple
        (sharedInteriorPairAnnulusEmbedding.faceBoundary (0 : SharedInteriorPairFace))) =
      Pi.single sip12 red := by
  funext e
  rcases sharedInteriorPairAnnulus_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [sharedInteriorPairSelectedBoundaryProjection, polarizedFaceGenerator,
      face0_blue_purple_support, Pi.single, Function.update] <;>
    decide

private theorem projected_face1_red_blue_eq :
    sharedInteriorPairSelectedBoundaryProjection
      (polarizedFaceGenerator sharedInteriorPairTaitEdgeColoring red blue
        (sharedInteriorPairAnnulusEmbedding.faceBoundary (1 : SharedInteriorPairFace))) =
      Pi.single sip01 purple + Pi.single sip12 purple := by
  funext e
  rcases sharedInteriorPairAnnulus_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [sharedInteriorPairSelectedBoundaryProjection, polarizedFaceGenerator,
      face1_red_blue_support, Pi.single, Function.update] <;>
    decide

private theorem projected_face1_red_purple_eq :
    sharedInteriorPairSelectedBoundaryProjection
      (polarizedFaceGenerator sharedInteriorPairTaitEdgeColoring red purple
        (sharedInteriorPairAnnulusEmbedding.faceBoundary (1 : SharedInteriorPairFace))) =
      Pi.single sip01 blue := by
  funext e
  rcases sharedInteriorPairAnnulus_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [sharedInteriorPairSelectedBoundaryProjection, polarizedFaceGenerator,
      face1_red_purple_support, Pi.single, Function.update] <;>
    decide

private theorem projected_face1_blue_purple_eq :
    sharedInteriorPairSelectedBoundaryProjection
      (polarizedFaceGenerator sharedInteriorPairTaitEdgeColoring blue purple
        (sharedInteriorPairAnnulusEmbedding.faceBoundary (1 : SharedInteriorPairFace))) =
      Pi.single sip12 red := by
  funext e
  rcases sharedInteriorPairAnnulus_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [sharedInteriorPairSelectedBoundaryProjection, polarizedFaceGenerator,
      face1_blue_purple_support, Pi.single, Function.update] <;>
    decide

private theorem projected_face2_red_blue_eq :
    sharedInteriorPairSelectedBoundaryProjection
      (polarizedFaceGenerator sharedInteriorPairTaitEdgeColoring red blue
        (sharedInteriorPairAnnulusEmbedding.faceBoundary (2 : SharedInteriorPairFace))) =
      0 := by
  funext e
  rcases sharedInteriorPairAnnulus_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [sharedInteriorPairSelectedBoundaryProjection, polarizedFaceGenerator,
      face2_red_blue_support, Function.update] <;>
    decide

private theorem projected_face2_red_purple_eq :
    sharedInteriorPairSelectedBoundaryProjection
      (polarizedFaceGenerator sharedInteriorPairTaitEdgeColoring red purple
        (sharedInteriorPairAnnulusEmbedding.faceBoundary (2 : SharedInteriorPairFace))) =
      0 := by
  funext e
  rcases sharedInteriorPairAnnulus_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [sharedInteriorPairSelectedBoundaryProjection, polarizedFaceGenerator,
      face2_red_purple_support, Function.update] <;>
    decide

private theorem projected_face2_blue_purple_eq :
    sharedInteriorPairSelectedBoundaryProjection
      (polarizedFaceGenerator sharedInteriorPairTaitEdgeColoring blue purple
        (sharedInteriorPairAnnulusEmbedding.faceBoundary (2 : SharedInteriorPairFace))) =
      0 := by
  funext e
  rcases sharedInteriorPairAnnulus_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [sharedInteriorPairSelectedBoundaryProjection, polarizedFaceGenerator,
      face2_blue_purple_support, Function.update] <;>
    decide

private theorem projectedColoringGeneratorFamily_radiusZero_subset_envelope :
    projectedColoringGeneratorFamily sharedInteriorPairAnnulusEmbedding
        sharedInteriorPairRadiusZeroColorings ⊆
      sharedInteriorPairRadiusZeroProjectedGeneratorEnvelope := by
  intro x hx
  rcases (mem_projectedColoringGeneratorFamily_iff
    (emb := sharedInteriorPairAnnulusEmbedding)
    (colorings := sharedInteriorPairRadiusZeroColorings)).1 hx with
    ⟨C, hC, f, a, b, hab, rfl⟩
  have hC' : C = sharedInteriorPairTaitEdgeColoring := by
    simpa [sharedInteriorPairRadiusZeroColorings] using hC
  subst hC'
  change SharedInteriorPairFace at f
  fin_cases f
  · rcases validColorPair_cases hab with
      h | h | h | h | h | h
    all_goals
      rcases h with ⟨rfl, rfl⟩
    · exact Or.inr <| Or.inr <| Or.inr projected_face0_red_blue_eq
    · exact Or.inr <| Or.inr <| Or.inr <| by
        simpa [polarizedFaceGenerator_symm] using projected_face0_red_blue_eq
    · exact Or.inr <| Or.inl projected_face0_red_purple_eq
    · exact Or.inr <| Or.inl <| by
        simpa [polarizedFaceGenerator_symm] using projected_face0_red_purple_eq
    · exact Or.inr <| Or.inr <| Or.inl projected_face0_blue_purple_eq
    · exact Or.inr <| Or.inr <| Or.inl <| by
        simpa [polarizedFaceGenerator_symm] using projected_face0_blue_purple_eq
  · rcases validColorPair_cases hab with
      h | h | h | h | h | h
    all_goals
      rcases h with ⟨rfl, rfl⟩
    · exact Or.inr <| Or.inr <| Or.inr projected_face1_red_blue_eq
    · exact Or.inr <| Or.inr <| Or.inr <| by
        simpa [polarizedFaceGenerator_symm] using projected_face1_red_blue_eq
    · exact Or.inr <| Or.inl projected_face1_red_purple_eq
    · exact Or.inr <| Or.inl <| by
        simpa [polarizedFaceGenerator_symm] using projected_face1_red_purple_eq
    · exact Or.inr <| Or.inr <| Or.inl projected_face1_blue_purple_eq
    · exact Or.inr <| Or.inr <| Or.inl <| by
        simpa [polarizedFaceGenerator_symm] using projected_face1_blue_purple_eq
  · rcases validColorPair_cases hab with
      h | h | h | h | h | h
    all_goals
      rcases h with ⟨rfl, rfl⟩
    · exact Or.inl projected_face2_red_blue_eq
    · exact Or.inl <| by
        simpa [polarizedFaceGenerator_symm] using projected_face2_red_blue_eq
    · exact Or.inl projected_face2_red_purple_eq
    · exact Or.inl <| by
        simpa [polarizedFaceGenerator_symm] using projected_face2_red_purple_eq
    · exact Or.inl projected_face2_blue_purple_eq
    · exact Or.inl <| by
        simpa [polarizedFaceGenerator_symm] using projected_face2_blue_purple_eq

private theorem sharedInteriorPairRadiusZeroWitness_mem_planarBoundaryZeroSubmodule :
    sharedInteriorPairRadiusZeroWitness ∈
      planarBoundaryZeroSubmodule sharedInteriorPairAnnulusEmbedding := by
  intro e he
  have hsip01 : e ≠ sip01 := by
    intro h
    subst h
    exact sip01_not_mem_selectedBoundarySupport he
  have hsip12 : e ≠ sip12 := by
    intro h
    subst h
    exact sip12_not_mem_selectedBoundarySupport he
  simp [sharedInteriorPairRadiusZeroWitness, Pi.single_eq_of_ne hsip01,
    Pi.single_eq_of_ne hsip12]

private theorem sharedInteriorPairRadiusZeroWitness_ne_zero :
    sharedInteriorPairRadiusZeroWitness ≠ 0 := by
  intro hzero
  have hcoord := congrArg (fun z => z sip01) hzero
  have hsip : sip01 ≠ sip12 := by decide
  have hred : red = 0 := by
    simpa [sharedInteriorPairRadiusZeroWitness, Pi.single, Function.update, hsip] using hcoord
  exact red_ne_zero hred

private theorem witness_pairs_zero_with_envelope_blue :
    chainDotBilinForm sharedInteriorPairAnnulusGraph.edgeSet
      (Pi.single sip01 blue) sharedInteriorPairRadiusZeroWitness = 0 := by
  rw [chainDotBilinForm_single_left]
  have hsip : sip01 ≠ sip12 := by decide
  calc
    colorDot blue (sharedInteriorPairRadiusZeroWitness sip01) = colorDot blue red := by
      simp [sharedInteriorPairRadiusZeroWitness, Pi.single, Function.update, hsip]
    _ = 0 := by
      simp [colorDot, red, blue]

private theorem witness_pairs_zero_with_envelope_red :
    chainDotBilinForm sharedInteriorPairAnnulusGraph.edgeSet
      (Pi.single sip12 red) sharedInteriorPairRadiusZeroWitness = 0 := by
  rw [chainDotBilinForm_single_left]
  have hsip : sip12 ≠ sip01 := by decide
  calc
    colorDot red (sharedInteriorPairRadiusZeroWitness sip12) = colorDot red blue := by
      simp [sharedInteriorPairRadiusZeroWitness, Pi.single, Function.update, hsip]
    _ = 0 := by
      simp [colorDot, red, blue]

private theorem witness_pairs_zero_with_envelope_purple :
    chainDotBilinForm sharedInteriorPairAnnulusGraph.edgeSet
      (Pi.single sip01 purple + Pi.single sip12 purple)
      sharedInteriorPairRadiusZeroWitness = 0 := by
  have hsip₀₁ : sip01 ≠ sip12 := by decide
  have hsip₁₂ : sip12 ≠ sip01 := by decide
  calc
    chainDotBilinForm sharedInteriorPairAnnulusGraph.edgeSet
        (Pi.single sip01 purple + Pi.single sip12 purple)
        sharedInteriorPairRadiusZeroWitness =
      chainDotBilinForm sharedInteriorPairAnnulusGraph.edgeSet
          (Pi.single sip01 purple) sharedInteriorPairRadiusZeroWitness +
        chainDotBilinForm sharedInteriorPairAnnulusGraph.edgeSet
          (Pi.single sip12 purple) sharedInteriorPairRadiusZeroWitness := by
            simp
    _ = colorDot purple red + colorDot purple blue := by
          rw [chainDotBilinForm_single_left, chainDotBilinForm_single_left]
          simp [sharedInteriorPairRadiusZeroWitness, Pi.single, Function.update, hsip₀₁, hsip₁₂]
    _ = 0 := by
          simp [colorDot, purple, red, blue]

private theorem sharedInteriorPairRadiusZeroWitness_mem_chainDot_orthogonal_envelopeSpan :
    sharedInteriorPairRadiusZeroWitness ∈
      (chainDotBilinForm sharedInteriorPairAnnulusGraph.edgeSet).orthogonal
        (Submodule.span F2 sharedInteriorPairRadiusZeroProjectedGeneratorEnvelope) := by
  intro q hqspan
  change chainDotBilinForm sharedInteriorPairAnnulusGraph.edgeSet q
      sharedInteriorPairRadiusZeroWitness = 0
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hqspan
  · intro q hq
    rcases hq with rfl | rfl | rfl | rfl
    · simp
    · exact witness_pairs_zero_with_envelope_blue
    · exact witness_pairs_zero_with_envelope_red
    · exact witness_pairs_zero_with_envelope_purple
  · simp
  · intro q₀ q₁ _ _ hq₀ hq₁
    simp [hq₀, hq₁]
  · intro a q _ hq
    simp [hq]

private theorem sharedInteriorPairRadiusZeroWitness_mem_chainDot_orthogonal_projectedColoringGeneratorSubspace :
    sharedInteriorPairRadiusZeroWitness ∈
      (chainDotBilinForm sharedInteriorPairAnnulusGraph.edgeSet).orthogonal
        (projectedColoringGeneratorSubspace sharedInteriorPairAnnulusEmbedding
          sharedInteriorPairRadiusZeroColorings) := by
  have hle :
      projectedColoringGeneratorSubspace sharedInteriorPairAnnulusEmbedding
          sharedInteriorPairRadiusZeroColorings ≤
        Submodule.span F2 sharedInteriorPairRadiusZeroProjectedGeneratorEnvelope := by
    rw [projectedColoringGeneratorSubspace_eq_span_projectedColoringGeneratorFamily]
    exact Submodule.span_mono
      projectedColoringGeneratorFamily_radiusZero_subset_envelope
  intro p hp
  exact
    sharedInteriorPairRadiusZeroWitness_mem_chainDot_orthogonal_envelopeSpan p
      (hle hp)

/-- The shared-interior-pair benchmark certifies the lab's exact radius-0 obstruction: if one
uses only the projected Definition 4.8 generators coming from the single explicit base coloring,
the selected-boundary-zero detector still has a nonzero kernel.  This is why the route needs the
radius-1 explicit Kempe neighborhood rather than the singleton family. -/
theorem not_boundaryZeroProjectedColoringGeneratorDetector_for_explicitTaitColoring_radiusZero :
    ¬ BoundaryZeroProjectedColoringGeneratorDetector
        sharedInteriorPairAnnulusEmbedding
        sharedInteriorPairRadiusZeroColorings := by
  intro hdet
  rcases hdet
      (z := sharedInteriorPairRadiusZeroWitness)
      sharedInteriorPairRadiusZeroWitness_mem_planarBoundaryZeroSubmodule
      sharedInteriorPairRadiusZeroWitness_ne_zero with
    ⟨p, hp, hpair⟩
  exact hpair
    (sharedInteriorPairRadiusZeroWitness_mem_chainDot_orthogonal_projectedColoringGeneratorSubspace
      p hp)

end Theorem49SharedInteriorPairRadiusZeroDetectorRegression

end Mettapedia.GraphTheory.FourColor
