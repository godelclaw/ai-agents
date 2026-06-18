import Mettapedia.GraphTheory.FourColor.Shells

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- Direct producer-side kernel certificate: an explicit projected-generator family has trivial
selected-boundary-zero pairing kernel once a finite set of controlling coordinates has two
ingredients:

1. vanishing on those coordinates forces vanishing of the whole chain; and
2. every nonzero value on each controlling coordinate is separated by some member of the chosen
   family that is exactly a single-coordinate chain there.

Unlike the older detector-facing theorem, this lands directly on
`LinearMap.ker (planarBoundaryZeroFamilyPairingMap family) = ⊥`, which is the certificate shape a
future verified finite `F₂` checker is expected to output. -/
theorem ker_planarBoundaryZeroFamilyPairingMap_eq_bot_of_singleCoordinateWitnesses
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {colorings : Set (G.EdgeColoring Color)}
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (controlEdges : Finset G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0)
    (hwitness :
      ∀ e ∈ controlEdges, ∀ d : Color, d ≠ 0 →
        ∃ i : κ,
          ∃ c : Color,
            ((family i : projectedColoringGeneratorSubspace emb colorings) : G.edgeSet → Color) =
                Pi.single e c ∧
              colorDot c d ≠ 0) :
    LinearMap.ker (planarBoundaryZeroFamilyPairingMap family) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro z hz
  apply Subtype.ext
  by_contra hzNonzero
  have hcoord : ∃ e ∈ controlEdges, (z : G.edgeSet → Color) e ≠ 0 := by
    by_contra hnone
    apply hzNonzero
    apply hcontrol z.property
    intro e he
    by_contra hze
    exact hnone ⟨e, he, hze⟩
  rcases hcoord with ⟨e, he, hze⟩
  rcases hwitness e he ((z : G.edgeSet → Color) e) hze with ⟨i, c, hfamily, hcdot⟩
  have hmap : planarBoundaryZeroFamilyPairingMap family z = 0 := hz
  have hcoordZero := congrArg (fun f : κ → F2 => f i) hmap
  have hpairZero :
      chainDotBilinForm G.edgeSet (family i : G.edgeSet → Color) (z : G.edgeSet → Color) = 0 := by
    simpa [planarBoundaryZeroFamilyPairingMap] using hcoordZero
  rw [hfamily, chainDotBilinForm_single_left] at hpairZero
  exact hcdot hpairZero

/-- Route form of the same producer-side certificate: explicit coordinate witnesses for a chosen
family already give the full theorem-4.9 synthesis package for the base coloring. -/
theorem theorem49BoundaryRootSynthesis_of_singleCoordinateFamilyWitnesses
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (controlEdges : Finset G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0)
    (hwitness :
      ∀ e ∈ controlEdges, ∀ d : Color, d ≠ 0 →
        ∃ i : κ,
          ∃ c : Color,
            ((family i : projectedColoringGeneratorSubspace emb colorings) : G.edgeSet → Color) =
                Pi.single e c ∧
              colorDot c d ≠ 0) :
    Theorem49BoundaryRootSynthesis emb C₀ :=
  theorem49BoundaryRootSynthesis_of_familyPairingKerEqBot emb C₀ colorings hsubset family
    (ker_planarBoundaryZeroFamilyPairingMap_eq_bot_of_singleCoordinateWitnesses
      family controlEdges hcontrol hwitness)

/-- Bundle the same explicit coordinate certificate directly as a closed-walk family-kernel shell.
This is the first non-legacy shell-facing producer surface for the finite `F₂` lane. -/
def ClosedWalkNeighborhoodPairingKernelShell.of_singleCoordinateWitnesses
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    (shell : ClosedWalkExactShell emb)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure shell.tait.coloring)
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (controlEdges : Finset G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0)
    (hwitness :
      ∀ e ∈ controlEdges, ∀ d : Color, d ≠ 0 →
        ∃ i : κ,
          ∃ c : Color,
            ((family i : projectedColoringGeneratorSubspace emb colorings) : G.edgeSet → Color) =
                Pi.single e c ∧
              colorDot c d ≠ 0) :
    ClosedWalkNeighborhoodPairingKernelShell emb where
  exactShell := shell
  colorings := colorings
  subset_closure := hsubset
  κ := κ
  family := family
  pairingKernel_eq_bot :=
    ker_planarBoundaryZeroFamilyPairingMap_eq_bot_of_singleCoordinateWitnesses
      family controlEdges hcontrol hwitness

/-- Successor-cycle version of the same shell-facing producer. -/
def SuccessorCycleNeighborhoodPairingKernelShell.of_singleCoordinateWitnesses
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    (shell : SuccessorCycleExactShell emb)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure shell.tait.coloring)
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (controlEdges : Finset G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0)
    (hwitness :
      ∀ e ∈ controlEdges, ∀ d : Color, d ≠ 0 →
        ∃ i : κ,
          ∃ c : Color,
            ((family i : projectedColoringGeneratorSubspace emb colorings) : G.edgeSet → Color) =
                Pi.single e c ∧
              colorDot c d ≠ 0) :
    SuccessorCycleNeighborhoodPairingKernelShell emb where
  exactShell := shell
  colorings := colorings
  subset_closure := hsubset
  κ := κ
  family := family
  pairingKernel_eq_bot :=
    ker_planarBoundaryZeroFamilyPairingMap_eq_bot_of_singleCoordinateWitnesses
      family controlEdges hcontrol hwitness

end Mettapedia.GraphTheory.FourColor
