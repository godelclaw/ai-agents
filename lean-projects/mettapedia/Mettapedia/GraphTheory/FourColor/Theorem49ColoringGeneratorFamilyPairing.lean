import Mettapedia.GraphTheory.FourColor.Theorem49ColoringGeneratorFamilyDetector

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- The concrete pairing map from the full selected-boundary-zero subspace into the dual of an
explicit projected coloring-generator span.  It sends a boundary-zero chain to its chain-dot
functional on that projected span.  This is the route-facing linear-algebra surface behind future
Lean-side finite `F₂` certificates for explicit Kempe neighborhoods. -/
noncomputable def planarBoundaryZeroProjectedColoringPairingMap
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (colorings : Set (G.EdgeColoring Color)) :
    planarBoundaryZeroSubmodule emb →ₗ[F2]
      (projectedColoringGeneratorSubspace emb colorings →ₗ[F2] F2) where
  toFun z :=
    { toFun := fun p =>
        chainDotBilinForm G.edgeSet (p : G.edgeSet → Color) (z : G.edgeSet → Color)
      map_add' := by
        intro p q
        change
          chainDotBilinForm G.edgeSet
              ((p + q : projectedColoringGeneratorSubspace emb colorings) : G.edgeSet → Color)
              (z : G.edgeSet → Color) =
            chainDotBilinForm G.edgeSet (p : G.edgeSet → Color) (z : G.edgeSet → Color) +
              chainDotBilinForm G.edgeSet (q : G.edgeSet → Color) (z : G.edgeSet → Color)
        exact congrArg (fun f : (G.edgeSet → Color) →ₗ[F2] F2 =>
            f (z : G.edgeSet → Color))
          ((chainDotBilinForm G.edgeSet).map_add
            (p : G.edgeSet → Color) (q : G.edgeSet → Color))
      map_smul' := by
        intro a p
        change
          chainDotBilinForm G.edgeSet
              ((a • p : projectedColoringGeneratorSubspace emb colorings) : G.edgeSet → Color)
              (z : G.edgeSet → Color) =
            a • chainDotBilinForm G.edgeSet (p : G.edgeSet → Color) (z : G.edgeSet → Color)
        exact congrArg (fun f : (G.edgeSet → Color) →ₗ[F2] F2 =>
            f (z : G.edgeSet → Color))
          ((chainDotBilinForm G.edgeSet).map_smul a (p : G.edgeSet → Color)) }
  map_add' := by
    intro z w
    ext p
    change
      chainDotBilinForm G.edgeSet (p : G.edgeSet → Color)
          ((z + w : planarBoundaryZeroSubmodule emb) : G.edgeSet → Color) =
        chainDotBilinForm G.edgeSet (p : G.edgeSet → Color) (z : G.edgeSet → Color) +
          chainDotBilinForm G.edgeSet (p : G.edgeSet → Color) (w : G.edgeSet → Color)
    simpa using
      ((chainDotBilinForm G.edgeSet (p : G.edgeSet → Color)).map_add
        (z : G.edgeSet → Color) (w : G.edgeSet → Color))
  map_smul' := by
    intro a z
    ext p
    change
      chainDotBilinForm G.edgeSet (p : G.edgeSet → Color)
          ((a • z : planarBoundaryZeroSubmodule emb) : G.edgeSet → Color) =
        a • chainDotBilinForm G.edgeSet (p : G.edgeSet → Color) (z : G.edgeSet → Color)
    exact
      ((chainDotBilinForm G.edgeSet (p : G.edgeSet → Color)).map_smul a
        (z : G.edgeSet → Color))

/-- The explicit-family detector forces the concrete selected-boundary-zero pairing map to have
trivial kernel. -/
theorem ker_planarBoundaryZeroProjectedColoringPairingMap_eq_bot_of_detector
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {colorings : Set (G.EdgeColoring Color)}
    (hdet : BoundaryZeroProjectedColoringGeneratorDetector emb colorings) :
    LinearMap.ker (planarBoundaryZeroProjectedColoringPairingMap emb colorings) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro z hz
  apply Subtype.ext
  by_contra hzNonzero
  rcases hdet z.property hzNonzero with ⟨p, hp, hpair⟩
  let p' : projectedColoringGeneratorSubspace emb colorings := ⟨p, hp⟩
  have hmap : planarBoundaryZeroProjectedColoringPairingMap emb colorings z = 0 := hz
  have hcoord := congrArg
    (fun f : projectedColoringGeneratorSubspace emb colorings →ₗ[F2] F2 => f p') hmap
  exact hpair (by simpa [planarBoundaryZeroProjectedColoringPairingMap, p'] using hcoord)

/-- Conversely, trivial kernel of the concrete selected-boundary-zero pairing map already gives
the full explicit-family detector property. -/
theorem detector_of_ker_planarBoundaryZeroProjectedColoringPairingMap_eq_bot
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {colorings : Set (G.EdgeColoring Color)}
    (hker :
      LinearMap.ker (planarBoundaryZeroProjectedColoringPairingMap emb colorings) = ⊥) :
    BoundaryZeroProjectedColoringGeneratorDetector emb colorings := by
  intro z hzBoundary hzNonzero
  by_contra hnone
  let z' : planarBoundaryZeroSubmodule emb := ⟨z, hzBoundary⟩
  have hzker :
      z' ∈ LinearMap.ker (planarBoundaryZeroProjectedColoringPairingMap emb colorings) := by
    change planarBoundaryZeroProjectedColoringPairingMap emb colorings z' = 0
    ext p
    by_contra hpair
    exact hnone ⟨p, p.property, hpair⟩
  have hzbot : z' ∈ (⊥ : Submodule F2 (planarBoundaryZeroSubmodule emb)) := by
    simpa [hker] using hzker
  have hzzero' : z' = 0 := by simpa using hzbot
  have hzzero : z = 0 := by
    change ((z' : planarBoundaryZeroSubmodule emb) : G.edgeSet → Color) = 0
    simpa using congrArg Subtype.val hzzero'
  exact hzNonzero hzzero

/-- Bidirectional form: the explicit-family detector is exactly trivial-kernel injectivity of the
concrete selected-boundary-zero pairing map. -/
theorem detector_iff_ker_planarBoundaryZeroProjectedColoringPairingMap_eq_bot
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {colorings : Set (G.EdgeColoring Color)} :
    BoundaryZeroProjectedColoringGeneratorDetector emb colorings ↔
      LinearMap.ker (planarBoundaryZeroProjectedColoringPairingMap emb colorings) = ⊥ := by
  constructor
  · exact ker_planarBoundaryZeroProjectedColoringPairingMap_eq_bot_of_detector
  · exact detector_of_ker_planarBoundaryZeroProjectedColoringPairingMap_eq_bot

/-- Pair a selected-boundary-zero chain against an explicit indexed family of projected coloring
generators.  This is the more concrete finite-certificate map suggested by the current lab output:
one only needs enough explicit family vectors to separate all nonzero selected-boundary-zero
chains. -/
noncomputable def planarBoundaryZeroFamilyPairingMap
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {colorings : Set (G.EdgeColoring Color)}
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings) :
    planarBoundaryZeroSubmodule emb →ₗ[F2] (κ → F2) where
  toFun z i := chainDotBilinForm G.edgeSet (family i : G.edgeSet → Color) (z : G.edgeSet → Color)
  map_add' := by
    intro z w
    ext i
    change
      chainDotBilinForm G.edgeSet (family i : G.edgeSet → Color)
          ((z + w : planarBoundaryZeroSubmodule emb) : G.edgeSet → Color) =
        chainDotBilinForm G.edgeSet (family i : G.edgeSet → Color) (z : G.edgeSet → Color) +
          chainDotBilinForm G.edgeSet (family i : G.edgeSet → Color) (w : G.edgeSet → Color)
    simpa using
      ((chainDotBilinForm G.edgeSet (family i : G.edgeSet → Color)).map_add
        (z : G.edgeSet → Color) (w : G.edgeSet → Color))
  map_smul' := by
    intro a z
    ext i
    change
      chainDotBilinForm G.edgeSet (family i : G.edgeSet → Color)
          ((a • z : planarBoundaryZeroSubmodule emb) : G.edgeSet → Color) =
        a • chainDotBilinForm G.edgeSet (family i : G.edgeSet → Color) (z : G.edgeSet → Color)
    exact
      ((chainDotBilinForm G.edgeSet (family i : G.edgeSet → Color)).map_smul a
        (z : G.edgeSet → Color))

/-- Trivial kernel of the concrete family-evaluation pairing map already gives the
explicit-family detector property.  This is the most direct kernel-checkable route from a finite
explicit family to the theorem-4.9 detector surface. -/
theorem detector_of_ker_planarBoundaryZeroFamilyPairingMap_eq_bot
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {colorings : Set (G.EdgeColoring Color)}
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (hker : LinearMap.ker (planarBoundaryZeroFamilyPairingMap family) = ⊥) :
    BoundaryZeroProjectedColoringGeneratorDetector emb colorings := by
  intro z hzBoundary hzNonzero
  let z' : planarBoundaryZeroSubmodule emb := ⟨z, hzBoundary⟩
  have hzmapNonzero : planarBoundaryZeroFamilyPairingMap family z' ≠ 0 := by
    intro hzmap
    have hzkerMem : z' ∈ LinearMap.ker (planarBoundaryZeroFamilyPairingMap family) := by
      simpa using hzmap
    have hzbot : z' ∈ (⊥ : Submodule F2 (planarBoundaryZeroSubmodule emb)) := by
      simpa [hker] using hzkerMem
    have hzzero' : z' = 0 := by simpa using hzbot
    have hzzero : z = 0 := by
      change ((z' : planarBoundaryZeroSubmodule emb) : G.edgeSet → Color) = 0
      simpa using congrArg Subtype.val hzzero'
    exact hzNonzero hzzero
  classical
  have hexists : ∃ i, planarBoundaryZeroFamilyPairingMap family z' i ≠ 0 := by
    by_contra hnone
    apply hzmapNonzero
    ext i
    by_contra hi
    exact hnone ⟨i, hi⟩
  rcases hexists with ⟨i, hi⟩
  exact ⟨family i, (family i).property, by simpa [planarBoundaryZeroFamilyPairingMap] using hi⟩

/-- If the indexed family spans the whole projected explicit-family subspace, then the
explicit-family detector forces the concrete family-evaluation pairing map to have trivial
kernel.  This is the converse direction needed when a future finite certificate chooses a
specific spanning witness family rather than the whole projected subspace at once. -/
theorem ker_planarBoundaryZeroFamilyPairingMap_eq_bot_of_detector_of_span_eq_top
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {colorings : Set (G.EdgeColoring Color)}
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (hdet : BoundaryZeroProjectedColoringGeneratorDetector emb colorings)
    (hspan : Submodule.span F2 (Set.range family) = ⊤) :
    LinearMap.ker (planarBoundaryZeroFamilyPairingMap family) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro z hz
  apply Subtype.ext
  by_contra hzNonzero
  rcases hdet z.property hzNonzero with ⟨p, hp, hpair⟩
  let p' : projectedColoringGeneratorSubspace emb colorings := ⟨p, hp⟩
  have hmap : planarBoundaryZeroFamilyPairingMap family z = 0 := hz
  have hzSpanZero :
      ∀ q : projectedColoringGeneratorSubspace emb colorings,
        q ∈ Submodule.span F2 (Set.range family) →
          chainDotBilinForm G.edgeSet (q : G.edgeSet → Color) (z : G.edgeSet → Color) = 0 := by
    intro q hqspan
    refine Submodule.span_induction
      (p := fun q : projectedColoringGeneratorSubspace emb colorings => fun _ =>
        chainDotBilinForm G.edgeSet (q : G.edgeSet → Color) (z : G.edgeSet → Color) = 0)
      (s := Set.range family) ?_ ?_ ?_ ?_ hqspan
    · intro x hx
      rcases hx with ⟨i, rfl⟩
      have hcoord := congrArg (fun f : κ → F2 => f i) hmap
      simpa [planarBoundaryZeroFamilyPairingMap] using hcoord
    · simp
    · intro x y _ _ hx hy
      have hadd := congrArg
        (fun f : (G.edgeSet → Color) →ₗ[F2] F2 => f (z : G.edgeSet → Color))
        ((chainDotBilinForm G.edgeSet).map_add
          (x : G.edgeSet → Color) (y : G.edgeSet → Color))
      simp [hx, hy] at hadd ⊢
    · intro a x _ hx
      have hsmul := congrArg
        (fun f : (G.edgeSet → Color) →ₗ[F2] F2 => f (z : G.edgeSet → Color))
        ((chainDotBilinForm G.edgeSet).map_smul a (x : G.edgeSet → Color))
      simp [hx] at hsmul ⊢
  have hpSpan : p' ∈ Submodule.span F2 (Set.range family) := by
    rw [hspan]
    simp
  exact hpair (by simpa [p'] using hzSpanZero p' hpSpan)

/-- When the indexed family spans the whole projected explicit-family subspace, the
explicit-family detector is exactly trivial-kernel injectivity of the concrete family-evaluation
pairing map. -/
theorem detector_iff_ker_planarBoundaryZeroFamilyPairingMap_eq_bot_of_span_eq_top
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {colorings : Set (G.EdgeColoring Color)}
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (hspan : Submodule.span F2 (Set.range family) = ⊤) :
    BoundaryZeroProjectedColoringGeneratorDetector emb colorings ↔
      LinearMap.ker (planarBoundaryZeroFamilyPairingMap family) = ⊥ := by
  constructor
  · intro hdet
    exact ker_planarBoundaryZeroFamilyPairingMap_eq_bot_of_detector_of_span_eq_top
      family hdet hspan
  · exact detector_of_ker_planarBoundaryZeroFamilyPairingMap_eq_bot family

/-- A left inverse to the concrete family-evaluation pairing map is already enough to prove the
explicit-family detector.  This is the most direct Lean target for future finite `F₂`
elimination/search certificates. -/
theorem detector_of_familyPairing_leftInverse
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {colorings : Set (G.EdgeColoring Color)}
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (L : (κ → F2) →ₗ[F2] planarBoundaryZeroSubmodule emb)
    (hL :
      L.comp (planarBoundaryZeroFamilyPairingMap family) =
        (LinearMap.id : planarBoundaryZeroSubmodule emb →ₗ[F2] planarBoundaryZeroSubmodule emb)) :
    BoundaryZeroProjectedColoringGeneratorDetector emb colorings := by
  have hleft : Function.LeftInverse L (planarBoundaryZeroFamilyPairingMap family) := by
    intro z
    have happly := congrArg
      (fun f : planarBoundaryZeroSubmodule emb →ₗ[F2] planarBoundaryZeroSubmodule emb => f z) hL
    simpa [LinearMap.comp_apply] using happly
  intro z hzBoundary hzNonzero
  by_contra hnone
  let z' : planarBoundaryZeroSubmodule emb := ⟨z, hzBoundary⟩
  have hmapZero : planarBoundaryZeroFamilyPairingMap family z' = 0 := by
    ext i
    by_contra hpair
    exact hnone ⟨family i, (family i).property, hpair⟩
  have hzSubZero : z' = 0 := by
    apply hleft.injective
    simpa using hmapZero
  have hzzero : z = 0 := by
    change ((z' : planarBoundaryZeroSubmodule emb) : G.edgeSet → Color) = 0
    simpa using congrArg Subtype.val hzSubZero
  exact hzNonzero hzzero

/-- Route theorem for future finite `F₂` certificates stated on an explicit family of projected
generators: a left inverse to the family pairing map already yields the full theorem-4.9
synthesis package for the base coloring. -/
theorem theorem49BoundaryRootSynthesis_of_familyPairingLeftInverse
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (L : (κ → F2) →ₗ[F2] planarBoundaryZeroSubmodule emb)
    (hL :
      L.comp (planarBoundaryZeroFamilyPairingMap family) =
        (LinearMap.id : planarBoundaryZeroSubmodule emb →ₗ[F2] planarBoundaryZeroSubmodule emb)) :
    Theorem49BoundaryRootSynthesis emb C₀ :=
  theorem49BoundaryRootSynthesis_of_boundaryZeroProjectedColoringGeneratorDetector
    emb C₀ colorings hsubset (detector_of_familyPairing_leftInverse family L hL)

/-- Route theorem for future finite `F₂` certificates stated directly on the concrete
family-evaluation pairing map: trivial kernel already yields the full theorem-4.9 synthesis
package for the base coloring. -/
theorem theorem49BoundaryRootSynthesis_of_familyPairingKerEqBot
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (hker : LinearMap.ker (planarBoundaryZeroFamilyPairingMap family) = ⊥) :
    Theorem49BoundaryRootSynthesis emb C₀ :=
  theorem49BoundaryRootSynthesis_of_boundaryZeroProjectedColoringGeneratorDetector
    emb C₀ colorings hsubset
    (detector_of_ker_planarBoundaryZeroFamilyPairingMap_eq_bot family hker)

/-- A left inverse for the concrete selected-boundary-zero pairing map is a kernel-checkable
certificate of injectivity.  This is the linear-algebra hook needed to turn future finite `F₂`
elimination outputs into honest Lean detector theorems. -/
theorem ker_planarBoundaryZeroProjectedColoringPairingMap_eq_bot_of_leftInverse
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {colorings : Set (G.EdgeColoring Color)}
    (L :
      (projectedColoringGeneratorSubspace emb colorings →ₗ[F2] F2) →ₗ[F2]
        planarBoundaryZeroSubmodule emb)
    (hL :
      L.comp (planarBoundaryZeroProjectedColoringPairingMap emb colorings) =
        (LinearMap.id : planarBoundaryZeroSubmodule emb →ₗ[F2] planarBoundaryZeroSubmodule emb)) :
    LinearMap.ker (planarBoundaryZeroProjectedColoringPairingMap emb colorings) = ⊥ := by
  have hleft :
      Function.LeftInverse L (planarBoundaryZeroProjectedColoringPairingMap emb colorings) := by
    intro z
    have happly := congrArg
      (fun f : planarBoundaryZeroSubmodule emb →ₗ[F2] planarBoundaryZeroSubmodule emb => f z) hL
    simpa [LinearMap.comp_apply] using happly
  exact (LinearMap.ker_eq_bot).2 hleft.injective

/-- A left inverse to the explicit-family pairing map already yields the explicit-family detector
property. -/
theorem detector_of_leftInverse
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {colorings : Set (G.EdgeColoring Color)}
    (L :
      (projectedColoringGeneratorSubspace emb colorings →ₗ[F2] F2) →ₗ[F2]
        planarBoundaryZeroSubmodule emb)
    (hL :
      L.comp (planarBoundaryZeroProjectedColoringPairingMap emb colorings) =
        (LinearMap.id : planarBoundaryZeroSubmodule emb →ₗ[F2] planarBoundaryZeroSubmodule emb)) :
    BoundaryZeroProjectedColoringGeneratorDetector emb colorings :=
  detector_of_ker_planarBoundaryZeroProjectedColoringPairingMap_eq_bot
    (ker_planarBoundaryZeroProjectedColoringPairingMap_eq_bot_of_leftInverse L hL)

/-- Route theorem for future finite `F₂` certificates: if an explicit coloring family inside the
chosen edge-Kempe closure comes with a left inverse to its concrete selected-boundary-zero pairing
map, then the full theorem-4.9 synthesis package follows for the base coloring. -/
theorem theorem49BoundaryRootSynthesis_of_leftInverse
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (L :
      (projectedColoringGeneratorSubspace emb colorings →ₗ[F2] F2) →ₗ[F2]
        planarBoundaryZeroSubmodule emb)
    (hL :
      L.comp (planarBoundaryZeroProjectedColoringPairingMap emb colorings) =
        (LinearMap.id : planarBoundaryZeroSubmodule emb →ₗ[F2] planarBoundaryZeroSubmodule emb)) :
    Theorem49BoundaryRootSynthesis emb C₀ :=
  theorem49BoundaryRootSynthesis_of_boundaryZeroProjectedColoringGeneratorDetector
    emb C₀ colorings hsubset (detector_of_leftInverse L hL)

/-- Whole-closure special case of the same left-inverse certificate interface. -/
theorem theorem49BoundaryRootSynthesis_of_kempeClosureLeftInverse
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (L :
      (projectedColoringGeneratorSubspace emb (G.EdgeKempeClosure C₀) →ₗ[F2] F2) →ₗ[F2]
        planarBoundaryZeroSubmodule emb)
    (hL :
      L.comp (planarBoundaryZeroProjectedColoringPairingMap emb (G.EdgeKempeClosure C₀)) =
        (LinearMap.id : planarBoundaryZeroSubmodule emb →ₗ[F2] planarBoundaryZeroSubmodule emb)) :
    Theorem49BoundaryRootSynthesis emb C₀ :=
  theorem49BoundaryRootSynthesis_of_leftInverse emb C₀ (G.EdgeKempeClosure C₀)
    (by intro C hC; exact hC) L hL

end Mettapedia.GraphTheory.FourColor
