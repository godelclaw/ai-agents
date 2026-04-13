import FourColor.Curriculum.Actual.SevenVertexSixteenCharacterization

namespace FourColor.Curriculum.Actual

section MinimalBridge

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- On the seven-vertex `K₅`-free frontier with no isolated vertices, minimal non-`4`-colorability
already forces vertex-critical non-`4`-colorability.

Source: both notions are canonically realized by the witness `K₂ ⋈ C₅` up to isomorphism. -/
theorem IsMinimalNonColorable.toVertexCritical_of_card_eq_seven_of_cliqueFree_and_forall_exists_adj
    (h : IsMinimalNonColorable G 4) (_hadj : ∀ v : V, ∃ w, G.Adj v w)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    IsVertexCriticalNonColorable G 4 := by
  rcases
      h.nonempty_iso_sevenVertexSixteenWitness_of_card_eq_seven_of_cliqueFree
        hcard hfree with ⟨φ⟩
  exact
    (SimpleGraph.Iso.isVertexCriticalNonColorable_iff (f := φ) (n := 4)).1
      sevenVertexSixteenWitness_isVertexCriticalNonColorable

/-- On the seven-vertex `K₅`-free frontier, edge-minimal non-`4`-colorability already forces
vertex-critical non-`4`-colorability.

Source: isolated vertices are impossible on this frontier, so the older no-isolated-vertices bridge
applies automatically. -/
theorem IsMinimalNonColorable.toVertexCritical_of_card_eq_seven_of_cliqueFree
    (h : IsMinimalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    IsVertexCriticalNonColorable G 4 := by
  rcases
      h.nonempty_iso_sevenVertexSixteenWitness_of_card_eq_seven_of_cliqueFree
        hcard hfree with ⟨φ⟩
  exact
    (SimpleGraph.Iso.isVertexCriticalNonColorable_iff (f := φ) (n := 4)).1
      sevenVertexSixteenWitness_isVertexCriticalNonColorable

/-- On the seven-vertex `K₅`-free frontier, edge-minimal non-`4`-colorability already forces
incidence-critical non-`4`-colorability.

Source: the new minimal-to-vertex bridge followed by the generic vertex-to-incidence implication. -/
theorem IsMinimalNonColorable.toIncidenceCritical_of_card_eq_seven_of_cliqueFree
    (h : IsMinimalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    IsIncidenceCriticalNonColorable G 4 := by
  exact (h.toVertexCritical_of_card_eq_seven_of_cliqueFree hcard hfree).toIncidenceCritical_four

end MinimalBridge

section IncidenceBridge

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- On the seven-vertex `K₅`-free frontier, incidence-critical non-`4`-colorability already
forces vertex-critical non-`4`-colorability.

Source: both notions are canonically realized by the witness `K₂ ⋈ C₅` up to isomorphism. -/
theorem IsIncidenceCriticalNonColorable.toVertexCritical_of_card_eq_seven_of_cliqueFree
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    IsVertexCriticalNonColorable G 4 := by
  rcases h.nonempty_iso_sevenVertexSixteenWitness_of_card_eq_seven_of_cliqueFree hcard hfree with
    ⟨φ⟩
  exact
    (SimpleGraph.Iso.isVertexCriticalNonColorable_iff (f := φ) (n := 4)).1
      sevenVertexSixteenWitness_isVertexCriticalNonColorable

/-- On the seven-vertex `K₅`-free frontier, incidence-critical non-`4`-colorability also forces
minimal non-`4`-colorability.

Source: the unique witness `K₂ ⋈ C₅` is minimal non-`4`-colorable. -/
theorem IsIncidenceCriticalNonColorable.toMinimal_of_card_eq_seven_of_cliqueFree
    (h : IsIncidenceCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    IsMinimalNonColorable G 4 := by
  rcases h.nonempty_iso_sevenVertexSixteenWitness_of_card_eq_seven_of_cliqueFree hcard hfree with
    ⟨φ⟩
  exact
    (SimpleGraph.Iso.isMinimalNonColorable_iff (f := φ) (n := 4)).1
      sevenVertexSixteenWitness_isMinimalNonColorable

end IncidenceBridge

section VertexBridge

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- On the seven-vertex `K₅`-free frontier, vertex-critical non-`4`-colorability already forces
minimal non-`4`-colorability.

Source: both notions are canonically realized by the witness `K₂ ⋈ C₅` up to isomorphism. -/
theorem IsVertexCriticalNonColorable.toMinimal_of_card_eq_seven_of_cliqueFree
    (h : IsVertexCriticalNonColorable G 4)
    (hcard : Fintype.card V = 7) (hfree : G.CliqueFree 5) :
    IsMinimalNonColorable G 4 := by
  rcases h.nonempty_iso_sevenVertexSixteenWitness_of_card_eq_seven_of_cliqueFree hcard hfree with
    ⟨φ⟩
  exact
    (SimpleGraph.Iso.isMinimalNonColorable_iff (f := φ) (n := 4)).1
      sevenVertexSixteenWitness_isMinimalNonColorable

end VertexBridge

section Equivalences

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- On seven vertices under `K₅`-freeness, vertex-critical and incidence-critical non-`4`-colorable
graphs coincide.

Source: incidence-critical graphs are forced to the unique witness class, which is vertex-critical;
the reverse implication is generic. -/
theorem cliqueFree_vertexCritical_iff_incidenceCritical_of_card_eq_seven
    (hcard : Fintype.card V = 7) :
    (G.CliqueFree 5 ∧ IsVertexCriticalNonColorable G 4) ↔
      (G.CliqueFree 5 ∧ IsIncidenceCriticalNonColorable G 4) := by
  constructor
  · rintro ⟨hfree, hvert⟩
    exact ⟨hfree, hvert.toIncidenceCritical_four⟩
  · rintro ⟨hfree, hinc⟩
    exact ⟨hfree, hinc.toVertexCritical_of_card_eq_seven_of_cliqueFree hcard hfree⟩

/-- On seven vertices under `K₅`-freeness, the no-isolated-vertices minimal branch coincides with
the vertex-critical branch.

Source: both branches collapse to the unique witness `K₂ ⋈ C₅`. -/
theorem cliqueFree_minimal_with_forall_exists_adj_iff_vertexCritical_of_card_eq_seven
    (hcard : Fintype.card V = 7) :
    (G.CliqueFree 5 ∧ IsMinimalNonColorable G 4 ∧ (∀ v : V, ∃ w, G.Adj v w)) ↔
      (G.CliqueFree 5 ∧ IsVertexCriticalNonColorable G 4) := by
  constructor
  · rintro ⟨hfree, hmin, hadj⟩
    exact
      ⟨hfree, hmin.toVertexCritical_of_card_eq_seven_of_cliqueFree hcard hfree⟩
  · rintro ⟨hfree, hvert⟩
    exact
      ⟨hfree,
        hvert.toMinimal_of_card_eq_seven_of_cliqueFree hcard hfree,
        fun v => hvert.exists_adj v⟩

/-- On seven vertices under `K₅`-freeness, the no-isolated-vertices minimal branch coincides with
the incidence-critical branch.

Source: the forward implication is the generic minimal-to-incidence bridge; the reverse implication
uses the unique witness realization. -/
theorem cliqueFree_minimal_with_forall_exists_adj_iff_incidenceCritical_of_card_eq_seven
    (hcard : Fintype.card V = 7) :
    (G.CliqueFree 5 ∧ IsMinimalNonColorable G 4 ∧ (∀ v : V, ∃ w, G.Adj v w)) ↔
      (G.CliqueFree 5 ∧ IsIncidenceCriticalNonColorable G 4) := by
  constructor
  · rintro ⟨hfree, hmin, hadj⟩
    exact ⟨hfree, hmin.toIncidenceCritical hadj⟩
  · rintro ⟨hfree, hinc⟩
    exact
      ⟨hfree,
        hinc.toMinimal_of_card_eq_seven_of_cliqueFree hcard hfree,
        fun v =>
          (hinc.toVertexCritical_of_card_eq_seven_of_cliqueFree hcard hfree).exists_adj v⟩

/-- On seven vertices under `K₅`-freeness, minimal non-`4`-colorability coincides with the
vertex-critical branch.

Source: the support-reduction theorem removes the extra no-isolated-vertices hypothesis from the
older equivalence. -/
theorem cliqueFree_minimal_iff_vertexCritical_of_card_eq_seven
    (hcard : Fintype.card V = 7) :
    (G.CliqueFree 5 ∧ IsMinimalNonColorable G 4) ↔
      (G.CliqueFree 5 ∧ IsVertexCriticalNonColorable G 4) := by
  constructor
  · rintro ⟨hfree, hmin⟩
    exact ⟨hfree, hmin.toVertexCritical_of_card_eq_seven_of_cliqueFree hcard hfree⟩
  · rintro ⟨hfree, hvert⟩
    exact ⟨hfree, hvert.toMinimal_of_card_eq_seven_of_cliqueFree hcard hfree⟩

/-- On seven vertices under `K₅`-freeness, minimal non-`4`-colorability coincides with the
incidence-critical branch.

Source: combine the new minimal-to-vertex bridge with the already settled
vertex/incidence equivalence. -/
theorem cliqueFree_minimal_iff_incidenceCritical_of_card_eq_seven
    (hcard : Fintype.card V = 7) :
    (G.CliqueFree 5 ∧ IsMinimalNonColorable G 4) ↔
      (G.CliqueFree 5 ∧ IsIncidenceCriticalNonColorable G 4) := by
  constructor
  · rintro ⟨hfree, hmin⟩
    exact ⟨hfree, hmin.toIncidenceCritical_of_card_eq_seven_of_cliqueFree hcard hfree⟩
  · rintro ⟨hfree, hinc⟩
    exact ⟨hfree, hinc.toMinimal_of_card_eq_seven_of_cliqueFree hcard hfree⟩

end Equivalences

end FourColor.Curriculum.Actual
