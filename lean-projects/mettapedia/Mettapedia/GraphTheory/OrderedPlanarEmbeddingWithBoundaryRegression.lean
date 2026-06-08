import Mettapedia.GraphTheory.OrderedPlanarEmbeddingWithBoundary
import Mathlib.Tactic

namespace Mettapedia.GraphTheory

open SimpleGraph

namespace OrderedPlanarEmbeddingWithBoundaryRegression

/-- A two-edge disconnected graph. This is the smallest graph on which the current
`PlaneEmbeddingWithBoundary` API can present one ambient face whose boundary contains two disjoint
edges, so there is no honest boundary order witnessing consecutive endpoint-sharing. -/
def badGraph : SimpleGraph (Fin 4) :=
  SimpleGraph.fromEdgeSet ({s(0, 1), s(2, 3)} : Set (Sym2 (Fin 4)))

def e01 : badGraph.edgeSet := ⟨s(0, 1), by simp [badGraph]⟩

def e23 : badGraph.edgeSet := ⟨s(2, 3), by simp [badGraph]⟩

theorem e01_ne_e23 : e01 ≠ e23 := by
  intro h
  have := congrArg Subtype.val h
  simp [e01, e23] at this

def badFaces : Finset Unit := {()}

def badFaceBoundary : Unit → Finset badGraph.edgeSet
  | () => {e01, e23}

theorem edge_eq_e01_or_e23 (e : badGraph.edgeSet) : e = e01 ∨ e = e23 := by
  have h : (e.1 = s(0, 1) ∨ e.1 = s(2, 3)) ∧ ¬ e.1.IsDiag := by
    simpa [badGraph] using e.2
  rcases h.1 with h01 | h23
  · left
    exact Subtype.ext h01
  · right
    exact Subtype.ext h23

/-- A boundary-aware embedding satisfying the current API but exposing the exact missing geometric
data: its unique ambient face boundary is the unordered pair of the two disjoint graph edges. -/
def badEmbedding : PlaneEmbeddingWithBoundary badGraph where
  Face := Unit
  faceDecidableEq := inferInstance
  faces := badFaces
  faceBoundary := badFaceBoundary
  edge_mem_faceSupport := by
    intro e
    rcases edge_eq_e01_or_e23 e with rfl | rfl <;>
      exact Finset.mem_biUnion.2 ⟨(), by simp [badFaces], by simp [badFaceBoundary]⟩
  edge_one_or_two_faces := by
    intro e he
    left
    rcases edge_eq_e01_or_e23 e with rfl | rfl <;>
      simp [badFaces, badFaceBoundary]

def onlyFace : {f // f ∈ badEmbedding.faces} := ⟨(), by simp [badEmbedding, badFaces]⟩

theorem not_planarEmbeddingBoundaryEdgeEndpointAdj_e01_e23 :
    ¬ planarEmbeddingBoundaryEdgeEndpointAdj e01 e23 := by
  rintro ⟨_, v, hv01, hv23⟩
  fin_cases v <;> simp [e01, e23] at hv01 hv23

theorem not_planarEmbeddingBoundaryEdgeEndpointAdj_e23_e01 :
    ¬ planarEmbeddingBoundaryEdgeEndpointAdj e23 e01 := by
  rintro ⟨_, v, hv23, hv01⟩
  fin_cases v <;> simp [e01, e23] at hv01 hv23

theorem faceBoundaryOrder_eq_pair_or_rev
    (data : PlaneEmbeddingWithBoundary.OrderedFaceBoundaryData badEmbedding) :
    data.faceBoundaryOrder onlyFace = [e01, e23] ∨
      data.faceBoundaryOrder onlyFace = [e23, e01] := by
  generalize hrun : data.faceBoundaryOrder onlyFace = run
  have hm01 : e01 ∈ run := by
    simpa [hrun] using
      (data.hmem onlyFace e01).2 (by simp [badEmbedding, badFaceBoundary, e01])
  have hm23 : e23 ∈ run := by
    simpa [hrun] using
      (data.hmem onlyFace e23).2 (by simp [badEmbedding, badFaceBoundary, e23])
  have hnodup : run.Nodup := by
    simpa [hrun] using data.hnodup onlyFace
  have hsubset : ∀ e ∈ run, e = e01 ∨ e = e23 := by
    intro e he
    exact edge_eq_e01_or_e23 e
  cases run with
  | nil =>
      cases hm01
  | cons a tl =>
      rcases hsubset a (by simp) with rfl | rfl
      · have hm23tl : e23 ∈ tl := by
          simpa [e01_ne_e23, e01_ne_e23.symm] using hm23
        have hnoduptl : tl.Nodup := (List.nodup_cons.mp hnodup).2
        have hnotmem01 : e01 ∉ tl := (List.nodup_cons.mp hnodup).1
        cases tl with
        | nil =>
            cases hm23tl
        | cons b tl' =>
            have hb : b = e23 := by
              rcases hsubset b (by simp) with hb | hb
              · exfalso
                exact hnotmem01 (hb ▸ by simp)
              · exact hb
            subst hb
            have hnotmem23 : e23 ∉ tl' := (List.nodup_cons.mp hnoduptl).1
            have htl' : tl' = [] := by
              apply List.eq_nil_iff_forall_not_mem.2
              intro e he
              rcases hsubset e (by simp [he]) with he01 | he23
              · exact hnotmem01 (he01 ▸ by simp [he])
              · exact hnotmem23 (he23 ▸ he)
            left
            simp [htl']
      · have hm01tl : e01 ∈ tl := by
          simpa [e01_ne_e23, e01_ne_e23.symm] using hm01
        have hnoduptl : tl.Nodup := (List.nodup_cons.mp hnodup).2
        have hnotmem23 : e23 ∉ tl := (List.nodup_cons.mp hnodup).1
        cases tl with
        | nil =>
            cases hm01tl
        | cons b tl' =>
            have hb : b = e01 := by
              rcases hsubset b (by simp) with hb | hb
              · exact hb
              · exfalso
                exact hnotmem23 (hb ▸ by simp)
            subst hb
            have hnotmem01 : e01 ∉ tl' := (List.nodup_cons.mp hnoduptl).1
            have htl' : tl' = [] := by
              apply List.eq_nil_iff_forall_not_mem.2
              intro e he
              rcases hsubset e (by simp [he]) with he01 | he23
              · exact hnotmem01 (he01 ▸ he)
              · exact hnotmem23 (he23 ▸ by simp [he])
            right
            simp [htl']

/-- The unique face of the bad embedding admits no honest ordered boundary run at all. -/
theorem not_nonempty_faceBoundaryEndpointRun_onlyFace :
    ¬ Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryEndpointRun badEmbedding onlyFace) := by
  rintro ⟨run⟩
  have hrun : run.run = [e01, e23] ∨ run.run = [e23, e01] := by
    generalize hmemRun : run.run = l
    have hm01 : e01 ∈ l := by
      simpa [hmemRun] using
        (run.hmem e01).2 (by simp [badEmbedding, badFaceBoundary, e01])
    have hm23 : e23 ∈ l := by
      simpa [hmemRun] using
        (run.hmem e23).2 (by simp [badEmbedding, badFaceBoundary, e23])
    have hnodup : l.Nodup := by
      simpa [hmemRun] using run.hnodup
    have hsubset : ∀ e ∈ l, e = e01 ∨ e = e23 := by
      intro e he
      exact edge_eq_e01_or_e23 e
    cases l with
    | nil =>
        cases hm01
    | cons a tl =>
        rcases hsubset a (by simp) with rfl | rfl
        · have hm23tl : e23 ∈ tl := by
            simpa [e01_ne_e23, e01_ne_e23.symm] using hm23
          have hnoduptl : tl.Nodup := (List.nodup_cons.mp hnodup).2
          have hnotmem01 : e01 ∉ tl := (List.nodup_cons.mp hnodup).1
          cases tl with
          | nil =>
              cases hm23tl
          | cons b tl' =>
              have hb : b = e23 := by
                rcases hsubset b (by simp) with hb | hb
                · exfalso
                  exact hnotmem01 (hb ▸ by simp)
                · exact hb
              subst hb
              have hnotmem23 : e23 ∉ tl' := (List.nodup_cons.mp hnoduptl).1
              have htl' : tl' = [] := by
                apply List.eq_nil_iff_forall_not_mem.2
                intro e he
                rcases hsubset e (by simp [he]) with he01 | he23
                · exact hnotmem01 (he01 ▸ by simp [he])
                · exact hnotmem23 (he23 ▸ he)
              left
              simp [htl']
        · have hm01tl : e01 ∈ tl := by
            simpa [e01_ne_e23, e01_ne_e23.symm] using hm01
          have hnoduptl : tl.Nodup := (List.nodup_cons.mp hnodup).2
          have hnotmem23 : e23 ∉ tl := (List.nodup_cons.mp hnodup).1
          cases tl with
          | nil =>
              cases hm01tl
          | cons b tl' =>
              have hb : b = e01 := by
                rcases hsubset b (by simp) with hb | hb
                · exact hb
                · exfalso
                  exact hnotmem23 (hb ▸ by simp)
              subst hb
              have hnotmem01 : e01 ∉ tl' := (List.nodup_cons.mp hnoduptl).1
              have htl' : tl' = [] := by
                apply List.eq_nil_iff_forall_not_mem.2
                intro e he
                rcases hsubset e (by simp [he]) with he01 | he23
                · exact hnotmem01 (he01 ▸ he)
                · exact hnotmem23 (he23 ▸ by simp [he])
              right
              simp [htl']
  rcases hrun with hrun | hrun
  · have hchain : List.IsChain planarEmbeddingBoundaryEdgeEndpointAdj [e01, e23] := by
      simpa [hrun] using run.hchain
    exact not_planarEmbeddingBoundaryEdgeEndpointAdj_e01_e23 ((List.isChain_pair).1 hchain)
  · have hchain : List.IsChain planarEmbeddingBoundaryEdgeEndpointAdj [e23, e01] := by
      simpa [hrun] using run.hchain
    exact not_planarEmbeddingBoundaryEdgeEndpointAdj_e23_e01 ((List.isChain_pair).1 hchain)

/-- The pure bundled face-boundary run target already fails on the bad embedding. -/
theorem not_nonempty_faceBoundaryRunGeometry_badEmbedding :
    ¬ Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryRunGeometry badEmbedding) := by
  rintro ⟨geom⟩
  exact not_nonempty_faceBoundaryEndpointRun_onlyFace ⟨geom.faceBoundaryRun onlyFace⟩

/-- The stronger ordered face-boundary interface already fails on the bad embedding:
there is no way to equip its unique face boundary with an endpoint-sharing order that lists
exactly the two disjoint edges. -/
theorem not_nonempty_orderedFaceBoundaryData_badEmbedding :
    ¬ Nonempty (PlaneEmbeddingWithBoundary.OrderedFaceBoundaryData badEmbedding) := by
  rintro ⟨data⟩
  exact not_nonempty_faceBoundaryRunGeometry_badEmbedding
    ⟨data.toFaceBoundaryRunGeometry⟩

/-- The proof-relevant linear boundary-step vertex layer already fails on the bad embedding for
the same reason as the edge-only ordered layer: there is no honest endpoint-sharing order at all.
-/
theorem not_nonempty_orderedFaceBoundaryVertexData_badEmbedding :
    ¬ Nonempty (PlaneEmbeddingWithBoundary.OrderedFaceBoundaryVertexData badEmbedding) := by
  rw [← nonempty_orderedFaceBoundaryData_iff_nonempty_orderedFaceBoundaryVertexData]
  exact not_nonempty_orderedFaceBoundaryData_badEmbedding

/-- The explicit ordered boundary-step vertex sequence layer also fails on the bad embedding. -/
theorem not_nonempty_orderedFaceBoundaryVertexSequenceData_badEmbedding :
    ¬ Nonempty (PlaneEmbeddingWithBoundary.OrderedFaceBoundaryVertexSequenceData badEmbedding) := by
  rw [← nonempty_orderedFaceBoundaryData_iff_nonempty_orderedFaceBoundaryVertexSequenceData]
  exact not_nonempty_orderedFaceBoundaryData_badEmbedding

/-- The bad embedding also fails the cyclic ordered source layer. -/
theorem not_nonempty_cyclicOrderedFaceBoundaryData_badEmbedding :
    ¬ Nonempty (PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryData badEmbedding) := by
  intro h
  exact not_nonempty_orderedFaceBoundaryData_badEmbedding
    (nonempty_cyclicOrderedFaceBoundaryData_implies_nonempty_orderedFaceBoundaryData h)

/-- The same bad embedding also fails the bundled cyclic boundary-walk layer. -/
theorem not_nonempty_faceBoundaryClosedRunGeometry_badEmbedding :
    ¬ Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryClosedRunGeometry badEmbedding) := by
  rw [← nonempty_cyclicOrderedFaceBoundaryData_iff_nonempty_faceBoundaryClosedRunGeometry]
  exact not_nonempty_cyclicOrderedFaceBoundaryData_badEmbedding

/-- The same bad embedding also fails the explicit cyclic edge/vertex boundary-walk layer. -/
theorem not_nonempty_faceBoundaryClosedVertexWalkGeometry_badEmbedding :
    ¬ Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryClosedVertexWalkGeometry badEmbedding) := by
  rw [← nonempty_cyclicOrderedFaceBoundaryData_iff_nonempty_faceBoundaryClosedVertexWalkGeometry]
  exact not_nonempty_cyclicOrderedFaceBoundaryData_badEmbedding

/-- The proof-relevant cyclic boundary-step vertex layer also fails on the bad embedding. -/
theorem not_nonempty_cyclicOrderedFaceBoundaryVertexData_badEmbedding :
    ¬ Nonempty (PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryVertexData badEmbedding) := by
  rw [← nonempty_cyclicOrderedFaceBoundaryData_iff_nonempty_cyclicOrderedFaceBoundaryVertexData]
  exact not_nonempty_cyclicOrderedFaceBoundaryData_badEmbedding

/-- The explicit cyclic boundary-step vertex sequence layer also fails on the bad embedding. -/
theorem not_nonempty_cyclicOrderedFaceBoundaryVertexSequenceData_badEmbedding :
    ¬ Nonempty (PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryVertexSequenceData
      badEmbedding) := by
  rw [← nonempty_cyclicOrderedFaceBoundaryData_iff_nonempty_cyclicOrderedFaceBoundaryVertexSequenceData]
  exact not_nonempty_cyclicOrderedFaceBoundaryData_badEmbedding

/-- The obstruction is genuinely at the level of one concrete embedding of the weak API:
the same graph can admit other embeddings, but this one cannot support ordered face-boundary
data. -/
theorem exists_embedding_withoutOrderedFaceBoundaryData :
    ∃ emb : PlaneEmbeddingWithBoundary badGraph,
      ¬ Nonempty (PlaneEmbeddingWithBoundary.OrderedFaceBoundaryData emb) := by
  exact ⟨badEmbedding, not_nonempty_orderedFaceBoundaryData_badEmbedding⟩

theorem exists_embedding_withoutOrderedFaceBoundaryVertexData :
    ∃ emb : PlaneEmbeddingWithBoundary badGraph,
      ¬ Nonempty (PlaneEmbeddingWithBoundary.OrderedFaceBoundaryVertexData emb) := by
  exact ⟨badEmbedding, not_nonempty_orderedFaceBoundaryVertexData_badEmbedding⟩

theorem exists_embedding_withoutOrderedFaceBoundaryVertexSequenceData :
    ∃ emb : PlaneEmbeddingWithBoundary badGraph,
      ¬ Nonempty (PlaneEmbeddingWithBoundary.OrderedFaceBoundaryVertexSequenceData emb) := by
  exact ⟨badEmbedding, not_nonempty_orderedFaceBoundaryVertexSequenceData_badEmbedding⟩

/-- A three-edge path. This is the smallest graph on which the weak embedding API can support a
linear endpoint-sharing face-boundary order while still failing any cyclic closure condition. -/
def pathGraph : SimpleGraph (Fin 4) :=
  SimpleGraph.fromEdgeSet ({s(0, 1), s(1, 2), s(2, 3)} : Set (Sym2 (Fin 4)))

def p01 : pathGraph.edgeSet := ⟨s(0, 1), by simp [pathGraph]⟩

def p12 : pathGraph.edgeSet := ⟨s(1, 2), by simp [pathGraph]⟩

def p23 : pathGraph.edgeSet := ⟨s(2, 3), by simp [pathGraph]⟩

theorem p01_ne_p12 : p01 ≠ p12 := by
  intro h
  have := congrArg Subtype.val h
  simp [p01, p12] at this

theorem p12_ne_p23 : p12 ≠ p23 := by
  intro h
  have := congrArg Subtype.val h
  simp [p12, p23] at this

theorem p01_ne_p23 : p01 ≠ p23 := by
  intro h
  have := congrArg Subtype.val h
  simp [p01, p23] at this

def pathFaces : Finset Unit := {()}

def pathFaceBoundary : Unit → Finset pathGraph.edgeSet
  | () => {p01, p12, p23}

theorem path_edge_eq_p01_or_p12_or_p23 (e : pathGraph.edgeSet) :
    e = p01 ∨ e = p12 ∨ e = p23 := by
  have h :
      (e.1 = s(0, 1) ∨ e.1 = s(1, 2) ∨ e.1 = s(2, 3)) ∧ ¬ e.1.IsDiag := by
    simpa [pathGraph] using e.2
  rcases h.1 with h01 | h12 | h23
  · exact Or.inl <| Subtype.ext h01
  · exact Or.inr <| Or.inl <| Subtype.ext h12
  · exact Or.inr <| Or.inr <| Subtype.ext h23

/-- A boundary-aware embedding whose unique ambient face boundary is the three-edge path
`0-1-2-3`. This admits a linear endpoint-sharing order but no cyclic one. -/
def pathEmbedding : PlaneEmbeddingWithBoundary pathGraph where
  Face := Unit
  faceDecidableEq := inferInstance
  faces := pathFaces
  faceBoundary := pathFaceBoundary
  edge_mem_faceSupport := by
    intro e
    rcases path_edge_eq_p01_or_p12_or_p23 e with rfl | rfl | rfl <;>
      exact Finset.mem_biUnion.2 ⟨(), by simp [pathFaces], by simp [pathFaceBoundary]⟩
  edge_one_or_two_faces := by
    intro e he
    left
    rcases path_edge_eq_p01_or_p12_or_p23 e with rfl | rfl | rfl <;>
      simp [pathFaces, pathFaceBoundary]

def pathOnlyFace : {f // f ∈ pathEmbedding.faces} := ⟨(), by simp [pathEmbedding, pathFaces]⟩

theorem planarEmbeddingBoundaryEdgeEndpointAdj_p01_p12 :
    planarEmbeddingBoundaryEdgeEndpointAdj p01 p12 := by
  refine ⟨p01_ne_p12, 1, ?_, ?_⟩ <;> simp [p01, p12]

theorem planarEmbeddingBoundaryEdgeEndpointAdj_p12_p23 :
    planarEmbeddingBoundaryEdgeEndpointAdj p12 p23 := by
  refine ⟨p12_ne_p23, 2, ?_, ?_⟩ <;> simp [p12, p23]

theorem not_planarEmbeddingBoundaryEdgeEndpointAdj_p01_p23 :
    ¬ planarEmbeddingBoundaryEdgeEndpointAdj p01 p23 := by
  rintro ⟨_, v, hv01, hv23⟩
  fin_cases v <;> simp [p01, p23] at hv01 hv23

theorem not_planarEmbeddingBoundaryEdgeEndpointAdj_p23_p01 :
    ¬ planarEmbeddingBoundaryEdgeEndpointAdj p23 p01 := by
  rintro ⟨_, v, hv23, hv01⟩
  fin_cases v <;> simp [p01, p23] at hv01 hv23

/-- The path embedding admits the obvious linear ordered face-boundary data. -/
def pathOrderedFaceBoundaryData : PlaneEmbeddingWithBoundary.OrderedFaceBoundaryData pathEmbedding where
  faceBoundaryOrder := fun _ => [p01, p12, p23]
  hchain := by
    intro f
    exact (List.isChain_cons_cons).2
      ⟨planarEmbeddingBoundaryEdgeEndpointAdj_p01_p12,
        (List.isChain_pair).2 planarEmbeddingBoundaryEdgeEndpointAdj_p12_p23⟩
  hnodup := by
    intro f
    simp [p01_ne_p12, p12_ne_p23, p01_ne_p23]
  hmem := by
    intro f e
    rcases path_edge_eq_p01_or_p12_or_p23 e with rfl | rfl | rfl <;>
      simp [pathEmbedding, pathFaceBoundary]

theorem path_faceBoundaryOrder_eq_forward_or_reverse
    (data : PlaneEmbeddingWithBoundary.OrderedFaceBoundaryData pathEmbedding) :
    data.faceBoundaryOrder pathOnlyFace = [p01, p12, p23] ∨
      data.faceBoundaryOrder pathOnlyFace = [p23, p12, p01] := by
  generalize hrun : data.faceBoundaryOrder pathOnlyFace = run
  have hm01 : p01 ∈ run := by
    simpa [hrun] using
      (data.hmem pathOnlyFace p01).2 (by simp [pathEmbedding, pathFaceBoundary, p01])
  have hm12 : p12 ∈ run := by
    simpa [hrun] using
      (data.hmem pathOnlyFace p12).2 (by simp [pathEmbedding, pathFaceBoundary, p12])
  have hm23 : p23 ∈ run := by
    simpa [hrun] using
      (data.hmem pathOnlyFace p23).2 (by simp [pathEmbedding, pathFaceBoundary, p23])
  have hnodup : run.Nodup := by
    simpa [hrun] using data.hnodup pathOnlyFace
  have hsubset : ∀ e ∈ run, e = p01 ∨ e = p12 ∨ e = p23 := by
    intro e he
    exact path_edge_eq_p01_or_p12_or_p23 e
  cases run with
  | nil =>
      cases hm01
  | cons a tl =>
      have hnodupRun : (a :: tl).Nodup := hnodup
      rcases hsubset a (by simp) with ha01 | ha12 | ha23
      · subst a
        cases tl with
        | nil =>
            exfalso
            rw [List.mem_singleton] at hm12
            exact p01_ne_p12 hm12.symm
        | cons b tl =>
            have hchainRun :
                List.IsChain planarEmbeddingBoundaryEdgeEndpointAdj (p01 :: b :: tl) := by
              simpa [hrun] using data.hchain pathOnlyFace
            have hab : planarEmbeddingBoundaryEdgeEndpointAdj p01 b :=
              (List.isChain_cons_cons.mp hchainRun).1
            have hnotmem01 : p01 ∉ b :: tl := (List.nodup_cons.mp hnodupRun).1
            have hb : b = p12 := by
              rcases hsubset b (by simp) with hb01 | hb12 | hb23
              · exfalso
                exact hnotmem01 (hb01 ▸ by simp)
              · exact hb12
              · exfalso
                exact not_planarEmbeddingBoundaryEdgeEndpointAdj_p01_p23 (hb23 ▸ hab)
            subst b
            have hm23tl : p23 ∈ tl := by
              rw [List.mem_cons, List.mem_cons] at hm23
              rcases hm23 with h23 | h23
              · exact False.elim (p01_ne_p23 h23.symm)
              rcases h23 with h23 | h23
              · exact False.elim (p12_ne_p23 h23.symm)
              · exact h23
            have hnodupTail : (p12 :: tl).Nodup := (List.nodup_cons.mp hnodupRun).2
            cases tl with
            | nil =>
                cases hm23tl
            | cons c tl' =>
                have hnotmem01' : p01 ∉ p12 :: c :: tl' := hnotmem01
                have hnotmem12 : p12 ∉ c :: tl' := (List.nodup_cons.mp hnodupTail).1
                have hc : c = p23 := by
                  rcases hsubset c (by simp) with hc01 | hc12 | hc23
                  · exfalso
                    exact hnotmem01' (hc01 ▸ by simp)
                  · exfalso
                    exact hnotmem12 (hc12 ▸ by simp)
                  · exact hc23
                subst c
                have hnodupTail' : (p23 :: tl').Nodup := (List.nodup_cons.mp hnodupTail).2
                have hnotmem23 : p23 ∉ tl' := (List.nodup_cons.mp hnodupTail').1
                have htl' : tl' = [] := by
                  apply List.eq_nil_iff_forall_not_mem.2
                  intro e he
                  rcases hsubset e (by simp [he]) with he01 | he12 | he23
                  · exact hnotmem01' (he01 ▸ by simp [he])
                  · exact hnotmem12 (he12 ▸ by simp [he])
                  · exact hnotmem23 (he23 ▸ he)
                left
                simp [htl']
      · subst a
        cases tl with
        | nil =>
            exfalso
            rw [List.mem_singleton] at hm01
            exact p01_ne_p12 hm01
        | cons b tl =>
            have hchainRun :
                List.IsChain planarEmbeddingBoundaryEdgeEndpointAdj (p12 :: b :: tl) := by
              simpa [hrun] using data.hchain pathOnlyFace
            have htail :
                List.IsChain planarEmbeddingBoundaryEdgeEndpointAdj (b :: tl) :=
              (List.isChain_cons_cons.mp hchainRun).2
            have hnotmem12 : p12 ∉ b :: tl := (List.nodup_cons.mp hnodupRun).1
            rcases hsubset b (by simp) with hb01 | hb12 | hb23
            · subst b
              have hm23tl : p23 ∈ tl := by
                rw [List.mem_cons, List.mem_cons] at hm23
                rcases hm23 with h23 | h23
                · exact False.elim (p12_ne_p23 h23.symm)
                rcases h23 with h23 | h23
                · exact False.elim (p01_ne_p23 h23.symm)
                · exact h23
              have hnodupTail : (p01 :: tl).Nodup := (List.nodup_cons.mp hnodupRun).2
              have hnotmem01 : p01 ∉ tl := (List.nodup_cons.mp hnodupTail).1
              cases tl with
              | nil =>
                  cases hm23tl
              | cons c tl' =>
                  have hchainTail :
                      List.IsChain planarEmbeddingBoundaryEdgeEndpointAdj (p01 :: c :: tl') :=
                    htail
                  have hbc : planarEmbeddingBoundaryEdgeEndpointAdj p01 c :=
                    (List.isChain_cons_cons.mp hchainTail).1
                  have hc : c = p23 := by
                    rcases hsubset c (by simp) with hc01 | hc12 | hc23
                    · exfalso
                      exact hnotmem01 (hc01 ▸ by simp)
                    · exfalso
                      exact hnotmem12 (hc12 ▸ by simp)
                    · exact hc23
                  subst c
                  exact False.elim
                    (not_planarEmbeddingBoundaryEdgeEndpointAdj_p01_p23 hbc)
            · exfalso
              exact hnotmem12 (hb12 ▸ by simp)
            · subst b
              have hm01tl : p01 ∈ tl := by
                rw [List.mem_cons, List.mem_cons] at hm01
                rcases hm01 with h01 | h01
                · exact False.elim (p01_ne_p12 h01)
                rcases h01 with h01 | h01
                · exact False.elim (p01_ne_p23 h01)
                · exact h01
              have hnodupTail : (p23 :: tl).Nodup := (List.nodup_cons.mp hnodupRun).2
              have hnotmem23 : p23 ∉ tl := (List.nodup_cons.mp hnodupTail).1
              cases tl with
              | nil =>
                  cases hm01tl
              | cons c tl' =>
                  have hchainTail :
                      List.IsChain planarEmbeddingBoundaryEdgeEndpointAdj (p23 :: c :: tl') :=
                    htail
                  have hbc : planarEmbeddingBoundaryEdgeEndpointAdj p23 c :=
                    (List.isChain_cons_cons.mp hchainTail).1
                  have hc : c = p01 := by
                    rcases hsubset c (by simp) with hc01 | hc12 | hc23
                    · exact hc01
                    · exfalso
                      exact hnotmem12 (hc12 ▸ by simp)
                    · exfalso
                      exact hnotmem23 (hc23 ▸ by simp)
                  subst c
                  exact False.elim
                    (not_planarEmbeddingBoundaryEdgeEndpointAdj_p23_p01 hbc)
      · subst a
        cases tl with
        | nil =>
            exfalso
            rw [List.mem_singleton] at hm12
            exact p12_ne_p23 hm12
        | cons b tl =>
            have hchainRun :
                List.IsChain planarEmbeddingBoundaryEdgeEndpointAdj (p23 :: b :: tl) := by
              simpa [hrun] using data.hchain pathOnlyFace
            have hab : planarEmbeddingBoundaryEdgeEndpointAdj p23 b :=
              (List.isChain_cons_cons.mp hchainRun).1
            have hnotmem23 : p23 ∉ b :: tl := (List.nodup_cons.mp hnodupRun).1
            have hb : b = p12 := by
              rcases hsubset b (by simp) with hb01 | hb12 | hb23
              · exfalso
                exact not_planarEmbeddingBoundaryEdgeEndpointAdj_p23_p01 (hb01 ▸ hab)
              · exact hb12
              · exfalso
                exact hnotmem23 (hb23 ▸ by simp)
            subst b
            have hm01tl : p01 ∈ tl := by
              rw [List.mem_cons, List.mem_cons] at hm01
              rcases hm01 with h01 | h01
              · exact False.elim (p01_ne_p23 h01)
              rcases h01 with h01 | h01
              · exact False.elim (p01_ne_p12 h01)
              · exact h01
            have hnodupTail : (p12 :: tl).Nodup := (List.nodup_cons.mp hnodupRun).2
            cases tl with
            | nil =>
                cases hm01tl
            | cons c tl' =>
                have hnotmem23' : p23 ∉ p12 :: c :: tl' := hnotmem23
                have hnotmem12 : p12 ∉ c :: tl' := (List.nodup_cons.mp hnodupTail).1
                have hc : c = p01 := by
                  rcases hsubset c (by simp) with hc01 | hc12 | hc23
                  · exact hc01
                  · exfalso
                    exact hnotmem12 (hc12 ▸ by simp)
                  · exfalso
                    exact hnotmem23' (hc23 ▸ by simp)
                subst c
                have hnodupTail' : (p01 :: tl').Nodup := (List.nodup_cons.mp hnodupTail).2
                have hnotmem01 : p01 ∉ tl' := (List.nodup_cons.mp hnodupTail').1
                have htl' : tl' = [] := by
                  apply List.eq_nil_iff_forall_not_mem.2
                  intro e he
                  rcases hsubset e (by simp [he]) with he01 | he12 | he23
                  · exact hnotmem01 (he01 ▸ he)
                  · exact hnotmem12 (he12 ▸ by simp [he])
                  · exact hnotmem23' (he23 ▸ by simp [he])
                right
                simp [htl']

/-- The path embedding does support the weaker linear ordered face-boundary interface. -/
theorem nonempty_orderedFaceBoundaryData_pathEmbedding :
    Nonempty (PlaneEmbeddingWithBoundary.OrderedFaceBoundaryData pathEmbedding) := by
  exact ⟨pathOrderedFaceBoundaryData⟩

/-- The path embedding also supports the proof-relevant linear boundary-step vertex layer. -/
noncomputable def pathOrderedFaceBoundaryVertexData :
    PlaneEmbeddingWithBoundary.OrderedFaceBoundaryVertexData pathEmbedding :=
  pathOrderedFaceBoundaryData.toOrderedFaceBoundaryVertexData

/-- The path embedding also supports the explicit ordered boundary-step vertex sequence layer. -/
noncomputable def pathOrderedFaceBoundaryVertexSequenceData :
    PlaneEmbeddingWithBoundary.OrderedFaceBoundaryVertexSequenceData pathEmbedding :=
  pathOrderedFaceBoundaryData.toOrderedFaceBoundaryVertexSequenceData

theorem nonempty_orderedFaceBoundaryVertexData_pathEmbedding :
    Nonempty (PlaneEmbeddingWithBoundary.OrderedFaceBoundaryVertexData pathEmbedding) := by
  exact ⟨pathOrderedFaceBoundaryVertexData⟩

theorem nonempty_orderedFaceBoundaryVertexSequenceData_pathEmbedding :
    Nonempty (PlaneEmbeddingWithBoundary.OrderedFaceBoundaryVertexSequenceData pathEmbedding) := by
  exact ⟨pathOrderedFaceBoundaryVertexSequenceData⟩

/-- But the same embedding still fails the cyclic strengthening: whichever linear order of the
three path edges is chosen, its two endpoints do not share a primal endpoint. -/
theorem not_nonempty_cyclicOrderedFaceBoundaryData_pathEmbedding :
    ¬ Nonempty (PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryData pathEmbedding) := by
  rintro ⟨data⟩
  rcases path_faceBoundaryOrder_eq_forward_or_reverse data.toOrderedFaceBoundaryData with hrun | hrun
  · have hwrap :
        planarEmbeddingBoundaryEdgeEndpointAdj p23 p01 := by
      exact data.hwrap pathOnlyFace p01 p23 (by simp [hrun]) (by simp [hrun])
    exact not_planarEmbeddingBoundaryEdgeEndpointAdj_p23_p01 hwrap
  · have hwrap :
        planarEmbeddingBoundaryEdgeEndpointAdj p01 p23 := by
      exact data.hwrap pathOnlyFace p23 p01 (by simp [hrun]) (by simp [hrun])
    exact not_planarEmbeddingBoundaryEdgeEndpointAdj_p01_p23 hwrap

/-- The proof-relevant cyclic boundary-step vertex layer fails on the path embedding as well,
because the obstruction is already in the cyclic edge order. -/
theorem not_nonempty_cyclicOrderedFaceBoundaryVertexData_pathEmbedding :
    ¬ Nonempty (PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryVertexData pathEmbedding) := by
  rw [← nonempty_cyclicOrderedFaceBoundaryData_iff_nonempty_cyclicOrderedFaceBoundaryVertexData]
  exact not_nonempty_cyclicOrderedFaceBoundaryData_pathEmbedding

/-- The explicit cyclic boundary-step vertex sequence layer fails on the path embedding as well,
because the obstruction is already in the cyclic edge order. -/
theorem not_nonempty_cyclicOrderedFaceBoundaryVertexSequenceData_pathEmbedding :
    ¬ Nonempty (PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryVertexSequenceData
      pathEmbedding) := by
  rw [← nonempty_cyclicOrderedFaceBoundaryData_iff_nonempty_cyclicOrderedFaceBoundaryVertexSequenceData]
  exact not_nonempty_cyclicOrderedFaceBoundaryData_pathEmbedding

/-- The path embedding also fails the bundled cyclic boundary-walk layer. -/
theorem not_nonempty_faceBoundaryClosedRunGeometry_pathEmbedding :
    ¬ Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryClosedRunGeometry pathEmbedding) := by
  rw [← nonempty_cyclicOrderedFaceBoundaryData_iff_nonempty_faceBoundaryClosedRunGeometry]
  exact not_nonempty_cyclicOrderedFaceBoundaryData_pathEmbedding

/-- The path embedding also fails the explicit cyclic edge/vertex boundary-walk layer. -/
theorem not_nonempty_faceBoundaryClosedVertexWalkGeometry_pathEmbedding :
    ¬ Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryClosedVertexWalkGeometry pathEmbedding) := by
  rw [← nonempty_cyclicOrderedFaceBoundaryData_iff_nonempty_faceBoundaryClosedVertexWalkGeometry]
  exact not_nonempty_cyclicOrderedFaceBoundaryData_pathEmbedding

/-- The cyclic strengthening is genuinely stronger than the linear ordered face-boundary
interface on the weak embedding API. -/
theorem exists_embedding_withOrderedFaceBoundaryData_withoutCyclicOrderedFaceBoundaryData :
    ∃ emb : PlaneEmbeddingWithBoundary pathGraph,
      Nonempty (PlaneEmbeddingWithBoundary.OrderedFaceBoundaryData emb) ∧
        ¬ Nonempty (PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryData emb) := by
  exact ⟨pathEmbedding, nonempty_orderedFaceBoundaryData_pathEmbedding,
    not_nonempty_cyclicOrderedFaceBoundaryData_pathEmbedding⟩

theorem exists_embedding_withOrderedFaceBoundaryVertexData_withoutCyclicOrderedFaceBoundaryVertexData :
    ∃ emb : PlaneEmbeddingWithBoundary pathGraph,
      Nonempty (PlaneEmbeddingWithBoundary.OrderedFaceBoundaryVertexData emb) ∧
        ¬ Nonempty (PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryVertexData emb) := by
  exact ⟨pathEmbedding, nonempty_orderedFaceBoundaryVertexData_pathEmbedding,
    not_nonempty_cyclicOrderedFaceBoundaryVertexData_pathEmbedding⟩

theorem
    exists_embedding_withOrderedFaceBoundaryVertexSequenceData_withoutCyclicOrderedFaceBoundaryVertexSequenceData :
    ∃ emb : PlaneEmbeddingWithBoundary pathGraph,
      Nonempty (PlaneEmbeddingWithBoundary.OrderedFaceBoundaryVertexSequenceData emb) ∧
        ¬ Nonempty (PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryVertexSequenceData emb) :=
    by
  exact ⟨pathEmbedding, nonempty_orderedFaceBoundaryVertexSequenceData_pathEmbedding,
    not_nonempty_cyclicOrderedFaceBoundaryVertexSequenceData_pathEmbedding⟩

theorem exists_embedding_withOrderedFaceBoundaryVertexSequenceData_withoutFaceBoundaryClosedVertexWalkGeometry :
    ∃ emb : PlaneEmbeddingWithBoundary pathGraph,
      Nonempty (PlaneEmbeddingWithBoundary.OrderedFaceBoundaryVertexSequenceData emb) ∧
        ¬ Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryClosedVertexWalkGeometry emb) := by
  exact ⟨pathEmbedding, nonempty_orderedFaceBoundaryVertexSequenceData_pathEmbedding,
    not_nonempty_faceBoundaryClosedVertexWalkGeometry_pathEmbedding⟩

/-- The bundled cyclic boundary-walk layer is strictly stronger than the linear run geometry
layer on the weak embedding API. -/
theorem exists_embedding_withFaceBoundaryRunGeometry_withoutFaceBoundaryClosedRunGeometry :
    ∃ emb : PlaneEmbeddingWithBoundary pathGraph,
      Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryRunGeometry emb) ∧
        ¬ Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryClosedRunGeometry emb) := by
  exact
    ⟨pathEmbedding,
      (nonempty_orderedFaceBoundaryData_iff_nonempty_faceBoundaryRunGeometry).1
        nonempty_orderedFaceBoundaryData_pathEmbedding,
      not_nonempty_faceBoundaryClosedRunGeometry_pathEmbedding⟩

end OrderedPlanarEmbeddingWithBoundaryRegression

end Mettapedia.GraphTheory
