import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Walks.Subwalks
import Mettapedia.GraphTheory.FourColor.Theorem49CertificateBuilder

namespace Mettapedia.GraphTheory.FourColor

variable {F : Type*}

/-- A chosen shortest walk between two reachable vertices. -/
noncomputable def shortestPathWalk (T : SimpleGraph F) {u v : F}
    (h : T.Reachable u v) : T.Walk u v :=
  Classical.choose h.exists_path_of_dist

theorem shortestPathWalk_isPath (T : SimpleGraph F) {u v : F} (h : T.Reachable u v) :
    (shortestPathWalk T h).IsPath :=
  (Classical.choose_spec h.exists_path_of_dist).1

theorem shortestPathWalk_length (T : SimpleGraph F) {u v : F} (h : T.Reachable u v) :
    (shortestPathWalk T h).length = T.dist u v :=
  (Classical.choose_spec h.exists_path_of_dist).2

/-- The first step of a chosen shortest walk from `u` to `v`, or `none` when `u = v`. -/
noncomputable def firstStepOnShortestPath (T : SimpleGraph F) (u v : F) : Option F :=
  by
    classical
    exact if h : T.Reachable u v then
      let p := shortestPathWalk T h
      if _ : ¬ p.Nil then some p.snd else none
    else none

theorem firstStepOnShortestPath_eq_none_of_eq (T : SimpleGraph F) {u : F}
    : firstStepOnShortestPath T u u = none := by
  classical
  have h : T.Reachable u u := SimpleGraph.Reachable.refl (G := T) u
  unfold firstStepOnShortestPath
  let p := shortestPathWalk T h
  have hp0 : p.length = 0 := by
    simpa [p] using shortestPathWalk_length T h
  have hpnil : p.Nil := (SimpleGraph.Walk.nil_iff_length_eq).2 hp0
  simp [p, hpnil]

theorem firstStepOnShortestPath_spec_of_ne (T : SimpleGraph F) {u v : F}
    (h : T.Reachable u v) (hne : u ≠ v) :
    ∃ w, firstStepOnShortestPath T u v = some w ∧
      T.Adj u w ∧ T.dist w v + 1 = T.dist u v := by
  classical
  let p := shortestPathWalk T h
  have hpLen : p.length = T.dist u v := by
    simpa [p] using shortestPathWalk_length T h
  have hpNotNil : ¬ p.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    simpa [hpLen] using h.pos_dist_of_ne hne
  have htailDist : p.tail.length = T.dist p.snd v := by
    simpa using
      (SimpleGraph.length_eq_dist_of_subwalk (G := T)
        (u := u) (v := v) (u' := p.snd) (v' := v) hpLen
        ((SimpleGraph.Walk.isSubwalk_rfl p).tail))
  refine ⟨p.snd, ?_, p.adj_snd hpNotNil, ?_⟩
  · simp [firstStepOnShortestPath, h, p, hpNotNil]
  · calc
      T.dist p.snd v + 1 = p.tail.length + 1 := by rw [htailDist]
      _ = p.length := p.length_tail_add_one hpNotNil
      _ = T.dist u v := hpLen

/-- The parent map taking each vertex to the first step of a chosen shortest walk toward its
designated root, when that root is reachable. -/
noncomputable def parentTowardsRoot (T : SimpleGraph F) (root : F → F) (u : F) : Option F :=
  firstStepOnShortestPath T u (root u)

theorem parentTowardsRoot_eq_none_of_eq_root (T : SimpleGraph F) (root : F → F) {u : F}
    (hu : u = root u) :
    parentTowardsRoot T root u = none := by
  calc
    parentTowardsRoot T root u = firstStepOnShortestPath T u (root u) := rfl
    _ = firstStepOnShortestPath T u u := by rw [← hu]
    _ = none := firstStepOnShortestPath_eq_none_of_eq (T := T) (u := u)

theorem parentTowardsRoot_spec_of_ne (T : SimpleGraph F) (root : F → F) {u : F}
    (h : T.Reachable u (root u)) (hne : u ≠ root u) :
    ∃ w, parentTowardsRoot T root u = some w ∧
      T.Adj u w ∧ T.dist w (root u) + 1 = T.dist u (root u) := by
  simpa [parentTowardsRoot] using firstStepOnShortestPath_spec_of_ne T h hne

theorem firstStepOnShortestPath_eq_some_of_adj_of_dist
    (T : SimpleGraph F) (hAcyc : T.IsAcyclic) {u v w : F}
    (hadj : T.Adj u w) (hreach : T.Reachable w v)
    (hdist : T.dist w v + 1 = T.dist u v) :
    firstStepOnShortestPath T u v = some w := by
  classical
  let p := shortestPathWalk T (hadj.reachable.trans hreach)
  let q := shortestPathWalk T hreach
  have hpPath : p.IsPath := shortestPathWalk_isPath T (hadj.reachable.trans hreach)
  have hqPath : q.IsPath := shortestPathWalk_isPath T hreach
  have hpLen : p.length = T.dist u v := shortestPathWalk_length T (hadj.reachable.trans hreach)
  have hqLen : q.length = T.dist w v := shortestPathWalk_length T hreach
  have hconsLen : (SimpleGraph.Walk.cons hadj q).length = T.dist u v := by
    simp [hqLen, hdist]
  have hconsPath : (SimpleGraph.Walk.cons hadj q).IsPath := by
    exact (SimpleGraph.Walk.isPath_of_length_eq_dist (p := SimpleGraph.Walk.cons hadj q) hconsLen)
  have hpEq : p = SimpleGraph.Walk.cons hadj q := by
    simpa [p, q] using congrArg Subtype.val
      (hAcyc.path_unique ⟨p, hpPath⟩ ⟨SimpleGraph.Walk.cons hadj q, hconsPath⟩)
  have hpNotNil : ¬ p.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    rw [hpLen, ← hdist]
    exact Nat.succ_pos _
  unfold firstStepOnShortestPath
  simp [hadj.reachable.trans hreach, p, hpEq]

theorem parentTowardsRoot_eq_some_of_adj_of_dist
    (T : SimpleGraph F) (hAcyc : T.IsAcyclic) (root : F → F) {u w : F}
    (hadj : T.Adj u w) (hreach : T.Reachable w (root u))
    (hdist : T.dist w (root u) + 1 = T.dist u (root u)) :
    parentTowardsRoot T root u = some w := by
  simpa [parentTowardsRoot] using
    firstStepOnShortestPath_eq_some_of_adj_of_dist T hAcyc hadj hreach hdist

theorem parentTowardsRoot_eq_some_or_eq_some_of_adj_of_acyclic_root
    (T : SimpleGraph F) (hAcyc : T.IsAcyclic) {u w r : F}
    (hadj : T.Adj u w) (hu : T.Reachable u r) (hw : T.Reachable w r) :
    parentTowardsRoot T (fun _ => r) u = some w ∨
      parentTowardsRoot T (fun _ => r) w = some u := by
  rcases hAcyc.dist_eq_dist_add_one_of_adj_of_reachable r hadj hu.symm with hdist | hdist
  · left
    exact parentTowardsRoot_eq_some_of_adj_of_dist T hAcyc (fun _ => r) hadj hw
      (by simpa [SimpleGraph.dist_comm] using hdist.symm)
  · right
    exact parentTowardsRoot_eq_some_of_adj_of_dist T hAcyc (fun _ => r) hadj.symm hu
      (by simpa [SimpleGraph.dist_comm] using hdist.symm)

theorem parentTowardsRoot_eq_some_of_adj_of_lt_dist_of_acyclic_root
    (T : SimpleGraph F) (hAcyc : T.IsAcyclic) {u w r : F}
    (hadj : T.Adj u w) (hu : T.Reachable u r) (hw : T.Reachable w r)
    (hlt : T.dist u r < T.dist w r) :
    parentTowardsRoot T (fun _ => r) w = some u := by
  rcases parentTowardsRoot_eq_some_or_eq_some_of_adj_of_acyclic_root T hAcyc hadj hu hw with
    huw | hwu
  · by_cases hur : u = r
    · rw [parentTowardsRoot_eq_none_of_eq_root (T := T) (root := fun _ => r) hur] at huw
      simp at huw
    · rcases parentTowardsRoot_spec_of_ne (T := T) (root := fun _ => r) (u := u) hu hur with
        ⟨x, hx, _hadj, hdist⟩
      rw [huw] at hx
      injection hx with hxu
      subst x
      omega
  · exact hwu

theorem eq_of_reachable_of_eq_on_adj (T : SimpleGraph F) {α : Sort*} (label : F → α)
    (hlabel : ∀ ⦃u v : F⦄, T.Adj u v → label u = label v) {u v : F}
    (h : T.Reachable u v) :
    label u = label v := by
  rcases h with ⟨p⟩
  induction p with
  | nil =>
      rfl
  | cons hadj p ih =>
      exact Eq.trans (hlabel hadj) ih

theorem eq_of_adj_of_parent_orientation
    (T : SimpleGraph F) (parentFace : F → Option F) (label : F → α)
    (horient : ∀ ⦃u v : F⦄, T.Adj u v → parentFace v = some u ∨ parentFace u = some v)
    (hparent : ∀ ⦃u v : F⦄, parentFace v = some u → label u = label v)
    {u v : F} (hadj : T.Adj u v) :
    label u = label v := by
  rcases horient hadj with huv | hvu
  · exact hparent huv
  · exact (hparent hvu).symm

/-- A parent map is well founded as soon as parent edges strictly decrease distance to a chosen
root label. This is the correct abstract replacement for the false heuristic that acyclicity plus
parent-edge adjacency alone should imply well-founded peeling. -/
theorem wellFounded_parentRel_of_rootDistance
    (T : SimpleGraph F) (parentFace : F → Option F) (rootFace : F → F)
    (hdist : ∀ {g f : F}, parentFace g = some f →
      T.dist f (rootFace f) < T.dist g (rootFace g)) :
    WellFounded (ParentRel parentFace) := by
  exact wellFounded_parentRel_of_lt_height parentFace (fun f => T.dist f (rootFace f))
    (by
      intro g f hgf
      exact hdist hgf)

/-- The canonical shortest-path parent map toward a reachable root is automatically well founded.
The decreasing invariant is the graph distance to the chosen root. -/
theorem wellFounded_parentRel_parentTowardsRoot
    (T : SimpleGraph F) (rootFace : F → F)
    (hreach : ∀ f : F, T.Reachable f (rootFace f))
    (hrootCompat : ∀ {g f : F}, parentTowardsRoot T rootFace g = some f →
      rootFace f = rootFace g) :
    WellFounded (ParentRel (parentTowardsRoot T rootFace)) := by
  apply wellFounded_parentRel_of_rootDistance T (parentTowardsRoot T rootFace) rootFace
  intro g f hgf
  have hneq : g ≠ rootFace g := by
    intro hgr
    rw [parentTowardsRoot_eq_none_of_eq_root (T := T) (root := rootFace) hgr] at hgf
    simp at hgf
  rcases parentTowardsRoot_spec_of_ne (T := T) (root := rootFace) (u := g) (h := hreach g) hneq with
    ⟨w, hw, _hadj, hdist⟩
  rw [hgf] at hw
  injection hw with hfw
  subst w
  have hdist' : T.dist g (rootFace g) = T.dist f (rootFace f) + 1 := by
    symm
    simpa [hrootCompat hgf] using hdist
  rw [hdist']
  exact Nat.lt_succ_self _

variable {V : Type*} [DecidableEq V] [DecidableEq F]

/-- Every vertex can reach some designated root. -/
def RootSetCovers (T : SimpleGraph F) (roots : Finset F) : Prop :=
  ∀ u, ∃ r, r ∈ roots ∧ T.Reachable u r

/-- Distinct designated roots lie in different reachability components. -/
def RootSetSeparated (T : SimpleGraph F) (roots : Finset F) : Prop :=
  ∀ ⦃r s : F⦄, r ∈ roots → s ∈ roots → T.Reachable r s → r = s

def HasUniqueReachableRoot (T : SimpleGraph F) (roots : Finset F) : Prop :=
  ∀ u, ∃! r, r ∈ roots ∧ T.Reachable u r

omit [DecidableEq F] in
theorem rootSetCovers_congr_reachable {T T' : SimpleGraph F} (roots : Finset F)
    (hEq : T.Reachable = T'.Reachable) :
    RootSetCovers T roots ↔ RootSetCovers T' roots := by
  simp [RootSetCovers, hEq]

omit [DecidableEq F] in
theorem rootSetSeparated_congr_reachable {T T' : SimpleGraph F} (roots : Finset F)
    (hEq : T.Reachable = T'.Reachable) :
    RootSetSeparated T roots ↔ RootSetSeparated T' roots := by
  simp [RootSetSeparated, hEq]

omit [DecidableEq F] in
theorem hasUniqueReachableRoot_congr_reachable {T T' : SimpleGraph F} (roots : Finset F)
    (hEq : T.Reachable = T'.Reachable) :
    HasUniqueReachableRoot T roots ↔ HasUniqueReachableRoot T' roots := by
  simp [HasUniqueReachableRoot, hEq]

omit [DecidableEq F] in
theorem hasUniqueReachableRoot_of_cover_and_separated
    (T : SimpleGraph F) (roots : Finset F)
    (hcover : RootSetCovers T roots) (hsep : RootSetSeparated T roots) :
    HasUniqueReachableRoot T roots := by
  intro u
  rcases hcover u with ⟨r, hrRoots, hur⟩
  refine ⟨r, ⟨hrRoots, hur⟩, ?_⟩
  intro s hs
  exact (hsep (r := r) (s := s) hrRoots hs.1 (hur.symm.trans hs.2)).symm

noncomputable def uniqueReachableRoot
    (T : SimpleGraph F) (roots : Finset F) (hroots : HasUniqueReachableRoot T roots) (u : F) : F :=
  Classical.choose <| ExistsUnique.exists <| hroots u

omit [DecidableEq F] in
theorem uniqueReachableRoot_mem_roots
    (T : SimpleGraph F) (roots : Finset F) (hroots : HasUniqueReachableRoot T roots) (u : F) :
    uniqueReachableRoot T roots hroots u ∈ roots := by
  exact (Classical.choose_spec <| ExistsUnique.exists <| hroots u).1

omit [DecidableEq F] in
theorem reachable_uniqueReachableRoot
    (T : SimpleGraph F) (roots : Finset F) (hroots : HasUniqueReachableRoot T roots) (u : F) :
    T.Reachable u (uniqueReachableRoot T roots hroots u) := by
  exact (Classical.choose_spec <| ExistsUnique.exists <| hroots u).2

omit [DecidableEq F] in
theorem uniqueReachableRoot_eq_of_reachable
    (T : SimpleGraph F) (roots : Finset F) (hroots : HasUniqueReachableRoot T roots)
    {u v : F} (h : T.Reachable u v) :
    uniqueReachableRoot T roots hroots u = uniqueReachableRoot T roots hroots v := by
  apply (hroots u).unique
  · exact ⟨uniqueReachableRoot_mem_roots T roots hroots u, reachable_uniqueReachableRoot T roots hroots u⟩
  · exact ⟨uniqueReachableRoot_mem_roots T roots hroots v,
      h.trans (reachable_uniqueReachableRoot T roots hroots v)⟩

omit [DecidableEq F] in
theorem uniqueReachableRoot_eq_of_adj
    (T : SimpleGraph F) (roots : Finset F) (hroots : HasUniqueReachableRoot T roots)
    {u v : F} (h : T.Adj u v) :
    uniqueReachableRoot T roots hroots u = uniqueReachableRoot T roots hroots v := by
  exact uniqueReachableRoot_eq_of_reachable T roots hroots h.reachable

omit [DecidableEq F] in
theorem parentTowardsRoot_eq_some_of_adj_of_lt_dist_of_componentConstantRoot
    (T : SimpleGraph F) (hAcyc : T.IsAcyclic) (root : F → F) {u w : F}
    (hadj : T.Adj u w) (hu : T.Reachable u (root u)) (hw : T.Reachable w (root w))
    (hroot : root u = root w)
    (hlt : T.dist u (root u) < T.dist w (root w)) :
    parentTowardsRoot T root w = some u := by
  have hw' : T.Reachable w (root u) := by
    simpa [hroot] using hw
  have hlt' : T.dist u (root u) < T.dist w (root u) := by
    simpa [hroot] using hlt
  simpa [parentTowardsRoot, hroot] using
    parentTowardsRoot_eq_some_of_adj_of_lt_dist_of_acyclic_root
      T hAcyc hadj hu hw' hlt'

theorem parentTowardsRoot_some_reachable
    (T : SimpleGraph F) (root : F → F) {u w : F}
    (hparent : parentTowardsRoot T root u = some w) :
    T.Reachable u w := by
  classical
  by_cases hreach : T.Reachable u (root u)
  · by_cases hu : u = root u
    · rw [parentTowardsRoot_eq_none_of_eq_root (T := T) (root := root) hu] at hparent
      simp at hparent
    · rcases parentTowardsRoot_spec_of_ne (T := T) (root := root) hreach hu with
        ⟨w', hw', hadj, _⟩
      rw [hparent] at hw'
      injection hw' with hww'
      subst w'
      exact hadj.reachable
  · unfold parentTowardsRoot firstStepOnShortestPath at hparent
    simp [hreach] at hparent

theorem parentTowardsRoot_some_adj
    (T : SimpleGraph F) (root : F → F) {u w : F}
    (hparent : parentTowardsRoot T root u = some w) :
    T.Adj u w := by
  classical
  by_cases hreach : T.Reachable u (root u)
  · by_cases hu : u = root u
    · rw [parentTowardsRoot_eq_none_of_eq_root (T := T) (root := root) hu] at hparent
      simp at hparent
    · rcases parentTowardsRoot_spec_of_ne (T := T) (root := root) hreach hu with
        ⟨w', hw', hadj, _⟩
      rw [hparent] at hw'
      injection hw' with hww'
      subst w'
      exact hadj
  · unfold parentTowardsRoot firstStepOnShortestPath at hparent
    simp [hreach] at hparent

/-- Root-distance version of the parent-face witness-cover theorem. Instead of carrying an
arbitrary explicit height function or a separate well-foundedness witness, it is enough to know
that the chosen parent map strictly decreases distance to some root label. -/
theorem zero_on_ambientFaceSupport_of_rootDistance_parentFacePeelWitnessCover
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (T : SimpleGraph F) (allFaces peelFaces : Finset F)
    (faceBoundary : F → Finset G.edgeSet)
    (parentFace : F → Option F) (rootFace : F → F) (witnessEdge : F → G.edgeSet)
    (hcover : interiorEdgeSupport faceBoundary allFaces ⊆ peelFaces.image witnessEdge)
    (hwitness : ∀ f ∈ peelFaces, witnessEdge f ∈ faceBoundary f)
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (faceBoundary f).erase (witnessEdge f),
      e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
        ∃ g ∈ peelFaces, parentFace g = some f ∧ witnessEdge g = e)
    (hdist : ∀ {g f : F}, parentFace g = some f →
      T.dist f (rootFace f) < T.dist g (rootFace g))
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport faceBoundary allFaces allFaces, z e = 0)
    (horth : ∀ f ∈ peelFaces,
      ∀ γ, γ ≠ 0 → γ ≠ C (witnessEdge f) →
        chainDot
            (boundaryBicoloredEdges C (C (witnessEdge f)) (C (witnessEdge f) + γ)
              (faceBoundary f))
            z
            (polarizedFaceGenerator C (C (witnessEdge f)) (C (witnessEdge f) + γ)
              (faceBoundary f)) = 0) :
    ∀ e ∈ allFaces.biUnion faceBoundary, z e = 0 := by
  exact zero_on_ambientFaceSupport_of_wellFounded_parentFacePeelWitnessCover
    (C := C) (htait := htait) (z := z)
    (allFaces := allFaces) (peelFaces := peelFaces) (faceBoundary := faceBoundary)
    (parentFace := parentFace) (witnessEdge := witnessEdge)
    (hWF := wellFounded_parentRel_of_rootDistance T parentFace rootFace
      (by
        intro g f hgf
        exact hdist hgf))
    hcover hwitness hchildren hall hzeroBoundary horth

/-- Rooted-reachability form of the current Theorem 4.9 witness-cover argument. The parent map and
height function are synthesized from shortest paths to designated roots: `parentTowardsRoot` gives
the next face on a chosen shortest path, and the height is graph distance to the root. The only
remaining geometric burden is then to supply root choices and the local child-edge ownership
condition in terms of this canonical parent map. -/
noncomputable def boundaryRootedFacePeelCertificate_of_rootedReachable_parentFacePeelWitnessCover
    {G : SimpleGraph V}
    (T : SimpleGraph F) (allFaces peelFaces : Finset F)
    (faceBoundary : F → Finset G.edgeSet)
    (rootFace : F → F) (witnessEdge : F → G.edgeSet)
    (hcover : interiorEdgeSupport faceBoundary allFaces ⊆ peelFaces.image witnessEdge)
    (hreach : ∀ f ∈ peelFaces, T.Reachable f (rootFace f))
    (hrootCompat : ∀ g ∈ peelFaces, ∀ f,
      parentTowardsRoot T rootFace g = some f → rootFace f = rootFace g)
    (hwitness : ∀ f ∈ peelFaces, witnessEdge f ∈ faceBoundary f)
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (faceBoundary f).erase (witnessEdge f),
      e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
        ∃ g ∈ peelFaces, parentTowardsRoot T rootFace g = some f ∧ witnessEdge g = e) :
    BoundaryRootedFacePeelCertificate allFaces faceBoundary :=
  boundaryRootedFacePeelCertificate_of_sortedHeightOrdered_parentFacePeelWitnessCover
    allFaces peelFaces faceBoundary
    (parentTowardsRoot T rootFace) witnessEdge
    (fun f => T.dist f (rootFace f))
    hcover hwitness hchildren
    (by
      intro g hg f hparent
      have hneq : g ≠ rootFace g := by
        intro hgr
        have hnone :=
          parentTowardsRoot_eq_none_of_eq_root (T := T) (root := rootFace)
            (u := g) hgr
        rw [hparent] at hnone
        simp at hnone
      rcases parentTowardsRoot_spec_of_ne (T := T) (root := rootFace)
          (u := g) (h := hreach g hg) hneq with ⟨w, hw, _hadj, hdist⟩
      rw [hparent] at hw
      injection hw with hwf
      subst w
      change T.dist f (rootFace f) < T.dist g (rootFace g)
      rw [hrootCompat g hg f hparent]
      rw [← hdist]
      exact Nat.lt_succ_self _)

/-- Rooted-reachability form of the current Theorem 4.9 witness-cover argument. The parent map and
height function are synthesized from shortest paths to designated roots: `parentTowardsRoot` gives
the next face on a chosen shortest path, and the height is graph distance to the root. The only
remaining geometric burden is then to supply root choices and the local child-edge ownership
condition in terms of this canonical parent map. -/
theorem zero_on_ambientFaceSupport_of_rootedReachable_parentFacePeelWitnessCover
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (T : SimpleGraph F) (allFaces peelFaces : Finset F)
    (faceBoundary : F → Finset G.edgeSet)
    (rootFace : F → F) (witnessEdge : F → G.edgeSet)
    (hcover : interiorEdgeSupport faceBoundary allFaces ⊆ peelFaces.image witnessEdge)
    (hreach : ∀ f ∈ peelFaces, T.Reachable f (rootFace f))
    (hrootCompat : ∀ g ∈ peelFaces, ∀ f,
      parentTowardsRoot T rootFace g = some f → rootFace f = rootFace g)
    (hwitness : ∀ f ∈ peelFaces, witnessEdge f ∈ faceBoundary f)
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (faceBoundary f).erase (witnessEdge f),
      e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
        ∃ g ∈ peelFaces, parentTowardsRoot T rootFace g = some f ∧ witnessEdge g = e)
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport faceBoundary allFaces allFaces, z e = 0)
    (horth : ∀ f ∈ peelFaces,
      ∀ γ, γ ≠ 0 → γ ≠ C (witnessEdge f) →
        chainDot
            (boundaryBicoloredEdges C (C (witnessEdge f)) (C (witnessEdge f) + γ)
              (faceBoundary f))
            z
            (polarizedFaceGenerator C (C (witnessEdge f)) (C (witnessEdge f) + γ)
              (faceBoundary f)) = 0) :
    ∀ e ∈ allFaces.biUnion faceBoundary, z e = 0 := by
  exact zero_on_ambientFaceSupport_of_boundaryRootedFacePeelCertificate
    (C := C) (htait := htait) (z := z)
    (allFaces := allFaces) (faceBoundary := faceBoundary)
    (cert :=
      boundaryRootedFacePeelCertificate_of_rootedReachable_parentFacePeelWitnessCover
        T allFaces peelFaces faceBoundary rootFace witnessEdge
        hcover hreach hrootCompat hwitness hchildren)
    hall hzeroBoundary
    (by
      intro f hf γ hγ0 hγd
      exact horth f
        ((mem_heightOrderedFaceOrder_iff peelFaces (fun f => T.dist f (rootFace f))).1 hf)
        γ hγ0 hγd)

theorem zero_on_ambientFaceSupport_of_componentConstantRootedReachable_parentFacePeelWitnessCover
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (T : SimpleGraph F) (allFaces peelFaces : Finset F)
    (faceBoundary : F → Finset G.edgeSet)
    (rootFace : F → F) (witnessEdge : F → G.edgeSet)
    (hcover : interiorEdgeSupport faceBoundary allFaces ⊆ peelFaces.image witnessEdge)
    (hreach : ∀ f ∈ peelFaces, T.Reachable f (rootFace f))
    (hrootConst : ∀ {f g : F}, T.Reachable f g → rootFace f = rootFace g)
    (hwitness : ∀ f ∈ peelFaces, witnessEdge f ∈ faceBoundary f)
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (faceBoundary f).erase (witnessEdge f),
      e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
        ∃ g ∈ peelFaces, parentTowardsRoot T rootFace g = some f ∧ witnessEdge g = e)
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport faceBoundary allFaces allFaces, z e = 0)
    (horth : ∀ f ∈ peelFaces,
      ∀ γ, γ ≠ 0 → γ ≠ C (witnessEdge f) →
        chainDot
            (boundaryBicoloredEdges C (C (witnessEdge f)) (C (witnessEdge f) + γ)
              (faceBoundary f))
            z
            (polarizedFaceGenerator C (C (witnessEdge f)) (C (witnessEdge f) + γ)
              (faceBoundary f)) = 0) :
    ∀ e ∈ allFaces.biUnion faceBoundary, z e = 0 := by
  exact zero_on_ambientFaceSupport_of_rootedReachable_parentFacePeelWitnessCover
    (C := C) (htait := htait) (z := z) (T := T) (allFaces := allFaces) (peelFaces := peelFaces)
    (faceBoundary := faceBoundary) (rootFace := rootFace) (witnessEdge := witnessEdge)
    hcover hreach
    (by
      intro g hg f hparent
      have hreachGF : T.Reachable g f := parentTowardsRoot_some_reachable T rootFace hparent
      exact (hrootConst hreachGF).symm)
    hwitness hchildren hall hzeroBoundary horth

/-- Acyclic adjacency-and-distance form of the rooted witness-cover theorem. This replaces the
explicit `parentFace` condition by a more geometric local condition: every non-witness edge on a
peeled face is either ambient boundary support or belongs to an adjacent peeled face that lies
strictly farther from the common component root. The directed parent relation is then recovered
canonically by `parentTowardsRoot`. -/
theorem zero_on_ambientFaceSupport_of_componentConstantRootedAdjDistanceWitnessCover
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (T : SimpleGraph F) (allFaces peelFaces : Finset F)
    (faceBoundary : F → Finset G.edgeSet)
    (rootFace : F → F) (witnessEdge : F → G.edgeSet)
    (hAcyc : T.IsAcyclic)
    (hcover : interiorEdgeSupport faceBoundary allFaces ⊆ peelFaces.image witnessEdge)
    (hreach : ∀ f ∈ peelFaces, T.Reachable f (rootFace f))
    (hrootConst : ∀ {f g : F}, T.Reachable f g → rootFace f = rootFace g)
    (hwitness : ∀ f ∈ peelFaces, witnessEdge f ∈ faceBoundary f)
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (faceBoundary f).erase (witnessEdge f),
      e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
        ∃ g ∈ peelFaces, T.Adj f g ∧ witnessEdge g = e ∧
          T.dist f (rootFace f) < T.dist g (rootFace g))
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport faceBoundary allFaces allFaces, z e = 0)
    (horth : ∀ f ∈ peelFaces,
      ∀ γ, γ ≠ 0 → γ ≠ C (witnessEdge f) →
        chainDot
            (boundaryBicoloredEdges C (C (witnessEdge f)) (C (witnessEdge f) + γ)
              (faceBoundary f))
            z
            (polarizedFaceGenerator C (C (witnessEdge f)) (C (witnessEdge f) + γ)
              (faceBoundary f)) = 0) :
    ∀ e ∈ allFaces.biUnion faceBoundary, z e = 0 := by
  exact zero_on_ambientFaceSupport_of_componentConstantRootedReachable_parentFacePeelWitnessCover
    (C := C) (htait := htait) (z := z) (T := T) (allFaces := allFaces) (peelFaces := peelFaces)
    (faceBoundary := faceBoundary) (rootFace := rootFace) (witnessEdge := witnessEdge)
    hcover hreach hrootConst hwitness
    (by
      intro f hf e he
      rcases hchildren f hf e he with hboundary | ⟨g, hg, hadj, hge, hlt⟩
      · exact Or.inl hboundary
      · refine Or.inr ⟨g, hg, ?_, hge⟩
        have hroot : rootFace f = rootFace g := hrootConst hadj.reachable
        exact parentTowardsRoot_eq_some_of_adj_of_lt_dist_of_componentConstantRoot
          T hAcyc rootFace hadj (hreach f hf) (hreach g hg) hroot hlt)
    hall hzeroBoundary horth

/-- Edge-local root invariance version of the acyclic adjacency-distance witness-cover theorem.
It is enough to know that the chosen root label is constant along dual-forest edges; componentwise
root constancy is then derived by transport along reachable walks. -/
theorem zero_on_ambientFaceSupport_of_adjInvariantRootedAdjDistanceWitnessCover
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (T : SimpleGraph F) (allFaces peelFaces : Finset F)
    (faceBoundary : F → Finset G.edgeSet)
    (rootFace : F → F) (witnessEdge : F → G.edgeSet)
    (hAcyc : T.IsAcyclic)
    (hcover : interiorEdgeSupport faceBoundary allFaces ⊆ peelFaces.image witnessEdge)
    (hreach : ∀ f ∈ peelFaces, T.Reachable f (rootFace f))
    (hrootAdj : ∀ ⦃f g : F⦄, T.Adj f g → rootFace f = rootFace g)
    (hwitness : ∀ f ∈ peelFaces, witnessEdge f ∈ faceBoundary f)
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (faceBoundary f).erase (witnessEdge f),
      e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
        ∃ g ∈ peelFaces, T.Adj f g ∧ witnessEdge g = e ∧
          T.dist f (rootFace f) < T.dist g (rootFace g))
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport faceBoundary allFaces allFaces, z e = 0)
    (horth : ∀ f ∈ peelFaces,
      ∀ γ, γ ≠ 0 → γ ≠ C (witnessEdge f) →
        chainDot
            (boundaryBicoloredEdges C (C (witnessEdge f)) (C (witnessEdge f) + γ)
              (faceBoundary f))
            z
            (polarizedFaceGenerator C (C (witnessEdge f)) (C (witnessEdge f) + γ)
              (faceBoundary f)) = 0) :
    ∀ e ∈ allFaces.biUnion faceBoundary, z e = 0 := by
  exact zero_on_ambientFaceSupport_of_componentConstantRootedAdjDistanceWitnessCover
    (C := C) (htait := htait) (z := z) (T := T) (allFaces := allFaces) (peelFaces := peelFaces)
    (faceBoundary := faceBoundary) (rootFace := rootFace) (witnessEdge := witnessEdge)
    hAcyc hcover hreach
    (by
      intro f g hfg
      exact eq_of_reachable_of_eq_on_adj T rootFace (fun {_ _} hab => hrootAdj hab) hfg)
    hwitness hchildren hall hzeroBoundary horth

/-- Reachability-transfer version of the edge-local root-invariance theorem. This removes the
explicit root-set bookkeeping from the current Theorem 4.9 interface: the chosen root face for each
peeled face may be witnessed in any ambient graph `T'` with the same reachability relation as the
acyclic graph `T` that supplies the distance and child-adjacency data. -/
theorem zero_on_ambientFaceSupport_of_adjInvariantRootedAdjDistanceWitnessCover_of_reachableEq
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (T T' : SimpleGraph F) (allFaces peelFaces : Finset F)
    (faceBoundary : F → Finset G.edgeSet)
    (rootFace : F → F) (witnessEdge : F → G.edgeSet)
    (hAcyc : T.IsAcyclic)
    (hreachEq : T.Reachable = T'.Reachable)
    (hcover : interiorEdgeSupport faceBoundary allFaces ⊆ peelFaces.image witnessEdge)
    (hreach : ∀ f ∈ peelFaces, T'.Reachable f (rootFace f))
    (hrootAdj : ∀ ⦃f g : F⦄, T.Adj f g → rootFace f = rootFace g)
    (hwitness : ∀ f ∈ peelFaces, witnessEdge f ∈ faceBoundary f)
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (faceBoundary f).erase (witnessEdge f),
      e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
        ∃ g ∈ peelFaces, T.Adj f g ∧ witnessEdge g = e ∧
          T.dist f (rootFace f) < T.dist g (rootFace g))
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport faceBoundary allFaces allFaces, z e = 0)
    (horth : ∀ f ∈ peelFaces,
      ∀ γ, γ ≠ 0 → γ ≠ C (witnessEdge f) →
        chainDot
            (boundaryBicoloredEdges C (C (witnessEdge f)) (C (witnessEdge f) + γ)
              (faceBoundary f))
            z
            (polarizedFaceGenerator C (C (witnessEdge f)) (C (witnessEdge f) + γ)
              (faceBoundary f)) = 0) :
    ∀ e ∈ allFaces.biUnion faceBoundary, z e = 0 := by
  exact zero_on_ambientFaceSupport_of_adjInvariantRootedAdjDistanceWitnessCover
    (C := C) (htait := htait) (z := z) (T := T) (allFaces := allFaces) (peelFaces := peelFaces)
    (faceBoundary := faceBoundary) (rootFace := rootFace) (witnessEdge := witnessEdge)
    hAcyc hcover
    (by
      intro f hf
      simpa [hreachEq] using hreach f hf)
    hrootAdj hwitness hchildren hall hzeroBoundary horth

/-- Root-set version of the acyclic adjacency-distance witness-cover theorem. A finite set of
designated roots with exactly one reachable root in each connected component determines a canonical
root function `uniqueReachableRoot`; the remaining local hypothesis is then stated only in terms of
adjacency and distance to these canonical roots. -/
theorem zero_on_ambientFaceSupport_of_uniqueReachableRootSetAdjDistanceWitnessCover
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (T : SimpleGraph F) (allFaces peelFaces roots : Finset F)
    (faceBoundary : F → Finset G.edgeSet)
    (witnessEdge : F → G.edgeSet)
    (hAcyc : T.IsAcyclic)
    (hroots : HasUniqueReachableRoot T roots)
    (hcover : interiorEdgeSupport faceBoundary allFaces ⊆ peelFaces.image witnessEdge)
    (hwitness : ∀ f ∈ peelFaces, witnessEdge f ∈ faceBoundary f)
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (faceBoundary f).erase (witnessEdge f),
      e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
        ∃ g ∈ peelFaces, T.Adj f g ∧ witnessEdge g = e ∧
          T.dist f (uniqueReachableRoot T roots hroots f) <
            T.dist g (uniqueReachableRoot T roots hroots g))
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport faceBoundary allFaces allFaces, z e = 0)
    (horth : ∀ f ∈ peelFaces,
      ∀ γ, γ ≠ 0 → γ ≠ C (witnessEdge f) →
        chainDot
            (boundaryBicoloredEdges C (C (witnessEdge f)) (C (witnessEdge f) + γ)
              (faceBoundary f))
            z
            (polarizedFaceGenerator C (C (witnessEdge f)) (C (witnessEdge f) + γ)
              (faceBoundary f)) = 0) :
    ∀ e ∈ allFaces.biUnion faceBoundary, z e = 0 := by
  exact zero_on_ambientFaceSupport_of_adjInvariantRootedAdjDistanceWitnessCover
    (C := C) (htait := htait) (z := z) (T := T) (allFaces := allFaces) (peelFaces := peelFaces)
    (faceBoundary := faceBoundary) (rootFace := uniqueReachableRoot T roots hroots)
    (witnessEdge := witnessEdge) hAcyc hcover
    (by
      intro f hf
      exact reachable_uniqueReachableRoot T roots hroots f)
    (by
      intro f g hfg
      exact uniqueReachableRoot_eq_of_adj T roots hroots hfg)
    hwitness hchildren hall hzeroBoundary horth

/-- Root-cover plus root-separation version of the root-set witness-cover theorem. This is the
most direct interface for an actual rooted forest: every face reaches some designated root, and no
two distinct designated roots lie in the same component. -/
noncomputable def boundaryRootedFacePeelCertificate_of_coverSeparatedRootsAdjDistanceWitnessCover
    {G : SimpleGraph V}
    (T : SimpleGraph F) (allFaces peelFaces roots : Finset F)
    (faceBoundary : F → Finset G.edgeSet)
    (witnessEdge : F → G.edgeSet)
    (hAcyc : T.IsAcyclic)
    (hcoverRoots : RootSetCovers T roots)
    (hsepRoots : RootSetSeparated T roots)
    (hcover : interiorEdgeSupport faceBoundary allFaces ⊆ peelFaces.image witnessEdge)
    (hwitness : ∀ f ∈ peelFaces, witnessEdge f ∈ faceBoundary f)
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (faceBoundary f).erase (witnessEdge f),
      e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
        ∃ g ∈ peelFaces, T.Adj f g ∧ witnessEdge g = e ∧
          T.dist f (uniqueReachableRoot T roots
            (hasUniqueReachableRoot_of_cover_and_separated T roots hcoverRoots hsepRoots) f) <
            T.dist g (uniqueReachableRoot T roots
              (hasUniqueReachableRoot_of_cover_and_separated T roots hcoverRoots hsepRoots) g)) :
    BoundaryRootedFacePeelCertificate allFaces faceBoundary := by
  let hroots : HasUniqueReachableRoot T roots :=
    hasUniqueReachableRoot_of_cover_and_separated T roots hcoverRoots hsepRoots
  let rootFace : F → F := uniqueReachableRoot T roots hroots
  refine boundaryRootedFacePeelCertificate_of_rootedReachable_parentFacePeelWitnessCover
    T allFaces peelFaces faceBoundary rootFace witnessEdge
    hcover
    (by
      intro f hf
      exact reachable_uniqueReachableRoot T roots hroots f)
    (by
      intro g hg f hparent
      exact (uniqueReachableRoot_eq_of_reachable T roots hroots
        (parentTowardsRoot_some_reachable T rootFace hparent)).symm)
    hwitness
    (by
      intro f hf e he
      rcases hchildren f hf e he with hboundary | ⟨g, hg, hadj, hge, hlt⟩
      · exact Or.inl hboundary
      · refine Or.inr ⟨g, hg, ?_, hge⟩
        have hroot : rootFace f = rootFace g :=
          uniqueReachableRoot_eq_of_adj T roots hroots hadj
        exact parentTowardsRoot_eq_some_of_adj_of_lt_dist_of_componentConstantRoot
          T hAcyc rootFace hadj
          (reachable_uniqueReachableRoot T roots hroots f)
          (reachable_uniqueReachableRoot T roots hroots g)
          hroot hlt)

/-- Root-cover plus root-separation version of the root-set witness-cover theorem. This is the
most direct interface for an actual rooted forest: every face reaches some designated root, and no
two distinct designated roots lie in the same component. -/
theorem zero_on_ambientFaceSupport_of_coverSeparatedRootsAdjDistanceWitnessCover
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (T : SimpleGraph F) (allFaces peelFaces roots : Finset F)
    (faceBoundary : F → Finset G.edgeSet)
    (witnessEdge : F → G.edgeSet)
    (hAcyc : T.IsAcyclic)
    (hcoverRoots : RootSetCovers T roots)
    (hsepRoots : RootSetSeparated T roots)
    (hcover : interiorEdgeSupport faceBoundary allFaces ⊆ peelFaces.image witnessEdge)
    (hwitness : ∀ f ∈ peelFaces, witnessEdge f ∈ faceBoundary f)
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (faceBoundary f).erase (witnessEdge f),
      e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
        ∃ g ∈ peelFaces, T.Adj f g ∧ witnessEdge g = e ∧
          T.dist f (uniqueReachableRoot T roots
            (hasUniqueReachableRoot_of_cover_and_separated T roots hcoverRoots hsepRoots) f) <
            T.dist g (uniqueReachableRoot T roots
              (hasUniqueReachableRoot_of_cover_and_separated T roots hcoverRoots hsepRoots) g))
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport faceBoundary allFaces allFaces, z e = 0)
    (horth : ∀ f ∈ peelFaces,
      ∀ γ, γ ≠ 0 → γ ≠ C (witnessEdge f) →
        chainDot
            (boundaryBicoloredEdges C (C (witnessEdge f)) (C (witnessEdge f) + γ)
              (faceBoundary f))
            z
            (polarizedFaceGenerator C (C (witnessEdge f)) (C (witnessEdge f) + γ)
              (faceBoundary f)) = 0) :
    ∀ e ∈ allFaces.biUnion faceBoundary, z e = 0 := by
  let hroots : HasUniqueReachableRoot T roots :=
    hasUniqueReachableRoot_of_cover_and_separated T roots hcoverRoots hsepRoots
  exact zero_on_ambientFaceSupport_of_boundaryRootedFacePeelCertificate
    (C := C) (htait := htait) (z := z)
    (allFaces := allFaces) (faceBoundary := faceBoundary)
    (cert :=
      boundaryRootedFacePeelCertificate_of_coverSeparatedRootsAdjDistanceWitnessCover
        T allFaces peelFaces roots faceBoundary witnessEdge
        hAcyc hcoverRoots hsepRoots hcover hwitness hchildren)
    hall hzeroBoundary
    (by
      intro f hf γ hγ0 hγd
      exact horth f
        ((mem_heightOrderedFaceOrder_iff peelFaces
          (fun f => T.dist f (uniqueReachableRoot T roots hroots f))).1 hf)
        γ hγ0 hγd)

/-- Reachability-transfer version of the cover/separated-root theorem. This matches the output of
Lemma 4.6 directly: if a rooted acyclic graph `T` has the same reachability relation as some
ambient graph `T'`, then root coverage and root separation may be stated on `T'` while the child
orientation and distance hypotheses remain on `T`. -/
noncomputable def
    boundaryRootedFacePeelCertificate_of_coverSeparatedRootsAdjDistanceWitnessCover_of_reachableEq
    {G : SimpleGraph V}
    (T T' : SimpleGraph F) (allFaces peelFaces roots : Finset F)
    (faceBoundary : F → Finset G.edgeSet)
    (witnessEdge : F → G.edgeSet)
    (hAcyc : T.IsAcyclic)
    (hreachEq : T.Reachable = T'.Reachable)
    (hcoverRoots : RootSetCovers T' roots)
    (hsepRoots : RootSetSeparated T' roots)
    (hcover : interiorEdgeSupport faceBoundary allFaces ⊆ peelFaces.image witnessEdge)
    (hwitness : ∀ f ∈ peelFaces, witnessEdge f ∈ faceBoundary f)
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (faceBoundary f).erase (witnessEdge f),
      e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
        ∃ g ∈ peelFaces, T.Adj f g ∧ witnessEdge g = e ∧
          T.dist f (uniqueReachableRoot T roots
            (hasUniqueReachableRoot_of_cover_and_separated T roots
              ((rootSetCovers_congr_reachable roots hreachEq).2 hcoverRoots)
              ((rootSetSeparated_congr_reachable roots hreachEq).2 hsepRoots)) f) <
            T.dist g (uniqueReachableRoot T roots
              (hasUniqueReachableRoot_of_cover_and_separated T roots
                ((rootSetCovers_congr_reachable roots hreachEq).2 hcoverRoots)
                ((rootSetSeparated_congr_reachable roots hreachEq).2 hsepRoots)) g)) :
    BoundaryRootedFacePeelCertificate allFaces faceBoundary :=
  boundaryRootedFacePeelCertificate_of_coverSeparatedRootsAdjDistanceWitnessCover
    T allFaces peelFaces roots faceBoundary witnessEdge hAcyc
    ((rootSetCovers_congr_reachable roots hreachEq).2 hcoverRoots)
    ((rootSetSeparated_congr_reachable roots hreachEq).2 hsepRoots)
    hcover hwitness hchildren

/-- Reachability-transfer version of the cover/separated-root theorem. This matches the output of
Lemma 4.6 directly: if a rooted acyclic graph `T` has the same reachability relation as some
ambient graph `T'`, then root coverage and root separation may be stated on `T'` while the child
orientation and distance hypotheses remain on `T`. -/
theorem zero_on_ambientFaceSupport_of_coverSeparatedRootsAdjDistanceWitnessCover_of_reachableEq
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (T T' : SimpleGraph F) (allFaces peelFaces roots : Finset F)
    (faceBoundary : F → Finset G.edgeSet)
    (witnessEdge : F → G.edgeSet)
    (hAcyc : T.IsAcyclic)
    (hreachEq : T.Reachable = T'.Reachable)
    (hcoverRoots : RootSetCovers T' roots)
    (hsepRoots : RootSetSeparated T' roots)
    (hcover : interiorEdgeSupport faceBoundary allFaces ⊆ peelFaces.image witnessEdge)
    (hwitness : ∀ f ∈ peelFaces, witnessEdge f ∈ faceBoundary f)
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (faceBoundary f).erase (witnessEdge f),
      e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
        ∃ g ∈ peelFaces, T.Adj f g ∧ witnessEdge g = e ∧
          T.dist f (uniqueReachableRoot T roots
            (hasUniqueReachableRoot_of_cover_and_separated T roots
              ((rootSetCovers_congr_reachable roots hreachEq).2 hcoverRoots)
              ((rootSetSeparated_congr_reachable roots hreachEq).2 hsepRoots)) f) <
            T.dist g (uniqueReachableRoot T roots
              (hasUniqueReachableRoot_of_cover_and_separated T roots
                ((rootSetCovers_congr_reachable roots hreachEq).2 hcoverRoots)
                ((rootSetSeparated_congr_reachable roots hreachEq).2 hsepRoots)) g))
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport faceBoundary allFaces allFaces, z e = 0)
    (horth : ∀ f ∈ peelFaces,
      ∀ γ, γ ≠ 0 → γ ≠ C (witnessEdge f) →
        chainDot
            (boundaryBicoloredEdges C (C (witnessEdge f)) (C (witnessEdge f) + γ)
              (faceBoundary f))
            z
            (polarizedFaceGenerator C (C (witnessEdge f)) (C (witnessEdge f) + γ)
              (faceBoundary f)) = 0) :
    ∀ e ∈ allFaces.biUnion faceBoundary, z e = 0 := by
  let hcoverRootsT : RootSetCovers T roots :=
    (rootSetCovers_congr_reachable roots hreachEq).2 hcoverRoots
  let hsepRootsT : RootSetSeparated T roots :=
    (rootSetSeparated_congr_reachable roots hreachEq).2 hsepRoots
  let hroots : HasUniqueReachableRoot T roots :=
    hasUniqueReachableRoot_of_cover_and_separated T roots hcoverRootsT hsepRootsT
  exact zero_on_ambientFaceSupport_of_boundaryRootedFacePeelCertificate
    (C := C) (htait := htait) (z := z)
    (allFaces := allFaces) (faceBoundary := faceBoundary)
    (cert :=
      boundaryRootedFacePeelCertificate_of_coverSeparatedRootsAdjDistanceWitnessCover_of_reachableEq
        T T' allFaces peelFaces roots faceBoundary witnessEdge
        hAcyc hreachEq hcoverRoots hsepRoots hcover hwitness hchildren)
    hall hzeroBoundary
    (by
      intro f hf γ hγ0 hγd
      exact horth f
        ((mem_heightOrderedFaceOrder_iff peelFaces
          (fun f => T.dist f (uniqueReachableRoot T roots hroots f))).1 hf)
        γ hγ0 hγd)

/-- Generic finite collar-layer witness-cover data for the Theorem 4.9 annihilator step. This is
the paper-shaped theorem-layer interface behind the current peeling route: peeled faces are grouped
into finitely many layers, and every non-witness remainder edge points either to the selected
boundary support or to a witness edge in a strictly later layer. -/
structure CollarLayerFacePeelWitnessData {G : SimpleGraph V}
    (allFaces : Finset F) (faceBoundary : F → Finset G.edgeSet) where
  numLayers : ℕ
  layerFaces : Fin numLayers → Finset F
  witnessEdge : F → G.edgeSet
  hdisjoint : ∀ {i j : Fin numLayers}, i ≠ j → Disjoint (layerFaces i) (layerFaces j)
  hcover : interiorEdgeSupport faceBoundary allFaces ⊆
    (Finset.univ.biUnion layerFaces).image witnessEdge
  hwitness : ∀ i f, f ∈ layerFaces i → witnessEdge f ∈ faceBoundary f
  hrest : ∀ i f, f ∈ layerFaces i → ∀ e ∈ (faceBoundary f).erase (witnessEdge f),
    e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
      ∃ j : Fin numLayers, i < j ∧ ∃ g ∈ layerFaces j, witnessEdge g = e

/-- The peeled faces covered by a collar-layer package. -/
def CollarLayerFacePeelWitnessData.peelFaces {G : SimpleGraph V}
    {allFaces : Finset F} {faceBoundary : F → Finset G.edgeSet}
    (data : CollarLayerFacePeelWitnessData allFaces faceBoundary) : Finset F :=
  Finset.univ.biUnion data.layerFaces

theorem CollarLayerFacePeelWitnessData.mem_peelFaces_iff {G : SimpleGraph V}
    {allFaces : Finset F} {faceBoundary : F → Finset G.edgeSet}
    (data : CollarLayerFacePeelWitnessData allFaces faceBoundary) {f : F} :
    f ∈ data.peelFaces ↔ ∃ i, f ∈ data.layerFaces i := by
  unfold CollarLayerFacePeelWitnessData.peelFaces
  constructor
  · intro hf
    rcases Finset.mem_biUnion.1 hf with ⟨i, -, hfi⟩
    exact ⟨i, hfi⟩
  · rintro ⟨i, hfi⟩
    exact Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hfi⟩

/-- Canonical layer index attached to a collar-layer package. Since the layers are pairwise
disjoint, this is the unique layer containing a peeled face, and `0` outside the package. -/
noncomputable def CollarLayerFacePeelWitnessData.layerHeight {G : SimpleGraph V}
    {allFaces : Finset F} {faceBoundary : F → Finset G.edgeSet}
    (data : CollarLayerFacePeelWitnessData allFaces faceBoundary) (f : F) : ℕ :=
  (Finset.univ.filter fun i : Fin data.numLayers => f ∈ data.layerFaces i).sup Fin.val

theorem CollarLayerFacePeelWitnessData.layerHeight_eq_of_mem {G : SimpleGraph V}
    {allFaces : Finset F} {faceBoundary : F → Finset G.edgeSet}
    (data : CollarLayerFacePeelWitnessData allFaces faceBoundary)
    {i : Fin data.numLayers} {f : F} (hf : f ∈ data.layerFaces i) :
    data.layerHeight f = i.1 := by
  have hs :
      Finset.univ.filter (fun j : Fin data.numLayers => f ∈ data.layerFaces j) = {i} := by
    ext j
    constructor
    · intro hj
      have hfj : f ∈ data.layerFaces j := (Finset.mem_filter.1 hj).2
      by_cases hji : j = i
      · simp [hji]
      · exact False.elim <| (Finset.disjoint_left.1 (data.hdisjoint hji)) hfj hf
    · intro hj
      have hji : j = i := Finset.mem_singleton.1 hj
      subst hji
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hf⟩
  unfold CollarLayerFacePeelWitnessData.layerHeight
  simp [hs]

theorem CollarLayerFacePeelWitnessData.layerHeight_lt_of_mem_of_lt_of_mem
    {G : SimpleGraph V}
    {allFaces : Finset F} {faceBoundary : F → Finset G.edgeSet}
    (data : CollarLayerFacePeelWitnessData allFaces faceBoundary)
    {i j : Fin data.numLayers} {f g : F}
    (hf : f ∈ data.layerFaces i) (hij : i < j) (hg : g ∈ data.layerFaces j) :
    data.layerHeight f < data.layerHeight g := by
  rw [data.layerHeight_eq_of_mem hf, data.layerHeight_eq_of_mem hg]
  exact hij

/-- A finite collar-layer package canonically yields the boundary-rooted certificate consumed by
Theorem 4.9 by sorting faces according to their canonical layer index. -/
noncomputable def CollarLayerFacePeelWitnessData.toBoundaryRootedFacePeelCertificate
    {G : SimpleGraph V}
    {allFaces : Finset F} {faceBoundary : F → Finset G.edgeSet}
    (data : CollarLayerFacePeelWitnessData allFaces faceBoundary) :
    BoundaryRootedFacePeelCertificate allFaces faceBoundary :=
  boundaryRootedFacePeelCertificate_of_heightOrdered_facePeelWitnessCover
    allFaces faceBoundary
    (heightOrderedFaceOrder data.peelFaces data.layerHeight) data.witnessEdge data.layerHeight
    (by
      intro e he
      rcases Finset.mem_image.1 (data.hcover he) with ⟨f, hf, hfe⟩
      exact (mem_facePeelWitnessSupport_iff _ _).2
        ⟨f, (mem_heightOrderedFaceOrder_iff _ _).2 hf, hfe⟩)
    (heightOrderedFaceOrder_order data.peelFaces data.layerHeight)
    (by
      intro f hf
      rcases (data.mem_peelFaces_iff).1 ((mem_heightOrderedFaceOrder_iff _ _).1 hf) with
        ⟨i, hfi⟩
      exact data.hwitness i f hfi)
    (by
      intro f hf e he
      rcases (data.mem_peelFaces_iff).1 ((mem_heightOrderedFaceOrder_iff _ _).1 hf) with
        ⟨i, hfi⟩
      rcases data.hrest i f hfi e he with hboundary | ⟨j, hij, g, hgj, hge⟩
      · exact Or.inl hboundary
      · exact Or.inr ⟨g, (mem_heightOrderedFaceOrder_iff _ _).2 <|
          (data.mem_peelFaces_iff).2 ⟨j, hgj⟩, hge,
          data.layerHeight_lt_of_mem_of_lt_of_mem hfi hij hgj⟩)

/-- Annihilator form of the generic finite collar-layer witness-cover interface. -/
theorem zero_on_ambientFaceSupport_of_collarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (allFaces : Finset F) (faceBoundary : F → Finset G.edgeSet)
    (data : CollarLayerFacePeelWitnessData allFaces faceBoundary)
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport faceBoundary allFaces allFaces, z e = 0)
    (horth : ∀ i f, f ∈ data.layerFaces i →
      ∀ γ, γ ≠ 0 → γ ≠ C (data.witnessEdge f) →
        chainDot
            (boundaryBicoloredEdges C (C (data.witnessEdge f)) (C (data.witnessEdge f) + γ)
              (faceBoundary f))
            z
            (polarizedFaceGenerator C (C (data.witnessEdge f)) (C (data.witnessEdge f) + γ)
              (faceBoundary f)) = 0) :
    ∀ e ∈ allFaces.biUnion faceBoundary, z e = 0 := by
  exact zero_on_ambientFaceSupport_of_boundaryRootedFacePeelCertificate
    (C := C) (htait := htait) (z := z)
    (allFaces := allFaces) (faceBoundary := faceBoundary)
    (cert := data.toBoundaryRootedFacePeelCertificate)
    hall hzeroBoundary
    (by
      intro f hf γ hγ0 hγd
      rcases (data.mem_peelFaces_iff).1 ((mem_heightOrderedFaceOrder_iff _ _).1 hf) with
        ⟨i, hfi⟩
      exact horth i f hfi γ hγ0 hγd)

/-- Canonical collar-layer decomposition of a height-ordered witness-cover package, obtained by
grouping peeled faces according to their natural-valued height. -/
noncomputable def collarLayerFacePeelWitnessData_of_heightOrderedFacePeelWitnessCover
    {G : SimpleGraph V}
    (allFaces peelFaces : Finset F) (faceBoundary : F → Finset G.edgeSet)
    (witnessEdge : F → G.edgeSet) (height : F → ℕ)
    (hcover : interiorEdgeSupport faceBoundary allFaces ⊆ peelFaces.image witnessEdge)
    (hwitness : ∀ f ∈ peelFaces, witnessEdge f ∈ faceBoundary f)
    (hrest : ∀ f ∈ peelFaces, ∀ e ∈ (faceBoundary f).erase (witnessEdge f),
      e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
        ∃ g ∈ peelFaces, witnessEdge g = e ∧ height f < height g) :
    CollarLayerFacePeelWitnessData allFaces faceBoundary := by
  let maxHeight : ℕ := peelFaces.sup height
  let layerFaces : Fin (maxHeight + 1) → Finset F :=
    fun i => peelFaces.filter fun f => height f = i.1
  refine
    { numLayers := maxHeight + 1
      layerFaces := layerFaces
      witnessEdge := witnessEdge
      hdisjoint := ?_
      hcover := ?_
      hwitness := ?_
      hrest := ?_ }
  · intro i j hij
    refine Finset.disjoint_left.2 ?_
    intro f hfi hfj
    have hfi' : height f = i.1 := (Finset.mem_filter.1 hfi).2
    have hfj' : height f = j.1 := (Finset.mem_filter.1 hfj).2
    apply hij
    exact Fin.ext <| hfi'.symm.trans hfj'
  · intro e he
    rcases Finset.mem_image.1 (hcover he) with ⟨f, hf, hfe⟩
    have hbound : height f < maxHeight + 1 := Nat.lt_succ_of_le (Finset.le_sup hf)
    let i : Fin (maxHeight + 1) := ⟨height f, hbound⟩
    refine Finset.mem_image.2 ⟨f, ?_, hfe⟩
    exact Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, Finset.mem_filter.2 ⟨hf, rfl⟩⟩
  · intro i f hfi
    exact hwitness f (Finset.mem_filter.1 hfi).1
  · intro i f hfi e he
    rcases hrest f (Finset.mem_filter.1 hfi).1 e he with hboundary | ⟨g, hg, hge, hlt⟩
    · exact Or.inl hboundary
    · have hbound : height g < maxHeight + 1 := Nat.lt_succ_of_le (Finset.le_sup hg)
      let j : Fin (maxHeight + 1) := ⟨height g, hbound⟩
      refine Or.inr ⟨j, ?_, g, Finset.mem_filter.2 ⟨hg, rfl⟩, hge⟩
      have hfiHeight : i.1 = height f := (Finset.mem_filter.1 hfi).2.symm
      exact hfiHeight.trans_lt hlt

/-- Canonical collar-layer decomposition of a well-founded parent witness-cover package, obtained
by grouping peeled faces according to the canonical `parentHeight`. -/
noncomputable def collarLayerFacePeelWitnessData_of_wellFounded_parentFacePeelWitnessCover
    {G : SimpleGraph V}
    (allFaces peelFaces : Finset F) (faceBoundary : F → Finset G.edgeSet)
    (parentFace : F → Option F) (witnessEdge : F → G.edgeSet)
    (hWF : WellFounded (ParentRel parentFace))
    (hcover : interiorEdgeSupport faceBoundary allFaces ⊆ peelFaces.image witnessEdge)
    (hwitness : ∀ f ∈ peelFaces, witnessEdge f ∈ faceBoundary f)
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (faceBoundary f).erase (witnessEdge f),
      e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
        ∃ g ∈ peelFaces, parentFace g = some f ∧ witnessEdge g = e) :
    CollarLayerFacePeelWitnessData allFaces faceBoundary :=
  collarLayerFacePeelWitnessData_of_heightOrderedFacePeelWitnessCover
    allFaces peelFaces faceBoundary witnessEdge (parentHeight parentFace hWF)
    hcover hwitness
    (by
      intro f hf e he
      rcases hchildren f hf e he with hboundary | ⟨g, hg, hgf, hge⟩
      · exact Or.inl hboundary
      · exact Or.inr ⟨g, hg, hge, parentHeight_lt_of_parent parentFace hWF hgf⟩)

/-- Packaged geometric data for the root-cover plus root-separation adjacency-distance route.
This is the reusable abstraction behind the current rooted forest Step 2 endpoint: a peeled face
owns a witness edge, every interior edge is owned by some peeled face, and every non-witness edge
on a peeled face lies either on the ambient boundary support or on an adjacent peeled child that
is strictly farther from the unique root of its component. -/
structure CoverSeparatedRootsAdjDistancePeelData {G : SimpleGraph V}
    (T : SimpleGraph F) (allFaces : Finset F) (faceBoundary : F → Finset G.edgeSet) where
  peelFaces : Finset F
  roots : Finset F
  witnessEdge : F → G.edgeSet
  hAcyc : T.IsAcyclic
  hcoverRoots : RootSetCovers T roots
  hsepRoots : RootSetSeparated T roots
  hcover : interiorEdgeSupport faceBoundary allFaces ⊆ peelFaces.image witnessEdge
  hwitness : ∀ f ∈ peelFaces, witnessEdge f ∈ faceBoundary f
  hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (faceBoundary f).erase (witnessEdge f),
    e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
      ∃ g ∈ peelFaces, T.Adj f g ∧ witnessEdge g = e ∧
        T.dist f (uniqueReachableRoot T roots
          (hasUniqueReachableRoot_of_cover_and_separated T roots hcoverRoots hsepRoots) f) <
          T.dist g (uniqueReachableRoot T roots
            (hasUniqueReachableRoot_of_cover_and_separated T roots hcoverRoots hsepRoots) g)

/-- Named constructor for the cover/separated-root adjacency-distance package. -/
def coverSeparatedRootsAdjDistancePeelDataOfWitnessCover
    {G : SimpleGraph V}
    (T : SimpleGraph F) (allFaces peelFaces roots : Finset F)
    (faceBoundary : F → Finset G.edgeSet)
    (witnessEdge : F → G.edgeSet)
    (hAcyc : T.IsAcyclic)
    (hcoverRoots : RootSetCovers T roots)
    (hsepRoots : RootSetSeparated T roots)
    (hcover : interiorEdgeSupport faceBoundary allFaces ⊆ peelFaces.image witnessEdge)
    (hwitness : ∀ f ∈ peelFaces, witnessEdge f ∈ faceBoundary f)
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (faceBoundary f).erase (witnessEdge f),
      e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
        ∃ g ∈ peelFaces, T.Adj f g ∧ witnessEdge g = e ∧
          T.dist f (uniqueReachableRoot T roots
            (hasUniqueReachableRoot_of_cover_and_separated T roots hcoverRoots hsepRoots) f) <
            T.dist g (uniqueReachableRoot T roots
              (hasUniqueReachableRoot_of_cover_and_separated T roots hcoverRoots hsepRoots) g)) :
    CoverSeparatedRootsAdjDistancePeelData T allFaces faceBoundary :=
  { peelFaces := peelFaces
    roots := roots
    witnessEdge := witnessEdge
    hAcyc := hAcyc
    hcoverRoots := hcoverRoots
    hsepRoots := hsepRoots
    hcover := hcover
    hwitness := hwitness
    hchildren := hchildren }

/-- The packaged cover/separated-root adjacency-distance data canonically yields a boundary-rooted
peel certificate. -/
noncomputable def CoverSeparatedRootsAdjDistancePeelData.toCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    {T : SimpleGraph F} {allFaces : Finset F} {faceBoundary : F → Finset G.edgeSet}
    (data : CoverSeparatedRootsAdjDistancePeelData T allFaces faceBoundary) :
    CollarLayerFacePeelWitnessData allFaces faceBoundary := by
  let hroots := hasUniqueReachableRoot_of_cover_and_separated T data.roots
    data.hcoverRoots data.hsepRoots
  let height : F → ℕ := fun f => T.dist f (uniqueReachableRoot T data.roots hroots f)
  refine collarLayerFacePeelWitnessData_of_heightOrderedFacePeelWitnessCover
    allFaces data.peelFaces faceBoundary data.witnessEdge height
    data.hcover data.hwitness ?_
  intro f hf e he
  rcases data.hchildren f hf e he with hboundary | ⟨g, hg, _hadj, hge, hlt⟩
  · exact Or.inl hboundary
  · exact Or.inr ⟨g, hg, hge, hlt⟩

/-- The packaged cover/separated-root adjacency-distance data canonically yields a boundary-rooted
peel certificate. -/
noncomputable def CoverSeparatedRootsAdjDistancePeelData.toBoundaryRootedFacePeelCertificate
    {G : SimpleGraph V}
    {T : SimpleGraph F} {allFaces : Finset F} {faceBoundary : F → Finset G.edgeSet}
    (data : CoverSeparatedRootsAdjDistancePeelData T allFaces faceBoundary) :
    BoundaryRootedFacePeelCertificate allFaces faceBoundary :=
  data.toCollarLayerFacePeelWitnessData.toBoundaryRootedFacePeelCertificate

/-- Annihilator form of the packaged cover/separated-root adjacency-distance data. -/
theorem zero_on_ambientFaceSupport_of_coverSeparatedRootsAdjDistancePeelData
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (T : SimpleGraph F) (allFaces : Finset F) (faceBoundary : F → Finset G.edgeSet)
    (data : CoverSeparatedRootsAdjDistancePeelData T allFaces faceBoundary)
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport faceBoundary allFaces allFaces, z e = 0)
    (horth : ∀ f ∈ data.peelFaces,
      ∀ γ, γ ≠ 0 → γ ≠ C (data.witnessEdge f) →
        chainDot
            (boundaryBicoloredEdges C (C (data.witnessEdge f)) (C (data.witnessEdge f) + γ)
              (faceBoundary f))
            z
            (polarizedFaceGenerator C (C (data.witnessEdge f)) (C (data.witnessEdge f) + γ)
              (faceBoundary f)) = 0) :
    ∀ e ∈ allFaces.biUnion faceBoundary, z e = 0 := by
  exact zero_on_ambientFaceSupport_of_collarLayerFacePeelWitnessData
    (C := C) (htait := htait) (z := z) (allFaces := allFaces) (faceBoundary := faceBoundary)
    (data := data.toCollarLayerFacePeelWitnessData) hall hzeroBoundary
    (by
      intro i f hfi γ hγ0 hγd
      exact horth f (Finset.mem_filter.1 hfi).1 γ hγ0 hγd)

end Mettapedia.GraphTheory.FourColor
