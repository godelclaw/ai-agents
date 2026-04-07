namespace FourColor.GoertzelV23

universe u v w

/--
Ben's second Step 4 substep for a single radius-1 collar.

After a cut-open collar word is lifted back to the ambient annulus, Ben proves
it is boundary-safe by a locality argument:
- if a switched component touched the already-fixed outer boundary, it would be
  anchored there;
- cap-aware locality confines such anchored components to the radius-1 collar;
- confinement forces contact with the cut-open input stubs;
- but lifted words coming from the cut-open LKRin execution avoid those input
  stubs.
-/
structure Section8BoundarySafetyTarget where
  Collar : Type u
  LiftedWord : Type v
  Component : Type w
  RadiusOneCollar : Collar → Prop
  LiftedBackTo : Collar → LiftedWord → Prop
  BoundarySafe : LiftedWord → Prop
  UsesComponent : LiftedWord → Component → Prop
  AvoidsInputStubs : LiftedWord → Prop
  TouchesFixedBoundary : Collar → Component → Prop
  AnchoredAtFixedBoundary : Collar → Component → Prop
  ConfinedToCollar : Collar → Component → Prop
  MeetsInputStub : Collar → Component → Prop
  lifted_words_avoid_input_stubs :
    ∀ {A : Collar} {w : LiftedWord},
      RadiusOneCollar A →
      LiftedBackTo A w →
      AvoidsInputStubs w
  touching_fixed_boundary_is_anchored :
    ∀ {A : Collar} {K : Component},
      RadiusOneCollar A →
      TouchesFixedBoundary A K →
      AnchoredAtFixedBoundary A K
  anchored_component_confined :
    ∀ {A : Collar} {K : Component},
      RadiusOneCollar A →
      AnchoredAtFixedBoundary A K →
      ConfinedToCollar A K
  confined_component_meets_input_stub :
    ∀ {A : Collar} {K : Component},
      RadiusOneCollar A →
      ConfinedToCollar A K →
      MeetsInputStub A K
  avoids_input_stubs_forbids_component :
    ∀ {A : Collar} {w : LiftedWord} {K : Component},
      AvoidsInputStubs w →
      UsesComponent w K →
      ¬ MeetsInputStub A K
  boundary_safe_of_components_avoid_fixed_boundary :
    ∀ {A : Collar} {w : LiftedWord},
      RadiusOneCollar A →
      LiftedBackTo A w →
      (∀ K : Component, UsesComponent w K → ¬ TouchesFixedBoundary A K) →
      BoundarySafe w

/--
The extracted Step 4 boundary-safety theorem: every lifted word coming from a
radius-1 collar is boundary-safe.
-/
theorem Section8BoundarySafetyTarget.lifted_word_is_boundary_safe
    (S : Section8BoundarySafetyTarget) :
    ∀ {A : S.Collar} {w : S.LiftedWord},
      S.RadiusOneCollar A →
      S.LiftedBackTo A w →
      S.BoundarySafe w := by
  intro A w hcollar hlift
  apply
    S.boundary_safe_of_components_avoid_fixed_boundary
      hcollar
      hlift
  intro K huse htouch
  have havoid : S.AvoidsInputStubs w :=
    S.lifted_words_avoid_input_stubs hcollar hlift
  have hanchor : S.AnchoredAtFixedBoundary A K :=
    S.touching_fixed_boundary_is_anchored hcollar htouch
  have hconfined : S.ConfinedToCollar A K :=
    S.anchored_component_confined hcollar hanchor
  have hstub : S.MeetsInputStub A K :=
    S.confined_component_meets_input_stub hcollar hconfined
  exact (S.avoids_input_stubs_forbids_component havoid huse) hstub

end FourColor.GoertzelV23
