namespace FourColor.GoertzelV23

universe u v

/--
Ben's cut-open transfer branch inside the final Step 4 closure.

After a lifted collar word is boundary-safe, the proof still needs to show that
the word agrees with the transfer data inherited from the cut-open gadget
execution. We isolate that as two substeps:
- boundary safety preserves the cut-open seam data during lift-back;
- preserved seam data determines the cut-open transfer on the whole collar.
-/
structure Section8CutOpenTransferTarget where
  Collar : Type u
  LiftedWord : Type v
  RadiusOneCollar : Collar → Prop
  LiftedBackTo : Collar → LiftedWord → Prop
  BoundarySafe : LiftedWord → Prop
  PreservesCutOpenSeam : Collar → LiftedWord → Prop
  MatchesCutOpenTransfer : Collar → LiftedWord → Prop
  boundary_safe_lift_preserves_cut_open_seam :
    ∀ {A : Collar} {w : LiftedWord},
      RadiusOneCollar A →
      LiftedBackTo A w →
      BoundarySafe w →
      PreservesCutOpenSeam A w
  cut_open_seam_preservation_matches_transfer :
    ∀ {A : Collar} {w : LiftedWord},
      RadiusOneCollar A →
      LiftedBackTo A w →
      PreservesCutOpenSeam A w →
      MatchesCutOpenTransfer A w

/--
The extracted cut-open transfer theorem: a boundary-safe lifted collar word
agrees with the cut-open transfer data on the collar.
-/
theorem Section8CutOpenTransferTarget.boundary_safe_lift_matches_cut_open_transfer
    (S : Section8CutOpenTransferTarget) :
    ∀ {A : S.Collar} {w : S.LiftedWord},
      S.RadiusOneCollar A →
      S.LiftedBackTo A w →
      S.BoundarySafe w →
      S.MatchesCutOpenTransfer A w := by
  intro A w hcollar hlift hsafe
  exact
    S.cut_open_seam_preservation_matches_transfer
      hcollar
      hlift
      (S.boundary_safe_lift_preserves_cut_open_seam hcollar hlift hsafe)

end FourColor.GoertzelV23
