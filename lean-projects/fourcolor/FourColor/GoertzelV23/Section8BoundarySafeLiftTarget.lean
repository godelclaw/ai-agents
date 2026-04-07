namespace FourColor.GoertzelV23

universe u v

/--
Ben's Step 4 closure split for a single radius-1 collar.

Once Section 8 provides reachability on the cut-open collar gadget, the
remaining work is not one anonymous theorem. Ben's proof uses two distinct
steps:
- lift the cut-open Kempe word back to the full annulus in a way that keeps the
  already-corrected outer boundary fixed;
- conclude from that boundary-safe lifted word that the collar correction is
  realized in the annulus.
-/
structure Section8BoundarySafeLiftTarget where
  Collar : Type u
  Gadget : Type v
  RadiusOneCollar : Collar → Prop
  CutOpenTo : Collar → Gadget → Prop
  CutOpenReachable : Gadget → Prop
  BoundarySafeLift : Collar → Prop
  CollarReachable : Collar → Prop
  cut_open_reachability_lifts_boundary_safely :
    ∀ {A : Collar} {G : Gadget},
      RadiusOneCollar A →
      CutOpenTo A G →
      CutOpenReachable G →
      BoundarySafeLift A
  boundary_safe_lift_closes_collar :
    ∀ {A : Collar},
      RadiusOneCollar A →
      BoundarySafeLift A →
      CollarReachable A

/--
The split closure theorem: cut-open reachability closes the collar once the
boundary-safe lift and closure steps are both available.
-/
theorem Section8BoundarySafeLiftTarget.cut_open_reachability_closes
    (S : Section8BoundarySafeLiftTarget) :
    ∀ {A : S.Collar} {G : S.Gadget},
      S.RadiusOneCollar A →
      S.CutOpenTo A G →
      S.CutOpenReachable G →
      S.CollarReachable A := by
  intro A G hcollar hcut hreach
  exact
    S.boundary_safe_lift_closes_collar
      hcollar
      (S.cut_open_reachability_lifts_boundary_safely hcollar hcut hreach)

/--
In particular, every radius-1 collar is reachable once some cut-open gadget for
it is known to be reachable.
-/
theorem Section8BoundarySafeLiftTarget.radius_one_collar_reachable
    (S : Section8BoundarySafeLiftTarget) :
    ∀ {A : S.Collar},
      (∃ G : S.Gadget, S.CutOpenTo A G ∧ S.CutOpenReachable G) →
      S.RadiusOneCollar A →
      S.CollarReachable A := by
  intro A hreach hcollar
  rcases hreach with ⟨G, hcut, hgreach⟩
  exact S.cut_open_reachability_closes hcollar hcut hgreach

end FourColor.GoertzelV23
