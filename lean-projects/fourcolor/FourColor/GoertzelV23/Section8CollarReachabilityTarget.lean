namespace FourColor.GoertzelV23

universe u v w

/--
The sharpest local closure target sitting between Ben's Section 8 gadget
execution results and Section 9's collar-by-collar assembly.

This factors the old one-step gap

  executable cut-open collar gadget -> collar reachability

into two explicit mouths:
- execution gives reachability on the cut-open collar gadget itself;
- cut-open collar reachability closes back to reachability of the radius-1
  collar.
-/
structure Section8CollarReachabilityTarget where
  Collar : Type u
  Gadget : Type v
  Operator : Type w
  RadiusOneCollar : Collar → Prop
  CutOpenTo : Collar → Gadget → Prop
  Executes : Gadget → Operator → Prop
  CutOpenReachable : Gadget → Prop
  CollarReachable : Collar → Prop
  execution_gives_cut_open_reachability :
    ∀ {G : Gadget} {op : Operator},
      Executes G op →
      CutOpenReachable G
  cut_open_reachability_closes_collar :
    ∀ {A : Collar} {G : Gadget},
      RadiusOneCollar A →
      CutOpenTo A G →
      CutOpenReachable G →
      CollarReachable A

/--
The extracted closure theorem: once a radius-1 collar cuts open to an executing
gadget, the two bridge mouths imply collar reachability.
-/
theorem Section8CollarReachabilityTarget.radius_one_collar_reachable
    (S : Section8CollarReachabilityTarget) :
    ∀ {A : S.Collar} {G : S.Gadget} {op : S.Operator},
      S.RadiusOneCollar A →
      S.CutOpenTo A G →
      S.Executes G op →
      S.CollarReachable A := by
  intro A G op hcollar hcut hexec
  exact
    S.cut_open_reachability_closes_collar
      hcollar
      hcut
      (S.execution_gives_cut_open_reachability hexec)

end FourColor.GoertzelV23
