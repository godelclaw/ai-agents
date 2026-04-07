import FourColor.GoertzelV23.Section8ChapterAssembly

namespace FourColor.GoertzelV23

/-
Concrete assembly for the first half of the sharp Section 8 closure bridge.

This file discharges the first new mouth introduced by
`Section8CollarReachabilityTarget`:

  execution -> cut-open collar reachability

by instantiating cut-open reachability with the already extracted
`LocalGadgetReachable` predicate from `Section8Target`.
-/

/-- Concrete cut-open reachability for Section 8: local gadget reachability. -/
def Section8ChapterData.CutOpenReachable
    (S : Section8ChapterData) : S.Gadget → Prop :=
  (S.toSection8Target).LocalGadgetReachable

/--
Execution immediately implies cut-open reachability, because the cut-open
gadget is reachable exactly when some operator executes it.
-/
theorem Section8ChapterData.execution_implies_cut_open_reachability
    (S : Section8ChapterData) :
    ∀ {G : S.Gadget} {op : S.Operator},
      S.Executes G op →
      S.CutOpenReachable G := by
  intro G op hexec
  exact ⟨op, hexec⟩

/--
Specialize the sharp collar bridge to the concrete cut-open reachability
predicate already extracted from Section 8.
-/
def Section8ChapterData.toConcreteCollarReachabilityTarget
    (S : Section8ChapterData)
    (hClose :
      ∀ {A : S.Collar} {G : S.Gadget},
        S.RadiusOneCollar A →
        S.CutOpenTo A G →
        S.CutOpenReachable G →
        S.CollarReachable A) :
    Section8CollarReachabilityTarget :=
  S.toCollarReachabilityTarget
    S.CutOpenReachable
    S.execution_implies_cut_open_reachability
    hClose

/--
Once the second half of the sharp bridge is supplied, the first half is no
longer an assumption: it is discharged by the existing Section 8 execution
surface.
-/
theorem Section8ChapterData.radius_one_collar_reachable_of_concrete_cut_open_closure
    (S : Section8ChapterData)
    (hClose :
      ∀ {A : S.Collar} {G : S.Gadget},
        S.RadiusOneCollar A →
        S.CutOpenTo A G →
        S.CutOpenReachable G →
        S.CollarReachable A) :
    ∀ {A : S.Collar},
      S.RadiusOneCollar A →
      S.CollarReachable A := by
  intro A hcollar
  rcases S.radius_one_collar_executes hcollar with ⟨G, op, hcut, _, hexec⟩
  exact
    (S.toConcreteCollarReachabilityTarget hClose).radius_one_collar_reachable
      hcollar
      hcut
      hexec

end FourColor.GoertzelV23
