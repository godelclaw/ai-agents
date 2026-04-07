import FourColor.GoertzelV23.Section8CollarDecompositionTarget
import FourColor.GoertzelV23.Section8CollarReachabilityTarget
import FourColor.GoertzelV23.Section8CompositionTarget

namespace FourColor.GoertzelV23

universe u v w

/--
Unified theorem-back package for Ben Goertzel's Section 8.

This chapter-level assembly follows Ben's actual proof spine:
- radius-1 collar decomposition into bounded gadgets
- rigidity to the canonical three-cell gadget up to mirror
- local execution / transparency / pairing control on that gadget
- transparent composition across the gadget chain

The remaining explicit gap after this assembly is the bridge from executable
cut-open collar gadgets back to the collar-level reachability statement used in
Section 9.
-/
structure Section8ChapterData where
  Collar : Type u
  Gadget : Type v
  Operator : Type w
  RadiusOneCollar : Collar → Prop
  CutOpenTo : Collar → Gadget → Prop
  CanonicalThreeCell : Gadget → Prop
  MirrorCanonicalThreeCell : Gadget → Prop
  Decomposable : Gadget → Prop
  Transparent : Gadget → Prop
  PairingControlled : Gadget → Prop
  Executes : Gadget → Operator → Prop
  InterfaceControlled : Gadget → Prop
  ComposesTo : Operator → Operator → Operator → Prop
  CollarReachable : Collar → Prop
  lemma_8_5 :
    ∀ {A : Collar},
      RadiusOneCollar A →
      ∃ G : Gadget, CutOpenTo A G ∧ Decomposable G
  lemma_8_6 :
    ∀ {A : Collar} {G : Gadget},
      CutOpenTo A G →
      Decomposable G →
      CanonicalThreeCell G ∨ MirrorCanonicalThreeCell G
  lemma_8_14 :
    ∀ {G : Gadget},
      (CanonicalThreeCell G ∨ MirrorCanonicalThreeCell G) →
      ∃ op : Operator, Executes G op
  lemma_8_15 :
    ∀ {G : Gadget},
      (CanonicalThreeCell G ∨ MirrorCanonicalThreeCell G) →
      Transparent G
  lemma_8_16 :
    ∀ {G : Gadget},
      (CanonicalThreeCell G ∨ MirrorCanonicalThreeCell G) →
      PairingControlled G
  executing_gadget_interface_controlled :
    ∀ {G : Gadget} {op : Operator},
      Executes G op →
      InterfaceControlled G
  lemma_8_17 :
    ∀ {G : Gadget},
      Transparent G →
      PairingControlled G →
      InterfaceControlled G
  lemma_8_18 :
    ∀ {G : Gadget} {op₁ op₂ op : Operator},
      Executes G op₁ →
      Executes G op₂ →
      InterfaceControlled G →
      ComposesTo op₁ op₂ op →
      Executes G op
  corollary_8_19 :
    ∀ {G : Gadget},
      Decomposable G →
      ∃ op : Operator, Executes G op

/-- Extract the collar-decomposition package. -/
def Section8ChapterData.toCollarDecompositionTarget
    (S : Section8ChapterData) :
    Section8CollarDecompositionTarget where
  Collar := S.Collar
  Gadget := S.Gadget
  RadiusOneCollar := S.RadiusOneCollar
  CutOpenTo := S.CutOpenTo
  CanonicalThreeCell := S.CanonicalThreeCell
  MirrorCanonicalThreeCell := S.MirrorCanonicalThreeCell
  Decomposable := S.Decomposable
  lemma_8_5 := S.lemma_8_5
  lemma_8_6 := S.lemma_8_6

/-- Extract the canonical-gadget execution package. -/
def Section8ChapterData.toCanonicalExecutionTarget
    (S : Section8ChapterData) :
    Section8CanonicalExecutionTarget where
  Gadget := S.Gadget
  Operator := S.Operator
  CanonicalThreeCell := S.CanonicalThreeCell
  MirrorCanonicalThreeCell := S.MirrorCanonicalThreeCell
  Transparent := S.Transparent
  PairingControlled := S.PairingControlled
  Executes := S.Executes
  lemma_8_14 := S.lemma_8_14
  lemma_8_15 := S.lemma_8_15
  lemma_8_16 := S.lemma_8_16

/-- Extract the transparent-composition package. -/
def Section8ChapterData.toCompositionTarget
    (S : Section8ChapterData) :
    Section8CompositionTarget where
  base := S.toCanonicalExecutionTarget
  Decomposable := S.Decomposable
  InterfaceControlled := S.InterfaceControlled
  ComposesTo := S.ComposesTo
  executing_gadget_interface_controlled := S.executing_gadget_interface_controlled
  lemma_8_17 := S.lemma_8_17
  lemma_8_18 := S.lemma_8_18
  corollary_8_19 := S.corollary_8_19

/-- Extract the existing abstract Section 8 target. -/
def Section8ChapterData.toSection8Target
    (S : Section8ChapterData) :
    Section8Target :=
  (S.toCompositionTarget).toSection8Target

/-- Every radius-1 collar cuts open to an executable decomposable gadget. -/
theorem Section8ChapterData.radius_one_collar_executes
    (S : Section8ChapterData) :
    ∀ {A : S.Collar},
      S.RadiusOneCollar A →
      ∃ G : S.Gadget, ∃ op : S.Operator,
        S.CutOpenTo A G ∧ S.Decomposable G ∧ S.Executes G op := by
  intro A hcollar
  rcases S.lemma_8_5 hcollar with ⟨G, hcut, hdecomp⟩
  rcases S.corollary_8_19 hdecomp with ⟨op, hexec⟩
  exact ⟨G, op, hcut, hdecomp, hexec⟩

/-- Decomposable gadgets are locally reachable in the extracted Section 8 target. -/
theorem Section8ChapterData.all_decomposable_reachable
    (S : Section8ChapterData) :
    ∀ {G : S.Gadget},
      S.Decomposable G →
      (S.toSection8Target).LocalGadgetReachable G := by
  intro G hdecomp
  exact (S.toSection8Target).decomposable_gadget_reachable hdecomp

/--
Repackage the old one-step Section 8 gap as the sharper two-step collar bridge.
-/
def Section8ChapterData.toCollarReachabilityTarget
    (S : Section8ChapterData)
    (CutOpenReachable : S.Gadget → Prop)
    (hExec :
      ∀ {G : S.Gadget} {op : S.Operator},
        S.Executes G op →
        CutOpenReachable G)
    (hClose :
      ∀ {A : S.Collar} {G : S.Gadget},
        S.RadiusOneCollar A →
        S.CutOpenTo A G →
        CutOpenReachable G →
        S.CollarReachable A) :
    Section8CollarReachabilityTarget where
  Collar := S.Collar
  Gadget := S.Gadget
  Operator := S.Operator
  RadiusOneCollar := S.RadiusOneCollar
  CutOpenTo := S.CutOpenTo
  Executes := S.Executes
  CutOpenReachable := CutOpenReachable
  CollarReachable := S.CollarReachable
  execution_gives_cut_open_reachability := hExec
  cut_open_reachability_closes_collar := hClose

/--
The explicit remaining chapter-level gap after the current assembly: turning
executable cut-open radius-1 collar gadgets into the collar-level reachability
statement used in Section 9's outside-in correction.
-/
def Section8ChapterData.RemainingGap (S : Section8ChapterData) : Prop :=
  ∀ {A : S.Collar} {G : S.Gadget} {op : S.Operator},
    S.RadiusOneCollar A →
    S.CutOpenTo A G →
    S.Executes G op →
    S.CollarReachable A

/--
If the remaining gap closes, every radius-1 collar is reachability-ready for
the later outside-in annulus correction.
-/
theorem Section8ChapterData.radius_one_collar_reachable_of_gap
    (S : Section8ChapterData)
    (hgap : S.RemainingGap) :
    ∀ {A : S.Collar},
      S.RadiusOneCollar A →
      S.CollarReachable A := by
  intro A hcollar
  rcases S.radius_one_collar_executes hcollar with ⟨G, op, hcut, _, hexec⟩
  exact hgap hcollar hcut hexec

/--
Sharper Section 8 closure theorem: if execution implies cut-open reachability
and cut-open reachability closes the collar, then every radius-1 collar is
reachable.
-/
theorem Section8ChapterData.radius_one_collar_reachable_of_bridge
    (S : Section8ChapterData)
    (CutOpenReachable : S.Gadget → Prop)
    (hExec :
      ∀ {G : S.Gadget} {op : S.Operator},
        S.Executes G op →
        CutOpenReachable G)
    (hClose :
      ∀ {A : S.Collar} {G : S.Gadget},
        S.RadiusOneCollar A →
        S.CutOpenTo A G →
        CutOpenReachable G →
        S.CollarReachable A) :
    ∀ {A : S.Collar},
      S.RadiusOneCollar A →
      S.CollarReachable A := by
  intro A hcollar
  rcases S.radius_one_collar_executes hcollar with ⟨G, op, hcut, _, hexec⟩
  exact
    (S.toCollarReachabilityTarget CutOpenReachable hExec hClose).radius_one_collar_reachable
      hcollar
      hcut
      hexec

end FourColor.GoertzelV23
