import FourColor.GoertzelV23.Section8CanonicalExecutionTarget
import FourColor.GoertzelV23.Section8Target

namespace FourColor.GoertzelV23

/--
The Section 8.5-8.6 theorem-back target for Ben Goertzel's `v23` route.

This packages the transparent interface step and the iterated composition
finish:
- Lemma 8.17: interface control for lifted switches
- Lemma 8.18: composition across a transparent interface
- Corollary 8.19: iterated LKRin composition for the gadget chain
-/
structure Section8CompositionTarget where
  base : Section8CanonicalExecutionTarget
  Decomposable : base.Gadget → Prop
  InterfaceControlled : base.Gadget → Prop
  ComposesTo : base.Operator → base.Operator → base.Operator → Prop
  executing_gadget_interface_controlled :
    ∀ {G : base.Gadget} {op : base.Operator},
      base.Executes G op →
      InterfaceControlled G
  lemma_8_17 :
    ∀ {G : base.Gadget},
      base.Transparent G →
      base.PairingControlled G →
      InterfaceControlled G
  lemma_8_18 :
    ∀ {G : base.Gadget} {op₁ op₂ op : base.Operator},
      base.Executes G op₁ →
      base.Executes G op₂ →
      InterfaceControlled G →
      ComposesTo op₁ op₂ op →
      base.Executes G op
  corollary_8_19 :
    ∀ {G : base.Gadget},
      Decomposable G →
      ∃ op : base.Operator, base.Executes G op

/-- Canonical-family gadgets admit interface control. -/
theorem Section8CompositionTarget.canonical_family_interface_controlled
    (S : Section8CompositionTarget) :
    ∀ {G : S.base.Gadget},
      S.base.CanonicalFamily G →
      S.InterfaceControlled G := by
  intro G hcanonical
  exact
    S.lemma_8_17
      ((S.base).canonical_family_transparent hcanonical)
      ((S.base).canonical_family_pairing_controlled hcanonical)

/-- Convert the explicit Section 8 spine back into the existing abstract target. -/
def Section8CompositionTarget.toSection8Target
    (S : Section8CompositionTarget) :
    Section8Target where
  Gadget := S.base.Gadget
  Operator := S.base.Operator
  CanonicalThreeCell := S.base.CanonicalFamily
  Decomposable := S.Decomposable
  Executes := S.base.Executes
  ComposesTo := S.ComposesTo
  lemma_8_14 := by
    intro G hcanonical
    exact (S.base).canonical_family_reachable hcanonical
  lemma_8_18 := by
    intro G op₁ op₂ op hexec₁ hexec₂ hcomp
    exact
      S.lemma_8_18
        hexec₁
        hexec₂
        (S.executing_gadget_interface_controlled hexec₁)
        hcomp
  corollary_8_19 := S.corollary_8_19

end FourColor.GoertzelV23
