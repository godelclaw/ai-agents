import FourColor.GoertzelV23.Section6BoundaryTarget

namespace FourColor.GoertzelV23

universe u v

/--
Theorem-back target for Ben Goertzel's Section 6.3 finite one-move repair basis.

This stays close to Lemma 6.6:
- a canonical bad boundary word
- a finite repair basis
- each repair basis element sends the canonical bad word to a good word
-/
structure Section6RepairBasisTarget where
  boundary : Section6BoundaryTarget
  RepairType : Type v
  CanonicalBadWord : boundary.BoundaryWord
  InRepairBasis : RepairType → Prop
  repairedCanonicalWord : RepairType → boundary.BoundaryWord
  canonical_bad :
    boundary.BadBoundaryWord CanonicalBadWord
  lemma_6_6 :
    ∀ {r : RepairType},
      InRepairBasis r →
      boundary.GoodBoundaryWord (repairedCanonicalWord r)

/-- Every repair-basis move on the canonical bad word produces a good word. -/
theorem Section6RepairBasisTarget.repair_basis_hits_good
    (S : Section6RepairBasisTarget) :
    ∀ {r : S.RepairType},
      S.InRepairBasis r →
      S.boundary.GoodBoundaryWord (S.repairedCanonicalWord r) := by
  intro r hr
  exact S.lemma_6_6 hr

/-- Every repair-basis move on the canonical bad word yields an extendable word. -/
theorem Section6RepairBasisTarget.repair_basis_hits_extendable
    (S : Section6RepairBasisTarget) :
    ∀ {r : S.RepairType},
      S.InRepairBasis r →
      S.boundary.ExtendsAcrossCap (S.repairedCanonicalWord r) := by
  intro r hr
  exact S.boundary.good_implies_extends (S.repair_basis_hits_good hr)

end FourColor.GoertzelV23
