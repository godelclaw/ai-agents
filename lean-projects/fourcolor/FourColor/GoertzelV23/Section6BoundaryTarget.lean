namespace FourColor.GoertzelV23

universe u

/--
Theorem-back target for Ben Goertzel's Section 6.1-6.2 CAP5 boundary package.

This isolates the boundary-word side of the CAP5 argument:
- `ParityAllowed` corresponds to the odd-count restriction from Lemma 6.3
- `GoodBoundaryWord` is block structure `(3,1,1)`
- `BadBoundaryWord` is block structure `(2,1,1,1)`
- `ExtendsAcrossCap` is the extension predicate from Lemma 6.4
-/
structure Section6BoundaryTarget where
  BoundaryWord : Type u
  ParityAllowed : BoundaryWord → Prop
  GoodBoundaryWord : BoundaryWord → Prop
  BadBoundaryWord : BoundaryWord → Prop
  ExtendsAcrossCap : BoundaryWord → Prop
  parity_normal_form :
    ∀ {w : BoundaryWord},
      ParityAllowed w →
      GoodBoundaryWord w ∨ BadBoundaryWord w
  lemma_6_4 :
    ∀ {w : BoundaryWord},
      GoodBoundaryWord w ↔ ExtendsAcrossCap w

/-- Parity-allowed CAP5 boundary words are either good or bad. -/
theorem Section6BoundaryTarget.good_or_bad
    (S : Section6BoundaryTarget) :
    ∀ {w : S.BoundaryWord},
      S.ParityAllowed w →
      S.GoodBoundaryWord w ∨ S.BadBoundaryWord w := by
  intro w hw
  exact S.parity_normal_form hw

/-- Good CAP5 boundary words extend across the cap. -/
theorem Section6BoundaryTarget.good_implies_extends
    (S : Section6BoundaryTarget) :
    ∀ {w : S.BoundaryWord},
      S.GoodBoundaryWord w →
      S.ExtendsAcrossCap w := by
  intro w hw
  exact (S.lemma_6_4).mp hw

/-- Extension across the cap forces the boundary word to be good. -/
theorem Section6BoundaryTarget.extends_implies_good
    (S : Section6BoundaryTarget) :
    ∀ {w : S.BoundaryWord},
      S.ExtendsAcrossCap w →
      S.GoodBoundaryWord w := by
  intro w hw
  exact (S.lemma_6_4).mpr hw

end FourColor.GoertzelV23
