import Mettapedia.Computability.PNP.ActualSwitchedLocalFamily
import Mettapedia.Computability.PNP.ExactZABTargetInterface

/-!
# PNP grassroots: manuscript structure beyond actual locality

`ActualSwitchedLocalFamily` records the manuscript local-normal-form bracket:
locality alone is insufficient, while exact identification with the ERM family
is sufficient.  This file isolates two narrower non-arbitrary structures that
can sit between those endpoints.

* `BitCodeData` says the actual local rules are selected from an `s`-bit
  encoded class.  This is the finite-hypothesis/description-length shape
  needed for the clocked small-image target.
* `ZABDecisionListData` specializes that idea to the existing shared
  `(zfeat z, a, b)` decision-list surface.  This is the Lean counterpart of the
  manuscript route where the switched local rule is not arbitrary but is
  selected from a fixed small local hypothesis class over the visible data.

The full-rule counterexample remains available below; these strengthened
interfaces explicitly rule it out when their bit budget is below the exact
visible truth-table budget.
-/

namespace Mettapedia.Computability.PNP

universe u v w

namespace ActualSwitchedLocalInterface

variable {Z : Type v} {k : ℕ} {Index : Type u} {Block : Type w}

/-- A strengthened actual-switched local interface: the local rules are not
arbitrary functions on the exact visible surface, but are all decoded from a
single `s`-bit family.  This captures the small finite hypothesis-class /
bounded-description-length obligation without committing to one concrete
learning algorithm. -/
structure BitCodeData
    (T : ActualSwitchedLocalInterface Z k Index Block) (s : ℕ) where
  codeFamily : BitEncodedClassifierFamily (ExactVisiblePostSwitchSurface Z k) s
  realized : ∀ i, ∃ c, codeFamily.decode c = T.localRule i

namespace BitCodeData

variable {T : ActualSwitchedLocalInterface Z k Index Block} {s clock : ℕ}

/-- The bounded-code strengthened interface is exactly the small-image
compression target needed by the clocked bridge. -/
theorem exactVisibleCompressionTarget
    (h : BitCodeData T s) :
    ExactVisibleCompressionTarget
      (Z := Z) (k := k) (Index := Index) T.predictorFamily s := by
  refine ⟨h.codeFamily, ?_⟩
  intro i
  rcases h.realized i with ⟨c, hc⟩
  exact ⟨c, by simpa [ActualSwitchedLocalInterface.predictorFamily] using hc⟩

/-- Equivalently, the actual switched local family has at most `2^s` distinct
exact-visible predictors. -/
theorem finitePredictorCover
    (h : BitCodeData T s) :
    T.predictorFamily.FinitePredictorCover (2 ^ s) := by
  exact
    (exactVisibleCompressionTarget_iff_finitePredictorCover
      (Z := Z) (k := k) (s := s) (Index := Index) (G := T.predictorFamily)).mp
      h.exactVisibleCompressionTarget

/-- The same bounded-code data yields finite representative indices. -/
theorem finiteIndexRepresentativeCover
    (h : BitCodeData T s) :
    T.predictorFamily.FiniteIndexRepresentativeCover (2 ^ s) := by
  exact
    (exactVisibleCompressionTarget_iff_finiteIndexRepresentativeCover
      (Z := Z) (k := k) (s := s) (Index := Index) (G := T.predictorFamily)).mp
      h.exactVisibleCompressionTarget

/-- The same bounded-code data yields a finite quotient-code presentation of
the predictor image. -/
theorem finitePredictorQuotient
    (h : BitCodeData T s) :
    T.predictorFamily.FinitePredictorQuotient (2 ^ s) := by
  exact
    (exactVisibleCompressionTarget_iff_finitePredictorQuotient
      (Z := Z) (k := k) (s := s) (Index := Index) (G := T.predictorFamily)).mp
      h.exactVisibleCompressionTarget

/-- Consequently the bounded-code strengthened actual switched local interface
closes the clocked finite-learning payload. -/
theorem clockedKpolyFiniteLearningPayload
    [Fintype Z]
    (h : BitCodeData T s) :
    ClockedKpolyFiniteLearningPayload T.predictorFamily s clock := by
  exact
    clockedKpolyFiniteLearningPayload_of_exactVisibleCompressionTarget
      (Z := Z) (k := k) (s := s) (clock := clock) (Index := Index)
      h.exactVisibleCompressionTarget

end BitCodeData

/-- A manuscript-shaped specialization of `BitCodeData`: the actual local rules
are realized by the fixed shared `(zfeat z, a, b)` decision-list class.  This
does not require equality with an ERM selector; it only requires that every
selected local rule factor through the same concrete bounded-code family. -/
structure ZABDecisionListData
    {r : ℕ}
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (zfeat : Z → BitVec r) where
  realized :
    RealizedByRawExactZABDecisionListFamily
      (Z := Z) (r := r) (k := k) (Index := Index) zfeat T.predictorFamily

namespace ZABDecisionListData

variable {r clock : ℕ}
variable {T : ActualSwitchedLocalInterface Z k Index Block}
variable {zfeat : Z → BitVec r}

/-- Package a ZAB realization as the existing target-data interface. -/
theorem targetData
    (h : ZABDecisionListData T zfeat) :
    ExactZABDecisionListTargetData
      (Z := Z) (r := r) (k := k) (Index := Index) zfeat T.predictorFamily := by
  exact ⟨h.realized⟩

/-- The ZAB decision-list structure gives the exact compression target at the
manuscript-visible budget `r + 2*k + 1`. -/
theorem exactVisibleCompressionTarget
    (h : ZABDecisionListData T zfeat) :
    ExactVisibleCompressionTarget
      (Z := Z) (k := k) (Index := Index) T.predictorFamily (r + 2 * k + 1) := by
  exact h.targetData.compressionTarget_twoMul

/-- Hence the ZAB decision-list structured actual family has a finite predictor
cover of size at most `2^(r + 2*k + 1)`. -/
theorem finitePredictorCover
    (h : ZABDecisionListData T zfeat) :
    T.predictorFamily.FinitePredictorCover (2 ^ (r + 2 * k + 1)) := by
  exact h.targetData.finitePredictorCover_twoMul

/-- The same ZAB data yields finite representative indices. -/
theorem finiteIndexRepresentativeCover
    (h : ZABDecisionListData T zfeat) :
    T.predictorFamily.FiniteIndexRepresentativeCover (2 ^ (r + 2 * k + 1)) := by
  exact h.targetData.finiteIndexRepresentativeCover_twoMul

/-- The same ZAB data yields a finite quotient-code presentation. -/
theorem finitePredictorQuotient
    (h : ZABDecisionListData T zfeat) :
    T.predictorFamily.FinitePredictorQuotient (2 ^ (r + 2 * k + 1)) := by
  exact h.targetData.finitePredictorQuotient_twoMul

/-- The ZAB decision-list structured actual family closes the clocked
finite-learning payload at the concrete visible decision-list budget. -/
theorem clockedKpolyFiniteLearningPayload
    [Fintype Z]
    (h : ZABDecisionListData T zfeat) :
    ClockedKpolyFiniteLearningPayload
      T.predictorFamily (r + 2 * k + 1) clock := by
  exact
    clockedKpolyFiniteLearningPayload_of_exactVisibleCompressionTarget
      (Z := Z) (k := k) (s := r + 2 * k + 1) (clock := clock) (Index := Index)
      h.exactVisibleCompressionTarget

/-- Under a strict budget gap, no ZAB decision-list structured family can have
the full exact-visible Boolean predictor image. -/
theorem not_surjective_predict_of_lt_surfaceCard
    [Fintype Z]
    (h : ZABDecisionListData T zfeat)
    (hs : r + 2 * k + 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective T.predictorFamily.predict := by
  exact h.targetData.not_surjective_predict_of_lt_surfaceCard hs

/-- The concrete ZAB decision-list structure is an instance of the bounded-code
minimal missing assumption at the raw ZAB code length. -/
noncomputable def bitCodeDataRaw
    (h : ZABDecisionListData T zfeat) :
    BitCodeData T (r + (k + k) + 1) where
  codeFamily := rawExactZABDecisionListBitFamily Z r k zfeat
  realized := by
    intro i
    rcases h.realized i with ⟨code, hcode⟩
    refine ⟨sharedAffineDecisionListCodeEquivBitCode (r + (k + k)) code, ?_⟩
    have hlocal :
        T.localRule i =
          rawExactZABDecisionListPredict
            (Z := Z) (r := r) (k := k) zfeat code := by
      simpa [ActualSwitchedLocalInterface.predictorFamily] using hcode
    exact
      (rawExactZABDecisionListBitFamily_decode_code
        (Z := Z) (r := r) (k := k) zfeat code).trans hlocal.symm

/-- The concrete ZAB decision-list structure is an instance of the bounded-code
minimal missing assumption at the normalized budget `r + 2*k + 1`. -/
noncomputable def bitCodeData
    (h : ZABDecisionListData T zfeat) :
    BitCodeData T (r + 2 * k + 1) := by
  have hbits : r + (k + k) + 1 = r + 2 * k + 1 := by
    simp [two_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  exact hbits ▸ h.bitCodeDataRaw

end ZABDecisionListData

/-- Explicit per-index ZAB decision-list codes are sufficient to build the
ZAB structured interface.  This is the direct target for a formalized
manuscript construction that computes one bounded local rule per output index. -/
noncomputable def zabDecisionListDataOfCodes
    {r : ℕ}
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (zfeat : Z → BitVec r)
    (codes : Index → SharedAffineDecisionListCode (r + (k + k)))
    (hcodes :
      ∀ i,
        T.localRule i =
          rawExactZABDecisionListPredict
            (Z := Z) (r := r) (k := k) zfeat (codes i)) :
    ZABDecisionListData T zfeat where
  realized := by
    intro i
    refine ⟨codes i, ?_⟩
    simpa [ActualSwitchedLocalInterface.predictorFamily] using hcodes i

/-- Equality to the concrete shared `(zfeat(z), a, b)` ERM-selected family is
one route into the ZAB structured actual-local interface. -/
noncomputable def zabDecisionListData_of_eq_exactZABDecisionListERMFamily
    {r : ℕ}
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (zfeat : Z → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (hT :
      T.predictorFamily =
        exactZABDecisionListERMFamily
          (Z := Z) (r := r) (k := k) (Index := Index) zfeat samples) :
    ZABDecisionListData T zfeat := by
  refine ⟨?_⟩
  intro i
  rcases
    (exactZABDecisionListERMTargetData
      (Z := Z) (r := r) (k := k) (Index := Index) zfeat samples).realized i
    with ⟨code, hcode⟩
  exact ⟨code, by simpa [hT] using hcode⟩

/-- Therefore equality to the concrete shared ERM-selected family supplies the
bounded-code minimal missing assumption directly. -/
noncomputable def bitCodeData_of_eq_exactZABDecisionListERMFamily
    {r : ℕ}
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (zfeat : Z → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (hT :
      T.predictorFamily =
        exactZABDecisionListERMFamily
          (Z := Z) (r := r) (k := k) (Index := Index) zfeat samples) :
    BitCodeData T (r + 2 * k + 1) :=
  (zabDecisionListData_of_eq_exactZABDecisionListERMFamily
    (Z := Z) (k := k) (Index := Index) (Block := Block)
    T zfeat samples hT).bitCodeData

/-- Bit-valued exact ERM equality is the identity-extractor specialization of
the ZAB structured actual-local interface. -/
noncomputable def zabDecisionListData_of_eq_bitVecZABDecisionListERMFamily
    {r : ℕ}
    (T : ActualSwitchedLocalInterface (BitVec r) k Index Block)
    (samples :
      Index → Sample (ExactVisiblePostSwitchSurface (BitVec r) k) Bool)
    (hT :
      T.predictorFamily =
        bitVecZABDecisionListERMFamily
          (r := r) (k := k) (Index := Index) samples) :
    ZABDecisionListData T identityZExtractor := by
  exact
    zabDecisionListData_of_eq_exactZABDecisionListERMFamily
      (Z := BitVec r) (r := r) (k := k) (Index := Index) (Block := Block)
      T identityZExtractor samples (by
        simpa [bitVecZABDecisionListERMFamily] using hT)

/-- The bit-valued exact ERM equality also supplies the bounded-code minimal
missing assumption directly. -/
noncomputable def bitCodeData_of_eq_bitVecZABDecisionListERMFamily
    {r : ℕ}
    (T : ActualSwitchedLocalInterface (BitVec r) k Index Block)
    (samples :
      Index → Sample (ExactVisiblePostSwitchSurface (BitVec r) k) Bool)
    (hT :
      T.predictorFamily =
        bitVecZABDecisionListERMFamily
          (r := r) (k := k) (Index := Index) samples) :
    BitCodeData T (r + 2 * k + 1) :=
  (zabDecisionListData_of_eq_bitVecZABDecisionListERMFamily
    (k := k) (Index := Index) (Block := Block) T samples hT).bitCodeData

end ActualSwitchedLocalInterface

section FullRuleExclusion

variable {Z : Type v} {k s r : ℕ}

/-- The bounded-code strengthening is not an arbitrary restatement: below the
truth-table budget it rules out the full-rule actual-local counterexample. -/
theorem fullRuleActualSwitchedLocalInterface_not_bitCodeData_of_lt_surfaceCard
    [Fintype Z]
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.BitCodeData
          (fullRuleActualSwitchedLocalInterface Z k) s) := by
  rintro ⟨hcode⟩
  exact
    fullRuleActualSwitchedLocalInterface_not_finitePredictorCover_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) hs
      hcode.finitePredictorCover

/-- Likewise, the concrete ZAB decision-list strengthening rules out the
full-rule actual-local counterexample whenever its visible code budget is below
the exact visible truth-table budget. -/
theorem fullRuleActualSwitchedLocalInterface_not_zabDecisionListData_of_lt_surfaceCard
    [Fintype Z]
    (zfeat : Z → BitVec r)
    (hs : r + 2 * k + 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.ZABDecisionListData
          (fullRuleActualSwitchedLocalInterface Z k) zfeat) := by
  rintro ⟨hzab⟩
  exact
    hzab.not_surjective_predict_of_lt_surfaceCard hs
      (fullRuleActualSwitchedLocalInterface_surjective Z k)

end FullRuleExclusion

end Mettapedia.Computability.PNP
