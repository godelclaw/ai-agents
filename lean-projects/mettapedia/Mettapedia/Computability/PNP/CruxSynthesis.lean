import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundation
import Mettapedia.Computability.PNP.AsymmetryBudgetObstruction
import Mettapedia.Computability.PNP.WeightAsymmetryObstruction
import Mettapedia.Computability.PNP.ResidualSideInformationObstruction
import Mettapedia.Computability.PNP.ResidualSideInformationResolutionCost
import Mettapedia.Computability.PNP.PostSwitchResidualWitness
import Mettapedia.Computability.PNP.PostSwitchRandomizedResidualObstruction
import Mettapedia.Computability.PNP.ClockedKpolyBridgeEquivalence
import Mettapedia.Computability.PNP.ExactVisibleImageBudget
import Mettapedia.Computability.PNP.ClockedKpolyGapAssessment
import Mettapedia.Computability.PNP.ClockedKpolyActualGapClosure
import Mettapedia.Computability.PNP.ActualSwitchedLocalSupportObstruction
import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleMajorityObstruction
import Mettapedia.Computability.PNP.ActualSwitchedLocalPluginSampleMajoritySparseThresholdERMObstruction
import Mettapedia.Computability.PNP.ActualSwitchedLocalBitFallbackWrapperSparseThresholdERMObstruction
import Mettapedia.Computability.PNP.ActualSwitchedLocalBitFallbackWrapperSparseThresholdERMRecoveryHeavyRegionCharacterization
import Mettapedia.Computability.PNP.BadCodeAgreementObstruction
import Mettapedia.Computability.PNP.PNPv13EvidenceNormalization
import Mettapedia.Computability.PNP.PNPv13TraceCapture
import Mettapedia.Computability.PNP.PNPv13TraceCaptureImageBudgetObstruction
import Mettapedia.Computability.PNP.PNPv13RandomCoinTraceCapture
import Mettapedia.Computability.PNP.PNPv13AtomicEvidenceBudgetExactnessReduction
import Mettapedia.Computability.PNP.PNPv13ACCEIEnvelope
import Mettapedia.Computability.PNP.PNPv13ManuscriptCNFReadout
import Mettapedia.Computability.PNP.PNPv13RouteSynthesis
import Mettapedia.Computability.PNP.PNPv13ForcedStepObstruction
import Mettapedia.Computability.PNP.PNPv13FieldRefinement
import Mettapedia.Computability.PNP.ProductSuccessKpolyBridgeObstruction
import Mettapedia.Computability.PNP.GlobalWeaknessObstruction
import Mettapedia.Computability.PNP.ABDecisionListObstruction
import Mettapedia.Computability.PNP.SharedABFeatureObstruction
import Mettapedia.Computability.PNP.ABVisibleInvariantSurjectivityObstruction
import Mettapedia.Computability.PNP.CanonicalZABERMInterface

/-!
# PNP crux synthesis ledger

This file is a meta-synthesis layer for the current PNP crux work.  It does
not add another conditioning refinement.  Instead it records the exact
stop-grade audit discipline used by the surrounding paper: a packet can only be
called route-stopping when it covers every live repair class named by the
ledger.

The current PNP packet covers several deterministic same-route obstruction
families, the same-source finite-count approximate-decorrelation subcase, the
finite-coin same-source stack, and the abstract clocked finite-uniform counting
kernel.  The same ledger records support-sensitive finite-coin randomized
residual obstructions as a narrow subledger.  It still leaves residual side
information, broad randomized residual objects, broad approximate
decorrelation, and the remaining manuscript-specific `Kpoly` realization bridge
outside the formal block.  The theorems below record that this packet is
therefore not stop-grade.
-/

namespace Mettapedia.Computability.PNP

open Mettapedia.GSLT.Meredith.WeaknessBridge
open scoped ENNReal BigOperators

universe u v w z

/-- Coarse repair classes that matter to the current PNP crux-status audit. -/
inductive PNPRepairClass where
  /-- Same-source Boolean recodings of a conditioned bit. -/
  | sameSourceBooleanRecoding
  /-- Same-source deterministic fibers into an arbitrary decidable codomain. -/
  | sameSourceDeterministicFiber
  /-- Repeated positive-mass pivot in the v13 fielded switching route. -/
  | repeatedPositiveFieldedPivot
  /-- Positive-mass accumulated histories whose next success event is already
  logically forced, even without literal event repetition. -/
  | forcedPositiveFieldedStep
  /-- Concrete fixed-field bad cell in the v13 switching route. -/
  | fixedFieldBadCell
  /-- Refining a bad field cell without changing the underlying balance defect. -/
  | fieldRefinementOfBadCell
  /-- Invariant-projection or invariant-score advantage repairs. -/
  | invariantScoreRepair
  /-- Bounded side-channel resolution repairs. -/
  | boundedSideChannelRepair
  /-- Short global decoder repairs without local readout constancy. -/
  | shortGlobalDecoderRepair
  /-- v13 CD evidence-normalization repairs that must classify every
  target-relevant non-neutral atom as safe-buffer or hidden-gauge. -/
  | cdEvidenceNormalization
  /-- v13 trace-capture repairs that replace target-relevant observers by
  finite traces. -/
  | traceCaptureFactorization
  /-- v13 atomic-evidence budget repairs that bound coordinate-summed cost
  without double-counting positive-cost atoms. -/
  | atomicEvidenceBudget
  /-- v13 ACCEI/PNLD repairs that must instantiate finite Markov pruning and
  the finite sequential product skeleton. -/
  | acceiEnvelopeProduct
  /-- Finite counting kernel for a clocked `s`-bit decoder family. -/
  | clockedFiniteUniformKernel
  /-- Residual side information not determined by the conditioned source bit. -/
  | residualSideInformation
  /-- Randomized post-conditioning residual objects. -/
  | randomizedResidual
  /-- Finite-count approximate decorrelation on same-source coupled,
  anti-coupled, or deterministic distinguishing-fiber surfaces. -/
  | sameSourceFiniteCountApproximation
  /-- Quantitatively approximate decorrelation replacing exact finite counting. -/
  | approximateDecorrelation
  /-- Remaining manuscript-specific exact-visible / clocked `Kpoly` bridge
  from product success. -/
  | kpolyCompressionBridge
  deriving DecidableEq, Repr

/-- A crux packet is represented by the repair classes it covers. -/
structure PNPCruxPacket where
  covers : PNPRepairClass → Prop

/-- A packet is stop-grade only if it covers every repair class in this ledger. -/
def PNPCruxPacket.StopGrade (packet : PNPCruxPacket) : Prop :=
  ∀ repair : PNPRepairClass, packet.covers repair

/-- One packet extends another when it covers every repair class covered by the
base packet. -/
def PNPCruxPacket.Extends (extension base : PNPCruxPacket) : Prop :=
  ∀ repair : PNPRepairClass, base.covers repair → extension.covers repair

/-- A packet covers every repair class in a named finite list. -/
def PNPCruxPacket.CoversList (packet : PNPCruxPacket)
    (repairs : List PNPRepairClass) : Prop :=
  ∀ repair : PNPRepairClass, repair ∈ repairs → packet.covers repair

/-- Missing any ledger repair class rules out stop-grade status. -/
theorem PNPCruxPacket.not_stopGrade_of_not_covers
    {packet : PNPCruxPacket} {repair : PNPRepairClass}
    (hmiss : ¬ packet.covers repair) :
    ¬ packet.StopGrade := by
  intro hstop
  exact hmiss (hstop repair)

/-- The v13 repeated-positive-fielded-pivot ledger entry is covered only by a
real route theorem: a repeated positive fielded pivot blocks both the fixed-field
certificate route and the equivalent same-cell matching route. -/
def V13RepeatedPositiveFieldedPivotCoverage : Prop :=
  ∀ {Ω : Type} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)},
    V13RepeatedPositiveFieldedPivotFrom hist items →
      (¬ V13FieldSwitchingInstantiatedFrom hist items) ∧
        ¬ V13FieldSwitchingFailureMatchingFrom hist items

/-- The v13 forced-positive-fielded-step ledger entry is covered only by the
route result showing that a logically forced next success event on positive
accumulated mass blocks both fixed-field formulations. -/
def V13ForcedPositiveFieldedStepCoverage : Prop :=
  ∀ {Ω : Type} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)},
    V13ForcedPositiveFieldedStepFrom hist items →
      (¬ V13FieldSwitchingInstantiatedFrom hist items) ∧
        ¬ V13FieldSwitchingFailureMatchingFrom hist items

/-- The v13 fixed-field bad-cell ledger entry is covered only by the theorem
that a localized bad cell blocks both fixed-field formulations. -/
def V13FieldedBadCellCoverage : Prop :=
  ∀ {Ω : Type} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)},
    V13FieldedBadCellFrom hist items →
      (¬ V13FieldSwitchingInstantiatedFrom hist items) ∧
        ¬ V13FieldSwitchingFailureMatchingFrom hist items

/-- The field-refinement ledger entry is covered only by the theorem that a bad
coarse cell survives every finite refinement and blocks the refined prefix
certificate. -/
def V13FieldRefinementBadCellCoverage : Prop :=
  ∀ {Ω : Type} [Fintype Ω]
    {fine coarse : V13HistoryField Ω}
    (refn : V13HistoryFieldRefinement fine coarse)
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    {coarseCell : coarse.Cell},
    v13ConcreteFailureCount (Ω := Ω) hist step coarse.cellOf coarseCell <
        v13ConcreteSuccessCount (Ω := Ω) hist step coarse.cellOf coarseCell →
      (∃ fineCell : fine.Cell,
        refn.project fineCell = coarseCell ∧
          v13ConcreteFailureCount (Ω := Ω) hist step fine.cellOf fineCell <
            v13ConcreteSuccessCount (Ω := Ω) hist step fine.cellOf fineCell) ∧
        ¬ V13FieldPrefixInstantiation fine hist step

@[simp] theorem v13RepeatedPositiveFieldedPivotCoverage :
    V13RepeatedPositiveFieldedPivotCoverage := by
  intro Ω _FintypeΩ hist items hrep
  exact v13RepeatedPositiveFieldedPivot_blocks_fixedFieldRoute hrep

@[simp] theorem v13ForcedPositiveFieldedStepCoverage :
    V13ForcedPositiveFieldedStepCoverage := by
  intro Ω _FintypeΩ hist items hforced
  exact v13ForcedPositiveFieldedStep_blocks_fixedFieldRoute hforced

@[simp] theorem v13FieldedBadCellCoverage :
    V13FieldedBadCellCoverage := by
  intro Ω _FintypeΩ hist items hbad
  exact
    ⟨not_v13FieldSwitchingInstantiatedFrom_of_fieldedBadCell hbad,
      not_v13FieldSwitchingFailureMatchingFrom_of_fieldedBadCell hbad⟩

@[simp] theorem v13FieldRefinementBadCellCoverage :
    V13FieldRefinementBadCellCoverage := by
  intro Ω _FintypeΩ fine coarse refn hist step coarseCell hbad
  exact
    ⟨exists_refined_bad_cell_of_bad_coarse_cell refn hbad,
      not_v13FieldPrefixInstantiation_of_refinement_bad_coarse_cell refn hbad⟩

/-- The broad packet's clocked finite-uniform kernel entry is covered by the
proved equivalence between the bundled clocked finite-learning payload and a
finite predictor-image cover.  This is only the abstract counting kernel, not
the manuscript-specific small-image theorem. -/
def ClockedFiniteUniformKernelCoverage : Prop :=
  ∀ {Z : Type} [Fintype Z] {k s clock : ℕ} {Index : Type}
    {G : ExactVisibleSwitchedFamily Z k Index},
    ClockedKpolyFiniteLearningPayload G s clock ↔
      G.FinitePredictorCover (2 ^ s)

@[simp] theorem clockedFiniteUniformKernelCoverage :
    ClockedFiniteUniformKernelCoverage := by
  intro Z _FintypeZ k s clock Index G
  exact clockedKpolyFiniteLearningPayload_iff_finitePredictorCover

/-- The short global decoder repair is covered only in the precise sense that a
concrete CNF countermodel now separates favorable-witness correctness from
arbitrary SAT-search-output correctness.  This does not prove any manuscript
CNF construction ambiguous; it pins the missing readout-constancy theorem that
such a construction must supply. -/
def ShortGlobalDecoderRepairCoverage : Prop :=
  (∀ readout : ConcreteCNF.Assignment (Fin 1) → Bool,
    (∃ msg : Bool,
      CorrectForAllSatSearchOutputs
        (ConcreteCNF.IsSatFormula oneVarTautologyCNF) readout msg) ↔
      SingleMessageReadout
        (ConcreteCNF.IsSatFormula oneVarTautologyCNF) readout) ∧
  (¬ ∃ msg : Bool,
    CorrectForAllSatSearchOutputs
      (ConcreteCNF.IsSatFormula oneVarTautologyCNF) oneVarReadout msg) ∧
    CorrectForSomeSatSearchOutput
      (ConcreteCNF.IsSatFormula oneVarTautologyCNF) oneVarReadout false ∧
    CorrectForSomeSatSearchOutput
      (ConcreteCNF.IsSatFormula oneVarTautologyCNF) oneVarReadout true

@[simp] theorem shortGlobalDecoderRepairCoverage :
    ShortGlobalDecoderRepairCoverage := by
  exact
    ⟨by
      intro readout
      exact
        cnf_exists_correctForAllSatSearchOutputs_iff_singleMessageReadout_of_satisfying_assignment
          (formula := oneVarTautologyCNF) (readout := readout)
          oneVarTautologyCNF_satisfied_false,
      oneVarTautologyCNF_not_exists_correctForAllSatSearchOutputs,
      oneVarTautologyCNF_correctForSomeSatSearchOutput_false_and_true.1,
      oneVarTautologyCNF_correctForSomeSatSearchOutput_false_and_true.2⟩

/-- Route-coverage anchor: under the natural CNF extraction-completeness and
supported-satisfiability directions, the manuscript-shaped arbitrary-output
SAT-search repair is exactly the semantic single-message promise. -/
theorem shortGlobalDecoderCoverage_anchor_supported_sat_search_equiv_singleMessagePromise
    {Public : Type u} {Var : Public → Type v}
    {Witness : Public → Type w} {Message : Type z}
    (D : ManuscriptCNFReadoutData Public Var Witness Message)
    (hsat : D.SupportedCNFSatisfiable)
    (hcomplete : D.CNFExtractionComplete) :
    D.SupportedArbitraryOutputSATSearchCorrect ↔ D.SingleMessagePromise := by
  exact D.supportedArbitraryOutputSATSearchCorrect_iff_singleMessagePromise hsat hcomplete

/-- Route-coverage anchor: extraction completeness is not a cosmetic premise.
There is a one-variable manuscript-shaped CNF whose CNF projection is constant
and therefore supports arbitrary-output SAT-search correctness, while an
unrepresented semantic witness still refutes the semantic single-message
promise. -/
theorem shortGlobalDecoderCoverage_anchor_incomplete_extraction_countermodel :
    unrepresentedOneVarManuscriptCNFReadoutData.SupportedArbitraryOutputSATSearchCorrect ∧
      ¬ unrepresentedOneVarManuscriptCNFReadoutData.SingleMessagePromise ∧
      ¬ unrepresentedOneVarManuscriptCNFReadoutData.CNFExtractionComplete := by
  exact
    ⟨unrepresentedOneVarManuscriptCNFReadoutData_supportedArbitraryOutputSATSearchCorrect,
      unrepresentedOneVarManuscriptCNFReadoutData_not_singleMessagePromise,
      unrepresentedOneVarManuscriptCNFReadoutData_not_cnfExtractionComplete⟩

/-- The v13 evidence-normalization ledger entry is covered only by the exact
residual-atom boundary: safe/gauge normalization is equivalent to absence of a
target-relevant non-neutral atom outside both classes. -/
def V13EvidenceNormalizationCoverage : Prop :=
  ∀ {Atom : Type} (S : V13EvidenceNormalizationSurface Atom),
    S.NormalizesNonNeutral ↔ ¬ S.HasResidualAtom

@[simp] theorem v13EvidenceNormalizationCoverage :
    V13EvidenceNormalizationCoverage := by
  intro Atom S
  exact V13EvidenceNormalizationSurface.normalizesNonNeutral_iff_not_hasResidualAtom S

/-- Route-coverage anchor: a residual atom with positive score blocks both full
safe/gauge normalization and the positive-score weakening. -/
theorem v13EvidenceNormalizationCoverage_anchor_toyResidual_blocks :
    ¬ v13ToyEvidenceSurface.NormalizesNonNeutral ∧
      v13ToyEvidenceSurface.PositiveResidualScore v13ToyEvidenceScore ∧
      ¬ v13ToyEvidenceSurface.PositiveAtomsCovered v13ToyEvidenceScore := by
  exact
    ⟨v13ToyEvidenceSurface_not_normalizesNonNeutral,
      v13ToyEvidenceSurface_positiveResidualScore,
      v13ToyEvidenceSurface_not_positiveAtomsCovered⟩

/-- The v13 trace-capture ledger entry is covered only by the full finite
quotient boundary: deterministic and randomized observers are decodable exactly
when they are constant on target-relevant trace fibers; capturing all Boolean
observers makes the restricted trace map injective; and any finite trace
alphabet or induced Boolean decoder space below the target-relevant support
already blocks universal Boolean capture. -/
def V13TraceCaptureFactorizationCoverage : Prop :=
  (∀ {State Trace Output : Type} [Inhabited Output]
    (S : V13TraceCaptureSurface State Trace) (observer : State → Output),
    S.ObserverTraceDecodable observer ↔
      S.ObserverConstantOnTraceFibers observer) ∧
  (∀ {State Trace Coin Output : Type} [Inhabited Output]
    (S : V13TraceCaptureSurface State Trace)
    (observer : State → Coin → Output),
    S.RandomObserverTraceDecodable observer ↔
      S.RandomObserverConstantOnTraceFibers observer) ∧
  (∀ {State Trace : Type} [DecidableEq State]
    (S : V13TraceCaptureSurface State Trace),
    S.CapturesAllBoolObservers ↔ Function.Injective S.traceOnRelevant) ∧
  (∀ {State Trace : Type} [DecidableEq State]
    (S : V13TraceCaptureSurface State Trace)
    [Fintype (Subtype S.targetRelevant)] [Fintype Trace],
    S.CapturesAllBoolObservers →
      Fintype.card (Subtype S.targetRelevant) ≤ Fintype.card Trace) ∧
  (∀ {State Trace : Type} [DecidableEq State]
    (S : V13TraceCaptureSurface State Trace)
    [Fintype (Subtype S.targetRelevant)] [Fintype Trace],
    Fintype.card Trace < Fintype.card (Subtype S.targetRelevant) →
      ¬ S.CapturesAllBoolObservers) ∧
  (∀ {State Trace : Type} [DecidableEq State]
    (S : V13TraceCaptureSurface State Trace)
    [Fintype (Subtype S.targetRelevant)] [Fintype Trace],
    S.CapturesAllBoolObservers →
      2 ^ Fintype.card (Subtype S.targetRelevant) ≤ 2 ^ Fintype.card Trace) ∧
  ∀ {State Trace : Type} [DecidableEq State]
    (S : V13TraceCaptureSurface State Trace)
    [Fintype (Subtype S.targetRelevant)] [Fintype Trace],
    2 ^ Fintype.card Trace < 2 ^ Fintype.card (Subtype S.targetRelevant) →
      ¬ S.CapturesAllBoolObservers

@[simp] theorem v13TraceCaptureFactorizationCoverage :
    V13TraceCaptureFactorizationCoverage := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro State Trace Output _InhabitedOutput S observer
    exact
      V13TraceCaptureSurface.observerTraceDecodable_iff_constantOnTraceFibers
        S observer
  · intro State Trace Coin Output _InhabitedOutput S observer
    exact
      V13TraceCaptureSurface.randomObserverTraceDecodable_iff_constantOnTraceFibers
        S observer
  · intro State Trace _DecidableEqState S
    exact
      V13TraceCaptureSurface.capturesAllBoolObservers_iff_traceOnRelevant_injective
        S
  · intro State Trace _DecidableEqState S _instRelevant _instTrace hcapture
    exact
      V13TraceCaptureSurface.relevantStateCard_le_traceCard_of_capturesAllBoolObservers
        (S := S) inferInstance inferInstance hcapture
  · intro State Trace _DecidableEqState S _instRelevant _instTrace hcard
    exact
      V13TraceCaptureSurface.not_capturesAllBoolObservers_of_traceCard_lt_relevantStateCard
        (S := S) inferInstance inferInstance hcard
  · intro State Trace _DecidableEqState S _instRelevant _instTrace hcapture
    exact
      V13TraceCaptureSurface.boolClassifierCard_le_traceClassifierCard_of_capturesAllBoolObservers
        (S := S) hcapture
  · intro State Trace _DecidableEqState S _instRelevant _instTrace hcard
    exact
      V13TraceCaptureSurface.not_capturesAllBoolObservers_of_traceClassifierCard_lt
        (S := S) hcard

/-- Route-coverage anchor: a collapsed target-relevant trace fiber with a
Boolean observer conflict blocks both that observer and universal Boolean
observer capture. -/
theorem v13TraceCaptureFactorizationCoverage_anchor_collapsedTrace_blocks :
    ¬ v13CollapsedTraceSurface.ObserverTraceDecodable v13ToyTraceObserver ∧
      v13CollapsedTraceSurface.RelevantTraceCollision ∧
      ¬ v13CollapsedTraceSurface.CapturesAllBoolObservers := by
  exact
    ⟨v13CollapsedTraceSurface_not_observerTraceDecodable,
      v13CollapsedTraceSurface_relevantTraceCollision,
      v13CollapsedTraceSurface_not_capturesAllBoolObservers⟩

/-- Route-coverage anchor: adding a coin parameter does not repair a collapsed
target-relevant trace fiber; one conflicting coin slice still blocks randomized
trace capture. -/
theorem v13TraceCaptureFactorizationCoverage_anchor_collapsedRandomTrace_blocks :
    v13CollapsedTraceSurface.RandomObserverSameTraceConflict
        v13ToyRandomTraceObserver ∧
      ¬ v13CollapsedTraceSurface.RandomObserverTraceDecodable
        v13ToyRandomTraceObserver := by
  exact
    ⟨v13CollapsedTraceSurface_randomSameTraceConflict,
      v13CollapsedTraceSurface_not_randomObserverTraceDecodable⟩

/-- The v13 atomic-evidence budget ledger entry is covered only at the full
finite exactness boundary: no-double-counting gives the upper budget bound,
charging every positive-cost atom gives the lower bound, strict under/over
budget localize to omitted/double-counted positive-cost atoms, the full
exactness-side conjunction gives exact equality, and the cancellation surface
shows that exact equality plus equivalence of the two side conditions is still
not enough. -/
def V13AtomicEvidenceBudgetCoverage : Prop :=
  ((∀ {Coord Atom : Type} [Fintype Coord] [Fintype Atom]
      (S : V13AtomicEvidenceBudgetSurface Coord Atom)
      [DecidableRel S.charges],
        S.NoDoubleCounting → S.coordinateSummedCost ≤ S.atomBudget) ∧
    (∀ {Coord Atom : Type} [Fintype Coord] [Fintype Atom]
      (S : V13AtomicEvidenceBudgetSurface Coord Atom)
      [DecidableRel S.charges],
        S.AllPositiveCostAtomsCharged → S.atomBudget ≤ S.coordinateSummedCost) ∧
    (∀ {Coord Atom : Type} [Fintype Coord] [Fintype Atom]
      (S : V13AtomicEvidenceBudgetSurface Coord Atom)
      [DecidableRel S.charges],
        S.atomBudget < S.coordinateSummedCost → S.DoubleCountedAtom) ∧
    ∀ {Coord Atom : Type} [Fintype Coord] [Fintype Atom]
      (S : V13AtomicEvidenceBudgetSurface Coord Atom)
      [DecidableRel S.charges],
      S.coordinateSummedCost < S.atomBudget → S.MissedPositiveCostAtom) ∧
  ((∀ {Coord Atom : Type} [Fintype Coord] [Fintype Atom]
      (S : V13AtomicEvidenceBudgetSurface Coord Atom)
      [DecidableRel S.charges],
        S.ExactnessSideConditions → S.coordinateSummedCost = S.atomBudget) ∧
    (∀ {Coord Atom : Type} [Fintype Coord] [Fintype Atom]
      (S : V13AtomicEvidenceBudgetSurface Coord Atom)
      [DecidableRel S.charges],
        S.coordinateSummedCost = S.atomBudget →
          (S.ExactnessSideConditions ↔ S.NoDoubleCounting)) ∧
    ∀ {Coord Atom : Type} [Fintype Coord] [Fintype Atom]
      (S : V13AtomicEvidenceBudgetSurface Coord Atom)
      [DecidableRel S.charges],
      S.coordinateSummedCost = S.atomBudget →
        (S.ExactnessSideConditions ↔ S.AllPositiveCostAtomsCharged)) ∧
  ¬ ∀ {Coord Atom : Type} [Fintype Coord] [Fintype Atom]
      (S : V13AtomicEvidenceBudgetSurface Coord Atom)
      [DecidableRel S.charges],
      S.coordinateSummedCost = S.atomBudget →
        (S.NoDoubleCounting ↔ S.AllPositiveCostAtomsCharged) →
        S.ExactnessSideConditions

@[simp] theorem v13AtomicEvidenceBudgetCoverage :
    V13AtomicEvidenceBudgetCoverage := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro Coord Atom _FintypeCoord _FintypeAtom S _DecidableRel hno
      exact
        V13AtomicEvidenceBudgetSurface.coordinateSummedCost_le_atomBudget_of_noDoubleCounting
          S hno
    · intro Coord Atom _FintypeCoord _FintypeAtom S _DecidableRel hall
      exact
        V13AtomicEvidenceBudgetSurface.atomBudget_le_coordinateSummedCost_of_allPositiveCostAtomsCharged
          S hall
    · intro Coord Atom _FintypeCoord _FintypeAtom S _DecidableRel hlt
      exact
        V13AtomicEvidenceBudgetSurface.doubleCountedAtom_of_atomBudget_lt_coordinateSummedCost
          S hlt
    · intro Coord Atom _FintypeCoord _FintypeAtom S _DecidableRel hlt
      exact
        V13AtomicEvidenceBudgetSurface.missedPositiveCostAtom_of_coordinateSummedCost_lt_atomBudget
          S hlt
  · refine ⟨?_, ?_, ?_⟩
    · intro Coord Atom _FintypeCoord _FintypeAtom S _DecidableRel hexact
      exact
        V13AtomicEvidenceBudgetSurface.coordinateSummedCost_eq_atomBudget_of_exactnessSideConditions
          S hexact
    · intro Coord Atom _FintypeCoord _FintypeAtom S _DecidableRel heq
      exact
        V13AtomicEvidenceBudgetSurface.exactnessSideConditions_iff_noDoubleCounting_of_coordinateSummedCost_eq_atomBudget
          S heq
    · intro Coord Atom _FintypeCoord _FintypeAtom S _DecidableRel heq
      exact
        V13AtomicEvidenceBudgetSurface.exactnessSideConditions_iff_allPositiveCostAtomsCharged_of_coordinateSummedCost_eq_atomBudget
          S heq
  · exact
      not_forall_coordinateSummedCost_eq_atomBudget_and_sideConditionEquivalence_implies_exactnessSideConditions

/-- Route-coverage anchor: a one-atom/two-coordinate surface proves that the
once-per-atom budget can undercount the coordinate-summed cost by a factor of
the charge multiplicity. -/
theorem v13AtomicEvidenceBudgetCoverage_anchor_doubleCountedAtom_blocks :
    v13DoubleCountedBudgetSurface.atomBudget = 1 ∧
      v13DoubleCountedBudgetSurface.coordinateSummedCost = 2 ∧
      ¬ v13DoubleCountedBudgetSurface.NoDoubleCounting ∧
      v13DoubleCountedBudgetSurface.atomBudget <
        v13DoubleCountedBudgetSurface.coordinateSummedCost := by
  exact
    ⟨v13DoubleCountedBudgetSurface_atomBudget,
      v13DoubleCountedBudgetSurface_coordinateSummedCost,
      v13DoubleCountedBudgetSurface_not_noDoubleCounting,
      v13DoubleCountedBudgetSurface_atomBudget_lt_coordinateSummedCost⟩

/-- Route-coverage anchor: the cancellation surface shows that exact aggregate
budget equality plus equivalence of the two structural side conditions still
does not certify the full exactness conjunction. -/
theorem v13AtomicEvidenceBudgetCoverage_anchor_cancellation_blocks :
    v13CancellationBudgetSurface.coordinateSummedCost =
        v13CancellationBudgetSurface.atomBudget ∧
      (v13CancellationBudgetSurface.NoDoubleCounting ↔
        v13CancellationBudgetSurface.AllPositiveCostAtomsCharged) ∧
      ¬ v13CancellationBudgetSurface.ExactnessSideConditions := by
  exact
    v13CancellationBudgetSurface_exact_budget_with_sideConditionEquivalence_without_exactnessSideConditions

/-- The v13 ACCEI/PNLD envelope-product ledger entry is covered only at the
finite skeleton level: finite Markov pruning bounds bad coordinates by total
envelope budget, lower-bounds the pruned good-coordinate count by the finite
Markov loss, records a two-coordinate sharpness example for that loss, any
sequential one-step rate proof implies the matching tower-product count bound,
and every product-bound violation localizes to one failed prefix rate step. -/
def V13ACCEIEnvelopeProductCoverage : Prop :=
  (∀ {ι : Type u} [Fintype ι] (η : ι → ℕ) (threshold budget : ℕ),
      (∑ i, η i) ≤ budget →
        acceiBadCount ι η threshold * (threshold + 1) ≤ budget) ∧
    (∀ {ι : Type u} [Fintype ι] (η : ι → ℕ) (threshold budget : ℕ),
      (∑ i, η i) ≤ budget →
        Fintype.card ι - budget / (threshold + 1) ≤
          acceiGoodCount ι η threshold) ∧
    (∀ {ι : Type u} [Fintype ι] (η : ι → ℕ) (threshold budget : ℕ),
      (∑ i, η i) ≤ budget →
        budget / (threshold + 1) < Fintype.card ι →
          ∃ i : ι, η i ≤ threshold) ∧
    (∀ threshold : ℕ,
      acceiBadCount Bool (oneGoodOneBadACCEIEnvelope threshold) threshold *
          (threshold + 1) =
        ∑ b : Bool, oneGoodOneBadACCEIEnvelope threshold b) ∧
    (∀ threshold : ℕ,
      Fintype.card Bool - (threshold + 1) / (threshold + 1) =
          acceiGoodCount Bool (oneGoodOneBadACCEIEnvelope threshold) threshold ∧
        ¬ ∀ b : Bool, oneGoodOneBadACCEIEnvelope threshold b ≤ threshold) ∧
    (∀ {Ω : Type u} [Fintype Ω]
      (hist rest : List (FiniteEvent Ω)) (numerator denominator : ℕ),
        SequentialRateAdmissibleFrom hist rest numerator denominator →
          denominator ^ rest.length *
              finiteHistoryCount Ω (hist ++ rest) ≤
            numerator ^ rest.length * finiteHistoryCount Ω hist) ∧
    (∀ {Ω : Type u} [Fintype Ω]
      {hist rest : List (FiniteEvent Ω)} {numerator denominator : ℕ},
        ¬ (denominator ^ rest.length *
              finiteHistoryCount Ω (hist ++ rest) ≤
            numerator ^ rest.length * finiteHistoryCount Ω hist) →
          ¬ SequentialRateAdmissibleFrom hist rest numerator denominator) ∧
      ∀ {Ω : Type u} [Fintype Ω]
        {hist events : List (FiniteEvent Ω)} {numerator denominator : ℕ},
          ¬ (denominator ^ events.length *
                finiteHistoryCount Ω (hist ++ events) ≤
              numerator ^ events.length * finiteHistoryCount Ω hist) →
            ∃ pre E suffix,
              events = pre ++ E :: suffix ∧
                ¬ PrefixRateStep (hist ++ pre) E numerator denominator

@[simp] theorem v13ACCEIEnvelopeProductCoverage :
    V13ACCEIEnvelopeProductCoverage := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ι _Fintypeι η threshold budget hbudget
    exact acceiBadCount_mul_succ_threshold_le_of_sum_le
      η threshold budget hbudget
  · intro ι _Fintypeι η threshold budget hbudget
    exact
      card_sub_budget_div_succ_threshold_le_acceiGoodCount_of_sum_le
        η threshold budget hbudget
  · intro ι _Fintypeι η threshold budget hbudget hloss
    exact
      exists_accei_good_of_budget_div_succ_threshold_lt_card
        η threshold budget hbudget hloss
  · intro threshold
    exact oneGoodOneBadACCEIEnvelope_markov_badCount_sharp threshold
  · intro threshold
    exact
      ⟨oneGoodOneBadACCEIEnvelope_good_lower_bound_sharp threshold,
        oneGoodOneBadACCEIEnvelope_not_all_good threshold⟩
  · intro Ω _FintypeΩ hist rest numerator denominator hseq
    exact finiteHistory_product_bound_of_sequentialRateFrom
      hist rest numerator denominator hseq
  · intro Ω _FintypeΩ hist rest numerator denominator hbad
    exact not_sequentialRateAdmissibleFrom_of_product_bound_violation hbad
  · intro Ω _FintypeΩ hist events numerator denominator hbad
    exact
      exists_failed_prefixRateStep_at_append_cons_of_product_bound_violation
        hbad

/-- The current accumulated local PNP packet, as of the deterministic-fiber
conditioning and v13 fixed-field audits. -/
def currentPNPLocalCruxPacket : PNPCruxPacket where
  covers
    | .sameSourceBooleanRecoding => True
    | .sameSourceDeterministicFiber => True
    | .repeatedPositiveFieldedPivot => V13RepeatedPositiveFieldedPivotCoverage
    | .forcedPositiveFieldedStep => V13ForcedPositiveFieldedStepCoverage
    | .fixedFieldBadCell => V13FieldedBadCellCoverage
    | .fieldRefinementOfBadCell => V13FieldRefinementBadCellCoverage
    | .invariantScoreRepair => True
    | .boundedSideChannelRepair => True
    | .shortGlobalDecoderRepair => ShortGlobalDecoderRepairCoverage
    | .cdEvidenceNormalization => V13EvidenceNormalizationCoverage
    | .traceCaptureFactorization => V13TraceCaptureFactorizationCoverage
    | .atomicEvidenceBudget => V13AtomicEvidenceBudgetCoverage
    | .acceiEnvelopeProduct => V13ACCEIEnvelopeProductCoverage.{0}
    | .clockedFiniteUniformKernel => ClockedFiniteUniformKernelCoverage
    | .residualSideInformation => False
    | .randomizedResidual => False
    | .sameSourceFiniteCountApproximation => True
    | .approximateDecorrelation => False
    | .kpolyCompressionBridge => False

/-- Repair classes currently covered by the accumulated local PNP packet. -/
def currentPNPCoveredRepairClasses : List PNPRepairClass :=
  [.sameSourceBooleanRecoding,
    .sameSourceDeterministicFiber,
    .repeatedPositiveFieldedPivot,
    .forcedPositiveFieldedStep,
    .fixedFieldBadCell,
    .fieldRefinementOfBadCell,
    .invariantScoreRepair,
    .boundedSideChannelRepair,
    .shortGlobalDecoderRepair,
    .cdEvidenceNormalization,
    .traceCaptureFactorization,
    .atomicEvidenceBudget,
    .acceiEnvelopeProduct,
    .clockedFiniteUniformKernel,
    .sameSourceFiniteCountApproximation]

/-- Repair classes still outside the accumulated local PNP packet. -/
def currentPNPUncoveredRepairClasses : List PNPRepairClass :=
  [.residualSideInformation,
    .randomizedResidual,
    .approximateDecorrelation,
    .kpolyCompressionBridge]

/-- Precise finite-coin subrepair classes covered by the current grassroots
finite-coin stack.  These sit inside the same-source finite-count approximation
surface; they are not broad residual or `Kpoly` closure claims. -/
inductive PNPFiniteCoinSubrepairClass where
  /-- Same-source finite-coin marginal recoding of a Boolean source bit. -/
  | sameSourceFiniteCoinMarginalRecoding
  /-- Balanced fibers are erasure for every decidable output predicate. -/
  | predicateErasure
  /-- Balanced fibers force every Boolean output decoder to be exactly
  half-accurate in aggregate. -/
  | decoderHalfAccuracy
  /-- Each output fiber's finite-count defect is `|Coin|` times its imbalance. -/
  | exactScaledFiberImbalance
  /-- Tolerance below `|Coin|` collapses approximate independence to exact
  balanced fibers. -/
  | subCardinalityToleranceQuantization
  /-- Tolerance below a lower-bounded source/coin imbalance block collapses
  approximate independence to exact balanced fibers. -/
  | sourceLowerBoundToleranceQuantization
  /-- If the coin is retained, tolerance below a source/coin block collapses
  approximate independence to pointwise source-blindness at every coin. -/
  | retainedCoinTolerancePointwiseCollapse
  /-- If side information is retained, tolerance below a source/coin block
  collapses approximate independence to true/false balance inside every
  retained side/output fiber. -/
  | retainedSideToleranceSideFiberBalance
  /-- Source-side nondegeneracy plus a nonempty coin space blocks uniform
  true/false distinguishing fibers at zero tolerance. -/
  | sourceNonconstantUniformFiberZeroBlock
  /-- On nondegenerate source surfaces, zero-tolerance finite-coin output
  independence is equivalent to balanced output fibers. -/
  | sourceNonconstantZeroIffBalanced
  /-- Exact balanced-fiber erasure is preserved by deterministic output
  postprocessing. -/
  | deterministicOutputPostprocessing
  /-- Injective deterministic output postprocessing cannot create balanced
  finite-coin erasure that was not already present. -/
  | injectivePostprocessingErasureEquivalence
  /-- A postprocessor that recovers the original observed finite-coin output on
  the support cannot create finite-coin erasure. -/
  | observedLeftInversePostprocessingErasureEquivalence
  /-- A postprocessor injective on the observed finite-coin support cannot
  create finite-coin erasure. -/
  | observedInjectivePostprocessingErasureEquivalence
  /-- If postprocessing balances an unbalanced finite-coin recoding, it must
  collide two distinct observed original outputs. -/
  | postprocessingObservedOutputCollisionObligation
  /-- If postprocessing balances an unbalanced finite-coin recoding, one
  postprocessed fiber must merge opposite source-bias original outputs. -/
  | postprocessingObservedOppositeBiasCollisionObligation
  /-- Balanced deterministic postprocessing requires exact signed-bias
  cancellation in every postprocessed fiber. -/
  | postprocessingSignedBiasCancellationCertificate
  /-- Postprocessed retained-side tolerance below a source/coin block collapses
  to observed-fiber true/false balance. -/
  | postprocessedSideToleranceObservedFiberBalance
  /-- Any residual observed-fiber imbalance after retained-side postprocessing
  forces a proportional source/coin tolerance lower bound. -/
  | postprocessedSideObservedFiberImbalanceLowerBound
  /-- Below a source/coin block, every downstream predicate on a postprocessed
  retained-side output has equal true/false coin counts. -/
  | postprocessedSidePredicateErasure
  /-- Below a source/coin block, every downstream Boolean decoder on a
  postprocessed retained-side output is exactly half-accurate. -/
  | postprocessedSideDecoderHalfAccuracy
  /-- Below a source/coin block, uniform downstream source recovery after
  retained-side postprocessing is impossible. -/
  | postprocessedSideSourceRecoveryBlock
  /-- Below a source/coin block, postprocessed retained-side independence
  forces a true/false observed support collision. -/
  | postprocessedSideCollisionObligation
  /-- Below a source/coin block, every postprocessed observed coin value must
  have witnesses on both source sides. -/
  | postprocessedSidePointwiseCollisionObligation
  /-- Two-sided pointwise support collisions do not suffice for the
  postprocessed-side preserving coin matching. -/
  | postprocessedSidePointwiseCollisionInsufficient
  /-- One-sided witness maps do not suffice for postprocessed-side preserving
  coin matching unless they are injective, hence bijective. -/
  | postprocessedSideOneSidedCoinMapInsufficient
  /-- Injective one-sided witness maps are exactly the preserving
  postprocessed-side coin-matching obligation. -/
  | postprocessedSideInjectiveWitnessMapEquivalence
  /-- Below a source/coin block, postprocessed observations must provide a
  bijective true/false coin matching preserving every observed value. -/
  | postprocessedSideCoinMatchingObligation
  /-- A single postprocessed observed-fiber multiplicity mismatch blocks the
  coin-matching repair and below-threshold approximate independence. -/
  | postprocessedSideCoinMatchingCardinalityBlock
  /-- A downstream predicate count mismatch blocks the postprocessed-side
  coin-matching repair, covering predicate-only and decoder-only probes. -/
  | postprocessedSideCoinMatchingPredicateBlock
  /-- Neutrality for all downstream predicates is equivalent to the full
  postprocessed-side preserving coin matching. -/
  | postprocessedSidePredicateMatchingEquivalence
  /-- Below a source/coin block, postprocessed approximate independence is
  equivalent to the full preserving coin matching. -/
  | postprocessedSideApproxIndependenceCoinMatchingEquivalence
  /-- Approximate output independence under deterministic postprocessing has
  explicit finite-preimage blowup `τ ↦ m * τ`. -/
  | finitePreimagePostprocessingBlowup
  deriving DecidableEq, Repr

/-- The exact finite-coin subrepair list currently covered by the stack. -/
def currentPNPFiniteCoinCoveredSubrepairs : List PNPFiniteCoinSubrepairClass :=
  [.sameSourceFiniteCoinMarginalRecoding,
    .predicateErasure,
    .decoderHalfAccuracy,
    .exactScaledFiberImbalance,
    .subCardinalityToleranceQuantization,
    .sourceLowerBoundToleranceQuantization,
    .retainedCoinTolerancePointwiseCollapse,
    .retainedSideToleranceSideFiberBalance,
    .sourceNonconstantUniformFiberZeroBlock,
    .sourceNonconstantZeroIffBalanced,
    .deterministicOutputPostprocessing,
    .injectivePostprocessingErasureEquivalence,
    .observedLeftInversePostprocessingErasureEquivalence,
    .observedInjectivePostprocessingErasureEquivalence,
    .postprocessingObservedOutputCollisionObligation,
    .postprocessingObservedOppositeBiasCollisionObligation,
    .postprocessingSignedBiasCancellationCertificate,
    .postprocessedSideToleranceObservedFiberBalance,
    .postprocessedSideObservedFiberImbalanceLowerBound,
    .postprocessedSidePredicateErasure,
    .postprocessedSideDecoderHalfAccuracy,
    .postprocessedSideSourceRecoveryBlock,
    .postprocessedSideCollisionObligation,
    .postprocessedSidePointwiseCollisionObligation,
    .postprocessedSidePointwiseCollisionInsufficient,
    .postprocessedSideOneSidedCoinMapInsufficient,
    .postprocessedSideInjectiveWitnessMapEquivalence,
    .postprocessedSideCoinMatchingObligation,
    .postprocessedSideCoinMatchingCardinalityBlock,
    .postprocessedSideCoinMatchingPredicateBlock,
    .postprocessedSidePredicateMatchingEquivalence,
    .postprocessedSideApproxIndependenceCoinMatchingEquivalence,
    .finitePreimagePostprocessingBlowup]

/-- Broad repair classes not closed by the finite-coin stack.  This repeats the
current gap list intentionally: the finite-coin stack is useful coverage inside
the same-source finite-count branch, not a stop-grade proof. -/
def finiteCoinStackUncoveredBroadRepairClasses : List PNPRepairClass :=
  [.residualSideInformation,
    .randomizedResidual,
    .approximateDecorrelation,
    .kpolyCompressionBridge]

/-- Narrow residual-side-information subrepair classes covered by the current
functional collision packet.  These do not close arbitrary residual side
information; they block the common repair move that treats varying residual data
as if it were source-only data. -/
inductive PNPResidualSideInformationSubrepairClass where
  /-- Same-source/different-residual pairs cannot be decoded from the source
  summary alone. -/
  | sourceDecoderCollisionBlock
  /-- Same-source/different-residual pairs block source-only equality
  predicates for the residual value. -/
  | sourcePredicateCollisionBlock
  /-- Same-source/different-Boolean-target pairs block source-only Boolean
  classifiers. -/
  | sourceBooleanClassifierCollisionBlock
  /-- A concrete two-point same-source residual collision witnesses the
  obstruction. -/
  | concreteSameSourceResidualCollision
  /-- Source-determined residual side information over an invariant base is
  itself unresolved under the involution. -/
  | sourceDeterminedInvariantResidualUnresolved
  /-- Source-determined residual side information over an invariant base has
  zero orbit-resolving mass. -/
  | sourceDeterminedInvariantResidualZeroResolvedMass
  /-- Source-determined residual side information over an invariant base cannot
  give positive doubled advantage. -/
  | sourceDeterminedInvariantResidualNoAdvantage
  /-- Positive doubled advantage over an invariant base forces strictly
  positive orbit-resolving mass for the residual side information. -/
  | positiveAdvantageForcesPositiveResolvedMass
  /-- Strict half-accuracy advantage over an invariant base forces strictly
  positive orbit-resolving mass for the residual side information. -/
  | strictHalfAdvantageForcesPositiveResolvedMass
  /-- Positive orbit-resolving mass over an invariant base already forces the
  pure residual obstruction package: non-source-determined residual data,
  supported same-base residual variation, and a supported non-source-only
  residual equality test. -/
  | positiveResolvedMassPureResidualPackage
  /-- The manuscript's exact post-switch active orbit already realizes
  positive resolved mass together with the pure residual obstruction package
  on the concrete visible surface. -/
  | exactPostSwitchConcretePureResidualWitness
  /-- The manuscript's exact post-switch active-orbit prediction witness is
  already a fork-obstruction witness on the same concrete surface. -/
  | exactPostSwitchPredictionWitnessForcesForkObstruction
  /-- Positive doubled advantage over an invariant base forces the residual side
  information to be non-source-determined. -/
  | positiveAdvantageForcesNonSourceDeterminedResidual
  /-- Strict half-accuracy advantage over an invariant base forces the residual
  side information to be non-source-determined. -/
  | strictHalfAdvantageForcesNonSourceDeterminedResidual
  /-- Positive doubled advantage over an invariant base exposes a positive
  support residual collision over the base. -/
  | positiveAdvantageSupportedResidualCollision
  /-- Positive doubled advantage over an invariant base exposes a supported
  residual value whose equality test is not source-only. -/
  | positiveAdvantageSupportedSourcePredicateBlock
  /-- If every supported residual equality test is source-only, positive
  doubled advantage over an invariant base is impossible. -/
  | supportedSourcePredicatesNoPositiveAdvantage
  /-- If the classifier is already source-only on positive support, syntactic
  mention of the residual side data cannot create positive doubled advantage. -/
  | supportwiseSourceClassifierNoPositiveAdvantage
  /-- Strict half-accuracy advantage over an invariant base exposes a positive
  support residual collision over the base. -/
  | strictHalfAdvantageSupportedResidualCollision
  /-- Strict half-accuracy advantage over an invariant base exposes a supported
  residual value whose equality test is not source-only. -/
  | strictHalfAdvantageSupportedSourcePredicateBlock
  /-- If every supported residual equality test is source-only, strict
  half-accuracy advantage over an invariant base is impossible. -/
  | supportedSourcePredicatesNoStrictHalfAdvantage
  /-- If the classifier is already source-only on positive support, syntactic
  mention of the residual side data cannot beat half accuracy. -/
  | supportwiseSourceClassifierNoStrictHalfAdvantage
  /-- Positive doubled advantage over an invariant base must separate some
  positive-support involution pair at the final classifier output. -/
  | positiveAdvantagePredictionSeparation
  /-- Strict half-accuracy advantage over an invariant base must separate some
  positive-support involution pair at the final classifier output. -/
  | strictHalfAdvantagePredictionSeparation
  deriving DecidableEq, Repr

/-- The exact narrow residual-side-information subrepairs covered by the
current functional collision and resolution-cost packets. -/
def currentPNPResidualSideInformationCoveredSubrepairs :
    List PNPResidualSideInformationSubrepairClass :=
  [.sourceDecoderCollisionBlock,
    .sourcePredicateCollisionBlock,
    .sourceBooleanClassifierCollisionBlock,
    .concreteSameSourceResidualCollision,
    .sourceDeterminedInvariantResidualUnresolved,
    .sourceDeterminedInvariantResidualZeroResolvedMass,
    .sourceDeterminedInvariantResidualNoAdvantage,
    .positiveAdvantageForcesPositiveResolvedMass,
    .strictHalfAdvantageForcesPositiveResolvedMass,
    .positiveResolvedMassPureResidualPackage,
    .exactPostSwitchConcretePureResidualWitness,
    .exactPostSwitchPredictionWitnessForcesForkObstruction,
    .positiveAdvantageForcesNonSourceDeterminedResidual,
    .strictHalfAdvantageForcesNonSourceDeterminedResidual,
    .positiveAdvantageSupportedResidualCollision,
    .positiveAdvantageSupportedSourcePredicateBlock,
    .supportedSourcePredicatesNoPositiveAdvantage,
    .supportwiseSourceClassifierNoPositiveAdvantage,
    .strictHalfAdvantageSupportedResidualCollision,
    .strictHalfAdvantageSupportedSourcePredicateBlock,
    .supportedSourcePredicatesNoStrictHalfAdvantage,
    .supportwiseSourceClassifierNoStrictHalfAdvantage,
    .positiveAdvantagePredictionSeparation,
    .strictHalfAdvantagePredictionSeparation]

/-- Narrow randomized-residual subrepair classes covered by the current
finite-coin product-space obstruction.  These do not close arbitrary randomized
residual repairs; they force any positive finite-coin advantage claim to expose
a positive joint-support resolving coin. -/
inductive PNPRandomizedResidualSubrepairClass where
  /-- A finite-coin randomized residual is an ordinary side channel on the
  source/coin product. -/
  | productSideChannelBudget
  /-- If the residual is unresolved on every positive joint-support pair, its
  joint resolving mass is zero. -/
  | supportwiseUnresolvedZeroMass
  /-- A supportwise-unresolved finite-coin residual cannot produce positive
  doubled advantage. -/
  | supportwiseUnresolvedNoAdvantage
  /-- Positive finite-coin randomized-residual advantage exposes a
  positive-weight source/coin pair where the residual changes across the
  involution. -/
  | positiveAdvantageResolutionWitness
  /-- Positive finite-coin randomized-residual advantage already exposes a
  deterministic positive-weight coin slice with positive ordinary resolving
  mass. -/
  | positiveAdvantageDeterministicCoinSliceWitness
  /-- Even strict half-accuracy finite-coin randomized-residual advantage is
  already witnessed by a deterministic positive-weight coin slice with
  positive ordinary resolving mass. -/
  | strictHalfDeterministicCoinSliceWitness
  /-- The exact post-switch invariant-projection surface inherits the same
  supportwise-unresolved blocker. -/
  | postSwitchSupportwiseUnresolvedNoAdvantage
  /-- On the exact post-switch surface, exact-input-invariant support blocks
  strict half-accuracy finite-coin randomized-residual advantage. -/
  | postSwitchExactSupportNoStrictHalfAdvantage
  /-- On the exact post-switch surface, positive finite-coin advantage exposes
  a positive-weight input/coin pair resolving the local-input switch. -/
  | postSwitchPositiveAdvantageResolutionWitness
  /-- On the exact post-switch surface, positive finite-coin advantage already
  exposes a deterministic positive-weight coin slice with positive ordinary
  resolving mass. -/
  | postSwitchPositiveAdvantageDeterministicCoinSliceWitness
  /-- On the exact post-switch surface, even strict half-accuracy finite-coin
  advantage already exposes a deterministic positive-weight coin slice with
  positive ordinary resolving mass. -/
  | postSwitchStrictHalfDeterministicCoinSliceWitness
  deriving DecidableEq, Repr

/-- The exact narrow randomized-residual subrepairs covered by the current
finite-coin product-space obstruction stack. -/
def currentPNPRandomizedResidualCoveredSubrepairs :
    List PNPRandomizedResidualSubrepairClass :=
  [.productSideChannelBudget,
    .supportwiseUnresolvedZeroMass,
    .supportwiseUnresolvedNoAdvantage,
    .positiveAdvantageResolutionWitness,
    .positiveAdvantageDeterministicCoinSliceWitness,
    .strictHalfDeterministicCoinSliceWitness,
    .postSwitchSupportwiseUnresolvedNoAdvantage,
    .postSwitchExactSupportNoStrictHalfAdvantage,
    .postSwitchPositiveAdvantageResolutionWitness,
    .postSwitchPositiveAdvantageDeterministicCoinSliceWitness,
    .postSwitchStrictHalfDeterministicCoinSliceWitness]

/-- Narrow `Kpoly` subrepair classes already covered by the current exact-visible
stack.  These are useful local closures, not a proof of the broad
manuscript-specific `Kpoly` compression bridge. -/
inductive PNPKpolySubrepairClass where
  /-- A clocked exact-visible realization family is exactly the existing
  exact-visible bit-budget target. -/
  | clockWrapperEquivalence
  /-- The fixed-order raw `(a,b)` decision-list class cannot realize the full
  raw Boolean rule family at positive width. -/
  | rawABDecisionListFullRuleObstruction
  /-- The same raw `(a,b)` full-rule obstruction lifts through the exact
  visible pullback. -/
  | rawABDecisionListExactPullbackObstruction
  /-- Shared affine-feature families cannot realize all raw `(a,b)` Boolean
  rules below the reduced truth-table threshold. -/
  | sharedABAffineFeatureFullRuleObstruction
  /-- Shared sparse-threshold families cannot realize all raw `(a,b)` Boolean
  rules below the reduced truth-table threshold. -/
  | sharedABSparseThresholdFullRuleObstruction
  /-- Shared decision-list families cannot realize all raw `(a,b)` Boolean
  rules below the reduced truth-table threshold. -/
  | sharedABDecisionListFullRuleObstruction
  /-- The shared affine-feature full-rule obstruction lifts through the exact
  visible pullback. -/
  | sharedExactABAffineFeaturePullbackObstruction
  /-- The shared sparse-threshold full-rule obstruction lifts through the exact
  visible pullback. -/
  | sharedExactABSparseThresholdPullbackObstruction
  /-- The shared decision-list full-rule obstruction lifts through the exact
  visible pullback. -/
  | sharedExactABDecisionListPullbackObstruction
  /-- Shared raw `(a,b)` feature families cannot realize injective finite probe
  images larger than their finite combiner image, without needing full reduced
  rule surjectivity. -/
  | sharedABFeatureInjectiveProbeImageObstruction
  /-- The shared raw `(a,b)` finite-probe obstruction lifts through exact
  visible pullback along `abVisibleData`. -/
  | sharedExactABFeatureInjectiveProbePullbackObstruction
  /-- Any exact family invariant under raw `(a,b)` cannot select a target rule
  that separates two exact inputs in the same `(a,b)` fiber. -/
  | abVisibleInvariantPointTargetObstruction
  /-- Any raw `(a,b)`-invariant exact predictor must disagree on positive mass
  with a target that separates two positive-mass inputs in one same-`(a,b)`
  fiber. -/
  | abVisibleInvariantSupportDisagreementObstruction
  /-- Any exact family invariant under raw `(a,b)` is not surjective onto all
  exact visible Boolean rules when the hidden `Z` datum is nontrivial. -/
  | abVisibleInvariantExactSurfaceSurjectivityObstruction
  /-- Exact visible / clocked `Kpoly` budgets are exactly finite predictor-image
  covers of size at most `2^s`. -/
  | exactVisibleImageBudgetEquivalence
  /-- The accumulated clocked finite-learning payload is exactly the same
  finite predictor-image cover obligation. -/
  | clockedFiniteLearningPayloadEquivalence
  /-- The concrete exact `(zfeat(z), a, b)` decision-list ERM family closes the
  clocked finite-learning payload at its explicit code budget. -/
  | exactZABERMClockedPayloadClosure
  /-- The bit-vector exact ZAB ERM specialization closes the clocked
  finite-learning payload at the same explicit budget. -/
  | bitVecZABERMClockedPayloadClosure
  /-- Equality with the concrete bit-vector ERM family is a sufficient
  manuscript-facing missing assumption for the clocked payload. -/
  | equalityToBitVecZABERMClockedPayloadClosure
  /-- A strict exact-ZAB bad-code agreement threshold forces every region above
  that threshold to contain a positive-mass bad-code disagreement. -/
  | exactZABBadCodeLargeRegionDisagreementBoundary
  /-- The bare exact-visible family interface alone cannot imply clocked
  finite-learning payloads for all families below the full visible surface. -/
  | bareExactVisibleInterfacePayloadInsufficiency
  /-- A small observed actual-local block-output image does not imply a small
  exact-visible local-rule image. -/
  | actualObservedSupportPayloadInsufficiency
  /-- Observed actual-local output compression transfers to full exact-visible
  compression only with a uniform visible section; the finite-support full-rule
  construction cannot supply one below the full exact-visible surface size. -/
  | actualObservedSupportUniformSectionBoundary
  /-- A reachable-support quotient only records restriction along `visibleOf`;
  below surface cardinality it identifies distinct exact-visible rules. -/
  | actualObservedSupportQuotientLossBoundary
  /-- No decoder from observed block-output traces can reconstruct all full
  exact-visible rules unless the reachable support hits the whole surface. -/
  | actualObservedSupportDecoderRecoveryBoundary
  /-- Any downstream property decoded from observed block traces must be
  constant on observed-output fibers; off-support exact-visible bits are not
  observable below full support. -/
  | actualObservedSupportObservablePropertyBoundary
  /-- A downstream property factors through observed block traces exactly when
  it is constant on observed-output fibers. -/
  | actualObservedSupportPropertyFactorBoundary
  /-- Exact-visible point queries are observable from block traces exactly at
  points in the reachable support; all point queries force full support
  surjectivity. -/
  | actualObservedSupportPointQueryBoundary
  /-- A whole family of exact-visible point queries is decodable from observed
  traces exactly when every queried point lies in reachable support. -/
  | actualObservedSupportQueryFamilyBoundary
  /-- Adaptive point-query trees over exact-visible points still factor
  through observed traces exactly by quotient constancy, and missed root
  queries with distinct branches are impossible to decode. -/
  | actualObservedSupportAdaptiveQueryBoundary
  /-- An unrestricted plug-in lookup endpoint over the exact visible alphabet
  is still the full Boolean rule family, not a small-image `Kpoly` bridge. -/
  | actualLocalPluginLookupFullRuleObstruction
  /-- Unrestricted per-input plug-in majority counts still realize every
  Boolean rule on the exact visible alphabet. -/
  | actualLocalPluginMajorityFullRuleObstruction
  /-- Sample-level plug-in majority still realizes every Boolean rule via the
  graph sample unless the samples are further restricted. -/
  | actualLocalPluginSampleMajorityFullRuleObstruction
  /-- Unrestricted sample-level plug-in majority still cannot be identified
  with one shared sparse-threshold ERM family, nor carry its stronger recovery
  packet, below the point-block visible-budget threshold. -/
  | actualLocalPluginSampleMajoritySparseThresholdERMVisibleBudgetBoundary
  /-- Bounded sample-level plug-in majority is full-rule expressive exactly
  when the sample bound reaches the exact visible alphabet size. -/
  | actualLocalBoundedSampleMajorityThresholdBoundary
  /-- Bounded sample-level plug-in majority can be false only on sampled exact
  visible inputs, so target rules with too-large false support are not
  realizable. -/
  | actualLocalBoundedSampleMajorityFalseSupportBoundary
  /-- Changing the bounded sample-level plug-in majority tie-break does not
  change the cardinal threshold: only sampled inputs can differ from the
  chosen default. -/
  | actualLocalBoundedSampleMajorityDefaultTieBoundary
  /-- An input-dependent tie fallback for bounded sample-level plug-in majority
  is already a full exact-visible lookup table, even with the empty sample. -/
  | actualLocalBoundedSampleMajorityFallbackSideChannelBoundary
  /-- If the input-dependent fallback is restricted to a structured fallback
  family, bounded samples only produce sparse point changes from the selected
  fallback rule. -/
  | actualLocalBoundedSampleMajorityFallbackFamilySparseBoundary
  /-- A bit-coded full-rule fallback decoder does not rescue bounded
  sample-level plug-in majority from the shared sparse-threshold ERM visible-
  budget boundary. -/
  | actualLocalBoundedSampleMajorityBitFallbackSparseThresholdERMVisibleBudgetBoundary
  /-- If a bit-coded structured fallback decoder is already full-rule
  expressive, then the bounded-sample wrapper still inherits the later
  lightest-point recovery threshold. -/
  | actualLocalBoundedSampleMajorityBitFallbackRecoveryLightestPointBoundary
  /-- Finite predictor-image covers are equivalently finite quotient-code
  presentations with an index encoder and predictor decoder. -/
  | finitePredictorQuotientEquivalence
  /-- A fully expressive exact visible family cannot have a finite
  predictor-image cover below the full Boolean classifier-space cardinality. -/
  | exactVisibleImageSurjectivityObstruction
  /-- Any injectively indexed finite probe family already realized by the
  switched predictors gives the same finite-image lower bound, without needing
  full surjectivity onto every Boolean classifier. -/
  | injectiveFiniteProbeImageLowerBound
  /-- The same surjectivity and finite-probe lower bounds refute the bundled
  clocked finite-learning payload below the corresponding image size. -/
  | clockedFiniteLearningPayloadImageObstruction
  /-- Section-backed factor maps preserve finite-probe lower bounds from a
  reduced view, without needing the reduced family to be fully surjective. -/
  | sectionBackedInjectiveFiniteProbePullbackLowerBound
  /-- Finite predictor-image covers are equivalently finite representative
  index covers using actual selected predictors. -/
  | finiteRepresentativeIndexCoverEquivalence
  /-- Finite predictor-image covers, representative-index covers, and
  quotient-code presentations are monotone in the allowed finite-image budget. -/
  | finiteImageCoverBudgetWeakening
  /-- Finite predictor-image covers, representative-index covers, and
  quotient-code presentations transport across explicit factor maps, and push
  back along factorizations with a section. -/
  | finiteImageCoverFactorTransport
  /-- If an exact family factors through `(a,b)` and the reduced family is
  still fully expressive, finite-image covers below the reduced Boolean
  classifier-space cardinality are impossible. -/
  | finiteImageReducedABPullbackObstruction
  /-- If an exact family factors through `(a,b)`, every injectively indexed
  finite probe family already realized on the reduced `(a,b)` view gives the
  same finite-image lower bound after pullback. -/
  | finiteImageReducedABInjectiveProbePullbackObstruction
  /-- The same reduced `(a,b)` pullback obstruction holds for finite
  quotient-code presentations. -/
  | finiteQuotientReducedABPullbackObstruction
  /-- Product-bound-only bridge schemas are exactly demands for finite
  predictor-image covers for every exact-visible family. -/
  | productBoundBridgeFiniteImageBoundary
  /-- Fixed-field switching-only bridge schemas are exactly demands for finite
  predictor-image covers for every exact-visible family. -/
  | fieldedSwitchingBridgeFiniteImageBoundary
  /-- Product-bound-only bridge schemas are refuted below the exact-visible
  surface threshold by the full exact-visible Boolean family. -/
  | productBoundOnlyFullVisibleObstruction
  /-- Fixed-field switching-only bridge schemas are refuted below the
  exact-visible surface threshold by the full exact-visible Boolean family. -/
  | fieldedSwitchingOnlyFullVisibleObstruction
  /-- Product-bound-only bridge schemas are refuted below the exact-visible
  surface threshold by any already-surjective exact-visible family. -/
  | productBoundOnlySurjectiveVisibleObstruction
  /-- Fixed-field switching-only bridge schemas are refuted below the
  exact-visible surface threshold by any already-surjective exact-visible
  family. -/
  | fieldedSwitchingOnlySurjectiveVisibleObstruction
  /-- Product-bound-only bridge schemas to the full clocked finite-learning
  payload are still exactly demands for finite predictor-image covers. -/
  | productBoundClockedPayloadBridgeFiniteImageBoundary
  /-- Fixed-field switching-only bridge schemas to the full clocked
  finite-learning payload are still exactly demands for finite predictor-image
  covers. -/
  | fieldedSwitchingClockedPayloadBridgeFiniteImageBoundary
  /-- Product-bound-only clocked-payload bridge schemas are refuted below the
  exact-visible surface threshold by the full exact-visible Boolean family. -/
  | productBoundOnlyClockedPayloadFullVisibleObstruction
  /-- Fixed-field switching-only clocked-payload bridge schemas are refuted
  below the exact-visible surface threshold by the full exact-visible Boolean
  family. -/
  | fieldedSwitchingOnlyClockedPayloadFullVisibleObstruction
  /-- Product-bound-only clocked-payload bridge schemas are refuted below the
  Boolean predictor-space threshold by any already-surjective exact-visible
  family. -/
  | productBoundOnlyClockedPayloadSurjectiveVisibleObstruction
  /-- Fixed-field switching-only clocked-payload bridge schemas are refuted
  below the Boolean predictor-space threshold by any already-surjective
  exact-visible family. -/
  | fieldedSwitchingOnlyClockedPayloadSurjectiveVisibleObstruction
  deriving DecidableEq, Repr

/-- The exact narrow `Kpoly` subrepairs covered by the current stack. -/
def currentPNPKpolyCoveredSubrepairs : List PNPKpolySubrepairClass :=
  [.clockWrapperEquivalence,
    .rawABDecisionListFullRuleObstruction,
    .rawABDecisionListExactPullbackObstruction,
    .sharedABAffineFeatureFullRuleObstruction,
    .sharedABSparseThresholdFullRuleObstruction,
    .sharedABDecisionListFullRuleObstruction,
    .sharedExactABAffineFeaturePullbackObstruction,
    .sharedExactABSparseThresholdPullbackObstruction,
    .sharedExactABDecisionListPullbackObstruction,
    .sharedABFeatureInjectiveProbeImageObstruction,
    .sharedExactABFeatureInjectiveProbePullbackObstruction,
    .abVisibleInvariantPointTargetObstruction,
    .abVisibleInvariantSupportDisagreementObstruction,
    .abVisibleInvariantExactSurfaceSurjectivityObstruction,
    .exactVisibleImageBudgetEquivalence,
    .clockedFiniteLearningPayloadEquivalence,
    .exactZABERMClockedPayloadClosure,
    .bitVecZABERMClockedPayloadClosure,
    .equalityToBitVecZABERMClockedPayloadClosure,
    .exactZABBadCodeLargeRegionDisagreementBoundary,
    .bareExactVisibleInterfacePayloadInsufficiency,
    .actualObservedSupportPayloadInsufficiency,
    .actualObservedSupportUniformSectionBoundary,
    .actualObservedSupportQuotientLossBoundary,
    .actualObservedSupportDecoderRecoveryBoundary,
    .actualObservedSupportObservablePropertyBoundary,
    .actualObservedSupportPropertyFactorBoundary,
    .actualObservedSupportPointQueryBoundary,
    .actualObservedSupportQueryFamilyBoundary,
    .actualObservedSupportAdaptiveQueryBoundary,
    .actualLocalPluginLookupFullRuleObstruction,
    .actualLocalPluginMajorityFullRuleObstruction,
    .actualLocalPluginSampleMajorityFullRuleObstruction,
    .actualLocalPluginSampleMajoritySparseThresholdERMVisibleBudgetBoundary,
    .actualLocalBoundedSampleMajorityThresholdBoundary,
    .actualLocalBoundedSampleMajorityFalseSupportBoundary,
    .actualLocalBoundedSampleMajorityDefaultTieBoundary,
    .actualLocalBoundedSampleMajorityFallbackSideChannelBoundary,
    .actualLocalBoundedSampleMajorityFallbackFamilySparseBoundary,
    .actualLocalBoundedSampleMajorityBitFallbackSparseThresholdERMVisibleBudgetBoundary,
    .actualLocalBoundedSampleMajorityBitFallbackRecoveryLightestPointBoundary,
    .finitePredictorQuotientEquivalence,
    .exactVisibleImageSurjectivityObstruction,
    .injectiveFiniteProbeImageLowerBound,
    .clockedFiniteLearningPayloadImageObstruction,
    .sectionBackedInjectiveFiniteProbePullbackLowerBound,
    .finiteRepresentativeIndexCoverEquivalence,
    .finiteImageCoverBudgetWeakening,
    .finiteImageCoverFactorTransport,
    .finiteImageReducedABPullbackObstruction,
    .finiteImageReducedABInjectiveProbePullbackObstruction,
    .finiteQuotientReducedABPullbackObstruction,
    .productBoundBridgeFiniteImageBoundary,
    .fieldedSwitchingBridgeFiniteImageBoundary,
    .productBoundOnlyFullVisibleObstruction,
    .fieldedSwitchingOnlyFullVisibleObstruction,
    .productBoundOnlySurjectiveVisibleObstruction,
    .fieldedSwitchingOnlySurjectiveVisibleObstruction,
    .productBoundClockedPayloadBridgeFiniteImageBoundary,
    .fieldedSwitchingClockedPayloadBridgeFiniteImageBoundary,
    .productBoundOnlyClockedPayloadFullVisibleObstruction,
    .fieldedSwitchingOnlyClockedPayloadFullVisibleObstruction,
    .productBoundOnlyClockedPayloadSurjectiveVisibleObstruction,
    .fieldedSwitchingOnlyClockedPayloadSurjectiveVisibleObstruction]

/-- The covered-class list is exact for the current PNP crux packet. -/
theorem currentPNPCoveredRepairClasses_exact (repair : PNPRepairClass) :
    repair ∈ currentPNPCoveredRepairClasses ↔
      currentPNPLocalCruxPacket.covers repair := by
  cases repair <;> simp [currentPNPCoveredRepairClasses, currentPNPLocalCruxPacket]

/-- The uncovered-class list is exact for the current PNP crux packet. -/
theorem currentPNPUncoveredRepairClasses_exact (repair : PNPRepairClass) :
    repair ∈ currentPNPUncoveredRepairClasses ↔
      ¬ currentPNPLocalCruxPacket.covers repair := by
  cases repair <;> simp [currentPNPUncoveredRepairClasses, currentPNPLocalCruxPacket]

/-- A single honest top-level status theorem for the current packet: the v13
ledger entries are backed by route theorems, while the broad packet is still not
stop-grade because named repair classes remain uncovered. -/
theorem currentPNPLocalCruxPacket_theoremBacked_v13_status :
    currentPNPLocalCruxPacket.covers .repeatedPositiveFieldedPivot ∧
      currentPNPLocalCruxPacket.covers .forcedPositiveFieldedStep ∧
      currentPNPLocalCruxPacket.covers .fixedFieldBadCell ∧
      currentPNPLocalCruxPacket.covers .fieldRefinementOfBadCell ∧
      currentPNPLocalCruxPacket.covers .cdEvidenceNormalization ∧
      currentPNPLocalCruxPacket.covers .traceCaptureFactorization ∧
      currentPNPLocalCruxPacket.covers .atomicEvidenceBudget ∧
      currentPNPLocalCruxPacket.covers .acceiEnvelopeProduct ∧
        ¬ currentPNPLocalCruxPacket.StopGrade := by
  refine
    ⟨v13RepeatedPositiveFieldedPivotCoverage,
      v13ForcedPositiveFieldedStepCoverage,
      v13FieldedBadCellCoverage,
      v13FieldRefinementBadCellCoverage,
      v13EvidenceNormalizationCoverage,
      v13TraceCaptureFactorizationCoverage,
      v13AtomicEvidenceBudgetCoverage,
      v13ACCEIEnvelopeProductCoverage, ?_⟩
  intro hstop
  have hres : currentPNPLocalCruxPacket.covers .residualSideInformation :=
    hstop .residualSideInformation
  simp [currentPNPLocalCruxPacket] at hres

/-- The finite-coin subrepair coverage list is exact. -/
theorem currentPNPFiniteCoinCoveredSubrepairs_exact
    (repair : PNPFiniteCoinSubrepairClass) :
    repair ∈ currentPNPFiniteCoinCoveredSubrepairs := by
  cases repair <;> simp [currentPNPFiniteCoinCoveredSubrepairs]

/-- The narrow residual-side-information subrepair coverage list is exact. -/
theorem currentPNPResidualSideInformationCoveredSubrepairs_exact
    (repair : PNPResidualSideInformationSubrepairClass) :
    repair ∈ currentPNPResidualSideInformationCoveredSubrepairs := by
  cases repair <;> simp [currentPNPResidualSideInformationCoveredSubrepairs]

/-- The broad repair classes not closed by the finite-coin stack are exactly the
current synthesis gaps. -/
theorem finiteCoinStackUncoveredBroadRepairClasses_exact
    (repair : PNPRepairClass) :
    repair ∈ finiteCoinStackUncoveredBroadRepairClasses ↔
      repair ∈ currentPNPUncoveredRepairClasses := by
  cases repair <;> simp [finiteCoinStackUncoveredBroadRepairClasses,
    currentPNPUncoveredRepairClasses]

/-- The narrow randomized-residual subrepair coverage list is exact. -/
theorem currentPNPRandomizedResidualCoveredSubrepairs_exact
    (repair : PNPRandomizedResidualSubrepairClass) :
    repair ∈ currentPNPRandomizedResidualCoveredSubrepairs := by
  cases repair <;> simp [currentPNPRandomizedResidualCoveredSubrepairs]

/-- The narrow `Kpoly` subrepair coverage list is exact. -/
theorem currentPNPKpolyCoveredSubrepairs_exact
    (repair : PNPKpolySubrepairClass) :
    repair ∈ currentPNPKpolyCoveredSubrepairs := by
  cases repair <;> simp [currentPNPKpolyCoveredSubrepairs]

/-- The finite-coin stack contributes to the same-source finite-count branch of
the ledger. -/
theorem finiteCoinStack_under_sameSourceFiniteCountApproximation :
    currentPNPLocalCruxPacket.covers .sameSourceFiniteCountApproximation := by
  simp [currentPNPLocalCruxPacket]

/-- The finite-coin stack does not by itself close broad randomized residual
repairs. -/
theorem finiteCoinStack_does_not_cover_randomizedResidual :
    ¬ currentPNPLocalCruxPacket.covers .randomizedResidual := by
  simp [currentPNPLocalCruxPacket]

/-- The support-sensitive finite-coin randomized-residual subledger does not by
itself close broad randomized residual repairs. -/
theorem randomizedResidualSubrepairStack_does_not_cover_randomizedResidual :
    ¬ currentPNPLocalCruxPacket.covers .randomizedResidual := by
  simp [currentPNPLocalCruxPacket]

/-- The finite-coin stack does not by itself close broad residual side
information repairs. -/
theorem finiteCoinStack_does_not_cover_residualSideInformation :
    ¬ currentPNPLocalCruxPacket.covers .residualSideInformation := by
  simp [currentPNPLocalCruxPacket]

/-- The narrow residual-side-information collision packet does not by itself
close broad residual side-information repairs. -/
theorem residualSideInformationSubrepairStack_does_not_cover_residualSideInformation :
    ¬ currentPNPLocalCruxPacket.covers .residualSideInformation := by
  simp [currentPNPLocalCruxPacket]

/-- The finite-coin stack does not by itself close broad approximate
decorrelation repairs. -/
theorem finiteCoinStack_does_not_cover_approximateDecorrelation :
    ¬ currentPNPLocalCruxPacket.covers .approximateDecorrelation := by
  simp [currentPNPLocalCruxPacket]

/-- The finite-coin stack does not by itself close the manuscript-specific
`Kpoly` compression bridge. -/
theorem finiteCoinStack_does_not_cover_kpolyCompressionBridge :
    ¬ currentPNPLocalCruxPacket.covers .kpolyCompressionBridge := by
  simp [currentPNPLocalCruxPacket]

/-- The narrow `Kpoly` subrepair stack does not by itself close the broad
manuscript-specific `Kpoly` compression bridge. -/
theorem kpolySubrepairStack_does_not_cover_kpolyCompressionBridge :
    ¬ currentPNPLocalCruxPacket.covers .kpolyCompressionBridge := by
  simp [currentPNPLocalCruxPacket]

/-- The current packet covers the v13 evidence-normalization boundary as an
exact residual-atom equivalence. -/
theorem cdEvidenceNormalization_covered_currentPNPLocalCruxPacket :
    currentPNPLocalCruxPacket.covers .cdEvidenceNormalization := by
  exact v13EvidenceNormalizationCoverage

/-- The current packet covers the v13 trace-capture factorization boundary as
an exact trace-fiber constancy equivalence. -/
theorem traceCaptureFactorization_covered_currentPNPLocalCruxPacket :
    currentPNPLocalCruxPacket.covers .traceCaptureFactorization := by
  exact v13TraceCaptureFactorizationCoverage

/-- The current packet covers the v13 atomic-evidence budget boundary at the
full finite exactness surface, including the cancellation obstruction to
equivalence-only repairs. -/
theorem atomicEvidenceBudget_covered_currentPNPLocalCruxPacket :
    currentPNPLocalCruxPacket.covers .atomicEvidenceBudget := by
  exact v13AtomicEvidenceBudgetCoverage

/-- The current packet covers the finite ACCEI/PNLD envelope-product skeleton:
finite Markov pruning plus the sequential one-step rate product bound and its
contrapositive. -/
theorem acceiEnvelopeProduct_covered_currentPNPLocalCruxPacket :
    currentPNPLocalCruxPacket.covers .acceiEnvelopeProduct := by
  exact v13ACCEIEnvelopeProductCoverage

/-- The current packet covers the v13 forced-positive-fielded-step boundary as
an exact finite-count obstruction, not only literal repeated pivots. -/
theorem forcedPositiveFieldedStep_covered_currentPNPLocalCruxPacket :
    currentPNPLocalCruxPacket.covers .forcedPositiveFieldedStep := by
  exact v13ForcedPositiveFieldedStepCoverage

/-- The next highest-marginal target selected by the current ledger.  The
finite-coin stack now has a precise subledger, the postprocessed-side matching
subcase is closed, and the clocked finite-uniform bookkeeping kernel is already
covered.  The next broad gap to push is therefore residual side information:
any useful residual must expose quantified orbit-resolving mass, not merely
exist as an extra retained variable. -/
def currentPNPNextMarginalTarget : PNPRepairClass :=
  .residualSideInformation

/-- The selected next target is still uncovered by the current packet. -/
theorem currentPNPNextMarginalTarget_uncovered :
    ¬ currentPNPLocalCruxPacket.covers currentPNPNextMarginalTarget := by
  simp [currentPNPNextMarginalTarget, currentPNPLocalCruxPacket]

/-- Any packet that still misses the selected next marginal target cannot be
called stop-grade. -/
theorem not_stopGrade_of_not_covers_currentPNPNextMarginalTarget
    {packet : PNPCruxPacket}
    (hmiss : ¬ packet.covers currentPNPNextMarginalTarget) :
    ¬ packet.StopGrade :=
  PNPCruxPacket.not_stopGrade_of_not_covers hmiss

/-- The selected next target is one of the current synthesis gaps. -/
theorem currentPNPNextMarginalTarget_mem_uncovered :
    currentPNPNextMarginalTarget ∈ currentPNPUncoveredRepairClasses := by
  simp [currentPNPNextMarginalTarget, currentPNPUncoveredRepairClasses]

/-- The selected next target is outside the finite-coin subledger. -/
theorem currentPNPNextMarginalTarget_mem_finiteCoin_uncovered_broad :
    currentPNPNextMarginalTarget ∈ finiteCoinStackUncoveredBroadRepairClasses := by
  simp [currentPNPNextMarginalTarget, finiteCoinStackUncoveredBroadRepairClasses]

/-- Route-coverage anchor: a same-source/different-residual collision cannot
be decoded from the source summary alone. -/
theorem residualSideInformationCoverage_anchor_collision_blocks_source_decoder
    {Ω Base Side : Type*} {base : Ω → Base} {side : Ω → Side}
    {x y : Ω} (hbase : base x = base y) (hside : side x ≠ side y) :
    ¬ SideInfoDeterminedBy base side :=
  not_sideInfoDeterminedBy_of_same_base_ne_side hbase hside

/-- Route-coverage anchor: the equality predicate for one residual value cannot
be pushed down to a source-only predicate across a same-source collision. -/
theorem residualSideInformationCoverage_anchor_collision_blocks_source_predicate
    {Ω Base Side : Type*} {base : Ω → Base} {side : Ω → Side}
    {x y : Ω} (hbase : base x = base y) (hside : side x ≠ side y) :
    ¬ SourceOnlyPredicateCapturesSideEq base side (side x) :=
  not_sourceOnlyPredicateCapturesSideEq_left_of_same_base_ne_side hbase hside

/-- Route-coverage anchor: a Boolean residual target that varies inside one
source-summary fiber cannot be recovered by a source-only classifier. -/
theorem residualSideInformationCoverage_anchor_collision_blocks_source_boolean_classifier
    {Ω Base : Type*} {base : Ω → Base} {target : Ω → Bool}
    {x y : Ω} (hbase : base x = base y) (htarget : target x ≠ target y) :
    ¬ SourceOnlyBooleanClassifier base target :=
  not_sourceOnlyBooleanClassifier_of_same_base_ne_target hbase htarget

/-- Route-coverage anchor: a concrete two-point same-source residual collision
witnesses that source-only residual decoding is not automatic. -/
theorem residualSideInformationCoverage_anchor_toy_collision :
    SideInfoCollisionOverBase residualSideInfoToyBase residualSideInfoToySide ∧
      ¬ SideInfoDeterminedBy residualSideInfoToyBase residualSideInfoToySide ∧
      ¬ SourceOnlyPredicateCapturesSideEq
        residualSideInfoToyBase residualSideInfoToySide false ∧
      ¬ SourceOnlyBooleanClassifier
        residualSideInfoToyBase residualSideInfoToySide := by
  exact
    ⟨residualSideInfoToy_collision,
      residualSideInfoToy_not_determinedBy_base,
      residualSideInfoToy_not_sourceOnlyPredicate_false,
      residualSideInfoToy_not_sourceOnlyBooleanClassifier⟩

/-- Route-coverage anchor: if residual side information is decoded from an
involution-invariant base feature, then it is itself unresolved across the
involution. -/
theorem residualSideInformationCoverage_anchor_source_determined_invariant_unresolved
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (hbase : ∀ x, base (τ x) = base x)
    (hdet : SideInfoDeterminedBy base side) :
    ∀ x, side (τ x) = side x :=
  side_eq_under_involution_of_determinedBy_invariant_base
    τ base side hbase hdet

/-- Route-coverage anchor: source-determined residual side information over an
invariant base has zero orbit-resolving mass. -/
theorem residualSideInformationCoverage_anchor_source_determined_zero_resolvedMass
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side) (w : α → ℕ)
    (hbase : ∀ x, base (τ x) = base x)
    (hdet : SideInfoDeterminedBy base side) :
    resolvedMass τ side w = 0 :=
  resolvedMass_eq_zero_of_determinedBy_invariant_base
    τ base side w hbase hdet

/-- Route-coverage anchor: source-determined residual side information over an
invariant base cannot supply positive doubled advantage. -/
theorem residualSideInformationCoverage_anchor_source_determined_no_positive_advantage
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hdet : SideInfoDeterminedBy base side)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x) :
    ¬ 0 < doubledAdvantage (fun x => (base x, side x)) y w h :=
  not_pos_doubledAdvantage_pair_of_determinedBy_invariant_base
    τ base side y w h hτ hbase hdet hy hw

/-- Route-coverage anchor: any positive doubled advantage from `(base, side)`
over an invariant base already forces strictly positive orbit-resolving mass
for the residual side information. -/
theorem residualSideInformationCoverage_anchor_positive_advantage_forces_positive_resolvedMass
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv : 0 < doubledAdvantage (fun x => (base x, side x)) y w h) :
    0 < resolvedMass τ side w :=
  resolvedMass_pos_of_pos_doubledAdvantage_pair
    τ base side y w h hτ hbase hy hw hadv

/-- Route-coverage anchor: the strict half-accuracy formulation likewise forces
strictly positive orbit-resolving mass for the residual side information. -/
theorem residualSideInformationCoverage_anchor_strict_half_advantage_forces_positive_resolvedMass
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv :
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h) :
    0 < resolvedMass τ side w :=
  resolvedMass_pos_of_total_lt_two_mul_weightedCorrectMass_pair
    τ base side y w h hτ hbase hy hw hadv

/-- Route-coverage anchor: once residual side information carries positive
orbit-resolving mass over an invariant base, some positive-weight involution
pair must already differ in residual value while agreeing on the base. -/
theorem residualSideInformationCoverage_anchor_positive_resolvedMass_witnesses_same_base_residual_collision
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side) (w : α → ℕ)
    (hbase : ∀ x, base (τ x) = base x)
    (hmass : 0 < resolvedMass τ side w) :
    ∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x := by
  obtain ⟨x, hxw, hside⟩ := exists_resolving_point_of_pos_resolvedMass τ side w hmass
  exact ⟨x, hxw, hbase x, hside⟩

/-- Route-coverage anchor: positive orbit-resolving mass over an invariant base
is already a pure residual-side-information obstruction package, before any
classifier-specific prediction facts are used. -/
theorem residualSideInformationCoverage_anchor_positive_resolvedMass_forces_supported_obstruction_package
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side) (w : α → ℕ)
    (hbase : ∀ x, base (τ x) = base x)
    (hmass : 0 < resolvedMass τ side w) :
    ¬ SideInfoDeterminedBy base side ∧
      PositiveWeightSideInfoCollisionOverBase base side w ∧
      (∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
      (∃ x, 0 < w x ∧
        ¬ SourceOnlyPredicateCapturesSideEq base side (side x)) :=
  pos_resolvedMass_obstruction_package_invariant_base
    τ base side w hbase hmass

/-- Route-coverage anchor: on the manuscript's exact visible post-switch
surface, the concrete active two-point orbit already realizes positive
resolved mass together with the pure residual obstruction package, before any
classifier-level prediction-separation argument is invoked. -/
theorem residualSideInformationCoverage_anchor_exactPostSwitch_activeOrbit_pure_residual_package
    {Z : Type*} [Fintype Z] (z0 : Z) :
    0 < resolvedMass tiInputMap
        (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b)
        (activeOrbitWeight z0) ∧
      ¬ SideInfoDeterminedBy invariantVisibleData
          (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b) ∧
      PositiveWeightSideInfoCollisionOverBase invariantVisibleData
        (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b)
        (activeOrbitWeight z0) ∧
      (∃ u : ExactVisiblePostSwitchSurface Z 1,
        0 < activeOrbitWeight z0 u ∧
          invariantVisibleData (tiInputMap u) = invariantVisibleData u ∧
          (tiInputMap u).b ≠ u.b) ∧
      (∃ u : ExactVisiblePostSwitchSurface Z 1,
        0 < activeOrbitWeight z0 u ∧
          ¬ SourceOnlyPredicateCapturesSideEq invariantVisibleData
            (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b) (u.b)) := by
  exact
    exactPostSwitch_activeOrbit_realizes_pure_residual_obstruction_package
      (Z := Z) z0

/-- Route-coverage anchor: on the manuscript's exact visible post-switch
surface, the concrete active two-point orbit already realizes the
classifier-level residual prediction witness as well.  The invariant
projection is preserved, the active weight is involution-symmetric, the target
flips on positive support, the concrete classifier has positive doubled
advantage, and some positive-weight involution pair is separated by the final
classifier output. -/
theorem residualSideInformationCoverage_anchor_exactPostSwitch_activeOrbit_prediction_witness
    {Z : Type*} [Fintype Z] (z0 : Z) :
    (∀ u : ExactVisiblePostSwitchSurface Z 1,
      invariantVisibleData (tiInputMap u) = invariantVisibleData u) ∧
    (∀ u : ExactVisiblePostSwitchSurface Z 1,
      activeOrbitWeight z0 (tiInputMap u) = activeOrbitWeight z0 u) ∧
    (∀ u : ExactVisiblePostSwitchSurface Z 1, 0 < activeOrbitWeight z0 u →
      activeOrbitTarget (tiInputMap u) = !(activeOrbitTarget u)) ∧
    0 <
      doubledAdvantage
        activeOrbitFeatures
        activeOrbitTarget
        (activeOrbitWeight z0)
        activeOrbitClassifier ∧
    ∃ u : ExactVisiblePostSwitchSurface Z 1,
      0 < activeOrbitWeight z0 u ∧
      activeOrbitClassifier (activeOrbitFeatures (tiInputMap u)) ≠
        activeOrbitClassifier (activeOrbitFeatures u) := by
  exact
    exactPostSwitch_activeOrbit_realizes_residual_prediction_witness
      (Z := Z) z0

/-- Route-coverage anchor: on the manuscript's exact visible post-switch
surface, the concrete active-orbit residual prediction witness already carries
the fork-obstruction package on the same two-point orbit.  So classifier-level
residual prediction separation is not a fresh concrete route on that surface:
it already brings strict half-accuracy success, positive nonzero-column mass,
and failure of exact-input-invariant support. -/
theorem residualSideInformationCoverage_anchor_exactPostSwitch_prediction_witness_forces_fork_obstruction
    {Z : Type*} [Fintype Z] (z0 : Z) :
    ((∀ u : ExactVisiblePostSwitchSurface Z 1,
        invariantVisibleData (tiInputMap u) = invariantVisibleData u) ∧
      (∀ u : ExactVisiblePostSwitchSurface Z 1,
        activeOrbitWeight z0 (tiInputMap u) = activeOrbitWeight z0 u) ∧
      (∀ u : ExactVisiblePostSwitchSurface Z 1, 0 < activeOrbitWeight z0 u →
        activeOrbitTarget (tiInputMap u) = !(activeOrbitTarget u)) ∧
      0 <
        doubledAdvantage
          activeOrbitFeatures
          activeOrbitTarget
          (activeOrbitWeight z0)
          activeOrbitClassifier ∧
      (∃ u : ExactVisiblePostSwitchSurface Z 1,
        0 < activeOrbitWeight z0 u ∧
          activeOrbitClassifier (activeOrbitFeatures (tiInputMap u)) ≠
            activeOrbitClassifier (activeOrbitFeatures u))) ∧
      weightedTotalMass (activeOrbitWeight z0) <
        2 * weightedCorrectMass
          activeOrbitFeatures
          activeOrbitTarget
          (activeOrbitWeight z0)
          activeOrbitClassifier ∧
      0 <
        sliceMass
          (fun u : ExactVisiblePostSwitchSurface Z 1 => nonzeroColumn u.a)
          (activeOrbitWeight z0) ∧
      ¬ exactInputInvariantWeightedSupport (activeOrbitWeight z0) := by
  exact ⟨
    residualSideInformationCoverage_anchor_exactPostSwitch_activeOrbit_prediction_witness
      (Z := Z) z0,
    exactPostSwitch_activeOrbit_forces_fork_obstruction (Z := Z) z0
  ⟩

/-- Route-coverage anchor: positive doubled advantage from `(base, side)` over
an invariant base proves the residual side information is not source-derived. -/
theorem residualSideInformationCoverage_anchor_positive_advantage_forces_not_source_determined
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv : 0 < doubledAdvantage (fun x => (base x, side x)) y w h) :
    ¬ SideInfoDeterminedBy base side :=
  not_sideInfoDeterminedBy_of_pos_doubledAdvantage_invariant_base
    τ base side y w h hτ hbase hy hw hadv

/-- Route-coverage anchor: strict half-accuracy advantage from `(base, side)`
over an invariant base also proves the residual side information is not
source-derived. -/
theorem residualSideInformationCoverage_anchor_strict_half_advantage_forces_not_source_determined
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv :
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h) :
    ¬ SideInfoDeterminedBy base side :=
  not_sideInfoDeterminedBy_of_total_lt_two_mul_weightedCorrectMass_invariant_base
    τ base side y w h hτ hbase hy hw hadv

/-- Route-coverage anchor: positive doubled advantage from `(base, side)` over
an invariant base exposes a positive-weight same-base residual collision. -/
theorem residualSideInformationCoverage_anchor_positive_advantage_witnesses_same_base_residual_collision
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv : 0 < doubledAdvantage (fun x => (base x, side x)) y w h) :
    ∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x :=
  exists_positive_same_base_ne_side_of_pos_doubledAdvantage_invariant_base
    τ base side y w h hτ hbase hy hw hadv

/-- Route-coverage anchor: positive doubled advantage from `(base, side)` over
an invariant base exposes a supported residual collision over the base. -/
theorem residualSideInformationCoverage_anchor_positive_advantage_positiveWeight_collision
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv : 0 < doubledAdvantage (fun x => (base x, side x)) y w h) :
    PositiveWeightSideInfoCollisionOverBase base side w :=
  positiveWeightSideInfoCollisionOverBase_of_pos_doubledAdvantage_invariant_base
    τ base side y w h hτ hbase hy hw hadv

/-- Route-coverage anchor: positive doubled advantage from `(base, side)` over
an invariant base exposes a supported residual value whose equality predicate
is not source-only. -/
theorem residualSideInformationCoverage_anchor_positive_advantage_blocks_supported_source_predicate
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv : 0 < doubledAdvantage (fun x => (base x, side x)) y w h) :
    ∃ x, 0 < w x ∧
      ¬ SourceOnlyPredicateCapturesSideEq base side (side x) :=
  exists_positive_not_sourceOnlyPredicateCapturesSideEq_of_pos_doubledAdvantage_invariant_base
    τ base side y w h hτ hbase hy hw hadv

/-- Route-coverage anchor: if every supported residual equality test is
source-only, then `(base, side)` cannot have positive doubled advantage over an
invariant base. -/
theorem residualSideInformationCoverage_anchor_supported_source_predicates_no_positive_advantage
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hsource :
      ∀ x, 0 < w x → SourceOnlyPredicateCapturesSideEq base side (side x)) :
    ¬ 0 < doubledAdvantage (fun x => (base x, side x)) y w h :=
  not_pos_doubledAdvantage_pair_of_supported_sourceOnlyPredicateCapturesSideEq_invariant_base
    τ base side y w h hτ hbase hy hw hsource

/-- Route-coverage anchor: if the classifier's positive-support predictions
are already source-only over the invariant base, then syntactically mentioning
the residual side channel cannot create positive doubled advantage. -/
theorem residualSideInformationCoverage_anchor_supportwise_source_classifier_no_positive_advantage
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hsource : SupportwiseSourceOnlyPairClassifier base side w h) :
    ¬ 0 < doubledAdvantage (fun x => (base x, side x)) y w h :=
  not_pos_doubledAdvantage_pair_of_supportwiseSourceOnlyPairClassifier_invariant_base
    τ base side y w h hτ hbase hy hw hsource

/-- Route-coverage anchor: strict half-accuracy advantage from `(base, side)`
over an invariant base exposes a positive-weight same-base residual collision. -/
theorem residualSideInformationCoverage_anchor_strict_half_advantage_witnesses_same_base_residual_collision
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv :
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h) :
    ∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x :=
  exists_positive_same_base_ne_side_of_total_lt_two_mul_weightedCorrectMass_invariant_base
    τ base side y w h hτ hbase hy hw hadv

/-- Route-coverage anchor: strict half-accuracy advantage from `(base, side)`
over an invariant base exposes a supported residual collision over the base. -/
theorem residualSideInformationCoverage_anchor_strict_half_advantage_positiveWeight_collision
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv :
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h) :
    PositiveWeightSideInfoCollisionOverBase base side w :=
  positiveWeightSideInfoCollisionOverBase_of_total_lt_two_mul_weightedCorrectMass_invariant_base
    τ base side y w h hτ hbase hy hw hadv

/-- Route-coverage anchor: strict half-accuracy advantage from `(base, side)`
over an invariant base exposes a supported residual value whose equality
predicate is not source-only. -/
theorem residualSideInformationCoverage_anchor_strict_half_advantage_blocks_supported_source_predicate
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv :
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h) :
    ∃ x, 0 < w x ∧
      ¬ SourceOnlyPredicateCapturesSideEq base side (side x) :=
  exists_positive_not_sourceOnlyPredicateCapturesSideEq_of_total_lt_two_mul_weightedCorrectMass_invariant_base
    τ base side y w h hτ hbase hy hw hadv

/-- Route-coverage anchor: if every supported residual equality test is
source-only, then `(base, side)` cannot beat half accuracy over an invariant
base. -/
theorem residualSideInformationCoverage_anchor_supported_source_predicates_no_strict_half_advantage
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hsource :
      ∀ x, 0 < w x → SourceOnlyPredicateCapturesSideEq base side (side x)) :
    ¬ weightedTotalMass w <
      2 * weightedCorrectMass (fun x => (base x, side x)) y w h :=
  not_total_lt_two_mul_weightedCorrectMass_pair_of_supported_sourceOnlyPredicateCapturesSideEq_invariant_base
    τ base side y w h hτ hbase hy hw hsource

/-- Route-coverage anchor: in the half-accuracy formulation, source-only
positive-support predictions over the invariant base cannot beat chance even if
the classifier is written on `(base, side)`. -/
theorem residualSideInformationCoverage_anchor_supportwise_source_classifier_no_strict_half_advantage
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hsource : SupportwiseSourceOnlyPairClassifier base side w h) :
    ¬ weightedTotalMass w <
      2 * weightedCorrectMass (fun x => (base x, side x)) y w h :=
  not_total_lt_two_mul_weightedCorrectMass_pair_of_supportwiseSourceOnlyPairClassifier_invariant_base
    τ base side y w h hτ hbase hy hw hsource

/-- Route-coverage anchor: positive doubled advantage from `(base, side)` over
an invariant base must exhibit a supported involution pair where the final
classifier prediction changes. -/
theorem residualSideInformationCoverage_anchor_positive_advantage_prediction_separation
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv : 0 < doubledAdvantage (fun x => (base x, side x)) y w h) :
    ∃ x, 0 < w x ∧
      h (base (τ x), side (τ x)) ≠ h (base x, side x) :=
  exists_positive_prediction_ne_of_pos_doubledAdvantage_pair_invariant_base
    τ base side y w h hτ hbase hy hw hadv

/-- Route-coverage anchor: the strict half-accuracy formulation yields the same
supported prediction-separation witness. -/
theorem residualSideInformationCoverage_anchor_strict_half_advantage_prediction_separation
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv :
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h) :
    ∃ x, 0 < w x ∧
      h (base (τ x), side (τ x)) ≠ h (base x, side x) :=
  exists_positive_prediction_ne_of_total_lt_two_mul_weightedCorrectMass_pair_invariant_base
    τ base side y w h hτ hbase hy hw hadv

/-- Route-coverage anchor: positive doubled advantage from `(base, side)` over
an invariant base is not a weak residual repair.  It simultaneously forces
strictly positive residual resolved mass, makes the residual side information
non-source-determined, blocks any positive-support source-only classifier
description, and exposes supported same-base residual variation, a supported
non-source-only residual equality test, and supported prediction separation. -/
theorem residualSideInformationCoverage_anchor_positive_advantage_forces_supported_obstruction_package
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv : 0 < doubledAdvantage (fun x => (base x, side x)) y w h) :
    0 < resolvedMass τ side w ∧
      ¬ SideInfoDeterminedBy base side ∧
      ¬ SupportwiseSourceOnlyPairClassifier base side w h ∧
      (∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
      (∃ x, 0 < w x ∧
        ¬ SourceOnlyPredicateCapturesSideEq base side (side x)) ∧
      (∃ x, 0 < w x ∧
        h (base (τ x), side (τ x)) ≠ h (base x, side x)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact
      residualSideInformationCoverage_anchor_positive_advantage_forces_positive_resolvedMass
        τ base side y w h hτ hbase hy hw hadv
  · exact
      residualSideInformationCoverage_anchor_positive_advantage_forces_not_source_determined
        τ base side y w h hτ hbase hy hw hadv
  · intro hsource
    exact
      (residualSideInformationCoverage_anchor_supportwise_source_classifier_no_positive_advantage
        τ base side y w h hτ hbase hy hw hsource) hadv
  · exact
      residualSideInformationCoverage_anchor_positive_advantage_witnesses_same_base_residual_collision
        τ base side y w h hτ hbase hy hw hadv
  · exact
      residualSideInformationCoverage_anchor_positive_advantage_blocks_supported_source_predicate
        τ base side y w h hτ hbase hy hw hadv
  · exact
      residualSideInformationCoverage_anchor_positive_advantage_prediction_separation
        τ base side y w h hτ hbase hy hw hadv

/-- Route-coverage anchor: the strict half-accuracy formulation forces the same
residual-side-information obstruction package.  Beating half accuracy with
`(base, side)` over an invariant base already requires strictly positive
resolved mass, supported non-source residual variation, and supported
prediction separation. -/
theorem residualSideInformationCoverage_anchor_strict_half_advantage_forces_supported_obstruction_package
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv :
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h) :
    0 < resolvedMass τ side w ∧
      ¬ SideInfoDeterminedBy base side ∧
      ¬ SupportwiseSourceOnlyPairClassifier base side w h ∧
      (∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
      (∃ x, 0 < w x ∧
        ¬ SourceOnlyPredicateCapturesSideEq base side (side x)) ∧
      (∃ x, 0 < w x ∧
        h (base (τ x), side (τ x)) ≠ h (base x, side x)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact
      residualSideInformationCoverage_anchor_strict_half_advantage_forces_positive_resolvedMass
        τ base side y w h hτ hbase hy hw hadv
  · exact
      residualSideInformationCoverage_anchor_strict_half_advantage_forces_not_source_determined
        τ base side y w h hτ hbase hy hw hadv
  · intro hsource
    exact
      (residualSideInformationCoverage_anchor_supportwise_source_classifier_no_strict_half_advantage
        τ base side y w h hτ hbase hy hw hsource) hadv
  · exact
      residualSideInformationCoverage_anchor_strict_half_advantage_witnesses_same_base_residual_collision
        τ base side y w h hτ hbase hy hw hadv
  · exact
      residualSideInformationCoverage_anchor_strict_half_advantage_blocks_supported_source_predicate
        τ base side y w h hτ hbase hy hw hadv
  · exact
      residualSideInformationCoverage_anchor_strict_half_advantage_prediction_separation
        τ base side y w h hτ hbase hy hw hadv

/-- The current residual-side-information subledger is theorem-backed at the
narrow invariant-base boundary: same-source residual variation is not
source-only; invariant-base source-determined residuals cannot supply
advantage; and any surviving positive or strict-half advantage must already
force strictly positive resolved mass, supported residual variation, a
supported non-source-only residual equality test, and supported prediction
separation.  The ledger also records that the manuscript's exact post-switch
active orbit already realizes both the pure residual obstruction package and a
concrete prediction-separation witness on the concrete visible surface. -/
def V13ResidualSideInformationSubcoverage : Prop :=
  (∀ {Ω Base Side : Type*} {base : Ω → Base} {side : Ω → Side}
    {x y : Ω},
      base x = base y →
        side x ≠ side y →
          ¬ SideInfoDeterminedBy base side) ∧
  (∀ {Ω Base Side : Type*} {base : Ω → Base} {side : Ω → Side}
    {x y : Ω},
      base x = base y →
        side x ≠ side y →
          ¬ SourceOnlyPredicateCapturesSideEq base side (side x)) ∧
  (∀ {Ω Base : Type*} {base : Ω → Base} {target : Ω → Bool}
    {x y : Ω},
      base x = base y →
        target x ≠ target y →
          ¬ SourceOnlyBooleanClassifier base target) ∧
  (SideInfoCollisionOverBase residualSideInfoToyBase residualSideInfoToySide ∧
    ¬ SideInfoDeterminedBy residualSideInfoToyBase residualSideInfoToySide ∧
    ¬ SourceOnlyPredicateCapturesSideEq
      residualSideInfoToyBase residualSideInfoToySide false ∧
    ¬ SourceOnlyBooleanClassifier
      residualSideInfoToyBase residualSideInfoToySide) ∧
  (∀ {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side),
      (∀ x, base (τ x) = base x) →
        SideInfoDeterminedBy base side →
          ∀ x, side (τ x) = side x) ∧
  (∀ {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side) (w : α → ℕ),
      (∀ x, base (τ x) = base x) →
        SideInfoDeterminedBy base side →
          resolvedMass τ side w = 0) ∧
  (∀ {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool),
      Function.Involutive τ →
        (∀ x, base (τ x) = base x) →
          SideInfoDeterminedBy base side →
            (∀ x, y (τ x) = !(y x)) →
              (∀ x, w (τ x) = w x) →
                ¬ 0 < doubledAdvantage (fun x => (base x, side x)) y w h) ∧
  (∀ {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool),
      Function.Involutive τ →
        (∀ x, base (τ x) = base x) →
          (∀ x, y (τ x) = !(y x)) →
            (∀ x, w (τ x) = w x) →
              0 < doubledAdvantage (fun x => (base x, side x)) y w h →
                0 < resolvedMass τ side w) ∧
  (∀ {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool),
      Function.Involutive τ →
        (∀ x, base (τ x) = base x) →
          (∀ x, y (τ x) = !(y x)) →
            (∀ x, w (τ x) = w x) →
              weightedTotalMass w <
                  2 * weightedCorrectMass (fun x => (base x, side x)) y w h →
                0 < resolvedMass τ side w) ∧
  (∀ {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side) (w : α → ℕ),
      (∀ x, base (τ x) = base x) →
        0 < resolvedMass τ side w →
          ¬ SideInfoDeterminedBy base side ∧
            PositiveWeightSideInfoCollisionOverBase base side w ∧
            (∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
            (∃ x, 0 < w x ∧
              ¬ SourceOnlyPredicateCapturesSideEq base side (side x))) ∧
  (∀ {Z : Type*} [Fintype Z] (z0 : Z),
      0 < resolvedMass tiInputMap
          (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b)
          (activeOrbitWeight z0) ∧
        ¬ SideInfoDeterminedBy invariantVisibleData
            (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b) ∧
        PositiveWeightSideInfoCollisionOverBase invariantVisibleData
          (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b)
          (activeOrbitWeight z0) ∧
        (∃ u : ExactVisiblePostSwitchSurface Z 1,
          0 < activeOrbitWeight z0 u ∧
            invariantVisibleData (tiInputMap u) = invariantVisibleData u ∧
            (tiInputMap u).b ≠ u.b) ∧
        (∃ u : ExactVisiblePostSwitchSurface Z 1,
          0 < activeOrbitWeight z0 u ∧
            ¬ SourceOnlyPredicateCapturesSideEq invariantVisibleData
              (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b) (u.b))) ∧
  (∀ {Z : Type*} [Fintype Z] (z0 : Z),
      (∀ u : ExactVisiblePostSwitchSurface Z 1,
        invariantVisibleData (tiInputMap u) = invariantVisibleData u) ∧
      (∀ u : ExactVisiblePostSwitchSurface Z 1,
        activeOrbitWeight z0 (tiInputMap u) = activeOrbitWeight z0 u) ∧
      (∀ u : ExactVisiblePostSwitchSurface Z 1, 0 < activeOrbitWeight z0 u →
        activeOrbitTarget (tiInputMap u) = !(activeOrbitTarget u)) ∧
      0 <
        doubledAdvantage
          activeOrbitFeatures
          activeOrbitTarget
          (activeOrbitWeight z0)
          activeOrbitClassifier ∧
      (∃ u : ExactVisiblePostSwitchSurface Z 1,
        0 < activeOrbitWeight z0 u ∧
          activeOrbitClassifier (activeOrbitFeatures (tiInputMap u)) ≠
            activeOrbitClassifier (activeOrbitFeatures u))) ∧
  (∀ {Z : Type*} [Fintype Z] (z0 : Z),
      ((∀ u : ExactVisiblePostSwitchSurface Z 1,
          invariantVisibleData (tiInputMap u) = invariantVisibleData u) ∧
        (∀ u : ExactVisiblePostSwitchSurface Z 1,
          activeOrbitWeight z0 (tiInputMap u) = activeOrbitWeight z0 u) ∧
        (∀ u : ExactVisiblePostSwitchSurface Z 1, 0 < activeOrbitWeight z0 u →
          activeOrbitTarget (tiInputMap u) = !(activeOrbitTarget u)) ∧
        0 <
          doubledAdvantage
            activeOrbitFeatures
            activeOrbitTarget
            (activeOrbitWeight z0)
            activeOrbitClassifier ∧
        (∃ u : ExactVisiblePostSwitchSurface Z 1,
          0 < activeOrbitWeight z0 u ∧
            activeOrbitClassifier (activeOrbitFeatures (tiInputMap u)) ≠
              activeOrbitClassifier (activeOrbitFeatures u))) ∧
        weightedTotalMass (activeOrbitWeight z0) <
          2 * weightedCorrectMass
            activeOrbitFeatures
            activeOrbitTarget
            (activeOrbitWeight z0)
            activeOrbitClassifier ∧
        0 <
          sliceMass
            (fun u : ExactVisiblePostSwitchSurface Z 1 => nonzeroColumn u.a)
            (activeOrbitWeight z0) ∧
        ¬ exactInputInvariantWeightedSupport (activeOrbitWeight z0)) ∧
  (∀ {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool),
      Function.Involutive τ →
        (∀ x, base (τ x) = base x) →
          (∀ x, y (τ x) = !(y x)) →
            (∀ x, w (τ x) = w x) →
              0 < doubledAdvantage (fun x => (base x, side x)) y w h →
                ¬ SideInfoDeterminedBy base side) ∧
  (∀ {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool),
      Function.Involutive τ →
        (∀ x, base (τ x) = base x) →
          (∀ x, y (τ x) = !(y x)) →
            (∀ x, w (τ x) = w x) →
              weightedTotalMass w <
                  2 * weightedCorrectMass (fun x => (base x, side x)) y w h →
                ¬ SideInfoDeterminedBy base side) ∧
  (∀ {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool),
      Function.Involutive τ →
        (∀ x, base (τ x) = base x) →
          (∀ x, y (τ x) = !(y x)) →
            (∀ x, w (τ x) = w x) →
              0 < doubledAdvantage (fun x => (base x, side x)) y w h →
                PositiveWeightSideInfoCollisionOverBase base side w) ∧
  (∀ {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool),
      Function.Involutive τ →
        (∀ x, base (τ x) = base x) →
          (∀ x, y (τ x) = !(y x)) →
            (∀ x, w (τ x) = w x) →
              0 < doubledAdvantage (fun x => (base x, side x)) y w h →
                ∃ x, 0 < w x ∧
                  ¬ SourceOnlyPredicateCapturesSideEq base side (side x)) ∧
  (∀ {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool),
      Function.Involutive τ →
        (∀ x, base (τ x) = base x) →
          (∀ x, y (τ x) = !(y x)) →
            (∀ x, w (τ x) = w x) →
              (∀ x, 0 < w x →
                SourceOnlyPredicateCapturesSideEq base side (side x)) →
                  ¬ 0 < doubledAdvantage (fun x => (base x, side x)) y w h) ∧
  (∀ {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool),
      Function.Involutive τ →
        (∀ x, base (τ x) = base x) →
          (∀ x, y (τ x) = !(y x)) →
            (∀ x, w (τ x) = w x) →
              SupportwiseSourceOnlyPairClassifier base side w h →
                ¬ 0 < doubledAdvantage (fun x => (base x, side x)) y w h) ∧
  (∀ {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool),
      Function.Involutive τ →
        (∀ x, base (τ x) = base x) →
          (∀ x, y (τ x) = !(y x)) →
            (∀ x, w (τ x) = w x) →
              weightedTotalMass w <
                  2 * weightedCorrectMass (fun x => (base x, side x)) y w h →
                PositiveWeightSideInfoCollisionOverBase base side w) ∧
  (∀ {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool),
      Function.Involutive τ →
        (∀ x, base (τ x) = base x) →
          (∀ x, y (τ x) = !(y x)) →
            (∀ x, w (τ x) = w x) →
              weightedTotalMass w <
                  2 * weightedCorrectMass (fun x => (base x, side x)) y w h →
                ∃ x, 0 < w x ∧
                  ¬ SourceOnlyPredicateCapturesSideEq base side (side x)) ∧
  (∀ {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool),
      Function.Involutive τ →
        (∀ x, base (τ x) = base x) →
          (∀ x, y (τ x) = !(y x)) →
            (∀ x, w (τ x) = w x) →
              (∀ x, 0 < w x →
                SourceOnlyPredicateCapturesSideEq base side (side x)) →
                  ¬ weightedTotalMass w <
                    2 * weightedCorrectMass (fun x => (base x, side x)) y w h) ∧
  (∀ {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool),
      Function.Involutive τ →
        (∀ x, base (τ x) = base x) →
          (∀ x, y (τ x) = !(y x)) →
            (∀ x, w (τ x) = w x) →
              SupportwiseSourceOnlyPairClassifier base side w h →
                ¬ weightedTotalMass w <
                  2 * weightedCorrectMass (fun x => (base x, side x)) y w h) ∧
  (∀ {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool),
      Function.Involutive τ →
        (∀ x, base (τ x) = base x) →
          (∀ x, y (τ x) = !(y x)) →
            (∀ x, w (τ x) = w x) →
              0 < doubledAdvantage (fun x => (base x, side x)) y w h →
                ∃ x, 0 < w x ∧
                  h (base (τ x), side (τ x)) ≠ h (base x, side x)) ∧
  ∀ {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool),
      Function.Involutive τ →
        (∀ x, base (τ x) = base x) →
          (∀ x, y (τ x) = !(y x)) →
            (∀ x, w (τ x) = w x) →
              weightedTotalMass w <
                  2 * weightedCorrectMass (fun x => (base x, side x)) y w h →
                ∃ x, 0 < w x ∧
                  h (base (τ x), side (τ x)) ≠ h (base x, side x)

@[simp] theorem v13ResidualSideInformationSubcoverage :
    V13ResidualSideInformationSubcoverage := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Ω Base Side base side x y hbase hside
    exact
      residualSideInformationCoverage_anchor_collision_blocks_source_decoder
        hbase hside
  · intro Ω Base Side base side x y hbase hside
    exact
      residualSideInformationCoverage_anchor_collision_blocks_source_predicate
        hbase hside
  · intro Ω Base base target x y hbase htarget
    exact
      residualSideInformationCoverage_anchor_collision_blocks_source_boolean_classifier
        hbase htarget
  · exact residualSideInformationCoverage_anchor_toy_collision
  · intro α Base Side _Fintypeα τ base side hbase hdet
    exact
      residualSideInformationCoverage_anchor_source_determined_invariant_unresolved
        τ base side hbase hdet
  · intro α Base Side _Fintypeα τ base side w hbase hdet
    exact
      residualSideInformationCoverage_anchor_source_determined_zero_resolvedMass
        τ base side w hbase hdet
  · intro α Base Side _Fintypeα τ base side y w h hτ hbase hdet hy hw
    exact
      residualSideInformationCoverage_anchor_source_determined_no_positive_advantage
        τ base side y w h hτ hbase hdet hy hw
  · intro α Base Side _Fintypeα τ base side y w h hτ hbase hy hw hadv
    exact
      residualSideInformationCoverage_anchor_positive_advantage_forces_positive_resolvedMass
        τ base side y w h hτ hbase hy hw hadv
  · intro α Base Side _Fintypeα τ base side y w h hτ hbase hy hw hadv
    exact
      residualSideInformationCoverage_anchor_strict_half_advantage_forces_positive_resolvedMass
        τ base side y w h hτ hbase hy hw hadv
  · intro α Base Side _Fintypeα τ base side w hbase hmass
    exact
      residualSideInformationCoverage_anchor_positive_resolvedMass_forces_supported_obstruction_package
        τ base side w hbase hmass
  · intro Z _FintypeZ z0
    exact
      residualSideInformationCoverage_anchor_exactPostSwitch_activeOrbit_pure_residual_package
        (Z := Z) z0
  · intro Z _FintypeZ z0
    exact
      residualSideInformationCoverage_anchor_exactPostSwitch_activeOrbit_prediction_witness
        (Z := Z) z0
  · intro Z _FintypeZ z0
    exact
      residualSideInformationCoverage_anchor_exactPostSwitch_prediction_witness_forces_fork_obstruction
        (Z := Z) z0
  · intro α Base Side _Fintypeα τ base side y w h hτ hbase hy hw hadv
    exact
      residualSideInformationCoverage_anchor_positive_advantage_forces_not_source_determined
        τ base side y w h hτ hbase hy hw hadv
  · intro α Base Side _Fintypeα τ base side y w h hτ hbase hy hw hadv
    exact
      residualSideInformationCoverage_anchor_strict_half_advantage_forces_not_source_determined
        τ base side y w h hτ hbase hy hw hadv
  · intro α Base Side _Fintypeα τ base side y w h hτ hbase hy hw hadv
    exact
      residualSideInformationCoverage_anchor_positive_advantage_positiveWeight_collision
        τ base side y w h hτ hbase hy hw hadv
  · intro α Base Side _Fintypeα τ base side y w h hτ hbase hy hw hadv
    exact
      residualSideInformationCoverage_anchor_positive_advantage_blocks_supported_source_predicate
        τ base side y w h hτ hbase hy hw hadv
  · intro α Base Side _Fintypeα τ base side y w h hτ hbase hy hw hsource
    exact
      residualSideInformationCoverage_anchor_supported_source_predicates_no_positive_advantage
        τ base side y w h hτ hbase hy hw hsource
  · intro α Base Side _Fintypeα τ base side y w h hτ hbase hy hw hsource
    exact
      residualSideInformationCoverage_anchor_supportwise_source_classifier_no_positive_advantage
        τ base side y w h hτ hbase hy hw hsource
  · intro α Base Side _Fintypeα τ base side y w h hτ hbase hy hw hadv
    exact
      residualSideInformationCoverage_anchor_strict_half_advantage_positiveWeight_collision
        τ base side y w h hτ hbase hy hw hadv
  · intro α Base Side _Fintypeα τ base side y w h hτ hbase hy hw hadv
    exact
      residualSideInformationCoverage_anchor_strict_half_advantage_blocks_supported_source_predicate
        τ base side y w h hτ hbase hy hw hadv
  · intro α Base Side _Fintypeα τ base side y w h hτ hbase hy hw hsource
    exact
      residualSideInformationCoverage_anchor_supported_source_predicates_no_strict_half_advantage
        τ base side y w h hτ hbase hy hw hsource
  · intro α Base Side _Fintypeα τ base side y w h hτ hbase hy hw hsource
    exact
      residualSideInformationCoverage_anchor_supportwise_source_classifier_no_strict_half_advantage
        τ base side y w h hτ hbase hy hw hsource
  · intro α Base Side _Fintypeα τ base side y w h hτ hbase hy hw hadv
    exact
      residualSideInformationCoverage_anchor_positive_advantage_prediction_separation
        τ base side y w h hτ hbase hy hw hadv
  · intro α Base Side _Fintypeα τ base side y w h hτ hbase hy hw hadv
    exact
      residualSideInformationCoverage_anchor_strict_half_advantage_prediction_separation
        τ base side y w h hτ hbase hy hw hadv

/-- Route-coverage anchor: decoding every selected predictor from the one
global distinction-weakness scalar cannot cover all Boolean classifiers on a
nontrivial state space. -/
theorem globalWeaknessCoverage_anchor_distinction_family_not_surjective
    {U : Type u} [Fintype U] [DecidableEq U] [Nontrivial U]
    {Q : Type v} [Monoid Q] [CompleteLattice Q]
    (ev : GSLTEvidence U Q) {Index : Type*} {predict : Index → U → Bool}
    (hfamily : FamilyFactorsThroughDistinctionWeakness ev predict) :
    ¬ Function.Surjective predict :=
  not_surjective_familyFactorsThroughDistinctionWeakness_of_nontrivial
    ev hfamily

/-- Route-coverage anchor: decoding every selected predictor from the one
global non-distinction weakness scalar cannot cover all Boolean classifiers on a
nontrivial state space. -/
theorem globalWeaknessCoverage_anchor_nonDistinction_family_not_surjective
    {U : Type u} [Fintype U] [DecidableEq U] [Nontrivial U]
    {Q : Type v} [Monoid Q] [CompleteLattice Q]
    (ev : GSLTEvidence U Q) {Index : Type*} {predict : Index → U → Bool}
    (hfamily : FamilyFactorsThroughNonDistinctionWeakness ev predict) :
    ¬ Function.Surjective predict :=
  not_surjective_familyFactorsThroughNonDistinctionWeakness_of_nontrivial
    ev hfamily

/-- Route-coverage anchor: an invariant soft score has no signed signal if
weights are symmetric on every nonzero-score point. -/
theorem invariantScoreCoverage_anchor_score_support_weight_symmetric_zero_signal
    {α U : Type*} [Fintype α]
    (τ : α → α) (u : α → U) (y : α → Bool) (w : α → ℕ)
    (score : U → ℤ)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hsym : ∀ x, score (u x) ≠ 0 → w (τ x) = w x) :
    ∑ x : α, signedScoreContribution u y w score x = 0 :=
  signedScore_sum_eq_zero_of_score_support_weight_symmetric
    τ u y w score hτ hu hy hsym

/-- Route-coverage anchor: a nonzero invariant-score signal exposes a
nonzero-score sample point where the weighting is asymmetric across the
involution. -/
theorem invariantScoreCoverage_anchor_nonzero_signal_exposes_weight_asymmetric_score_point
    {α U : Type*} [Fintype α]
    (τ : α → α) (u : α → U) (y : α → Bool) (w : α → ℕ)
    (score : U → ℤ)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hsignal :
      (∑ x : α, signedScoreContribution u y w score x) ≠ 0) :
    ∃ x, w x ≠ w (τ x) ∧ score (u x) ≠ 0 :=
  exists_weight_asymmetric_score_point_of_signedScore_sum_ne_zero
    τ u y w score hτ hu hy hsignal

/-- Route-coverage anchor: if all positive-weight points remain inside an
unresolved symmetric slice, feature-only classification cannot have strict
advantage over half accuracy. -/
theorem asymmetryBudgetCoverage_anchor_support_inside_symmetric_slice_blocks_strict_advantage
    {α U : Type*} [Fintype α]
    (τ : α → α) (p : α → Prop) [DecidablePred p]
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool)
    (hτ : Function.Involutive τ)
    (hp : ∀ x, p x → p (τ x))
    (hu : ∀ x, p x → u (τ x) = u x)
    (hy : ∀ x, p x → y (τ x) = !(y x))
    (hw : ∀ x, p x → w (τ x) = w x)
    (hsupport : ∀ x, 0 < w x → p x) :
    ¬ weightedTotalMass w < 2 * weightedCorrectMass u y w h :=
  not_total_lt_two_mul_weightedCorrectMass_of_support_subset
    τ p u y w h hτ hp hu hy hw hsupport

/-- Route-coverage anchor: a strict feature-only advantage claim must expose a
positive-weight sample outside the unresolved symmetric slice. -/
theorem asymmetryBudgetCoverage_anchor_strict_advantage_exposes_outside_support
    {α U : Type*} [Fintype α]
    (τ : α → α) (p : α → Prop) [DecidablePred p]
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool)
    (hτ : Function.Involutive τ)
    (hp : ∀ x, p x → p (τ x))
    (hu : ∀ x, p x → u (τ x) = u x)
    (hy : ∀ x, p x → y (τ x) = !(y x))
    (hw : ∀ x, p x → w (τ x) = w x)
    (hadv : weightedTotalMass w < 2 * weightedCorrectMass u y w h) :
    ∃ x, 0 < w x ∧ ¬ p x :=
  exists_support_outside_of_total_lt_two_mul_weightedCorrectMass
    τ p u y w h hτ hp hu hy hw hadv

/-- Route-coverage anchor: a deterministic residual side channel that is
unresolved on every positive-weight source point cannot provide positive
doubled advantage. -/
theorem sideChannelCoverage_anchor_supportwise_unresolved_no_positive_advantage
    {α U V : Type*} [Fintype α]
    (τ : α → α) (u : α → U) (v : α → V)
    (y : α → Bool) (w : α → ℕ) (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hunresolved : ∀ x, 0 < w x → v (τ x) = v x) :
    ¬ 0 < doubledAdvantage (fun x => (u x, v x)) y w h :=
  not_pos_doubledAdvantage_pair_of_supportwise_unresolved
    τ u v y w h hτ hu hy hw hunresolved

/-- Route-coverage anchor: positive deterministic side-channel advantage
exposes a positive-weight source point where the side channel changes across
the involution. -/
theorem sideChannelCoverage_anchor_positive_advantage_resolution_witness
    {α U V : Type*} [Fintype α]
    (τ : α → α) (u : α → U) (v : α → V)
    (y : α → Bool) (w : α → ℕ) (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv : 0 < doubledAdvantage (fun x => (u x, v x)) y w h) :
    ∃ x, 0 < w x ∧ v (τ x) ≠ v x :=
  exists_resolving_point_of_pos_doubledAdvantage_pair
    τ u v y w h hτ hu hy hw hadv

/-- Route-coverage anchor: phrased directly at the success-rate surface, any
strict advantage over half accuracy from an invariant feature plus residual
side channel exposes a positive-weight point where the residual changes across
the involution. -/
theorem sideChannelCoverage_anchor_strict_half_accuracy_advantage_resolution_witness
    {α U V : Type*} [Fintype α]
    (τ : α → α) (u : α → U) (v : α → V)
    (y : α → Bool) (w : α → ℕ) (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv :
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (u x, v x)) y w h) :
    ∃ x, 0 < w x ∧ v (τ x) ≠ v x :=
  exists_resolving_point_of_total_lt_two_mul_weightedCorrectMass_pair
    τ u v y w h hτ hu hy hw hadv

/-- Route-coverage anchor: positive advantage from the exact post-switch
classifier on `((z, a_i), b)` exposes a positive-weight input where the
`b` side channel changes under the manuscript involution. -/
theorem postSwitchForkCoverage_anchor_positive_advantage_b_resolution_witness
    {Z : Type*} [Fintype Z] {k : ℕ}
    (y : PostSwitchInput Z k → Bool) (w : PostSwitchInput Z k → ℕ)
    (h : (Z × BitVec k) × BitVec k → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hadv : 0 < doubledAdvantage (fun u => (invariantProjection u, u.b)) y w h) :
    ∃ u : PostSwitchInput Z k, 0 < w u ∧ (tiInputMap u).b ≠ u.b :=
  exists_b_resolving_input_of_pos_doubledAdvantage_invariantProjection_with_b
    y w h hy hw hadv

/-- Route-coverage anchor: positive advantage from the exact post-switch
classifier on `((z, a_i), b)` exposes a positive-weight nonzero `a_i` column. -/
theorem postSwitchForkCoverage_anchor_positive_advantage_nonzeroColumn_witness
    {Z : Type*} [Fintype Z] {k : ℕ}
    (y : PostSwitchInput Z k → Bool) (w : PostSwitchInput Z k → ℕ)
    (h : (Z × BitVec k) × BitVec k → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hadv : 0 < doubledAdvantage (fun u => (invariantProjection u, u.b)) y w h) :
    ∃ u : PostSwitchInput Z k, 0 < w u ∧ nonzeroColumn u.a :=
  exists_nonzeroColumn_of_pos_doubledAdvantage_invariantProjection_with_b
    y w h hy hw hadv

/-- Route-coverage anchor: strict half-accuracy advantage from the exact
post-switch classifier on `((z, a_i), b)` exposes a positive-weight input
where the retained `b` side channel changes under the manuscript involution. -/
theorem postSwitchForkCoverage_anchor_strict_half_advantage_b_resolution_witness
    {Z : Type*} [Fintype Z] {k : ℕ}
    (y : PostSwitchInput Z k → Bool) (w : PostSwitchInput Z k → ℕ)
    (h : (Z × BitVec k) × BitVec k → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hadv :
      weightedTotalMass w <
        2 * weightedCorrectMass (fun u => (invariantProjection u, u.b)) y w h) :
    ∃ u : PostSwitchInput Z k, 0 < w u ∧ (tiInputMap u).b ≠ u.b :=
  exists_b_resolving_input_of_total_lt_two_mul_weightedCorrectMass_invariantProjection_with_b
    y w h hy hw hadv

/-- Route-coverage anchor: strict half-accuracy advantage from the exact
post-switch classifier on `((z, a_i), b)` exposes a positive-weight input on
a nonzero `a_i` column. -/
theorem postSwitchForkCoverage_anchor_strict_half_advantage_nonzeroColumn_witness
    {Z : Type*} [Fintype Z] {k : ℕ}
    (y : PostSwitchInput Z k → Bool) (w : PostSwitchInput Z k → ℕ)
    (h : (Z × BitVec k) × BitVec k → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hadv :
      weightedTotalMass w <
        2 * weightedCorrectMass (fun u => (invariantProjection u, u.b)) y w h) :
    ∃ u : PostSwitchInput Z k, 0 < w u ∧ nonzeroColumn u.a :=
  exists_nonzeroColumn_of_total_lt_two_mul_weightedCorrectMass_invariantProjection_with_b
    y w h hy hw hadv

/-- Route-coverage anchor: strict half-accuracy advantage from the exact
post-switch classifier on `((z, a_i), b)` already lands on the fork
obstruction surface.  It simultaneously exposes a positive-weight
`b`-resolving input, a positive-weight nonzero `a_i` column, and refutes the
manuscript's exact-input-invariant support premise. -/
theorem postSwitchForkCoverage_anchor_strict_half_advantage_fork_obstruction_package
    {Z : Type*} [Fintype Z] {k : ℕ}
    (y : PostSwitchInput Z k → Bool) (w : PostSwitchInput Z k → ℕ)
    (h : (Z × BitVec k) × BitVec k → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hadv :
      weightedTotalMass w <
        2 * weightedCorrectMass (fun u => (invariantProjection u, u.b)) y w h) :
    (∃ u : PostSwitchInput Z k, 0 < w u ∧ (tiInputMap u).b ≠ u.b) ∧
      (∃ u : PostSwitchInput Z k, 0 < w u ∧ nonzeroColumn u.a) ∧
      ¬ exactInputInvariantWeightedSupport w := by
  refine ⟨?_, ?_, ?_⟩
  · exact
      postSwitchForkCoverage_anchor_strict_half_advantage_b_resolution_witness
        y w h hy hw hadv
  · exact
      postSwitchForkCoverage_anchor_strict_half_advantage_nonzeroColumn_witness
        y w h hy hw hadv
  · exact
      not_exactInputInvariantWeightedSupport_of_total_lt_two_mul_weightedCorrectMass_invariantProjection_with_b
        y w h hy hw hadv

/-- Route-coverage anchor: a supportwise-unresolved finite-coin randomized
residual cannot provide positive doubled advantage. -/
theorem randomizedResidualCoverage_anchor_supportwise_unresolved_no_positive_advantage
    {α Coin U V : Type*} [Fintype α] [Fintype Coin]
    (τ : α → α) (u : α → U) (v : α → Coin → V)
    (y : α → Bool) (w : α → ℕ) (coinWeight : Coin → ℕ)
    (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hunresolved :
      ∀ x c, 0 < w x * coinWeight c → v (τ x) c = v x c) :
    ¬ 0 < doubledAdvantage
        (fun xr : α × Coin => (u xr.1, v xr.1 xr.2))
        (fun xr : α × Coin => y xr.1)
        (productWeight w coinWeight) h :=
  not_pos_doubledAdvantage_randomizedResidual_of_supportwise_unresolved
    τ u v y w coinWeight h hτ hu hy hw hunresolved

/-- Route-coverage anchor: positive finite-coin randomized-residual advantage
must expose a positive joint-support source/coin pair where the residual
changes across the involution. -/
theorem randomizedResidualCoverage_anchor_positive_advantage_witnesses_resolving_coin
    {α Coin U V : Type*} [Fintype α] [Fintype Coin]
    (τ : α → α) (u : α → U) (v : α → Coin → V)
    (y : α → Bool) (w : α → ℕ) (coinWeight : Coin → ℕ)
    (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv :
      0 < doubledAdvantage
        (fun xr : α × Coin => (u xr.1, v xr.1 xr.2))
        (fun xr : α × Coin => y xr.1)
        (productWeight w coinWeight) h) :
    ∃ x c, 0 < w x * coinWeight c ∧ v (τ x) c ≠ v x c :=
  exists_resolving_coin_of_pos_doubledAdvantage_randomizedResidual
    τ u v y w coinWeight h hτ hu hy hw hadv

/-- Route-coverage anchor: positive finite-coin randomized-residual advantage
is already witnessed by a deterministic positive-weight coin slice with
positive ordinary side-channel resolving mass. -/
theorem randomizedResidualCoverage_anchor_positive_advantage_witnesses_deterministic_coin_slice
    {α Coin U V : Type*} [Fintype α] [Fintype Coin]
    (τ : α → α) (u : α → U) (v : α → Coin → V)
    (y : α → Bool) (w : α → ℕ) (coinWeight : Coin → ℕ)
    (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv :
      0 < doubledAdvantage
        (fun xr : α × Coin => (u xr.1, v xr.1 xr.2))
        (fun xr : α × Coin => y xr.1)
        (productWeight w coinWeight) h) :
    ∃ c, 0 < coinWeight c ∧ 0 < resolvedMass τ (fun x => v x c) w :=
  exists_positive_coin_resolvedMass_of_pos_doubledAdvantage_randomizedResidual
    τ u v y w coinWeight h hτ hu hy hw hadv

/-- Route-coverage anchor: strict half-accuracy finite-coin randomized-
residual advantage is already witnessed by a deterministic positive-weight
coin slice with positive ordinary side-channel resolving mass. -/
theorem randomizedResidualCoverage_anchor_strict_half_advantage_witnesses_deterministic_coin_slice
    {α Coin U V : Type*} [Fintype α] [Fintype Coin]
    (τ : α → α) (u : α → U) (v : α → Coin → V)
    (y : α → Bool) (w : α → ℕ) (coinWeight : Coin → ℕ)
    (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv :
      weightedTotalMass (productWeight w coinWeight) <
        2 * weightedCorrectMass
          (fun xr : α × Coin => (u xr.1, v xr.1 xr.2))
          (fun xr : α × Coin => y xr.1)
          (productWeight w coinWeight) h) :
    ∃ c, 0 < coinWeight c ∧ 0 < resolvedMass τ (fun x => v x c) w :=
  exists_positive_coin_resolvedMass_of_total_lt_two_mul_weightedCorrectMass_randomizedResidual
    τ u v y w coinWeight h hτ hu hy hw hadv

/-- Route-coverage anchor: on the exact post-switch surface, supportwise-
unresolved finite-coin randomized residuals cannot provide positive doubled
advantage over the invariant projection. -/
theorem randomizedResidualCoverage_anchor_postSwitch_supportwise_unresolved_no_positive_advantage
    {Z Coin V : Type*} {k : ℕ} [Fintype Z] [Fintype Coin]
    (v : PostSwitchInput Z k → Coin → V)
    (y : PostSwitchInput Z k → Bool)
    (w : PostSwitchInput Z k → ℕ) (coinWeight : Coin → ℕ)
    (h : (Z × BitVec k) × V → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hunresolved :
      ∀ u c, 0 < w u * coinWeight c → v (tiInputMap u) c = v u c) :
    ¬ 0 < doubledAdvantage
        (fun xr : PostSwitchInput Z k × Coin =>
          (invariantProjection xr.1, v xr.1 xr.2))
        (fun xr : PostSwitchInput Z k × Coin => y xr.1)
        (productWeight w coinWeight) h :=
  not_pos_doubledAdvantage_randomizedResidual_invariantProjection_of_supportwise_unresolved
    v y w coinWeight h hy hw hunresolved

/-- Route-coverage anchor: on the exact post-switch surface, exact-input-
invariant support blocks strict half-accuracy finite-coin randomized-residual
advantage over the invariant projection. -/
theorem randomizedResidualCoverage_anchor_postSwitch_exact_support_no_strict_half_advantage
    {Z Coin V : Type*} {k : ℕ} [Fintype Z] [Fintype Coin]
    (v : PostSwitchInput Z k → Coin → V)
    (y : PostSwitchInput Z k → Bool)
    (w : PostSwitchInput Z k → ℕ) (coinWeight : Coin → ℕ)
    (h : (Z × BitVec k) × V → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hsupport : exactInputInvariantWeightedSupport w) :
    ¬ weightedTotalMass (productWeight w coinWeight) <
      2 * weightedCorrectMass
        (fun xr : PostSwitchInput Z k × Coin =>
          (invariantProjection xr.1, v xr.1 xr.2))
        (fun xr : PostSwitchInput Z k × Coin => y xr.1)
        (productWeight w coinWeight) h :=
  not_total_lt_two_mul_weightedCorrectMass_randomizedResidual_invariantProjection_of_exactInputInvariantWeightedSupport
    v y w coinWeight h hy hw hsupport

/-- Route-coverage anchor: on the exact post-switch surface, positive
finite-coin randomized-residual advantage must expose a positive joint-support
input/coin pair resolving the local-input switch. -/
theorem randomizedResidualCoverage_anchor_postSwitch_positive_advantage_witnesses_resolving_coin
    {Z Coin V : Type*} {k : ℕ} [Fintype Z] [Fintype Coin]
    (v : PostSwitchInput Z k → Coin → V)
    (y : PostSwitchInput Z k → Bool)
    (w : PostSwitchInput Z k → ℕ) (coinWeight : Coin → ℕ)
    (h : (Z × BitVec k) × V → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hadv :
      0 < doubledAdvantage
        (fun xr : PostSwitchInput Z k × Coin =>
          (invariantProjection xr.1, v xr.1 xr.2))
        (fun xr : PostSwitchInput Z k × Coin => y xr.1)
        (productWeight w coinWeight) h) :
    ∃ u c, 0 < w u * coinWeight c ∧ v (tiInputMap u) c ≠ v u c :=
  exists_resolving_coin_of_pos_doubledAdvantage_randomizedResidual_invariantProjection
    v y w coinWeight h hy hw hadv

/-- Route-coverage anchor: on the exact post-switch surface, positive
finite-coin randomized-residual advantage is already witnessed by a
deterministic positive-weight coin slice with positive ordinary resolving
mass for the local-input switch. -/
theorem randomizedResidualCoverage_anchor_postSwitch_positive_advantage_witnesses_deterministic_coin_slice
    {Z Coin V : Type*} {k : ℕ} [Fintype Z] [Fintype Coin]
    (v : PostSwitchInput Z k → Coin → V)
    (y : PostSwitchInput Z k → Bool)
    (w : PostSwitchInput Z k → ℕ) (coinWeight : Coin → ℕ)
    (h : (Z × BitVec k) × V → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hadv :
      0 < doubledAdvantage
        (fun xr : PostSwitchInput Z k × Coin =>
          (invariantProjection xr.1, v xr.1 xr.2))
        (fun xr : PostSwitchInput Z k × Coin => y xr.1)
        (productWeight w coinWeight) h) :
    ∃ c, 0 < coinWeight c ∧
      0 < resolvedMass tiInputMap (fun u => v u c) w :=
  exists_positive_coin_resolvedMass_of_pos_doubledAdvantage_randomizedResidual_invariantProjection
    v y w coinWeight h hy hw hadv

/-- Route-coverage anchor: on the exact post-switch surface, strict half-
accuracy finite-coin randomized-residual advantage is already witnessed by a
deterministic positive-weight coin slice with positive ordinary resolving
mass for the local-input switch. -/
theorem randomizedResidualCoverage_anchor_postSwitch_strict_half_advantage_witnesses_deterministic_coin_slice
    {Z Coin V : Type*} {k : ℕ} [Fintype Z] [Fintype Coin]
    (v : PostSwitchInput Z k → Coin → V)
    (y : PostSwitchInput Z k → Bool)
    (w : PostSwitchInput Z k → ℕ) (coinWeight : Coin → ℕ)
    (h : (Z × BitVec k) × V → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hadv :
      weightedTotalMass (productWeight w coinWeight) <
        2 * weightedCorrectMass
          (fun xr : PostSwitchInput Z k × Coin =>
            (invariantProjection xr.1, v xr.1 xr.2))
          (fun xr : PostSwitchInput Z k × Coin => y xr.1)
          (productWeight w coinWeight) h) :
    ∃ c, 0 < coinWeight c ∧
      0 < resolvedMass tiInputMap (fun u => v u c) w :=
  exists_positive_coin_resolvedMass_of_total_lt_two_mul_weightedCorrectMass_randomizedResidual_invariantProjection
    v y w coinWeight h hy hw hadv

/-- The current randomized-residual subledger is theorem-backed at the narrow
finite-coin/product boundary: randomized residuals stay under the ordinary
resolution budget on the source/coin product; supportwise unresolvedness kills
the joint resolving mass and therefore kills positive doubled advantage; any
surviving positive advantage must expose a positive joint-support resolving
coin and in fact a deterministic positive-weight coin slice with positive
ordinary resolving mass, with the same deterministic coin-slice conclusion
already available on the strict half-accuracy surface; and the exact post-
switch specialization inherits the same unresolved blocker, the strict-half
exact-support blocker, and the same deterministic coin-slice witness
obligations. -/
def V13RandomizedResidualSubcoverage : Prop :=
  (∀ {α Coin U V : Type*} [Fintype α] [Fintype Coin]
    (τ : α → α) (u : α → U) (v : α → Coin → V)
    (y : α → Bool) (w : α → ℕ) (coinWeight : Coin → ℕ)
    (h : U × V → Bool),
      Function.Involutive τ →
        (∀ x, u (τ x) = u x) →
          (∀ x, y (τ x) = !(y x)) →
            (∀ x, w (τ x) = w x) →
              doubledAdvantage
                  (fun xr : α × Coin => (u xr.1, v xr.1 xr.2))
                  (fun xr : α × Coin => y xr.1)
                  (productWeight w coinWeight) h
                ≤ randomizedResidualResolvedMass τ v w coinWeight) ∧
  (∀ {α Coin V : Type*} [Fintype α] [Fintype Coin]
    (τ : α → α) (v : α → Coin → V)
    (w : α → ℕ) (coinWeight : Coin → ℕ),
      (∀ x c, 0 < w x * coinWeight c → v (τ x) c = v x c) →
        randomizedResidualResolvedMass τ v w coinWeight = 0) ∧
  (∀ {α Coin U V : Type*} [Fintype α] [Fintype Coin]
    (τ : α → α) (u : α → U) (v : α → Coin → V)
    (y : α → Bool) (w : α → ℕ) (coinWeight : Coin → ℕ)
    (h : U × V → Bool),
      Function.Involutive τ →
        (∀ x, u (τ x) = u x) →
          (∀ x, y (τ x) = !(y x)) →
            (∀ x, w (τ x) = w x) →
              (∀ x c, 0 < w x * coinWeight c → v (τ x) c = v x c) →
                ¬ 0 < doubledAdvantage
                    (fun xr : α × Coin => (u xr.1, v xr.1 xr.2))
                    (fun xr : α × Coin => y xr.1)
                    (productWeight w coinWeight) h) ∧
  (∀ {α Coin U V : Type*} [Fintype α] [Fintype Coin]
    (τ : α → α) (u : α → U) (v : α → Coin → V)
    (y : α → Bool) (w : α → ℕ) (coinWeight : Coin → ℕ)
    (h : U × V → Bool),
      Function.Involutive τ →
        (∀ x, u (τ x) = u x) →
          (∀ x, y (τ x) = !(y x)) →
            (∀ x, w (τ x) = w x) →
              0 < doubledAdvantage
                  (fun xr : α × Coin => (u xr.1, v xr.1 xr.2))
                  (fun xr : α × Coin => y xr.1)
                  (productWeight w coinWeight) h →
                ∃ x c, 0 < w x * coinWeight c ∧ v (τ x) c ≠ v x c) ∧
  (∀ {α Coin U V : Type*} [Fintype α] [Fintype Coin]
    (τ : α → α) (u : α → U) (v : α → Coin → V)
    (y : α → Bool) (w : α → ℕ) (coinWeight : Coin → ℕ)
    (h : U × V → Bool),
      Function.Involutive τ →
        (∀ x, u (τ x) = u x) →
          (∀ x, y (τ x) = !(y x)) →
            (∀ x, w (τ x) = w x) →
              0 < doubledAdvantage
                  (fun xr : α × Coin => (u xr.1, v xr.1 xr.2))
                  (fun xr : α × Coin => y xr.1)
                  (productWeight w coinWeight) h →
                ∃ c, 0 < coinWeight c ∧ 0 < resolvedMass τ (fun x => v x c) w) ∧
  (∀ {α Coin U V : Type*} [Fintype α] [Fintype Coin]
    (τ : α → α) (u : α → U) (v : α → Coin → V)
    (y : α → Bool) (w : α → ℕ) (coinWeight : Coin → ℕ)
    (h : U × V → Bool),
      Function.Involutive τ →
        (∀ x, u (τ x) = u x) →
          (∀ x, y (τ x) = !(y x)) →
            (∀ x, w (τ x) = w x) →
              weightedTotalMass (productWeight w coinWeight) <
                2 * weightedCorrectMass
                  (fun xr : α × Coin => (u xr.1, v xr.1 xr.2))
                  (fun xr : α × Coin => y xr.1)
                  (productWeight w coinWeight) h →
                ∃ c, 0 < coinWeight c ∧
                  0 < resolvedMass τ (fun x => v x c) w) ∧
  (∀ {Z Coin V : Type*} {k : ℕ} [Fintype Z] [Fintype Coin]
    (v : PostSwitchInput Z k → Coin → V)
    (y : PostSwitchInput Z k → Bool)
    (w : PostSwitchInput Z k → ℕ) (coinWeight : Coin → ℕ)
    (h : (Z × BitVec k) × V → Bool),
      (∀ u, y (tiInputMap u) = !(y u)) →
        (∀ u, w (tiInputMap u) = w u) →
          (∀ u c, 0 < w u * coinWeight c → v (tiInputMap u) c = v u c) →
            ¬ 0 < doubledAdvantage
                (fun xr : PostSwitchInput Z k × Coin =>
                  (invariantProjection xr.1, v xr.1 xr.2))
                (fun xr : PostSwitchInput Z k × Coin => y xr.1)
                (productWeight w coinWeight) h) ∧
  (∀ {Z Coin V : Type*} {k : ℕ} [Fintype Z] [Fintype Coin]
    (v : PostSwitchInput Z k → Coin → V)
    (y : PostSwitchInput Z k → Bool)
    (w : PostSwitchInput Z k → ℕ) (coinWeight : Coin → ℕ)
    (h : (Z × BitVec k) × V → Bool),
      (∀ u, y (tiInputMap u) = !(y u)) →
        (∀ u, w (tiInputMap u) = w u) →
          exactInputInvariantWeightedSupport w →
            ¬ weightedTotalMass (productWeight w coinWeight) <
              2 * weightedCorrectMass
                (fun xr : PostSwitchInput Z k × Coin =>
                  (invariantProjection xr.1, v xr.1 xr.2))
                (fun xr : PostSwitchInput Z k × Coin => y xr.1)
                (productWeight w coinWeight) h) ∧
  (∀ {Z Coin V : Type*} {k : ℕ} [Fintype Z] [Fintype Coin]
    (v : PostSwitchInput Z k → Coin → V)
    (y : PostSwitchInput Z k → Bool)
    (w : PostSwitchInput Z k → ℕ) (coinWeight : Coin → ℕ)
    (h : (Z × BitVec k) × V → Bool),
      (∀ u, y (tiInputMap u) = !(y u)) →
        (∀ u, w (tiInputMap u) = w u) →
          0 < doubledAdvantage
              (fun xr : PostSwitchInput Z k × Coin =>
                (invariantProjection xr.1, v xr.1 xr.2))
              (fun xr : PostSwitchInput Z k × Coin => y xr.1)
              (productWeight w coinWeight) h →
            ∃ u c, 0 < w u * coinWeight c ∧ v (tiInputMap u) c ≠ v u c) ∧
  (∀ {Z Coin V : Type*} {k : ℕ} [Fintype Z] [Fintype Coin]
    (v : PostSwitchInput Z k → Coin → V)
    (y : PostSwitchInput Z k → Bool)
    (w : PostSwitchInput Z k → ℕ) (coinWeight : Coin → ℕ)
    (h : (Z × BitVec k) × V → Bool),
      (∀ u, y (tiInputMap u) = !(y u)) →
        (∀ u, w (tiInputMap u) = w u) →
          0 < doubledAdvantage
              (fun xr : PostSwitchInput Z k × Coin =>
                (invariantProjection xr.1, v xr.1 xr.2))
              (fun xr : PostSwitchInput Z k × Coin => y xr.1)
              (productWeight w coinWeight) h →
            ∃ c, 0 < coinWeight c ∧
              0 < resolvedMass tiInputMap (fun u => v u c) w) ∧
  ∀ {Z Coin V : Type*} {k : ℕ} [Fintype Z] [Fintype Coin]
    (v : PostSwitchInput Z k → Coin → V)
    (y : PostSwitchInput Z k → Bool)
    (w : PostSwitchInput Z k → ℕ) (coinWeight : Coin → ℕ)
    (h : (Z × BitVec k) × V → Bool),
      (∀ u, y (tiInputMap u) = !(y u)) →
        (∀ u, w (tiInputMap u) = w u) →
          weightedTotalMass (productWeight w coinWeight) <
            2 * weightedCorrectMass
              (fun xr : PostSwitchInput Z k × Coin =>
                (invariantProjection xr.1, v xr.1 xr.2))
              (fun xr : PostSwitchInput Z k × Coin => y xr.1)
              (productWeight w coinWeight) h →
            ∃ c, 0 < coinWeight c ∧
              0 < resolvedMass tiInputMap (fun u => v u c) w

@[simp] theorem v13RandomizedResidualSubcoverage :
    V13RandomizedResidualSubcoverage := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro α Coin U V _Fintypeα _FintypeCoin τ u v y w coinWeight h hτ hu hy hw
    exact
      doubledAdvantage_randomizedResidual_le_resolvedMass
        τ u v y w coinWeight h hτ hu hy hw
  · intro α Coin V _Fintypeα _FintypeCoin τ v w coinWeight hunresolved
    exact
      randomizedResidualResolvedMass_eq_zero_of_supportwise_unresolved
        τ v w coinWeight hunresolved
  · intro α Coin U V _Fintypeα _FintypeCoin τ u v y w coinWeight h hτ hu hy hw hunresolved
    exact
      randomizedResidualCoverage_anchor_supportwise_unresolved_no_positive_advantage
        τ u v y w coinWeight h hτ hu hy hw hunresolved
  · intro α Coin U V _Fintypeα _FintypeCoin τ u v y w coinWeight h hτ hu hy hw hadv
    exact
      randomizedResidualCoverage_anchor_positive_advantage_witnesses_resolving_coin
        τ u v y w coinWeight h hτ hu hy hw hadv
  · intro α Coin U V _Fintypeα _FintypeCoin τ u v y w coinWeight h hτ hu hy hw hadv
    exact
      randomizedResidualCoverage_anchor_positive_advantage_witnesses_deterministic_coin_slice
        τ u v y w coinWeight h hτ hu hy hw hadv
  · intro α Coin U V _Fintypeα _FintypeCoin τ u v y w coinWeight h hτ hu hy hw hadv
    exact
      randomizedResidualCoverage_anchor_strict_half_advantage_witnesses_deterministic_coin_slice
        τ u v y w coinWeight h hτ hu hy hw hadv
  · intro Z Coin V k _FintypeZ _FintypeCoin v y w coinWeight h hy hw hunresolved
    exact
      randomizedResidualCoverage_anchor_postSwitch_supportwise_unresolved_no_positive_advantage
        v y w coinWeight h hy hw hunresolved
  · intro Z Coin V k _FintypeZ _FintypeCoin v y w coinWeight h hy hw hsupport
    exact
      randomizedResidualCoverage_anchor_postSwitch_exact_support_no_strict_half_advantage
        v y w coinWeight h hy hw hsupport
  · intro Z Coin V k _FintypeZ _FintypeCoin v y w coinWeight h hy hw hadv
    exact
      randomizedResidualCoverage_anchor_postSwitch_positive_advantage_witnesses_resolving_coin
        v y w coinWeight h hy hw hadv
  · intro Z Coin V k _FintypeZ _FintypeCoin v y w coinWeight h hy hw hadv
    exact
      randomizedResidualCoverage_anchor_postSwitch_positive_advantage_witnesses_deterministic_coin_slice
        v y w coinWeight h hy hw hadv
  · intro Z Coin V k _FintypeZ _FintypeCoin v y w coinWeight h hy hw hadv
    exact
      randomizedResidualCoverage_anchor_postSwitch_strict_half_advantage_witnesses_deterministic_coin_slice
        v y w coinWeight h hy hw hadv

/-- Route-coverage anchor for the `Kpoly` gap: at the current abstraction
level, a clocked exact-visible realization family is exactly an exact visible
compression target.  The remaining `Kpoly` burden is therefore a real
small-class theorem for the actual switched family, not clock bookkeeping. -/
theorem kpolyCoverage_anchor_clockedRealization_iff_exactVisibleCompressionTarget
    {Z : Type*} {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} :
    (∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F) ↔
      ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s :=
  exists_clockedExactVisibleRealization_iff_exactVisibleCompressionTarget
    (G := G) (s := s) (clock := clock)

/-- Route-coverage anchor: the full raw `(a,b)` Boolean rule family is not
realized by the fixed-order raw decision-list class at positive width. -/
theorem kpolyCoverage_anchor_fullABRule_not_rawDecisionList_of_pos
    {k : ℕ} (hk : 0 < k) :
    ¬ RealizedByABDecisionListFamily (k := k) (fullABRuleFamily k) :=
  fullABRuleFamily_not_realizedByABDecisionListFamily_of_pos (k := k) hk

/-- Route-coverage anchor: the exact visible pullback of the full raw `(a,b)`
rule family is not realized by the raw exact-surface decision-list class at
positive width. -/
theorem kpolyCoverage_anchor_fullExactABRule_not_rawExactDecisionList_of_pos
    (Z : Type*) [Inhabited Z] {k : ℕ} (hk : 0 < k) :
    ¬ RealizedByRawExactABDecisionListFamily (Z := Z) (k := k)
        (fullExactABRuleFamily Z k) :=
  fullExactABRuleFamily_not_realizedByRawExactABDecisionListFamily_of_pos
    (Z := Z) (k := k) hk

/-- Route-coverage anchor: the full raw `(a,b)` Boolean rule family is not
realized by shared affine-feature families below the reduced truth-table
threshold. -/
theorem kpolyCoverage_anchor_fullABRule_not_sharedAffineFeature_of_lt_cardFormula
    {r k : ℕ} (features : Fin r → AffineColumnCode (k + k))
    (hs : 2 ^ r < 2 ^ (2 * k)) :
    ¬ RealizedBySharedABAffineFeatureFamily (r := r) (k := k) features
        (fullABRuleFamily k) :=
  fullABRuleFamily_not_realizedBySharedABAffineFeatureFamily_of_lt_cardFormula
    (r := r) (k := k) features hs

/-- Route-coverage anchor: the full raw `(a,b)` Boolean rule family is not
realized by shared sparse-threshold families below the reduced truth-table
threshold. -/
theorem kpolyCoverage_anchor_fullABRule_not_sharedSparseThreshold_of_lt_cardFormula
    {r k : ℕ} (features : Fin r → AffineColumnCode (k + k))
    (hs : 2 * r < 2 ^ (2 * k)) :
    ¬ RealizedBySharedABSparseThresholdAffineFamily (r := r) (k := k) features
        (fullABRuleFamily k) :=
  fullABRuleFamily_not_realizedBySharedABSparseThresholdAffineFamily_of_lt_cardFormula
    (r := r) (k := k) features hs

/-- Route-coverage anchor: the full raw `(a,b)` Boolean rule family is not
realized by shared decision-list families below the reduced truth-table
threshold. -/
theorem kpolyCoverage_anchor_fullABRule_not_sharedDecisionList_of_lt_cardFormula
    {r k : ℕ} (features : Fin r → AffineColumnCode (k + k))
    (hs : r + 1 < 2 ^ (2 * k)) :
    ¬ RealizedBySharedABAffineDecisionListFamily (r := r) (k := k) features
        (fullABRuleFamily k) :=
  fullABRuleFamily_not_realizedBySharedABAffineDecisionListFamily_of_lt_cardFormula
    (r := r) (k := k) features hs

/-- Route-coverage anchor: the exact visible pullback of the full raw `(a,b)`
rule family is not realized by shared affine-feature exact families below the
reduced truth-table threshold. -/
theorem kpolyCoverage_anchor_fullExactABRule_not_sharedExactAffineFeature_of_lt_cardFormula
    (Z : Type*) [Inhabited Z] {r k : ℕ}
    (features : Fin r → AffineColumnCode (k + k))
    (hs : 2 ^ r < 2 ^ (2 * k)) :
    ¬ RealizedBySharedExactABAffineFeatureFamily (Z := Z) (r := r) (k := k)
        features (fullExactABRuleFamily Z k) :=
  fullExactABRuleFamily_not_realizedBySharedExactABAffineFeatureFamily_of_lt_cardFormula
    (Z := Z) (r := r) (k := k) features hs

/-- Route-coverage anchor: the exact visible pullback of the full raw `(a,b)`
rule family is not realized by shared sparse-threshold exact families below the
reduced truth-table threshold. -/
theorem kpolyCoverage_anchor_fullExactABRule_not_sharedExactSparseThreshold_of_lt_cardFormula
    (Z : Type*) [Inhabited Z] {r k : ℕ}
    (features : Fin r → AffineColumnCode (k + k))
    (hs : 2 * r < 2 ^ (2 * k)) :
    ¬ RealizedBySharedExactABSparseThresholdAffineFamily (Z := Z) (r := r) (k := k)
        features (fullExactABRuleFamily Z k) :=
  fullExactABRuleFamily_not_realizedBySharedExactABSparseThresholdAffineFamily_of_lt_cardFormula
    (Z := Z) (r := r) (k := k) features hs

/-- Route-coverage anchor: the exact visible pullback of the full raw `(a,b)`
rule family is not realized by shared decision-list exact families below the
reduced truth-table threshold. -/
theorem kpolyCoverage_anchor_fullExactABRule_not_sharedExactDecisionList_of_lt_cardFormula
    (Z : Type*) [Inhabited Z] {r k : ℕ}
    (features : Fin r → AffineColumnCode (k + k))
    (hs : r + 1 < 2 ^ (2 * k)) :
    ¬ RealizedBySharedExactABAffineDecisionListFamily (Z := Z) (r := r) (k := k)
        features (fullExactABRuleFamily Z k) :=
  fullExactABRuleFamily_not_realizedBySharedExactABAffineDecisionListFamily_of_lt_cardFormula
    (Z := Z) (r := r) (k := k) features hs

/-- Route-coverage anchor: shared affine-feature families cannot realize a
finite probe image larger than their truth-table combiner image. -/
theorem kpolyCoverage_anchor_not_sharedABAffineFeature_of_injective_probe_of_lt_budgetImageCard
    {Probe : Type*} [Fintype Probe] {r k : ℕ} {Index : Type*}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hprobe : ∀ p, ∃ i, H.predict i = target p)
    (hcard : 2 ^ (2 ^ r) < Fintype.card Probe) :
    ¬ RealizedBySharedABAffineFeatureFamily (r := r) (k := k) features H :=
  not_realizedBySharedABAffineFeatureFamily_of_injective_probe_of_lt_budgetImageCard
    target hinj hprobe hcard

/-- Route-coverage anchor: shared sparse-threshold families cannot realize a
finite probe image larger than their combiner image. -/
theorem kpolyCoverage_anchor_not_sharedABSparseThreshold_of_injective_probe_of_lt_budgetImageCard
    {Probe : Type*} [Fintype Probe] {r k : ℕ} {Index : Type*}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hprobe : ∀ p, ∃ i, H.predict i = target p)
    (hcard : 2 ^ (2 * r) < Fintype.card Probe) :
    ¬ RealizedBySharedABSparseThresholdAffineFamily (r := r) (k := k) features H :=
  not_realizedBySharedABSparseThresholdAffineFamily_of_injective_probe_of_lt_budgetImageCard
    target hinj hprobe hcard

/-- Route-coverage anchor: shared decision-list families cannot realize a
finite probe image larger than their combiner image. -/
theorem kpolyCoverage_anchor_not_sharedABDecisionList_of_injective_probe_of_lt_budgetImageCard
    {Probe : Type*} [Fintype Probe] {r k : ℕ} {Index : Type*}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hprobe : ∀ p, ∃ i, H.predict i = target p)
    (hcard : 2 ^ (r + 1) < Fintype.card Probe) :
    ¬ RealizedBySharedABAffineDecisionListFamily (r := r) (k := k) features H :=
  not_realizedBySharedABAffineDecisionListFamily_of_injective_probe_of_lt_budgetImageCard
    target hinj hprobe hcard

/-- Route-coverage anchor: the shared affine-feature finite-probe obstruction
lifts through exact visible pullback along `abVisibleData`. -/
theorem kpolyCoverage_anchor_not_sharedExactABAffineFeature_of_factorsThrough_ab_and_injective_probe_of_lt_budgetImageCard
    {Z Probe : Type*} [Inhabited Z] [Fintype Probe]
    {r k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hprobe : ∀ p, ∃ i, H.predict i = target p)
    (hcard : 2 ^ (2 ^ r) < Fintype.card Probe)
    (hfactor : G.FactorsThrough abVisibleData H) :
    ¬ RealizedBySharedExactABAffineFeatureFamily
        (Z := Z) (r := r) (k := k) features G :=
  not_realizedBySharedExactABAffineFeatureFamily_of_factorsThrough_ab_and_injective_probe_of_lt_budgetImageCard
    target hinj hprobe hcard hfactor

/-- Route-coverage anchor: the shared sparse-threshold finite-probe obstruction
lifts through exact visible pullback along `abVisibleData`. -/
theorem kpolyCoverage_anchor_not_sharedExactABSparseThreshold_of_factorsThrough_ab_and_injective_probe_of_lt_budgetImageCard
    {Z Probe : Type*} [Inhabited Z] [Fintype Probe]
    {r k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hprobe : ∀ p, ∃ i, H.predict i = target p)
    (hcard : 2 ^ (2 * r) < Fintype.card Probe)
    (hfactor : G.FactorsThrough abVisibleData H) :
    ¬ RealizedBySharedExactABSparseThresholdAffineFamily
        (Z := Z) (r := r) (k := k) features G :=
  not_realizedBySharedExactABSparseThresholdAffineFamily_of_factorsThrough_ab_and_injective_probe_of_lt_budgetImageCard
    target hinj hprobe hcard hfactor

/-- Route-coverage anchor: the shared decision-list finite-probe obstruction
lifts through exact visible pullback along `abVisibleData`. -/
theorem kpolyCoverage_anchor_not_sharedExactABDecisionList_of_factorsThrough_ab_and_injective_probe_of_lt_budgetImageCard
    {Z Probe : Type*} [Inhabited Z] [Fintype Probe]
    {r k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hprobe : ∀ p, ∃ i, H.predict i = target p)
    (hcard : 2 ^ (r + 1) < Fintype.card Probe)
    (hfactor : G.FactorsThrough abVisibleData H) :
    ¬ RealizedBySharedExactABAffineDecisionListFamily
        (Z := Z) (r := r) (k := k) features G :=
  not_realizedBySharedExactABAffineDecisionListFamily_of_factorsThrough_ab_and_injective_probe_of_lt_budgetImageCard
    target hinj hprobe hcard hfactor

/-- Route-coverage anchor: an exact family invariant under raw `(a,b)` cannot
select any target rule that separates a same-`(a,b)` exact fiber. -/
theorem kpolyCoverage_anchor_not_exists_predict_eq_of_abVisibleInvariant_of_abFiberSeparatingRule
    {Z : Type*} {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hinv : ABVisibleInvariant (Z := Z) (k := k) G)
    {rule : ExactVisiblePostSwitchSurface Z k → Bool}
    (hsep : ABFiberSeparatingRule (Z := Z) (k := k) rule) :
    ¬ ∃ i, G.predict i = rule :=
  not_exists_predict_eq_of_abVisibleInvariant_of_abFiberSeparatingRule
    (Z := Z) (k := k) hinv hsep

/-- Route-coverage anchor: a raw `(a,b)`-invariant exact family cannot select
the concrete hidden-`z` projection rule. -/
theorem kpolyCoverage_anchor_not_exists_predict_eq_boolZProjectionRule_of_abVisibleInvariant
    {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Bool k Index}
    (hinv : ABVisibleInvariant (Z := Bool) (k := k) G) :
    ¬ ∃ i, G.predict i = boolZProjectionRule (k := k) :=
  not_exists_predict_eq_boolZProjectionRule_of_abVisibleInvariant
    (k := k) hinv

/-- Route-coverage anchor: a raw `(a,b)`-invariant exact predictor must have a
positive-mass disagreement whenever the target separates two positive-mass
points in one same-`(a,b)` exact fiber. -/
theorem kpolyCoverage_anchor_exists_pos_mass_disagreement_of_abVisibleInvariant_predict_of_abFiberSeparation
    {Z : Type*} {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hinv : ABVisibleInvariant (Z := Z) (k := k) G)
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {target : ExactVisiblePostSwitchSurface Z k → Bool}
    (i : Index)
    {u v : ExactVisiblePostSwitchSurface Z k}
    (hab : abVisibleData u = abVisibleData v)
    (hsep : target u ≠ target v)
    (huμ : μ u ≠ 0) (hvμ : μ v ≠ 0) :
    ∃ x, μ x ≠ 0 ∧ G.predict i x ≠ target x :=
  exists_pos_mass_disagreement_of_abVisibleInvariant_predict_of_abFiberSeparation
    (Z := Z) (k := k) hinv (μ := μ) (target := target) i
    hab hsep huμ hvμ

/-- Route-coverage anchor: on any distribution that puts positive mass on the
two default same-`(a,b)` hidden-bit points, a raw `(a,b)`-invariant predictor
must disagree with the hidden-`z` projection on positive mass. -/
theorem kpolyCoverage_anchor_exists_pos_mass_disagreement_boolZProjectionRule_of_abVisibleInvariant
    {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Bool k Index}
    (hinv : ABVisibleInvariant (Z := Bool) (k := k) G)
    {μ : PMF (ExactVisiblePostSwitchSurface Bool k)}
    (i : Index)
    (hfalse : μ ⟨false, default, default⟩ ≠ 0)
    (htrue : μ ⟨true, default, default⟩ ≠ 0) :
    ∃ x, μ x ≠ 0 ∧ G.predict i x ≠ boolZProjectionRule (k := k) x :=
  exists_pos_mass_disagreement_of_abVisibleInvariant_predict_boolZProjectionRule
    (k := k) hinv (μ := μ) i hfalse htrue

/-- Route-coverage anchor: positive-mass same-`(a,b)` target separation forces
agreement mass below one for every raw `(a,b)`-invariant exact predictor. -/
theorem kpolyCoverage_anchor_agreementMass_lt_one_of_abVisibleInvariant_predict_of_abFiberSeparation
    {Z : Type*} [Fintype Z] {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hinv : ABVisibleInvariant (Z := Z) (k := k) G)
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {target : ExactVisiblePostSwitchSurface Z k → Bool}
    (i : Index)
    {u v : ExactVisiblePostSwitchSurface Z k}
    (hab : abVisibleData u = abVisibleData v)
    (hsep : target u ≠ target v)
    (huμ : μ u ≠ 0) (hvμ : μ v ≠ 0) :
    agreementMass μ target (G.predict i) < 1 :=
  agreementMass_lt_one_of_abVisibleInvariant_predict_of_abFiberSeparation
    (Z := Z) (k := k) hinv (μ := μ) (target := target) i
    hab hsep huμ hvμ

/-- Route-coverage anchor: on a distribution supporting both default
hidden-bit sides of one same-`(a,b)` fiber, a raw `(a,b)`-invariant exact
predictor has agreement mass below one against the hidden-`z` projection. -/
theorem kpolyCoverage_anchor_agreementMass_lt_one_boolZProjectionRule_of_abVisibleInvariant
    {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Bool k Index}
    (hinv : ABVisibleInvariant (Z := Bool) (k := k) G)
    {μ : PMF (ExactVisiblePostSwitchSurface Bool k)}
    (i : Index)
    (hfalse : μ ⟨false, default, default⟩ ≠ 0)
    (htrue : μ ⟨true, default, default⟩ ≠ 0) :
    agreementMass μ (boolZProjectionRule (k := k)) (G.predict i) < 1 :=
  agreementMass_lt_one_of_abVisibleInvariant_predict_boolZProjectionRule
    (k := k) hinv (μ := μ) i hfalse htrue

/-- Route-coverage anchor: positive-mass same-`(a,b)` target separation rules
out every perfect-agreement member of a raw `(a,b)`-invariant exact family. -/
theorem kpolyCoverage_anchor_not_exists_agreementMass_eq_one_of_abVisibleInvariant_of_abFiberSeparation
    {Z : Type*} [Fintype Z] {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hinv : ABVisibleInvariant (Z := Z) (k := k) G)
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {target : ExactVisiblePostSwitchSurface Z k → Bool}
    {u v : ExactVisiblePostSwitchSurface Z k}
    (hab : abVisibleData u = abVisibleData v)
    (hsep : target u ≠ target v)
    (huμ : μ u ≠ 0) (hvμ : μ v ≠ 0) :
    ¬ ∃ i, agreementMass μ target (G.predict i) = 1 :=
  not_exists_agreementMass_eq_one_of_abVisibleInvariant_of_abFiberSeparation
    (Z := Z) (k := k) hinv (μ := μ) (target := target)
    hab hsep huμ hvμ

/-- Route-coverage anchor: on a distribution supporting both default hidden-bit
sides of one same-`(a,b)` fiber, a raw `(a,b)`-invariant exact family has no
member with perfect agreement against the hidden-`z` projection. -/
theorem kpolyCoverage_anchor_not_exists_agreementMass_eq_one_boolZProjectionRule_of_abVisibleInvariant
    {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Bool k Index}
    (hinv : ABVisibleInvariant (Z := Bool) (k := k) G)
    {μ : PMF (ExactVisiblePostSwitchSurface Bool k)}
    (hfalse : μ ⟨false, default, default⟩ ≠ 0)
    (htrue : μ ⟨true, default, default⟩ ≠ 0) :
    ¬ ∃ i, agreementMass μ (boolZProjectionRule (k := k)) (G.predict i) = 1 :=
  not_exists_agreementMass_eq_one_boolZProjectionRule_of_abVisibleInvariant
    (k := k) hinv (μ := μ) hfalse htrue

/-- Route-coverage anchor: a raw `(a,b)`-invariant exact family is not
surjective onto exact visible Boolean rules when `Z` is nontrivial. -/
theorem kpolyCoverage_anchor_not_surjective_predict_of_abVisibleInvariant_of_nontrivial
    {Z : Type*} [Nontrivial Z] {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hinv : ABVisibleInvariant (Z := Z) (k := k) G) :
    ¬ Function.Surjective G.predict :=
  not_surjective_predict_of_abVisibleInvariant_of_nontrivial
    (Z := Z) (k := k) hinv

/-- Route-coverage anchor: the exact visible / clocked `Kpoly` target is exactly
a finite predictor-image cover of size at most `2^s`. -/
theorem kpolyCoverage_anchor_exactVisibleCompressionTarget_iff_finitePredictorCover
    {Z : Type*} {k s : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s ↔
      G.FinitePredictorCover (2 ^ s) :=
  exactVisibleCompressionTarget_iff_finitePredictorCover

/-- Route-coverage anchor: a global product-bound-only bridge is exactly a
demand for finite predictor-image covers for every exact-visible family. -/
theorem kpolyCoverage_anchor_productBoundOnlyExactVisibleCompressionBridge_iff_forall_semanticFiniteImageBridge
    {Ω : Type u} {Z : Type v} [Fintype Ω] {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)} :
    ProductBoundOnlyExactVisibleCompressionBridge Ω Z k s hist items ↔
      ∀ {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index),
        ProductBoundSemanticFiniteImageBridge Ω Z k s hist items G :=
  productBoundOnlyExactVisibleCompressionBridge_iff_forall_semanticFiniteImageBridge

/-- Route-coverage anchor: a global fixed-field-switching-only bridge is
exactly a demand for finite predictor-image covers for every exact-visible
family. -/
theorem kpolyCoverage_anchor_fieldedSwitchingOnlyExactVisibleCompressionBridge_iff_forall_semanticFiniteImageBridge
    {Ω : Type u} {Z : Type v} [Fintype Ω] {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)} :
    FieldedSwitchingOnlyExactVisibleCompressionBridge Ω Z k s hist items ↔
      ∀ {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index),
        FieldedSwitchingSemanticFiniteImageBridge Ω Z k s hist items G :=
  fieldedSwitchingOnlyExactVisibleCompressionBridge_iff_forall_semanticFiniteImageBridge

/-- Route-coverage anchor: an empty product-bound-only bridge is refuted below
the exact-visible surface threshold by the full exact-visible Boolean family. -/
theorem kpolyCoverage_anchor_not_productBoundOnlyExactVisibleCompressionBridge_nil_of_lt_surfaceCard
    {Ω Z : Type*} [Fintype Ω] [Fintype Z] {k s : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ProductBoundOnlyExactVisibleCompressionBridge
        Ω Z k s ([] : List (FiniteEvent Ω)) ([] : List (V13FieldedStep Ω)) :=
  not_productBoundOnlyExactVisibleCompressionBridge_nil_of_lt_surfaceCard
    (Ω := Ω) (Z := Z) (k := k) (s := s) hs

/-- Route-coverage anchor: an empty fixed-field-switching-only bridge is
refuted below the exact-visible surface threshold by the full exact-visible
Boolean family. -/
theorem kpolyCoverage_anchor_not_fieldedSwitchingOnlyExactVisibleCompressionBridge_nil_of_lt_surfaceCard
    {Ω Z : Type*} [Fintype Ω] [Fintype Z] {k s : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ FieldedSwitchingOnlyExactVisibleCompressionBridge
        Ω Z k s ([] : List (FiniteEvent Ω)) ([] : List (V13FieldedStep Ω)) :=
  not_fieldedSwitchingOnlyExactVisibleCompressionBridge_nil_of_lt_surfaceCard
    (Ω := Ω) (Z := Z) (k := k) (s := s) hs

/-- Route-coverage anchor: a nonempty Boolean-square product-bound bridge is
also refuted below the exact-visible surface threshold. -/
theorem kpolyCoverage_anchor_not_productBoundOnlyExactVisibleCompressionBridge_boolPair_one_step_of_lt_surfaceCard
    {Z : Type*} [Fintype Z] {k s : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ProductBoundOnlyExactVisibleCompressionBridge
        (Bool × Bool) Z k s
        ([] : List (FiniteEvent (Bool × Bool)))
        [v13BoolPairUnitFieldedStep] :=
  not_productBoundOnlyExactVisibleCompressionBridge_boolPair_one_step_of_lt_surfaceCard
    (Z := Z) (k := k) (s := s) hs

/-- Route-coverage anchor: a nonempty Boolean-square fixed-field switching
bridge is also refuted below the exact-visible surface threshold. -/
theorem kpolyCoverage_anchor_not_fieldedSwitchingOnlyExactVisibleCompressionBridge_boolPair_one_step_of_lt_surfaceCard
    {Z : Type*} [Fintype Z] {k s : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ FieldedSwitchingOnlyExactVisibleCompressionBridge
        (Bool × Bool) Z k s
        ([] : List (FiniteEvent (Bool × Bool)))
        [v13BoolPairUnitFieldedStep] :=
  not_fieldedSwitchingOnlyExactVisibleCompressionBridge_boolPair_one_step_of_lt_surfaceCard
    (Z := Z) (k := k) (s := s) hs

/-- Route-coverage anchor: any true product-bound-only bridge is refuted by an
already-surjective exact-visible family below the surface threshold. -/
theorem kpolyCoverage_anchor_not_productBoundOnlyExactVisibleCompressionBridge_of_true_productBound_of_surjective_predict_of_lt_surfaceCard
    {Ω : Type u} {Z : Type v} [Fintype Ω] [Fintype Z] {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index)
    (hprod : V13FieldedProductBoundFrom Ω hist items)
    (hsurj : Function.Surjective G.predict)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ProductBoundOnlyExactVisibleCompressionBridge Ω Z k s hist items :=
  not_productBoundOnlyExactVisibleCompressionBridge_of_true_productBound_of_surjective_predict_of_lt_surfaceCard
    G hprod hsurj hs

/-- Route-coverage anchor: any true fixed-field-switching-only bridge is
refuted by an already-surjective exact-visible family below the surface
threshold. -/
theorem kpolyCoverage_anchor_not_fieldedSwitchingOnlyExactVisibleCompressionBridge_of_true_fieldedSwitching_of_surjective_predict_of_lt_surfaceCard
    {Ω : Type u} {Z : Type v} [Fintype Ω] [Fintype Z] {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index)
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hsurj : Function.Surjective G.predict)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ FieldedSwitchingOnlyExactVisibleCompressionBridge Ω Z k s hist items :=
  not_fieldedSwitchingOnlyExactVisibleCompressionBridge_of_true_fieldedSwitching_of_surjective_predict_of_lt_surfaceCard
    G hfield hsurj hs

/-- Route-coverage anchor: a global product-bound-only bridge to the full
clocked finite-learning payload is still exactly a demand for finite
predictor-image covers for every exact-visible family. -/
theorem kpolyCoverage_anchor_productBoundOnlyClockedKpolyFiniteLearningBridge_iff_forall_semanticFiniteImageBridge
    {Ω : Type u} {Z : Type v} [Fintype Ω] [Fintype Z] {k s clock : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)} :
    ProductBoundOnlyClockedKpolyFiniteLearningBridge Ω Z k s clock hist items ↔
      ∀ {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index),
        ProductBoundSemanticFiniteImageBridge Ω Z k s hist items G :=
  productBoundOnlyClockedKpolyFiniteLearningBridge_iff_forall_semanticFiniteImageBridge

/-- Route-coverage anchor: a global fixed-field-switching-only bridge to the
full clocked finite-learning payload is still exactly a demand for finite
predictor-image covers for every exact-visible family. -/
theorem kpolyCoverage_anchor_fieldedSwitchingOnlyClockedKpolyFiniteLearningBridge_iff_forall_semanticFiniteImageBridge
    {Ω : Type u} {Z : Type v} [Fintype Ω] [Fintype Z] {k s clock : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)} :
    FieldedSwitchingOnlyClockedKpolyFiniteLearningBridge Ω Z k s clock hist items ↔
      ∀ {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index),
        FieldedSwitchingSemanticFiniteImageBridge Ω Z k s hist items G :=
  fieldedSwitchingOnlyClockedKpolyFiniteLearningBridge_iff_forall_semanticFiniteImageBridge

/-- Route-coverage anchor: an empty product-bound-only bridge to the full
clocked payload is refuted below the exact-visible surface threshold. -/
theorem kpolyCoverage_anchor_not_productBoundOnlyClockedKpolyFiniteLearningBridge_nil_of_lt_surfaceCard
    {Ω Z : Type*} [Fintype Ω] [Fintype Z] {k s clock : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ProductBoundOnlyClockedKpolyFiniteLearningBridge
        Ω Z k s clock
        ([] : List (FiniteEvent Ω)) ([] : List (V13FieldedStep Ω)) :=
  not_productBoundOnlyClockedKpolyFiniteLearningBridge_nil_of_lt_surfaceCard
    (Ω := Ω) (Z := Z) (k := k) (s := s) (clock := clock) hs

/-- Route-coverage anchor: an empty fixed-field-switching-only bridge to the
full clocked payload is refuted below the exact-visible surface threshold. -/
theorem kpolyCoverage_anchor_not_fieldedSwitchingOnlyClockedKpolyFiniteLearningBridge_nil_of_lt_surfaceCard
    {Ω Z : Type*} [Fintype Ω] [Fintype Z] {k s clock : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ FieldedSwitchingOnlyClockedKpolyFiniteLearningBridge
        Ω Z k s clock
        ([] : List (FiniteEvent Ω)) ([] : List (V13FieldedStep Ω)) :=
  not_fieldedSwitchingOnlyClockedKpolyFiniteLearningBridge_nil_of_lt_surfaceCard
    (Ω := Ω) (Z := Z) (k := k) (s := s) (clock := clock) hs

/-- Route-coverage anchor: the nonempty Boolean-square product-bound bridge to
the full clocked payload is also refuted below the exact-visible surface
threshold. -/
theorem kpolyCoverage_anchor_not_productBoundOnlyClockedKpolyFiniteLearningBridge_boolPair_one_step_of_lt_surfaceCard
    {Z : Type*} [Fintype Z] {k s clock : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ProductBoundOnlyClockedKpolyFiniteLearningBridge
        (Bool × Bool) Z k s clock
        ([] : List (FiniteEvent (Bool × Bool)))
        [v13BoolPairUnitFieldedStep] :=
  not_productBoundOnlyClockedKpolyFiniteLearningBridge_boolPair_one_step_of_lt_surfaceCard
    (Z := Z) (k := k) (s := s) (clock := clock) hs

/-- Route-coverage anchor: the nonempty Boolean-square fixed-field switching
bridge to the full clocked payload is also refuted below the exact-visible
surface threshold. -/
theorem kpolyCoverage_anchor_not_fieldedSwitchingOnlyClockedKpolyFiniteLearningBridge_boolPair_one_step_of_lt_surfaceCard
    {Z : Type*} [Fintype Z] {k s clock : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ FieldedSwitchingOnlyClockedKpolyFiniteLearningBridge
        (Bool × Bool) Z k s clock
        ([] : List (FiniteEvent (Bool × Bool)))
        [v13BoolPairUnitFieldedStep] :=
  not_fieldedSwitchingOnlyClockedKpolyFiniteLearningBridge_boolPair_one_step_of_lt_surfaceCard
    (Z := Z) (k := k) (s := s) (clock := clock) hs

/-- Route-coverage anchor: any true product-bound-only bridge to the full
clocked payload is refuted by an already-surjective exact-visible family below
the Boolean predictor-space threshold. -/
theorem kpolyCoverage_anchor_not_productBoundOnlyClockedKpolyFiniteLearningBridge_of_true_productBound_of_surjective_predict_of_lt_predictorCard
    {Ω : Type u} {Z : Type v} [Fintype Ω] [Fintype Z] {k s clock : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index)
    (hprod : V13FieldedProductBoundFrom Ω hist items)
    (hsurj : Function.Surjective G.predict)
    (hs : 2 ^ s < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ProductBoundOnlyClockedKpolyFiniteLearningBridge
        Ω Z k s clock hist items :=
  not_productBoundOnlyClockedKpolyFiniteLearningBridge_of_true_productBound_of_surjective_predict_of_lt_predictorCard
    G hprod hsurj hs

/-- Route-coverage anchor: any true fixed-field-switching-only bridge to the
full clocked payload is refuted by an already-surjective exact-visible family
below the Boolean predictor-space threshold. -/
theorem kpolyCoverage_anchor_not_fieldedSwitchingOnlyClockedKpolyFiniteLearningBridge_of_true_fieldedSwitching_of_surjective_predict_of_lt_predictorCard
    {Ω : Type u} {Z : Type v} [Fintype Ω] [Fintype Z] {k s clock : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index)
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hsurj : Function.Surjective G.predict)
    (hs : 2 ^ s < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ FieldedSwitchingOnlyClockedKpolyFiniteLearningBridge
        Ω Z k s clock hist items :=
  not_fieldedSwitchingOnlyClockedKpolyFiniteLearningBridge_of_true_fieldedSwitching_of_surjective_predict_of_lt_predictorCard
    G hfield hsurj hs

/-- Route-coverage anchor: the clocked exact-visible realization interface has
the same finite predictor-image content. -/
theorem kpolyCoverage_anchor_clockedRealization_iff_finitePredictorCover
    {Z : Type*} {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} :
    (∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F) ↔
      G.FinitePredictorCover (2 ^ s) :=
  exists_clockedExactVisibleRealization_iff_finitePredictorCover

/-- Route-coverage anchor: adding the accumulated finite-learning consequences
to the clocked bridge still has exactly the same finite predictor-image
content. -/
theorem kpolyCoverage_anchor_clockedFiniteLearningPayload_iff_finitePredictorCover
    {Z : Type*} [Fintype Z] {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} :
    ClockedKpolyFiniteLearningPayload G s clock ↔
      G.FinitePredictorCover (2 ^ s) :=
  clockedKpolyFiniteLearningPayload_iff_finitePredictorCover

/-- Route-coverage anchor: the accumulated finite-learning payload is exactly
the existing exact visible compression target. -/
theorem kpolyCoverage_anchor_clockedFiniteLearningPayload_iff_exactVisibleCompressionTarget
    {Z : Type*} [Fintype Z] {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} :
    ClockedKpolyFiniteLearningPayload G s clock ↔
      ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s :=
  clockedKpolyFiniteLearningPayload_iff_exactVisibleCompressionTarget

/-- Route-coverage anchor: the final manuscript-facing canonical exact
`(zfeat(z), a, b)` ERM recovery interface already lands on the exact-visible /
finite-image surface tracked by the stop-grade `Kpoly` packet.  Any such route
supplies the concrete visible-budget compression target, all three equivalent
finite-image presentations, the bundled clocked finite-learning payload at the
same budget, and the usual strict-budget non-surjectivity consequence. -/
def CanonicalZABERMRouteCoverage : Prop :=
  ∀ {Z : Type*} [Fintype Z] {r k clock : ℕ} {Index : Type*}
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index} {q : ℝ≥0∞},
      CanonicalZABERMRecoveryData
          (Z := Z) (r := r) (k := k) (Index := Index) μ zfeat G q →
        ExactVisibleCompressionTarget
          (Z := Z) (k := k) (Index := Index) G (r + 2 * k + 1) ∧
        G.FinitePredictorCover (2 ^ (r + 2 * k + 1)) ∧
        G.FiniteIndexRepresentativeCover (2 ^ (r + 2 * k + 1)) ∧
        G.FinitePredictorQuotient (2 ^ (r + 2 * k + 1)) ∧
        ClockedKpolyFiniteLearningPayload G (r + 2 * k + 1) clock ∧
        (r + 2 * k + 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k) →
          ¬ Function.Surjective G.predict)

@[simp] theorem canonicalZABERMRouteCoverage :
    CanonicalZABERMRouteCoverage := by
  intro Z _ r k clock Index μ zfeat G q h
  refine ⟨h.compressionTarget, h.finitePredictorCover, h.finiteIndexRepresentativeCover,
    h.finitePredictorQuotient, ?_, ?_⟩
  · exact
      clockedKpolyFiniteLearningPayload_of_exactVisibleCompressionTarget
        (Z := Z) (k := k) (s := r + 2 * k + 1) (clock := clock) (Index := Index)
        h.compressionTarget
  · intro hs
    exact h.not_surjective_predict_of_lt_surfaceCard hs

/-- Route-coverage anchor: the concrete exact `(zfeat(z), a, b)`
decision-list ERM family closes the bundled clocked finite-learning payload at
the explicit decision-list budget. -/
theorem kpolyCoverage_anchor_exactZABDecisionListERMClockedKpolyFiniteLearningPayload
    {Z : Type*} [Fintype Z] {r k clock : ℕ} {Index : Type*}
    (zfeat : Z → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    ClockedKpolyFiniteLearningPayload
      (exactZABDecisionListERMFamily
        (Z := Z) (r := r) (k := k) (Index := Index) zfeat samples)
      (r + 2 * k + 1) clock :=
  exactZABDecisionListERMClockedKpolyFiniteLearningPayload zfeat samples

/-- Route-coverage anchor: the bit-vector exact ZAB ERM specialization closes
the bundled clocked finite-learning payload at the explicit decision-list
budget. -/
theorem kpolyCoverage_anchor_bitVecZABDecisionListERMClockedKpolyFiniteLearningPayload
    {r k clock : ℕ} {Index : Type*} [Fintype (BitVec r)]
    (samples :
      Index → Sample (ExactVisiblePostSwitchSurface (BitVec r) k) Bool) :
    ClockedKpolyFiniteLearningPayload
      (bitVecZABDecisionListERMFamily
        (r := r) (k := k) (Index := Index) samples)
      (r + 2 * k + 1) clock :=
  bitVecZABDecisionListERMClockedKpolyFiniteLearningPayload samples

/-- Route-coverage anchor: equality with the concrete bit-vector exact ZAB ERM
family is a sufficient missing assumption for transferring the payload to a
manuscript-facing family variable. -/
theorem kpolyCoverage_anchor_clockedPayload_of_eq_bitVecZABDecisionListERMFamily
    {r k clock : ℕ} {Index : Type*} [Fintype (BitVec r)]
    (samples :
      Index → Sample (ExactVisiblePostSwitchSurface (BitVec r) k) Bool)
    {G : ExactVisibleSwitchedFamily (BitVec r) k Index}
    (hG :
      G =
        bitVecZABDecisionListERMFamily
          (r := r) (k := k) (Index := Index) samples) :
    ClockedKpolyFiniteLearningPayload G (r + 2 * k + 1) clock :=
  clockedKpolyFiniteLearningPayload_of_eq_bitVecZABDecisionListERMFamily samples hG

/-- Route-coverage anchor: exact-ZAB recovery with a bad-code agreement bound
localizes the obligation to every finite region whose sampling mass exceeds the
advertised threshold. -/
theorem kpolyCoverage_anchor_exactZABERMRecoveryData_exists_pos_mass_disagreement_in_region_of_badCode
    {Z : Type*} [Fintype Z] {r k : ℕ} {Index : Type*}
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (i : Index)
    (c :
      (rawExactZABDecisionListBitFamily Z r k zfeat).toEncodedFamily.BadCodes
        (G.predict i))
    (region : Finset (ExactVisiblePostSwitchSurface Z k))
    (hmass : q < region.sum (fun x => μ x)) :
    ∃ x, x ∈ region ∧ μ x ≠ 0 ∧
      (rawExactZABDecisionListBitFamily Z r k zfeat).decode c.1 x ≠
        G.predict i x :=
  h.exists_pos_mass_disagreement_in_region_of_badCode i c region hmass

/-- Route-coverage anchor: the bare exact-visible interface is insufficient for
the clocked payload below the full exact-visible surface threshold. -/
theorem kpolyCoverage_anchor_currentExactVisibleInterface_not_forall_clockedPayload_of_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k s clock : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (∀ {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index),
        ClockedKpolyFiniteLearningPayload G s clock) :=
  currentExactVisibleInterface_not_forall_clockedKpolyFiniteLearningPayload_of_lt_surfaceCard
    (Z := Z) (k := k) (s := s) (clock := clock) hs

/-- Route-coverage anchor: a bare plug-in lookup table over the exact visible
alphabet is already surjective onto all exact-visible Boolean rules. -/
theorem kpolyCoverage_anchor_pluginLookup_surjective
    (Z : Type v) (k : ℕ) :
    Function.Surjective
      (pluginLookupActualSwitchedLocalInterface Z k).predictorFamily.predict :=
  pluginLookupActualSwitchedLocalInterface_surjective Z k

/-- Route-coverage anchor: the bare plug-in lookup endpoint has no clocked
finite-learning payload below the full exact-visible truth-table budget. -/
theorem kpolyCoverage_anchor_pluginLookup_not_clockedPayload_of_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k s clock : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ClockedKpolyFiniteLearningPayload
        (pluginLookupActualSwitchedLocalInterface Z k).predictorFamily s clock :=
  pluginLookupActualSwitchedLocalInterface_not_clockedKpolyFiniteLearningPayload_of_lt_surfaceCard
    hs

/-- Route-coverage anchor: a bare plug-in lookup endpoint cannot be identified
with bounded ZAB decision-list constructor data below the exact-visible
truth-table budget. -/
theorem kpolyCoverage_anchor_pluginLookup_not_zabDecisionListData_of_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k r : ℕ}
    (zfeat : Z → BitVec r)
    (hs : r + 2 * k + 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.ZABDecisionListData
          (pluginLookupActualSwitchedLocalInterface Z k) zfeat) :=
  pluginLookupActualSwitchedLocalInterface_not_zabDecisionListData_of_lt_surfaceCard
    zfeat hs

/-- Route-coverage anchor: unrestricted plug-in majority counts are already
surjective onto all exact-visible Boolean rules. -/
theorem kpolyCoverage_anchor_pluginMajority_surjective
    (Z : Type v) (k : ℕ) :
    Function.Surjective
      (pluginMajorityActualSwitchedLocalInterface Z k).predictorFamily.predict :=
  pluginMajorityActualSwitchedLocalInterface_surjective Z k

/-- Route-coverage anchor: unrestricted plug-in majority counts have no clocked
finite-learning payload below the exact-visible truth-table budget. -/
theorem kpolyCoverage_anchor_pluginMajority_not_clockedPayload_of_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k s clock : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ClockedKpolyFiniteLearningPayload
        (pluginMajorityActualSwitchedLocalInterface Z k).predictorFamily s clock :=
  pluginMajorityActualSwitchedLocalInterface_not_clockedKpolyFiniteLearningPayload_of_lt_surfaceCard
    hs

/-- Route-coverage anchor: unrestricted plug-in majority cannot be treated as
bounded ZAB decision-list constructor data below the exact-visible truth-table
budget. -/
theorem kpolyCoverage_anchor_pluginMajority_not_zabDecisionListData_of_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k r : ℕ}
    (zfeat : Z → BitVec r)
    (hs : r + 2 * k + 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.ZABDecisionListData
          (pluginMajorityActualSwitchedLocalInterface Z k) zfeat) :=
  pluginMajorityActualSwitchedLocalInterface_not_zabDecisionListData_of_lt_surfaceCard
    zfeat hs

/-- Route-coverage anchor: sample-level plug-in majority is still surjective
onto all exact-visible Boolean rules via graph samples. -/
theorem kpolyCoverage_anchor_pluginSampleMajority_surjective
    (Z : Type v) (k : ℕ) [Fintype Z] :
    Function.Surjective
      (pluginSampleMajorityActualSwitchedLocalInterface Z k).predictorFamily.predict :=
  pluginSampleMajorityActualSwitchedLocalInterface_surjective Z k

/-- Route-coverage anchor: sample-level plug-in majority has no clocked
finite-learning payload below the exact-visible truth-table budget. -/
theorem kpolyCoverage_anchor_pluginSampleMajority_not_clockedPayload_of_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k s clock : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ClockedKpolyFiniteLearningPayload
        (pluginSampleMajorityActualSwitchedLocalInterface Z k).predictorFamily s clock :=
  pluginSampleMajorityActualSwitchedLocalInterface_not_clockedKpolyFiniteLearningPayload_of_lt_surfaceCard
    hs

/-- Route-coverage anchor: sample-level plug-in majority cannot be treated as
bounded ZAB decision-list constructor data below the exact-visible truth-table
budget. -/
theorem kpolyCoverage_anchor_pluginSampleMajority_not_zabDecisionListData_of_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k r : ℕ}
    (zfeat : Z → BitVec r)
    (hs : r + 2 * k + 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.ZABDecisionListData
          (pluginSampleMajorityActualSwitchedLocalInterface Z k) zfeat) :=
  pluginSampleMajorityActualSwitchedLocalInterface_not_zabDecisionListData_of_lt_surfaceCard
    zfeat hs

/-- Route-coverage anchor: unrestricted sample-level plug-in majority cannot
be identified with one shared exact sparse-threshold ERM family below the
point-block visible-budget threshold. -/
theorem kpolyCoverage_anchor_pluginSampleMajority_not_nonempty_sharedExactZABSparseThresholdERMData_of_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k r : ℕ}
    (zfeat : Z → BitVec r)
    (hs :
      2 * allAffinePointBlockFeatureCount (r + (k + k)) <
        Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMData
          (pluginSampleMajorityActualSwitchedLocalInterface Z k)
          zfeat) :=
  pluginSampleMajorityActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMData_of_lt_surfaceCard
    (Z := Z) (k := k) zfeat hs

/-- Route-coverage anchor: any surjective actual-local endpoint on
`BitVec n` already loses the manuscript-facing sparse-threshold recovery packet
below the unconditional half-width ceiling, regardless of extractor choice.
The concrete plug-in-majority and fallback repairs are only instances of this
surjective actual-local boundary. -/
theorem kpolyCoverage_anchor_surjectiveActualLocal_not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
    {n k r : ℕ} {Index : Type u} {Block : Type w}
    (μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k))
    (T : ActualSwitchedLocalInterface (BitVec n) k Index Block)
    (q : ℝ≥0∞)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    (hgap : 2 * r + 2 * k + 1 < n) :
    ¬ ∃ zfeat : BitVec n → BitVec r,
        Nonempty
          (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
            μ T zfeat q) :=
  ActualSwitchedLocalInterface.not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_surjective_predict_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
    (T := T) (μ := μ) (q := q) hsurj hgap

/-- Route-coverage anchor: on `BitVec n`, the same sample-level majority
endpoint cannot carry the stronger sparse-threshold recovery packet once the
visible width exceeds the unconditional half-width ceiling. -/
theorem kpolyCoverage_anchor_pluginSampleMajority_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
    {n k r : ℕ}
    (μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k))
    (zfeat : BitVec n → BitVec r)
    (q : ℝ≥0∞)
    (hgap : 2 * r + 2 * k + 1 < n) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          μ
          (pluginSampleMajorityActualSwitchedLocalInterface (BitVec n) k)
          zfeat
          q) :=
  pluginSampleMajorityActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
    (n := n) (k := k) (r := r) μ zfeat q hgap

/-- Route-coverage anchor: bounded sample-level plug-in majority is full-rule
expressive exactly when the sample bound reaches the exact-visible alphabet
size. -/
theorem kpolyCoverage_anchor_boundedSampleMajority_surjective_iff
    (Z : Type v) (k sampleBound : ℕ) [Fintype Z] :
    Function.Surjective
        (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).predictorFamily.predict ↔
      Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound :=
  boundedSamplePluginMajorityActualSwitchedLocalInterface_surjective_iff
    Z k sampleBound

/-- Route-coverage anchor: every predictor selected by bounded sample-level
plug-in majority is false on at most `sampleBound` exact-visible inputs. -/
theorem kpolyCoverage_anchor_boundedSampleMajority_falseSupport_card_le_sampleBound
    {Z : Type v} [Fintype Z] {k sampleBound : ℕ}
    (sample :
      BoundedSampleIndex (ExactVisiblePostSwitchSurface Z k) sampleBound) :
    (PluginSampleMajority.falseSupport
      (fun u : ExactVisiblePostSwitchSurface Z k =>
        (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).predictorFamily.predict
          sample u)).card ≤ sampleBound :=
  boundedSamplePluginMajorityActualSwitchedLocalInterface_falseSupport_card_le_sampleBound
    (Z := Z) (k := k) (sampleBound := sampleBound) sample

/-- Route-coverage anchor: a target rule whose false-support exceeds the
sample bound is not realized by bounded sample-level plug-in majority. -/
theorem kpolyCoverage_anchor_boundedSampleMajority_not_realizes_rule_of_sampleBound_lt_falseSupport_card
    {Z : Type v} [Fintype Z] {k sampleBound : ℕ}
    (rule : ExactVisibleRule Z k)
    (hcard : sampleBound < (PluginSampleMajority.falseSupport rule).card) :
    ¬ ∃ sample,
      (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).predictorFamily.predict
          sample =
        rule :=
  boundedSamplePluginMajorityActualSwitchedLocalInterface_not_realizes_rule_of_sampleBound_lt_falseSupport_card
    (Z := Z) (k := k) (sampleBound := sampleBound) rule hcard

/-- Route-coverage anchor: with any explicit tie-breaking default, every
bounded sample-level plug-in majority predictor differs from that default on at
most `sampleBound` exact-visible inputs. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithDefault_nondefaultSupport_card_le_sampleBound
    {Z : Type v} [Fintype Z] {k sampleBound : ℕ}
    (default : Bool)
    (sample :
      BoundedSampleIndex (ExactVisiblePostSwitchSurface Z k) sampleBound) :
    (PluginSampleMajority.nondefaultSupport default
      (fun u : ExactVisiblePostSwitchSurface Z k =>
        (boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface
          default Z k sampleBound).predictorFamily.predict sample u)).card ≤ sampleBound :=
  boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface_nondefaultSupport_card_le_sampleBound
    (Z := Z) (k := k) (sampleBound := sampleBound) default sample

/-- Route-coverage anchor: for any tie-breaking default, a target rule whose
nondefault support exceeds the sample bound is not realized by bounded
sample-level plug-in majority. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithDefault_not_realizes_rule_of_sampleBound_lt_nondefaultSupport_card
    {Z : Type v} [Fintype Z] {k sampleBound : ℕ}
    (default : Bool) (rule : ExactVisibleRule Z k)
    (hcard : sampleBound < (PluginSampleMajority.nondefaultSupport default rule).card) :
    ¬ ∃ sample,
      (boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface
          default Z k sampleBound).predictorFamily.predict sample =
        rule :=
  boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface_not_realizes_rule_of_sampleBound_lt_nondefaultSupport_card
    (Z := Z) (k := k) (sampleBound := sampleBound) default rule hcard

/-- Route-coverage anchor: changing the bounded plug-in majority tie-break does
not change the exact surjectivity threshold. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithDefault_surjective_iff
    (default : Bool) (Z : Type v) (k sampleBound : ℕ) [Fintype Z] :
    Function.Surjective
        (boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface
          default Z k sampleBound).predictorFamily.predict ↔
      Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound :=
  boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface_surjective_iff
    default Z k sampleBound

/-- Route-coverage anchor: if the tie fallback is allowed to depend on the
exact-visible input, the empty sample already realizes any fallback rule. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithFallback_emptySample_predict
    {Z : Type v} {k sampleBound : ℕ}
    (fallback : ExactVisibleRule Z k) :
    (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
        Z k sampleBound).predictorFamily.predict
        (fallback, ⟨[], by simp⟩) =
      fallback :=
  boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface_emptySample_predict
    (Z := Z) (k := k) (sampleBound := sampleBound) fallback

/-- Route-coverage anchor: the input-dependent fallback endpoint is
full-rule expressive for every sample bound, including zero. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithFallback_surjective
    (Z : Type v) (k sampleBound : ℕ) :
    Function.Surjective
      (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
        Z k sampleBound).predictorFamily.predict :=
  boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface_surjective
    Z k sampleBound

/-- Route-coverage anchor: since the fallback component is already a full rule,
the endpoint has no small finite predictor cover below the exact-visible
truth-table budget. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithFallback_not_finitePredictorCover_of_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k s sampleBound : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
        Z k sampleBound).predictorFamily.FinitePredictorCover (2 ^ s) :=
  boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface_not_finitePredictorCover_of_lt_surfaceCard
    (Z := Z) (k := k) (s := s) (sampleBound := sampleBound) hs

/-- Route-coverage anchor: the same fallback side channel cannot provide the
clocked finite-learning payload below the exact-visible truth-table budget. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithFallback_not_clockedPayload_of_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k s sampleBound clock : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ClockedKpolyFiniteLearningPayload
        (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
          Z k sampleBound).predictorFamily s clock :=
  boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface_not_clockedKpolyFiniteLearningPayload_of_lt_surfaceCard
    (Z := Z) (k := k) (s := s) (sampleBound := sampleBound) (clock := clock) hs

/-- Route-coverage anchor: if the fallback is chosen from a structured
fallback family, bounded samples can only make `sampleBound` point changes
relative to the selected fallback rule. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_disagreementSupport_card_le_sampleBound
    {FallbackIndex : Type v} {Z : Type v} [Fintype Z] {k sampleBound : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k)
    (index :
      BoundedSampleFallbackFamilyIndex
        FallbackIndex (ExactVisiblePostSwitchSurface Z k) sampleBound) :
    (PluginSampleMajority.disagreementSupport (fallback index.1)
      (fun u : ExactVisiblePostSwitchSurface Z k =>
        (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k sampleBound fallback).predictorFamily.predict index u)).card ≤
        sampleBound :=
  boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_disagreementSupport_card_le_sampleBound
    (Z := Z) (k := k) (sampleBound := sampleBound) fallback index

/-- Route-coverage anchor: selecting a structured fallback code and using the
empty sample realizes that fallback rule exactly. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_emptySample_predict
    {FallbackIndex : Type v} {Z : Type v} {k sampleBound : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k) (code : FallbackIndex) :
    (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
        FallbackIndex Z k sampleBound fallback).predictorFamily.predict
        (code, ⟨[], by simp⟩) =
      fallback code :=
  boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_emptySample_predict
    (Z := Z) (k := k) (sampleBound := sampleBound) fallback code

/-- Route-coverage anchor: bounded samples do not reduce a structured fallback
family that is already full-rule expressive.  A proposed repair must therefore
prove smallness of the fallback family itself, not merely boundedness of the
sampled overrides. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_surjective_of_fallback_surjective
    {FallbackIndex : Type v} {Z : Type v} {k sampleBound : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k)
    (hsurj : Function.Surjective fallback) :
    Function.Surjective
      (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
        FallbackIndex Z k sampleBound fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_surjective_of_fallback_surjective
    (Z := Z) (k := k) (sampleBound := sampleBound) fallback hsurj

/-- Route-coverage anchor: with no sampled overrides, a structured fallback
endpoint is full-rule expressive exactly when the fallback family itself is
full-rule expressive.  Thus the zero-sample boundary leaves no hidden
expressivity in the bounded-sample wrapper. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_zeroSample_surjective_iff_fallback_surjective
    {FallbackIndex : Type v} {Z : Type v} {k : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k) :
    Function.Surjective
        (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k 0 fallback).predictorFamily.predict ↔
      Function.Surjective fallback :=
  boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_zeroSample_surjective_iff_fallback_surjective
    (Z := Z) (k := k) fallback

/-- Route-coverage anchor: a structured fallback family plus bounded samples
cannot realize a rule that is farther than `sampleBound` from every fallback
code. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_not_realizes_rule_of_forall_sampleBound_lt_disagreementSupport_card
    {FallbackIndex : Type v} {Z : Type v} [Fintype Z] {k sampleBound : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k)
    (rule : ExactVisibleRule Z k)
    (hcard :
      ∀ code : FallbackIndex,
        sampleBound <
          (PluginSampleMajority.disagreementSupport (fallback code) rule).card) :
    ¬ ∃ index,
      (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k sampleBound fallback).predictorFamily.predict index =
        rule :=
  boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_not_realizes_rule_of_forall_sampleBound_lt_disagreementSupport_card
    (Z := Z) (k := k) (sampleBound := sampleBound) fallback rule hcard

/-- Route-coverage anchor: structured fallback plus bounded samples realizes
exactly the finite Hamming-radius cover around the fallback codes. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_realizes_rule_iff_mem_fallbackFamilyRadiusCover
    {FallbackIndex : Type v} {Z : Type v} [Fintype FallbackIndex] [Fintype Z]
    {k sampleBound : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k)
    (rule : ExactVisibleRule Z k) :
    (∃ index,
      (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k sampleBound fallback).predictorFamily.predict index =
        rule) ↔
      rule ∈ PluginSampleMajority.fallbackFamilyRadiusCover fallback sampleBound :=
  boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_realizes_rule_iff_mem_fallbackFamilyRadiusCover
    (Z := Z) (k := k) (sampleBound := sampleBound) fallback rule

/-- Route-coverage anchor: structured fallback plus bounded samples is
surjective exactly when the fallback-code Hamming cover is the full rule cube. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_surjective_iff_fallbackFamilyRadiusCover_eq_univ
    {FallbackIndex : Type v} {Z : Type v} [Fintype FallbackIndex] [Fintype Z]
    {k sampleBound : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k) :
    Function.Surjective
        (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k sampleBound fallback).predictorFamily.predict ↔
      PluginSampleMajority.fallbackFamilyRadiusCover fallback sampleBound =
        (Finset.univ : Finset (ExactVisibleRule Z k)) :=
  boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_surjective_iff_fallbackFamilyRadiusCover_eq_univ
    (Z := Z) (k := k) (sampleBound := sampleBound) fallback

/-- Route-coverage anchor: the exact pointwise repair condition for structured
fallback plus bounded samples is radius-`sampleBound` coverage of every
exact-visible rule by some fallback code. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_surjective_iff_forall_exists_disagreementSupport_card_le_sampleBound
    {FallbackIndex : Type v} {Z : Type v} [Fintype FallbackIndex] [Fintype Z]
    {k sampleBound : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k) :
    Function.Surjective
        (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k sampleBound fallback).predictorFamily.predict ↔
      ∀ rule : ExactVisibleRule Z k,
        ∃ code : FallbackIndex,
          (PluginSampleMajority.disagreementSupport (fallback code) rule).card ≤
            sampleBound :=
  boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_surjective_iff_forall_exists_disagreementSupport_card_le_sampleBound
    (Z := Z) (k := k) (sampleBound := sampleBound) fallback

/-- Route-coverage anchor: once the sample bound reaches the exact-visible
alphabet size, any nonempty structured fallback family is full-rule expressive.
Thus the bounded-sample obstruction is sharp at full radius. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_surjective_of_nonempty_of_surfaceCard_le_sampleBound
    {FallbackIndex : Type v} {Z : Type v}
    [Fintype FallbackIndex] [Nonempty FallbackIndex] [Fintype Z]
    {k sampleBound : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k)
    (hbound : Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound) :
    Function.Surjective
      (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
        FallbackIndex Z k sampleBound fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_surjective_of_nonempty_of_surfaceCard_le_sampleBound
    (FallbackIndex := FallbackIndex) (Z := Z) (k := k)
    (sampleBound := sampleBound) fallback hbound

/-- Route-coverage anchor: a structured fallback family plus bounded samples
has a predictor-image cover bounded by fallback-code count times the number of
small sparse override supports. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_finitePredictorCover
    {FallbackIndex : Type v} {Z : Type v} [Fintype FallbackIndex] [Fintype Z]
    {k sampleBound : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k) :
    (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
        FallbackIndex Z k sampleBound fallback).predictorFamily.FinitePredictorCover
      (Fintype.card FallbackIndex *
        (PluginSampleMajority.smallSubsets
          (ExactVisiblePostSwitchSurface Z k) sampleBound).card) :=
  boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_finitePredictorCover
    (Z := Z) (k := k) (sampleBound := sampleBound) fallback

/-- Route-coverage anchor: if that Hamming-cover product is below the full
truth-table space, the structured fallback-family endpoint is not full-rule
expressive. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_not_surjective_of_code_mul_smallSubsets_card_lt_boolClassifierSpace
    {FallbackIndex : Type v} {Z : Type v} [Fintype FallbackIndex] [Fintype Z]
    {k sampleBound : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k)
    (hcard :
      Fintype.card FallbackIndex *
          (PluginSampleMajority.smallSubsets
            (ExactVisiblePostSwitchSurface Z k) sampleBound).card <
        2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
        FallbackIndex Z k sampleBound fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_code_mul_smallSubsets_card_lt_boolClassifierSpace
    (Z := Z) (k := k) (sampleBound := sampleBound) fallback hcard

/-- Route-coverage anchor: full-rule expressivity of a structured fallback
family plus bounded samples forces the Hamming-cover product to reach the full
exact-visible Boolean truth-table count. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_boolClassifierSpace_card_le_code_mul_smallSubsets_card_of_surjective
    {FallbackIndex : Type v} {Z : Type v} [Fintype FallbackIndex] [Fintype Z]
    {k sampleBound : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k sampleBound fallback).predictorFamily.predict) :
    2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      Fintype.card FallbackIndex *
        (PluginSampleMajority.smallSubsets
          (ExactVisiblePostSwitchSurface Z k) sampleBound).card :=
  boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_boolClassifierSpace_card_le_code_mul_smallSubsets_card_of_surjective
    (Z := Z) (k := k) (sampleBound := sampleBound) fallback hsurj

/-- Route-coverage anchor: full-rule expressivity of a `fallbackBits`-bit
structured fallback family plus bounded samples forces the explicit bit-code
budget times sparse override supports to reach the full exact-visible Boolean
truth-table count. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_boolClassifierSpace_card_le_bitCode_mul_smallSubsets_card_of_surjective
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k sampleBound fallbackBits fallback).predictorFamily.predict) :
    2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      2 ^ fallbackBits *
        (PluginSampleMajority.smallSubsets
          (ExactVisiblePostSwitchSurface Z k) sampleBound).card :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_boolClassifierSpace_card_le_bitCode_mul_smallSubsets_card_of_surjective
    (Z := Z) (k := k) (sampleBound := sampleBound)
    (fallbackBits := fallbackBits) fallback hsurj

/-- Route-coverage anchor: bit-coded fallback families are full-rule
expressive at full sample radius, independently of the fallback-bit budget. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_surjective_of_surfaceCard_le_sampleBound
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hbound : Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound) :
    Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound fallbackBits fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_surjective_of_surfaceCard_le_sampleBound
    (Z := Z) (k := k) (sampleBound := sampleBound)
    (fallbackBits := fallbackBits) fallback hbound

/-- Route-coverage anchor: if the explicit bit-code budget times sparse
override supports is below the full truth-table space, then a `fallbackBits`-bit
structured fallback-family endpoint is not full-rule expressive. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_surjective_of_bitCode_mul_smallSubsets_card_lt_boolClassifierSpace
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hcard :
      2 ^ fallbackBits *
          (PluginSampleMajority.smallSubsets
            (ExactVisiblePostSwitchSurface Z k) sampleBound).card <
        2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound fallbackBits fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_bitCode_mul_smallSubsets_card_lt_boolClassifierSpace
    (Z := Z) (k := k) (sampleBound := sampleBound)
    (fallbackBits := fallbackBits) fallback hcard

/-- Route-coverage anchor: the same bit-code obstruction with the sparse
override count expanded as the exact binomial-prefix Hamming-ball support
count. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_boolClassifierSpace_card_le_bitCode_mul_sum_choose_of_surjective
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k sampleBound fallbackBits fallback).predictorFamily.predict) :
    2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      2 ^ fallbackBits *
        ∑ i ∈ Finset.range (sampleBound + 1),
          (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose i :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_boolClassifierSpace_card_le_bitCode_mul_sum_choose_of_surjective
    (Z := Z) (k := k) (sampleBound := sampleBound)
    (fallbackBits := fallbackBits) fallback hsurj

/-- Route-coverage anchor: if the bit-code budget times the exact
binomial-prefix Hamming-ball support count is still below the full
exact-visible Boolean rule cube, the endpoint is not full-rule expressive. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_surjective_of_bitCode_mul_sum_choose_lt_boolClassifierSpace
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hcard :
      2 ^ fallbackBits *
          (∑ i ∈ Finset.range (sampleBound + 1),
            (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose i) <
        2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound fallbackBits fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_bitCode_mul_sum_choose_lt_boolClassifierSpace
    (Z := Z) (k := k) (sampleBound := sampleBound)
    (fallbackBits := fallbackBits) fallback hcard

/-- Route-coverage anchor: if the exact binomial-prefix Hamming-ball support
count fits into `overheadBits` bits, full expressivity forces the total
fallback-plus-overhead bit budget to reach the exact-visible alphabet size. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_fallbackBits_add_overheadBits_ge_surfaceCard_of_sumChooseEnvelope_le_twoPow_surjective
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits overheadBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (henvelope :
      (∑ i ∈ Finset.range (sampleBound + 1),
        (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose i) ≤
        2 ^ overheadBits)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k sampleBound fallbackBits fallback).predictorFamily.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      fallbackBits + overheadBits :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_fallbackBits_add_overheadBits_ge_surfaceCard_of_sumChooseEnvelope_le_twoPow_surjective
    (Z := Z) (k := k) (sampleBound := sampleBound)
    (fallbackBits := fallbackBits) (overheadBits := overheadBits)
    fallback henvelope hsurj

/-- Route-coverage anchor: if the exact binomial-prefix support envelope fits
into `overheadBits` bits but the total bit budget is still below the
exact-visible alphabet size, then the endpoint is not full-rule expressive. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_surjective_of_sumChooseEnvelope_le_twoPow_and_fallbackBits_add_overheadBits_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits overheadBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (henvelope :
      (∑ i ∈ Finset.range (sampleBound + 1),
        (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose i) ≤
        2 ^ overheadBits)
    (hbits :
      fallbackBits + overheadBits <
        Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound fallbackBits fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_sumChooseEnvelope_le_twoPow_and_fallbackBits_add_overheadBits_lt_surfaceCard
    (Z := Z) (k := k) (sampleBound := sampleBound)
    (fallbackBits := fallbackBits) (overheadBits := overheadBits)
    fallback henvelope hbits

/-- Route-coverage anchor: with no fallback bits, a bounded-sample sparse
override endpoint is not full-rule expressive below the exact-visible alphabet
size. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_surjective_zeroFallbackBits_of_sampleBound_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k sampleBound : ℕ}
    (fallback : BitCode 0 → ExactVisibleRule Z k)
    (hbound :
      sampleBound < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound 0 fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_zeroFallbackBits_of_sampleBound_lt_surfaceCard
    (Z := Z) (k := k) (sampleBound := sampleBound) fallback hbound

/-- Route-coverage anchor: with no fallback bits, full-rule expressivity is
equivalent to the sample bound reaching the exact-visible alphabet size. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_zeroFallbackBits_surjective_iff_surfaceCard_le_sampleBound
    {Z : Type v} [Fintype Z] {k sampleBound : ℕ}
    (fallback : BitCode 0 → ExactVisibleRule Z k) :
    Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k sampleBound 0 fallback).predictorFamily.predict ↔
      Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_zeroFallbackBits_surjective_iff_surfaceCard_le_sampleBound
    (Z := Z) (k := k) (sampleBound := sampleBound) fallback

/-- Route-coverage anchor: a coarse polynomial envelope of the exact
binomial-prefix sparse override count is already enough to state the fallback
bit-budget burden in a directly asymptotic-looking form. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_boolClassifierSpace_card_le_bitCode_mul_sampleBound_succ_mul_surfaceCard_succ_pow_of_surjective
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k sampleBound fallbackBits fallback).predictorFamily.predict) :
    2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      2 ^ fallbackBits *
        ((sampleBound + 1) *
          (Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1) ^ sampleBound) :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_boolClassifierSpace_card_le_bitCode_mul_sampleBound_succ_mul_surfaceCard_succ_pow_of_surjective
    (Z := Z) (k := k) (sampleBound := sampleBound)
    (fallbackBits := fallbackBits) fallback hsurj

/-- Route-coverage anchor: if the bit-code budget times the coarse polynomial
Hamming-ball envelope is below the full exact-visible Boolean rule cube, then
the bit-coded structured fallback endpoint is not full-rule expressive. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_surjective_of_bitCode_mul_sampleBound_succ_mul_surfaceCard_succ_pow_lt_boolClassifierSpace
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hcard :
      2 ^ fallbackBits *
          ((sampleBound + 1) *
            (Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1) ^ sampleBound) <
        2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound fallbackBits fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_bitCode_mul_sampleBound_succ_mul_surfaceCard_succ_pow_lt_boolClassifierSpace
    (Z := Z) (k := k) (sampleBound := sampleBound)
    (fallbackBits := fallbackBits) fallback hcard

/-- Route-coverage anchor: if the sampled sparse-override polynomial envelope
fits into `overheadBits` bits, then full expressivity forces the total
fallback-plus-overhead bit budget to reach the exact-visible alphabet size. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_fallbackBits_add_overheadBits_ge_surfaceCard_of_polynomialEnvelope_le_twoPow_surjective
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits overheadBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (henvelope :
      (sampleBound + 1) *
          (Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1) ^ sampleBound ≤
        2 ^ overheadBits)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k sampleBound fallbackBits fallback).predictorFamily.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      fallbackBits + overheadBits :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_fallbackBits_add_overheadBits_ge_surfaceCard_of_polynomialEnvelope_le_twoPow_surjective
    (Z := Z) (k := k) (sampleBound := sampleBound)
    (fallbackBits := fallbackBits) (overheadBits := overheadBits)
    fallback henvelope hsurj

/-- Route-coverage anchor: if the sparse-override polynomial envelope fits into
`overheadBits` bits but `fallbackBits + overheadBits` is still below the
exact-visible alphabet size, then the bit-coded structured fallback endpoint is
not full-rule expressive. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_surjective_of_polynomialEnvelope_le_twoPow_and_fallbackBits_add_overheadBits_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits overheadBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (henvelope :
      (sampleBound + 1) *
          (Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1) ^ sampleBound ≤
        2 ^ overheadBits)
    (hbits :
      fallbackBits + overheadBits <
        Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound fallbackBits fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_polynomialEnvelope_le_twoPow_and_fallbackBits_add_overheadBits_lt_surfaceCard
    (Z := Z) (k := k) (sampleBound := sampleBound)
    (fallbackBits := fallbackBits) (overheadBits := overheadBits)
    fallback henvelope hbits

/-- Route-coverage anchor: explicit bit bounds for the radius multiplier and
visible-alphabet base turn the polynomial envelope into the additive budget
`radiusBits + baseBits * sampleBound`. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_fallbackBits_add_radiusBits_add_baseBits_mul_sampleBound_ge_surfaceCard_of_envelopeFactors_le_twoPow_surjective
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits radiusBits baseBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hradius : sampleBound + 1 ≤ 2 ^ radiusBits)
    (hbase :
      Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1 ≤
        2 ^ baseBits)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k sampleBound fallbackBits fallback).predictorFamily.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      fallbackBits + radiusBits + baseBits * sampleBound :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_fallbackBits_add_radiusBits_add_baseBits_mul_sampleBound_ge_surfaceCard_of_envelopeFactors_le_twoPow_surjective
    (Z := Z) (k := k) (sampleBound := sampleBound)
    (fallbackBits := fallbackBits) (radiusBits := radiusBits) (baseBits := baseBits)
    fallback hradius hbase hsurj

/-- Route-coverage anchor: strict total-bit deficit after separately bounding
the radius and base factors blocks the bit-coded structured fallback endpoint. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_surjective_of_envelopeFactors_le_twoPow_and_fallbackBits_add_radiusBits_add_baseBits_mul_sampleBound_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits radiusBits baseBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hradius : sampleBound + 1 ≤ 2 ^ radiusBits)
    (hbase :
      Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1 ≤
        2 ^ baseBits)
    (hbits :
      fallbackBits + radiusBits + baseBits * sampleBound <
        Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound fallbackBits fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_envelopeFactors_le_twoPow_and_fallbackBits_add_radiusBits_add_baseBits_mul_sampleBound_lt_surfaceCard
    (Z := Z) (k := k) (sampleBound := sampleBound)
    (fallbackBits := fallbackBits) (radiusBits := radiusBits) (baseBits := baseBits)
    fallback hradius hbase hbits

/-- Route-coverage anchor: when the route only proves `sampleBound ≤
2 ^ radiusBits`, the successor factor in the sparse-support envelope costs one
extra radius bit. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_fallbackBits_add_radiusBits_succ_add_baseBits_mul_sampleBound_ge_surfaceCard_of_sampleBound_le_twoPow_and_base_le_twoPow_surjective
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits radiusBits baseBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hradius : sampleBound ≤ 2 ^ radiusBits)
    (hbase :
      Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1 ≤
        2 ^ baseBits)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k sampleBound fallbackBits fallback).predictorFamily.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      fallbackBits + (radiusBits + 1) + baseBits * sampleBound :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_fallbackBits_add_radiusBits_succ_add_baseBits_mul_sampleBound_ge_surfaceCard_of_sampleBound_le_twoPow_and_base_le_twoPow_surjective
    (Z := Z) (k := k) (sampleBound := sampleBound)
    (fallbackBits := fallbackBits) (radiusBits := radiusBits) (baseBits := baseBits)
    fallback hradius hbase hsurj

/-- Route-coverage anchor: strict bit deficit after paying the successor bit for
the radius multiplier blocks the bit-coded structured fallback endpoint. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_surjective_of_sampleBound_le_twoPow_and_base_le_twoPow_and_fallbackBits_add_radiusBits_succ_add_baseBits_mul_sampleBound_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits radiusBits baseBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hradius : sampleBound ≤ 2 ^ radiusBits)
    (hbase :
      Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1 ≤
        2 ^ baseBits)
    (hbits :
      fallbackBits + (radiusBits + 1) + baseBits * sampleBound <
        Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound fallbackBits fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_sampleBound_le_twoPow_and_base_le_twoPow_and_fallbackBits_add_radiusBits_succ_add_baseBits_mul_sampleBound_lt_surfaceCard
    (Z := Z) (k := k) (sampleBound := sampleBound)
    (fallbackBits := fallbackBits) (radiusBits := radiusBits) (baseBits := baseBits)
    fallback hradius hbase hbits

/-- Route-coverage anchor: if both the sample bound and the surface-cardinality
bound are stated for the raw values, the sparse-support envelope charges one
successor bit for each of them. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_fallbackBits_add_radiusBits_succ_add_baseBits_succ_mul_sampleBound_ge_surfaceCard_of_sampleBound_le_twoPow_and_surfaceCard_le_twoPow_surjective
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits radiusBits baseBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hradius : sampleBound ≤ 2 ^ radiusBits)
    (hbase :
      Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
        2 ^ baseBits)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k sampleBound fallbackBits fallback).predictorFamily.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      fallbackBits + (radiusBits + 1) + (baseBits + 1) * sampleBound :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_fallbackBits_add_radiusBits_succ_add_baseBits_succ_mul_sampleBound_ge_surfaceCard_of_sampleBound_le_twoPow_and_surfaceCard_le_twoPow_surjective
    (Z := Z) (k := k) (sampleBound := sampleBound)
    (fallbackBits := fallbackBits) (radiusBits := radiusBits) (baseBits := baseBits)
    fallback hradius hbase hsurj

/-- Route-coverage anchor: strict bit deficit after paying both successor bits
blocks the bit-coded structured fallback endpoint. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_surjective_of_sampleBound_le_twoPow_and_surfaceCard_le_twoPow_and_fallbackBits_add_radiusBits_succ_add_baseBits_succ_mul_sampleBound_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits radiusBits baseBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hradius : sampleBound ≤ 2 ^ radiusBits)
    (hbase :
      Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
        2 ^ baseBits)
    (hbits :
      fallbackBits + (radiusBits + 1) + (baseBits + 1) * sampleBound <
        Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound fallbackBits fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_sampleBound_le_twoPow_and_surfaceCard_le_twoPow_and_fallbackBits_add_radiusBits_succ_add_baseBits_succ_mul_sampleBound_lt_surfaceCard
    (Z := Z) (k := k) (sampleBound := sampleBound)
    (fallbackBits := fallbackBits) (radiusBits := radiusBits) (baseBits := baseBits)
    fallback hradius hbase hbits

/-- Route-coverage anchor: without sampled sparse overrides, a bit-coded
structured fallback family can be full-rule expressive only if the fallback bit
budget reaches the exact-visible input alphabet size. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_fallbackBits_ge_surfaceCard_of_zeroSample_surjective
    {Z : Type v} [Fintype Z] {k fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 0 fallbackBits fallback).predictorFamily.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ fallbackBits :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_fallbackBits_ge_surfaceCard_of_zeroSample_surjective
    (Z := Z) (k := k) (fallbackBits := fallbackBits) fallback hsurj

/-- Route-coverage anchor: a zero-sample bit-coded structured fallback endpoint
is not full-rule expressive when its fallback bit budget is below the
exact-visible input alphabet size. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_surjective_zeroSample_of_fallbackBits_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hbits : fallbackBits < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 0 fallbackBits fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_zeroSample_of_fallbackBits_lt_surfaceCard
    (Z := Z) (k := k) (fallbackBits := fallbackBits) fallback hbits

/-- Route-coverage anchor: the zero-sample lower bound is sharp for the
canonical full truth-table fallback decoder.  At exactly one fallback bit per
exact-visible input, the empty sample already realizes every local rule. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_surjective_zeroSample_exactVisibleRuleDecode
    {Z : Type v} [Fintype Z] {k : ℕ} :
    Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 0 (Fintype.card (ExactVisiblePostSwitchSurface Z k))
        (exactVisibleRuleDecode (Z := Z) (k := k))).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_surjective_zeroSample_exactVisibleRuleDecode
    (Z := Z) (k := k)

/-- Route-coverage anchor: with no sampled overrides, a bit-coded structured
fallback endpoint is full-rule expressive exactly when its fallback decoder is
full-rule expressive. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_zeroSample_surjective_iff_fallback_surjective
    {Z : Type v} {k fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k) :
    Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 0 fallbackBits fallback).predictorFamily.predict ↔
      Function.Surjective fallback :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_zeroSample_surjective_iff_fallback_surjective
    (Z := Z) (k := k) (fallbackBits := fallbackBits) fallback

/-- Route-coverage anchor: the canonical full truth-table fallback decoder is
full-rule expressive for every sample bound; the empty sample is enough. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_surjective_exactVisibleRuleDecode
    {Z : Type v} [Fintype Z] {k sampleBound : ℕ} :
    Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound (Fintype.card (ExactVisiblePostSwitchSurface Z k))
        (exactVisibleRuleDecode (Z := Z) (k := k))).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_surjective_exactVisibleRuleDecode
    (Z := Z) (k := k) (sampleBound := sampleBound)

/-- Route-coverage anchor: the raw exact-visible truth-table decoder itself is
surjective onto the full exact-visible rule family.  This is the compatibility
lemma needed to transport generic fallback-decoder theorems to the canonical
decoder specialization without re-proving them at the wrapper level. -/
theorem kpolyCoverage_anchor_exactVisibleRuleDecode_surjective
    {Z : Type v} [Fintype Z] {k : ℕ} :
    Function.Surjective (exactVisibleRuleDecode (Z := Z) (k := k)) := by
  intro rule
  refine ⟨exactVisibleRuleEncode (Z := Z) (k := k) rule, ?_⟩
  simpa using exactVisibleRuleDecode_encode (Z := Z) (k := k) rule

/-- Route-coverage anchor: if a bit-coded fallback decoder is already
full-rule expressive, then the wrapped bounded-sample endpoint cannot carry
shared exact sparse-threshold ERM data below the point-block visible-budget
threshold. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_nonempty_sharedExactZABSparseThresholdERMData_of_fallback_surjective_of_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k r sampleBound fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hsurj : Function.Surjective fallback)
    (zfeat : Z → BitVec r)
    (hs :
      2 * allAffinePointBlockFeatureCount (r + (k + k)) <
        Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMData
          (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
            Z k sampleBound fallbackBits fallback)
          zfeat) :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMData_of_fallback_surjective_of_lt_surfaceCard
    (Z := Z) (k := k) (sampleBound := sampleBound)
    (fallbackBits := fallbackBits) fallback hsurj zfeat hs

/-- Route-coverage anchor: on `BitVec n`, a bit-coded full-rule fallback side
channel does not rescue the stronger sparse-threshold recovery packet below
the same unconditional half-width ceiling. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_fallback_surjective_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
    {n k r sampleBound fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule (BitVec n) k)
    (hsurj : Function.Surjective fallback)
    (μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k))
    (zfeat : BitVec n → BitVec r)
    (q : ℝ≥0∞)
    (hgap : 2 * r + 2 * k + 1 < n) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          μ
          (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
            (BitVec n) k sampleBound fallbackBits fallback)
          zfeat
          q) :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_fallback_surjective_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
    (n := n) (k := k) (r := r) (sampleBound := sampleBound)
    (fallbackBits := fallbackBits) fallback hsurj μ zfeat q hgap

/-- Route-coverage anchor: if a bit-coded fallback decoder is already
full-rule expressive, then any sparse-threshold recovery packet on the wrapped
bounded-sample endpoint still forces the later lightest-point threshold. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_one_sub_apply_lightestPoint_le_of_nonempty_recovery_of_fallback_surjective
    {Z : Type v} [Fintype Z] {k r sampleBound fallbackBits : ℕ}
    [Nonempty (ExactVisiblePostSwitchSurface Z k)]
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)} {q : ℝ≥0∞}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hsurj : Function.Surjective fallback)
    (zfeat : Z → BitVec r)
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          μ
          (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
            Z k sampleBound fallbackBits fallback)
          zfeat
          q)) :
    1 - μ (PMF.lightestPoint μ) ≤ q :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_one_sub_apply_lightestPoint_le_of_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_fallback_surjective
    (Z := Z) (k := k) (sampleBound := sampleBound)
    (fallbackBits := fallbackBits) fallback hsurj zfeat h

/-- Route-coverage anchor: on the same bounded-sample bit-fallback endpoint,
surjective fallback expressivity lets two independent obstruction axes fire at
once.  Any hypothetical recovery witness must satisfy both the visible-width
budget and the lightest-point threshold. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_visibleWidth_and_lightestPoint_threshold_of_nonempty_recovery_of_fallback_surjective
    {n k r sampleBound fallbackBits : ℕ}
    [Nonempty (ExactVisiblePostSwitchSurface (BitVec n) k)]
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)} {q : ℝ≥0∞}
    (fallback : BitCode fallbackBits → ExactVisibleRule (BitVec n) k)
    (hsurj : Function.Surjective fallback)
    (zfeat : BitVec n → BitVec r)
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          μ
          (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
            (BitVec n) k sampleBound fallbackBits fallback)
          zfeat
          q)) :
    n ≤ 2 * r + 2 * k + 1 ∧
      1 - μ (PMF.lightestPoint μ) ≤ q := by
  refine ⟨?_, ?_⟩
  · exact
      boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_visibleWidth_le_two_mul_extractorWidth_add_two_mul_k_succ_of_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_fallback_surjective
        (sampleBound := sampleBound)
        (fallbackBits := fallbackBits)
        fallback hsurj μ zfeat q h
  · exact
      kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_one_sub_apply_lightestPoint_le_of_nonempty_recovery_of_fallback_surjective
        (k := k) (r := r) (sampleBound := sampleBound)
        (fallbackBits := fallbackBits)
        fallback hsurj zfeat h

/-- Route-coverage anchor: on any finite surjective actual-local endpoint, the
manuscript-facing sparse-threshold recovery packet already forces the intrinsic
lightest-point threshold.  The fallback-side repairs are only concrete
specializations of this surjective actual-local barrier. -/
theorem kpolyCoverage_anchor_surjectiveActualLocal_one_sub_apply_lightestPoint_le_of_nonempty_recovery
    {Z : Type v} [Fintype Z] {k r : ℕ} {Index : Type u} {Block : Type w}
    [Nonempty (ExactVisiblePostSwitchSurface Z k)]
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)} {q : ℝ≥0∞}
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    (zfeat : Z → BitVec r)
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          μ T zfeat q)) :
    1 - μ (PMF.lightestPoint μ) ≤ q := by
  rcases h with ⟨h⟩
  exact h.one_sub_apply_lightestPoint_le_of_surjective_predict hsurj

/-- Route-coverage anchor: below the intrinsic lightest-point threshold, no
extractor at all can support the manuscript-facing sparse-threshold recovery
packet on a surjective actual-local endpoint. -/
theorem kpolyCoverage_anchor_surjectiveActualLocal_not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_lt_one_sub_apply_lightestPoint
    {Z : Type v} [Fintype Z] {k r : ℕ} {Index : Type u} {Block : Type w}
    [Nonempty (ExactVisiblePostSwitchSurface Z k)]
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (q : ℝ≥0∞)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    (hq_lt : q < 1 - μ (PMF.lightestPoint μ)) :
    ¬ ∃ zfeat : Z → BitVec r,
        Nonempty
          (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
            μ T zfeat q) := by
  rintro ⟨zfeat, hdata⟩
  exact
    ActualSwitchedLocalInterface.not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_surjective_predict_of_lt_one_sub_apply_lightestPoint
      (μ := μ) (T := T) (zfeat := zfeat) hsurj hq_lt hdata

/-- Route-coverage anchor: in particular, the canonical truth-table fallback
decoder cannot rescue the wrapped bounded-sample endpoint below the same
lightest-point recovery threshold. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_nonempty_recovery_of_exactVisibleRuleDecode_of_lt_one_sub_apply_lightestPoint
    {Z : Type v} [Fintype Z] {k r sampleBound : ℕ}
    [Nonempty (ExactVisiblePostSwitchSurface Z k)]
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)} {q : ℝ≥0∞}
    (zfeat : Z → BitVec r)
    (hq_lt : q < 1 - μ (PMF.lightestPoint μ)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          μ
          (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
            Z k sampleBound
            (Fintype.card (ExactVisiblePostSwitchSurface Z k))
            (exactVisibleRuleDecode (Z := Z) (k := k)))
          zfeat
          q) :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_exactVisibleRuleDecode_of_lt_one_sub_apply_lightestPoint
    (Z := Z) (k := k) (sampleBound := sampleBound) zfeat hq_lt

/-- Route-coverage anchor: for the canonical exact-visible truth-table fallback
decoder, any hypothetical recovery witness on the wrapped bounded-sample
endpoint must satisfy both the visible-width ceiling and the lightest-point
threshold together. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_visibleWidth_and_lightestPoint_threshold_of_nonempty_recovery_of_exactVisibleRuleDecode
    {n k r sampleBound : ℕ}
    [Nonempty (ExactVisiblePostSwitchSurface (BitVec n) k)]
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)} {q : ℝ≥0∞}
    (zfeat : BitVec n → BitVec r)
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          μ
          (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
            (BitVec n) k sampleBound
            (Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k))
            (exactVisibleRuleDecode (Z := BitVec n) (k := k)))
          zfeat
          q)) :
    n ≤ 2 * r + 2 * k + 1 ∧
      1 - μ (PMF.lightestPoint μ) ≤ q := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_visibleWidth_and_lightestPoint_threshold_of_nonempty_recovery_of_fallback_surjective
      (k := k) (r := r) (sampleBound := sampleBound)
      (fallbackBits := Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k))
      (μ := μ) (q := q)
      (exactVisibleRuleDecode (Z := BitVec n) (k := k))
      (kpolyCoverage_anchor_exactVisibleRuleDecode_surjective
        (Z := BitVec n) (k := k))
      zfeat h

/-- Route-coverage anchor: on the canonical exact-visible truth-table fallback
decoder, violating either the visible-width ceiling or the lightest-point
threshold already rules out the manuscript-facing recovery packet. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_nonempty_recovery_of_exactVisibleRuleDecode_of_visibleWidth_gap_or_lt_one_sub_apply_lightestPoint
    {n k r sampleBound : ℕ}
    [Nonempty (ExactVisiblePostSwitchSurface (BitVec n) k)]
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)} {q : ℝ≥0∞}
    (zfeat : BitVec n → BitVec r)
    (hbad : 2 * r + 2 * k + 1 < n ∨ q < 1 - μ (PMF.lightestPoint μ)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          μ
          (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
            (BitVec n) k sampleBound
            (Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k))
            (exactVisibleRuleDecode (Z := BitVec n) (k := k)))
          zfeat
          q) := by
  rcases hbad with hgap | hq_lt
  · exact
      kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_fallback_surjective_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
        (sampleBound := sampleBound)
        (fallbackBits := Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k))
        (exactVisibleRuleDecode (Z := BitVec n) (k := k))
        (kpolyCoverage_anchor_exactVisibleRuleDecode_surjective
          (Z := BitVec n) (k := k))
        μ zfeat q hgap
  · exact
      kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_nonempty_recovery_of_exactVisibleRuleDecode_of_lt_one_sub_apply_lightestPoint
        (k := k) (r := r) (sampleBound := sampleBound)
        (μ := μ) (q := q) zfeat hq_lt

/-- Route-coverage anchor: with one sampled sparse override, full-rule
expressivity of a bit-coded structured fallback endpoint forces the concrete
budget `2 ^ fallbackBits * (surfaceCard + 1)`. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_boolClassifierSpace_card_le_bitCode_mul_surfaceCard_succ_of_oneSample_surjective
    {Z : Type v} [Fintype Z] {k fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 1 fallbackBits fallback).predictorFamily.predict) :
    2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      2 ^ fallbackBits *
        (Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1) :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_boolClassifierSpace_card_le_bitCode_mul_surfaceCard_succ_of_oneSample_surjective
    (Z := Z) (k := k) (fallbackBits := fallbackBits) fallback hsurj

/-- Route-coverage anchor: if the one-sample bit-coded fallback budget times
`surfaceCard + 1` is still below the full exact-visible Boolean rule cube, the
endpoint is not full-rule expressive. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_surjective_oneSample_of_bitCode_mul_surfaceCard_succ_lt_boolClassifierSpace
    {Z : Type v} [Fintype Z] {k fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hcard :
      2 ^ fallbackBits *
          (Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1) <
        2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 1 fallbackBits fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_oneSample_of_bitCode_mul_surfaceCard_succ_lt_boolClassifierSpace
    (Z := Z) (k := k) (fallbackBits := fallbackBits) fallback hcard

/-- Route-coverage anchor: allowing two sampled sparse overrides gives exactly
the quadratic support multiplier `1 + surfaceCard + choose surfaceCard 2`; full
rule expressivity must fit inside this product budget. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_boolClassifierSpace_card_le_bitCode_mul_one_add_surfaceCard_add_choose_two_of_twoSample_surjective
    {Z : Type v} [Fintype Z] {k fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 2 fallbackBits fallback).predictorFamily.predict) :
    2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      2 ^ fallbackBits *
        (1 + Fintype.card (ExactVisiblePostSwitchSurface Z k) +
          (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose 2) :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_boolClassifierSpace_card_le_bitCode_mul_one_add_surfaceCard_add_choose_two_of_twoSample_surjective
    (Z := Z) (k := k) (fallbackBits := fallbackBits) fallback hsurj

/-- Route-coverage anchor: a bit-coded structured fallback plus two sampled
overrides is not full-rule expressive when its exact quadratic product budget
is below the Boolean rule cube. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_surjective_twoSample_of_bitCode_mul_one_add_surfaceCard_add_choose_two_lt_boolClassifierSpace
    {Z : Type v} [Fintype Z] {k fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hcard :
      2 ^ fallbackBits *
          (1 + Fintype.card (ExactVisiblePostSwitchSurface Z k) +
            (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose 2) <
        2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 2 fallbackBits fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_twoSample_of_bitCode_mul_one_add_surfaceCard_add_choose_two_lt_boolClassifierSpace
    (Z := Z) (k := k) (fallbackBits := fallbackBits) fallback hcard

/-- Route-coverage anchor: if the exact two-sample quadratic support envelope
fits into `overheadBits` bits, full rule coverage still forces the total
fallback-plus-overhead bit budget to reach the visible alphabet size. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_fallbackBits_add_overheadBits_ge_surfaceCard_of_twoSample_quadraticEnvelope_le_twoPow_surjective
    {Z : Type v} [Fintype Z] {k fallbackBits overheadBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (henvelope :
      1 + Fintype.card (ExactVisiblePostSwitchSurface Z k) +
          (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose 2 ≤
        2 ^ overheadBits)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 2 fallbackBits fallback).predictorFamily.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      fallbackBits + overheadBits :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_fallbackBits_add_overheadBits_ge_surfaceCard_of_twoSample_quadraticEnvelope_le_twoPow_surjective
    (Z := Z) (k := k) (fallbackBits := fallbackBits) (overheadBits := overheadBits)
    fallback henvelope hsurj

/-- Route-coverage anchor: strict bit deficit against the exact two-sample
quadratic support envelope blocks full-rule expressivity. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_surjective_twoSample_of_quadraticEnvelope_le_twoPow_and_fallbackBits_add_overheadBits_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k fallbackBits overheadBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (henvelope :
      1 + Fintype.card (ExactVisiblePostSwitchSurface Z k) +
          (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose 2 ≤
        2 ^ overheadBits)
    (hbits :
      fallbackBits + overheadBits <
        Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 2 fallbackBits fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_twoSample_of_quadraticEnvelope_le_twoPow_and_fallbackBits_add_overheadBits_lt_surfaceCard
    (Z := Z) (k := k) (fallbackBits := fallbackBits) (overheadBits := overheadBits)
    fallback henvelope hbits

/-- Route-coverage anchor: with one sampled sparse override, a successor bit
bound for `surfaceCard + 1` converts the exact product bound into the additive
bit budget `fallbackBits + baseBits`. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_fallbackBits_add_baseBits_ge_surfaceCard_of_oneSample_surfaceCard_succ_le_twoPow_surjective
    {Z : Type v} [Fintype Z] {k fallbackBits baseBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hbase :
      Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1 ≤
        2 ^ baseBits)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 1 fallbackBits fallback).predictorFamily.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      fallbackBits + baseBits :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_fallbackBits_add_baseBits_ge_surfaceCard_of_oneSample_surfaceCard_succ_le_twoPow_surjective
    (Z := Z) (k := k) (fallbackBits := fallbackBits) (baseBits := baseBits)
    fallback hbase hsurj

/-- Route-coverage anchor: strict bit deficit for the exact one-sample
successor-count envelope blocks full-rule expressivity. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_surjective_oneSample_of_surfaceCard_succ_le_twoPow_and_fallbackBits_add_baseBits_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k fallbackBits baseBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hbase :
      Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1 ≤
        2 ^ baseBits)
    (hbits :
      fallbackBits + baseBits <
        Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 1 fallbackBits fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_oneSample_of_surfaceCard_succ_le_twoPow_and_fallbackBits_add_baseBits_lt_surfaceCard
    (Z := Z) (k := k) (fallbackBits := fallbackBits) (baseBits := baseBits)
    fallback hbase hbits

/-- Route-coverage anchor: if the manuscript route states only a raw bit bound
on `surfaceCard`, the one-sample sparse-support envelope still needs one extra
successor bit. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_fallbackBits_add_baseBits_succ_ge_surfaceCard_of_oneSample_surfaceCard_le_twoPow_surjective
    {Z : Type v} [Fintype Z] {k fallbackBits baseBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hbase :
      Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
        2 ^ baseBits)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 1 fallbackBits fallback).predictorFamily.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      fallbackBits + (baseBits + 1) :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_fallbackBits_add_baseBits_succ_ge_surfaceCard_of_oneSample_surfaceCard_le_twoPow_surjective
    (Z := Z) (k := k) (fallbackBits := fallbackBits) (baseBits := baseBits)
    fallback hbase hsurj

/-- Route-coverage anchor: strict bit deficit for the raw one-sample
surface-cardinality bound blocks full-rule expressivity. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_surjective_oneSample_of_surfaceCard_le_twoPow_and_fallbackBits_add_baseBits_succ_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k fallbackBits baseBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hbase :
      Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
        2 ^ baseBits)
    (hbits :
      fallbackBits + (baseBits + 1) <
        Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 1 fallbackBits fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_oneSample_of_surfaceCard_le_twoPow_and_fallbackBits_add_baseBits_succ_lt_surfaceCard
    (Z := Z) (k := k) (fallbackBits := fallbackBits) (baseBits := baseBits)
    fallback hbase hbits

/-- Route-coverage anchor: once the sample bound reaches the exact-visible
alphabet size, bounded sample-level plug-in majority has no clocked
finite-learning payload below the truth-table budget. -/
theorem kpolyCoverage_anchor_boundedSampleMajority_not_clockedPayload_of_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k s sampleBound clock : ℕ}
    (hbound : Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ClockedKpolyFiniteLearningPayload
        (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).predictorFamily
        s clock :=
  boundedSamplePluginMajorityActualSwitchedLocalInterface_not_clockedKpolyFiniteLearningPayload_of_lt_surfaceCard
    hbound hs

/-- Route-coverage anchor: once the sample bound reaches the exact-visible
alphabet size, bounded sample-level plug-in majority still cannot be treated as
bounded ZAB decision-list constructor data below the truth-table budget. -/
theorem kpolyCoverage_anchor_boundedSampleMajority_not_zabDecisionListData_of_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k r sampleBound : ℕ}
    (hbound : Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound)
    (zfeat : Z → BitVec r)
    (hs : r + 2 * k + 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.ZABDecisionListData
          (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound) zfeat) :=
  boundedSamplePluginMajorityActualSwitchedLocalInterface_not_zabDecisionListData_of_lt_surfaceCard
    hbound zfeat hs

/-- Route-coverage anchor: an actual-local interface can have observed
block-output behaviour bounded by a finite support while its full exact-visible
local-rule image still has no below-surface predictor cover. -/
theorem kpolyCoverage_anchor_supportFullRule_observedSmall_and_not_exactVisibleCover
    {Z : Type v} [Fintype Z] {Block : Type v} [Fintype Block] {k s : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.FinitePredictorCover
        (2 ^ Fintype.card Block) ∧
      ¬ (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily.FinitePredictorCover
        (2 ^ s) :=
  supportFullRule_observedSmall_and_not_exactVisibleCover visibleOf hs

/-- Route-coverage anchor: finite observed actual-local support still does not
give the clocked finite-learning payload below the full exact-visible surface
threshold. -/
theorem kpolyCoverage_anchor_supportFullRule_not_clockedPayload_of_lt_surfaceCard
    {Z : Type v} [Fintype Z] {Block : Type v} {k s clock : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ClockedKpolyFiniteLearningPayload
        (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily s clock :=
  supportFullRule_not_clockedKpolyFiniteLearningPayload_of_lt_surfaceCard visibleOf hs

/-- Route-coverage anchor: a uniform visible section is sufficient to transfer
an observed-output finite cover to the full exact-visible predictor family. -/
theorem kpolyCoverage_anchor_uniformVisibleSection_transfers_observed_cover
    {Z : Type v} {Block Index : Type v} {k N : ℕ}
    (T : ActualSwitchedLocalInterface Z k Index Block)
    {sec : ExactVisiblePostSwitchSurface Z k → Block}
    (hsec : T.HasUniformVisibleSection sec)
    (hcover : T.outputFamily.FinitePredictorCover N) :
    T.predictorFamily.FinitePredictorCover N :=
  T.predictorFamily_finitePredictorCover_of_outputFamily_finitePredictorCover
    hsec hcover

/-- Route-coverage anchor: in the support-full-rule construction, a uniform
visible section forces the actual block support to be at least as large as the
full exact-visible surface. -/
theorem kpolyCoverage_anchor_supportFullRule_uniformSection_forces_surfaceCard_le_supportCard
    {Z : Type v} [Fintype Z] {Block : Type v} [Fintype Block] {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    {sec : ExactVisiblePostSwitchSurface Z k → Block}
    (hsec :
      (supportFullRuleActualSwitchedLocalInterface visibleOf).HasUniformVisibleSection sec) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ Fintype.card Block :=
  supportFullRule_surfaceCard_le_blockCard_of_uniformVisibleSection visibleOf hsec

/-- Route-coverage anchor: therefore finite observed support cannot repair the
observed-output bridge when the support has smaller cardinality than the full
exact-visible surface. -/
theorem kpolyCoverage_anchor_supportFullRule_no_uniformSection_below_surfaceCard
    {Z : Type v} [Fintype Z] {Block : Type v} [Fintype Block] {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (hcard :
      Fintype.card Block < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ∃ sec : ExactVisiblePostSwitchSurface Z k → Block,
      (supportFullRuleActualSwitchedLocalInterface visibleOf).HasUniformVisibleSection sec :=
  supportFullRule_not_hasUniformVisibleSection_of_card_lt_surfaceCard visibleOf hcard

/-- Route-coverage anchor: the reachable-support quotient is only the pullback
of the exact-visible family along `visibleOf`. -/
theorem kpolyCoverage_anchor_supportFullRule_outputFamily_factorsThrough_predictorFamily
    {Z : Type v} {Block : Type v} {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k) :
    (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.FactorsThrough
      visibleOf (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily :=
  supportFullRule_outputFamily_factorsThrough_predictorFamily visibleOf

/-- Route-coverage anchor: exact recovery from the observed quotient forces
the support map to hit every exact-visible input. -/
theorem kpolyCoverage_anchor_supportFullRule_observedRuleMap_injective_forces_surjective
    {Z : Type v} {Block : Type v} {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (hinj :
      Function.Injective
        (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict) :
    Function.Surjective visibleOf :=
  supportFullRule_observedRuleMap_injective_forces_visibleOf_surjective visibleOf hinj

/-- Route-coverage anchor: any exact decoder from observed block-output traces
to full exact-visible rules forces the support map to hit every exact-visible
input. -/
theorem kpolyCoverage_anchor_supportFullRule_exactDecoder_forces_surjective
    {Z : Type v} {Block : Type v} {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (decode : (Block → Bool) → ExactVisibleRule Z k)
    (hdecode :
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          rule) :
    Function.Surjective visibleOf :=
  supportFullRule_exactDecoder_forces_visibleOf_surjective
    visibleOf decode hdecode

/-- Route-coverage anchor: any downstream property decoded from observed
block-output traces must be constant on observed-output fibers. -/
theorem kpolyCoverage_anchor_supportFullRule_propertyDecoder_constant_on_observedFibers
    {Z : Type v} {Block : Type v} {α : Type v} {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (property : ExactVisibleRule Z k → α)
    (decode : (Block → Bool) → α)
    (hdecode :
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          property rule)
    {rule₀ rule₁ : ExactVisibleRule Z k}
    (hsame :
      (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₀ =
        (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₁) :
    property rule₀ = property rule₁ :=
  supportFullRule_propertyDecoder_constant_on_observedFibers
    visibleOf property decode hdecode hsame

/-- Route-coverage anchor: a downstream property is decodable from observed
block-output traces exactly when it is constant on observed-output fibers. -/
theorem kpolyCoverage_anchor_supportFullRule_propertyDecoder_iff_constant_on_observedFibers
    {Z : Type v} {Block : Type v} {α : Type v} {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (property : ExactVisibleRule Z k → α) :
    (∃ decode : (Block → Bool) → α,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          property rule) ↔
      ∀ {rule₀ rule₁ : ExactVisibleRule Z k},
        (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₀ =
          (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₁ →
        property rule₀ = property rule₁ :=
  supportFullRule_exists_propertyDecoder_iff_constant_on_observedFibers
    visibleOf property

/-- Route-coverage anchor: any downstream property separating one observed
fiber cannot be decoded from observed block-output traces. -/
theorem kpolyCoverage_anchor_supportFullRule_no_propertyDecoder_of_same_output_ne
    {Z : Type v} {Block : Type v} {α : Type v} {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (property : ExactVisibleRule Z k → α)
    {rule₀ rule₁ : ExactVisibleRule Z k}
    (hsame :
      (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₀ =
        (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₁)
    (hprop : property rule₀ ≠ property rule₁) :
    ¬ ∃ decode : (Block → Bool) → α,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          property rule :=
  supportFullRule_not_exists_propertyDecoder_of_same_output_ne
    visibleOf property hsame hprop

/-- Route-coverage anchor: a single exact-visible point query is decodable
from observed block-output traces exactly when that point lies in the reachable
support. -/
theorem kpolyCoverage_anchor_supportFullRule_evalDecoder_iff_mem_range
    {Z : Type v} {Block : Type v} {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (u₀ : ExactVisiblePostSwitchSurface Z k) :
    (∃ decode : (Block → Bool) → Bool,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          rule u₀) ↔ ∃ phi, visibleOf phi = u₀ :=
  supportFullRule_exists_evalDecoder_iff_mem_range
    visibleOf u₀

/-- Route-coverage anchor: decoding every exact-visible point query from
observed block-output traces is equivalent to full reachable-support
surjectivity. -/
theorem kpolyCoverage_anchor_supportFullRule_all_evalDecoders_iff_surjective
    {Z : Type v} {Block : Type v} {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k) :
    (∀ u₀ : ExactVisiblePostSwitchSurface Z k,
      ∃ decode : (Block → Bool) → Bool,
        ∀ rule : ExactVisibleRule Z k,
          decode
              ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
            rule u₀) ↔ Function.Surjective visibleOf :=
  supportFullRule_all_evalDecoders_iff_visibleOf_surjective
    visibleOf

/-- Route-coverage anchor: a whole family of exact-visible point queries is
decodable from observed block-output traces exactly when every queried point is
in reachable support. -/
theorem kpolyCoverage_anchor_supportFullRule_queryDecoder_iff_forall_mem_range
    {Z : Type v} {Block : Type v} {Query : Type v} {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (queryOf : Query → ExactVisiblePostSwitchSurface Z k) :
    (∃ decode : (Block → Bool) → Query → Bool,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          fun q => rule (queryOf q)) ↔ ∀ q, ∃ phi, visibleOf phi = queryOf q :=
  supportFullRule_exists_queryDecoder_iff_forall_mem_range
    visibleOf queryOf

/-- Route-coverage anchor: a query family containing one unreachable
exact-visible point cannot be decoded from observed block-output traces. -/
theorem kpolyCoverage_anchor_supportFullRule_no_queryDecoder_of_missed_query
    {Z : Type v} {Block : Type v} {Query : Type v} {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (queryOf : Query → ExactVisiblePostSwitchSurface Z k)
    (q₀ : Query) (hmiss : ∀ phi, visibleOf phi ≠ queryOf q₀) :
    ¬ ∃ decode : (Block → Bool) → Query → Bool,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          fun q => rule (queryOf q) :=
  supportFullRule_not_exists_queryDecoder_of_missed_query
    visibleOf queryOf q₀ hmiss

/-- Route-coverage anchor: an adaptive exact-visible query tree is decodable
from observed block-output traces whenever all points it may query are in
reachable support. -/
theorem kpolyCoverage_anchor_supportFullRule_adaptiveQueryDecoder_of_allQueriesReachable
    {Z : Type v} {Block : Type v} {α : Type v} {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (tree : AdaptiveBoolQueryTree (ExactVisiblePostSwitchSurface Z k) α)
    (hreach : AdaptiveBoolQueryTree.AllQueriesReachable visibleOf tree) :
    ∃ decode : (Block → Bool) → α,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          AdaptiveBoolQueryTree.eval rule tree :=
  supportFullRule_exists_adaptiveQueryDecoder_of_allQueriesReachable
    visibleOf tree hreach

/-- Route-coverage anchor: adaptive exact-visible query-tree decodability is
equivalent to constancy on observed-output fibers. -/
theorem kpolyCoverage_anchor_supportFullRule_adaptiveQueryDecoder_iff_constant_on_observedFibers
    {Z : Type v} {Block : Type v} {α : Type v} {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (tree : AdaptiveBoolQueryTree (ExactVisiblePostSwitchSurface Z k) α) :
    (∃ decode : (Block → Bool) → α,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          AdaptiveBoolQueryTree.eval rule tree) ↔
      ∀ {rule₀ rule₁ : ExactVisibleRule Z k},
        (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₀ =
          (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₁ →
        AdaptiveBoolQueryTree.eval rule₀ tree =
          AdaptiveBoolQueryTree.eval rule₁ tree :=
  supportFullRule_exists_adaptiveQueryDecoder_iff_constant_on_observedFibers
    visibleOf tree

/-- Route-coverage anchor: two full rules with the same observed trace but
different adaptive-tree outputs refute every observed-trace decoder for that
tree. -/
theorem kpolyCoverage_anchor_supportFullRule_no_adaptiveQueryDecoder_of_same_output_eval_ne
    {Z : Type v} {Block : Type v} {α : Type v} {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (tree : AdaptiveBoolQueryTree (ExactVisiblePostSwitchSurface Z k) α)
    {rule₀ rule₁ : ExactVisibleRule Z k}
    (hsame :
      (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₀ =
        (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₁)
    (hne :
      AdaptiveBoolQueryTree.eval rule₀ tree ≠
        AdaptiveBoolQueryTree.eval rule₁ tree) :
    ¬ ∃ decode : (Block → Bool) → α,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          AdaptiveBoolQueryTree.eval rule tree :=
  supportFullRule_not_exists_adaptiveQueryDecoder_of_same_output_eval_ne
    visibleOf tree hsame hne

/-- Route-coverage anchor: a missed root query with distinct branch outputs
cannot be decoded from observed block-output traces. -/
theorem kpolyCoverage_anchor_supportFullRule_no_rootAdaptiveQueryDecoder_of_missed_point_ne
    {Z : Type v} {Block : Type v} {α : Type v} {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (u₀ : ExactVisiblePostSwitchSurface Z k)
    {valueFalse valueTrue : α}
    (hmiss : ∀ phi, visibleOf phi ≠ u₀)
    (hne : valueFalse ≠ valueTrue) :
    ¬ ∃ decode : (Block → Bool) → α,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          AdaptiveBoolQueryTree.eval rule
            (AdaptiveBoolQueryTree.query u₀
              (AdaptiveBoolQueryTree.leaf valueFalse)
              (AdaptiveBoolQueryTree.leaf valueTrue)) :=
  supportFullRule_not_exists_rootAdaptiveQueryDecoder_of_missed_point_ne
    visibleOf u₀ hmiss hne

/-- Route-coverage anchor: below surface cardinality, the observed
reachable-support quotient cannot identify full exact-visible rules. -/
theorem kpolyCoverage_anchor_supportFullRule_no_observedRuleMap_injective_below_surfaceCard
    {Z : Type v} [Fintype Z] {Block : Type v} [Fintype Block] {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (hcard :
      Fintype.card Block < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Injective
        (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict :=
  supportFullRule_not_observedRuleMap_injective_of_card_lt_surfaceCard visibleOf hcard

/-- Route-coverage anchor: cardinally small support yields two exact-visible
rules that are distinct as full predictors but indistinguishable on observed
block outputs. -/
theorem kpolyCoverage_anchor_supportFullRule_distinct_rules_same_output_below_surfaceCard
    {Z : Type v} [Fintype Z] {Block : Type v} [Fintype Block] {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (hcard :
      Fintype.card Block < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ∃ rule₀ rule₁ : ExactVisibleRule Z k,
      rule₀ ≠ rule₁ ∧
        (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₀ =
          (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₁ ∧
        (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily.predict rule₀ ≠
          (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily.predict rule₁ :=
  supportFullRule_exists_distinct_rules_same_outputFamily_of_card_lt_surfaceCard
    visibleOf hcard

/-- Route-coverage anchor: below surface cardinality, no post-processing
decoder can recover all full exact-visible rules from observed block-output
traces. -/
theorem kpolyCoverage_anchor_supportFullRule_no_exactDecoder_below_surfaceCard
    {Z : Type v} [Fintype Z] {Block : Type v} [Fintype Block] {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (hcard :
      Fintype.card Block < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ∃ decode : (Block → Bool) → ExactVisibleRule Z k,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          rule :=
  supportFullRule_not_exists_exactDecoder_of_card_lt_surfaceCard
    visibleOf hcard

/-- Route-coverage anchor: below surface cardinality, at least one
exact-visible rule bit is not observable from the block-output quotient. -/
theorem kpolyCoverage_anchor_supportFullRule_exists_unobservable_eval_below_surfaceCard
    {Z : Type v} [Fintype Z] {Block : Type v} [Fintype Block] {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (hcard :
      Fintype.card Block < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ∃ u₀ : ExactVisiblePostSwitchSurface Z k,
      ¬ ∃ decode : (Block → Bool) → Bool,
        ∀ rule : ExactVisibleRule Z k,
          decode
              ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
            rule u₀ :=
  supportFullRule_exists_unobservable_eval_of_card_lt_surfaceCard
    visibleOf hcard

/-- Route-coverage anchor: a one-block actual-local interface is the minimal
finite-support instance of the same obstruction. -/
theorem kpolyCoverage_anchor_oneBlockFullRule_observedSmall_and_not_exactVisibleCover
    {Z : Type v} [Fintype Z] {k s : ℕ}
    (u0 : ExactVisiblePostSwitchSurface Z k)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    (oneBlockFullRuleActualSwitchedLocalInterface u0).outputFamily.FinitePredictorCover 2 ∧
      ¬ (oneBlockFullRuleActualSwitchedLocalInterface u0).predictorFamily.FinitePredictorCover
        (2 ^ s) :=
  oneBlockFullRule_observedSmall_and_not_exactVisibleCover u0 hs

/-- Route-coverage anchor: the same one-block actual-local interface refutes
deriving the clocked finite-learning payload from observed support smallness. -/
theorem kpolyCoverage_anchor_oneBlockFullRule_not_clockedPayload_of_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k s clock : ℕ}
    (u0 : ExactVisiblePostSwitchSurface Z k)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ClockedKpolyFiniteLearningPayload
        (oneBlockFullRuleActualSwitchedLocalInterface u0).predictorFamily s clock :=
  oneBlockFullRule_not_clockedKpolyFiniteLearningPayload_of_lt_surfaceCard u0 hs

/-- Route-coverage anchor: the one-block support quotient admits no exact full
rule decoder once the exact-visible surface has more than one point. -/
theorem kpolyCoverage_anchor_oneBlockFullRule_no_exactDecoder
    {Z : Type v} [Fintype Z] {k : ℕ}
    (u0 : ExactVisiblePostSwitchSurface Z k)
    (hcard : 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ∃ decode : (Unit → Bool) → ExactVisibleRule Z k,
      ∀ rule : ExactVisibleRule Z k,
        decode ((oneBlockFullRuleActualSwitchedLocalInterface u0).outputFamily.predict rule) =
          rule :=
  oneBlockFullRule_not_exists_exactDecoder_of_one_lt_surfaceCard u0 hcard

/-- Route-coverage anchor: in the one-block case, some exact-visible rule bit
is not observable once the exact-visible surface has more than one point. -/
theorem kpolyCoverage_anchor_oneBlockFullRule_exists_unobservable_eval
    {Z : Type v} [Fintype Z] {k : ℕ}
    (u0 : ExactVisiblePostSwitchSurface Z k)
    (hcard : 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ∃ u : ExactVisiblePostSwitchSurface Z k,
      ¬ ∃ decode : (Unit → Bool) → Bool,
        ∀ rule : ExactVisibleRule Z k,
          decode ((oneBlockFullRuleActualSwitchedLocalInterface u0).outputFamily.predict rule) =
            rule u :=
  oneBlockFullRule_exists_unobservable_eval_of_one_lt_surfaceCard u0 hcard

/-- Route-coverage anchor: exact visible compression is equivalently a finite
quotient-code presentation of size at most `2^s`. -/
theorem kpolyCoverage_anchor_exactVisibleCompressionTarget_iff_finitePredictorQuotient
    {Z : Type*} {k s : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s ↔
      G.FinitePredictorQuotient (2 ^ s) :=
  exactVisibleCompressionTarget_iff_finitePredictorQuotient

/-- Route-coverage anchor: clocked exact-visible realization is equivalently a
finite quotient-code presentation of size at most `2^s`. -/
theorem kpolyCoverage_anchor_clockedRealization_iff_finitePredictorQuotient
    {Z : Type*} {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} :
    (∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F) ↔
      G.FinitePredictorQuotient (2 ^ s) :=
  exists_clockedExactVisibleRealization_iff_finitePredictorQuotient

/-- Route-coverage anchor: finite predictor-image covers can be represented by a
finite list of actual selected indices, and conversely. -/
theorem kpolyCoverage_anchor_finitePredictorCover_iff_finiteIndexRepresentativeCover
    {Index Input : Type*} {G : IndexedPredictorFamily Index Input} {N : ℕ} :
    G.FinitePredictorCover N ↔ G.FiniteIndexRepresentativeCover N :=
  IndexedPredictorFamily.finitePredictorCover_iff_finiteIndexRepresentativeCover

/-- Route-coverage anchor: finite predictor-image covers are equivalently
finite quotient-code presentations. -/
theorem kpolyCoverage_anchor_finitePredictorCover_iff_finitePredictorQuotient
    {Index Input : Type*} {G : IndexedPredictorFamily Index Input} {N : ℕ} :
    G.FinitePredictorCover N ↔ G.FinitePredictorQuotient N :=
  IndexedPredictorFamily.finitePredictorCover_iff_finitePredictorQuotient

/-- Route-coverage anchor: finite representative-index covers are equivalently
finite quotient-code presentations. -/
theorem kpolyCoverage_anchor_finiteIndexRepresentativeCover_iff_finitePredictorQuotient
    {Index Input : Type*} {G : IndexedPredictorFamily Index Input} {N : ℕ} :
    G.FiniteIndexRepresentativeCover N ↔ G.FinitePredictorQuotient N :=
  IndexedPredictorFamily.finiteIndexRepresentativeCover_iff_finitePredictorQuotient

/-- Route-coverage anchor: exact visible compression is equivalently a finite
representative-index cover of size at most `2^s`. -/
theorem kpolyCoverage_anchor_exactVisibleCompressionTarget_iff_finiteIndexRepresentativeCover
    {Z : Type*} {k s : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s ↔
      G.FiniteIndexRepresentativeCover (2 ^ s) :=
  exactVisibleCompressionTarget_iff_finiteIndexRepresentativeCover

/-- Route-coverage anchor: clocked exact-visible realization is equivalently a
finite representative-index cover of size at most `2^s`. -/
theorem kpolyCoverage_anchor_clockedRealization_iff_finiteIndexRepresentativeCover
    {Z : Type*} {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} :
    (∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F) ↔
      G.FiniteIndexRepresentativeCover (2 ^ s) :=
  exists_clockedExactVisibleRealization_iff_finiteIndexRepresentativeCover

/-- Route-coverage anchor: nonexistence of a clocked exact-visible realization
is equivalently nonexistence of a finite representative-index cover of size at
most `2^s`. -/
theorem kpolyCoverage_anchor_not_clockedRealization_iff_not_finiteIndexRepresentativeCover
    {Z : Type*} {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} :
    (¬ ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F) ↔
      ¬ G.FiniteIndexRepresentativeCover (2 ^ s) :=
  not_exists_clockedExactVisibleRealization_iff_not_finiteIndexRepresentativeCover

/-- Route-coverage anchor: nonexistence of a clocked exact-visible realization
is equivalently nonexistence of a finite quotient-code presentation of size at
most `2^s`. -/
theorem kpolyCoverage_anchor_not_clockedRealization_iff_not_finitePredictorQuotient
    {Z : Type*} {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} :
    (¬ ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F) ↔
      ¬ G.FinitePredictorQuotient (2 ^ s) :=
  not_exists_clockedExactVisibleRealization_iff_not_finitePredictorQuotient

/-- Route-coverage anchor: finite predictor-image covers are stable under
weakening the allowed cover size. -/
theorem kpolyCoverage_anchor_finitePredictorCover_mono
    {Index Input : Type*} {G : IndexedPredictorFamily Index Input} {N M : ℕ}
    (hNM : N ≤ M) (hcover : G.FinitePredictorCover N) :
    G.FinitePredictorCover M :=
  IndexedPredictorFamily.finitePredictorCover_mono hNM hcover

/-- Route-coverage anchor: finite representative-index covers are stable under
weakening the allowed representative count. -/
theorem kpolyCoverage_anchor_finiteIndexRepresentativeCover_mono
    {Index Input : Type*} {G : IndexedPredictorFamily Index Input} {N M : ℕ}
    (hNM : N ≤ M) (hrep : G.FiniteIndexRepresentativeCover N) :
    G.FiniteIndexRepresentativeCover M :=
  IndexedPredictorFamily.finiteIndexRepresentativeCover_mono hNM hrep

/-- Route-coverage anchor: finite quotient-code presentations are stable under
weakening the allowed code count. -/
theorem kpolyCoverage_anchor_finitePredictorQuotient_mono
    {Index Input : Type*} {G : IndexedPredictorFamily Index Input} {N M : ℕ}
    (hNM : N ≤ M) (hquot : G.FinitePredictorQuotient N) :
    G.FinitePredictorQuotient M :=
  IndexedPredictorFamily.finitePredictorQuotient_mono hNM hquot

/-- Route-coverage anchor: finite predictor-image covers pull back across an
explicit factor map. -/
theorem kpolyCoverage_anchor_finitePredictorCover_of_factorsThrough
    {Index Input View : Type*} {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View} {view : Input → View} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hcover : H.FinitePredictorCover N) :
    G.FinitePredictorCover N :=
  IndexedPredictorFamily.finitePredictorCover_of_factorsThrough hfactor hcover

/-- Route-coverage anchor: when a factor map has a section, finite
predictor-image covers push back to the summary family. -/
theorem kpolyCoverage_anchor_finitePredictorCover_of_factorsThrough_of_rightInverse
    {Index Input View : Type*} {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View} {view : Input → View}
    {sec : View → Input} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hcover : G.FinitePredictorCover N) :
    H.FinitePredictorCover N :=
  IndexedPredictorFamily.finitePredictorCover_of_factorsThrough_of_rightInverse
    hfactor hsection hcover

/-- Route-coverage anchor: finite representative-index covers pull back across
an explicit factor map. -/
theorem kpolyCoverage_anchor_finiteIndexRepresentativeCover_of_factorsThrough
    {Index Input View : Type*} {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View} {view : Input → View} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hrep : H.FiniteIndexRepresentativeCover N) :
    G.FiniteIndexRepresentativeCover N :=
  IndexedPredictorFamily.finiteIndexRepresentativeCover_of_factorsThrough
    hfactor hrep

/-- Route-coverage anchor: when a factor map has a section, finite
representative-index covers push back to the summary family. -/
theorem kpolyCoverage_anchor_finiteIndexRepresentativeCover_of_factorsThrough_of_rightInverse
    {Index Input View : Type*} {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View} {view : Input → View}
    {sec : View → Input} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hrep : G.FiniteIndexRepresentativeCover N) :
    H.FiniteIndexRepresentativeCover N :=
  IndexedPredictorFamily.finiteIndexRepresentativeCover_of_factorsThrough_of_rightInverse
    hfactor hsection hrep

/-- Route-coverage anchor: finite quotient-code presentations pull back across
an explicit factor map. -/
theorem kpolyCoverage_anchor_finitePredictorQuotient_of_factorsThrough
    {Index Input View : Type*} {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View} {view : Input → View} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hquot : H.FinitePredictorQuotient N) :
    G.FinitePredictorQuotient N :=
  IndexedPredictorFamily.finitePredictorQuotient_of_factorsThrough
    hfactor hquot

/-- Route-coverage anchor: when a factor map has a section, finite
quotient-code presentations push back to the summary family. -/
theorem kpolyCoverage_anchor_finitePredictorQuotient_of_factorsThrough_of_rightInverse
    {Index Input View : Type*} {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View} {view : Input → View}
    {sec : View → Input} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hquot : G.FinitePredictorQuotient N) :
    H.FinitePredictorQuotient N :=
  IndexedPredictorFamily.finitePredictorQuotient_of_factorsThrough_of_rightInverse
    hfactor hsection hquot

/-- Route-coverage anchor: a section-backed factorization through a finite
summary inherits the full Boolean classifier-space lower bound from a
surjective summary family. -/
theorem kpolyCoverage_anchor_not_finitePredictorCover_of_factorsThrough_of_rightInverse
    {Index Input View : Type*} [Fintype View]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (hN : N < 2 ^ Fintype.card View)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hsurj : Function.Surjective H.predict) :
    ¬ G.FinitePredictorCover N :=
  IndexedPredictorFamily.not_finitePredictorCover_of_factorsThrough_of_rightInverse_of_surjective_predict
    hN hfactor hsection hsurj

/-- Route-coverage anchor: representative-index covers inherit the same
section-backed reduced-view obstruction. -/
theorem kpolyCoverage_anchor_not_finiteIndexRepresentativeCover_of_factorsThrough_of_rightInverse
    {Index Input View : Type*} [Fintype View]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (hN : N < 2 ^ Fintype.card View)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hsurj : Function.Surjective H.predict) :
    ¬ G.FiniteIndexRepresentativeCover N :=
  IndexedPredictorFamily.not_finiteIndexRepresentativeCover_of_factorsThrough_of_rightInverse_of_surjective_predict
    hN hfactor hsection hsurj

/-- Route-coverage anchor: quotient-code presentations inherit the same
section-backed reduced-view obstruction. -/
theorem kpolyCoverage_anchor_not_finitePredictorQuotient_of_factorsThrough_of_rightInverse
    {Index Input View : Type*} [Fintype View]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (hN : N < 2 ^ Fintype.card View)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hsurj : Function.Surjective H.predict) :
    ¬ G.FinitePredictorQuotient N :=
  IndexedPredictorFamily.not_finitePredictorQuotient_of_factorsThrough_of_rightInverse_of_surjective_predict
    hN hfactor hsection hsurj

/-- Route-coverage anchor: finite predictor-image covers cannot rescue an
exact family that factors through `(a,b)` when the reduced family is still
fully expressive and the cover is below the reduced Boolean classifier-space
cardinality. -/
theorem kpolyCoverage_anchor_not_finitePredictorCover_of_factorsThrough_ab_and_surjective_predict
    {Z : Type*} [Inhabited Z] {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index} {N : ℕ}
    (hN : N < 2 ^ Fintype.card (ABVisibleSurface k))
    (hfactor : G.FactorsThrough abVisibleData H)
    (hsurj : Function.Surjective H.predict) :
    ¬ G.FinitePredictorCover N :=
  not_finitePredictorCover_of_factorsThrough_ab_and_surjective_predict
    hN hfactor hsurj

/-- Route-coverage anchor: finite predictor-image covers of an exact family
factoring through `(a,b)` inherit every injective finite-probe lower bound
already present on the reduced `(a,b)` view. -/
theorem kpolyCoverage_anchor_abVisible_finitePredictorCover_card_le_of_factorsThrough_of_injective_realization
    {Z Probe : Type*} [Inhabited Z] [Fintype Probe]
    {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index} {N : ℕ}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hfactor : G.FactorsThrough abVisibleData H)
    (hcover : G.FinitePredictorCover N) :
    Fintype.card Probe ≤ N :=
  abVisible_finitePredictorCover_card_le_of_factorsThrough_of_injective_realization
    target hinj hreal hfactor hcover

/-- Route-coverage anchor: exact visible compression is impossible below any
injective finite-probe family already realized by the reduced `(a,b)` view. -/
theorem kpolyCoverage_anchor_not_exactVisibleCompressionTarget_of_factorsThrough_ab_and_injective_realization_of_lt_card
    {Z Probe : Type*} [Inhabited Z] [Fintype Probe]
    {k s : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hs : 2 ^ s < Fintype.card Probe)
    (hfactor : G.FactorsThrough abVisibleData H) :
    ¬ ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s :=
  not_exactVisibleCompressionTarget_of_factorsThrough_ab_and_injective_realization_of_lt_card
    target hinj hreal hs hfactor

/-- Route-coverage anchor: representative-index covers have the same reduced
`(a,b)` pullback obstruction. -/
theorem kpolyCoverage_anchor_not_finiteIndexRepresentativeCover_of_factorsThrough_ab_and_surjective_predict
    {Z : Type*} [Inhabited Z] {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index} {N : ℕ}
    (hN : N < 2 ^ Fintype.card (ABVisibleSurface k))
    (hfactor : G.FactorsThrough abVisibleData H)
    (hsurj : Function.Surjective H.predict) :
    ¬ G.FiniteIndexRepresentativeCover N :=
  not_finiteIndexRepresentativeCover_of_factorsThrough_ab_and_surjective_predict
    hN hfactor hsurj

/-- Route-coverage anchor: representative-index covers have the same reduced
`(a,b)` finite-probe pullback obstruction. -/
theorem kpolyCoverage_anchor_abVisible_finiteIndexRepresentativeCover_card_le_of_factorsThrough_of_injective_realization
    {Z Probe : Type*} [Inhabited Z] [Fintype Probe]
    {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index} {N : ℕ}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hfactor : G.FactorsThrough abVisibleData H)
    (hrep : G.FiniteIndexRepresentativeCover N) :
    Fintype.card Probe ≤ N :=
  abVisible_finiteIndexRepresentativeCover_card_le_of_factorsThrough_of_injective_realization
    target hinj hreal hfactor hrep

/-- Route-coverage anchor: quotient-code presentations have the same reduced
`(a,b)` pullback obstruction. -/
theorem kpolyCoverage_anchor_not_finitePredictorQuotient_of_factorsThrough_ab_and_surjective_predict
    {Z : Type*} [Inhabited Z] {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index} {N : ℕ}
    (hN : N < 2 ^ Fintype.card (ABVisibleSurface k))
    (hfactor : G.FactorsThrough abVisibleData H)
    (hsurj : Function.Surjective H.predict) :
    ¬ G.FinitePredictorQuotient N :=
  not_finitePredictorQuotient_of_factorsThrough_ab_and_surjective_predict
    hN hfactor hsurj

/-- Route-coverage anchor: quotient-code presentations have the same reduced
`(a,b)` finite-probe pullback obstruction. -/
theorem kpolyCoverage_anchor_abVisible_finitePredictorQuotient_card_le_of_factorsThrough_of_injective_realization
    {Z Probe : Type*} [Inhabited Z] [Fintype Probe]
    {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index} {N : ℕ}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hfactor : G.FactorsThrough abVisibleData H)
    (hquot : G.FinitePredictorQuotient N) :
    Fintype.card Probe ≤ N :=
  abVisible_finitePredictorQuotient_card_le_of_factorsThrough_of_injective_realization
    target hinj hreal hfactor hquot

/-- Route-coverage anchor: clocked exact-visible realization is impossible
below any injective finite-probe family already realized by the reduced
`(a,b)` view. -/
theorem kpolyCoverage_anchor_not_clockedRealization_of_factorsThrough_ab_and_injective_realization_of_lt_card
    {Z Probe : Type*} [Inhabited Z] [Fintype Probe]
    {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hs : 2 ^ s < Fintype.card Probe)
    (hfactor : G.FactorsThrough abVisibleData H) :
    ¬ ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F :=
  not_exists_clockedExactVisibleRealization_of_factorsThrough_ab_and_injective_realization_of_lt_card
    target hinj hreal hs hfactor

/-- Route-coverage anchor: a fully expressive finite indexed family cannot have
a finite predictor-image cover smaller than the full Boolean classifier space. -/
theorem kpolyCoverage_anchor_finitePredictorCover_card_le_of_surjective_predict
    {Index Input : Type*} [Fintype Input]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (hsurj : Function.Surjective G.predict)
    (hcover : G.FinitePredictorCover N) :
    2 ^ Fintype.card Input ≤ N :=
  IndexedPredictorFamily.finitePredictorCover_card_le_of_surjective_predict
    hsurj hcover

/-- Route-coverage anchor: finite predictor-image covers must be at least as
large as any injectively indexed finite probe family already realized by the
indexed predictors. -/
theorem kpolyCoverage_anchor_finitePredictorCover_card_le_of_injective_realization
    {Probe Index Input : Type*} [Fintype Probe]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (target : Probe → Input → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hcover : G.FinitePredictorCover N) :
    Fintype.card Probe ≤ N :=
  IndexedPredictorFamily.finitePredictorCover_card_le_of_injective_realization
    target hinj hreal hcover

/-- Route-coverage anchor: representative-index covers have the same finite
probe lower bound. -/
theorem kpolyCoverage_anchor_finiteIndexRepresentativeCover_card_le_of_injective_realization
    {Probe Index Input : Type*} [Fintype Probe]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (target : Probe → Input → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hrep : G.FiniteIndexRepresentativeCover N) :
    Fintype.card Probe ≤ N :=
  IndexedPredictorFamily.finiteIndexRepresentativeCover_card_le_of_injective_realization
    target hinj hreal hrep

/-- Route-coverage anchor: quotient-code presentations have the same finite
probe lower bound. -/
theorem kpolyCoverage_anchor_finitePredictorQuotient_card_le_of_injective_realization
    {Probe Index Input : Type*} [Fintype Probe]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (target : Probe → Input → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hquot : G.FinitePredictorQuotient N) :
    Fintype.card Probe ≤ N :=
  IndexedPredictorFamily.finitePredictorQuotient_card_le_of_injective_realization
    target hinj hreal hquot

/-- Route-coverage anchor: if an indexed family factors through a section-backed
reduced view, finite predictor-image covers inherit every injective finite-probe
lower bound already present on that reduced view. -/
theorem kpolyCoverage_anchor_finitePredictorCover_card_le_of_factorsThrough_of_rightInverse_of_injective_realization
    {Probe Index Input View : Type*} [Fintype Probe]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (target : Probe → View → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hcover : G.FinitePredictorCover N) :
    Fintype.card Probe ≤ N :=
  IndexedPredictorFamily.finitePredictorCover_card_le_of_factorsThrough_of_rightInverse_of_injective_realization
    target hinj hreal hfactor hsection hcover

/-- Route-coverage anchor: the section-backed finite-probe pullback lower bound
has the same negative form for finite predictor-image covers. -/
theorem kpolyCoverage_anchor_not_finitePredictorCover_of_factorsThrough_of_rightInverse_of_injective_realization_of_lt_card
    {Probe Index Input View : Type*} [Fintype Probe]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (target : Probe → View → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hN : N < Fintype.card Probe)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view) :
    ¬ G.FinitePredictorCover N :=
  IndexedPredictorFamily.not_finitePredictorCover_of_factorsThrough_of_rightInverse_of_injective_realization_of_lt_card
    target hinj hreal hN hfactor hsection

/-- Route-coverage anchor: representative-index covers inherit the same
section-backed finite-probe lower bound. -/
theorem kpolyCoverage_anchor_finiteIndexRepresentativeCover_card_le_of_factorsThrough_of_rightInverse_of_injective_realization
    {Probe Index Input View : Type*} [Fintype Probe]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (target : Probe → View → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hrep : G.FiniteIndexRepresentativeCover N) :
    Fintype.card Probe ≤ N :=
  IndexedPredictorFamily.finiteIndexRepresentativeCover_card_le_of_factorsThrough_of_rightInverse_of_injective_realization
    target hinj hreal hfactor hsection hrep

/-- Route-coverage anchor: the section-backed finite-probe pullback lower bound
has the same negative form for representative-index covers. -/
theorem kpolyCoverage_anchor_not_finiteIndexRepresentativeCover_of_factorsThrough_of_rightInverse_of_injective_realization_of_lt_card
    {Probe Index Input View : Type*} [Fintype Probe]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (target : Probe → View → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hN : N < Fintype.card Probe)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view) :
    ¬ G.FiniteIndexRepresentativeCover N :=
  IndexedPredictorFamily.not_finiteIndexRepresentativeCover_of_factorsThrough_of_rightInverse_of_injective_realization_of_lt_card
    target hinj hreal hN hfactor hsection

/-- Route-coverage anchor: quotient-code presentations inherit the same
section-backed finite-probe lower bound. -/
theorem kpolyCoverage_anchor_finitePredictorQuotient_card_le_of_factorsThrough_of_rightInverse_of_injective_realization
    {Probe Index Input View : Type*} [Fintype Probe]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (target : Probe → View → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hquot : G.FinitePredictorQuotient N) :
    Fintype.card Probe ≤ N :=
  IndexedPredictorFamily.finitePredictorQuotient_card_le_of_factorsThrough_of_rightInverse_of_injective_realization
    target hinj hreal hfactor hsection hquot

/-- Route-coverage anchor: the section-backed finite-probe pullback lower bound
has the same negative form for quotient-code presentations. -/
theorem kpolyCoverage_anchor_not_finitePredictorQuotient_of_factorsThrough_of_rightInverse_of_injective_realization_of_lt_card
    {Probe Index Input View : Type*} [Fintype Probe]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (target : Probe → View → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hN : N < Fintype.card Probe)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view) :
    ¬ G.FinitePredictorQuotient N :=
  IndexedPredictorFamily.not_finitePredictorQuotient_of_factorsThrough_of_rightInverse_of_injective_realization_of_lt_card
    target hinj hreal hN hfactor hsection

/-- Route-coverage anchor: a fully expressive exact visible family has no finite
predictor-image cover below the full exact visible Boolean classifier space. -/
theorem kpolyCoverage_anchor_not_exactVisible_finitePredictorCover_of_surjective_predict
    {Z : Type*} [Fintype Z] {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} {N : ℕ}
    (hN : N < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k))
    (hsurj : Function.Surjective G.predict) :
    ¬ G.FinitePredictorCover N :=
  not_exactVisible_finitePredictorCover_of_surjective_predict hN hsurj

/-- Route-coverage anchor: a fully expressive exact visible family has no finite
representative-index cover below the full exact visible Boolean classifier
space. -/
theorem kpolyCoverage_anchor_not_exactVisible_finiteIndexRepresentativeCover_of_surjective_predict
    {Z : Type*} [Fintype Z] {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} {N : ℕ}
    (hN : N < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k))
    (hsurj : Function.Surjective G.predict) :
    ¬ G.FiniteIndexRepresentativeCover N :=
  not_exactVisible_finiteIndexRepresentativeCover_of_surjective_predict hN hsurj

/-- Route-coverage anchor: a fully expressive exact visible family has no finite
quotient-code presentation below the full exact visible Boolean classifier
space. -/
theorem kpolyCoverage_anchor_not_exactVisible_finitePredictorQuotient_of_surjective_predict
    {Z : Type*} [Fintype Z] {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} {N : ℕ}
    (hN : N < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k))
    (hsurj : Function.Surjective G.predict) :
    ¬ G.FinitePredictorQuotient N :=
  not_exactVisible_finitePredictorQuotient_of_surjective_predict hN hsurj

/-- Route-coverage anchor: the clocked exact-visible realization target is
impossible below the full predictor-image cardinality for a fully expressive
exact visible family. -/
theorem kpolyCoverage_anchor_not_clockedRealization_of_surjective_predict_of_lt_predictorCard
    {Z : Type*} [Fintype Z] {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hs : 2 ^ s < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k))
    (hsurj : Function.Surjective G.predict) :
    ¬ ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F :=
  not_exists_clockedExactVisibleRealization_of_surjective_predict_of_lt_predictorCard
    hs hsurj

/-- Route-coverage anchor: the same surjectivity obstruction refutes the full
clocked finite-learning payload below the full predictor-image cardinality. -/
theorem kpolyCoverage_anchor_not_clockedFiniteLearningPayload_of_surjective_predict_of_lt_predictorCard
    {Z : Type*} [Fintype Z] {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hs : 2 ^ s < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k))
    (hsurj : Function.Surjective G.predict) :
    ¬ ClockedKpolyFiniteLearningPayload G s clock :=
  not_clockedKpolyFiniteLearningPayload_of_surjective_predict_of_lt_predictorCard
    hs hsurj

/-- Route-coverage anchor: exact visible compression is impossible below the
size of any injectively indexed finite probe family already realized by the
switched predictors. -/
theorem kpolyCoverage_anchor_not_exactVisibleCompressionTarget_of_injective_realization_of_lt_card
    {Probe Z : Type*} [Fintype Probe] {k s : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hs : 2 ^ s < Fintype.card Probe) :
    ¬ ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s :=
  not_exactVisibleCompressionTarget_of_injective_realization_of_lt_card
    target hinj hreal hs

/-- Route-coverage anchor: the same finite-probe lower bound refutes clocked
exact-visible realization below the probe cardinality. -/
theorem kpolyCoverage_anchor_not_clockedRealization_of_injective_realization_of_lt_card
    {Probe Z : Type*} [Fintype Probe] {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hs : 2 ^ s < Fintype.card Probe) :
    ¬ ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F :=
  not_exists_clockedExactVisibleRealization_of_injective_realization_of_lt_card
    target hinj hreal hs

/-- Route-coverage anchor: finite-probe lower bounds also refute the bundled
clocked finite-learning payload below the probe cardinality. -/
theorem kpolyCoverage_anchor_not_clockedFiniteLearningPayload_of_injective_realization_of_lt_card
    {Probe Z : Type*} [Fintype Probe] [Fintype Z] {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hs : 2 ^ s < Fintype.card Probe) :
    ¬ ClockedKpolyFiniteLearningPayload G s clock :=
  not_clockedKpolyFiniteLearningPayload_of_injective_realization_of_lt_card
    target hinj hreal hs

/-- Route-coverage anchor: balanced finite-coin fibers are exactly output
predicate erasure. -/
theorem finiteCoinCoverage_anchor_predicateErasure
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) :
    FiniteCoinRecodingFiberBalanced r ↔ FiniteCoinOutputPredicateErasing r :=
  finiteCoinRecodingFiberBalanced_iff_outputPredicateErasing r

/-- Route-coverage anchor: balanced finite-coin fibers force every Boolean
output decoder to be exactly half-accurate. -/
theorem finiteCoinCoverage_anchor_decoderHalfAccuracy
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (decode : α → Bool)
    (hbal : FiniteCoinRecodingFiberBalanced r) :
    finiteCoinOutputDecoderHalfAccurate r decode :=
  finiteCoinOutputDecoderHalfAccurate_of_fiberBalanced r decode hbal

/-- Route-coverage anchor: each finite-coin output fiber's symmetric defect is
the scaled true/false fiber imbalance. -/
theorem finiteCoinCoverage_anchor_exactScaledFiberImbalance
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (y : α) :
    countIndependentWithinDefect (Ω := Bool × Coin)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (fun ω => finiteCoinOutput r ω = y) =
      Fintype.card Coin * finiteCoinFiberImbalance r y :=
  countIndependentWithinDefect_finiteCoinOutput_fiber r y

/-- Route-coverage anchor: below one coin block of tolerance, approximate
finite-coin output independence is exact balanced-fiber erasure. -/
theorem finiteCoinCoverage_anchor_subCardinalityToleranceQuantization
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) {τ : Nat}
    (hlt : τ < Fintype.card Coin) :
    CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput r) τ ↔
    FiniteCoinRecodingFiberBalanced r :=
  countIndependentWithinToleranceOutput_finiteCoinOutput_lt_card_iff_fiberBalanced
    r hlt

/-- Route-coverage anchor: deterministic output postprocessing preserves exact
balanced-fiber erasure. -/
theorem finiteCoinCoverage_anchor_deterministicOutputPostprocessing
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hbal : FiniteCoinRecodingFiberBalanced r) :
    FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)) :=
  finiteCoinRecodingFiberBalanced_postcompose r g hbal

/-- Route-coverage anchor: lossless deterministic output postprocessing cannot
create finite-coin erasure.  Balanced fibers after an injective postprocessor
are equivalent to balanced fibers before that postprocessor. -/
theorem finiteCoinCoverage_anchor_injectivePostprocessingErasureEquivalence
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hinj : Function.Injective g) :
    FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)) ↔
      FiniteCoinRecodingFiberBalanced r :=
  finiteCoinRecodingFiberBalanced_postcompose_iff_of_injective r g hinj

/-- Route-coverage anchor: even a many-to-one postprocessor cannot create
finite-coin erasure if the original output is recoverable from the
postprocessed value on every observed true/false coin sample. -/
theorem finiteCoinCoverage_anchor_observedLeftInversePostprocessingErasureEquivalence
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) (recover : β → α)
    (hrecover : ∀ b c, recover (g (r b c)) = r b c) :
    FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)) ↔
      FiniteCoinRecodingFiberBalanced r :=
  finiteCoinRecodingFiberBalanced_postcompose_iff_of_observedLeftInverse
    r g recover hrecover

/-- Route-coverage anchor: a deterministic postprocessor that is injective on
the actually observed finite-coin support cannot create finite-coin erasure. -/
theorem finiteCoinCoverage_anchor_observedInjectivePostprocessingErasureEquivalence
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hinjObs :
      ∀ b1 c1 b2 c2,
        g (r b1 c1) = g (r b2 c2) → r b1 c1 = r b2 c2) :
    FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)) ↔
      FiniteCoinRecodingFiberBalanced r :=
  finiteCoinRecodingFiberBalanced_postcompose_iff_of_observedInjective
    r g hinjObs

/-- Route-coverage anchor: if deterministic postprocessing balances an
originally unbalanced finite-coin recoding, then two distinct observed original
outputs must collide under the postprocessor. -/
theorem finiteCoinCoverage_anchor_postprocessingObservedOutputCollisionObligation
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hbal : FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)))
    (hnot : ¬ FiniteCoinRecodingFiberBalanced r) :
    ∃ b1 : Bool, ∃ c1 : Coin, ∃ b2 : Bool, ∃ c2 : Coin,
      r b1 c1 ≠ r b2 c2 ∧ g (r b1 c1) = g (r b2 c2) :=
  exists_observedOutput_collision_of_postcompose_fiberBalanced_of_not_fiberBalanced
    r g hbal hnot

/-- Route-coverage anchor: if deterministic postprocessing balances an
originally unbalanced finite-coin recoding, then one postprocessed fiber must
merge an original true-heavy output with an original false-heavy output. -/
theorem finiteCoinCoverage_anchor_postprocessingObservedOppositeBiasCollisionObligation
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hbal : FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)))
    (hnot : ¬ FiniteCoinRecodingFiberBalanced r) :
    ∃ yTrue yFalse : α,
      g yTrue = g yFalse ∧ yTrue ≠ yFalse ∧
        coinFalseFiberCount r yTrue < coinTrueFiberCount r yTrue ∧
          coinTrueFiberCount r yFalse < coinFalseFiberCount r yFalse :=
  exists_oppositeBias_observedOutput_collision_of_postcompose_fiberBalanced_of_not_fiberBalanced
    r g hbal hnot

/-- Route-coverage anchor: balanced deterministic postprocessing is equivalent
to exact zero total signed original bias in every postprocessed fiber. -/
theorem finiteCoinCoverage_anchor_postprocessingSignedBiasCancellationCertificate
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) :
    FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)) ↔
      ∀ z : β,
        (∑ y ∈ finiteOutputPreimageFiber g z,
          finiteCoinSignedFiberBias r y) = 0 :=
  finiteCoinRecodingFiberBalanced_postcompose_iff_forall_sum_signedFiberBias_preimage_eq_zero
    r g

/-- Route-coverage anchor: deterministic finite-output postprocessing has
explicit finite-preimage tolerance blowup `τ ↦ m * τ`. -/
theorem finiteCoinCoverage_anchor_finitePreimagePostprocessingBlowup
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) {m τ : Nat}
    (hbound : finiteOutputMapFiberCardBound g m)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput r) τ) :
    CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput (fun b c => g (r b c))) (m * τ) :=
  countIndependentWithinToleranceOutput_finiteCoinOutput_postcompose
    r g hbound happrox

/-- Route-coverage anchor: if a retained-side output is deterministically
postprocessed, then below one lower-bounded source/coin block approximate
output independence is equivalent to exact true/false balance in every
observed postprocessed fiber. -/
theorem finiteCoinCoverage_anchor_postprocessedSideToleranceObservedFiberBalance
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ ↔
    ∀ z : β,
      finiteEventCount Coin (fun c => post (r true c, side c) = z) =
        finiteEventCount Coin (fun c => post (r false c, side c) = z) :=
  countIndependentWithinToleranceOutput_postprocessedSide_sourceLowerBounds_lt_coinProduct_iff_observedFiber_count_eq
    C E r side post htrue hfalse hlt

/-- Route-coverage anchor: after deterministic postprocessing of a retained-side
output, approximate output independence can only tolerate observed fibers whose
true/false residual imbalances fit inside the explicit source/coin budget. -/
theorem finiteCoinCoverage_anchor_postprocessedSideObservedFiberImbalanceLowerBound
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    (∀ z : β,
      loTrue * loFalse * Fintype.card Coin *
          (finiteEventCount Coin (fun c => post (r true c, side c) = z) -
            finiteEventCount Coin (fun c => post (r false c, side c) = z)) ≤ τ) ∧
    (∀ z : β,
      loTrue * loFalse * Fintype.card Coin *
          (finiteEventCount Coin (fun c => post (r false c, side c) = z) -
            finiteEventCount Coin (fun c => post (r true c, side c) = z)) ≤ τ) :=
  sourceLowerBounds_observedFiberImbalanceProducts_le_of_CountIndependentWithinToleranceOutput_postprocessedSide
    C E r side post τ loTrue loFalse htrue hfalse happrox

/-- Route-coverage anchor: below one lower-bounded source/coin block, no
decidable predicate downstream of deterministic retained-side postprocessing can
have a source-side count advantage. -/
theorem finiteCoinCoverage_anchor_postprocessedSidePredicateErasure
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (P : β → Prop) [DecidablePred P] {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    finiteEventCount Coin (fun c => P (post (r true c, side c))) =
      finiteEventCount Coin (fun c => P (post (r false c, side c))) :=
  postprocessedSide_outputPredicate_count_eq_of_countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct
    C E r side post P htrue hfalse hlt happrox

/-- Route-coverage anchor: below one lower-bounded source/coin block, no
Boolean decoder downstream of deterministic retained-side postprocessing can
achieve better-than-half aggregate accuracy. -/
theorem finiteCoinCoverage_anchor_postprocessedSideDecoderHalfAccuracy
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (decode : β → Bool) {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    finiteEventCount Coin (fun c => decode (post (r true c, side c)) = true) +
      finiteEventCount Coin (fun c => decode (post (r false c, side c)) = false) =
        Fintype.card Coin :=
  postprocessedSide_outputDecoder_correctCount_eq_card_of_countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct
    C E r side post decode htrue hfalse hlt happrox

/-- Route-coverage anchor: below one lower-bounded source/coin block, a
downstream Boolean decoder cannot uniformly recover the source bit after
deterministic retained-side postprocessing. -/
theorem finiteCoinCoverage_anchor_postprocessedSideSourceRecoveryBlock
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [Nonempty Coin]
    [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (decode : β → Bool) {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (hdecodeTrue : ∀ c : Coin, decode (post (r true c, side c)) = true)
    (hdecodeFalse : ∀ c : Coin, decode (post (r false c, side c)) = false) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ :=
  not_countIndependentWithinToleranceOutput_of_postprocessedSide_outputDecoder_recovers_sourceLowerBounds_lt_coinProduct
    C E r side post decode htrue hfalse hlt hdecodeTrue hdecodeFalse

/-- Route-coverage anchor: below one lower-bounded source/coin block,
deterministic retained-side postprocessing must create true/false observed
support overlap if approximate output independence is to hold. -/
theorem finiteCoinCoverage_anchor_postprocessedSideCollisionObligation
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [Nonempty Coin]
    [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    ∃ cTrue cFalse : Coin,
      post (r true cTrue, side cTrue) = post (r false cFalse, side cFalse) :=
  exists_postprocessedSide_true_false_collision_of_countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct
    C E r side post htrue hfalse hlt happrox

/-- Route-coverage anchor: below one lower-bounded source/coin block,
deterministic retained-side postprocessing must give every observed coin value
witnesses on both source sides if approximate output independence is to hold. -/
theorem finiteCoinCoverage_anchor_postprocessedSidePointwiseCollisionObligation
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    (∀ cTrue : Coin,
        ∃ cFalse : Coin,
          post (r true cTrue, side cTrue) = post (r false cFalse, side cFalse)) ∧
      (∀ cFalse : Coin,
        ∃ cTrue : Coin,
          post (r true cTrue, side cTrue) =
            post (r false cFalse, side cFalse)) :=
  postprocessedSide_pointwise_true_false_collisions_of_countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct
    C E r side post htrue hfalse hlt happrox

/-- Route-coverage anchor: two-sided pointwise support collisions are strictly
weaker than a preserving postprocessed-side coin equivalence.  The three-coin
audit instance has support overlap in both directions but no bijective
observation-preserving matching. -/
theorem finiteCoinCoverage_anchor_postprocessedSidePointwiseCollisionInsufficient :
    ∃ r : Bool → Fin 3 → Bool,
    ∃ side : Fin 3 → Unit,
    ∃ post : Bool × Unit → Bool,
      ((∀ cTrue : Fin 3,
          ∃ cFalse : Fin 3,
            post (r true cTrue, side cTrue) =
              post (r false cFalse, side cFalse)) ∧
        (∀ cFalse : Fin 3,
          ∃ cTrue : Fin 3,
            post (r true cTrue, side cTrue) =
              post (r false cFalse, side cFalse))) ∧
        ¬ ∃ e : Fin 3 ≃ Fin 3,
          ∀ c : Fin 3,
            post (r true c, side c) = post (r false (e c), side (e c)) :=
  postprocessedSide_pointwise_collisions_do_not_imply_coinEquiv_preserving

/-- Route-coverage anchor: one-sided true-to-false witness maps are still
weaker than a preserving postprocessed-side coin equivalence.  In the
three-coin audit instance, such maps exist, but every preserving one-sided map
is non-injective and therefore cannot be promoted to a bijective matching. -/
theorem finiteCoinCoverage_anchor_postprocessedSideOneSidedCoinMapInsufficient :
    ∃ r : Bool → Fin 3 → Bool,
    ∃ side : Fin 3 → Unit,
    ∃ post : Bool × Unit → Bool,
      (∃ f : Fin 3 → Fin 3,
        ∀ c : Fin 3,
          post (r true c, side c) = post (r false (f c), side (f c))) ∧
        (∀ f : Fin 3 → Fin 3,
          (∀ c : Fin 3,
            post (r true c, side c) = post (r false (f c), side (f c))) →
            ¬ Function.Injective f) ∧
          ¬ ∃ e : Fin 3 ≃ Fin 3,
            ∀ c : Fin 3,
              post (r true c, side c) = post (r false (e c), side (e c)) :=
  postprocessedSide_oneSided_coinMap_preserving_does_not_imply_coinEquiv_preserving

/-- Route-coverage anchor: the injective one-sided witness-map repair is not a
new intermediate target.  For finite coins it is equivalent to the preserving
postprocessed-side coin equivalence, and with decidable observed outputs it is
therefore the same observed-fiber multiplicity-balance obligation. -/
theorem finiteCoinCoverage_anchor_postprocessedSideInjectiveWitnessMapEquivalence
    {Coin α Side β : Type*} [Fintype Coin] [DecidableEq β]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β) :
    ((∃ f : Coin → Coin,
      (∀ c : Coin,
        post (r true c, side c) = post (r false (f c), side (f c))) ∧
        Function.Injective f) ↔
      ∃ e : Coin ≃ Coin,
        ∀ c : Coin,
          post (r true c, side c) = post (r false (e c), side (e c))) ∧
      ((∃ f : Coin → Coin,
        (∀ c : Coin,
          post (r true c, side c) = post (r false (f c), side (f c))) ∧
          Function.Injective f) ↔
        ∀ z : β,
          finiteEventCount Coin (fun c => post (r true c, side c) = z) =
            finiteEventCount Coin (fun c => post (r false c, side c) = z)) := by
  exact
    ⟨exists_injective_postprocessedSide_coinMap_preserving_iff_exists_coinEquiv_preserving
      r side post,
    exists_injective_postprocessedSide_coinMap_preserving_iff_observedFiber_count_eq
      r side post⟩

/-- Route-coverage anchor: below one lower-bounded source/coin block,
deterministic retained-side postprocessing must provide a bijective matching of
true-side and false-side coin choices preserving every observed value if
approximate output independence is to hold. -/
theorem finiteCoinCoverage_anchor_postprocessedSideCoinMatchingObligation
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    ∃ e : Coin ≃ Coin,
      ∀ c : Coin,
        post (r true c, side c) = post (r false (e c), side (e c)) :=
  exists_postprocessedSide_coinEquiv_preserving_of_countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct
    C E r side post htrue hfalse hlt happrox

/-- Route-coverage anchor: a single observed postprocessed value with unequal
true-side and false-side coin-fiber multiplicities blocks the coin-matching
repair, hence also blocks below-threshold approximate independence for
deterministic retained-side postprocessing. -/
theorem finiteCoinCoverage_anchor_postprocessedSideCoinMatchingCardinalityBlock
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (z : β) {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (hne :
      finiteEventCount Coin (fun c => post (r true c, side c) = z) ≠
        finiteEventCount Coin (fun c => post (r false c, side c) = z)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ :=
  not_countIndependentWithinToleranceOutput_of_postprocessedSide_observedFiber_count_ne_sourceLowerBounds_lt_coinProduct
    C E r side post z htrue hfalse hlt hne

/-- Route-coverage anchor: a downstream predicate with unequal true-side and
false-side coin counts blocks the postprocessed-side coin-matching repair,
hence also blocks below-threshold approximate independence for deterministic
retained-side postprocessing.  Decoder-only probes are a special case of this
predicate obstruction. -/
theorem finiteCoinCoverage_anchor_postprocessedSideCoinMatchingPredicateBlock
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (P : β → Prop) [DecidablePred P] {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (hne :
      finiteEventCount Coin (fun c => P (post (r true c, side c))) ≠
        finiteEventCount Coin (fun c => P (post (r false c, side c)))) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ :=
  not_countIndependentWithinToleranceOutput_of_postprocessedSide_outputPredicate_count_ne_sourceLowerBounds_lt_coinProduct
    C E r side post P htrue hfalse hlt hne

/-- Route-coverage anchor: all downstream decidable predicates are neutral
exactly when the postprocessed retained-side observations support a preserving
true/false coin equivalence.  Predicate-only certificates therefore do not
avoid the full observed-fiber matching obligation. -/
theorem finiteCoinCoverage_anchor_postprocessedSidePredicateMatchingEquivalence
    {Coin α Side β : Type*} [Fintype Coin] [DecidableEq β]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β) :
    (∃ e : Coin ≃ Coin,
      ∀ c : Coin,
        post (r true c, side c) = post (r false (e c), side (e c))) ↔
      ∀ P : β → Prop, [DecidablePred P] →
        finiteEventCount Coin (fun c => P (post (r true c, side c))) =
          finiteEventCount Coin (fun c => P (post (r false c, side c))) :=
  exists_postprocessedSide_coinEquiv_preserving_iff_outputPredicate_count_eq
    r side post

/-- Route-coverage anchor: below one lower-bounded source/coin block,
postprocessed retained-side approximate independence is exactly the existence
of a preserving true/false coin equivalence.  A repair cannot certify the
independence condition while leaving the finite matching obligation unsolved. -/
theorem finiteCoinCoverage_anchor_postprocessedSideApproxIndependenceCoinMatchingEquivalence
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ ↔
      ∃ e : Coin ≃ Coin,
        ∀ c : Coin,
          post (r true c, side c) = post (r false (e c), side (e c)) :=
  countIndependentWithinToleranceOutput_postprocessedSide_sourceLowerBounds_lt_coinProduct_iff_coinEquiv_preserving
    C E r side post htrue hfalse hlt

/-- Route-coverage anchor: source-side nondegeneracy rules out zero-tolerance
approximate output independence for a nonempty finite-coin recoding with a
uniform true-side distinguishing fiber. -/
theorem finiteCoinCoverage_anchor_coinwiseTrueFiber_sourceNonconstant_zeroBlock
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [Nonempty Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α)
    (htrue : ∀ c : Coin, r true c = y)
    (hfalse : ∀ c : Coin, r false c ≠ y)
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) 0 :=
  not_countIndependentWithinToleranceOutput_zero_of_coinwise_trueFiber_sourceNonconstant
    C E r y htrue hfalse hpos hneg

/-- Route-coverage anchor: source-side nondegeneracy rules out zero-tolerance
approximate output independence for a nonempty finite-coin recoding with a
uniform false-side distinguishing fiber. -/
theorem finiteCoinCoverage_anchor_coinwiseFalseFiber_sourceNonconstant_zeroBlock
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [Nonempty Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α)
    (htrue : ∀ c : Coin, r true c ≠ y)
    (hfalse : ∀ c : Coin, r false c = y)
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) 0 :=
  not_countIndependentWithinToleranceOutput_zero_of_coinwise_falseFiber_sourceNonconstant
    C E r y htrue hfalse hpos hneg

/-- Route-coverage anchor: on any source-side nondegenerate conditioned
surface, zero-tolerance finite-coin output independence is exactly balanced
true/false output fibers. -/
theorem finiteCoinCoverage_anchor_sourceNonconstantZeroIffBalanced
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [Nonempty Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α)
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) 0 ↔
    FiniteCoinRecodingFiberBalanced r :=
  countIndependentWithinToleranceOutput_zero_iff_finiteCoinRecoding_fiberBalanced_of_sourceNonconstant
    C E r hpos hneg

/-- Route-coverage anchor: below one lower-bounded source/coin imbalance
block, finite-coin approximate output independence is already equivalent to
balanced true/false output fibers. -/
theorem finiteCoinCoverage_anchor_sourceLowerBoundToleranceQuantization
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ ↔
    FiniteCoinRecodingFiberBalanced r :=
  countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct_iff_finiteCoinRecoding_fiberBalanced
    C E r htrue hfalse hlt

/-- Route-coverage anchor: if the random coin is retained in the certified
output, then below one lower-bounded source/coin block, approximate output
independence is equivalent to pointwise source-blindness at every coin. -/
theorem finiteCoinCoverage_anchor_retainedCoinTolerancePointwiseCollapse
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, xr.2)) τ ↔
    ∀ c : Coin, r true c = r false c :=
  countIndependentWithinToleranceOutput_coinRetained_sourceLowerBounds_lt_coinProduct_iff_pointwise_eq
    C E r htrue hfalse hlt

/-- Route-coverage anchor: if side information is retained in the certified
output, then below one lower-bounded source/coin block, approximate output
independence is equivalent to exact true/false balance inside every retained
side/output fiber. -/
theorem finiteCoinCoverage_anchor_retainedSideToleranceSideFiberBalance
    {Ω Coin α Side : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    [DecidableEq Side]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, side xr.2)) τ ↔
    ∀ (y : α) (s : Side),
      finiteEventCount Coin (fun c => r true c = y ∧ side c = s) =
        finiteEventCount Coin (fun c => r false c = y ∧ side c = s) :=
  countIndependentWithinToleranceOutput_sideRetained_sourceLowerBounds_lt_coinProduct_iff_sideFiber_count_eq
    C E r side htrue hfalse hlt

/-- For any extension of the current packet, becoming stop-grade is equivalent
to covering the currently named gap list.  This is the formal boundary between a
local obstruction packet and a packet that would close the whole audit ledger. -/
theorem stopGrade_iff_covers_currentPNP_gaps_of_extends_current
    {packet : PNPCruxPacket}
    (hExtends : packet.Extends currentPNPLocalCruxPacket) :
    packet.StopGrade ↔ packet.CoversList currentPNPUncoveredRepairClasses := by
  constructor
  · intro hstop repair _
    exact hstop repair
  · intro hGaps repair
    by_cases hCurrent : currentPNPLocalCruxPacket.covers repair
    · exact hExtends repair hCurrent
    · exact hGaps repair ((currentPNPUncoveredRepairClasses_exact repair).2 hCurrent)

/-- An extension of the current packet is not stop-grade if it still fails to
cover the current gap list. -/
theorem not_stopGrade_of_not_covers_currentPNP_gaps_of_extends_current
    {packet : PNPCruxPacket}
    (hExtends : packet.Extends currentPNPLocalCruxPacket)
    (hNotGaps : ¬ packet.CoversList currentPNPUncoveredRepairClasses) :
    ¬ packet.StopGrade := by
  intro hstop
  exact hNotGaps
    ((stopGrade_iff_covers_currentPNP_gaps_of_extends_current hExtends).1 hstop)

/-- The current packet still leaves residual-side-information repairs outside
the formal block. -/
theorem residualSideInformation_uncovered_currentPNPLocalCruxPacket :
    ¬ currentPNPLocalCruxPacket.covers .residualSideInformation := by
  simp [currentPNPLocalCruxPacket]

/-- The current accumulated local PNP packet is not stop-grade: residual side
information remains a named live repair class outside the formal block. -/
theorem not_stopGrade_currentPNPLocalCruxPacket :
    ¬ currentPNPLocalCruxPacket.StopGrade := by
  intro hstop
  exact residualSideInformation_uncovered_currentPNPLocalCruxPacket
    (hstop .residualSideInformation)

/-- The current packet also leaves randomized residual repairs outside the
formal block. -/
theorem randomizedResidual_uncovered_currentPNPLocalCruxPacket :
    ¬ currentPNPLocalCruxPacket.covers .randomizedResidual := by
  simp [currentPNPLocalCruxPacket]

/-- The current packet covers the finite-count same-source approximation
subcase supplied by `ApproximateDecorrelationObstruction.lean`.  This is not a
claim that broad approximate-decorrelation repairs are closed. -/
theorem sameSourceFiniteCountApproximation_covered_currentPNPLocalCruxPacket :
    currentPNPLocalCruxPacket.covers .sameSourceFiniteCountApproximation := by
  simp [currentPNPLocalCruxPacket]

/-- The current packet leaves approximate-decorrelation repairs outside the
formal block. -/
theorem approximateDecorrelation_uncovered_currentPNPLocalCruxPacket :
    ¬ currentPNPLocalCruxPacket.covers .approximateDecorrelation := by
  simp [currentPNPLocalCruxPacket]

/-- The current packet leaves the final `Kpoly` compression bridge outside the
formal block. -/
theorem kpolyCompressionBridge_uncovered_currentPNPLocalCruxPacket :
    ¬ currentPNPLocalCruxPacket.covers .kpolyCompressionBridge := by
  simp [currentPNPLocalCruxPacket]

/-- The current packet now includes the abstract finite counting kernel for the
clocked `Kpoly` bridge. -/
theorem clockedFiniteUniformKernel_covered_currentPNPLocalCruxPacket :
    currentPNPLocalCruxPacket.covers .clockedFiniteUniformKernel := by
  exact clockedFiniteUniformKernelCoverage

/-- Current strongest honest synthesis status: the v13 route entries now have
theorem-backed ledger coverage, the abstract clocked finite-uniform kernel is
covered, the concrete bit-vector exact ZAB ERM family closes the clocked
payload at its explicit budget, and the bare exact-visible interface is still
insufficient.  The broad manuscript-specific `Kpoly` bridge remains uncovered,
so the current packet is not stop-grade. -/
theorem currentPNPStrongestHonestStatus :
    currentPNPLocalCruxPacket.covers .repeatedPositiveFieldedPivot ∧
      currentPNPLocalCruxPacket.covers .forcedPositiveFieldedStep ∧
      currentPNPLocalCruxPacket.covers .fixedFieldBadCell ∧
      currentPNPLocalCruxPacket.covers .fieldRefinementOfBadCell ∧
      currentPNPLocalCruxPacket.covers .cdEvidenceNormalization ∧
      currentPNPLocalCruxPacket.covers .traceCaptureFactorization ∧
      currentPNPLocalCruxPacket.covers .atomicEvidenceBudget ∧
      currentPNPLocalCruxPacket.covers .acceiEnvelopeProduct ∧
      currentPNPLocalCruxPacket.covers .clockedFiniteUniformKernel ∧
      (∀ {r k clock : ℕ} {Index : Type u} [Fintype (BitVec r)]
        (samples :
          Index → Sample (ExactVisiblePostSwitchSurface (BitVec r) k) Bool),
        ClockedKpolyFiniteLearningPayload
          (bitVecZABDecisionListERMFamily
            (r := r) (k := k) (Index := Index) samples)
          (r + 2 * k + 1) clock) ∧
      (∀ {Z : Type v} [Fintype Z] {k s clock : ℕ}
        (_ : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)),
        ¬ (∀ {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index),
          ClockedKpolyFiniteLearningPayload G s clock)) ∧
      ¬ currentPNPLocalCruxPacket.covers .kpolyCompressionBridge ∧
      ¬ currentPNPLocalCruxPacket.StopGrade := by
  refine
    ⟨v13RepeatedPositiveFieldedPivotCoverage,
      v13ForcedPositiveFieldedStepCoverage,
      v13FieldedBadCellCoverage,
      v13FieldRefinementBadCellCoverage,
      v13EvidenceNormalizationCoverage,
      v13TraceCaptureFactorizationCoverage,
      v13AtomicEvidenceBudgetCoverage,
      v13ACCEIEnvelopeProductCoverage,
      clockedFiniteUniformKernelCoverage, ?_, ?_,
      kpolyCompressionBridge_uncovered_currentPNPLocalCruxPacket,
      not_stopGrade_currentPNPLocalCruxPacket⟩
  · intro r k clock Index _FintypeBitVec samples
    exact
      bitVecZABDecisionListERMClockedKpolyFiniteLearningPayload
        (r := r) (k := k) (clock := clock) (Index := Index) samples
  · intro Z _FintypeZ k s clock hs
    exact
      currentExactVisibleInterface_not_forall_clockedKpolyFiniteLearningPayload_of_lt_surfaceCard
        (Z := Z) (k := k) (s := s) (clock := clock) hs

/-- The formal packet obtained by adding precisely the current gap list to the
current local packet.  This does not prove those gaps mathematically; it is the
ledger object used to state what a full current-audit closure would have to
cover. -/
def currentPNPGapCompletedPacket : PNPCruxPacket where
  covers repair :=
    currentPNPLocalCruxPacket.covers repair ∨
      repair ∈ currentPNPUncoveredRepairClasses

/-- The gap-completed ledger packet extends the current local packet. -/
theorem currentPNPGapCompletedPacket_extends_current :
    currentPNPGapCompletedPacket.Extends currentPNPLocalCruxPacket := by
  intro repair hCurrent
  exact Or.inl hCurrent

/-- The gap-completed ledger packet covers every currently named gap. -/
theorem currentPNPGapCompletedPacket_covers_current_gaps :
    currentPNPGapCompletedPacket.CoversList currentPNPUncoveredRepairClasses := by
  intro repair hGap
  exact Or.inr hGap

/-- The gap-completed ledger packet covers the selected next marginal target. -/
theorem currentPNPGapCompletedPacket_covers_currentPNPNextMarginalTarget :
    currentPNPGapCompletedPacket.covers currentPNPNextMarginalTarget := by
  exact Or.inr currentPNPNextMarginalTarget_mem_uncovered

/-- Adding exactly the named current gaps is sufficient to make the ledger
stop-grade.  The theorem is bookkeeping, not a claim that the missing
mathematics has been supplied. -/
theorem stopGrade_currentPNPGapCompletedPacket :
    currentPNPGapCompletedPacket.StopGrade := by
  rw [stopGrade_iff_covers_currentPNP_gaps_of_extends_current
    currentPNPGapCompletedPacket_extends_current]
  exact currentPNPGapCompletedPacket_covers_current_gaps

end Mettapedia.Computability.PNP
