import Mettapedia.Computability.ProbabilisticTM
import Mathlib.Computability.PartrecCode

/-!
# Oracle Turing Machines

This file defines oracle Turing machines (OTM) that can query an oracle during computation.
An oracle is a function `ℕ → Bool` that answers threshold queries about probabilities.

## Main Definitions

* `Oracle`: A function `ℕ → Bool` answering probability threshold queries
* `OTM`: An oracle Turing machine combining random bits and oracle access
* `OTM.outputProb`: The probability that an OTM outputs 1 given an oracle

## Mathematical Model

An Oracle Turing Machine takes:
1. An input `x : ℕ`
2. Random bits `r : CantorSpace`
3. An oracle `O : Oracle`

The oracle O answers queries of the form "Is P(M outputs 1 on x) > p?" for
(M, x, p) encoded as a natural number.

## References

* Leike, "Nonparametric General Reinforcement Learning", Chapter 7
* Turing, "On Computable Numbers", 1936 (original oracle machines)

-/

open MeasureTheory Measure Filter
open scoped ENNReal NNReal

namespace Mettapedia.Computability

/-! ## Oracle Definition -/

/-- An oracle is a function answering probability threshold queries.

Mathematically, an oracle O : ℕ → Bool satisfies the reflectivity condition:
- O(encode(M, x, p)) = true iff P(M outputs 1 on x | O) > p

where P(· | O) is the probability using O as the oracle.
-/
abbrev Oracle := ℕ → Bool

/-- A query to the oracle: (machine index, input, threshold). -/
structure OracleQuery where
  machineIdx : ℕ
  input : ℕ
  threshold : ℚ
  threshold_pos : 0 < threshold
  threshold_lt_one : threshold < 1
deriving DecidableEq

/-- Encode an oracle query as a natural number. -/
def encodeOracleQuery (q : OracleQuery) : ℕ :=
  Nat.pair q.machineIdx (Nat.pair q.input (Int.toNat (q.threshold.num + q.threshold.den)))

/-! ## Oracle Turing Machine -/

/-- An Oracle Turing Machine index.

An OTM is a PTM that additionally has access to an oracle.
We model this by encoding oracle query results in the random bits encoding.
-/
abbrev OTMIndex := Nat.Partrec.Code

/-- Decode a query index to machine and input (threshold is encoded separately).
This extracts the (M, x) pair from an encoded query. -/
def decodeQuery (n : ℕ) : OTMIndex × ℕ :=
  let machineIdx := n.unpair.1
  let x := n.unpair.2
  (Nat.Partrec.Code.ofNatCode machineIdx, x)

/-- The query index for a machine M and input x.
The encoding uses pair (encodeCode M, x). -/
def queryIndex (M : OTMIndex) (x : ℕ) : ℕ :=
  Nat.pair (Nat.Partrec.Code.encodeCode M) x

/-- Run an OTM for at most k steps with n random bits and oracle access.

The machine can query the oracle by encoding a query in its output and checking
the corresponding bit in the oracle.
-/
def runOTMBounded (M : OTMIndex) (x : ℕ) (r : CantorSpace) (O : Oracle)
    (fuel : ℕ) (numBits : ℕ) : Option ℕ :=
  -- We encode both random bits and oracle answers in the input
  -- Random bits: first numBits of the encoding
  -- Oracle answers: accessed by querying specific indices
  let randomPart := encodeRandomBits r numBits
  -- For simplicity, we use a fixed encoding scheme:
  -- Input = (x, (randomBits, oracleBit))
  -- Oracle answers are determined by O applied to encoded queries
  let oracleBit : ℕ := if O 0 then 1 else 0
  let input := Nat.pair x (Nat.pair randomPart oracleBit)
  Nat.Partrec.Code.evaln fuel M input

/-- An OTM halts with output k given random bits r and oracle O. -/
def OTMHaltsWithOutput (M : OTMIndex) (x : ℕ) (r : CantorSpace) (O : Oracle) (k : ℕ) : Prop :=
  ∃ fuel numBits, runOTMBounded M x r O fuel numBits = some k

/-- The set of random tapes for which the OTM outputs 1 given oracle O. -/
def oracleOutputOneSet (M : OTMIndex) (x : ℕ) (O : Oracle) : Set CantorSpace :=
  {r : CantorSpace | OTMHaltsWithOutput M x r O 1}

/-- The set of random tapes for which the OTM outputs 0 given oracle O. -/
def oracleOutputZeroSet (M : OTMIndex) (x : ℕ) (O : Oracle) : Set CantorSpace :=
  {r : CantorSpace | OTMHaltsWithOutput M x r O 0}

/-! ## Output Probability with Oracle -/

/-- The probability that OTM M on input x outputs 1 given oracle O.

This is the key quantity for reflective oracles: we want the oracle O to
correctly report whether this probability exceeds a given threshold.
-/
noncomputable def oracleOutputProb (M : OTMIndex) (x : ℕ) (O : Oracle) : ℝ≥0∞ :=
  coinMeasure (oracleOutputOneSet M x O)

/-- The probability that OTM M on input x outputs 0 given oracle O. -/
noncomputable def oracleOutputProbZero (M : OTMIndex) (x : ℕ) (O : Oracle) : ℝ≥0∞ :=
  coinMeasure (oracleOutputZeroSet M x O)

/-- Oracle output probability is at most 1. -/
theorem oracleOutputProb_le_one (M : OTMIndex) (x : ℕ) (O : Oracle) :
    oracleOutputProb M x O ≤ 1 := by
  unfold oracleOutputProb
  have h1 : coinMeasure (oracleOutputOneSet M x O) ≤ coinMeasure Set.univ :=
    measure_mono (Set.subset_univ _)
  have h2 : coinMeasure Set.univ = 1 := measure_univ
  calc coinMeasure (oracleOutputOneSet M x O) ≤ coinMeasure Set.univ := h1
    _ = 1 := h2

/-- Oracle output probability is non-negative. -/
theorem oracleOutputProb_nonneg (M : OTMIndex) (x : ℕ) (O : Oracle) :
    0 ≤ oracleOutputProb M x O :=
  zero_le _

/-! ## Reflectivity Conditions

A reflective oracle O satisfies two conditions for each query q:

1. **Soundness**: O(q) = true → P(M outputs 1 | O) > threshold
2. **Completeness**: P(M outputs 1 | O) > threshold → O(q) = true

The gap theorem (in DirectionMismatch.lean) shows that during construction,
soundness is preserved but completeness requires additional work.
-/

/-- Soundness condition for a reflective oracle at a specific query. -/
def isSoundAt (O : Oracle) (M : OTMIndex) (x : ℕ) (threshold : ℝ≥0∞) : Prop :=
  O (Nat.pair (Nat.Partrec.Code.encodeCode M) x) = true → oracleOutputProb M x O > threshold

/-- Completeness condition for a reflective oracle at a specific query. -/
def isCompleteAt (O : Oracle) (M : OTMIndex) (x : ℕ) (threshold : ℝ≥0∞) : Prop :=
  oracleOutputProb M x O > threshold → O (Nat.pair (Nat.Partrec.Code.encodeCode M) x) = true

/-- An oracle is reflective if it satisfies both soundness and completeness
for all queries. -/
def isReflective (O : Oracle) : Prop :=
  ∀ M : OTMIndex, ∀ x : ℕ, ∀ threshold : ℝ≥0∞,
    threshold < 1 →
    isSoundAt O M x threshold ∧ isCompleteAt O M x threshold

/-! ## Partial Oracles

For the constructive proof of reflective oracle existence, we use
partial oracles that are defined on only finitely many queries.
-/

/-- A partial oracle defined on the first k queries. -/
structure PartialOracle (k : ℕ) where
  /-- The value of the oracle on each query. Uses ℚ to represent 0, 1, or 1/2. -/
  value : Fin k → ℚ
  /-- Values are in {0, 1/2, 1}. -/
  onGrid : ∀ i, value i = 0 ∨ value i = 1/2 ∨ value i = 1

/-- Convert a partial oracle to a full oracle by extending with 1/2 (unknown). -/
def PartialOracle.toFullOracle {k : ℕ} (Õ : PartialOracle k) : Oracle :=
  fun n => if h : n < k
           then Õ.value ⟨n, h⟩ = 1  -- True if oracle says "yes"
           else false  -- Unknown queries default to false

/-- A partial oracle extends another if they agree on the smaller domain. -/
def PartialOracle.extends {k₁ k₂ : ℕ} (Õ₂ : PartialOracle k₂) (Õ₁ : PartialOracle k₁)
    (h : k₁ ≤ k₂) : Prop :=
  ∀ i : Fin k₁, Õ₂.value ⟨i.val, Nat.lt_of_lt_of_le i.isLt h⟩ = Õ₁.value i

/-! ## Monotonicity

In the current simplified encoding, `runOTMBounded` only threads the value of
`O 0` into the machine input. So the honest invariant is weaker than a general
oracle-extension monotonicity statement: if two oracles agree at query `0`,
then the bounded runs, output sets, and output probabilities coincide.
-/

/-- In the current simplified oracle model, bounded execution only depends on `O 0`. -/
theorem runOTMBounded_congr_of_oracle_zero_eq
    (M : OTMIndex) (x : ℕ) (r : CantorSpace) (O₁ O₂ : Oracle)
    (fuel numBits : ℕ) (h0 : O₁ 0 = O₂ 0) :
    runOTMBounded M x r O₁ fuel numBits = runOTMBounded M x r O₂ fuel numBits := by
  unfold runOTMBounded
  simp [h0]

/-- In the current simplified oracle model, the output-1 set only depends on `O 0`. -/
theorem oracleOutputOneSet_congr_of_oracle_zero_eq
    (M : OTMIndex) (x : ℕ) (O₁ O₂ : Oracle)
    (h0 : O₁ 0 = O₂ 0) :
    oracleOutputOneSet M x O₁ = oracleOutputOneSet M x O₂ := by
  ext r
  constructor <;> intro hr
  · rcases hr with ⟨fuel, numBits, hrun⟩
    exact ⟨fuel, numBits, by
      rw [← runOTMBounded_congr_of_oracle_zero_eq M x r O₁ O₂ fuel numBits h0]
      exact hrun⟩
  · rcases hr with ⟨fuel, numBits, hrun⟩
    exact ⟨fuel, numBits, by
      rw [runOTMBounded_congr_of_oracle_zero_eq M x r O₁ O₂ fuel numBits h0]
      exact hrun⟩

/-- In the current simplified oracle model, output probability only depends on `O 0`. -/
theorem oracleOutputProb_congr_of_oracle_zero_eq
    (M : OTMIndex) (x : ℕ) (O₁ O₂ : Oracle)
    (h0 : O₁ 0 = O₂ 0) :
    oracleOutputProb M x O₁ = oracleOutputProb M x O₂ := by
  unfold oracleOutputProb
  rw [oracleOutputOneSet_congr_of_oracle_zero_eq M x O₁ O₂ h0]

/-- When extending a partial oracle, output probabilities don't decrease.

Under the current simplified encoding, a positive base domain forces equality
at query `0`, so the output probabilities are actually equal.
-/
theorem oracleOutputProb_mono_extension {k₁ k₂ : ℕ} (h : k₁ ≤ k₂)
    (hk₁ : 0 < k₁)
    (Õ₁ : PartialOracle k₁) (Õ₂ : PartialOracle k₂)
    (h_ext : Õ₂.extends Õ₁ h) (M : OTMIndex) (x : ℕ) :
    oracleOutputProb M x Õ₁.toFullOracle ≤ oracleOutputProb M x Õ₂.toFullOracle := by
  have hk₂ : 0 < k₂ := lt_of_lt_of_le hk₁ h
  have hval :
      Õ₂.value ⟨0, hk₂⟩ = Õ₁.value ⟨0, hk₁⟩ :=
    h_ext ⟨0, hk₁⟩
  have hzero : Õ₁.toFullOracle 0 = Õ₂.toFullOracle 0 := by
    unfold PartialOracle.toFullOracle
    simp [hk₁, hk₂, hval]
  rw [oracleOutputProb_congr_of_oracle_zero_eq M x Õ₁.toFullOracle Õ₂.toFullOracle hzero]

end Mettapedia.Computability
