import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMCharacterization

/-!
# P vs NP route characterization: full-rule actual switched-local sparse-threshold
  ERM data exists at width `r` exactly when `BitVec n` admits an injective
  extractor into `BitVec r`

The previous manuscript-facing characterization isolated the actual switched-local
sparse-threshold ERM packet as exactly an injective-extractor route for a fixed
extractor `zfeat`.

This file eliminates the remaining extractor choice on the native `BitVec`
surface.  It gives an explicit low-bit-preserving embedding
`BitVec n → BitVec r` whenever `n ≤ r`, proves that no injective extractor
exists when `r < n`, and packages the result into an existential
width-characterization for the full-rule actual switched-local packet.
-/

namespace Mettapedia.Computability.PNP

namespace ActualSwitchedLocalInterface

section BitVecEmbedding

variable {n r : ℕ}

/-- The canonical low-bit embedding `BitVec n → BitVec r` for `n ≤ r`: keep the
first `n` bits and pad the rest with `false`. -/
def bitVecPrefixEmbedding : BitVec n → BitVec r :=
  fun x i =>
    if hi : (i : ℕ) < n then
      x ⟨i, hi⟩
    else
      false

@[simp] theorem bitVecPrefixEmbedding_apply_of_lt
    (x : BitVec n)
    (i : Fin r)
    (hi : (i : ℕ) < n) :
    bitVecPrefixEmbedding (n := n) (r := r) x i = x ⟨i, hi⟩ := by
  simp [bitVecPrefixEmbedding, hi]

@[simp] theorem bitVecPrefixEmbedding_apply_of_ge
    (x : BitVec n)
    (i : Fin r)
    (hi : n ≤ (i : ℕ)) :
    bitVecPrefixEmbedding (n := n) (r := r) x i = false := by
  simp [bitVecPrefixEmbedding, Nat.not_lt.mpr hi]

theorem injective_bitVecPrefixEmbedding
    (hnr : n ≤ r) :
    Function.Injective (bitVecPrefixEmbedding (n := n) (r := r)) := by
  intro x y hxy
  funext i
  have hxyi :=
    congrFun hxy ⟨i, lt_of_lt_of_le i.isLt hnr⟩
  simpa [bitVecPrefixEmbedding] using hxyi

theorem exists_injective_bitVecExtractor_of_le
    (hnr : n ≤ r) :
    ∃ zfeat : BitVec n → BitVec r, Function.Injective zfeat := by
  exact ⟨bitVecPrefixEmbedding (n := n) (r := r),
    injective_bitVecPrefixEmbedding (n := n) (r := r) hnr⟩

theorem exists_injective_bitVecExtractor_iff_width_le :
    (∃ zfeat : BitVec n → BitVec r, Function.Injective zfeat) ↔ n ≤ r := by
  constructor
  · rintro ⟨zfeat, hinj⟩
    by_contra hnr
    exact
      (not_injective_bitVecExtractor_of_width_lt zfeat (Nat.lt_of_not_ge hnr)) hinj
  · intro hnr
    exact exists_injective_bitVecExtractor_of_le (n := n) (r := r) hnr

end BitVecEmbedding

section FullRule

variable {n r k m : ℕ}

theorem fullRuleActualSwitchedLocalInterface_exists_sharedExactZABSparseThresholdERMData_of_width_le
    (hnr : n ≤ r)
    (hwidth : 0 < r + (k + k))
    (hbound :
      2 ^ (2 * allAffinePointBlockFeatureCount (r + (k + k))) *
          (Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k) - 1) ^ m <
        Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k) ^ m) :
    ∃ zfeat : BitVec n → BitVec r,
      Nonempty
        (SharedExactZABSparseThresholdERMData
          (fullRuleActualSwitchedLocalInterface (BitVec n) k)
          zfeat) := by
  refine ⟨bitVecPrefixEmbedding (n := n) (r := r), ?_⟩
  exact
    fullRuleActualSwitchedLocalInterface_nonempty_sharedExactZABSparseThresholdERMData_of_injective_zfeat
      (Z := BitVec n) (r := r) (k := k) (m := m)
      (bitVecPrefixEmbedding (n := n) (r := r))
      (injective_bitVecPrefixEmbedding (n := n) (r := r) hnr)
      hwidth hbound

theorem fullRuleActualSwitchedLocalInterface_exists_sharedExactZABSparseThresholdERMData_iff_width_le
    (hwidth : 0 < r + (k + k))
    (hbound :
      2 ^ (2 * allAffinePointBlockFeatureCount (r + (k + k))) *
          (Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k) - 1) ^ m <
        Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k) ^ m) :
    (∃ zfeat : BitVec n → BitVec r,
      Nonempty
        (SharedExactZABSparseThresholdERMData
          (fullRuleActualSwitchedLocalInterface (BitVec n) k)
          zfeat)) ↔
      n ≤ r := by
  constructor
  · rintro ⟨zfeat, hdata⟩
    have hinj :
        Function.Injective zfeat := by
      exact
        (fullRuleActualSwitchedLocalInterface_nonempty_sharedExactZABSparseThresholdERMData_iff_injective_zfeat
          (Z := BitVec n) (r := r) (k := k) (m := m)
          zfeat hwidth hbound).1 hdata
    exact
      (exists_injective_bitVecExtractor_iff_width_le (n := n) (r := r)).1
        ⟨zfeat, hinj⟩
  · intro hnr
    exact
      fullRuleActualSwitchedLocalInterface_exists_sharedExactZABSparseThresholdERMData_of_width_le
        (n := n) (r := r) (k := k) (m := m)
        hnr hwidth hbound

end FullRule

end ActualSwitchedLocalInterface

end Mettapedia.Computability.PNP
