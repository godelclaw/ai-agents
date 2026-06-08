import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoveryAtomObstruction
import Mathlib.Tactic

namespace Mettapedia.Computability.PNP

def bitVec1ZeroVisiblePointActualSparseRecovery :
    ExactVisiblePostSwitchSurface (BitVec 1) 0 :=
  ⟨zeroVec, zeroVec, zeroVec⟩

def bitVec1OneVisiblePointActualSparseRecovery :
    ExactVisiblePostSwitchSurface (BitVec 1) 0 :=
  ⟨fun _ => true, zeroVec, zeroVec⟩

def idBitVec1ActualSparseRecovery : BitVec 1 → BitVec 1 := fun x => x

theorem fullRuleActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_bitVec1_pure_zero_regression :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          (PMF.pure bitVec1ZeroVisiblePointActualSparseRecovery)
          (fullRuleActualSwitchedLocalInterface (BitVec 1) 0)
          idBitVec1ActualSparseRecovery
          0) := by
  exact
    ActualSwitchedLocalInterface.fullRuleActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_pure_atom_lt_one_of_visibleWidth_pos
      (n := 1)
      (k := 0)
      (r := 1)
      (x := bitVec1ZeroVisiblePointActualSparseRecovery)
      (zfeat := idBitVec1ActualSparseRecovery)
      (q := 0)
      (by decide)
      (by norm_num)

theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_bitVec1_pure_zero_regression :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          (PMF.pure bitVec1ZeroVisiblePointActualSparseRecovery)
          (boundedSamplePluginMajorityActualSwitchedLocalInterface
            (BitVec 1) 0 2)
          idBitVec1ActualSparseRecovery
          0) := by
  have hxy :
      bitVec1ZeroVisiblePointActualSparseRecovery ≠
        bitVec1OneVisiblePointActualSparseRecovery := by
    intro h
    have hz := congrArg (fun u => u.z) h
    have hbit := congrFun hz 0
    simp [bitVec1ZeroVisiblePointActualSparseRecovery,
      bitVec1OneVisiblePointActualSparseRecovery, zeroVec] at hbit
  exact
    ActualSwitchedLocalInterface.boundedSamplePluginMajorityActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_pure_atom_lt_one
      (Z := BitVec 1)
      (k := 0)
      (r := 1)
      (sampleBound := 2)
      (q := 0)
      (zfeat := idBitVec1ActualSparseRecovery)
      (x := bitVec1ZeroVisiblePointActualSparseRecovery)
      (y := bitVec1OneVisiblePointActualSparseRecovery)
      (by
        rw [card_exactVisiblePostSwitchSurface_bitVec]
        norm_num)
      hxy
      (by norm_num)

end Mettapedia.Computability.PNP
