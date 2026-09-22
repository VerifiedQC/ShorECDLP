import ShorECDLP.Submission.«2607_13816».EEA.MeasuredPrimitiveBalance
import ShorECDLP.Submission.«2607_13816».EEA.MeasuredWrapperCounts
namespace ShorECDLP.Paper2607_13816
open Quantum
attribute [local irreducible] primitiveResources AdaptiveCircuit.seq
private theorem seq_balance {a b c d : AdaptiveCircuit}
    (h : PrimitiveBalance (primitiveResources a) (primitiveResources c))
    (j : PrimitiveBalance (primitiveResources b) (primitiveResources d)) :
    PrimitiveBalance (primitiveResources (a.seq b)) (primitiveResources (c.seq d)) := by
  simp only [primitiveResources_seq,PrimitiveBalance,PrimitiveResources.add] at *
  omega
private theorem refl_balance (a : AdaptiveCircuit) : PrimitiveBalance (primitiveResources a) (primitiveResources a) := by
  simp [PrimitiveBalance]
theorem measuredIndexedStep_balance (r : IndexedStepRegisters) (n T : Nat) :
    PrimitiveBalance (primitiveResources (measuredIndexedStep r n T))
      (primitiveResources (indexedStepAdaptive r n T)) := by
  rw [measuredStepPrefix_factor]
  exact seq_balance (refl_balance _) (measuredBlockHForward_balance r n T)
theorem measuredIndexedStepInverse_balance (r : IndexedStepRegisters) (n T : Nat) :
    PrimitiveBalance (primitiveResources (measuredIndexedStepInverse r n T))
      (primitiveResources (indexedStepInverseAdaptive r n T)) := by
  rw [indexedStepInverseAdaptive_factor]
  exact seq_balance (measuredBlockHInverse_balance r n T) (refl_balance _)
theorem measuredIndexedSchedule_balance (r : IndexedStepRegisters) (n start count : Nat) :
    PrimitiveBalance (primitiveResources (measuredIndexedSchedule r n start count))
      (primitiveResources (indexedScheduleAdaptive r n start count)) := by
  induction count generalizing start with
  | zero => exact refl_balance _
  | succ count ih => exact seq_balance (measuredIndexedStep_balance r n start) (ih (start+1))
theorem measuredIndexedScheduleInverse_balance (r : IndexedStepRegisters) (n start count : Nat) :
    PrimitiveBalance (primitiveResources (measuredIndexedScheduleInverse r n start count))
      (primitiveResources (indexedScheduleInverseAdaptive r n start count)) := by
  induction count generalizing start with
  | zero => exact refl_balance _
  | succ count ih => exact seq_balance (ih (start+1)) (measuredIndexedStepInverse_balance r n start)
private theorem forward_balance :
    PrimitiveBalance (primitiveResources (secp256k1MeasuredEEAForward indexedStepProductionRegisters))
      (primitiveResources (secp256k1EEAForwardAdaptive indexedStepProductionRegisters)) :=
  measuredIndexedSchedule_balance _ _ _ _
private theorem reverse_balance :
    PrimitiveBalance (primitiveResources (secp256k1MeasuredEEAReverse indexedStepProductionRegisters))
      (primitiveResources (secp256k1EEAReverseAdaptive indexedStepProductionRegisters)) :=
  measuredIndexedScheduleInverse_balance _ _ _ _
attribute [local irreducible] eeaPreprocess eeaUnpreprocess secp256k1MeasuredEEAForward
  secp256k1MeasuredEEAReverse secp256k1EEAForwardAdaptive secp256k1EEAReverseAdaptive
  secp256k1EEAParityCorrection canonicalWork2Rotation terminalEpochCompression terminalWork1Clear
  secp256k1EEAReversePostprocessing

theorem secp256k1MeasuredEEAForwardWrapper_balance :
    PrimitiveBalance (primitiveResources secp256k1MeasuredEEAForwardWrapper)
      (primitiveResources secp256k1EEAForwardWrapper) := by
  unfold secp256k1MeasuredEEAForwardWrapper secp256k1EEAForwardWrapper
  exact seq_balance (seq_balance (seq_balance (seq_balance (refl_balance _) forward_balance)
    (refl_balance _)) (refl_balance _)) (refl_balance _)
theorem secp256k1MeasuredEEAReverseWrapper_balance :
    PrimitiveBalance (primitiveResources secp256k1MeasuredEEAReverseWrapper)
      (primitiveResources secp256k1EEAReverseWrapper) := by
  unfold secp256k1MeasuredEEAReverseWrapper secp256k1EEAReverseWrapper
  exact seq_balance (seq_balance (refl_balance _) reverse_balance) (refl_balance _)

attribute [local irreducible] secp256k1MeasuredEEAForwardWrapper secp256k1MeasuredEEAReverseWrapper secp256k1EEAForwardWrapper secp256k1EEAReverseWrapper

private theorem balance_exact (v w z : PrimitiveResources)
    (hb : PrimitiveBalance v w) (hz : PrimitiveBalance z w)
    (ht : v.toffoli = z.toffoli) : v = z := by
  cases v
  cases w
  cases z
  simp only [PrimitiveBalance, PrimitiveResources.mk.injEq] at *
  omega

theorem secp256k1MeasuredEEAForwardWrapper_primitive_exact :
    primitiveResources secp256k1MeasuredEEAForwardWrapper=⟨19437345,13926240,31417379,15910015,0,6961844⟩ := by
  apply balance_exact _ _ _ secp256k1MeasuredEEAForwardWrapper_balance
  · rw [secp256k1EEAForwardWrapper_primitive_exact]
    simp [PrimitiveBalance]
  · exact secp256k1MeasuredEEAForwardWrapper_toffoli

theorem secp256k1MeasuredEEAReverseWrapper_primitive_exact :
    primitiveResources secp256k1MeasuredEEAReverseWrapper=⟨19489185,13926240,31417379,15910015,0,6961844⟩ := by
  apply balance_exact _ _ _ secp256k1MeasuredEEAReverseWrapper_balance
  · rw [secp256k1EEAReverseWrapper_primitive_exact]
    simp [PrimitiveBalance]
  · exact secp256k1MeasuredEEAReverseWrapper_toffoli

theorem secp256k1MeasuredEEAForwardWrapper_primitive_bounds :
    let v := primitiveResources secp256k1MeasuredEEAForwardWrapper
    v.x≤19441121 ∧ v.h≤13926240 ∧ v.cnot≤31424883 ∧ v.toffoli≤15910015 ∧ v.phase=0 ∧ v.measurements≤6961844 := by
  rw [secp256k1MeasuredEEAForwardWrapper_primitive_exact]
  decide
theorem secp256k1MeasuredEEAReverseWrapper_primitive_bounds :
    let v := primitiveResources secp256k1MeasuredEEAReverseWrapper
    v.x≤19492961 ∧ v.h≤13926240 ∧ v.cnot≤31424883 ∧ v.toffoli≤15910015 ∧ v.phase=0 ∧ v.measurements≤6961844 := by
  rw [secp256k1MeasuredEEAReverseWrapper_primitive_exact]
  decide
end ShorECDLP.Paper2607_13816
