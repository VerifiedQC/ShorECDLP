import ShorECDLP.Submission.«2607_13816».EEA.MeasuredWrapper
import ShorECDLP.Submission.«2607_13816».EEA.WrapperPrimitiveCounts
namespace ShorECDLP.Paper2607_13816
open Quantum
attribute [local irreducible] AdaptiveCircuit.seq primitiveResources secp256k1MeasuredEEAForward secp256k1MeasuredEEAReverse
  secp256k1EEAForwardAdaptive secp256k1EEAReverseAdaptive
  eeaPreprocess eeaUnpreprocess secp256k1EEAParityCorrection
  canonicalWork2Rotation terminalEpochCompression terminalWork1Clear
  secp256k1EEAReversePostprocessing
  secp256k1MeasuredEEAForwardWrapper secp256k1MeasuredEEAReverseWrapper
  secp256k1EEAForwardWrapper secp256k1EEAReverseWrapper

private theorem toffoli_seq (a b : AdaptiveCircuit) :
    (primitiveResources (a.seq b)).toffoli =
      (primitiveResources a).toffoli + (primitiveResources b).toffoli := by
  rw [primitiveResources_seq]
  rfl

/-- Actual complete forward-wrapper savings, retaining preprocessing and all postprocessing. -/
theorem secp256k1MeasuredEEAForwardWrapper_savings :
    (primitiveResources secp256k1MeasuredEEAForwardWrapper).toffoli + 1681736 =
      (primitiveResources secp256k1EEAForwardWrapper).toffoli := by
  have h := secp256k1MeasuredEEAForward_toffoli indexedStepProductionRegisters
    secp256k1ScheduleLayout_production (by decide)
  simp only [secp256k1MeasuredEEAForwardWrapper, secp256k1EEAForwardWrapper,
    toffoli_seq]
  omega

/-- Actual complete inverse-wrapper savings, retaining both source wrapper boundaries. -/
theorem secp256k1MeasuredEEAReverseWrapper_savings :
    (primitiveResources secp256k1MeasuredEEAReverseWrapper).toffoli + 1681736 =
      (primitiveResources secp256k1EEAReverseWrapper).toffoli := by
  have h := secp256k1MeasuredEEAReverse_toffoli indexedStepProductionRegisters
    secp256k1ScheduleLayout_production (by decide)
  simp only [secp256k1MeasuredEEAReverseWrapper, secp256k1EEAReverseWrapper,
    toffoli_seq]
  omega

/-- Exact Toffoli count of the emitted measured forward inversion wrapper. -/
theorem secp256k1MeasuredEEAForwardWrapper_toffoli :
    (primitiveResources secp256k1MeasuredEEAForwardWrapper).toffoli = 15910015 := by
  have h := secp256k1MeasuredEEAForwardWrapper_savings
  rw [secp256k1EEAForwardWrapper_primitive_exact] at h
  change _ + 1681736 = 17591751 at h
  omega

/-- Exact Toffoli count of the emitted measured inverse inversion wrapper. -/
theorem secp256k1MeasuredEEAReverseWrapper_toffoli :
    (primitiveResources secp256k1MeasuredEEAReverseWrapper).toffoli = 15910015 := by
  have h := secp256k1MeasuredEEAReverseWrapper_savings
  rw [secp256k1EEAReverseWrapper_primitive_exact] at h
  change _ + 1681736 = 17591751 at h
  omega
end ShorECDLP.Paper2607_13816
